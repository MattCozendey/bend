import Bootstrap.WordJump

-- Machine
-- =======
--
-- The environment machine. It runs a term without substitution: a variable
-- reads its value from an environment, and a function value is its code
-- with its environment. It keeps its place in the term with a stack of
-- frames, so it never walks the term from the top again. decode gives the
-- term that a machine state stands for.

open Quan Term Spec

namespace Interp

-- Values
-- ======

-- a value of the machine
-- - clo t e: a λ, a λ-match or a type t, with the values e of its variables
-- - dead t e: a dead term t (q=0), with e. The machine never runs it.
-- - lab, rfl, tup: plain data
-- - call k xs: a call of def k on xs whose case tree needs more arguments
inductive Val where
  | clo (t : Term) (e : List Val)
  | dead (t : Term) (e : List Val)
  | lab (k : String)
  | rfl
  | tup (q : Quan) (a b : Val)
  | call (k : String) (xs : List (Quan × Val))

mutual
-- Val.rb v: the term that v stands for
def Val.rb : Val → Term
  | .clo t e => sub (Env.sub (Val.rbs e)) t
  | .dead t e => sub (Env.sub (Val.rbs e)) t
  | .lab k => Lab k
  | .rfl => Rfl
  | .tup q a b => Tup q a.rb b.rb
  | .call k xs => spine (Ref k) (Val.rbArgs xs)

def Val.rbs : List Val → List Term
  | [] => []
  | v :: vs => v.rb :: Val.rbs vs

def Val.rbArgs : List (Quan × Val) → List Arg
  | [] => []
  | (q, v) :: xs => (q, v.rb) :: Val.rbArgs xs
end

-- ofData t: t as a value, for a result of a word jump (plain data). A
-- dead field (q=0) stays a dead term.
def ofData : Term → Val
  | Lab k => .lab k
  | Rfl => .rfl
  | Tup q a b => .tup q (if q.live then ofData a else .dead a []) (ofData b)
  | t => .clo t []

-- v.live: v is no dead term
def Val.live : Val → Bool
  | .dead .. => false
  | _ => true

-- dataV v: v is plain data. It is false for each closure.
def dataV : Val → Bool
  | .lab _ => true
  | .rfl => true
  | .tup q a b => (!q.live || dataV a) && dataV b
  | _ => false

-- walkV t e xs: walk, on values. some none: the tree needs more arguments.
-- some (some (t, e, xs)): the walk leaves the tree at t, with e and the
-- rest xs.
def walkV : Term → List Val → List (Quan × Val) →
    Option (Option (Term × List Val × List (Quan × Val)))
  | Lam _ _, _, [] => some none
  | Lam p f, e, (q, x) :: xs =>
    if p.live = q.live ∧ (p = Q2 → dataV x = true) then walkV f (x :: e) xs else none
  | Prj _, _, [] => some none
  | Prj h, e, (q, .tup r a b) :: xs =>
    if q.live then walkV h e ((Quan.fld r q, a) :: (q, b) :: xs) else none
  | Prj _, _, _ :: _ => none
  | Mat .., _, [] => some none
  | Mat k h m, e, (q, .lab j) :: xs =>
    if q.live then (if j = k then walkV h e xs else walkV m e ((q, .lab j) :: xs)) else none
  | Mat .., _, _ :: _ => none
  | Efq, _, [] => some none
  | Efq, _, _ :: _ => none
  | App q f (Var v), e, xs =>
    if takes (unspine f []).1 then
      match e[v]? with
      | some x => if q.live = true → x.live = true then walkV f e ((q, x) :: xs) else none
      | none => none
    else some (some (App q f (Var v), e, xs))
  | t, e, xs => some (some (t, e, xs))

-- States
-- ======

-- a frame: what to do with the value of the current term
-- - appF q x e: it is the function of App q _ x
-- - appX q f: it is the argument of App q f _, and f is a value
-- - appV q a: it is the function of App q _ a, and a is a value
-- - letV q f e: it is the value of Let q _ f
-- - tupA q b e, tupB q a: it is the first or second field of a pair
-- - rwt P f e: it is the proof of Rwt _ P f
-- - minA b e, minB a: it is the first or second side of a meet
inductive Frame where
  | appF (q : Quan) (x : Term) (e : List Val)
  | appX (q : Quan) (f : Val)
  | appV (q : Quan) (a : Val)
  | letV (q : Quan) (f : Term) (e : List Val)
  | tupA (q : Quan) (b : Term) (e : List Val)
  | tupB (q : Quan) (a : Val)
  | rwt (P f : Term) (e : List Val)
  | minA (b : Term) (e : List Val)
  | minB (a : Val)

-- a state: run t with e, or return v, then the frames k
inductive St where
  | eval (t : Term) (e : List Val) (k : List Frame)
  | ret (v : Val) (k : List Frame)

-- plug k t: the term with t in the place of the frames k
def plug : List Frame → Term → Term
  | [], t => t
  | .appF q x e :: k, t => plug k (App q t (sub (Env.sub (Val.rbs e)) x))
  | .appX q f :: k, t => plug k (App q f.rb t)
  | .appV q a :: k, t => plug k (App q t a.rb)
  | .letV q f e :: k, t => plug k (Let q t (sub (Subst.up (Env.sub (Val.rbs e))) f))
  | .tupA q b e :: k, t => plug k (Tup q t (sub (Env.sub (Val.rbs e)) b))
  | .tupB q a :: k, t => plug k (Tup q a.rb t)
  | .rwt P f e :: k, t =>
    plug k (Rwt t (sub (Subst.up (Subst.up (Env.sub (Val.rbs e)))) P) (sub (Env.sub (Val.rbs e)) f))
  | .minA b e :: k, t => plug k (.Min t (sub (Env.sub (Val.rbs e)) b))
  | .minB a :: k, t => plug k (.Min a.rb t)

def decode : St → Term
  | .eval t e k => plug k (sub (Env.sub (Val.rbs e)) t)
  | .ret v k => plug k v.rb

-- Steps
-- =====

-- the names of the word defs that a jump can take
def wordDefs : List String :=
  ["Word.adc.group", "Word.not", "Word.and", "Word.or", "Word.xor", "Word.inc", "Word.to_nat",
   "Word.cmp", "Word.shl", "Word.shr", "Word.mul.go"]

-- tryCall bk jump k xs fs: a call of def k on the values xs, then fs
def tryCall (bk : Book) (jump : Term → Option Term) (k : String) (xs : List (Quan × Val))
    (fs : List Frame) : Option St :=
  match (if k ∈ wordDefs then jump (spine (Ref k) (Val.rbArgs xs)) else none) with
  | some u => if isData u then some (.ret (ofData u) fs) else none
  | none =>
    match bk.get k with
    | some d =>
      match walkV d.v [] xs with
      | some none => some (.ret (.call k xs) fs)
      | some (some (t, e, rest)) => some (.eval t e (rest.map (fun (q, a) => .appV q a) ++ fs))
      | none => none
    | none => none

-- apply bk jump f x fs: the value f applied to x, then fs
def apply (bk : Book) (jump : Term → Option Term) (f : Val) (q : Quan) (x : Val)
    (fs : List Frame) : Option St :=
  match f, x with
  | .clo (Lam p b) e, x =>
    if p.live = q.live ∧ (p = Q2 → dataV x = true) then some (.eval b (x :: e) fs) else none
  | .clo (Prj h) e, .tup r a b =>
    if q.live then some (.eval h e (.appV (Quan.fld r q) a :: .appV q b :: fs)) else none
  | .clo (Mat k h m) e, .lab j =>
    if q.live then
      (if j = k then some (.eval h e fs) else some (.eval m e (.appV q (.lab j) :: fs)))
    else none
  | .call k xs, x => tryCall bk jump k (xs ++ [(q, x)]) fs
  | _, _ => none

-- mstep bk jump s: one step of the machine, or none when it stops
def mstep (bk : Book) (jump : Term → Option Term) : St → Option St
  | .eval t e fs =>
    match t with
    | Var i =>
      match e[i]? with
      | some (.dead ..) => none
      | some v => some (.ret v fs)
      | none => none
    | Ref k => tryCall bk jump k [] fs
    | Ann x _ => some (.eval x e fs)
    | Let q v f =>
      if q.live then some (.eval v e (.letV q f e :: fs)) else some (.eval f (.dead v e :: e) fs)
    | Tup q a b =>
      if q.live then some (.eval a e (.tupA q b e :: fs))
      else some (.eval b e (.tupB q (.dead a e) :: fs))
    | App q f x => some (.eval f e (.appF q x e :: fs))
    | Rwt p P f => some (.eval p e (.rwt P f e :: fs))
    | .Min a b => some (.eval a e (.minA b e :: fs))
    | Lab j => some (.ret (.lab j) fs)
    | Rfl => some (.ret .rfl fs)
    | _ => some (.ret (.clo t e) fs)
  | .ret _ [] => none
  | .ret v (fr :: fs) =>
    match fr with
    | .appF q x e =>
      if q.live then some (.eval x e (.appX q v :: fs)) else apply bk jump v q (.dead x e) fs
    | .appX q f => apply bk jump f q v fs
    | .appV q a => apply bk jump v q a fs
    | .letV q f e => if q = Q2 → dataV v = true then some (.eval f (v :: e) fs) else none
    | .tupA q b e => some (.eval b e (.tupB q v :: fs))
    | .tupB q a => some (.ret (.tup q a v) fs)
    | .rwt _ f e =>
      match v with
      | .rfl => some (.eval f e fs)
      | _ => none
    | .minA b e => some (.eval b e (.minB v :: fs))
    | .minB a =>
      match a, v with
      | .lab i, .lab j =>
        if i ∈ QS ∧ j ∈ QS then some (.eval (qmin (Lab i) (Lab j)) [] fs) else none
      | _, _ => none

-- mrun bk jump n s: at most n machine steps from s; the state where it
-- stops, and the fuel left
def mrun (bk : Book) (jump : Term → Option Term) : Nat → St → St × Nat
  | 0, s => (s, 0)
  | n + 1, s =>
    match mstep bk jump s with
    | some s' => mrun bk jump n s'
    | none => (s, n + 1)

end Interp
