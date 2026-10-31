import Bootstrap.Stepwise

-- Machine
-- =======
--
-- Runs of Eval that cost about the same for each step, at any size of the
-- term. stepwise (Bootstrap/Stepwise.lean) starts each step again from the top
-- of the term, and checks again that each part to the left is a value. The
-- machine keeps its place: a focus, and the frames around it. It evaluates a
-- term under the terms of its variables, its locals, and remembers which of
-- them are values. It puts them into the term only when the term is needed
-- whole. When it stops, or runs out of gas, stepwise goes on from its term.

open Quan Term

namespace Machine

-- the terms of a term's variables, each with whether it is known to be a value
abbrev Locals := List (Term × Bool)

def subst (l : Locals) : Nat → Term := Env.sub (l.map (·.1))

-- the term t under its locals l
def close (t : Term) (l : Locals) : Term := if l.isEmpty then t else sub (subst l) t

-- an argument of a walk: its quantity, its term, and whether it is known to be
-- a value
abbrev MArg := Quan × Term × Bool

-- the local v of l
def localAt (l : Locals) (v : Nat) : Term × Bool :=
  (l[v]?).getD (Var (v - l.length), false)

-- walk (Bootstrap/Interp.lean), with its leaf left open: the leaf, its locals,
-- and the arguments left
def walkOpen (bk : Book) : Term → Locals → List MArg → Option (Option (Term × Locals × List MArg))
  | Lam p f, l, (q, x, k) :: xs => if bindsAt p q x then walkOpen bk f ((x, k) :: l) xs else none
  | Prj h, l, (q, Tup r a b, k) :: xs =>
    if q.live then walkOpen bk h l ((Quan.fld r q, a, k && r.live) :: (q, b, k) :: xs) else none
  | Mat j h m, l, (q, Lab i, _) :: xs =>
    if q.live then
      if i = j then walkOpen bk h l xs else walkOpen bk m l ((q, Lab i, true) :: xs)
    else none
  | App q f (Var v), l, xs =>
    if takes (unspine f []).1 then walkOpen bk f l ((q, (localAt l v).1, (localAt l v).2) :: xs)
    else some (some (App q f (Var v), l, xs))
  | t, l, xs =>
    if takes t then if xs.isEmpty then some none else none
    else some (some (t, l, xs))

-- a term with a hole, around the focus
inductive Frame where
  -- App q □ x, with x under l
  | appArg (q : Quan) (x : Term) (l : Locals)
  -- App q □ x, with x known to be a value when k
  | appVal (q : Quan) (x : Term) (k : Bool)
  -- App q f □, with f a value
  | appFun (q : Quan) (f : Term)
  -- Let q □ f, with f under l
  | letIn (q : Quan) (f : Term) (l : Locals)
  -- Tup q □ b, with b under l
  | tupB (q : Quan) (b : Term) (l : Locals)
  -- Tup q a □, with a a value when q is live
  | tupA (q : Quan) (a : Term)
  -- Rwt □ P f, with P and f under l
  | rwt (P f : Term) (l : Locals)
  -- Min □ b, with b under l
  | minB (b : Term) (l : Locals)
  -- Min a □, with a a value
  | minA (a : Term)

-- the frame, with t in its hole
def Frame.plug : Frame → Term → Term
  | .appArg q x l, t => App q t (close x l)
  | .appVal q x _, t => App q t x
  | .appFun q f, t => App q f t
  | .letIn q f l, t => Let q t (sub (Subst.up (subst l)) f)
  | .tupB q b l, t => Tup q t (close b l)
  | .tupA q a, t => Tup q a t
  | .rwt P f l, t => Rwt t (sub (Subst.up (Subst.up (subst l))) P) (close f l)
  | .minB b l, t => Term.Min t (close b l)
  | .minA a, t => Term.Min a t

inductive Focus where
  -- t under l, to evaluate
  | ev (t : Term) (l : Locals)
  -- a value
  | ret (v : Term)

-- the focus, and its frames, the innermost first
structure State where
  focus : Focus
  stack : List Frame

def Focus.term : Focus → Term
  | .ev t l => close t l
  | .ret v => v

-- the frames st around t, the innermost first
def plugs (st : List Frame) (t : Term) : Term := st.foldl (fun t f => f.plug t) t

-- the whole term of the state
def State.term (s : State) : Term := plugs s.stack s.focus.term

def init (t : Term) : State := ⟨.ev t [], []⟩

-- a move: no step of Eval, or one, or none possible
inductive Move where
  | admin (s : State)
  | step (s : State)
  | stop

-- the frames of a spine's arguments, the innermost first
def argFrames (ys : List MArg) : List Frame := ys.map fun (q, y, k) => .appVal q y k

-- a call of k on xs, in the frames st: the leaf of its case tree; or v, a
-- value, when the case tree needs more arguments
def callMove (bk : Book) (k : String) (xs : List MArg) (st : List Frame) (v : Term) : Move :=
  match bk.get k with
  | none => .stop
  | some d =>
    match walkOpen bk d.v [] xs with
    | some (some (t, l, ys)) => .step ⟨.ev t l, argFrames ys ++ st⟩
    | some none => .admin ⟨.ret v, st⟩
    | none => .stop

-- App q f x, in the frames st, with f a value, and x a value when q is live
def appMove (bk : Book) (q : Quan) (f x : Term) (st : List Frame) : Move :=
  match f, x with
  | Lam p b, x => if bindsAt p q x then .step ⟨.ev b [(x, q.live)], st⟩ else .stop
  | Prj h, Tup r a b =>
    if q.live then .step ⟨.ev h [], .appVal (Quan.fld r q) a r.live :: .appVal q b true :: st⟩
    else .stop
  | Mat j h m, Lab i =>
    if q.live then
      if i = j then .step ⟨.ev h [], st⟩ else .step ⟨.ev m [], .appVal q (Lab i) true :: st⟩
    else .stop
  | f, x =>
    match unspine (App q f x) [] with
    | (Ref k, xs) => callMove bk k (xs.map fun (q, y) => (q, y, q.live)) st (App q f x)
    | _ => .stop

def move (bk : Book) : State → Move
  | ⟨.ev t l, st⟩ =>
    match t with
    | Var i =>
      match l[i]? with
      | some (x, true) => .admin ⟨.ret x, st⟩
      | some (x, false) => .admin ⟨.ev x [], st⟩
      | none => .stop
    | Ref k => callMove bk k [] st (Ref k)
    | Ann x _ => .step ⟨.ev x l, st⟩
    | App q f x => .admin ⟨.ev f l, .appArg q x l :: st⟩
    | Let q v f =>
      if q.live then .admin ⟨.ev v l, .letIn q f l :: st⟩
      else .step ⟨.ev f ((close v l, false) :: l), st⟩
    | Tup q a b =>
      if q.live then .admin ⟨.ev a l, .tupB q b l :: st⟩
      else .admin ⟨.ev b l, .tupA q (close a l) :: st⟩
    | Rwt e P f => .admin ⟨.ev e l, .rwt P f l :: st⟩
    | Term.Min a b => .admin ⟨.ev a l, .minB b l :: st⟩
    | t => .admin ⟨.ret (close t l), st⟩
  | ⟨.ret _, []⟩ => .stop
  | ⟨.ret v, f :: st⟩ =>
    match f with
    | .appArg q x l =>
      if q.live then .admin ⟨.ev x l, .appFun q v :: st⟩ else appMove bk q v (close x l) st
    | .appVal q x k =>
      if q.live && !k then .admin ⟨.ev x [], .appFun q v :: st⟩ else appMove bk q v x st
    | .appFun q f => appMove bk q f v st
    | .letIn q f l => if q != Q2 || data v then .step ⟨.ev f ((v, true) :: l), st⟩ else .stop
    | .tupB q b l => .admin ⟨.ev b l, .tupA q v :: st⟩
    | .tupA q a => .admin ⟨.ret (Tup q a v), st⟩
    | .rwt _ f l => if v = Rfl then .step ⟨.ev f l, st⟩ else .stop
    | .minB b l => .admin ⟨.ev b l, .minA v :: st⟩
    | .minA a =>
      match a, v with
      | Lab i, Lab j =>
        if i ∈ QS ∧ j ∈ QS then .step ⟨.ev (Term.qmin (Lab i) (Lab j)) [], st⟩ else .stop
      | _, _ => .stop

-- the moves that a run makes before stepwise takes over: far more than a run
-- can make in practice
def gas : Nat := 2 ^ 60

-- at most fuel more steps of the state s, after n: the term reached, and the
-- steps in all
def run (bk : Book) : Nat → Nat → State → Nat → Term × Nat
  | 0, fuel, s, n => stepwise bk fuel s.term n
  | gas + 1, fuel, s, n =>
    match move bk s with
    | .admin s' => run bk gas fuel s' n
    | .step s' =>
      match fuel with
      | 0 => (s.term, n)
      | fuel + 1 => run bk gas fuel s' (n + 1)
    | .stop => stepwise bk fuel s.term n

end Machine
