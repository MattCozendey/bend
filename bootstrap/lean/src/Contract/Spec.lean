import Kernel

-- Contract.Spec
-- =============
--
-- The contract: what a correct compiler does. This file holds definitions
-- and claims only. Other files hold the proofs. The build pins its hash, so
-- change it only after a review.
--
-- The claims use the kernel's Eval, Value and Book.check, and the parts below.

open Quan Term

namespace Contract

-- Answer
-- ======

-- Evals bk t u: t becomes u in zero or more Eval steps.
inductive Evals (bk : Book) : Term → Term → Prop
  | refl : Evals bk t t
  | step : Eval bk t u → Evals bk u v → Evals bk t v

-- Obs: the plain data that a result shows.
-- - lab k: the label .k. The unit () is lab "()".
-- - rfl: a proof of an equality.
-- - tup a b: a pair with a live first field.
-- - tup0 b: a pair with a dead (q=0) first field. It does not show that field.
inductive Obs where
  | lab (k : String)
  | rfl
  | tup (a b : Obs)
  | tup0 (b : Obs)
  deriving DecidableEq, Repr

-- observe t: the Obs that t shows, or none when t is not plain data (for
-- example, a λ). It is the kernel's Data: it keeps each live field and drops
-- each dead (q=0) field.
def observe : Term → Option Obs
  | Lab k => some (.lab k)
  | Rfl => some .rfl
  | Tup q a b => do
    let b ← observe b
    if q.live then
      let a ← observe a
      pure (.tup a b)
    else
      pure (.tup0 b)
  | _ => none

-- Answer bk k o: o is the result of def k.
-- 1. A value that Eval reaches from k shows o.
-- 2. Each value that Eval reaches from k shows o. So o is the only result.
def Answer (bk : Book) (k : String) (o : Obs) : Prop :=
  (∃ v, Evals bk (Ref k) v ∧ Value bk v ∧ observe v = some o) ∧
  (∀ v, Evals bk (Ref k) v → Value bk v → observe v = some o)

-- Pure
-- ====

-- refs t: each def name in t, in the live and the dead parts.
def refs : Term → List String
  | Var _ => []
  | Ref k => [k]
  | Ann x T => refs x ++ refs T
  | Let _ v f => refs v ++ refs f
  | Typ q => refs q
  | .Min a b => refs a ++ refs b
  | All _ A B => refs A ++ refs B
  | Lam _ f => refs f
  | App _ f x => refs f ++ refs x
  | Sig _ A B => refs A ++ refs B
  | Tup _ a b => refs a ++ refs b
  | Prj h => refs h
  | Enu _ => []
  | Lab _ => []
  | Mat _ h m => refs h ++ refs m
  | Efq => []
  | Eql a b T => refs a ++ refs b ++ refs T
  | Rfl => []
  | Rwt e P f => refs e ++ refs P ++ refs f

-- grow bk n ks: ks, then the defs that their bodies name, n times.
def grow (bk : Book) : Nat → List String → List String
  | 0, ks => ks
  | n + 1, ks =>
    let new := ks.flatMap fun k => match bk.get k with
      | some d => refs d.v
      | none => []
    grow bk n (ks ++ (new.filter (!ks.contains ·)).eraseDups)

-- shut bk ks: each name in ks is a def of bk that is not opaque, and its body
-- names only defs in ks.
def shut (bk : Book) (ks : List String) : Bool :=
  ks.all fun k => match bk.get k with
    | some d => !d.o && (refs d.v).all ks.contains
    | none => false

-- Pure bk k: the compiler runs def k. Both conditions must be true:
-- 1. The kernel's checker accepts the type of k as Data (*2). So the result
--    of k is plain data.
-- 2. A shut set holds k. So Eval from k meets no opaque def (claim 6). The
--    kernel gives an opaque def only a placeholder model, so its result has
--    no meaning to preserve.
-- Pure can be false by mistake, never true by mistake. It is also false when
-- only a dead part names an opaque def, because refs reads each part.
def Pure (bk : Book) (k : String) : Bool :=
  match bk.get k with
  | none => false
  | some d =>
    (Term.check bk FUEL [] d.T T2 matches .ok _) &&
      shut bk (grow bk bk.length [k])

-- Bytes
-- =====

-- The CLI gives input as bytes, and writes a result as bytes when it can.
-- A byte is a Nat from 0 to 255, in unary: Zero, or Succ of a Nat. A Nat has
-- one form only, so its type fixes its meaning. A list of bytes is a List of
-- Nat: Nil, or Con of a byte and a list.

-- Bytes.nat n: the Nat n as a term.
def Bytes.nat : Nat → Term
  | 0 => Tup Q1 (Lab "Zero") (Lab "()")
  | n + 1 => Tup Q1 (Lab "Succ") (Tup Q1 (Bytes.nat n) (Lab "()"))

-- Bytes.term bs: the list bs as a term.
def Bytes.term : List UInt8 → Term
  | [] => Tup Q1 (Lab "Nil") (Lab "()")
  | b :: bs =>
    Tup Q1 (Lab "Con") (Tup Q1 (Bytes.nat b.toNat) (Tup Q1 (Bytes.term bs) (Lab "()")))

-- Bytes.ofNat o: the number that o shows, when o is a Nat.
def Bytes.ofNat : Obs → Option Nat
  | .tup (.lab "Zero") (.lab "()") => some 0
  | .tup (.lab "Succ") (.tup o (.lab "()")) => (Bytes.ofNat o).map (· + 1)
  | _ => none

-- Bytes.ofObs o: the bytes that o shows, when o is a List of Nat below 256.
def Bytes.ofObs : Obs → Option (List UInt8)
  | .tup (.lab "Nil") (.lab "()") => some []
  | .tup (.lab "Con") (.tup h (.tup t (.lab "()"))) => do
    let n ← Bytes.ofNat h
    if n < 256 then
      let bs ← Bytes.ofObs t
      pure (n.toUInt8 :: bs)
    else
      none
  | _ => none

-- Entry
-- =====

-- INPUT, RUN: the names of the defs that the CLI adds for an input.
def INPUT : String := "bootstrap.input"
def RUN : String := "bootstrap.run"

-- Input.apply bk bs: bk with two more defs, or none when the type of main is
-- not a function type. A is the input type of main.
-- - INPUT : A = bs. So the kernel checks that bs has type A.
-- - RUN = main(INPUT). So the kernel checks bs only once.
-- The kernel checks the new defs with the full book.
def Input.apply (bk : Book) (bs : List UInt8) : Option Book :=
  match bk.get "main" with
  | some d =>
    match d.T with
    | All q A B =>
      some (Book.of (bk.defs ++ [⟨INPUT, A, Bytes.term bs, false⟩,
        ⟨RUN, Term.inst B (Ref INPUT), App q (Ref "main") (Ref INPUT), false⟩]))
    | _ => none
  | none => none

-- entry bk input: the book and the def that the CLI runs.
-- - No input: def main of bk.
-- - Input bs: def RUN of Input.apply bk bs.
def entry (bk : Book) : Option (List UInt8) → Option (Book × String)
  | none => some (bk, "main")
  | some bs => (Input.apply bk bs).map (·, RUN)

-- Instances
-- =========

-- Call dm q x W t: t is the call that a law names for main(x), and main(x)
-- becomes W(t). W has one hole, Var 0. dm is the def main, and q is the
-- quantity of its input.
-- - main(x), and W is the hole.
-- - f(x), when main is λy. f(y), and W is the hole. bend -o puts a path
--   before the names of an imported file, so a law in such a file can name
--   f, but not main.
-- - f(x), when main is λy. g(f(y)), and W is g(hole). The law speaks of
--   f(x); the output is g of it.
inductive Call (dm : Def) (q : Quan) (x : Term) : Term → Term → Prop
  | main : Call dm q x (Var 0) (App q (Ref "main") x)
  | body : dm.v = Lam p (App p' (Ref f) (Var 0)) → Call dm q x (Var 0) (App p' (Ref f) x)
  | inner : dm.v = Lam p (App p' (Ref g) (App p'' (Ref f) (Var 0))) →
      Call dm q x (App p' (Ref g) (Var 0)) (App p'' (Ref f) x)

-- Inst bk P ys R: R is P with its leading ∀ binders (Bend's `for`) filled by
-- ys, in order. Each y is closed and live, and has the type of its binder.
inductive Inst (bk : Book) : Term → List Term → Term → Prop
  | nil : Inst bk P [] P
  | all : Term.Closed y → Term.Live bk y → Typed bk [] y D → Inst bk (Term.inst Q y) ys R →
      Inst bk (All q D Q) (y :: ys) R

-- Claims
-- ======

-- Compiler: the parts of a compiler.
-- - Code: the type of its output.
-- - compile bk k: the code for def k of book bk, or an error.
-- - run n code: the result of code with n steps of fuel, or none (no result).
structure Compiler where
  Code : Type
  compile : Book → String → Except String Code
  run : Nat → Code → Option Obs

-- Claim 1, correct. When compile accepts def k of a checked book:
-- 1. Def k is Pure.
-- 2. Def k has a result o (see Answer).
-- 3. Some fuel makes run give o.
-- 4. At all fuel, run gives o or no result. It never gives a wrong result.
def Claim.correct (c : Compiler) : Prop :=
  ∀ bk k code, Book.check bk = .ok () → c.compile bk k = .ok code →
    Pure bk k = true ∧ ∃ o, Answer bk k o ∧
      (∃ n, c.run n code = some o) ∧ (∀ n r, c.run n code = some r → r = o)

-- Claim 2, total. compile accepts each Pure def of a checked book. So claim 1
-- is not empty.
def Claim.total (c : Compiler) : Prop :=
  ∀ bk k, Book.check bk = .ok () → Pure bk k = true →
    ∃ code, c.compile bk k = .ok code

-- Claim 3, bytes. Bytes go in and out without change.
-- 1. The input term for bs shows bs.
-- 2. Bytes.ofObs gives bs only for the Obs that the term for bs shows. So
--    output bytes show the result exactly.
def Claim.bytes : Prop :=
  (∀ bs, (observe (Bytes.term bs)).bind Bytes.ofObs = some bs) ∧
  (∀ o bs, Bytes.ofObs o = some bs → observe (Bytes.term bs) = some o)

-- Claim 4, cli. cli n bk input: the CLI's result or error, for book bk, an
-- input and n steps of fuel.
-- 1. Sound. When it gives a result o, at any fuel:
--    a. entry gives the book bk' and the def k that the CLI runs.
--    b. The kernel accepts bk, as for --verdict, and bk'. Def k is Pure.
--    c. o is the result of def k (see Answer).
-- 2. Not empty. When entry gives bk' and k, the kernel accepts bk and bk',
--    and def k is Pure, some fuel gives a result.
def Claim.cli (cli : Nat → Book → Option (List UInt8) → Except String Obs) : Prop :=
  (∀ n bk input o, cli n bk input = .ok o →
    ∃ bk' k, entry bk input = some (bk', k) ∧ Book.check bk = .ok () ∧
      Book.check bk' = .ok () ∧ Pure bk' k = true ∧ Answer bk' k o) ∧
  (∀ bk input bk' k, entry bk input = some (bk', k) → Book.check bk = .ok () →
    Book.check bk' = .ok () → Pure bk' k = true → ∃ n o, cli n bk input = .ok o)

-- Claim 5, laws. Each law about def k holds about each value v that Eval
-- reaches from k.
-- - A law is a closed, live, typed proof p of an equality {C(t) == b : A},
--   where t is k or the body of k. C has one hole, Var 0.
-- - "Holds" means: C(v) and b convert.
-- Claim 7 applies this to the input of the CLI.
-- This is the kernel's theory, as for --verdict: an opaque def unfolds to its
-- model. So a law whose C or b names an opaque def holds only for that model.
def Claim.laws : Prop :=
  ∀ bk k t v p C b A, Book.check bk = .ok () →
    (t = Ref k ∨ ∃ d, Book.get bk k = some d ∧ t = d.v) → Evals bk (Ref k) v →
    Term.Closed p → Term.Live bk p → Typed bk [] p (Eql (Term.inst C t) b A) →
    Conv bk (Term.inst C v) b

-- Claim 6, shut. Eval from a Pure def meets no opaque def: each def name in
-- each term that Eval reaches from it names a def that is not opaque.
def Claim.shut : Prop :=
  ∀ bk k v, Pure bk k = true → Evals bk (Ref k) v →
    ∀ j ∈ refs v, ∃ d, Book.get bk j = some d ∧ d.o = false

-- Claim 7, input. When the CLI gives a result o for input bs, each law for all
-- inputs of main holds at bs.
-- - A law for all inputs is a def L : ∀r x:A -> P of bk, where A is the input
--   type of main.
-- - An instance of L fills x with bs, and each further ∀ binder of P with a
--   closed value (see Inst). It is an equality {C(t) == b : T}, where t is
--   main(bs) or the call that main makes (see Call). C has one hole, Var 0.
-- - "Holds at bs" means, for each instance: C(t) and b convert, and W(t)
--   converts with a value v that shows o. When W is the hole, so t and v
--   convert, C(v) and b convert too.
-- It joins claims 4 and 5 for the CLI's own book.
def Claim.input (cli : Nat → Book → Option (List UInt8) → Except String Obs) : Prop :=
  ∀ n bk bs o dm q A B L dL r P, cli n bk (some bs) = .ok o →
    Book.get bk "main" = some dm → dm.T = All q A B → Book.get bk L = some dL →
    dL.T = All r A P →
    ∃ bk' v, entry bk (some bs) = some (bk', RUN) ∧ Evals bk' (Ref RUN) v ∧ Value bk' v ∧
      observe v = some o ∧
      ∀ ys W t C b T, Call dm q (Bytes.term bs) W t →
        Inst bk' (Term.inst P (Bytes.term bs)) ys (Eql (Term.inst C t) b T) →
        Conv bk' (Term.inst W t) v ∧ Conv bk' (Term.inst C t) b

end Contract
