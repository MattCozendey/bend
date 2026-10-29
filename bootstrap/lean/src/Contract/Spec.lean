import Kernel

-- Contract.Spec
-- =============
--
-- The contract. It states what a correct compiler does.
-- It holds definitions and claims only. The proofs are in other files.
-- Change this file only after a review. The build pins its hash.
--
-- The claims use the kernel's Eval, Value and Book.check, and the parts below.

open Quan Term

namespace Spec

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
-- - tup0 b: a pair with a dead (q=0) first field. That field is not shown.
inductive Obs where
  | lab (k : String)
  | rfl
  | tup (a b : Obs)
  | tup0 (b : Obs)
  deriving DecidableEq, Repr

-- observe t: the Obs that t shows. It is the same as the kernel's Data:
-- it keeps each live field and drops each dead (q=0) field.
-- It is none when t is not plain data, for example a λ.
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

-- refs t: each def name in t. It reads the live and the dead parts.
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

-- shut bk ks: each name in ks is a def of bk that is not opaque,
-- and its body names only defs in ks.
def shut (bk : Book) (ks : List String) : Bool :=
  ks.all fun k => match bk.get k with
    | some d => !d.o && (refs d.v).all ks.contains
    | none => false

-- Pure bk k: the compiler can run def k. Two conditions must be true:
-- 1. The kernel's checker accepts the type of k as Data (*2).
--    So the result of k is plain data.
-- 2. No opaque def is reachable from the body of k.
--    So Eval never runs a placeholder body.
-- Pure is true only when it finds a shut set of defs that holds k.
-- So it can be false by mistake, but never true by mistake.
def Pure (bk : Book) (k : String) : Bool :=
  match bk.get k with
  | none => false
  | some d =>
    (Term.check bk FUEL [] d.T T2 matches .ok _) &&
      shut bk (grow bk bk.length [k])

-- Bytes
-- =====

-- The CLI gives input as bytes, and can write output as bytes.
-- A byte is a Nat from 0 to 255, in unary: Zero, or Succ of a Nat.
-- A Nat has one form only, so its type fixes its meaning.
-- A list of bytes is a List of Nat: Nil, or Con of a byte and a list.

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

-- RUN: the name of the def that the CLI adds for an input.
def RUN : String := "bootstrap.run"

-- Input.apply bk bs: bk with one more def, RUN = main(bs).
-- It is none when the type of main is not a function type.
-- The kernel checks the new def with the full book.
def Input.apply (bk : Book) (bs : List UInt8) : Option Book :=
  match bk.get "main" with
  | some d =>
    match d.T with
    | All q _ B =>
      let x := Bytes.term bs
      some (Book.of (bk.defs ++ [⟨RUN, Term.inst B x, App q (Ref "main") x, false⟩]))
    | _ => none
  | none => none

-- entry bk input: the book and the def that the CLI runs.
-- - No input: def main of bk.
-- - Input bs: def RUN of Input.apply bk bs.
def entry (bk : Book) : Option (List UInt8) → Option (Book × String)
  | none => some (bk, "main")
  | some bs => (Input.apply bk bs).map (·, RUN)

-- Claims
-- ======

-- Compiler: the parts of a compiler.
-- - Code: the type of its output.
-- - compile bk k: the code for def k of book bk, or an error.
-- - run n code: the result of code, with n steps of fuel.
--   none means no result.
structure Compiler where
  Code : Type
  compile : Book → String → Except String Code
  run : Nat → Code → Option Obs

-- Claim 1, correct. When compile accepts def k of a checked book:
-- 1. Def k is Pure.
-- 2. Def k has a result o (see Answer).
-- 3. With sufficient fuel, run gives o.
-- 4. With all fuel, run gives o or no result. It never gives a wrong result.
def Claim.correct (c : Compiler) : Prop :=
  ∀ bk k code, Book.check bk = .ok () → c.compile bk k = .ok code →
    Pure bk k = true ∧ ∃ o, Answer bk k o ∧
      (∃ n, c.run n code = some o) ∧ (∀ n r, c.run n code = some r → r = o)

-- Claim 2, total. compile accepts each Pure def of a checked book.
-- So Claim 1 is not empty.
def Claim.total (c : Compiler) : Prop :=
  ∀ bk k, Book.check bk = .ok () → Pure bk k = true →
    ∃ code, c.compile bk k = .ok code

-- Claim 3, bytes. Bytes go in and out without change.
-- 1. The input term for bs shows bs.
-- 2. Bytes.ofObs gives bs only for the Obs that the term for bs shows.
--    So output bytes show the result exactly.
def Claim.bytes : Prop :=
  (∀ bs, (observe (Bytes.term bs)).bind Bytes.ofObs = some bs) ∧
  (∀ o bs, Bytes.ofObs o = some bs → observe (Bytes.term bs) = some o)

-- Claim 4, cli. When the CLI gives a result o for book bk and an input:
-- 1. entry gives the book and the def k that the CLI runs.
-- 2. The kernel accepts that book, and def k is Pure.
-- 3. o is the result of def k (see Answer).
def Claim.cli (cli : Book → Option (List UInt8) → Except String Obs) : Prop :=
  ∀ bk input o, cli bk input = .ok o →
    ∃ bk' k, entry bk input = some (bk', k) ∧ Book.check bk' = .ok () ∧
      Pure bk' k = true ∧ Answer bk' k o

-- Claim 5, laws. Each law about def k holds about each value v that Eval
-- reaches from k.
-- - A law is a closed, live, typed proof p of an equality {C(k) == b : A}.
--   C has one hole, Var 0.
-- - "Holds" means: C(v) and b convert.
-- With Claim 4: each law about the def that the CLI runs holds about the
-- value that the CLI shows.
-- This is the kernel's theory, as for --verdict. So a law that names an
-- opaque def holds only for its placeholder body.
def Claim.laws : Prop :=
  ∀ bk k v p C b A, Book.check bk = .ok () → Evals bk (Ref k) v →
    Term.Closed p → Term.Live bk p → Typed bk [] p (Eql (Term.inst C (Ref k)) b A) →
    Conv bk (Term.inst C v) b

end Spec
