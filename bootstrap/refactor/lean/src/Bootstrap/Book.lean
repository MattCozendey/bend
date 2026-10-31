import Bootstrap.Bytes

-- Book
-- ====
--
-- The Bend data form of the kernel's book (bootstrap/refactor/bend/src/book),
-- as `bend -o` writes its values, and the Lean writer of INVARIANTS #5, whose
-- tokens Book.read reads back. That Bend file states the tokens. The writer
-- puts each list last to first, as the reader puts each item in front.

open Quan Term

namespace Form

def name (k : String) : Term := bytes k.toUTF8.toList

def nat : Nat → Term
  | 0 => ctor "Zero" []
  | n + 1 => ctor "Succ" [nat n]

def quan : Quan → Term
  | Q0 => ctor "Quan.Q0" []
  | Q1 => ctor "Quan.Q1" []
  | Q2 => ctor "Quan.Q2" []

def bool (b : Bool) : Term := ctor (if b then "True" else "False") []

def term : Term → Term
  | Var i => ctor "Term.Var" [nat i]
  | Ref k => ctor "Term.Ref" [name k]
  | Ann x T => ctor "Term.Ann" [term x, term T]
  | Let q v f => ctor "Term.Let" [quan q, term v, term f]
  | Typ q => ctor "Term.Typ" [term q]
  | Term.Min a b => ctor "Term.Min" [term a, term b]
  | All q A B => ctor "Term.All" [quan q, term A, term B]
  | Lam q f => ctor "Term.Lam" [quan q, term f]
  | App q f x => ctor "Term.App" [quan q, term f, term x]
  | Sig q A B => ctor "Term.Sig" [quan q, term A, term B]
  | Tup q a b => ctor "Term.Tup" [quan q, term a, term b]
  | Prj h => ctor "Term.Prj" [term h]
  | Enu ks => ctor "Term.Enu" [list (ks.map name)]
  | Lab k => ctor "Term.Lab" [name k]
  | Mat k h m => ctor "Term.Mat" [name k, term h, term m]
  | Efq => ctor "Term.Efq" []
  | Eql a b T => ctor "Term.Eql" [term a, term b, term T]
  | Rfl => ctor "Term.Rfl" []
  | Rwt e P f => ctor "Term.Rwt" [term e, term P, term f]

def defn (d : Def) : Term := ctor "Def" [name d.k, term d.T, term d.v, bool d.o]

def defs (ds : List Def) : Term := list (ds.map defn)

def some (x : Term) : Term := ctor "Some" [x]

end Form

namespace Write

def tok (tag : Nat) (arg : UInt8 := 0) : List UInt8 := [tag.toUInt8, arg]

def name (k : String) : List UInt8 := tok 5 ++ k.toUTF8.toList.reverse.flatMap (tok 6 ·)

def nat : Nat → List UInt8
  | 0 => tok 3
  | n + 1 => nat n ++ tok 4

def quan : Quan → List UInt8
  | Q0 => tok 0
  | Q1 => tok 1
  | Q2 => tok 2

def bool (b : Bool) : List UInt8 := tok (if b then 10 else 9)

def names (ks : List String) : List UInt8 := tok 7 ++ ks.reverse.flatMap (name · ++ tok 8)

def term : Term → List UInt8
  | Var i => nat i ++ tok 14
  | Ref k => name k ++ tok 15
  | Ann x T => term x ++ term T ++ tok 16
  | Let q v f => quan q ++ term v ++ term f ++ tok 17
  | Typ q => term q ++ tok 18
  | Term.Min a b => term a ++ term b ++ tok 19
  | All q A B => quan q ++ term A ++ term B ++ tok 20
  | Lam q f => quan q ++ term f ++ tok 21
  | App q f x => quan q ++ term f ++ term x ++ tok 22
  | Sig q A B => quan q ++ term A ++ term B ++ tok 23
  | Tup q a b => quan q ++ term a ++ term b ++ tok 24
  | Prj h => term h ++ tok 25
  | Enu ks => names ks ++ tok 26
  | Lab k => name k ++ tok 27
  | Mat k h m => name k ++ term h ++ term m ++ tok 28
  | Efq => tok 29
  | Eql a b T => term a ++ term b ++ term T ++ tok 30
  | Rfl => tok 31
  | Rwt e P f => term e ++ term P ++ term f ++ tok 32

def defn (d : Def) : List UInt8 := name d.k ++ term d.T ++ term d.v ++ bool d.o ++ tok 13

end Write

def write (bk : Book) : List UInt8 :=
  Write.tok 11 ++ bk.defs.reverse.flatMap (Write.defn · ++ Write.tok 12)
