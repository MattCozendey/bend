import Bootstrap.Book

-- Read.Model
-- ==========
--
-- A Lean model of the stack machine of the Bend reader
-- (bootstrap/refactor/bend/src/book), over the terms of its stack items.

open Quan Term

namespace Read

-- the stack item k{x}
def item (k : String) (x : Term) : Term := ctor ("Item." ++ k) [x]

-- x, when the term is the stack item k{x}
def unitem (k : String) : Term → Option Term
  | Tup Q1 (Lab j) (Tup Q1 x (Lab "()")) => if j = "Item." ++ k then some x else none
  | _ => none

-- what the token with the tag t and the argument b does to the stack s:
-- Book.read.token
def token : Nat → UInt8 → List Term → Option (List Term)
  | 0, _, s => some (item "quan" (Form.quan Q0) :: s)
  | 1, _, s => some (item "quan" (Form.quan Q1) :: s)
  | 2, _, s => some (item "quan" (Form.quan Q2) :: s)
  | 3, _, s => some (item "nat" (Form.nat 0) :: s)
  | 4, _, n :: s => return item "nat" (ctor "Succ" [← unitem "nat" n]) :: s
  | 5, _, s => some (item "name" (list []) :: s)
  | 6, b, k :: s => return item "name" (ctor "Con" [cell b, ← unitem "name" k]) :: s
  | 7, _, s => some (item "names" (list []) :: s)
  | 8, _, k :: ks :: s =>
    return item "names" (ctor "Con" [← unitem "name" k, ← unitem "names" ks]) :: s
  | 9, _, s => some (item "bool" (Form.bool false) :: s)
  | 10, _, s => some (item "bool" (Form.bool true) :: s)
  | 11, _, s => some (item "defs" (list []) :: s)
  | 12, _, d :: ds :: s =>
    return item "defs" (ctor "Con" [← unitem "def" d, ← unitem "defs" ds]) :: s
  | 13, _, o :: v :: T :: k :: s =>
    return item "def" (ctor "Def"
      [← unitem "name" k, ← unitem "term" T, ← unitem "term" v, ← unitem "bool" o]) :: s
  | 14, _, i :: s => return item "term" (ctor "Term.Var" [← unitem "nat" i]) :: s
  | 15, _, k :: s => return item "term" (ctor "Term.Ref" [← unitem "name" k]) :: s
  | 16, _, T :: x :: s =>
    return item "term" (ctor "Term.Ann" [← unitem "term" x, ← unitem "term" T]) :: s
  | 17, _, f :: v :: q :: s =>
    return item "term" (ctor "Term.Let"
      [← unitem "quan" q, ← unitem "term" v, ← unitem "term" f]) :: s
  | 18, _, q :: s => return item "term" (ctor "Term.Typ" [← unitem "term" q]) :: s
  | 19, _, b :: a :: s =>
    return item "term" (ctor "Term.Min" [← unitem "term" a, ← unitem "term" b]) :: s
  | 20, _, B :: A :: q :: s =>
    return item "term" (ctor "Term.All"
      [← unitem "quan" q, ← unitem "term" A, ← unitem "term" B]) :: s
  | 21, _, f :: q :: s =>
    return item "term" (ctor "Term.Lam" [← unitem "quan" q, ← unitem "term" f]) :: s
  | 22, _, x :: f :: q :: s =>
    return item "term" (ctor "Term.App"
      [← unitem "quan" q, ← unitem "term" f, ← unitem "term" x]) :: s
  | 23, _, B :: A :: q :: s =>
    return item "term" (ctor "Term.Sig"
      [← unitem "quan" q, ← unitem "term" A, ← unitem "term" B]) :: s
  | 24, _, b :: a :: q :: s =>
    return item "term" (ctor "Term.Tup"
      [← unitem "quan" q, ← unitem "term" a, ← unitem "term" b]) :: s
  | 25, _, h :: s => return item "term" (ctor "Term.Prj" [← unitem "term" h]) :: s
  | 26, _, ks :: s => return item "term" (ctor "Term.Enu" [← unitem "names" ks]) :: s
  | 27, _, k :: s => return item "term" (ctor "Term.Lab" [← unitem "name" k]) :: s
  | 28, _, m :: h :: k :: s =>
    return item "term" (ctor "Term.Mat"
      [← unitem "name" k, ← unitem "term" h, ← unitem "term" m]) :: s
  | 29, _, s => some (item "term" (Form.term Efq) :: s)
  | 30, _, T :: b :: a :: s =>
    return item "term" (ctor "Term.Eql"
      [← unitem "term" a, ← unitem "term" b, ← unitem "term" T]) :: s
  | 31, _, s => some (item "term" (Form.term Rfl) :: s)
  | 32, _, f :: P :: e :: s =>
    return item "term" (ctor "Term.Rwt"
      [← unitem "term" e, ← unitem "term" P, ← unitem "term" f]) :: s
  | _, _, _ => none

-- the stack after the tokens xs, from the stack s: Book.read.go, before its end
def run : List UInt8 → List Term → Option (List Term)
  | t :: b :: xs, s => (token t.toNat b s).bind (run xs)
  | [], s => some s
  | [_], _ => none

-- the defs, when the stack holds just them: Book.read.done
def done : List Term → Option Term
  | [ds] => unitem "defs" ds
  | _ => none

end Read

-- a stack item reads back as its term
theorem unitem_item : Read.unitem k (Read.item k x) = some x := by
  simp [Read.item, ctor, Read.unitem]

-- a term that unitem reads is the stack item it reads
theorem unitem_some : Read.unitem k x = some y → x = Read.item k y := by
  unfold Read.unitem; split
  · split <;> simp_all [Read.item, ctor]
  · simp
