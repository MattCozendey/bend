import Base

# Book
# ====
#
# BendTT's book (bend2/bendtt.lean) as Bend data, field for field, and
# Book.read, which reads back the bytes that the Lean writer writes for a book
# (INVARIANTS #5). A name is the list of its UTF-8 bytes.

# Types
# -----
type Quan is Data:
  Quan.Q0{}
  Quan.Q1{}
  Quan.Q2{}

type Term is Data:
  Term.Var{i: Nat}
  Term.Ref{k: List<&2, U32>}
  Term.Ann{x: Term, T: Term}
  Term.Let{q: Quan, v: Term, f: Term}
  Term.Typ{q: Term}
  Term.Min{a: Term, b: Term}
  Term.All{q: Quan, A: Term, B: Term}
  Term.Lam{q: Quan, f: Term}
  Term.App{q: Quan, f: Term, x: Term}
  Term.Sig{q: Quan, A: Term, B: Term}
  Term.Tup{q: Quan, a: Term, b: Term}
  Term.Prj{h: Term}
  Term.Enu{ks: List<&2, List<&2, U32>>}
  Term.Lab{k: List<&2, U32>}
  Term.Mat{k: List<&2, U32>, h: Term, m: Term}
  Term.Efq{}
  Term.Eql{a: Term, b: Term, T: Term}
  Term.Rfl{}
  Term.Rwt{e: Term, P: Term, f: Term}

type Def is Data:
  Def{k: List<&2, U32>, T: Term, v: Term, o: Bool}

# what the reader's stack holds
type Item is Data:
  Item.quan{q: Quan}
  Item.nat{n: Nat}
  Item.name{k: List<&2, U32>}
  Item.names{ks: List<&2, List<&2, U32>>}
  Item.bool{b: Bool}
  Item.term{t: Term}
  Item.def{d: Def}
  Item.defs{ds: List<&2, Def>}

# Reader
# ------
#
# The bytes are tokens of two cells, a tag and an argument, in postfix order: a
# token pushes an item, or pops the fields of a constructor and pushes the
# constructor. Only a name's byte (tag 6) uses its argument. The tags:
#   0 1 2 Q0 Q1 Q2, 3 4 Nat zero and succ, 5 6 a name's nil and byte,
#   7 8 names' nil and cons, 9 10 False True, 11 12 defs' nil and cons, 13 Def,
#   14 to 32 the terms, in the kernel's order Var Ref Ann Let Typ Min All Lam
#   App Sig Tup Prj Enu Lab Mat Efq Eql Rfl Rwt.
def Book.read.succ(st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match st:
    case Con{Item.nat{n}, rest}:
      Some{Con{Item.nat{1n+n}, rest}}
    case _:
      None{}

def Book.read.byte(st: List<&2, Item>, b: U32) -> Maybe<List<&2, Item>>:
  match st:
    case Con{Item.name{k}, rest}:
      Some{Con{Item.name{Con{b, k}}, rest}}
    case _:
      None{}

def Book.read.names(st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match st:
    case Con{Item.name{k}, Con{Item.names{ks}, rest}}:
      Some{Con{Item.names{Con{k, ks}}, rest}}
    case _:
      None{}

def Book.read.defs(st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match st:
    case Con{Item.def{d}, Con{Item.defs{ds}, rest}}:
      Some{Con{Item.defs{Con{d, ds}}, rest}}
    case _:
      None{}

def Book.read.def(st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match st:
    case Con{Item.bool{o}, Con{Item.term{v}, Con{Item.term{T}, Con{Item.name{k}, rest}}}}:
      Some{Con{Item.def{Def{k, T, v, o}}, rest}}
    case _:
      None{}

def Book.read.var(st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match st:
    case Con{Item.nat{i}, rest}:
      Some{Con{Item.term{Term.Var{i}}, rest}}
    case _:
      None{}

def Book.read.ref(st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match st:
    case Con{Item.name{k}, rest}:
      Some{Con{Item.term{Term.Ref{k}}, rest}}
    case _:
      None{}

def Book.read.ann(st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match st:
    case Con{Item.term{T}, Con{Item.term{x}, rest}}:
      Some{Con{Item.term{Term.Ann{x, T}}, rest}}
    case _:
      None{}

def Book.read.let(st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match st:
    case Con{Item.term{f}, Con{Item.term{v}, Con{Item.quan{q}, rest}}}:
      Some{Con{Item.term{Term.Let{q, v, f}}, rest}}
    case _:
      None{}

def Book.read.typ(st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match st:
    case Con{Item.term{q}, rest}:
      Some{Con{Item.term{Term.Typ{q}}, rest}}
    case _:
      None{}

def Book.read.min(st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match st:
    case Con{Item.term{b}, Con{Item.term{a}, rest}}:
      Some{Con{Item.term{Term.Min{a, b}}, rest}}
    case _:
      None{}

def Book.read.all(st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match st:
    case Con{Item.term{B}, Con{Item.term{A}, Con{Item.quan{q}, rest}}}:
      Some{Con{Item.term{Term.All{q, A, B}}, rest}}
    case _:
      None{}

def Book.read.lam(st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match st:
    case Con{Item.term{f}, Con{Item.quan{q}, rest}}:
      Some{Con{Item.term{Term.Lam{q, f}}, rest}}
    case _:
      None{}

def Book.read.app(st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match st:
    case Con{Item.term{x}, Con{Item.term{f}, Con{Item.quan{q}, rest}}}:
      Some{Con{Item.term{Term.App{q, f, x}}, rest}}
    case _:
      None{}

def Book.read.sig(st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match st:
    case Con{Item.term{B}, Con{Item.term{A}, Con{Item.quan{q}, rest}}}:
      Some{Con{Item.term{Term.Sig{q, A, B}}, rest}}
    case _:
      None{}

def Book.read.tup(st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match st:
    case Con{Item.term{b}, Con{Item.term{a}, Con{Item.quan{q}, rest}}}:
      Some{Con{Item.term{Term.Tup{q, a, b}}, rest}}
    case _:
      None{}

def Book.read.prj(st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match st:
    case Con{Item.term{h}, rest}:
      Some{Con{Item.term{Term.Prj{h}}, rest}}
    case _:
      None{}

def Book.read.enu(st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match st:
    case Con{Item.names{ks}, rest}:
      Some{Con{Item.term{Term.Enu{ks}}, rest}}
    case _:
      None{}

def Book.read.lab(st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match st:
    case Con{Item.name{k}, rest}:
      Some{Con{Item.term{Term.Lab{k}}, rest}}
    case _:
      None{}

def Book.read.mat(st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match st:
    case Con{Item.term{m}, Con{Item.term{h}, Con{Item.name{k}, rest}}}:
      Some{Con{Item.term{Term.Mat{k, h, m}}, rest}}
    case _:
      None{}

def Book.read.eql(st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match st:
    case Con{Item.term{T}, Con{Item.term{b}, Con{Item.term{a}, rest}}}:
      Some{Con{Item.term{Term.Eql{a, b, T}}, rest}}
    case _:
      None{}

def Book.read.rwt(st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match st:
    case Con{Item.term{f}, Con{Item.term{P}, Con{Item.term{e}, rest}}}:
      Some{Con{Item.term{Term.Rwt{e, P, f}}, rest}}
    case _:
      None{}

# the token of tag 32 + n
def Book.read.token32(n: Nat, st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match n:
    case 0n:
      Book.read.rwt(st)
    case 1n+_:
      None{}

# the token of tag 24 + n
def Book.read.token24(n: Nat, st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match n:
    case 0n:
      Book.read.tup(st)
    case 1n:
      Book.read.prj(st)
    case 2n:
      Book.read.enu(st)
    case 3n:
      Book.read.lab(st)
    case 4n:
      Book.read.mat(st)
    case 5n:
      Some{Con{Item.term{Term.Efq{}}, st}}
    case 6n:
      Book.read.eql(st)
    case 7n:
      Some{Con{Item.term{Term.Rfl{}}, st}}
    case 8n+p:
      Book.read.token32(p, st)

# the token of tag 16 + n
def Book.read.token16(n: Nat, st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match n:
    case 0n:
      Book.read.ann(st)
    case 1n:
      Book.read.let(st)
    case 2n:
      Book.read.typ(st)
    case 3n:
      Book.read.min(st)
    case 4n:
      Book.read.all(st)
    case 5n:
      Book.read.lam(st)
    case 6n:
      Book.read.app(st)
    case 7n:
      Book.read.sig(st)
    case 8n+p:
      Book.read.token24(p, st)

# the token of tag 8 + n
def Book.read.token8(n: Nat, st: List<&2, Item>) -> Maybe<List<&2, Item>>:
  match n:
    case 0n:
      Book.read.names(st)
    case 1n:
      Some{Con{Item.bool{False{}}, st}}
    case 2n:
      Some{Con{Item.bool{True{}}, st}}
    case 3n:
      Some{Con{Item.defs{Nil{}}, st}}
    case 4n:
      Book.read.defs(st)
    case 5n:
      Book.read.def(st)
    case 6n:
      Book.read.var(st)
    case 7n:
      Book.read.ref(st)
    case 8n+p:
      Book.read.token16(p, st)

# the token of tag n, with its argument b
def Book.read.token(n: Nat, st: List<&2, Item>, b: U32) -> Maybe<List<&2, Item>>:
  match n:
    case 0n:
      Some{Con{Item.quan{Quan.Q0{}}, st}}
    case 1n:
      Some{Con{Item.quan{Quan.Q1{}}, st}}
    case 2n:
      Some{Con{Item.quan{Quan.Q2{}}, st}}
    case 3n:
      Some{Con{Item.nat{0n}, st}}
    case 4n:
      Book.read.succ(st)
    case 5n:
      Some{Con{Item.name{Nil{}}, st}}
    case 6n:
      Book.read.byte(st, b)
    case 7n:
      Some{Con{Item.names{Nil{}}, st}}
    case 8n+p:
      Book.read.token8(p, st)

def Book.read.step(st: Maybe<List<&2, Item>>, tag: U32, b: U32) -> Maybe<List<&2, Item>>:
  match st:
    case None{}:
      None{}
    case Some{s}:
      Book.read.token(U32.to_nat(tag), s, b)

def Book.read.done(st: Maybe<List<&2, Item>>) -> Maybe<List<&2, Def>>:
  match st:
    case Some{Con{Item.defs{ds}, Nil{}}}:
      Some{ds}
    case _:
      None{}

def Book.read.go(xs: List<&2, U32>, st: Maybe<List<&2, Item>>) -> Maybe<List<&2, Def>>:
  match xs:
    case Nil{}:
      Book.read.done(st)
    case Con{_, Nil{}}:
      None{}
    case Con{tag, Con{b, rest}}:
      Book.read.go(rest, Book.read.step(st, tag, b))

def Book.read(xs: List<&2, U32>) -> Maybe<List<&2, Def>>:
  Book.read.go(xs, Some{Nil{}})
