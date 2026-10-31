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

# Eval
# ----
#
# A copy of the kernel's Eval: Eval.steps(n, ds, t) gives the term that t
# reaches after exactly n steps, in the book of the defs ds (INVARIANTS #2). It
# follows step of bootstrap/refactor/lean/src/Bootstrap/Interp.lean case for
# case, and works out each part that a case may need before it picks one.

# an argument of a spine, at its quantity
type Arg is Data:
  Arg{q: Quan, x: Term}

def Quan.live(q: Quan) -> Bool:
  match q:
    case Quan.Q0{}:
      False{}
    case Quan.Q1{}:
      True{}
    case Quan.Q2{}:
      True{}

# p and q are both live or both dead
def Quan.lives_as(p: Quan, q: Quan) -> Bool:
  match p q:
    case Quan.Q0{} Quan.Q0{}:
      True{}
    case Quan.Q0{} _:
      False{}
    case _ Quan.Q0{}:
      False{}
    case _ _:
      True{}

# the quantity of a pair's first field, when the pair is used at q
def Quan.fld(r: Quan, q: Quan) -> Quan:
  match r:
    case Quan.Q0{}:
      Quan.Q0{}
    case Quan.Q1{}:
      q
    case Quan.Q2{}:
      Quan.Q2{}

def Name.is_eq(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, xs} Con{y, ys}:
      U32.is_eq(x, y) && Name.is_eq(xs, ys)
    case _ _:
      False{}

def Term.is_data(t: Term) -> Bool:
  match t:
    case Term.Lab{_}:
      True{}
    case Term.Rfl{}:
      True{}
    case Term.Tup{q, a, b}:
      (Bool.not(Quan.live(q)) || Term.is_data(a)) && Term.is_data(b)
    case _:
      False{}

# q may hold v: v is Data when q is 2
def Quan.fits(q: Quan, v: Term) -> Bool:
  match q:
    case Quan.Q2{}:
      Term.is_data(v)
    case _:
      True{}

# a λ of quantity p binds x at quantity q
def Quan.binds(+p: Quan, q: Quan, x: Term) -> Bool:
  Quan.lives_as(p, q) && Quan.fits(p, x)

# a former: a term that is a value by its form
def Term.is_former(t: Term) -> Bool:
  match t:
    case Term.Typ{_}:
      True{}
    case Term.All{_, _, _}:
      True{}
    case Term.Sig{_, _, _}:
      True{}
    case Term.Enu{_}:
      True{}
    case Term.Eql{_, _, _}:
      True{}
    case Term.Lam{_, _}:
      True{}
    case Term.Prj{_}:
      True{}
    case Term.Mat{_, _, _}:
      True{}
    case Term.Efq{}:
      True{}
    case Term.Tup{_, _, _}:
      True{}
    case Term.Lab{_}:
      True{}
    case Term.Rfl{}:
      True{}
    case _:
      False{}

# a λ or a λ-match: a node of a case tree, which takes an argument
def Term.takes(t: Term) -> Bool:
  match t:
    case Term.Lam{_, _}:
      True{}
    case Term.Prj{_}:
      True{}
    case Term.Mat{_, _, _}:
      True{}
    case Term.Efq{}:
      True{}
    case _:
      False{}

# the head of a spine
def Term.head(t: Term) -> Term:
  match t:
    case Term.App{_, f, _}:
      Term.head(f)
    case u:
      u

# the arguments of a spine, in front of xs
def Term.args(t: Term, xs: List<&2, Arg>) -> List<&2, Arg>:
  match t:
    case Term.App{q, f, x}:
      Term.args(f, Con{Arg{q, x}, xs})
    case _:
      xs

# t applied to xs
def Term.spine(xs: List<&2, Arg>, t: Term) -> Term:
  match xs:
    case Nil{}:
      t
    case Con{Arg{q, x}, rest}:
      Term.spine(rest, Term.App{q, t, x})

# the term of the variable i, in e
def Env.sub(e: List<&2, Term>, i: Nat) -> Term:
  match e i:
    case Nil{} j:
      Term.Var{j}
    case Con{x, _} 0n:
      x
    case Con{_, rest} 1n+j:
      Env.sub(rest, j)

def Term.shift.at(lt: Bool, i: Nat, d: Nat) -> Nat:
  match lt:
    case True{}:
      i
    case False{}:
      Nat.add(i, d)

# t with each variable from c on moved up by d
def Term.shift(t: Term, +d: Nat, +c: Nat) -> Term:
  match t:
    case Term.Var{+i}:
      Term.Var{Term.shift.at(Nat.is_lt(i, c), i, d)}
    case Term.Ref{k}:
      Term.Ref{k}
    case Term.Ann{x, T}:
      Term.Ann{Term.shift(x, d, c), Term.shift(T, d, c)}
    case Term.Let{q, v, f}:
      Term.Let{q, Term.shift(v, d, c), Term.shift(f, d, 1n+c)}
    case Term.Typ{q}:
      Term.Typ{Term.shift(q, d, c)}
    case Term.Min{a, b}:
      Term.Min{Term.shift(a, d, c), Term.shift(b, d, c)}
    case Term.All{q, A, B}:
      Term.All{q, Term.shift(A, d, c), Term.shift(B, d, 1n+c)}
    case Term.Lam{q, f}:
      Term.Lam{q, Term.shift(f, d, 1n+c)}
    case Term.App{q, f, x}:
      Term.App{q, Term.shift(f, d, c), Term.shift(x, d, c)}
    case Term.Sig{q, A, B}:
      Term.Sig{q, Term.shift(A, d, c), Term.shift(B, d, 1n+c)}
    case Term.Tup{q, a, b}:
      Term.Tup{q, Term.shift(a, d, c), Term.shift(b, d, c)}
    case Term.Prj{h}:
      Term.Prj{Term.shift(h, d, c)}
    case Term.Enu{ks}:
      Term.Enu{ks}
    case Term.Lab{k}:
      Term.Lab{k}
    case Term.Mat{k, h, m}:
      Term.Mat{k, Term.shift(h, d, c), Term.shift(m, d, c)}
    case Term.Efq{}:
      Term.Efq{}
    case Term.Eql{a, b, T}:
      Term.Eql{Term.shift(a, d, c), Term.shift(b, d, c), Term.shift(T, d, c)}
    case Term.Rfl{}:
      Term.Rfl{}
    case Term.Rwt{e, P, f}:
      Term.Rwt{Term.shift(e, d, c), Term.shift(P, d, 2n+c), Term.shift(f, d, c)}

def Term.lift.at(lt: Bool, i: Nat, v: Term) -> Term:
  match lt:
    case True{}:
      Term.Var{i}
    case False{}:
      v

# the variable i under d binders, with e put in for the free variables
def Term.lift(+e: List<&2, Term>, +d: Nat, +i: Nat) -> Term:
  match d:
    case 0n:
      Env.sub(e, i)
    case 1n+p:
      Term.lift.at(Nat.is_lt(i, 1n+p), i, Term.shift(Env.sub(e, Nat.sub(i, 1n+p)), 1n+p, 0n))

# t under d binders, with e put in for the free variables
def Term.subst(t: Term, +e: List<&2, Term>, +d: Nat) -> Term:
  match t:
    case Term.Var{i}:
      Term.lift(e, d, i)
    case Term.Ref{k}:
      Term.Ref{k}
    case Term.Ann{x, T}:
      Term.Ann{Term.subst(x, e, d), Term.subst(T, e, d)}
    case Term.Let{q, v, f}:
      Term.Let{q, Term.subst(v, e, d), Term.subst(f, e, 1n+d)}
    case Term.Typ{q}:
      Term.Typ{Term.subst(q, e, d)}
    case Term.Min{a, b}:
      Term.Min{Term.subst(a, e, d), Term.subst(b, e, d)}
    case Term.All{q, A, B}:
      Term.All{q, Term.subst(A, e, d), Term.subst(B, e, 1n+d)}
    case Term.Lam{q, f}:
      Term.Lam{q, Term.subst(f, e, 1n+d)}
    case Term.App{q, f, x}:
      Term.App{q, Term.subst(f, e, d), Term.subst(x, e, d)}
    case Term.Sig{q, A, B}:
      Term.Sig{q, Term.subst(A, e, d), Term.subst(B, e, 1n+d)}
    case Term.Tup{q, a, b}:
      Term.Tup{q, Term.subst(a, e, d), Term.subst(b, e, d)}
    case Term.Prj{h}:
      Term.Prj{Term.subst(h, e, d)}
    case Term.Enu{ks}:
      Term.Enu{ks}
    case Term.Lab{k}:
      Term.Lab{k}
    case Term.Mat{k, h, m}:
      Term.Mat{k, Term.subst(h, e, d), Term.subst(m, e, d)}
    case Term.Efq{}:
      Term.Efq{}
    case Term.Eql{a, b, T}:
      Term.Eql{Term.subst(a, e, d), Term.subst(b, e, d), Term.subst(T, e, d)}
    case Term.Rfl{}:
      Term.Rfl{}
    case Term.Rwt{x, P, f}:
      Term.Rwt{Term.subst(x, e, d), Term.subst(P, e, 2n+d), Term.subst(f, e, d)}

# f with v put in for its variable 0
def Term.inst(f: Term, v: Term) -> Term:
  Term.subst(f, Con{v, Nil{}}, 0n)

def Book.get.if(is_k: Bool, d: Def, r: Maybe<Def>) -> Maybe<Def>:
  match is_k:
    case True{}:
      Some{d}
    case False{}:
      r

# the first def of the name k
def Book.get(ds: List<&2, Def>, +k: List<&2, U32>) -> Maybe<Def>:
  match ds:
    case Nil{}:
      None{}
    case Con{Def{+n, T, v, o}, rest}:
      Book.get.if(Name.is_eq(n, k), Def{n, T, v, o}, Book.get(rest, k))

def Eval.walk.if(b: Bool, r: Maybe<Maybe<Term>>) -> Maybe<Maybe<Term>>:
  match b:
    case True{}:
      r
    case False{}:
      None{}

def Eval.walk.pick(b: Bool, r: Maybe<Maybe<Term>>, s: Maybe<Maybe<Term>>) -> Maybe<Maybe<Term>>:
  match b:
    case True{}:
      r
    case False{}:
      s

def Eval.walk.app(node: Bool, r: Maybe<Maybe<Term>>, u: Term) -> Maybe<Maybe<Term>>:
  match node:
    case True{}:
      r
    case False{}:
      Some{Some{u}}

def Eval.walk.leaf(node: Bool, xs: List<&2, Arg>, u: Term) -> Maybe<Maybe<Term>>:
  match node:
    case True{}:
      match xs:
        case Nil{}:
          Some{None{}}
        case _:
          None{}
    case False{}:
      Some{Some{u}}

# the walk of the case tree t on the arguments xs, with e bound: its leaf;
# None{} inside, when it needs more arguments; or None{}, when no walk exists
def Eval.walk(+t: Term, +e: List<&2, Term>, +xs: List<&2, Arg>) -> Maybe<Maybe<Term>>:
  match t xs:
    case Term.Lam{p, f} Con{Arg{q, x}, rest}:
      Eval.walk.if(Quan.binds(p, q, x), Eval.walk(f, Con{x, e}, rest))
    case Term.Prj{h} Con{Arg{q, Term.Tup{r, a, b}}, rest}:
      Eval.walk.if(Quan.live(q), Eval.walk(h, e, Con{Arg{Quan.fld(r, q), a}, Con{Arg{q, b}, rest}}))
    case Term.Mat{k, h, m} Con{Arg{q, Term.Lab{j}}, rest}:
      Eval.walk.if(Quan.live(q), Eval.walk.pick(Name.is_eq(j, k), Eval.walk(h, e, rest), Eval.walk(m, e, Con{Arg{q, Term.Lab{j}}, rest})))
    case Term.App{q, f, Term.Var{v}} ys:
      Eval.walk.app(Term.takes(Term.head(f)), Eval.walk(f, e, Con{Arg{q, Env.sub(e, v)}, ys}), Term.spine(ys, Term.subst(Term.App{q, f, Term.Var{v}}, e, 0n)))
    case u ys:
      Eval.walk.leaf(Term.takes(u), ys, Term.spine(ys, Term.subst(u, e, 0n)))

def Eval.callWalk.def(m: Maybe<Def>, xs: List<&2, Arg>) -> Maybe<Maybe<Term>>:
  match m:
    case None{}:
      None{}
    case Some{Def{_, _, v, _}}:
      Eval.walk(v, Nil{}, xs)

def Eval.callWalk.head(ds: List<&2, Def>, h: Term, xs: List<&2, Arg>) -> Maybe<Maybe<Term>>:
  match h:
    case Term.Ref{k}:
      Eval.callWalk.def(Book.get(ds, k), xs)
    case _:
      None{}

# the walk of a call's case tree on its arguments
def Eval.callWalk(ds: List<&2, Def>, +t: Term) -> Maybe<Maybe<Term>>:
  Eval.callWalk.head(ds, Term.head(t), Term.args(t, Nil{}))

# the walk needs more arguments
def Eval.waits(r: Maybe<Maybe<Term>>) -> Bool:
  match r:
    case Some{None{}}:
      True{}
    case _:
      False{}

def Eval.vals.app(as_args: Bool, ok: Bool, r: Maybe<Maybe<Term>>) -> Bool:
  match as_args:
    case True{}:
      ok
    case False{}:
      ok && Eval.waits(r)

def Eval.vals.ref(as_args: Bool, r: Maybe<Maybe<Term>>) -> Bool:
  match as_args:
    case True{}:
      True{}
    case False{}:
      Eval.waits(r)

def Eval.vals.other(as_args: Bool, former: Bool) -> Bool:
  match as_args:
    case True{}:
      False{}
    case False{}:
      former

# t is a value, or, when as_args, a spine of a def on arguments whose live ones
# are values
def Eval.vals(+ds: List<&2, Def>, +t: Term, as_args: Bool) -> Bool:
  match t:
    case Term.Tup{q, a, b}:
      match as_args:
        case True{}:
          False{}
        case False{}:
          (Bool.not(Quan.live(q)) || Eval.vals(ds, a, False{})) && Eval.vals(ds, b, False{})
    case Term.App{q, f, x}:
      Eval.vals.app(as_args, Eval.vals(ds, f, True{}) && (Bool.not(Quan.live(q)) || Eval.vals(ds, x, False{})), Eval.callWalk(ds, Term.App{q, f, x}))
    case Term.Ref{k}:
      Eval.vals.ref(as_args, Eval.callWalk(ds, Term.Ref{k}))
    case u:
      Eval.vals.other(as_args, Term.is_former(u))

def Eval.call.if(ok: Bool, r: Maybe<Maybe<Term>>) -> Maybe<Term>:
  match ok r:
    case True{} Some{Some{u}}:
      Some{u}
    case _ _:
      None{}

# the step of a call whose case tree takes the whole walk
def Eval.call(+ds: List<&2, Def>, +t: Term) -> Maybe<Term>:
  Eval.call.if(Eval.vals(ds, t, True{}), Eval.callWalk(ds, t))

def Eval.redex.if(b: Bool, u: Term) -> Maybe<Term>:
  match b:
    case True{}:
      Some{u}
    case False{}:
      None{}

def Eval.redex.pick(b: Bool, h: Term, m: Term) -> Term:
  match b:
    case True{}:
      h
    case False{}:
      m

# the step of App q f x, with f a value, and x a value when q is live
def Eval.redex(ds: List<&2, Def>, +q: Quan, +f: Term, +x: Term) -> Maybe<Term>:
  match f x:
    case Term.Lam{p, b} y:
      Eval.redex.if(Quan.binds(p, q, y), Term.inst(b, y))
    case Term.Prj{h} Term.Tup{r, a, b}:
      Eval.redex.if(Quan.live(q), Term.App{q, Term.App{Quan.fld(r, q), h, a}, b})
    case Term.Mat{k, h, m} Term.Lab{j}:
      Eval.redex.if(Quan.live(q), Eval.redex.pick(Name.is_eq(j, k), h, Term.App{q, m, Term.Lab{j}}))
    case g y:
      Eval.call(ds, Term.App{q, g, y})

def Quan.read.if(is_q: Bool, q: Quan, r: Maybe<Quan>) -> Maybe<Quan>:
  match is_q:
    case True{}:
      Some{q}
    case False{}:
      r

# the quantity that a label names: Q0, Q1 or Q2
def Quan.read(+k: List<&2, U32>) -> Maybe<Quan>:
  Quan.read.if(Name.is_eq(k, [81, 48]), Quan.Q0{}, Quan.read.if(Name.is_eq(k, [81, 49]), Quan.Q1{}, Quan.read.if(Name.is_eq(k, [81, 50]), Quan.Q2{}, None{})))

def Quan.name(q: Quan) -> List<&2, U32>:
  match q:
    case Quan.Q0{}:
      [81, 48]
    case Quan.Q1{}:
      [81, 49]
    case Quan.Q2{}:
      [81, 50]

# the least of two quantities: 2 below none, and 0 below all
def Quan.min(p: Quan, q: Quan) -> Quan:
  match p q:
    case Quan.Q2{} r:
      r
    case r Quan.Q2{}:
      r
    case Quan.Q0{} _:
      Quan.Q0{}
    case _ Quan.Q0{}:
      Quan.Q0{}
    case _ _:
      Quan.Q1{}

def Eval.meet.of(i: Maybe<Quan>, j: Maybe<Quan>) -> Maybe<Term>:
  match i j:
    case Some{p} Some{q}:
      Some{Term.Lab{Quan.name(Quan.min(p, q))}}
    case _ _:
      None{}

# the meet of two quantity labels
def Eval.meet(a: Term, b: Term) -> Maybe<Term>:
  match a b:
    case Term.Lab{i} Term.Lab{j}:
      Eval.meet.of(Quan.read(i), Quan.read(j))
    case _ _:
      None{}

# App q f x: the step of f; or, once f is a value, the step of x when q is
# live; or, once x is a value too, the redex r
def Eval.step.app(q: Quan, f: Term, x: Term, sf: Maybe<Term>, vf: Bool, live: Bool, sx: Maybe<Term>, vx: Bool, r: Maybe<Term>) -> Maybe<Term>:
  match sf:
    case Some{f2}:
      Some{Term.App{q, f2, x}}
    case None{}:
      match vf:
        case False{}:
          None{}
        case True{}:
          match live:
            case False{}:
              r
            case True{}:
              match sx:
                case Some{x2}:
                  Some{Term.App{q, f, x2}}
                case None{}:
                  match vx:
                    case True{}:
                      r
                    case False{}:
                      None{}

def Eval.step.unlet(fits: Bool, f: Term, v: Term) -> Maybe<Term>:
  match fits:
    case True{}:
      Some{Term.inst(f, v)}
    case False{}:
      None{}

# Let q v f: the step of v, when q is live; or, once v is a value, f with v put
# in, when q may hold v
def Eval.step.let(q: Quan, v: Term, f: Term, live: Bool, sv: Maybe<Term>, vv: Bool, fits: Bool) -> Maybe<Term>:
  match live:
    case False{}:
      Eval.step.unlet(fits, f, v)
    case True{}:
      match sv:
        case Some{v2}:
          Some{Term.Let{q, v2, f}}
        case None{}:
          match vv:
            case True{}:
              Eval.step.unlet(fits, f, v)
            case False{}:
              None{}

def Eval.step.tup_b(q: Quan, a: Term, sb: Maybe<Term>) -> Maybe<Term>:
  match sb:
    case Some{b2}:
      Some{Term.Tup{q, a, b2}}
    case None{}:
      None{}

# Tup q a b: the step of a, when q is live; or, once a is a value, the step of b
def Eval.step.tup(q: Quan, a: Term, b: Term, live: Bool, sa: Maybe<Term>, va: Bool, sb: Maybe<Term>) -> Maybe<Term>:
  match live:
    case False{}:
      Eval.step.tup_b(q, a, sb)
    case True{}:
      match sa:
        case Some{a2}:
          Some{Term.Tup{q, a2, b}}
        case None{}:
          match va:
            case True{}:
              Eval.step.tup_b(q, a, sb)
            case False{}:
              None{}

def Eval.step.cast(e: Term, f: Term) -> Maybe<Term>:
  match e:
    case Term.Rfl{}:
      Some{f}
    case _:
      None{}

# Rwt e P f: the step of e; or, once e is Rfl, f
def Eval.step.rwt(e: Term, P: Term, f: Term, se: Maybe<Term>, ve: Bool) -> Maybe<Term>:
  match se:
    case Some{e2}:
      Some{Term.Rwt{e2, P, f}}
    case None{}:
      match ve:
        case True{}:
          Eval.step.cast(e, f)
        case False{}:
          None{}

# Min a b: the step of a; or, once a is a value, the step of b; or, once b is
# a value too, their meet m
def Eval.step.min(a: Term, b: Term, sa: Maybe<Term>, va: Bool, sb: Maybe<Term>, vb: Bool, m: Maybe<Term>) -> Maybe<Term>:
  match sa:
    case Some{a2}:
      Some{Term.Min{a2, b}}
    case None{}:
      match va:
        case False{}:
          None{}
        case True{}:
          match sb:
            case Some{b2}:
              Some{Term.Min{a, b2}}
            case None{}:
              match vb:
                case True{}:
                  m
                case False{}:
                  None{}

# one step of Eval
def Eval.step(+ds: List<&2, Def>, +t: Term) -> Maybe<Term>:
  match t:
    case Term.Ann{x, _}:
      Some{x}
    case Term.Ref{k}:
      Eval.call(ds, Term.Ref{k})
    case Term.App{q, f, x}:
      Eval.step.app(q, f, x, Eval.step(ds, f), Eval.vals(ds, f, False{}), Quan.live(q), Eval.step(ds, x), Eval.vals(ds, x, False{}), Eval.redex(ds, q, f, x))
    case Term.Let{q, v, f}:
      Eval.step.let(q, v, f, Quan.live(q), Eval.step(ds, v), Eval.vals(ds, v, False{}), Quan.fits(q, v))
    case Term.Tup{q, a, b}:
      Eval.step.tup(q, a, b, Quan.live(q), Eval.step(ds, a), Eval.vals(ds, a, False{}), Eval.step(ds, b))
    case Term.Rwt{e, P, f}:
      Eval.step.rwt(e, P, f, Eval.step(ds, e), Eval.vals(ds, e, False{}))
    case Term.Min{a, b}:
      Eval.step.min(a, b, Eval.step(ds, a), Eval.vals(ds, a, False{}), Eval.step(ds, b), Eval.vals(ds, b, False{}), Eval.meet(a, b))
    case _:
      None{}

# the state r after n more steps
def Eval.run(n: Nat, +ds: List<&2, Def>, r: Maybe<Term>) -> Maybe<Term>:
  match n r:
    case 0n s:
      s
    case 1n+_ None{}:
      None{}
    case 1n+m Some{t}:
      Eval.run(m, ds, Eval.step(ds, t))

def Eval.steps(n: Nat, ds: List<&2, Def>, t: Term) -> Maybe<Term>:
  Eval.run(n, ds, Some{t})
