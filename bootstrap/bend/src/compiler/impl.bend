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
# ====
#
# A copy of the kernel's Eval: Eval.steps(n, ds, t) gives the term that t
# reaches after exactly n steps, in the book of the defs ds (INVARIANTS #2). It
# follows step of bootstrap/lean/src/Bootstrap/Interp.lean case for
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

# Wasm
# ====
#
# The part of WebAssembly that our compiler uses (PLAN, WHAT WE TRUST #6), as
# the WebAssembly core spec defines it: W1 to W6, approved by the user.
# Wasm.run(f, w, i, m) runs the module of the bytes w on the input bytes i,
# with at most f steps for each of its two calls and at most m pages (of
# 64 KiB) of memory. A module outside the subset gives unsupported and does
# not run. The subset is in every version of the spec (1.0, 2.0, 3.0); where
# they decode a number with more bits, the model reads the 32 bits of 1.0, so
# it accepts only what every version accepts, and it runs that as every
# version does.

# Types
# -----

# how a run ends (W5)
type Wasm.Outcome is Data:
  Wasm.Outcome.result{bytes: List<&2, U32>}
  Wasm.Outcome.out_of_memory{}
  Wasm.Outcome.no_result{}
  Wasm.Outcome.unsupported{}
  Wasm.Outcome.trap{}
  Wasm.Outcome.not_done{}

# the binary operators on i32 (W2); a comparison gives 1 or 0
type Wasm.Op is Data:
  Wasm.Op.add{}
  Wasm.Op.sub{}
  Wasm.Op.and{}
  Wasm.Op.or{}
  Wasm.Op.shl{}
  Wasm.Op.shr_u{}
  Wasm.Op.eq{}
  Wasm.Op.ne{}
  Wasm.Op.lt_u{}
  Wasm.Op.gt_u{}
  Wasm.Op.le_u{}
  Wasm.Op.ge_u{}

# an instruction (W2); a block or a loop holds its body, and takes and gives
# no values
type Wasm.Instr is Data:
  Wasm.Instr.const{n: U32}
  Wasm.Instr.local_get{i: U32}
  Wasm.Instr.local_set{i: U32}
  Wasm.Instr.local_tee{i: U32}
  Wasm.Instr.op{op: Wasm.Op}
  Wasm.Instr.eqz{}
  Wasm.Instr.load{offset: U32}
  Wasm.Instr.load8_u{offset: U32}
  Wasm.Instr.store{offset: U32}
  Wasm.Instr.store8{offset: U32}
  Wasm.Instr.memory_size{}
  Wasm.Instr.memory_grow{}
  Wasm.Instr.block{body: List<&2, Wasm.Instr>}
  Wasm.Instr.loop{body: List<&2, Wasm.Instr>}
  Wasm.Instr.br{l: U32}
  Wasm.Instr.br_if{l: U32}
  Wasm.Instr.br_table{ls: List<&2, U32>, l: U32}

# a function type: its numbers of i32 parameters and results
type Wasm.Type is Data:
  Wasm.Type{params: Nat, results: Nat}

# a function: its numbers of i32 parameters, results and locals (after the
# parameters), and its body
type Wasm.Func is Data:
  Wasm.Func{params: Nat, results: Nat, locals: Nat, body: List<&2, Wasm.Instr>}

# an export: of a function, by its index, or of the memory
type Wasm.Export is Data:
  Wasm.Export.func{name: List<&2, U32>, index: U32}
  Wasm.Export.memory{name: List<&2, U32>}

# the limits of the memory, in pages
type Wasm.Limits is Data:
  Wasm.Limits{min: U32, max: Maybe<&2, U32>}

# an active data segment of the memory: where it starts, and its bytes
type Wasm.Segment is Data:
  Wasm.Segment{offset: U32, bytes: List<&2, U32>}

# a module of the subset (W3)
type Wasm.Module is Data:
  Wasm.Module{
    funcs: List<&2, Wasm.Func>,
    memory: Maybe<&2, Wasm.Limits>,
    exports: List<&2, Wasm.Export>,
    data: Maybe<&2, Wasm.Segment>}

# Decoding
# --------
#
# The binary format (spec, chapter 5). A decoder takes bytes and gives the
# value that they start with and the bytes after it, or None when they are
# malformed or leave the subset (W3).

# a decoded value and the bytes after it
type Wasm.Decoded<-A: Data> is Data:
  Wasm.Decoded{x: A, rest: List<&2, U32>}

# x, when ok holds
def Wasm.decode.keep(-A: Data, ok: Bool, x: A, rest: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<A>>:
  match ok:
    case True{}:
      Some{Wasm.Decoded{x, rest}}
    case False{}:
      None{}

# a last byte is below 2^7; after a byte that goes on, more decodes the rest
def Wasm.decode.leb.if(
  last: Bool, ok: Bool, x: U32, rest: List<&2, U32>, more: List<&2, U32> -> Maybe<&2, Wasm.Decoded<U32>>
) -> Maybe<&2, Wasm.Decoded<U32>>:
  match last:
    case True{}:
      Wasm.decode.keep(U32, ok, x, rest)
    case False{}:
      more(rest)

# the low 7 bits of the byte b, then the bits of the number after it
def Wasm.decode.leb.more(+b: U32, m: Maybe<&2, Wasm.Decoded<U32>>) -> Maybe<&2, Wasm.Decoded<U32>>:
  match m:
    case None{}:
      None{}
    case Some{Wasm.Decoded{x, rest}}:
      Some{Wasm.Decoded{U32.or(U32.and(b, 127), U32.shln(x, 7n)), rest}}

# uN, an unsigned LEB128 number of at most n bits (spec 5.1):
#   a byte n < 2^7 with n < 2^N is n; a byte n >= 2^7 with N > 7, then
#   m of u(N-7), is 2^7 * m + (n - 2^7)
def Wasm.decode.uleb(n: Nat, bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<U32>>:
  match n bs:
    case _ Nil{}:
      None{}
    case 8n+p Con{+b, rest}:
      Wasm.decode.leb.if(U32.is_lt(b, 128), True{}, b, rest,
        r => Wasm.decode.leb.more(b, Wasm.decode.uleb(1n+p, r)))
    case +k Con{+b, rest}:
      Wasm.decode.leb.if(U32.is_lt(b, 128), U32.is_lt(b, U32.shln(1, k)), b, rest, r => None{})

# a last byte of a signed number of n <= 7 bits: n < 2^6 with n < 2^(N-1)
# is n; 2^6 <= n < 2^7 with n >= 2^7 - 2^(N-1) is n - 2^7
def Wasm.decode.sleb.last(n: Nat, +b: U32) -> Bool:
  +h = U32.shln(1, Nat.sub(n, 1n))
  (U32.is_lt(b, 64) && U32.is_lt(b, h)) || (U32.is_ge(b, 64) && U32.is_ge(b, U32.sub(128, h)))

def Wasm.decode.sleb.pick(low: Bool, b: U32) -> U32:
  match low:
    case True{}:
      b
    case False{}:
      U32.sub(b, 128)

# a last byte below 2^6 stands for itself, one from 2^6 up for b - 2^7
def Wasm.decode.sleb.sign(+b: U32) -> U32:
  Wasm.decode.sleb.pick(U32.is_lt(b, 64), b)

# sN, a signed LEB128 number of at most n bits, as its 32 bits (spec 5.1):
#   the last byte is as in sleb.last; a byte n >= 2^7 with N > 7, then i of
#   s(N-7), is 2^7 * i + (n - 2^7)
def Wasm.decode.sleb(n: Nat, bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<U32>>:
  match n bs:
    case _ Nil{}:
      None{}
    case 8n+p Con{+b, rest}:
      Wasm.decode.leb.if(U32.is_lt(b, 128), True{}, Wasm.decode.sleb.sign(b), rest,
        r => Wasm.decode.leb.more(b, Wasm.decode.sleb(1n+p, r)))
    case +k Con{+b, rest}:
      Wasm.decode.leb.if(U32.is_lt(b, 128), Wasm.decode.sleb.last(k, b), Wasm.decode.sleb.sign(b),
        rest, r => None{})

def Wasm.decode.u32(bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<U32>>:
  Wasm.decode.uleb(32n, bs)

# the byte b, exactly
def Wasm.decode.byte(+b: U32, bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<U32>>:
  match bs:
    case Nil{}:
      None{}
    case Con{+c, rest}:
      Wasm.decode.keep(U32, U32.is_eq(b, c), c, rest)

# the number of bytes, as a U32 when it fits
def Wasm.length32.if(full: Bool, more: Unit -> Maybe<&2, U32>) -> Maybe<&2, U32>:
  match full:
    case True{}:
      None{}
    case False{}:
      more(Unit{})

def Wasm.length32.go(xs: List<&2, U32>, +n: U32) -> Maybe<&2, U32>:
  match xs:
    case Nil{}:
      Some{n}
    case Con{_, rest}:
      Wasm.length32.if(U32.is_eq(n, 4294967295), u => Wasm.length32.go(rest, U32.inc(n)))

def Wasm.length32(xs: List<&2, U32>) -> Maybe<&2, U32>:
  Wasm.length32.go(xs, 0)

# the value of m and the bytes after it, then f of them
def Wasm.decode.bind(
  -A: Data, -B: Data, m: Maybe<&2, Wasm.Decoded<A>>, f: A -> List<&2, U32> -> Maybe<&2, Wasm.Decoded<B>>
) -> Maybe<&2, Wasm.Decoded<B>>:
  match m:
    case None{}:
      None{}
    case Some{Wasm.Decoded{x, rest}}:
      f(x, rest)

# the item x, then the items of m
def Wasm.decode.cons(-A: Data, x: A, m: Maybe<&2, Wasm.Decoded<List<&2, A>>>) -> Maybe<&2, Wasm.Decoded<List<&2, A>>>:
  match m:
    case None{}:
      None{}
    case Some{Wasm.Decoded{xs, rest}}:
      Some{Wasm.Decoded{Con{x, xs}, rest}}

# the value of m, when it takes all of the bytes
def Wasm.decode.done(-A: Data, m: Maybe<&2, Wasm.Decoded<A>>) -> Maybe<&2, A>:
  match m:
    case Some{Wasm.Decoded{x, Nil{}}}:
      Some{x}
    case _:
      None{}

# the value of m, when it takes all of its bytes, then the bytes after
def Wasm.decode.whole(-A: Data, m: Maybe<&2, Wasm.Decoded<A>>, after: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<A>>:
  match m:
    case Some{Wasm.Decoded{x, Nil{}}}:
      Some{Wasm.Decoded{x, after}}
    case _:
      None{}

def Wasm.has.if(zero: Bool, more: Unit -> Bool) -> Bool:
  match zero:
    case True{}:
      True{}
    case False{}:
      more(Unit{})

# xs holds at least n bytes
def Wasm.has(xs: List<&2, U32>, +n: U32) -> Bool:
  match xs:
    case Nil{}:
      U32.is_zero(n)
    case Con{_, rest}:
      Wasm.has.if(U32.is_zero(n), u => Wasm.has(rest, U32.sub(n, 1)))

def Wasm.decode.count.if(ok: Bool, n: U32, rest: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<Nat>>:
  match ok:
    case True{}:
      Some{Wasm.Decoded{U32.to_nat(n), rest}}
    case False{}:
      None{}

# the length of a vector (spec 5.1: list), which counts items of a byte or
# more, so no more than the bytes after it; only then is it made a Nat, as a
# larger one could take as many steps to make as it counts
def Wasm.decode.count(bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<Nat>>:
  Wasm.decode.bind(U32, Nat, Wasm.decode.u32(bs), +n => +r =>
    Wasm.decode.count.if(Wasm.has(r, n), n, r))

# n bytes
def Wasm.decode.take(n: Nat, bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<List<&2, U32>>>:
  match n:
    case 0n:
      Some{Wasm.Decoded{Nil{}, bs}}
    case 1n+p:
      match bs:
        case Nil{}:
          None{}
        case Con{b, rest}:
          Wasm.decode.cons(U32, b, Wasm.decode.take(p, rest))

# n items, each decoded by d
def Wasm.decode.items(
  ~A: Data, ~d: List<&2, U32> -> Maybe<&2, Wasm.Decoded<A>>, n: Nat, bs: List<&2, U32>
) -> Maybe<&2, Wasm.Decoded<List<&2, A>>>:
  match n:
    case 0n:
      Some{Wasm.Decoded{Nil{}, bs}}
    case 1n+p:
      Wasm.decode.bind(A, List<&2, A>, d(bs), x => r => Wasm.decode.cons(A, x, Wasm.decode.items(~A, ~d, p, r)))

# a vector of items, each decoded by d
def Wasm.decode.vec(
  ~A: Data, ~d: List<&2, U32> -> Maybe<&2, Wasm.Decoded<A>>, bs: List<&2, U32>
) -> Maybe<&2, Wasm.Decoded<List<&2, A>>>:
  Wasm.decode.bind(Nat, List<&2, A>, Wasm.decode.count(bs), n => r => Wasm.decode.items(~A, ~d, n, r))

# vec(byte)
def Wasm.decode.bytes(bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<List<&2, U32>>>:
  Wasm.decode.bind(Nat, List<&2, U32>, Wasm.decode.count(bs), n => r => Wasm.decode.take(n, r))

# every byte is ASCII
def Wasm.is_ascii(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{b, rest}:
      U32.is_lt(b, 128) && Wasm.is_ascii(rest)

# a name (spec 5.1); the subset takes ASCII names only, which are UTF-8
def Wasm.decode.name(bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<List<&2, U32>>>:
  Wasm.decode.bind(List<&2, U32>, List<&2, U32>, Wasm.decode.bytes(bs), +xs => r =>
    Wasm.decode.keep(List<&2, U32>, Wasm.is_ascii(xs), xs, r))

# every byte is 0x7F, the value type i32
def Wasm.is_i32s(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{b, rest}:
      U32.is_eq(b, 127) && Wasm.is_i32s(rest)

# a result type (spec 5.2): a vector of value types, all i32 (W2); its length
def Wasm.decode.i32s(bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<Nat>>:
  Wasm.decode.bind(List<&2, U32>, Nat, Wasm.decode.bytes(bs), +xs => r =>
    Wasm.decode.keep(Nat, Wasm.is_i32s(xs), List.length(&2, U32, xs), r))

# a function type (spec 5.2): 0x60, then its parameters' and results' types
def Wasm.decode.functype(bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<Wasm.Type>>:
  Wasm.decode.bind(U32, Wasm.Type, Wasm.decode.byte(96, bs), t => r =>
    Wasm.decode.bind(Nat, Wasm.Type, Wasm.decode.i32s(r), p => r2 =>
      Wasm.decode.bind(Nat, Wasm.Type, Wasm.decode.i32s(r2), q => r3 =>
        Some{Wasm.Decoded{Wasm.Type{p, q}, r3}})))

# the limits after their flag: 0 for a minimum, 1 for a minimum and maximum
def Wasm.decode.limits.of(flag: Nat, bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<Wasm.Limits>>:
  match flag:
    case 0n:
      Wasm.decode.bind(U32, Wasm.Limits, Wasm.decode.u32(bs), n => r =>
        Some{Wasm.Decoded{Wasm.Limits{n, None{}}, r}})
    case 1n:
      Wasm.decode.bind(U32, Wasm.Limits, Wasm.decode.u32(bs), n => r =>
        Wasm.decode.bind(U32, Wasm.Limits, Wasm.decode.u32(r), m => r2 =>
          Some{Wasm.Decoded{Wasm.Limits{n, Some{m}}, r2}}))
    case _:
      None{}

# a memory type (spec 5.2): its limits, of a memory of 32-bit addresses
def Wasm.decode.limits(bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<Wasm.Limits>>:
  match bs:
    case Nil{}:
      None{}
    case Con{flag, rest}:
      Wasm.decode.limits.of(U32.to_nat(flag), rest)

def Wasm.decode.export.kind(
  kind: Nat, name: List<&2, U32>, bs: List<&2, U32>
) -> Maybe<&2, Wasm.Decoded<Wasm.Export>>:
  match kind:
    case 0n:
      Wasm.decode.bind(U32, Wasm.Export, Wasm.decode.u32(bs), i => r =>
        Some{Wasm.Decoded{Wasm.Export.func{name, i}, r}})
    case 2n:
      Wasm.decode.bind(U32, Wasm.Export, Wasm.decode.u32(bs), +i => r =>
        Wasm.decode.keep(Wasm.Export, U32.is_zero(i), Wasm.Export.memory{name}, r))
    case _:
      None{}

# an export's description: 0x00 and a function index, or 0x02 and memory 0
def Wasm.decode.export.of(name: List<&2, U32>, bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<Wasm.Export>>:
  match bs:
    case Nil{}:
      None{}
    case Con{kind, rest}:
      Wasm.decode.export.kind(U32.to_nat(kind), name, rest)

# an export (spec 5.4): a name and a description
def Wasm.decode.export(bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<Wasm.Export>>:
  Wasm.decode.bind(List<&2, U32>, Wasm.Export, Wasm.decode.name(bs), n => r => Wasm.decode.export.of(n, r))

# the head of an instruction: an instruction, the start of a block or a loop,
# or the end of a block
type Wasm.Token is Data:
  Wasm.Token.instr{x: Wasm.Instr}
  Wasm.Token.start{loop: Bool}
  Wasm.Token.end{}

def Wasm.decode.as(x: Wasm.Instr, bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<Wasm.Token>>:
  Some{Wasm.Decoded{Wasm.Token.instr{x}, bs}}

# an instruction with a u32 immediate, which k turns into the instruction
def Wasm.decode.index(k: U32 -> Wasm.Instr, bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<Wasm.Token>>:
  Wasm.decode.bind(U32, Wasm.Token, Wasm.decode.u32(bs), i => r => Wasm.decode.as(k(i), r))

# the start of a block or a loop (spec 5.3): its block type, which must be
# 0x40 (no values, W2)
def Wasm.decode.block(loop: Bool, bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<Wasm.Token>>:
  Wasm.decode.bind(U32, Wasm.Token, Wasm.decode.byte(64, bs), t => r =>
    Some{Wasm.Decoded{Wasm.Token.start{loop}, r}})

# br_table (spec 5.3): a vector of labels, then the default label
def Wasm.decode.table(bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<Wasm.Token>>:
  Wasm.decode.bind(List<&2, U32>, Wasm.Token, Wasm.decode.vec(~U32, ~Wasm.decode.u32, bs), ls => r =>
    Wasm.decode.bind(U32, Wasm.Token, Wasm.decode.u32(r), l => r2 => Wasm.decode.as(Wasm.Instr.br_table{ls, l}, r2)))

def Wasm.decode.memarg.if(ok: Bool, k: U32 -> Wasm.Instr, bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<Wasm.Token>>:
  match ok:
    case True{}:
      Wasm.decode.bind(U32, Wasm.Token, Wasm.decode.u32(bs), o => r => Wasm.decode.as(k(o), r))
    case False{}:
      None{}

# a load or store (spec 5.3): its alignment, as a power of 2 no more than
# max (the access's width; spec 3.4), then its offset; an alignment of 2^6
# or more names another memory, outside the subset
def Wasm.decode.memarg(max: U32, k: U32 -> Wasm.Instr, bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<Wasm.Token>>:
  Wasm.decode.bind(U32, Wasm.Token, Wasm.decode.u32(bs), a => r => Wasm.decode.memarg.if(U32.is_le(a, max), k, r))

# memory.size or memory.grow: memory 0, as the one byte 0x00 of 1.0
def Wasm.decode.memory(x: Wasm.Instr, bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<Wasm.Token>>:
  Wasm.decode.bind(U32, Wasm.Token, Wasm.decode.byte(0, bs), z => r => Wasm.decode.as(x, r))

# i32.const (spec 5.3): a signed 32-bit LEB128 number
def Wasm.decode.const(bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<Wasm.Token>>:
  Wasm.decode.bind(U32, Wasm.Token, Wasm.decode.sleb(32n, bs), n => r => Wasm.decode.as(Wasm.Instr.const{n}, r))

# the head of the instruction of opcode op (spec 5.3), with its immediates
def Wasm.decode.token(op: Nat, bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<Wasm.Token>>:
  match op:
    case 2n:
      Wasm.decode.block(False{}, bs)
    case 3n:
      Wasm.decode.block(True{}, bs)
    case 11n:
      Some{Wasm.Decoded{Wasm.Token.end{}, bs}}
    case 12n:
      Wasm.decode.index(l => Wasm.Instr.br{l}, bs)
    case 13n:
      Wasm.decode.index(l => Wasm.Instr.br_if{l}, bs)
    case 14n:
      Wasm.decode.table(bs)
    case 32n:
      Wasm.decode.index(i => Wasm.Instr.local_get{i}, bs)
    case 33n:
      Wasm.decode.index(i => Wasm.Instr.local_set{i}, bs)
    case 34n:
      Wasm.decode.index(i => Wasm.Instr.local_tee{i}, bs)
    case 40n:
      Wasm.decode.memarg(2, o => Wasm.Instr.load{o}, bs)
    case 45n:
      Wasm.decode.memarg(0, o => Wasm.Instr.load8_u{o}, bs)
    case 54n:
      Wasm.decode.memarg(2, o => Wasm.Instr.store{o}, bs)
    case 58n:
      Wasm.decode.memarg(0, o => Wasm.Instr.store8{o}, bs)
    case 63n:
      Wasm.decode.memory(Wasm.Instr.memory_size{}, bs)
    case 64n:
      Wasm.decode.memory(Wasm.Instr.memory_grow{}, bs)
    case 65n:
      Wasm.decode.const(bs)
    case 69n:
      Wasm.decode.as(Wasm.Instr.eqz{}, bs)
    case 70n:
      Wasm.decode.as(Wasm.Instr.op{Wasm.Op.eq{}}, bs)
    case 71n:
      Wasm.decode.as(Wasm.Instr.op{Wasm.Op.ne{}}, bs)
    case 73n:
      Wasm.decode.as(Wasm.Instr.op{Wasm.Op.lt_u{}}, bs)
    case 75n:
      Wasm.decode.as(Wasm.Instr.op{Wasm.Op.gt_u{}}, bs)
    case 77n:
      Wasm.decode.as(Wasm.Instr.op{Wasm.Op.le_u{}}, bs)
    case 79n:
      Wasm.decode.as(Wasm.Instr.op{Wasm.Op.ge_u{}}, bs)
    case 106n:
      Wasm.decode.as(Wasm.Instr.op{Wasm.Op.add{}}, bs)
    case 107n:
      Wasm.decode.as(Wasm.Instr.op{Wasm.Op.sub{}}, bs)
    case 113n:
      Wasm.decode.as(Wasm.Instr.op{Wasm.Op.and{}}, bs)
    case 114n:
      Wasm.decode.as(Wasm.Instr.op{Wasm.Op.or{}}, bs)
    case 116n:
      Wasm.decode.as(Wasm.Instr.op{Wasm.Op.shl{}}, bs)
    case 118n:
      Wasm.decode.as(Wasm.Instr.op{Wasm.Op.shr_u{}}, bs)
    case _:
      None{}

# an open block: whether it is a loop, and the instructions before it in its
# own block, the last first
type Wasm.Open is Data:
  Wasm.Open{loop: Bool, before: List<&2, Wasm.Instr>}

def Wasm.decode.closed(loop: Bool, body: List<&2, Wasm.Instr>) -> Wasm.Instr:
  match loop:
    case True{}:
      Wasm.Instr.loop{body}
    case False{}:
      Wasm.Instr.block{body}

# an end: of the outermost block, its instructions; of an open block, the
# block joins the instructions before it
def Wasm.decode.instrs.end(
  st: List<&2, Wasm.Open>,
  xs: List<&2, Wasm.Instr>,
  r: List<&2, U32>,
  more: List<&2, U32> -> List<&2, Wasm.Instr> -> List<&2, Wasm.Open> -> Maybe<&2, Wasm.Decoded<List<&2, Wasm.Instr>>>
) -> Maybe<&2, Wasm.Decoded<List<&2, Wasm.Instr>>>:
  match st:
    case Nil{}:
      Some{Wasm.Decoded{List.reverse(&2, Wasm.Instr, xs), r}}
    case Con{Wasm.Open{loop, before}, outer}:
      more(r, Con{Wasm.decode.closed(loop, List.reverse(&2, Wasm.Instr, xs)), before}, outer)

# the next head, after the instructions xs (the last first) of the innermost
# open block, inside the open blocks st (the innermost first)
def Wasm.decode.instrs.then(
  t: Maybe<&2, Wasm.Decoded<Wasm.Token>>,
  xs: List<&2, Wasm.Instr>,
  st: List<&2, Wasm.Open>,
  more: List<&2, U32> -> List<&2, Wasm.Instr> -> List<&2, Wasm.Open> -> Maybe<&2, Wasm.Decoded<List<&2, Wasm.Instr>>>
) -> Maybe<&2, Wasm.Decoded<List<&2, Wasm.Instr>>>:
  match t:
    case None{}:
      None{}
    case Some{Wasm.Decoded{Wasm.Token.instr{x}, r}}:
      more(r, Con{x, xs}, st)
    case Some{Wasm.Decoded{Wasm.Token.start{loop}, r}}:
      more(r, Nil{}, Con{Wasm.Open{loop, xs}, st})
    case Some{Wasm.Decoded{Wasm.Token.end{}, r}}:
      Wasm.decode.instrs.end(st, xs, r, more)

# the instructions up to the end (0x0B) of their block, and the bytes after
# it, one head at a time, as the reader of Book reads its tokens: xs and st
# hold the instructions and open blocks so far. Each head takes a byte or
# more, so fuel of the bytes' length always suffices.
def Wasm.decode.instrs.go(
  fuel: Nat, bs: List<&2, U32>, xs: List<&2, Wasm.Instr>, st: List<&2, Wasm.Open>
) -> Maybe<&2, Wasm.Decoded<List<&2, Wasm.Instr>>>:
  match fuel bs:
    case 0n _:
      None{}
    case 1n+p Nil{}:
      None{}
    case 1n+p Con{op, rest}:
      Wasm.decode.instrs.then(Wasm.decode.token(U32.to_nat(op), rest), xs, st,
        r => ys => st2 => Wasm.decode.instrs.go(p, r, ys, st2))

def Wasm.decode.instrs(fuel: Nat, bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<List<&2, Wasm.Instr>>>:
  Wasm.decode.instrs.go(fuel, bs, Nil{}, Nil{})

# a function's code
type Wasm.Code is Data:
  Wasm.Code{locals: Nat, body: List<&2, Wasm.Instr>}

# a group of locals (spec 5.4): their number, then their type, i32
def Wasm.decode.local(bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<U32>>:
  Wasm.decode.bind(U32, U32, Wasm.decode.u32(bs), n => r =>
    Wasm.decode.bind(U32, U32, Wasm.decode.byte(127, r), t => r2 => Some{Wasm.Decoded{n, r2}}))

def Wasm.locals.if(ok: Bool, more: Unit -> Maybe<&2, U32>) -> Maybe<&2, U32>:
  match ok:
    case True{}:
      more(Unit{})
    case False{}:
      None{}

# the number of locals of the groups ns, from acc: at most 50000, the
# limit of the JS API (engines take no more; the spec allows fewer than 2^32)
def Wasm.locals.sum(ns: List<&2, U32>, +acc: U32) -> Maybe<&2, U32>:
  match ns:
    case Nil{}:
      Some{acc}
    case Con{+n, rest}:
      +s = U32.add(acc, n)
      Wasm.locals.if(U32.is_le(n, 50000) && U32.is_le(s, 50000), u => Wasm.locals.sum(rest, s))

def Wasm.decode.func.body(
  n: Maybe<&2, U32>, +bs: List<&2, U32>
) -> Maybe<&2, Wasm.Decoded<Wasm.Code>>:
  match n:
    case None{}:
      None{}
    case Some{k}:
      Wasm.decode.bind(List<&2, Wasm.Instr>, Wasm.Code, Wasm.decode.instrs(1n+List.length(&2, U32, bs), bs), b => r =>
        Some{Wasm.Decoded{Wasm.Code{U32.to_nat(k), b}, r}})

# a function's code (spec 5.4): its groups of locals, then its body
def Wasm.decode.func(bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<Wasm.Code>>:
  Wasm.decode.bind(List<&2, U32>, Wasm.Code, Wasm.decode.vec(~U32, ~Wasm.decode.local, bs), ns => r =>
    Wasm.decode.func.body(Wasm.locals.sum(ns, 0), r))

# an entry of the code section (spec 5.4): its size, then exactly that many
# bytes of code
def Wasm.decode.code(bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<Wasm.Code>>:
  Wasm.decode.bind(Nat, Wasm.Code, Wasm.decode.count(bs), n => r =>
    Wasm.decode.bind(List<&2, U32>, Wasm.Code, Wasm.decode.take(n, r), c => r2 =>
      Wasm.decode.whole(Wasm.Code, Wasm.decode.func(c), r2)))

def Wasm.decode.data.if(ok: Bool, bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<Wasm.Segment>>:
  match ok:
    case True{}:
      Wasm.decode.bind(U32, Wasm.Segment, Wasm.decode.byte(65, bs), c => r =>
        Wasm.decode.bind(U32, Wasm.Segment, Wasm.decode.sleb(32n, r), k => r2 =>
          Wasm.decode.bind(U32, Wasm.Segment, Wasm.decode.byte(11, r2), e => r3 =>
            Wasm.decode.bind(List<&2, U32>, Wasm.Segment, Wasm.decode.bytes(r3), b => r4 =>
              Some{Wasm.Decoded{Wasm.Segment{k, b}, r4}}))))
    case False{}:
      None{}

# a data segment (spec 5.4): 0, an active one of memory 0, then its offset,
# which in the subset is the constant expression i32.const n end, then its
# bytes
def Wasm.decode.data(bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<Wasm.Segment>>:
  Wasm.decode.bind(U32, Wasm.Segment, Wasm.decode.u32(bs), flag => r => Wasm.decode.data.if(U32.is_zero(flag), r))

# a section (spec 5.4): its id, its size, then exactly that many bytes
type Wasm.Section is Data:
  Wasm.Section{id: U32, content: List<&2, U32>}

def Wasm.decode.section(bs: List<&2, U32>) -> Maybe<&2, Wasm.Decoded<Wasm.Section>>:
  match bs:
    case Nil{}:
      None{}
    case Con{id, rest}:
      Wasm.decode.bind(Nat, Wasm.Section, Wasm.decode.count(rest), n => r =>
        Wasm.decode.bind(List<&2, U32>, Wasm.Section, Wasm.decode.take(n, r), c => r2 =>
          Some{Wasm.Decoded{Wasm.Section{id, c}, r2}}))

def Wasm.decode.sections.cons(x: Wasm.Section, m: Maybe<&2, List<&2, Wasm.Section>>) -> Maybe<&2, List<&2, Wasm.Section>>:
  match m:
    case None{}:
      None{}
    case Some{xs}:
      Some{Con{x, xs}}

def Wasm.decode.sections.got(
  m: Maybe<&2, Wasm.Decoded<Wasm.Section>>, more: List<&2, U32> -> Maybe<&2, List<&2, Wasm.Section>>
) -> Maybe<&2, List<&2, Wasm.Section>>:
  match m:
    case None{}:
      None{}
    case Some{Wasm.Decoded{x, rest}}:
      Wasm.decode.sections.cons(x, more(rest))

# the sections up to the end of the bytes; each takes 2 bytes or more, so
# fuel of the bytes' length always suffices
def Wasm.decode.sections(fuel: Nat, bs: List<&2, U32>) -> Maybe<&2, List<&2, Wasm.Section>>:
  match fuel bs:
    case _ Nil{}:
      Some{Nil{}}
    case 0n Con{_, _}:
      None{}
    case 1n+f Con{b, rest}:
      Wasm.decode.sections.got(Wasm.decode.section(Con{b, rest}), r => Wasm.decode.sections(f, r))

# the subset's sections (W3): 1 type, 3 function, 5 memory, 7 export, 10
# code and 11 data; the spec's order for them is this numeric order
def Wasm.section.is_known(+id: U32) -> Bool:
  U32.is_eq(id, 1) || U32.is_eq(id, 3) || U32.is_eq(id, 5) || U32.is_eq(id, 7) || U32.is_eq(id, 10) || U32.is_eq(id, 11)

# the sections are of the subset, each at most once and in order (spec 5.4)
def Wasm.sections.is_ordered(ss: List<&2, Wasm.Section>, +last: U32) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{Wasm.Section{+id, _}, rest}:
      Wasm.section.is_known(id) && U32.is_gt(id, last) && Wasm.sections.is_ordered(rest, id)

def Wasm.sections.find.if(
  hit: Bool, c: List<&2, U32>, more: Unit -> Maybe<&2, List<&2, U32>>
) -> Maybe<&2, List<&2, U32>>:
  match hit:
    case True{}:
      Some{c}
    case False{}:
      more(Unit{})

# the content of the section of the id, if any
def Wasm.sections.find(ss: List<&2, Wasm.Section>, +id: U32) -> Maybe<&2, List<&2, U32>>:
  match ss:
    case Nil{}:
      None{}
    case Con{Wasm.Section{k, c}, rest}:
      Wasm.sections.find.if(U32.is_eq(k, id), c, u => Wasm.sections.find(rest, id))

# the items of a section (spec 5.4), its whole content; none without it
def Wasm.decode.part(
  ~A: Data, ~d: List<&2, U32> -> Maybe<&2, Wasm.Decoded<A>>, c: Maybe<&2, List<&2, U32>>
) -> Maybe<&2, List<&2, A>>:
  match c:
    case None{}:
      Some{Nil{}}
    case Some{bs}:
      Wasm.decode.done(List<&2, A>, Wasm.decode.vec(~A, ~d, bs))

# at most one item: the subset has one memory and one data segment at most
def Wasm.decode.one(-A: Data, m: Maybe<&2, List<&2, A>>) -> Maybe<&2, Maybe<&2, A>>:
  match m:
    case Some{Nil{}}:
      Some{None{}}
    case Some{Con{x, Nil{}}}:
      Some{Some{x}}
    case _:
      None{}

def Wasm.type.at.if(zero: Bool, t: Wasm.Type, more: Unit -> Maybe<&2, Wasm.Type>) -> Maybe<&2, Wasm.Type>:
  match zero:
    case True{}:
      Some{t}
    case False{}:
      more(Unit{})

# the type of index i
def Wasm.type.at(ts: List<&2, Wasm.Type>, +i: U32) -> Maybe<&2, Wasm.Type>:
  match ts:
    case Nil{}:
      None{}
    case Con{t, rest}:
      Wasm.type.at.if(U32.is_zero(i), t, u => Wasm.type.at(rest, U32.sub(i, 1)))

def Wasm.func.of(t: Maybe<&2, Wasm.Type>, c: Wasm.Code) -> Maybe<&2, Wasm.Func>:
  match t c:
    case None{} _:
      None{}
    case Some{Wasm.Type{p, q}} Wasm.Code{n, b}:
      Some{Wasm.Func{p, q, n, b}}

def Wasm.funcs.cons(f: Maybe<&2, Wasm.Func>, m: Maybe<&2, List<&2, Wasm.Func>>) -> Maybe<&2, List<&2, Wasm.Func>>:
  match f m:
    case Some{x} Some{xs}:
      Some{Con{x, xs}}
    case _ _:
      None{}

# the functions, of the function section's types and the code section's
# codes, one each (spec 5.4)
def Wasm.funcs.of(
  +ts: List<&2, Wasm.Type>, idx: List<&2, U32>, cs: List<&2, Wasm.Code>
) -> Maybe<&2, List<&2, Wasm.Func>>:
  match idx cs:
    case Nil{} Nil{}:
      Some{Nil{}}
    case Con{i, idx2} Con{c, cs2}:
      Wasm.funcs.cons(Wasm.func.of(Wasm.type.at(ts, i), c), Wasm.funcs.of(ts, idx2, cs2))
    case _ _:
      None{}

def Wasm.decode.module.parts(
  +ss: List<&2, Wasm.Section>
) -> Maybe<&2, Wasm.Module>:
  Maybe.bind(&2, List<&2, Wasm.Type>, Wasm.Module, Wasm.decode.part(~Wasm.Type, ~Wasm.decode.functype, Wasm.sections.find(ss, 1)), ts =>
    Maybe.bind(&2, List<&2, U32>, Wasm.Module, Wasm.decode.part(~U32, ~Wasm.decode.u32, Wasm.sections.find(ss, 3)), idx =>
      Maybe.bind(&2, Maybe<&2, Wasm.Limits>, Wasm.Module,
        Wasm.decode.one(Wasm.Limits, Wasm.decode.part(~Wasm.Limits, ~Wasm.decode.limits, Wasm.sections.find(ss, 5))), mem =>
        Maybe.bind(&2, List<&2, Wasm.Export>, Wasm.Module, Wasm.decode.part(~Wasm.Export, ~Wasm.decode.export, Wasm.sections.find(ss, 7)), es =>
          Maybe.bind(&2, List<&2, Wasm.Code>, Wasm.Module, Wasm.decode.part(~Wasm.Code, ~Wasm.decode.code, Wasm.sections.find(ss, 10)), cs =>
            Maybe.bind(&2, Maybe<&2, Wasm.Segment>, Wasm.Module,
              Wasm.decode.one(Wasm.Segment, Wasm.decode.part(~Wasm.Segment, ~Wasm.decode.data, Wasm.sections.find(ss, 11))), seg =>
              Maybe.bind(&2, List<&2, Wasm.Func>, Wasm.Module, Wasm.funcs.of(ts, idx, cs), fs =>
                Some{Wasm.Module{fs, mem, es, seg}})))))))

def Wasm.decode.module.if(ok: Bool, +ss: List<&2, Wasm.Section>) -> Maybe<&2, Wasm.Module>:
  match ok:
    case True{}:
      Wasm.decode.module.parts(ss)
    case False{}:
      None{}

def Wasm.decode.module.sections(m: Maybe<&2, List<&2, Wasm.Section>>) -> Maybe<&2, Wasm.Module>:
  match m:
    case None{}:
      None{}
    case Some{+ss}:
      Wasm.decode.module.if(Wasm.sections.is_ordered(ss, 0), ss)

# the sections after a right header
def Wasm.decode.sections.if(ok: Bool, +rest: List<&2, U32>) -> Maybe<&2, List<&2, Wasm.Section>>:
  match ok:
    case True{}:
      Wasm.decode.sections(List.length(&2, U32, rest), rest)
    case False{}:
      None{}

def Wasm.decode.module.header(m: Maybe<&2, Wasm.Decoded<List<&2, U32>>>) -> Maybe<&2, Wasm.Module>:
  match m:
    case None{}:
      None{}
    case Some{Wasm.Decoded{h, +rest}}:
      Wasm.decode.module.sections(
        Wasm.decode.sections.if(Name.is_eq(h, [0, 97, 115, 109, 1, 0, 0, 0]), rest))

# a module (spec 5.4): the magic \0asm, version 1, then its sections
def Wasm.decode.module(bs: List<&2, U32>) -> Maybe<&2, Wasm.Module>:
  Wasm.decode.module.header(Wasm.decode.take(8n, bs))

# Validation
# ----------
#
# The spec's rules for the subset's instructions (spec 3.4) and modules
# (spec 3.5). Every value is an i32, so a type is a number of values: a
# label's type is the number of values that a branch to it takes.

# a stack's height at the end of instructions, relative to their block's
# start, or any after a branch
type Wasm.Height is Data:
  Wasm.Height.at{h: Nat}
  Wasm.Height.any{}

def Wasm.valid.if(ok: Bool, more: Unit -> Maybe<&2, Wasm.Height>) -> Maybe<&2, Wasm.Height>:
  match ok:
    case True{}:
      more(Unit{})
    case False{}:
      None{}

def Wasm.valid.label.if(zero: Bool, a: Nat, more: Unit -> Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match zero:
    case True{}:
      Some{a}
    case False{}:
      more(Unit{})

# the type of the label l, from the innermost
def Wasm.valid.label(labels: List<&2, Nat>, +l: U32) -> Maybe<&2, Nat>:
  match labels:
    case Nil{}:
      None{}
    case Con{a, rest}:
      Wasm.valid.label.if(U32.is_zero(l), a, u => Wasm.valid.label(rest, U32.sub(l, 1)))

# a block's body ends with no values left, or after a branch
def Wasm.valid.is_empty(m: Maybe<&2, Wasm.Height>) -> Bool:
  match m:
    case Some{Wasm.Height.at{0n}}:
      True{}
    case Some{Wasm.Height.any{}}:
      True{}
    case _:
      False{}

# br l takes the label's values
def Wasm.valid.br(a: Maybe<&2, Nat>, h: Nat) -> Bool:
  match a:
    case None{}:
      False{}
    case Some{k}:
      Nat.is_ge(h, k)

# br_if l takes the label's values and the condition, and leaves the values
def Wasm.valid.br_if(a: Maybe<&2, Nat>, h: Nat) -> Bool:
  match a:
    case None{}:
      False{}
    case Some{k}:
      Nat.is_ge(h, 1n+k)

def Wasm.valid.is_type(a: Maybe<&2, Nat>, k: Nat) -> Bool:
  match a:
    case None{}:
      False{}
    case Some{j}:
      Nat.is_eq(j, k)

# every label of ls has the type k
def Wasm.valid.table.all(+labels: List<&2, Nat>, ls: List<&2, U32>, +k: Nat) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{l, rest}:
      Wasm.valid.is_type(Wasm.valid.label(labels, l), k) && Wasm.valid.table.all(labels, rest, k)

# br_table ls l: its labels all have the default label's type, and it takes
# their values and the index
def Wasm.valid.table(+labels: List<&2, Nat>, ls: List<&2, U32>, a: Maybe<&2, Nat>, h: Nat) -> Bool:
  match a:
    case None{}:
      False{}
    case Some{+k}:
      Nat.is_ge(h, 1n+k) && Wasm.valid.table.all(labels, ls, k)

# the instructions xs from the height h: the height at their end, or None
# when they are invalid; labels holds the labels' types, innermost first,
# locals the number of locals, and mem says the module has a memory. The
# subset takes no instruction after br or br_table in their block (W4).
def Wasm.valid.go(
  xs: List<&2, Wasm.Instr>, +h: Nat, +labels: List<&2, Nat>, +locals: U32, +mem: Bool
) -> Maybe<&2, Wasm.Height>:
  match xs:
    case Nil{}:
      Some{Wasm.Height.at{h}}
    case Con{Wasm.Instr.const{_}, rest}:
      Wasm.valid.go(rest, 1n+h, labels, locals, mem)
    case Con{Wasm.Instr.local_get{i}, rest}:
      Wasm.valid.if(U32.is_lt(i, locals), u => Wasm.valid.go(rest, 1n+h, labels, locals, mem))
    case Con{Wasm.Instr.local_set{i}, rest}:
      Wasm.valid.if(U32.is_lt(i, locals) && Nat.is_ge(h, 1n), u => Wasm.valid.go(rest, Nat.sub(h, 1n), labels, locals, mem))
    case Con{Wasm.Instr.local_tee{i}, rest}:
      Wasm.valid.if(U32.is_lt(i, locals) && Nat.is_ge(h, 1n), u => Wasm.valid.go(rest, h, labels, locals, mem))
    case Con{Wasm.Instr.op{_}, rest}:
      Wasm.valid.if(Nat.is_ge(h, 2n), u => Wasm.valid.go(rest, Nat.sub(h, 1n), labels, locals, mem))
    case Con{Wasm.Instr.eqz{}, rest}:
      Wasm.valid.if(Nat.is_ge(h, 1n), u => Wasm.valid.go(rest, h, labels, locals, mem))
    case Con{Wasm.Instr.load{_}, rest}:
      Wasm.valid.if(mem && Nat.is_ge(h, 1n), u => Wasm.valid.go(rest, h, labels, locals, mem))
    case Con{Wasm.Instr.load8_u{_}, rest}:
      Wasm.valid.if(mem && Nat.is_ge(h, 1n), u => Wasm.valid.go(rest, h, labels, locals, mem))
    case Con{Wasm.Instr.store{_}, rest}:
      Wasm.valid.if(mem && Nat.is_ge(h, 2n), u => Wasm.valid.go(rest, Nat.sub(h, 2n), labels, locals, mem))
    case Con{Wasm.Instr.store8{_}, rest}:
      Wasm.valid.if(mem && Nat.is_ge(h, 2n), u => Wasm.valid.go(rest, Nat.sub(h, 2n), labels, locals, mem))
    case Con{Wasm.Instr.memory_size{}, rest}:
      Wasm.valid.if(mem, u => Wasm.valid.go(rest, 1n+h, labels, locals, mem))
    case Con{Wasm.Instr.memory_grow{}, rest}:
      Wasm.valid.if(mem && Nat.is_ge(h, 1n), u => Wasm.valid.go(rest, h, labels, locals, mem))
    case Con{Wasm.Instr.block{body}, rest}:
      Wasm.valid.if(Wasm.valid.is_empty(Wasm.valid.go(body, 0n, Con{0n, labels}, locals, mem)),
        u => Wasm.valid.go(rest, h, labels, locals, mem))
    case Con{Wasm.Instr.loop{body}, rest}:
      Wasm.valid.if(Wasm.valid.is_empty(Wasm.valid.go(body, 0n, Con{0n, labels}, locals, mem)),
        u => Wasm.valid.go(rest, h, labels, locals, mem))
    case Con{Wasm.Instr.br{l}, rest}:
      Wasm.valid.if(Wasm.valid.br(Wasm.valid.label(labels, l), h) && List.is_empty(&2, Wasm.Instr, rest),
        u => Some{Wasm.Height.any{}})
    case Con{Wasm.Instr.br_if{l}, rest}:
      Wasm.valid.if(Wasm.valid.br_if(Wasm.valid.label(labels, l), h),
        u => Wasm.valid.go(rest, Nat.sub(h, 1n), labels, locals, mem))
    case Con{Wasm.Instr.br_table{ls, l}, rest}:
      Wasm.valid.if(Wasm.valid.table(labels, ls, Wasm.valid.label(labels, l), h) && List.is_empty(&2, Wasm.Instr, rest),
        u => Some{Wasm.Height.any{}})

# a function's body ends with its results, or after a branch
def Wasm.valid.is_results(m: Maybe<&2, Wasm.Height>, q: Nat) -> Bool:
  match m:
    case Some{Wasm.Height.at{h}}:
      Nat.is_eq(h, q)
    case Some{Wasm.Height.any{}}:
      True{}
    case _:
      False{}

# a function (spec 3.5): its locals are its parameters, then its locals;
# its body's label, and its end, take its results
def Wasm.valid.func(+mem: Bool, f: Wasm.Func) -> Bool:
  match f:
    case Wasm.Func{p, +q, n, body}:
      Wasm.valid.is_results(Wasm.valid.go(body, 0n, [q], U32.from_nat(Nat.add(p, n)), mem), q)

def Wasm.valid.funcs(+mem: Bool, fs: List<&2, Wasm.Func>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{f, rest}:
      Wasm.valid.func(mem, f) && Wasm.valid.funcs(mem, rest)

# memory limits (spec 3.2): at most 2^16 pages, the minimum no more than the
# maximum
def Wasm.valid.max(+min: U32, max: Maybe<&2, U32>) -> Bool:
  match max:
    case None{}:
      True{}
    case Some{+k}:
      U32.is_le(k, 65536) && U32.is_le(min, k)

def Wasm.valid.memory(m: Maybe<&2, Wasm.Limits>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Wasm.Limits{+min, max}}:
      U32.is_le(min, 65536) && Wasm.valid.max(min, max)

def Wasm.export.name(e: Wasm.Export) -> List<&2, U32>:
  match e:
    case Wasm.Export.func{n, _}:
      n
    case Wasm.Export.memory{n}:
      n

# no export of es is named n
def Wasm.valid.is_new(+n: List<&2, U32>, es: List<&2, Wasm.Export>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, rest}:
      Bool.not(Name.is_eq(n, Wasm.export.name(e))) && Wasm.valid.is_new(n, rest)

# exports (spec 3.5): of a function that exists, or of the memory when there
# is one, each with its own name
def Wasm.valid.exports(es: List<&2, Wasm.Export>, +funcs: U32, +mem: Bool) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{Wasm.Export.func{+n, i}, +rest}:
      U32.is_lt(i, funcs) && Wasm.valid.is_new(n, rest) && Wasm.valid.exports(rest, funcs, mem)
    case Con{Wasm.Export.memory{+n}, +rest}:
      mem && Wasm.valid.is_new(n, rest) && Wasm.valid.exports(rest, funcs, mem)

# a data segment needs a memory (spec 3.5)
def Wasm.valid.data(seg: Maybe<&2, Wasm.Segment>, mem: Bool) -> Bool:
  match seg:
    case None{}:
      True{}
    case Some{_}:
      mem

# a module (spec 3.5)
def Wasm.valid.module(m: Wasm.Module) -> Bool:
  match m:
    case Wasm.Module{+fs, +memory, es, seg}:
      +mem = Maybe.is_some(&2, Wasm.Limits, memory)
      Wasm.valid.memory(memory) && Wasm.valid.funcs(mem, fs) &&
        Wasm.valid.exports(es, U32.from_nat(List.length(&2, Wasm.Func, fs)), mem) && Wasm.valid.data(seg, mem)

# Running
# -------
#
# Execution (spec 4.4): one step per instruction, and one more at the end
# of each block.

# the bytes of a memory: a tree over the 32 bits of an address, lowest bit
# first; zero stands for bytes that are all 0
type Wasm.Bytes is Data:
  Wasm.Bytes.zero{}
  Wasm.Bytes.byte{b: U32}
  Wasm.Bytes.node{lo: Wasm.Bytes, hi: Wasm.Bytes}

# a byte read, and the bytes that it was read from
type Wasm.Peek is Data:
  Wasm.Peek{b: U32, m: Wasm.Bytes}

def Wasm.Bytes.peek.lo(r: Wasm.Peek, hi: Wasm.Bytes) -> Wasm.Peek:
  match r:
    case Wasm.Peek{b, lo}:
      Wasm.Peek{b, Wasm.Bytes.node{lo, hi}}

def Wasm.Bytes.peek.hi(lo: Wasm.Bytes, r: Wasm.Peek) -> Wasm.Peek:
  match r:
    case Wasm.Peek{b, hi}:
      Wasm.Peek{b, Wasm.Bytes.node{lo, hi}}

# the byte at the address of the n bits w, and the bytes again
def Wasm.Bytes.peek(n: Nat, w: Word(n), m: Wasm.Bytes) -> Wasm.Peek:
  match n:
    case 0n:
      match m:
        case Wasm.Bytes.byte{+b}:
          Wasm.Peek{b, Wasm.Bytes.byte{b}}
        case Wasm.Bytes.zero{}:
          Wasm.Peek{0, Wasm.Bytes.zero{}}
        case Wasm.Bytes.node{lo, hi}:
          Wasm.Peek{0, Wasm.Bytes.node{lo, hi}}
    case 1n+p:
      match w:
        case WCon{bit, t}:
          match bit:
            case False{}:
              match m:
                case Wasm.Bytes.node{lo, hi}:
                  Wasm.Bytes.peek.lo(Wasm.Bytes.peek(p, t, lo), hi)
                case Wasm.Bytes.zero{}:
                  Wasm.Peek{0, Wasm.Bytes.zero{}}
                case Wasm.Bytes.byte{b}:
                  Wasm.Peek{0, Wasm.Bytes.byte{b}}
            case True{}:
              match m:
                case Wasm.Bytes.node{lo, hi}:
                  Wasm.Bytes.peek.hi(lo, Wasm.Bytes.peek(p, t, hi))
                case Wasm.Bytes.zero{}:
                  Wasm.Peek{0, Wasm.Bytes.zero{}}
                case Wasm.Bytes.byte{b}:
                  Wasm.Peek{0, Wasm.Bytes.byte{b}}

# the bytes with b at the address of the n bits w
def Wasm.Bytes.set(n: Nat, w: Word(n), m: Wasm.Bytes, b: U32) -> Wasm.Bytes:
  match n:
    case 0n:
      Wasm.Bytes.byte{b}
    case 1n+p:
      match w:
        case WCon{bit, t}:
          match bit:
            case False{}:
              match m:
                case Wasm.Bytes.node{lo, hi}:
                  Wasm.Bytes.node{Wasm.Bytes.set(p, t, lo, b), hi}
                case _:
                  Wasm.Bytes.node{Wasm.Bytes.set(p, t, Wasm.Bytes.zero{}, b), Wasm.Bytes.zero{}}
            case True{}:
              match m:
                case Wasm.Bytes.node{lo, hi}:
                  Wasm.Bytes.node{lo, Wasm.Bytes.set(p, t, hi, b)}
                case _:
                  Wasm.Bytes.node{Wasm.Bytes.zero{}, Wasm.Bytes.set(p, t, Wasm.Bytes.zero{}, b)}

def Wasm.read8(m: Wasm.Bytes, a: U32) -> Wasm.Peek:
  match a:
    case U32{w}:
      Wasm.Bytes.peek(32n, w, m)

def Wasm.write8(m: Wasm.Bytes, a: U32, b: U32) -> Wasm.Bytes:
  match a:
    case U32{w}:
      Wasm.Bytes.set(32n, w, m, b)

def Wasm.read32.b3(v: U32, r: Wasm.Peek) -> Wasm.Peek:
  match r:
    case Wasm.Peek{b, m}:
      Wasm.Peek{U32.or(v, U32.shln(b, 24n)), m}

def Wasm.read32.b2(v: U32, r: Wasm.Peek, +a: U32) -> Wasm.Peek:
  match r:
    case Wasm.Peek{b, m}:
      Wasm.read32.b3(U32.or(v, U32.shln(b, 16n)), Wasm.read8(m, U32.add(a, 3)))

def Wasm.read32.b1(v: U32, r: Wasm.Peek, +a: U32) -> Wasm.Peek:
  match r:
    case Wasm.Peek{b, m}:
      Wasm.read32.b2(U32.or(v, U32.shln(b, 8n)), Wasm.read8(m, U32.add(a, 2)), a)

def Wasm.read32.b0(r: Wasm.Peek, +a: U32) -> Wasm.Peek:
  match r:
    case Wasm.Peek{b, m}:
      Wasm.read32.b1(b, Wasm.read8(m, U32.add(a, 1)), a)

# the 4 bytes from a, lowest first (spec 4.4.7: little-endian), and the bytes
def Wasm.read32(m: Wasm.Bytes, +a: U32) -> Wasm.Peek:
  Wasm.read32.b0(Wasm.read8(m, a), a)

def Wasm.write32(m: Wasm.Bytes, +a: U32, +v: U32) -> Wasm.Bytes:
  Wasm.write8(
    Wasm.write8(
      Wasm.write8(Wasm.write8(m, a, U32.and(v, 255)), U32.add(a, 1), U32.and(U32.shrn(v, 8n), 255)),
      U32.add(a, 2), U32.and(U32.shrn(v, 16n), 255)),
    U32.add(a, 3), U32.shrn(v, 24n))

def Wasm.read.bytes.of(r: Wasm.Peek, more: Wasm.Bytes -> List<&2, U32>) -> List<&2, U32>:
  match r:
    case Wasm.Peek{b, m}:
      Con{b, more(m)}

# the n bytes from a
def Wasm.read.bytes(n: Nat, m: Wasm.Bytes, +a: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Wasm.read.bytes.of(Wasm.read8(m, a), m2 => Wasm.read.bytes(p, m2, U32.inc(a)))

# the bytes xs, written from a on
def Wasm.write.bytes(xs: List<&2, U32>, +a: U32, m: Wasm.Bytes) -> Wasm.Bytes:
  match xs:
    case Nil{}:
      m
    case Con{x, rest}:
      Wasm.write.bytes(rest, U32.inc(a), Wasm.write8(m, a, x))

# len bytes from start fit in p pages of 2^16 bytes
def Wasm.fits(+p: U32, +start: U32, +len: U32) -> Bool:
  +end = U32.add(start, len)
  Bool.not(U32.is_lt(end, start)) && (U32.is_zero(end) || U32.is_lt(U32.shrn(U32.sub(end, 1), 16n), p))

# an access of w bytes at a + o is inside the memory of p pages (spec 4.4.7);
# the sum a + o does not wrap
def Wasm.inside(+p: U32, +a: U32, +o: U32, w: U32) -> Bool:
  +ea = U32.add(a, o)
  Bool.not(U32.is_lt(ea, a)) && Wasm.fits(p, ea, w)

# a binary operator on i32 (spec 4.3.2); a shift is by its count mod 32
def Wasm.op(o: Wasm.Op, +a: U32, +b: U32) -> U32:
  match o:
    case Wasm.Op.add{}:
      U32.add(a, b)
    case Wasm.Op.sub{}:
      U32.sub(a, b)
    case Wasm.Op.and{}:
      U32.and(a, b)
    case Wasm.Op.or{}:
      U32.or(a, b)
    case Wasm.Op.shl{}:
      U32.shln(a, U32.to_nat(U32.and(b, 31)))
    case Wasm.Op.shr_u{}:
      U32.shrn(a, U32.to_nat(U32.and(b, 31)))
    case Wasm.Op.eq{}:
      Bool.to_u32(U32.is_eq(a, b))
    case Wasm.Op.ne{}:
      Bool.to_u32(U32.is_ne(a, b))
    case Wasm.Op.lt_u{}:
      Bool.to_u32(U32.is_lt(a, b))
    case Wasm.Op.gt_u{}:
      Bool.to_u32(U32.is_gt(a, b))
    case Wasm.Op.le_u{}:
      Bool.to_u32(U32.is_le(a, b))
    case Wasm.Op.ge_u{}:
      Bool.to_u32(U32.is_ge(a, b))

# a memory (spec 4.2): its size and the limit of its growth, in pages, and
# its bytes
type Wasm.Memory is Data:
  Wasm.Memory{pages: U32, limit: U32, bytes: Wasm.Bytes}

# a label (spec 4.2): for a loop, its body, which a branch runs again; the
# instructions after its block; and the stack's height when it began
type Wasm.Label is Data:
  Wasm.Label{loop: Maybe<&2, List<&2, Wasm.Instr>>, rest: List<&2, Wasm.Instr>, height: Nat}

# a running function (spec 4.2): the instructions left in its innermost
# block, its labels (innermost first), its number of results, its stack (top
# first) and its locals
type Wasm.Frame is Data:
  Wasm.Frame{
    code: List<&2, Wasm.Instr>,
    labels: List<&2, Wasm.Label>,
    results: Nat,
    stack: List<&2, U32>,
    locals: List<&2, U32>}

# the result of a step: the next frame, the function's results, or a trap,
# with the memory's state
type Wasm.Step is Data:
  Wasm.Step.next{f: Wasm.Frame, mem: Wasm.Memory}
  Wasm.Step.done{results: List<&2, U32>, mem: Wasm.Memory}
  Wasm.Step.trap{mem: Wasm.Memory}

# the end of a block (spec 4.4.8): its label goes, and the instructions after
# it run; at the end of the function, it gives its results
def Wasm.step.end(
  labels: List<&2, Wasm.Label>, +results: Nat, stack: List<&2, U32>, locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match labels:
    case Nil{}:
      Wasm.Step.done{List.take(&2, U32, stack, results), mem}
    case Con{Wasm.Label{_, after, _}, outer}:
      Wasm.Step.next{Wasm.Frame{after, outer, results, stack, locals}, mem}

def Wasm.step.br.to(
  loop: Maybe<&2, List<&2, Wasm.Instr>>,
  after: List<&2, Wasm.Instr>,
  h: Nat,
  outer: List<&2, Wasm.Label>,
  results: Nat,
  kept: List<&2, U32>,
  locals: List<&2, U32>,
  mem: Wasm.Memory
) -> Wasm.Step:
  match loop:
    case None{}:
      Wasm.Step.next{Wasm.Frame{after, outer, results, kept, locals}, mem}
    case Some{+body}:
      Wasm.Step.next{Wasm.Frame{body, Con{Wasm.Label{Some{body}, after, h}, outer}, results, kept, locals}, mem}

# a branch (spec 4.4.8) to the first label of ls: to the end of its block, or
# to the start of its loop again, with the stack cut to the label's height;
# past every label, the function returns its results
def Wasm.step.br(
  ls: List<&2, Wasm.Label>, +results: Nat, +stack: List<&2, U32>, locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match ls:
    case Nil{}:
      Wasm.Step.done{List.take(&2, U32, stack, results), mem}
    case Con{Wasm.Label{loop, after, +h}, outer}:
      Wasm.step.br.to(loop, after, h, outer, results,
        List.drop(&2, U32, stack, Nat.sub(List.length(&2, U32, stack), h)), locals, mem)

def Wasm.step.set(
  i: U32, rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat, stack: List<&2, U32>,
  locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match stack:
    case Con{v, s}:
      Wasm.Step.next{Wasm.Frame{rest, labels, results, s, List.set(&2, U32, locals, U32.to_nat(i), v)}, mem}
    case Nil{}:
      Wasm.Step.trap{mem}

def Wasm.step.tee(
  i: U32, rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat, stack: List<&2, U32>,
  locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match stack:
    case Con{+v, s}:
      Wasm.Step.next{Wasm.Frame{rest, labels, results, Con{v, s}, List.set(&2, U32, locals, U32.to_nat(i), v)}, mem}
    case Nil{}:
      Wasm.Step.trap{mem}

def Wasm.step.op(
  o: Wasm.Op, rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat, stack: List<&2, U32>,
  locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match stack:
    case Con{b, Con{a, s}}:
      Wasm.Step.next{Wasm.Frame{rest, labels, results, Con{Wasm.op(o, a, b), s}, locals}, mem}
    case _:
      Wasm.Step.trap{mem}

def Wasm.step.eqz(
  rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat, stack: List<&2, U32>,
  locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match stack:
    case Con{a, s}:
      Wasm.Step.next{Wasm.Frame{rest, labels, results, Con{Bool.to_u32(U32.is_zero(a)), s}, locals}, mem}
    case Nil{}:
      Wasm.Step.trap{mem}

def Wasm.load.of(wide: Bool, m: Wasm.Bytes, a: U32) -> Wasm.Peek:
  match wide:
    case True{}:
      Wasm.read32(m, a)
    case False{}:
      Wasm.read8(m, a)

def Wasm.step.peeked(
  r: Wasm.Peek, p: U32, lim: U32, rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat,
  s: List<&2, U32>, locals: List<&2, U32>
) -> Wasm.Step:
  match r:
    case Wasm.Peek{v, bytes}:
      Wasm.Step.next{Wasm.Frame{rest, labels, results, Con{v, s}, locals}, Wasm.Memory{p, lim, bytes}}

def Wasm.step.loaded(
  ok: Bool, wide: Bool, ea: U32, rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat,
  s: List<&2, U32>, locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match ok:
    case True{}:
      match mem:
        case Wasm.Memory{p, lim, bytes}:
          Wasm.step.peeked(Wasm.load.of(wide, bytes, ea), p, lim, rest, labels, results, s, locals)
    case False{}:
      Wasm.Step.trap{mem}

# i32.load or i32.load8_u (spec 4.4.7): the w bytes at the address plus the
# offset o, or a trap when they are outside the memory
def Wasm.step.load(
  +o: U32, +w: U32, rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat,
  stack: List<&2, U32>, locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match stack:
    case Con{+a, s}:
      match mem:
        case Wasm.Memory{+p, lim, bytes}:
          Wasm.step.loaded(Wasm.inside(p, a, o, w), U32.is_eq(w, 4), U32.add(a, o),
            rest, labels, results, s, locals, Wasm.Memory{p, lim, bytes})
    case Nil{}:
      Wasm.Step.trap{mem}

def Wasm.store.of(wide: Bool, m: Wasm.Bytes, a: U32, v: U32) -> Wasm.Bytes:
  match wide:
    case True{}:
      Wasm.write32(m, a, v)
    case False{}:
      Wasm.write8(m, a, U32.and(v, 255))

def Wasm.step.stored(
  ok: Bool, wide: Bool, ea: U32, v: U32, rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>,
  results: Nat, s: List<&2, U32>, locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match ok:
    case True{}:
      match mem:
        case Wasm.Memory{p, lim, bytes}:
          Wasm.Step.next{Wasm.Frame{rest, labels, results, s, locals}, Wasm.Memory{p, lim, Wasm.store.of(wide, bytes, ea, v)}}
    case False{}:
      Wasm.Step.trap{mem}

# i32.store or i32.store8 (spec 4.4.7): the value's w low bytes at the
# address plus the offset o, or a trap when they are outside the memory
def Wasm.step.store(
  +o: U32, +w: U32, rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat,
  stack: List<&2, U32>, locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match stack:
    case Con{v, Con{+a, s}}:
      match mem:
        case Wasm.Memory{+p, lim, bytes}:
          Wasm.step.stored(Wasm.inside(p, a, o, w), U32.is_eq(w, 4), U32.add(a, o), v,
            rest, labels, results, s, locals, Wasm.Memory{p, lim, bytes})
    case _:
      Wasm.Step.trap{mem}

# memory.size (spec 4.4.7): the size, in pages
def Wasm.step.size(
  rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat, stack: List<&2, U32>,
  locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match mem:
    case Wasm.Memory{+p, lim, bytes}:
      Wasm.Step.next{Wasm.Frame{rest, labels, results, Con{p, stack}, locals}, Wasm.Memory{p, lim, bytes}}

def Wasm.step.grown(
  ok: Bool, p: U32, n: U32, lim: U32, bytes: Wasm.Bytes, rest: List<&2, Wasm.Instr>,
  labels: List<&2, Wasm.Label>, results: Nat, s: List<&2, U32>, locals: List<&2, U32>
) -> Wasm.Step:
  match ok:
    case True{}:
      Wasm.Step.next{Wasm.Frame{rest, labels, results, Con{p, s}, locals}, Wasm.Memory{n, lim, bytes}}
    case False{}:
      Wasm.Step.next{Wasm.Frame{rest, labels, results, Con{4294967295, s}, locals}, Wasm.Memory{p, lim, bytes}}

# memory.grow (spec 4.4.7): by d pages, when the new size is within the
# limit, giving the old size; else -1, with no change
def Wasm.step.grow(
  rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat, stack: List<&2, U32>,
  locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match stack:
    case Con{d, s}:
      match mem:
        case Wasm.Memory{+p, +lim, bytes}:
          +n = U32.add(p, d)
          Wasm.step.grown(U32.is_ge(n, p) && U32.is_le(n, lim), p, n, lim, bytes, rest, labels, results, s, locals)
    case Nil{}:
      Wasm.Step.trap{mem}

def Wasm.step.br_if.if(
  zero: Bool, l: U32, rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat,
  s: List<&2, U32>, locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match zero:
    case True{}:
      Wasm.Step.next{Wasm.Frame{rest, labels, results, s, locals}, mem}
    case False{}:
      Wasm.step.br(List.drop(&2, Wasm.Label, labels, U32.to_nat(l)), results, s, locals, mem)

# br_if l (spec 4.4.8): a branch to l unless the value is 0
def Wasm.step.br_if(
  l: U32, rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat, stack: List<&2, U32>,
  locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match stack:
    case Con{c, s}:
      Wasm.step.br_if.if(U32.is_zero(c), l, rest, labels, results, s, locals, mem)
    case Nil{}:
      Wasm.Step.trap{mem}

def Wasm.table.pick.if(zero: Bool, x: U32, more: Unit -> U32) -> U32:
  match zero:
    case True{}:
      x
    case False{}:
      more(Unit{})

# the label of br_table ls l for the index i (spec 4.4.8): the i-th of ls,
# or l past them
def Wasm.table.pick(ls: List<&2, U32>, +i: U32, l: U32) -> U32:
  match ls:
    case Nil{}:
      l
    case Con{x, rest}:
      Wasm.table.pick.if(U32.is_zero(i), x, u => Wasm.table.pick(rest, U32.sub(i, 1), l))

def Wasm.step.table(
  ls: List<&2, U32>, l: U32, labels: List<&2, Wasm.Label>, results: Nat, stack: List<&2, U32>,
  locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match stack:
    case Con{i, s}:
      Wasm.step.br(List.drop(&2, Wasm.Label, labels, U32.to_nat(Wasm.table.pick(ls, i, l))), results, s, locals, mem)
    case Nil{}:
      Wasm.Step.trap{mem}

# one step of the instruction x, with the instructions rest after it in its
# block (spec 4.4)
def Wasm.step.instr(
  x: Wasm.Instr, rest: List<&2, Wasm.Instr>, labels: List<&2, Wasm.Label>, results: Nat,
  +stack: List<&2, U32>, +locals: List<&2, U32>, mem: Wasm.Memory
) -> Wasm.Step:
  match x:
    case Wasm.Instr.const{n}:
      Wasm.Step.next{Wasm.Frame{rest, labels, results, Con{n, stack}, locals}, mem}
    case Wasm.Instr.local_get{i}:
      Wasm.Step.next{Wasm.Frame{rest, labels, results,
        Con{Maybe.default(&2, U32, List.get(&2, U32, locals, U32.to_nat(i)), 0), stack}, locals}, mem}
    case Wasm.Instr.local_set{i}:
      Wasm.step.set(i, rest, labels, results, stack, locals, mem)
    case Wasm.Instr.local_tee{i}:
      Wasm.step.tee(i, rest, labels, results, stack, locals, mem)
    case Wasm.Instr.op{o}:
      Wasm.step.op(o, rest, labels, results, stack, locals, mem)
    case Wasm.Instr.eqz{}:
      Wasm.step.eqz(rest, labels, results, stack, locals, mem)
    case Wasm.Instr.load{o}:
      Wasm.step.load(o, 4, rest, labels, results, stack, locals, mem)
    case Wasm.Instr.load8_u{o}:
      Wasm.step.load(o, 1, rest, labels, results, stack, locals, mem)
    case Wasm.Instr.store{o}:
      Wasm.step.store(o, 4, rest, labels, results, stack, locals, mem)
    case Wasm.Instr.store8{o}:
      Wasm.step.store(o, 1, rest, labels, results, stack, locals, mem)
    case Wasm.Instr.memory_size{}:
      Wasm.step.size(rest, labels, results, stack, locals, mem)
    case Wasm.Instr.memory_grow{}:
      Wasm.step.grow(rest, labels, results, stack, locals, mem)
    case Wasm.Instr.block{body}:
      Wasm.Step.next{Wasm.Frame{body,
        Con{Wasm.Label{None{}, rest, List.length(&2, U32, stack)}, labels}, results, stack, locals}, mem}
    case Wasm.Instr.loop{+body}:
      Wasm.Step.next{Wasm.Frame{body,
        Con{Wasm.Label{Some{body}, rest, List.length(&2, U32, stack)}, labels}, results, stack, locals}, mem}
    case Wasm.Instr.br{l}:
      Wasm.step.br(List.drop(&2, Wasm.Label, labels, U32.to_nat(l)), results, stack, locals, mem)
    case Wasm.Instr.br_if{l}:
      Wasm.step.br_if(l, rest, labels, results, stack, locals, mem)
    case Wasm.Instr.br_table{ls, l}:
      Wasm.step.table(ls, l, labels, results, stack, locals, mem)

# one step of a running function
def Wasm.step(f: Wasm.Frame, mem: Wasm.Memory) -> Wasm.Step:
  match f:
    case Wasm.Frame{code, labels, results, stack, locals}:
      match code:
        case Nil{}:
          Wasm.step.end(labels, results, stack, locals, mem)
        case Con{x, rest}:
          Wasm.step.instr(x, rest, labels, results, stack, locals, mem)

# how a call ends: its results and the memory; a trap, with the memory; or
# no end within the fuel
type Wasm.Call is Data:
  Wasm.Call.done{results: List<&2, U32>, mem: Wasm.Memory}
  Wasm.Call.trap{mem: Wasm.Memory}
  Wasm.Call.not_done{}

def Wasm.call.stepped(s: Wasm.Step, more: Wasm.Frame -> Wasm.Memory -> Wasm.Call) -> Wasm.Call:
  match s:
    case Wasm.Step.next{f, m}:
      more(f, m)
    case Wasm.Step.done{rs, m}:
      Wasm.Call.done{rs, m}
    case Wasm.Step.trap{m}:
      Wasm.Call.trap{m}

# the steps of a running function, one per unit of fuel
def Wasm.call.go(fuel: Nat, f: Wasm.Frame, mem: Wasm.Memory) -> Wasm.Call:
  match fuel:
    case 0n:
      Wasm.Call.not_done{}
    case 1n+k:
      Wasm.call.stepped(Wasm.step(f, mem), g => m => Wasm.call.go(k, g, m))

# a call of the function to the arguments, in order (spec 4.4.10): its locals
# are the arguments, then its own locals at 0
def Wasm.call(fuel: Nat, func: Wasm.Func, args: List<&2, U32>, mem: Wasm.Memory) -> Wasm.Call:
  match func:
    case Wasm.Func{_, q, n, body}:
      Wasm.call.go(fuel, Wasm.Frame{body, Nil{}, q, Nil{}, List.append(&2, U32, args, List.replicate(U32, n, 0))}, mem)

# Instances
# ---------
#
# Instantiation (spec 4.5.4) and invocation (spec 4.5.5), as the host does
# them: the spec's own tests use these.

# an instance (spec 4.2): its module, and the state of its memory
type Wasm.Instance is Data:
  Wasm.Instance{module: Wasm.Module, mem: Wasm.Memory}

# how an instantiation ends
type Wasm.Made is Data:
  Wasm.Made.instance{i: Wasm.Instance}
  Wasm.Made.unsupported{}
  Wasm.Made.out_of_memory{}
  Wasm.Made.trap{}

def Wasm.min.if(le: Bool, a: U32, b: U32) -> U32:
  match le:
    case True{}:
      a
    case False{}:
      b

def Wasm.min(+a: U32, +b: U32) -> U32:
  Wasm.min.if(U32.is_le(a, b), a, b)

# the limit of a memory's growth: its maximum, if any, at most m pages, and
# at most 2^16 pages (4 GiB)
def Wasm.limit(max: Maybe<&2, U32>, +m: U32) -> U32:
  Wasm.min(Maybe.default(&2, U32, max, 65536), Wasm.min(m, 65536))

def Wasm.memory.of.if(ok: Bool, mem: Wasm.Memory) -> Maybe<&2, Wasm.Memory>:
  match ok:
    case True{}:
      Some{mem}
    case False{}:
      None{}

# the memory of the limits, at its minimum, when that fits in m pages; a
# module without one gets a memory of no pages, which it cannot use
def Wasm.memory.of(l: Maybe<&2, Wasm.Limits>, +m: U32) -> Maybe<&2, Wasm.Memory>:
  match l:
    case None{}:
      Some{Wasm.Memory{0, 0, Wasm.Bytes.zero{}}}
    case Some{Wasm.Limits{+min, max}}:
      Wasm.memory.of.if(U32.is_le(min, m), Wasm.Memory{min, Wasm.limit(max, m), Wasm.Bytes.zero{}})

def Wasm.fits.len(+p: U32, +k: U32, n: Maybe<&2, U32>) -> Bool:
  match n:
    case None{}:
      False{}
    case Some{len}:
      Wasm.fits(p, k, len)

def Wasm.memory.init.if(ok: Bool, p: U32, lim: U32, bytes: Wasm.Bytes) -> Maybe<&2, Wasm.Memory>:
  match ok:
    case True{}:
      Some{Wasm.Memory{p, lim, bytes}}
    case False{}:
      None{}

# the memory with the data segment's bytes from its offset (spec 4.5.4), or
# None, a trap, when they do not fit
def Wasm.memory.init(seg: Maybe<&2, Wasm.Segment>, mem: Wasm.Memory) -> Maybe<&2, Wasm.Memory>:
  match seg:
    case None{}:
      Some{mem}
    case Some{Wasm.Segment{+k, +xs}}:
      match mem:
        case Wasm.Memory{+p, lim, bytes}:
          Wasm.memory.init.if(Wasm.fits.len(p, k, Wasm.length32(xs)), p, lim, Wasm.write.bytes(xs, k, bytes))

def Wasm.instantiate.made(m: Maybe<&2, Wasm.Memory>, module: Wasm.Module) -> Wasm.Made:
  match m:
    case None{}:
      Wasm.Made.trap{}
    case Some{mem}:
      Wasm.Made.instance{Wasm.Instance{module, mem}}

def Wasm.instantiate.sized(m: Maybe<&2, Wasm.Memory>, seg: Maybe<&2, Wasm.Segment>, module: Wasm.Module) -> Wasm.Made:
  match m:
    case None{}:
      Wasm.Made.out_of_memory{}
    case Some{mem}:
      Wasm.instantiate.made(Wasm.memory.init(seg, mem), module)

def Wasm.instantiate.valid(ok: Bool, module: Wasm.Module, +m: U32) -> Wasm.Made:
  match ok:
    case False{}:
      Wasm.Made.unsupported{}
    case True{}:
      match module:
        case Wasm.Module{fs, +memory, es, +seg}:
          Wasm.instantiate.sized(Wasm.memory.of(memory, m), seg, Wasm.Module{fs, memory, es, seg})

def Wasm.instantiate.decoded(m: Maybe<&2, Wasm.Module>, +lim: U32) -> Wasm.Made:
  match m:
    case None{}:
      Wasm.Made.unsupported{}
    case Some{+module}:
      Wasm.instantiate.valid(Wasm.valid.module(module), module, lim)

# an instance of the module of the bytes w, with at most m pages of memory
def Wasm.instantiate(w: List<&2, U32>, m: U32) -> Wasm.Made:
  Wasm.instantiate.decoded(Wasm.decode.module(w), m)

def Wasm.export.find.if(hit: Bool, i: U32, more: Unit -> Maybe<&2, U32>) -> Maybe<&2, U32>:
  match hit:
    case True{}:
      Some{i}
    case False{}:
      more(Unit{})

# the index of the function exported as name
def Wasm.export.find(es: List<&2, Wasm.Export>, +name: List<&2, U32>) -> Maybe<&2, U32>:
  match es:
    case Nil{}:
      None{}
    case Con{Wasm.Export.func{n, i}, rest}:
      Wasm.export.find.if(Name.is_eq(n, name), i, u => Wasm.export.find(rest, name))
    case Con{Wasm.Export.memory{_}, rest}:
      Wasm.export.find(rest, name)

# the memory is exported as name
def Wasm.export.has_memory(es: List<&2, Wasm.Export>, +name: List<&2, U32>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case Con{Wasm.Export.memory{n}, rest}:
      Name.is_eq(n, name) || Wasm.export.has_memory(rest, name)
    case Con{Wasm.Export.func{_, _}, rest}:
      Wasm.export.has_memory(rest, name)

def Wasm.func.at.if(zero: Bool, f: Wasm.Func, more: Unit -> Maybe<&2, Wasm.Func>) -> Maybe<&2, Wasm.Func>:
  match zero:
    case True{}:
      Some{f}
    case False{}:
      more(Unit{})

# the function of index i
def Wasm.func.at(fs: List<&2, Wasm.Func>, +i: U32) -> Maybe<&2, Wasm.Func>:
  match fs:
    case Nil{}:
      None{}
    case Con{f, rest}:
      Wasm.func.at.if(U32.is_zero(i), f, u => Wasm.func.at(rest, U32.sub(i, 1)))

# the function exported as name, if any
def Wasm.export.func(+fs: List<&2, Wasm.Func>, es: List<&2, Wasm.Export>, name: List<&2, U32>) -> Maybe<&2, Wasm.Func>:
  Maybe.bind(&2, U32, Wasm.Func, Wasm.export.find(es, name), i => Wasm.func.at(fs, i))

# the function has p parameters and q results
def Wasm.func.is_type(f: Maybe<&2, Wasm.Func>, p: Nat, q: Nat) -> Bool:
  match f:
    case None{}:
      False{}
    case Some{Wasm.Func{a, b, _, _}}:
      Nat.is_eq(a, p) && Nat.is_eq(b, q)

# how an invocation ends: its results, with the instance after it; a trap,
# with the instance after it; no end within the fuel; or no such function
type Wasm.Invoked is Data:
  Wasm.Invoked.values{vs: List<&2, U32>, i: Wasm.Instance}
  Wasm.Invoked.trap{i: Wasm.Instance}
  Wasm.Invoked.not_done{}
  Wasm.Invoked.unsupported{}

def Wasm.invoked(c: Wasm.Call, module: Wasm.Module) -> Wasm.Invoked:
  match c:
    case Wasm.Call.done{vs, mem}:
      Wasm.Invoked.values{vs, Wasm.Instance{module, mem}}
    case Wasm.Call.trap{mem}:
      Wasm.Invoked.trap{Wasm.Instance{module, mem}}
    case Wasm.Call.not_done{}:
      Wasm.Invoked.not_done{}

def Wasm.invoke.arity(
  ok: Bool, f: Wasm.Func, fuel: Nat, args: List<&2, U32>, mem: Wasm.Memory, module: Wasm.Module
) -> Wasm.Invoked:
  match ok:
    case True{}:
      Wasm.invoked(Wasm.call(fuel, f, args, mem), module)
    case False{}:
      Wasm.Invoked.unsupported{}

def Wasm.invoke.found(
  f: Maybe<&2, Wasm.Func>, fuel: Nat, +args: List<&2, U32>, mem: Wasm.Memory, module: Wasm.Module
) -> Wasm.Invoked:
  match f:
    case None{}:
      Wasm.Invoked.unsupported{}
    case Some{Wasm.Func{+p, q, n, body}}:
      Wasm.invoke.arity(Nat.is_eq(p, List.length(&2, U32, args)), Wasm.Func{p, q, n, body}, fuel, args, mem, module)

# a call of the function exported as name, with the arguments in order, in at
# most fuel steps; unsupported when no such function takes as many arguments
def Wasm.invoke(fuel: Nat, inst: Wasm.Instance, name: List<&2, U32>, args: List<&2, U32>) -> Wasm.Invoked:
  match inst:
    case Wasm.Instance{module, mem}:
      match module:
        case Wasm.Module{+fs, memory, +es, seg}:
          Wasm.invoke.found(Wasm.export.func(fs, es, name), fuel, args, mem, Wasm.Module{fs, memory, es, seg})

# Host
# ----
#
# How a compiled program runs (W5). Its module exports its memory as
# "memory", alloc, of 1 parameter and 1 result, and run, of 2 parameters
# and 1 result. The host calls alloc(n) for the n bytes of the input; -1
# means out of memory. It writes the input from the address that alloc
# gives, then calls run(address, n), which gives 0 for a result, 1 for out of
# memory and 2 for no result. For a result, bytes 0 to 3 of the memory hold
# the output's address, and bytes 4 to 7 its length. Each of the two calls
# may take f steps.

# the names that the host uses, as ASCII bytes
def Wasm.name.memory() -> List<&2, U32>:
  [109, 101, 109, 111, 114, 121]

def Wasm.name.alloc() -> List<&2, U32>:
  [97, 108, 108, 111, 99]

def Wasm.name.run() -> List<&2, U32>:
  [114, 117, 110]

def Wasm.run.output.if(ok: Bool, bytes: Wasm.Bytes, a: U32, n: U32) -> Wasm.Outcome:
  match ok:
    case True{}:
      Wasm.Outcome.result{Wasm.read.bytes(U32.to_nat(n), bytes, a)}
    case False{}:
      Wasm.Outcome.trap{}

def Wasm.run.output.n(+p: U32, +a: U32, r: Wasm.Peek) -> Wasm.Outcome:
  match r:
    case Wasm.Peek{+n, bytes}:
      Wasm.run.output.if(Wasm.fits(p, a, n), bytes, a, n)

def Wasm.run.output.a(+p: U32, r: Wasm.Peek) -> Wasm.Outcome:
  match r:
    case Wasm.Peek{a, bytes}:
      Wasm.run.output.n(p, a, Wasm.read32(bytes, 4))

def Wasm.run.output.at(ok: Bool, p: U32, bytes: Wasm.Bytes) -> Wasm.Outcome:
  match ok:
    case True{}:
      Wasm.run.output.a(p, Wasm.read32(bytes, 0))
    case False{}:
      Wasm.Outcome.trap{}

# the output: the length at byte 4 of the bytes from the address at byte 0
def Wasm.run.output(mem: Wasm.Memory) -> Wasm.Outcome:
  match mem:
    case Wasm.Memory{+p, _, bytes}:
      Wasm.run.output.at(Wasm.fits(p, 0, 8), p, bytes)

def Wasm.run.status(zero: Bool, one: Bool, two: Bool, mem: Wasm.Memory) -> Wasm.Outcome:
  match zero one two:
    case True{} _ _:
      Wasm.run.output(mem)
    case False{} True{} _:
      Wasm.Outcome.out_of_memory{}
    case False{} False{} True{}:
      Wasm.Outcome.no_result{}
    case False{} False{} False{}:
      Wasm.Outcome.trap{}

# what run gave
def Wasm.run.ran(r: Wasm.Invoked) -> Wasm.Outcome:
  match r:
    case Wasm.Invoked.values{Con{+s, _}, Wasm.Instance{_, mem}}:
      Wasm.run.status(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), mem)
    case Wasm.Invoked.trap{_}:
      Wasm.Outcome.trap{}
    case Wasm.Invoked.not_done{}:
      Wasm.Outcome.not_done{}
    case Wasm.Invoked.unsupported{}:
      Wasm.Outcome.unsupported{}
    case _:
      Wasm.Outcome.trap{}

def Wasm.run.written(ok: Bool, f: Nat, inst: Wasm.Instance, a: U32, n: U32) -> Wasm.Outcome:
  match ok:
    case True{}:
      Wasm.run.ran(Wasm.invoke(f, inst, Wasm.name.run(), [a, n]))
    case False{}:
      Wasm.Outcome.trap{}

# the input written from the address a, when its n bytes fit
def Wasm.run.input(f: Nat, inst: Wasm.Instance, +a: U32, +n: U32, i: List<&2, U32>) -> Wasm.Outcome:
  match inst:
    case Wasm.Instance{module, mem}:
      match mem:
        case Wasm.Memory{+p, lim, bytes}:
          Wasm.run.written(Wasm.fits(p, a, n), f,
            Wasm.Instance{module, Wasm.Memory{p, lim, Wasm.write.bytes(i, a, bytes)}}, a, n)

def Wasm.run.alloced.if(full: Bool, f: Nat, inst: Wasm.Instance, a: U32, n: U32, i: List<&2, U32>) -> Wasm.Outcome:
  match full:
    case True{}:
      Wasm.Outcome.out_of_memory{}
    case False{}:
      Wasm.run.input(f, inst, a, n, i)

# what alloc gave: the input's address, or -1 for out of memory
def Wasm.run.alloced(r: Wasm.Invoked, f: Nat, n: U32, i: List<&2, U32>) -> Wasm.Outcome:
  match r:
    case Wasm.Invoked.values{Con{+a, _}, inst}:
      Wasm.run.alloced.if(U32.is_eq(a, 4294967295), f, inst, a, n, i)
    case Wasm.Invoked.trap{_}:
      Wasm.Outcome.trap{}
    case Wasm.Invoked.not_done{}:
      Wasm.Outcome.not_done{}
    case Wasm.Invoked.unsupported{}:
      Wasm.Outcome.unsupported{}
    case _:
      Wasm.Outcome.trap{}

# the input's length: an input of 2^32 bytes or more cannot fit in memory
def Wasm.run.sized(n: Maybe<&2, U32>, +f: Nat, inst: Wasm.Instance, i: List<&2, U32>) -> Wasm.Outcome:
  match n:
    case None{}:
      Wasm.Outcome.out_of_memory{}
    case Some{+k}:
      Wasm.run.alloced(Wasm.invoke(f, inst, Wasm.name.alloc(), [k]), f, k, i)

# the module exports what the host uses (W3)
def Wasm.run.is_host(inst: Wasm.Instance) -> Bool:
  match inst:
    case Wasm.Instance{Wasm.Module{+fs, _, +es, _}, _}:
      Wasm.export.has_memory(es, Wasm.name.memory()) &&
        Wasm.func.is_type(Wasm.export.func(fs, es, Wasm.name.alloc()), 1n, 1n) &&
        Wasm.func.is_type(Wasm.export.func(fs, es, Wasm.name.run()), 2n, 1n)

def Wasm.run.instance(ok: Bool, f: Nat, inst: Wasm.Instance, +i: List<&2, U32>) -> Wasm.Outcome:
  match ok:
    case True{}:
      Wasm.run.sized(Wasm.length32(i), f, inst, i)
    case False{}:
      Wasm.Outcome.unsupported{}

def Wasm.run.made(f: Nat, made: Wasm.Made, i: List<&2, U32>) -> Wasm.Outcome:
  match made:
    case Wasm.Made.instance{+inst}:
      Wasm.run.instance(Wasm.run.is_host(inst), f, inst, i)
    case Wasm.Made.unsupported{}:
      Wasm.Outcome.unsupported{}
    case Wasm.Made.out_of_memory{}:
      Wasm.Outcome.out_of_memory{}
    case Wasm.Made.trap{}:
      Wasm.Outcome.trap{}

# a run (W5) of the module of the bytes w on the input bytes i, with at most
# f steps for each of its two calls, and at most m pages (64 KiB each) of
# memory
def Wasm.run(f: Nat, w: List<&2, U32>, i: List<&2, U32>, m: U32) -> Wasm.Outcome:
  Wasm.run.made(f, Wasm.instantiate(w, m), i)
