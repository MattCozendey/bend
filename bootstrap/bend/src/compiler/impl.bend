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
# in at most f steps, with at most m pages (of 64 KiB) of memory. A module
# outside the subset gives unsupported and does not run. The subset is in
# every version of the spec (1.0, 2.0, 3.0); where they decode a number with
# more bits, the model reads the 32 bits of 1.0, so it accepts only what
# every version accepts, and it runs that as every version does.

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

# how a call ends: its results, the memory, and the steps that it took; a
# trap, with the memory; or no end within the fuel
type Wasm.Call is Data:
  Wasm.Call.done{results: List<&2, U32>, mem: Wasm.Memory, steps: Nat}
  Wasm.Call.trap{mem: Wasm.Memory}
  Wasm.Call.not_done{}

# the call c, after one more step
def Wasm.call.plus(c: Wasm.Call) -> Wasm.Call:
  match c:
    case Wasm.Call.done{rs, m, n}:
      Wasm.Call.done{rs, m, 1n+n}
    case Wasm.Call.trap{m}:
      Wasm.Call.trap{m}
    case Wasm.Call.not_done{}:
      Wasm.Call.not_done{}

def Wasm.call.stepped(s: Wasm.Step, more: Wasm.Frame -> Wasm.Memory -> Wasm.Call) -> Wasm.Call:
  match s:
    case Wasm.Step.next{f, m}:
      Wasm.call.plus(more(f, m))
    case Wasm.Step.done{rs, m}:
      Wasm.Call.done{rs, m, 1n}
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

# how an invocation ends: its results, with the instance after it and the
# steps that it took; a trap, with the instance after it; no end within the
# fuel; or no such function
type Wasm.Invoked is Data:
  Wasm.Invoked.values{vs: List<&2, U32>, i: Wasm.Instance, steps: Nat}
  Wasm.Invoked.trap{i: Wasm.Instance}
  Wasm.Invoked.not_done{}
  Wasm.Invoked.unsupported{}

def Wasm.invoked(c: Wasm.Call, module: Wasm.Module) -> Wasm.Invoked:
  match c:
    case Wasm.Call.done{vs, mem, n}:
      Wasm.Invoked.values{vs, Wasm.Instance{module, mem}, n}
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
# the output's address, and bytes 4 to 7 its length. The two calls take at
# most f steps in all.

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
    case Wasm.Invoked.values{Con{+s, _}, Wasm.Instance{_, mem}, _}:
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

# what alloc gave: the input's address, or -1 for out of memory; run then
# has the steps that alloc left
def Wasm.run.alloced(r: Wasm.Invoked, f: Nat, n: U32, i: List<&2, U32>) -> Wasm.Outcome:
  match r:
    case Wasm.Invoked.values{Con{+a, _}, inst, used}:
      Wasm.run.alloced.if(U32.is_eq(a, 4294967295), Nat.sub(f, used), inst, a, n, i)
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

# a run (W5) of the module of the bytes w on the input bytes i, in at most f
# steps of its functions, with at most m pages (64 KiB each) of memory
def Wasm.run(f: Nat, w: List<&2, U32>, i: List<&2, U32>, m: U32) -> Wasm.Outcome:
  Wasm.run.made(f, Wasm.instantiate(w, m), i)

# Program
# =======
#
# What a program gives on its input (INVARIANTS #3), and the memory that the
# laws of step 1 (spec.bend) grant it (INVARIANTS #4). The terms mirror
# bootstrap/lean/src/Bootstrap/Bytes.lean, and Program.gives mirrors Gives in
# Program.lean, so that step 3 can join them.

# the names of the constructors of a list of bytes, as `bend -o` writes them
def Program.name.unit() -> List<&2, U32>:
  [40, 41]

def Program.name.nil() -> List<&2, U32>:
  [78, 105, 108]

def Program.name.con() -> List<&2, U32>:
  [67, 111, 110]

def Program.name.u32() -> List<&2, U32>:
  [85, 51, 50]

def Program.name.wnil() -> List<&2, U32>:
  [87, 78, 105, 108]

def Program.name.wcon() -> List<&2, U32>:
  [87, 67, 111, 110]

def Program.name.true() -> List<&2, U32>:
  [84, 114, 117, 101]

def Program.name.false() -> List<&2, U32>:
  [70, 97, 108, 115, 101]

def Program.name.main() -> List<&2, U32>:
  [109, 97, 105, 110]

# the fields of a constructor: each paired at quantity 1 with the rest, and ()
# at the end
def Program.fields(fs: List<&2, Term>) -> Term:
  match fs:
    case Nil{}:
      Term.Lab{Program.name.unit()}
    case Con{f, rest}:
      Term.Tup{Quan.Q1{}, f, Program.fields(rest)}

# the constructor k with the fields fs, as `bend -o` writes a value
def Program.ctor(k: List<&2, U32>, fs: List<&2, Term>) -> Term:
  Term.Tup{Quan.Q1{}, Term.Lab{k}, Program.fields(fs)}

def Program.bit(b: Bool) -> Term:
  match b:
    case True{}:
      Program.ctor(Program.name.true(), [])
    case False{}:
      Program.ctor(Program.name.false(), [])

# a Word(n), its lowest bit first
def Program.word(n: Nat, w: Word(n)) -> Term:
  match n:
    case 0n:
      Program.ctor(Program.name.wnil(), [])
    case 1n+p:
      match w:
        case WCon{b, t}:
          Program.ctor(Program.name.wcon(), [Program.bit(b), Program.word(p, t)])

def Program.cell.of(c: U32) -> Term:
  match c:
    case U32{w}:
      Program.ctor(Program.name.u32(), [Program.word(32n, w)])

# a byte of the input, as Base's U32: an element of the input is its low byte,
# as a host that writes bytes writes it
def Program.cell(b: U32) -> Term:
  Program.cell.of(U32.and(b, 255))

# a list of bytes, as Base's List<&2, U32>
def Program.bytes(i: List<&2, U32>) -> Term:
  match i:
    case Nil{}:
      Program.ctor(Program.name.nil(), [])
    case Con{b, rest}:
      Program.ctor(Program.name.con(), [Program.cell(b), Program.bytes(rest)])

# the start of a run: main, applied once at quantity 1 to the input's bytes
def Program.start(i: List<&2, U32>) -> Term:
  Term.App{Quan.Q1{}, Term.Ref{Program.name.main()}, Program.bytes(i)}

def Program.unbit.if(is_true: Bool, is_false: Bool) -> Maybe<&2, Bool>:
  match is_true is_false:
    case True{} _:
      Some{True{}}
    case False{} True{}:
      Some{False{}}
    case False{} False{}:
      None{}

# the Bool of a constructor's name
def Program.unbit(+k: List<&2, U32>) -> Maybe<&2, Bool>:
  Program.unbit.if(Name.is_eq(k, Program.name.true()), Name.is_eq(k, Program.name.false()))

def Program.unword.nil(ok: Bool) -> Maybe<&2, Word(0n)>:
  match ok:
    case True{}:
      Some{WNil{}}
    case False{}:
      None{}

def Program.unword.con(-p: Nat, ok: Bool, b: Maybe<&2, Bool>, w: Maybe<&2, Word(p)>) ->
  Maybe<&2, Word(1n+p)>:
  match ok b w:
    case True{} Some{x} Some{t}:
      Some{WCon{x, t}}
    case _ _ _:
      None{}

# the Word(n) that Program.word gives the term of; nothing for any other term
def Program.unword(n: Nat, t: Term) -> Maybe<&2, Word(n)>:
  match n:
    case 0n:
      match t:
        case Term.Tup{Quan.Q1{}, Term.Lab{+k}, Term.Lab{+u}}:
          Program.unword.nil(Name.is_eq(k, Program.name.wnil()) && Name.is_eq(u, Program.name.unit()))
        case _:
          None{}
    case 1n+p:
      match t:
        case Term.Tup{Quan.Q1{}, Term.Lab{+k},
            Term.Tup{Quan.Q1{}, Term.Tup{Quan.Q1{}, Term.Lab{+b}, Term.Lab{+u1}}, Term.Tup{Quan.Q1{}, w, Term.Lab{+u2}}}}:
          Program.unword.con(p,
            Name.is_eq(k, Program.name.wcon()) && Name.is_eq(u1, Program.name.unit()) && Name.is_eq(u2, Program.name.unit()),
            Program.unbit(b), Program.unword(p, w))
        case _:
          None{}

def Program.unbytes.nil(ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      Some{Nil{}}
    case False{}:
      None{}

def Program.unbytes.byte(lt: Bool, v: U32, bs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match lt:
    case True{}:
      Some{Con{v, bs}}
    case False{}:
      None{}

def Program.unbytes.con(ok: Bool, w: Maybe<&2, Word(32n)>, bs: Maybe<&2, List<&2, U32>>) ->
  Maybe<&2, List<&2, U32>>:
  match ok w bs:
    case True{} Some{+x} Some{rest}:
      Program.unbytes.byte(U32.is_lt(U32{x}, 256), U32{x}, rest)
    case _ _ _:
      None{}

# the list of bytes that Program.bytes gives the term of, each below 256;
# nothing for any other term
def Program.unbytes(t: Term) -> Maybe<&2, List<&2, U32>>:
  match t:
    case Term.Tup{Quan.Q1{}, Term.Lab{+k}, Term.Lab{+u}}:
      Program.unbytes.nil(Name.is_eq(k, Program.name.nil()) && Name.is_eq(u, Program.name.unit()))
    case Term.Tup{Quan.Q1{}, Term.Lab{+k},
        Term.Tup{Quan.Q1{}, Term.Tup{Quan.Q1{}, Term.Lab{+c}, Term.Tup{Quan.Q1{}, w, Term.Lab{+u1}}},
          Term.Tup{Quan.Q1{}, rest, Term.Lab{+u2}}}}:
      Program.unbytes.con(
        Name.is_eq(k, Program.name.con()) && Name.is_eq(c, Program.name.u32()) &&
          Name.is_eq(u1, Program.name.unit()) && Name.is_eq(u2, Program.name.unit()),
        Program.unword(32n, w), Program.unbytes(rest))
    case _:
      None{}

def Program.result.if(ok: Bool, v: Term) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      Program.unbytes(v)
    case False{}:
      None{}

# the bytes at the end r of a run, when it is a value that is a list of bytes
def Program.result(ds: List<&2, Def>, r: Maybe<Term>) -> Maybe<&2, List<&2, U32>>:
  match r:
    case None{}:
      None{}
    case Some{+v}:
      Program.result.if(Eval.vals(ds, v, False{}), v)

def Program.gives.of(r: Maybe<List<&2, Def>>, i: List<&2, U32>, n: Nat) -> Maybe<&2, List<&2, U32>>:
  match r:
    case None{}:
      None{}
    case Some{+ds}:
      Program.result(ds, Eval.steps(n, ds, Program.start(i)))

# INVARIANTS #3: what the program of the book bytes p (INVARIANTS #5) gives on
# the input i after exactly n steps of Eval: the list of bytes of the value that
# it reaches, or nothing
def Program.gives(p: List<&2, U32>, i: List<&2, U32>, n: Nat) -> Maybe<&2, List<&2, U32>>:
  Program.gives.of(Book.read(p), i, n)

# the nodes of a term
def Term.size(t: Term) -> Nat:
  match t:
    case Term.Var{_}:
      1n
    case Term.Ref{_}:
      1n
    case Term.Ann{x, T}:
      1n+Nat.add(Term.size(x), Term.size(T))
    case Term.Let{_, v, f}:
      1n+Nat.add(Term.size(v), Term.size(f))
    case Term.Typ{q}:
      1n+Term.size(q)
    case Term.Min{a, b}:
      1n+Nat.add(Term.size(a), Term.size(b))
    case Term.All{_, A, B}:
      1n+Nat.add(Term.size(A), Term.size(B))
    case Term.Lam{_, f}:
      1n+Term.size(f)
    case Term.App{_, f, x}:
      1n+Nat.add(Term.size(f), Term.size(x))
    case Term.Sig{_, A, B}:
      1n+Nat.add(Term.size(A), Term.size(B))
    case Term.Tup{_, a, b}:
      1n+Nat.add(Term.size(a), Term.size(b))
    case Term.Prj{h}:
      1n+Term.size(h)
    case Term.Enu{_}:
      1n
    case Term.Lab{_}:
      1n
    case Term.Mat{_, h, m}:
      1n+Nat.add(Term.size(h), Term.size(m))
    case Term.Efq{}:
      1n
    case Term.Eql{a, b, T}:
      1n+Nat.add(Term.size(a), Nat.add(Term.size(b), Term.size(T)))
    case Term.Rfl{}:
      1n
    case Term.Rwt{e, P, f}:
      1n+Nat.add(Term.size(e), Nat.add(Term.size(P), Term.size(f)))

def Program.largest.next(r: Maybe<Term>, more: Term -> Nat) -> Nat:
  match r:
    case None{}:
      0n
    case Some{t}:
      more(t)

# the most nodes of a term that the run from t reaches within n steps, t
# included
def Program.largest.go(n: Nat, +ds: List<&2, Def>, +t: Term) -> Nat:
  match n:
    case 0n:
      Term.size(t)
    case 1n+m:
      Nat.max(Term.size(t), Program.largest.next(Eval.step(ds, t), u => Program.largest.go(m, ds, u)))

def Program.largest.of(r: Maybe<List<&2, Def>>, i: List<&2, U32>, n: Nat) -> Nat:
  match r:
    case None{}:
      0n
    case Some{ds}:
      Program.largest.go(n, ds, Program.start(i))

# S of INVARIANTS #4: the most nodes of a term that the run on the input i
# reaches within n steps; the input is in the first term
def Program.largest(p: List<&2, U32>, i: List<&2, U32>, n: Nat) -> Nat:
  Program.largest.of(Book.read(p), i, n)

# F of INVARIANTS #4 (C1, approved): 64 × (|p| + S) + 2^24 bytes
def Program.need(+p: List<&2, U32>, i: List<&2, U32>, n: Nat) -> Nat:
  Nat.add(Nat.mul(64n, Nat.add(List.length(&2, U32, p), Program.largest(p, i, n))), 16777216n)

# the bytes of m pages of 2^16 bytes, up to 2^16 pages: as much as a memory of
# 32-bit addresses can have
def Program.memory(m: U32) -> Nat:
  Nat.mul(65536n, U32.to_nat(Wasm.min(m, 65536)))

# Compiler
# ========
#
# The compiler of step 1 (C2 to C4, approved): a fixed machine (C3) with the
# program's book as the data of its memory. The machine is written in
# Cir, a small language of memory cells (C5), which Cir.module translates to a
# module of the subset of WASM that the Bend copy of WASM models (W2, W3).

# Encoding
# --------
#
# The bytes of a module of the subset, as Wasm.decode.module reads them.

def Wasm.encode.leb.if(last: Bool, b: U32, more: Unit -> List<&2, U32>) -> List<&2, U32>:
  match last:
    case True{}:
      [b]
    case False{}:
      Con{U32.or(b, 128), more(Unit{})}

def Wasm.encode.uleb.go(fuel: Nat, +v: U32) -> List<&2, U32>:
  match fuel:
    case 0n:
      []
    case 1n+f:
      +r = U32.shrn(v, 7n)
      Wasm.encode.leb.if(U32.is_zero(r), U32.and(v, 127), u => Wasm.encode.uleb.go(f, r))

# a U32 as unsigned LEB128 (spec 5.2.2): seven bits a byte, the lowest first
def Wasm.encode.uleb(v: U32) -> List<&2, U32>:
  Wasm.encode.uleb.go(5n, v)

# the bits that an arithmetic shift right by 7 brings in at the top
def Wasm.encode.sign(neg: Bool) -> U32:
  match neg:
    case True{}:
      4261412864
    case False{}:
      0

def Wasm.encode.sleb.go(fuel: Nat, +v: U32) -> List<&2, U32>:
  match fuel:
    case 0n:
      []
    case 1n+f:
      +b = U32.and(v, 127)
      +r = U32.or(U32.shrn(v, 7n), Wasm.encode.sign(U32.is_ne(U32.and(v, 2147483648), 0)))
      +low = U32.is_zero(U32.and(b, 64))
      Wasm.encode.leb.if((U32.is_zero(r) && low) || (U32.is_eq(r, 4294967295) && Bool.not(low)), b,
        u => Wasm.encode.sleb.go(f, r))

# a U32 as signed 32-bit LEB128 (spec 5.2.2), of its two's complement value
def Wasm.encode.sleb(v: U32) -> List<&2, U32>:
  Wasm.encode.sleb.go(5n, v)

# the number of items of a list
def Wasm.encode.len(-A: Data, xs: List<&2, A>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{_, rest}:
      U32.inc(Wasm.encode.len(A, rest))

# a vector (spec 5.1.3): the number n of its items, then their bytes
def Wasm.encode.vec(n: U32, items: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, Wasm.encode.uleb(n), items)

# bytes after their number: a vector of bytes or a name (spec 5.1.3, 5.2.4)
def Wasm.encode.sized(+c: List<&2, U32>) -> List<&2, U32>:
  Wasm.encode.vec(Wasm.encode.len(U32, c), c)

# the labels of a br_table, then the bytes acc
def Wasm.encode.labels(ls: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match ls:
    case Nil{}:
      acc
    case Con{l, rest}:
      List.append(&2, U32, Wasm.encode.uleb(l), Wasm.encode.labels(rest, acc))

def Wasm.encode.opcode(o: Wasm.Op) -> U32:
  match o:
    case Wasm.Op.add{}:
      106
    case Wasm.Op.sub{}:
      107
    case Wasm.Op.and{}:
      113
    case Wasm.Op.or{}:
      114
    case Wasm.Op.shl{}:
      116
    case Wasm.Op.shr_u{}:
      118
    case Wasm.Op.eq{}:
      70
    case Wasm.Op.ne{}:
      71
    case Wasm.Op.lt_u{}:
      73
    case Wasm.Op.gt_u{}:
      75
    case Wasm.Op.le_u{}:
      77
    case Wasm.Op.ge_u{}:
      79

# an opcode and its immediate, then the bytes acc
def Wasm.encode.with(op: U32, imm: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  Con{op, List.append(&2, U32, imm, acc)}

# the instructions xs (spec 5.4), then the bytes acc; a load or a store names
# the natural alignment of its width
def Wasm.encode.instrs(xs: List<&2, Wasm.Instr>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{x, rest}:
      match x:
        case Wasm.Instr.const{n}:
          Wasm.encode.with(65, Wasm.encode.sleb(n), Wasm.encode.instrs(rest, acc))
        case Wasm.Instr.local_get{i}:
          Wasm.encode.with(32, Wasm.encode.uleb(i), Wasm.encode.instrs(rest, acc))
        case Wasm.Instr.local_set{i}:
          Wasm.encode.with(33, Wasm.encode.uleb(i), Wasm.encode.instrs(rest, acc))
        case Wasm.Instr.local_tee{i}:
          Wasm.encode.with(34, Wasm.encode.uleb(i), Wasm.encode.instrs(rest, acc))
        case Wasm.Instr.op{o}:
          Con{Wasm.encode.opcode(o), Wasm.encode.instrs(rest, acc)}
        case Wasm.Instr.eqz{}:
          Con{69, Wasm.encode.instrs(rest, acc)}
        case Wasm.Instr.load{o}:
          Wasm.encode.with(40, Con{2, Wasm.encode.uleb(o)}, Wasm.encode.instrs(rest, acc))
        case Wasm.Instr.load8_u{o}:
          Wasm.encode.with(45, Con{0, Wasm.encode.uleb(o)}, Wasm.encode.instrs(rest, acc))
        case Wasm.Instr.store{o}:
          Wasm.encode.with(54, Con{2, Wasm.encode.uleb(o)}, Wasm.encode.instrs(rest, acc))
        case Wasm.Instr.store8{o}:
          Wasm.encode.with(58, Con{0, Wasm.encode.uleb(o)}, Wasm.encode.instrs(rest, acc))
        case Wasm.Instr.memory_size{}:
          Con{63, Con{0, Wasm.encode.instrs(rest, acc)}}
        case Wasm.Instr.memory_grow{}:
          Con{64, Con{0, Wasm.encode.instrs(rest, acc)}}
        case Wasm.Instr.block{body}:
          Con{2, Con{64, Wasm.encode.instrs(body, Con{11, Wasm.encode.instrs(rest, acc)})}}
        case Wasm.Instr.loop{body}:
          Con{3, Con{64, Wasm.encode.instrs(body, Con{11, Wasm.encode.instrs(rest, acc)})}}
        case Wasm.Instr.br{l}:
          Wasm.encode.with(12, Wasm.encode.uleb(l), Wasm.encode.instrs(rest, acc))
        case Wasm.Instr.br_if{l}:
          Wasm.encode.with(13, Wasm.encode.uleb(l), Wasm.encode.instrs(rest, acc))
        case Wasm.Instr.br_table{+ls, l}:
          Wasm.encode.with(14, Wasm.encode.uleb(Wasm.encode.len(U32, ls)),
            Wasm.encode.labels(ls, List.append(&2, U32, Wasm.encode.uleb(l), Wasm.encode.instrs(rest, acc))))

# the value type i32, n times
def Wasm.encode.i32s(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      []
    case 1n+p:
      Con{127, Wasm.encode.i32s(p)}

# a function's type (spec 5.3.6): 0x60, then its parameters and results
def Wasm.encode.functype(f: Wasm.Func) -> List<&2, U32>:
  match f:
    case Wasm.Func{p, q, _, _}:
      Con{96, List.append(&2, U32, Wasm.encode.sized(Wasm.encode.i32s(p)), Wasm.encode.sized(Wasm.encode.i32s(q)))}

def Wasm.encode.functypes(fs: List<&2, Wasm.Func>) -> List<&2, U32>:
  match fs:
    case Nil{}:
      []
    case Con{f, rest}:
      List.append(&2, U32, Wasm.encode.functype(f), Wasm.encode.functypes(rest))

# the function section: function i has type i
def Wasm.encode.indices(fs: List<&2, Wasm.Func>, +i: U32) -> List<&2, U32>:
  match fs:
    case Nil{}:
      []
    case Con{_, rest}:
      List.append(&2, U32, Wasm.encode.uleb(i), Wasm.encode.indices(rest, U32.inc(i)))

# a function's locals after its parameters (spec 5.5.13): one group of n
# locals of i32, or none
def Wasm.encode.locals(+n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [0]
    case 1n+_:
      Con{1, List.append(&2, U32, Wasm.encode.uleb(U32.from_nat(n)), [127])}

# a function's code (spec 5.5.13): its size, its locals, its body and its end
def Wasm.encode.code(f: Wasm.Func) -> List<&2, U32>:
  match f:
    case Wasm.Func{_, _, n, body}:
      Wasm.encode.sized(List.append(&2, U32, Wasm.encode.locals(n), Wasm.encode.instrs(body, [11])))

def Wasm.encode.codes(fs: List<&2, Wasm.Func>) -> List<&2, U32>:
  match fs:
    case Nil{}:
      []
    case Con{f, rest}:
      List.append(&2, U32, Wasm.encode.code(f), Wasm.encode.codes(rest))

# an export (spec 5.5.10): its name, then 0 and a function index, or 2 and
# memory 0
def Wasm.encode.export(e: Wasm.Export) -> List<&2, U32>:
  match e:
    case Wasm.Export.func{name, i}:
      List.append(&2, U32, Wasm.encode.sized(name), Con{0, Wasm.encode.uleb(i)})
    case Wasm.Export.memory{name}:
      List.append(&2, U32, Wasm.encode.sized(name), [2, 0])

def Wasm.encode.exports(es: List<&2, Wasm.Export>) -> List<&2, U32>:
  match es:
    case Nil{}:
      []
    case Con{e, rest}:
      List.append(&2, U32, Wasm.encode.export(e), Wasm.encode.exports(rest))

# a memory's limits (spec 5.3.7): 0 and a minimum, or 1, a minimum and a
# maximum
def Wasm.encode.limits(l: Wasm.Limits) -> List<&2, U32>:
  match l:
    case Wasm.Limits{min, None{}}:
      Con{0, Wasm.encode.uleb(min)}
    case Wasm.Limits{min, Some{max}}:
      Con{1, List.append(&2, U32, Wasm.encode.uleb(min), Wasm.encode.uleb(max))}

# a section (spec 5.5.2): its id, its size and its content c; then the bytes
# acc
def Wasm.encode.section(id: U32, c: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  Con{id, List.append(&2, U32, Wasm.encode.sized(c), acc)}

# the memory section, when there is a memory
def Wasm.encode.memory(m: Maybe<&2, Wasm.Limits>, acc: List<&2, U32>) -> List<&2, U32>:
  match m:
    case None{}:
      acc
    case Some{l}:
      Wasm.encode.section(5, Con{1, Wasm.encode.limits(l)}, acc)

# the data section, when there is a segment: 0, an active segment of memory
# 0, its offset as the constant expression i32.const n end, then its bytes
def Wasm.encode.data(d: Maybe<&2, Wasm.Segment>) -> List<&2, U32>:
  match d:
    case None{}:
      []
    case Some{Wasm.Segment{o, bs}}:
      Wasm.encode.section(11, Con{1, Con{0, Con{65, List.append(&2, U32, Wasm.encode.sleb(o), Con{11, Wasm.encode.sized(bs)})}}}, [])

# a module of the subset (spec 5.5.15): the magic \0asm, version 1, then its
# sections in the order of their ids; function i has type i
def Wasm.encode(m: Wasm.Module) -> List<&2, U32>:
  match m:
    case Wasm.Module{+fs, mem, +es, d}:
      +n = Wasm.encode.len(Wasm.Func, fs)
      Con{0, Con{97, Con{115, Con{109, Con{1, Con{0, Con{0, Con{0,
        Wasm.encode.section(1, Wasm.encode.vec(n, Wasm.encode.functypes(fs)),
          Wasm.encode.section(3, Wasm.encode.vec(n, Wasm.encode.indices(fs, 0)),
            Wasm.encode.memory(mem,
              Wasm.encode.section(7, Wasm.encode.vec(Wasm.encode.len(Wasm.Export, es), Wasm.encode.exports(es)),
                Wasm.encode.section(10, Wasm.encode.vec(n, Wasm.encode.codes(fs)), Wasm.encode.data(d))))))}}}}}}}}

# Cir
# ---
#
# The language of the machine (C5): statements over U32 registers, a memory of
# cells of five U32 fields, the input's bytes and the output's. Cell c is the
# 20 bytes from byte 20 × c of the module's memory: cells 1 to `image` hold
# the book, the input's bytes follow them, and the machine's own cells start
# at `first`. The memory grows by the pages that an access needs, as in the
# module that Cir.module makes, so that Cir.exec says what that module does. An access that the module could
# not make in the same way traps: the machine makes none.

# a cell: five fields
type Cir.Cell is Data:
  Cir.Cell{f0: U32, f1: U32, f2: U32, f3: U32, f4: U32}

def Cir.Cell.zero() -> Cir.Cell:
  Cir.Cell{0, 0, 0, 0, 0}

# field k of a cell, from 0 to 4
def Cir.Cell.get(k: Nat, c: Cir.Cell) -> U32:
  match k c:
    case 0n Cir.Cell{a, _, _, _, _}:
      a
    case 1n Cir.Cell{_, b, _, _, _}:
      b
    case 2n Cir.Cell{_, _, x, _, _}:
      x
    case 3n Cir.Cell{_, _, _, y, _}:
      y
    case _ Cir.Cell{_, _, _, _, z}:
      z

def Cir.Cell.set(k: Nat, c: Cir.Cell, v: U32) -> Cir.Cell:
  match k c:
    case 0n Cir.Cell{_, b, x, y, z}:
      Cir.Cell{v, b, x, y, z}
    case 1n Cir.Cell{a, _, x, y, z}:
      Cir.Cell{a, v, x, y, z}
    case 2n Cir.Cell{a, b, _, y, z}:
      Cir.Cell{a, b, v, y, z}
    case 3n Cir.Cell{a, b, x, _, z}:
      Cir.Cell{a, b, x, v, z}
    case _ Cir.Cell{a, b, x, y, _}:
      Cir.Cell{a, b, x, y, v}

# the cells, by the bits of their number, the lowest first; a missing cell is
# all zeros
type Cir.Cells is Data:
  Cir.Cells.none{}
  Cir.Cells.one{c: Cir.Cell}
  Cir.Cells.node{lo: Cir.Cells, hi: Cir.Cells}

def Cir.Cells.get.at(n: Nat, w: Word(n), m: Cir.Cells) -> Cir.Cell:
  match n:
    case 0n:
      match m:
        case Cir.Cells.one{c}:
          c
        case _:
          Cir.Cell.zero()
    case 1n+p:
      match w:
        case WCon{bit, t}:
          match bit m:
            case False{} Cir.Cells.node{lo, _}:
              Cir.Cells.get.at(p, t, lo)
            case True{} Cir.Cells.node{_, hi}:
              Cir.Cells.get.at(p, t, hi)
            case _ _:
              Cir.Cell.zero()

def Cir.Cells.set.at(n: Nat, w: Word(n), m: Cir.Cells, c: Cir.Cell) -> Cir.Cells:
  match n:
    case 0n:
      Cir.Cells.one{c}
    case 1n+p:
      match w:
        case WCon{bit, t}:
          match bit m:
            case False{} Cir.Cells.node{lo, hi}:
              Cir.Cells.node{Cir.Cells.set.at(p, t, lo, c), hi}
            case True{} Cir.Cells.node{lo, hi}:
              Cir.Cells.node{lo, Cir.Cells.set.at(p, t, hi, c)}
            case False{} _:
              Cir.Cells.node{Cir.Cells.set.at(p, t, Cir.Cells.none{}, c), Cir.Cells.none{}}
            case True{} _:
              Cir.Cells.node{Cir.Cells.none{}, Cir.Cells.set.at(p, t, Cir.Cells.none{}, c)}

# the cell numbered i
def Cir.Cells.get(m: Cir.Cells, i: U32) -> Cir.Cell:
  match i:
    case U32{w}:
      Cir.Cells.get.at(32n, w, m)

def Cir.Cells.set(m: Cir.Cells, i: U32, c: Cir.Cell) -> Cir.Cells:
  match i:
    case U32{w}:
      Cir.Cells.set.at(32n, w, m, c)

# the registers r of a Cir program are Nat; its cells' fields are numbered 0
# to 4
type Cir.Expr is Data:
  Cir.Expr.const{n: U32}
  Cir.Expr.get{r: Nat}
  Cir.Expr.op{op: Wasm.Op, a: Cir.Expr, b: Cir.Expr}
  Cir.Expr.eqz{a: Cir.Expr}
  Cir.Expr.field{k: Nat, c: Cir.Expr}
  Cir.Expr.byte{i: Cir.Expr}
  Cir.Expr.size{}

# a while repeats its body while its condition is not 0; halt ends the run
# with a status: 0 a result, 2 no result
type Cir.Stmt is Data:
  Cir.Stmt.nop{}
  Cir.Stmt.set{r: Nat, e: Cir.Expr}
  Cir.Stmt.store{k: Nat, c: Cir.Expr, v: Cir.Expr}
  Cir.Stmt.alloc{r: Nat}
  Cir.Stmt.emit{v: Cir.Expr}
  Cir.Stmt.seq{a: Cir.Stmt, b: Cir.Stmt}
  Cir.Stmt.if{c: Cir.Expr, t: Cir.Stmt, e: Cir.Stmt}
  Cir.Stmt.while{c: Cir.Expr, body: Cir.Stmt}
  Cir.Stmt.halt{s: U32}

# the state of a run: the registers; the cells, the first never used (next),
# the first of the machine's own (first) and the last of the book's (image);
# the memory's size and the limit of its growth, in pages; the input; and the
# output, the last byte first, with its length
type Cir.State is Data:
  Cir.State{
    regs: List<&2, U32>, cells: Cir.Cells, next: U32, first: U32, image: U32,
    pages: U32, limit: U32, input: List<&2, U32>, out: List<&2, U32>, outn: U32}

# how a statement ends: after it, with the state; halted, with a status; out
# of memory; with an access that the module could not make in the same way;
# or out of fuel
type Cir.Out is Data:
  Cir.Out.next{st: Cir.State}
  Cir.Out.halt{s: U32, st: Cir.State}
  Cir.Out.out_of_memory{}
  Cir.Out.trap{}
  Cir.Out.not_done{}

# the cell i is one the machine may use: one of the book's, or one of its own
# that it took
def Cir.is_cell(+i: U32, +image: U32, +first: U32, +next: U32) -> Bool:
  (Bool.not(U32.is_zero(i)) && U32.is_le(i, image)) || (U32.is_le(first, i) && U32.is_lt(i, next))

def Cir.eval.op(o: Wasm.Op, a: Maybe<&2, U32>, b: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match a b:
    case Some{x} Some{y}:
      Some{Wasm.op(o, x, y)}
    case _ _:
      None{}

def Cir.eval.eqz(a: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match a:
    case Some{x}:
      Some{Bool.to_u32(U32.is_zero(x))}
    case None{}:
      None{}

def Cir.eval.field.if(ok: Bool, k: Nat, cells: Cir.Cells, i: U32) -> Maybe<&2, U32>:
  match ok:
    case True{}:
      Some{Cir.Cell.get(k, Cir.Cells.get(cells, i))}
    case False{}:
      None{}

def Cir.eval.field(k: Nat, c: Maybe<&2, U32>, st: Cir.State) -> Maybe<&2, U32>:
  match c st:
    case Some{+i} Cir.State{_, cells, next, first, image, _, _, _, _, _}:
      Cir.eval.field.if(Cir.is_cell(i, image, first, next), k, cells, i)
    case None{} _:
      None{}

def Cir.eval.byte.of(b: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match b:
    case Some{x}:
      Some{U32.and(x, 255)}
    case None{}:
      None{}

# the input's byte i: the low byte of its element i
def Cir.eval.byte(i: Maybe<&2, U32>, input: List<&2, U32>) -> Maybe<&2, U32>:
  match i:
    case Some{x}:
      Cir.eval.byte.of(List.get(&2, U32, input, U32.to_nat(x)))
    case None{}:
      None{}

def Cir.eval.size(st: Cir.State) -> Maybe<&2, U32>:
  match st:
    case Cir.State{_, _, _, _, _, _, _, input, _, _}:
      Some{Wasm.encode.len(U32, input)}

def Cir.eval.get(r: Nat, st: Cir.State) -> Maybe<&2, U32>:
  match st:
    case Cir.State{regs, _, _, _, _, _, _, _, _, _}:
      List.get(&2, U32, regs, r)

def Cir.eval.input(st: Cir.State) -> List<&2, U32>:
  match st:
    case Cir.State{_, _, _, _, _, _, _, input, _, _}:
      input

# the value of an expression; nothing for an access that traps
def Cir.eval(e: Cir.Expr, +st: Cir.State) -> Maybe<&2, U32>:
  match e:
    case Cir.Expr.const{n}:
      Some{n}
    case Cir.Expr.get{r}:
      Cir.eval.get(r, st)
    case Cir.Expr.op{o, a, b}:
      Cir.eval.op(o, Cir.eval(a, st), Cir.eval(b, st))
    case Cir.Expr.eqz{a}:
      Cir.eval.eqz(Cir.eval(a, st))
    case Cir.Expr.field{k, c}:
      Cir.eval.field(k, Cir.eval(c, st), st)
    case Cir.Expr.byte{i}:
      Cir.eval.byte(Cir.eval(i, st), Cir.eval.input(st))
    case Cir.Expr.size{}:
      Cir.eval.size(st)

def Cir.regs.set.if(ok: Bool, regs: List<&2, U32>, r: Nat, v: U32) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      Some{List.set(&2, U32, regs, r, v)}
    case False{}:
      None{}

# the registers with r set to v, when there is a register r
def Cir.regs.set(+regs: List<&2, U32>, +r: Nat, v: U32) -> Maybe<&2, List<&2, U32>>:
  Cir.regs.set.if(Nat.is_lt(r, List.length(&2, U32, regs)), regs, r, v)

def Cir.exec.set.of(regs: Maybe<&2, List<&2, U32>>, st: Cir.State) -> Cir.Out:
  match regs st:
    case Some{rs} Cir.State{_, cells, next, first, image, pages, limit, input, out, outn}:
      Cir.Out.next{Cir.State{rs, cells, next, first, image, pages, limit, input, out, outn}}
    case None{} _:
      Cir.Out.trap{}

def Cir.exec.set(r: Nat, v: Maybe<&2, U32>, +st: Cir.State) -> Cir.Out:
  match v st:
    case Some{x} Cir.State{regs, _, _, _, _, _, _, _, _, _}:
      Cir.exec.set.of(Cir.regs.set(regs, r, x), st)
    case None{} _:
      Cir.Out.trap{}

def Cir.exec.store.if(ok: Bool, k: Nat, +i: U32, v: U32, st: Cir.State) -> Cir.Out:
  match ok st:
    case True{} Cir.State{regs, +cells, next, first, image, pages, limit, input, out, outn}:
      Cir.Out.next{Cir.State{regs, Cir.Cells.set(cells, i, Cir.Cell.set(k, Cir.Cells.get(cells, i), v)), next, first, image, pages, limit, input, out, outn}}
    case False{} _:
      Cir.Out.trap{}

def Cir.exec.store(k: Nat, c: Maybe<&2, U32>, v: Maybe<&2, U32>, +st: Cir.State) -> Cir.Out:
  match c v st:
    case Some{+i} Some{x} Cir.State{_, _, +next, +first, +image, _, _, _, _, _}:
      Cir.exec.store.if(Cir.is_cell(i, image, first, next), k, i, x, st)
    case _ _ _:
      Cir.Out.trap{}

# a register holds the cell i, made all zeros
def Cir.exec.took(r: Nat, +i: U32, st: Cir.State, next: U32, pages: U32) -> Cir.Out:
  match st:
    case Cir.State{regs, cells, _, first, image, _, limit, input, out, outn}:
      Cir.exec.set(r, Some{i},
        Cir.State{regs, Cir.Cells.set(cells, i, Cir.Cell.zero()), next, first, image, pages, limit, input, out, outn})

def Cir.room.if(inside: Bool, can_grow: Bool, p: U32, need: U32) -> Maybe<&2, U32>:
  match inside can_grow:
    case True{} _:
      Some{p}
    case False{} True{}:
      Some{need}
    case False{} False{}:
      None{}

# the pages that the memory has once the byte b is in it, when it holds p
# pages and may grow to lim: (b >> 16) + 1 at least; none when it cannot grow
# that far
def Cir.room(b: U32, +p: U32, +lim: U32) -> Maybe<&2, U32>:
  +need = U32.inc(U32.shrn(b, 16n))
  Cir.room.if(U32.is_le(need, p), U32.is_le(need, lim), p, need)

# 20 × c, the first byte of the cell c
def Cir.at(+c: U32) -> U32:
  U32.add(U32.shln(c, 4n), U32.shln(c, 2n))

def Cir.exec.bump.of(r: Nat, +next: U32, st: Cir.State, pages: Maybe<&2, U32>) -> Cir.Out:
  match pages:
    case Some{p}:
      Cir.exec.took(r, next, st, U32.inc(next), p)
    case None{}:
      Cir.Out.out_of_memory{}

def Cir.exec.bump.if(fits: Bool, r: Nat, +next: U32, +pages: U32, lim: U32, st: Cir.State) -> Cir.Out:
  match fits:
    case True{}:
      Cir.exec.bump.of(r, next, st, Cir.room(U32.add(Cir.at(next), 19), pages, lim))
    case False{}:
      Cir.Out.out_of_memory{}

def Cir.exec.alloc.if(no_out: Bool, r: Nat, +st: Cir.State) -> Cir.Out:
  match no_out st:
    case True{} Cir.State{_, _, +next, _, _, +pages, lim, _, _, _}:
      Cir.exec.bump.if(U32.is_lt(next, 214748364), r, next, pages, lim, st)
    case False{} _:
      Cir.Out.trap{}

# a register gets a new cell, all zeros, which may grow the memory; out of
# memory when the memory cannot grow. Once
# the output has begun, no cell may be taken: they would overlap
def Cir.exec.alloc(r: Nat, +st: Cir.State) -> Cir.Out:
  match st:
    case Cir.State{_, _, _, _, _, _, _, _, _, outn}:
      Cir.exec.alloc.if(U32.is_zero(outn), r, st)

def Cir.exec.emit.of(pages: Maybe<&2, U32>, v: U32, st: Cir.State) -> Cir.Out:
  match pages st:
    case Some{p} Cir.State{regs, cells, next, first, image, _, limit, input, out, outn}:
      Cir.Out.next{Cir.State{regs, cells, next, first, image, p, limit, input, Con{U32.and(v, 255), out}, U32.inc(outn)}}
    case None{} _:
      Cir.Out.out_of_memory{}

def Cir.exec.emit.if(ok: Bool, +b: U32, v: U32, +st: Cir.State) -> Cir.Out:
  match ok st:
    case True{} Cir.State{_, _, _, _, _, +pages, lim, _, _, _}:
      Cir.exec.emit.of(Cir.room(b, pages, lim), v, st)
    case False{} _:
      Cir.Out.out_of_memory{}

# the byte v (its low 8 bits) goes at the end of the output, which lies after
# the cells, at byte 20 × next; out of memory when the memory cannot grow to
# hold it
def Cir.exec.emit(v: Maybe<&2, U32>, +st: Cir.State) -> Cir.Out:
  match v st:
    case Some{x} Cir.State{_, _, +next, _, _, _, _, _, _, +outn}:
      +b = U32.add(Cir.at(next), outn)
      Cir.exec.emit.if(U32.is_lt(next, 214748365) && U32.is_ge(b, outn), b, x, st)
    case None{} _:
      Cir.Out.trap{}

def Cir.exec.then(r: Cir.Out, more: Cir.State -> Cir.Out) -> Cir.Out:
  match r:
    case Cir.Out.next{st}:
      more(st)
    case Cir.Out.halt{s, st}:
      Cir.Out.halt{s, st}
    case Cir.Out.out_of_memory{}:
      Cir.Out.out_of_memory{}
    case Cir.Out.trap{}:
      Cir.Out.trap{}
    case Cir.Out.not_done{}:
      Cir.Out.not_done{}

def Cir.exec.if.of(zero: Bool, yes: Unit -> Cir.Out, no: Unit -> Cir.Out) -> Cir.Out:
  match zero:
    case False{}:
      yes(Unit{})
    case True{}:
      no(Unit{})

def Cir.exec.if(c: Maybe<&2, U32>, yes: Unit -> Cir.Out, no: Unit -> Cir.Out) -> Cir.Out:
  match c:
    case Some{x}:
      Cir.exec.if.of(U32.is_zero(x), yes, no)
    case None{}:
      Cir.Out.trap{}

# a run of the statement s from the state st; each round of a while takes a
# unit of fuel
def Cir.exec(+fuel: Nat, s: Cir.Stmt, +st: Cir.State) -> Cir.Out:
  match fuel s:
    case _ Cir.Stmt.nop{}:
      Cir.Out.next{st}
    case _ Cir.Stmt.set{r, e}:
      Cir.exec.set(r, Cir.eval(e, st), st)
    case _ Cir.Stmt.store{k, c, v}:
      Cir.exec.store(k, Cir.eval(c, st), Cir.eval(v, st), st)
    case _ Cir.Stmt.alloc{r}:
      Cir.exec.alloc(r, st)
    case _ Cir.Stmt.emit{v}:
      Cir.exec.emit(Cir.eval(v, st), st)
    case _ Cir.Stmt.seq{a, b}:
      Cir.exec.then(Cir.exec(fuel, a, st), t => Cir.exec(fuel, b, t))
    case _ Cir.Stmt.if{c, t, e}:
      Cir.exec.if(Cir.eval(c, st), u => Cir.exec(fuel, t, st), u => Cir.exec(fuel, e, st))
    case 0n Cir.Stmt.while{_, _}:
      Cir.Out.not_done{}
    case 1n+f Cir.Stmt.while{+c, +body}:
      Cir.exec.if(Cir.eval(c, st),
        u => Cir.exec.then(Cir.exec(f, body, st), t => Cir.exec(f, Cir.Stmt.while{c, body}, t)),
        u => Cir.Out.next{st})
    case _ Cir.Stmt.halt{s}:
      Cir.Out.halt{s, st}

# Translation
# -----------
#
# Cir.module: the module of a Cir program, with the book's cells as the data
# of its memory, from byte 20. Its function run (W5) keeps, in its locals 2 to
# 7, the status it returns, the first cell never used, the output's length and
# three scratch values; register r of the program is local 8 + r. Every
# branch out of run is the last instruction of a block of its own (W4). Its
# function alloc takes the input's bytes just after the book's cells.

def Cir.l.status() -> U32:
  2

def Cir.l.next() -> U32:
  3

def Cir.l.outn() -> U32:
  4

def Cir.l.tmp() -> U32:
  5

def Cir.l.need() -> U32:
  6

def Cir.l.addr() -> U32:
  7

def Cir.l.reg(r: Nat) -> U32:
  U32.add(8, U32.from_nat(r))

def Cir.i.get(l: U32) -> Wasm.Instr:
  Wasm.Instr.local_get{l}

def Cir.i.set(l: U32) -> Wasm.Instr:
  Wasm.Instr.local_set{l}

def Cir.i.op(o: Wasm.Op) -> Wasm.Instr:
  Wasm.Instr.op{o}

def Cir.i.const(n: U32) -> Wasm.Instr:
  Wasm.Instr.const{n}

# the cell number on the stack, turned into its first byte, 20 × c; then acc
def Cir.code.at(acc: List<&2, Wasm.Instr>) -> List<&2, Wasm.Instr>:
  Con{Wasm.Instr.local_tee{Cir.l.tmp()}, Con{Cir.i.const(4), Con{Cir.i.op(Wasm.Op.shl{}),
    Con{Cir.i.get(Cir.l.tmp()), Con{Cir.i.const(2), Con{Cir.i.op(Wasm.Op.shl{}),
      Con{Cir.i.op(Wasm.Op.add{}), acc}}}}}}}

# an expression, whose value it leaves on the stack; then acc
def Cir.code.expr(e: Cir.Expr, acc: List<&2, Wasm.Instr>) -> List<&2, Wasm.Instr>:
  match e:
    case Cir.Expr.const{n}:
      Con{Cir.i.const(n), acc}
    case Cir.Expr.get{r}:
      Con{Cir.i.get(Cir.l.reg(r)), acc}
    case Cir.Expr.op{o, a, b}:
      Cir.code.expr(a, Cir.code.expr(b, Con{Cir.i.op(o), acc}))
    case Cir.Expr.eqz{a}:
      Cir.code.expr(a, Con{Wasm.Instr.eqz{}, acc})
    case Cir.Expr.field{k, c}:
      Cir.code.expr(c, Cir.code.at(Con{Wasm.Instr.load{U32.shln(U32.from_nat(k), 2n)}, acc}))
    case Cir.Expr.byte{i}:
      Cir.code.expr(i, Con{Cir.i.get(0), Con{Cir.i.op(Wasm.Op.add{}), Con{Wasm.Instr.load8_u{0},
        Con{Cir.i.const(255), Con{Cir.i.op(Wasm.Op.and{}), acc}}}}})
    case Cir.Expr.size{}:
      Con{Cir.i.get(1), acc}

# the status s, then a branch out of run: the label d + 1 levels out, from a
# block of its own at d levels inside run's block
def Cir.code.exit(s: U32, d: Nat) -> Wasm.Instr:
  Wasm.Instr.block{[Cir.i.const(s), Cir.i.set(Cir.l.status()), Wasm.Instr.br{U32.from_nat(1n+d)}]}

# the instructions cond, which leave a Bool; when it is 0, out of memory
def Cir.code.unless(cond: List<&2, Wasm.Instr>, d: Nat, acc: List<&2, Wasm.Instr>) -> List<&2, Wasm.Instr>:
  Con{Wasm.Instr.block{List.append(&2, Wasm.Instr, cond, [Wasm.Instr.br_if{0}, Cir.code.exit(1, 1n+d)])}, acc}

# the memory grows to the pages in local need, when it has fewer; out of
# memory when it cannot
def Cir.code.grow(d: Nat, acc: List<&2, Wasm.Instr>) -> List<&2, Wasm.Instr>:
  Con{Wasm.Instr.block{Con{Cir.i.get(Cir.l.need()), Con{Wasm.Instr.memory_size{}, Con{Cir.i.op(Wasm.Op.le_u{}),
    Con{Wasm.Instr.br_if{0},
      Cir.code.unless([Cir.i.get(Cir.l.need()), Wasm.Instr.memory_size{}, Cir.i.op(Wasm.Op.sub{}),
        Wasm.Instr.memory_grow{}, Cir.i.const(4294967295), Cir.i.op(Wasm.Op.ne{})], 1n+d, [])}}}}}, acc}

# the pages (b >> 16) + 1 that the byte b on the stack needs, into local need
def Cir.code.need(acc: List<&2, Wasm.Instr>) -> List<&2, Wasm.Instr>:
  Con{Cir.i.const(16), Con{Cir.i.op(Wasm.Op.shr_u{}), Con{Cir.i.const(1), Con{Cir.i.op(Wasm.Op.add{}),
    Con{Cir.i.set(Cir.l.need()), acc}}}}}

# the five fields of the cell at the byte in local addr, made 0
def Cir.code.zero(acc: List<&2, Wasm.Instr>) -> List<&2, Wasm.Instr>:
  Con{Cir.i.get(Cir.l.addr()), Con{Cir.i.const(0), Con{Wasm.Instr.store{0},
  Con{Cir.i.get(Cir.l.addr()), Con{Cir.i.const(0), Con{Wasm.Instr.store{4},
  Con{Cir.i.get(Cir.l.addr()), Con{Cir.i.const(0), Con{Wasm.Instr.store{8},
  Con{Cir.i.get(Cir.l.addr()), Con{Cir.i.const(0), Con{Wasm.Instr.store{12},
  Con{Cir.i.get(Cir.l.addr()), Con{Cir.i.const(0), Con{Wasm.Instr.store{16}, acc}}}}}}}}}}}}}}}

# Cir.exec.alloc: a new cell, when the memory can grow to hold it; then the
# cell made 0
def Cir.code.alloc(+r: U32, +d: Nat, acc: List<&2, Wasm.Instr>) -> List<&2, Wasm.Instr>:
  Cir.code.unless([Cir.i.get(Cir.l.next()), Cir.i.const(214748364), Cir.i.op(Wasm.Op.lt_u{})], d,
    Con{Cir.i.get(Cir.l.next()), Cir.code.at(Con{Cir.i.const(19), Con{Cir.i.op(Wasm.Op.add{}),
      Cir.code.need(Cir.code.grow(d,
        Con{Cir.i.get(Cir.l.next()), Con{Cir.i.set(r),
        Con{Cir.i.get(Cir.l.next()), Con{Cir.i.const(1), Con{Cir.i.op(Wasm.Op.add{}), Con{Cir.i.set(Cir.l.next()),
        Con{Cir.i.get(r), Cir.code.at(Con{Cir.i.set(Cir.l.addr()), Cir.code.zero(acc)})}}}}}}}))}})})

# Cir.exec.emit: the byte at 20 × next + outn, after the memory grows to hold
# it
def Cir.code.emit(v: Cir.Expr, +d: Nat, acc: List<&2, Wasm.Instr>) -> List<&2, Wasm.Instr>:
  Con{Cir.i.get(Cir.l.next()), Cir.code.at(Con{Cir.i.get(Cir.l.outn()), Con{Cir.i.op(Wasm.Op.add{}),
    Con{Cir.i.set(Cir.l.addr()),
      Cir.code.unless([Cir.i.get(Cir.l.next()), Cir.i.const(214748365), Cir.i.op(Wasm.Op.lt_u{}),
        Cir.i.get(Cir.l.addr()), Cir.i.get(Cir.l.outn()), Cir.i.op(Wasm.Op.ge_u{}), Cir.i.op(Wasm.Op.and{})], d,
        Con{Cir.i.get(Cir.l.addr()), Cir.code.need(Cir.code.grow(d,
          Con{Cir.i.get(Cir.l.addr()), Cir.code.expr(v, Con{Wasm.Instr.store8{0},
            Con{Cir.i.get(Cir.l.outn()), Con{Cir.i.const(1), Con{Cir.i.op(Wasm.Op.add{}),
              Con{Cir.i.set(Cir.l.outn()), acc}}}}})}))})}}})}

# for a result, the output's first byte, 20 × next, at byte 0, and its length
# at byte 4 (W5)
def Cir.code.result(ok: Bool) -> List<&2, Wasm.Instr>:
  match ok:
    case True{}:
      Con{Cir.i.const(0), Con{Cir.i.get(Cir.l.next()), Cir.code.at(
        [Wasm.Instr.store{0}, Cir.i.const(0), Cir.i.get(Cir.l.outn()), Wasm.Instr.store{4}])}}
    case False{}:
      []

def Cir.code.halt(+s: U32, d: Nat) -> Wasm.Instr:
  Wasm.Instr.block{Con{Cir.i.const(s), Con{Cir.i.set(Cir.l.status()),
    List.append(&2, Wasm.Instr, Cir.code.result(U32.is_zero(s)), [Wasm.Instr.br{U32.from_nat(1n+d)}])}}}

# a statement at d levels inside run's block; then acc
def Cir.code.stmt(s: Cir.Stmt, +d: Nat, acc: List<&2, Wasm.Instr>) -> List<&2, Wasm.Instr>:
  match s:
    case Cir.Stmt.nop{}:
      acc
    case Cir.Stmt.set{r, e}:
      Cir.code.expr(e, Con{Cir.i.set(Cir.l.reg(r)), acc})
    case Cir.Stmt.store{k, c, v}:
      Cir.code.expr(c, Cir.code.at(Cir.code.expr(v, Con{Wasm.Instr.store{U32.shln(U32.from_nat(k), 2n)}, acc})))
    case Cir.Stmt.alloc{r}:
      Cir.code.alloc(Cir.l.reg(r), d, acc)
    case Cir.Stmt.emit{v}:
      Cir.code.emit(v, d, acc)
    case Cir.Stmt.seq{a, b}:
      Cir.code.stmt(a, d, Cir.code.stmt(b, d, acc))
    case Cir.Stmt.if{c, t, e}:
      Con{Wasm.Instr.block{Con{
        Wasm.Instr.block{Cir.code.expr(c, Con{Wasm.Instr.eqz{}, Con{Wasm.Instr.br_if{0},
          Cir.code.stmt(t, 2n+d, [Wasm.Instr.br{1}])}})},
        Cir.code.stmt(e, 1n+d, [])}}, acc}
    case Cir.Stmt.while{c, body}:
      Con{Wasm.Instr.block{[Wasm.Instr.loop{Cir.code.expr(c, Con{Wasm.Instr.eqz{}, Con{Wasm.Instr.br_if{1},
        Cir.code.stmt(body, 2n+d, [Wasm.Instr.br{0}])}})}]}, acc}
    case Cir.Stmt.halt{s}:
      Con{Cir.code.halt(s, d), acc}

# the first byte of the input: just after cells 0 to k
def Cir.input.at(k: U32) -> U32:
  Cir.at(U32.inc(k))

# alloc(n) (W5): the first byte of the input's n bytes, just after the book's
# k cells, once the memory holds them; -1 when it cannot. The input ends below
# byte 4294967280, so that the cells after it have numbers below 2^32 / 20
def Cir.alloc(+k: U32) -> Wasm.Func:
  +a = Cir.input.at(k)
  Wasm.Func{1n, 1n, 3n, [
    Cir.i.const(4294967295), Cir.i.set(2),
    Cir.i.const(a), Cir.i.get(0), Cir.i.op(Wasm.Op.add{}), Cir.i.set(1),
    Wasm.Instr.block{[
      Cir.i.get(1), Cir.i.const(a), Cir.i.op(Wasm.Op.lt_u{}), Wasm.Instr.br_if{0},
      Cir.i.get(1), Cir.i.const(4294967280), Cir.i.op(Wasm.Op.gt_u{}), Wasm.Instr.br_if{0},
      Cir.i.get(1), Cir.i.const(1), Cir.i.op(Wasm.Op.sub{}), Cir.i.const(16), Cir.i.op(Wasm.Op.shr_u{}),
      Cir.i.const(1), Cir.i.op(Wasm.Op.add{}), Cir.i.set(3),
      Wasm.Instr.block{[
        Cir.i.get(3), Wasm.Instr.memory_size{}, Cir.i.op(Wasm.Op.le_u{}), Wasm.Instr.br_if{0},
        Cir.i.get(3), Wasm.Instr.memory_size{}, Cir.i.op(Wasm.Op.sub{}), Wasm.Instr.memory_grow{},
        Cir.i.const(4294967295), Cir.i.op(Wasm.Op.eq{}), Wasm.Instr.br_if{1}]},
      Cir.i.const(a), Cir.i.set(2)]},
    Cir.i.get(2)]}

# run(a, n) (W5): the first cell after the input, then the program; the
# status that it ends with
def Cir.run(prog: Cir.Stmt, regs: Nat, k: U32) -> Wasm.Func:
  Wasm.Func{2n, 1n, 6n+regs, [
    Cir.i.const(2), Cir.i.set(Cir.l.status()),
    Cir.i.get(0), Cir.i.get(1), Cir.i.op(Wasm.Op.add{}), Cir.i.set(Cir.l.addr()),
    Cir.i.const(U32.inc(k)), Cir.i.set(Cir.l.next()),
    Wasm.Instr.block{[Wasm.Instr.loop{Con{Cir.i.get(Cir.l.next()), Cir.code.at(
      [Cir.i.get(Cir.l.addr()), Cir.i.op(Wasm.Op.ge_u{}), Wasm.Instr.br_if{1},
       Cir.i.get(Cir.l.next()), Cir.i.const(1), Cir.i.op(Wasm.Op.add{}), Cir.i.set(Cir.l.next()),
       Wasm.Instr.br{0}])}}]},
    Wasm.Instr.block{Cir.code.stmt(prog, 0n, [])},
    Cir.i.get(Cir.l.status())]}

# the pages that bytes 0 to b - 1 need, for b above 0
def Cir.pages(b: U32) -> U32:
  U32.inc(U32.shrn(U32.sub(b, 1), 16n))

# the bytes of the word w, the lowest first; then acc
def Cir.word.bytes(+w: U32, acc: List<&2, U32>) -> List<&2, U32>:
  Con{U32.and(w, 255), Con{U32.and(U32.shrn(w, 8n), 255), Con{U32.and(U32.shrn(w, 16n), 255),
    Con{U32.shrn(w, 24n), acc}}}}

# the bytes of the cells, 20 for each: its fields in order
def Cir.bytes(cs: List<&2, Cir.Cell>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{Cir.Cell{a, b, c, d, e}, rest}:
      Cir.word.bytes(a, Cir.word.bytes(b, Cir.word.bytes(c, Cir.word.bytes(d, Cir.word.bytes(e, Cir.bytes(rest))))))

# the module of the program prog with regs registers, whose memory holds the
# cells from cell 1 (W3): memory, alloc and run
def Cir.module(prog: Cir.Stmt, regs: Nat, +cells: List<&2, Cir.Cell>) -> Wasm.Module:
  +k = Wasm.encode.len(Cir.Cell, cells)
  Wasm.Module{
    [Cir.alloc(k), Cir.run(prog, regs, k)],
    Some{Wasm.Limits{Cir.pages(Cir.input.at(k)), None{}}},
    [Wasm.Export.memory{Wasm.name.memory()}, Wasm.Export.func{Wasm.name.alloc(), 0},
     Wasm.Export.func{Wasm.name.run(), 1}],
    Some{Wasm.Segment{20, Cir.bytes(cells)}}}

# Runs
# ----
#
# Cir.result: what Cir says that a run of the module of Cir.module gives, as
# the host runs it (W5): the memory of the module's minimum, when the host
# allows that many pages; the input after the cells, when alloc can make
# room for it; then the program, from the first cell after the input, until
# it halts: with 0, its bytes; with 1, out of memory; with 2, no result.

# the cells cs, from the cell i on
def Cir.load(cs: List<&2, Cir.Cell>, +i: U32, m: Cir.Cells) -> Cir.Cells:
  match cs:
    case Nil{}:
      m
    case Con{c, rest}:
      Cir.load(rest, U32.inc(i), Cir.Cells.set(m, i, c))

def Cir.ended.halt(zero: Bool, one: Bool, two: Bool, out: List<&2, U32>) -> Wasm.Outcome:
  match zero one two:
    case True{} _ _:
      Wasm.Outcome.result{List.reverse(&2, U32, out)}
    case False{} True{} _:
      Wasm.Outcome.out_of_memory{}
    case False{} False{} True{}:
      Wasm.Outcome.no_result{}
    case False{} False{} False{}:
      Wasm.Outcome.trap{}

# how a run ends, by how its program ended; past its end, run gives the
# status 2
def Cir.ended(r: Cir.Out) -> Wasm.Outcome:
  match r:
    case Cir.Out.next{_}:
      Wasm.Outcome.no_result{}
    case Cir.Out.halt{+s, Cir.State{_, _, _, _, _, _, _, _, out, _}}:
      Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), out)
    case Cir.Out.out_of_memory{}:
      Wasm.Outcome.out_of_memory{}
    case Cir.Out.trap{}:
      Wasm.Outcome.trap{}
    case Cir.Out.not_done{}:
      Wasm.Outcome.not_done{}

# the first cell after the image's k cells whose first byte is past end, as
# run's first loop finds it
def Cir.first(+k: U32, +end: U32) -> U32:
  Bool.pick(U32, U32.is_ge(Cir.at(U32.inc(k)), end), U32.inc(k), U32.div(U32.add(end, 19), 20))

def Cir.alloc.grow(enough: Bool, can: Bool, p: U32, need: U32) -> Maybe<&2, U32>:
  match enough can:
    case True{} _:
      Some{p}
    case False{} True{}:
      Some{need}
    case False{} False{}:
      None{}

def Cir.alloc.end(bad: Bool, +end: U32, +p: U32, +lim: U32) -> Maybe<&2, U32>:
  match bad:
    case True{}:
      None{}
    case False{}:
      +need = Cir.pages(end)
      Cir.alloc.grow(U32.is_le(need, p), U32.is_le(need, lim), p, need)

# the pages of the memory after alloc(n) (Cir.alloc), when it holds p pages
# and may grow to lim: none when it gives -1
def Cir.alloc.pages(+k: U32, +n: U32, +p: U32, +lim: U32) -> Maybe<&2, U32>:
  +a = Cir.input.at(k)
  +end = U32.add(a, n)
  Cir.alloc.end(U32.is_lt(end, a) || U32.is_gt(end, 4294967280), end, p, lim)

def Cir.result.alloced(r: Maybe<&2, U32>, fuel: Nat, prog: Cir.Stmt, +regs: Nat, cells: List<&2, Cir.Cell>,
  +k: U32, +end: U32, +lim: U32, i: List<&2, U32>) -> Wasm.Outcome:
  match r:
    case None{}:
      Wasm.Outcome.out_of_memory{}
    case Some{p}:
      +first = Cir.first(k, end)
      Cir.ended(Cir.exec(fuel, prog, Cir.State{
        List.replicate(U32, regs, 0), Cir.load(cells, 1, Cir.Cells.none{}), first, first, k, p, lim, i, Nil{}, 0}))

def Cir.result.sized(n: Maybe<&2, U32>, fuel: Nat, prog: Cir.Stmt, +regs: Nat, cells: List<&2, Cir.Cell>,
  +k: U32, +p: U32, +lim: U32, +i: List<&2, U32>) -> Wasm.Outcome:
  match n:
    case None{}:
      Wasm.Outcome.out_of_memory{}
    case Some{+len}:
      Cir.result.alloced(Cir.alloc.pages(k, len, p, lim), fuel, prog, regs, cells, k,
        U32.add(Cir.input.at(k), len), lim, i)

def Cir.result.memory(ok: Bool, fuel: Nat, prog: Cir.Stmt, +regs: Nat, cells: List<&2, Cir.Cell>, +k: U32,
  +p: U32, +lim: U32, +i: List<&2, U32>) -> Wasm.Outcome:
  match ok:
    case False{}:
      Wasm.Outcome.out_of_memory{}
    case True{}:
      Cir.result.sized(Wasm.length32(i), fuel, prog, regs, cells, k, p, lim, i)

# what a run of the module of Cir.module(prog, regs, cells) on the input i
# with at most m pages gives, by Cir.exec with the fuel
def Cir.result(fuel: Nat, prog: Cir.Stmt, +regs: Nat, +cells: List<&2, Cir.Cell>, +i: List<&2, U32>, +m: U32) ->
  Wasm.Outcome:
  +k = Wasm.encode.len(Cir.Cell, cells)
  +p = Cir.pages(Cir.input.at(k))
  Cir.result.memory(U32.is_le(p, m), fuel, prog, regs, cells, k, p, Wasm.min(m, 65536), i)

# Machine
# -------
#
# The machine of C3, as a Cir program: Mach.code. A term is a graph of cells;
# a cell never changes after it is made, but for the flags that say what is
# known of it. Field 0 holds its tag (bits 0 to 5: the kernel's order of
# formers, Var 0 to Rwt 18; 32 and above for the machine's own cells), its
# quantity (bits 6 and 7), its flags (VALUE, DATA, STATIC, K, OWNED: bits 8
# to 12) and fv (bits 13 up): 1 + the highest free variable of its term, 0
# when it has none. Field 1 counts the pointers to it, or links it into a
# list. Fields 2 to 4 hold its parts: as the kernel's formers do, in order;
# a Ref holds its def's body and its name, a Lab and a Mat their name, by the
# number that the image gives it.
#
# The machine runs as the Lean machine (bootstrap/lean, Machine.lean) does,
# on closed terms: a focus, and a stack of frames, which are cells. A call or
# a λ copies its code, with pointers to its arguments: a part whose free
# variables the copy does not reach is shared, not copied. A cell whose count
# drops to 0 goes to a list of cells to reuse, and its parts lose a pointer
# when the cell is reused.

# building Cir

def M.c(n: U32) -> Cir.Expr:
  Cir.Expr.const{n}

def M.g(r: Nat) -> Cir.Expr:
  Cir.Expr.get{r}

def M.f(k: Nat, c: Cir.Expr) -> Cir.Expr:
  Cir.Expr.field{k, c}

def M.add(a: Cir.Expr, b: Cir.Expr) -> Cir.Expr:
  Cir.Expr.op{Wasm.Op.add{}, a, b}

def M.sub(a: Cir.Expr, b: Cir.Expr) -> Cir.Expr:
  Cir.Expr.op{Wasm.Op.sub{}, a, b}

def M.and(a: Cir.Expr, b: Cir.Expr) -> Cir.Expr:
  Cir.Expr.op{Wasm.Op.and{}, a, b}

def M.or(a: Cir.Expr, b: Cir.Expr) -> Cir.Expr:
  Cir.Expr.op{Wasm.Op.or{}, a, b}

def M.shl(a: Cir.Expr, b: Cir.Expr) -> Cir.Expr:
  Cir.Expr.op{Wasm.Op.shl{}, a, b}

def M.shr(a: Cir.Expr, b: Cir.Expr) -> Cir.Expr:
  Cir.Expr.op{Wasm.Op.shr_u{}, a, b}

def M.eq(a: Cir.Expr, b: Cir.Expr) -> Cir.Expr:
  Cir.Expr.op{Wasm.Op.eq{}, a, b}

def M.ne(a: Cir.Expr, b: Cir.Expr) -> Cir.Expr:
  Cir.Expr.op{Wasm.Op.ne{}, a, b}

def M.lt(a: Cir.Expr, b: Cir.Expr) -> Cir.Expr:
  Cir.Expr.op{Wasm.Op.lt_u{}, a, b}

def M.le(a: Cir.Expr, b: Cir.Expr) -> Cir.Expr:
  Cir.Expr.op{Wasm.Op.le_u{}, a, b}

def M.gt(a: Cir.Expr, b: Cir.Expr) -> Cir.Expr:
  Cir.Expr.op{Wasm.Op.gt_u{}, a, b}

def M.ge(a: Cir.Expr, b: Cir.Expr) -> Cir.Expr:
  Cir.Expr.op{Wasm.Op.ge_u{}, a, b}

def M.not(a: Cir.Expr) -> Cir.Expr:
  Cir.Expr.eqz{a}

def M.set(r: Nat, e: Cir.Expr) -> Cir.Stmt:
  Cir.Stmt.set{r, e}

def M.st(k: Nat, c: Cir.Expr, v: Cir.Expr) -> Cir.Stmt:
  Cir.Stmt.store{k, c, v}

def M.do(ss: List<&2, Cir.Stmt>) -> Cir.Stmt:
  match ss:
    case Nil{}:
      Cir.Stmt.nop{}
    case Con{s, rest}:
      Cir.Stmt.seq{s, M.do(rest)}

def M.if(c: Cir.Expr, t: Cir.Stmt, e: Cir.Stmt) -> Cir.Stmt:
  Cir.Stmt.if{c, t, e}

def M.when(c: Cir.Expr, t: Cir.Stmt) -> Cir.Stmt:
  Cir.Stmt.if{c, t, Cir.Stmt.nop{}}

def M.while(c: Cir.Expr, body: Cir.Stmt) -> Cir.Stmt:
  Cir.Stmt.while{c, body}

def M.halt(s: U32) -> Cir.Stmt:
  Cir.Stmt.halt{s}

# the registers

def R.focus() -> Nat:
  0n

def R.mode() -> Nat:
  1n

def R.sp() -> Nat:
  2n

def R.pend() -> Nat:
  3n

def R.dx() -> Nat:
  4n

def R.dr() -> Nat:
  5n

def R.aq() -> Nat:
  6n

def R.am() -> Nat:
  7n

def R.c() -> Nat:
  8n

def R.h() -> Nat:
  9n

def R.tag() -> Nat:
  10n

def R.x() -> Nat:
  11n

def R.y() -> Nat:
  12n

def R.z() -> Nat:
  13n

def R.q() -> Nat:
  14n

def R.n() -> Nat:
  15n

def R.fr() -> Nat:
  16n

def R.k() -> Nat:
  17n

def R.p() -> Nat:
  18n

def R.wt() -> Nat:
  19n

def R.wenv() -> Nat:
  20n

def R.wargs() -> Nat:
  21n

def R.wa() -> Nat:
  22n

def R.wx() -> Nat:
  23n

def R.wq() -> Nat:
  24n

def R.wn() -> Nat:
  25n

def R.wres() -> Nat:
  26n

def R.wok() -> Nat:
  27n

def R.wb() -> Nat:
  28n

def R.wh() -> Nat:
  29n

def R.cs() -> Nat:
  30n

def R.csrc() -> Nat:
  31n

def R.cd() -> Nat:
  32n

def R.sdep() -> Nat:
  33n

def R.ck() -> Nat:
  34n

def R.cnew() -> Nat:
  35n

def R.cenv() -> Nat:
  36n

def R.clen() -> Nat:
  37n

def R.cj() -> Nat:
  38n

def R.croot() -> Nat:
  39n

def R.sres() -> Nat:
  40n

def R.cm() -> Nat:
  41n

def R.ds() -> Nat:
  42n

def R.dok() -> Nat:
  43n

def R.dc() -> Nat:
  44n

def R.oc() -> Nat:
  45n

def R.ow() -> Nat:
  46n

def R.ov() -> Nat:
  47n

def R.oi() -> Nat:
  48n

def R.ii() -> Nat:
  49n

def R.ib() -> Nat:
  50n

def R.il() -> Nat:
  51n

def R.iu() -> Nat:
  52n

def R.iw() -> Nat:
  53n

def R.ij() -> Nat:
  54n

def R.ss() -> Nat:
  55n

def R.ssrc() -> Nat:
  56n

def R.scut() -> Nat:
  57n

def R.sroot() -> Nat:
  58n

def R.sk() -> Nat:
  59n

def R.snew() -> Nat:
  60n

def R.samt() -> Nat:
  61n

def R.t1() -> Nat:
  62n

def R.t2() -> Nat:
  63n

def Mach.regs() -> Nat:
  64n

# the tags of the formers, in the kernel's order

def T.var() -> U32:
  0

def T.ref() -> U32:
  1

def T.ann() -> U32:
  2

def T.let() -> U32:
  3

def T.min() -> U32:
  5

def T.lam() -> U32:
  7

def T.app() -> U32:
  8

def T.tup() -> U32:
  10

def T.prj() -> U32:
  11

def T.lab() -> U32:
  13

def T.mat() -> U32:
  14

def T.efq() -> U32:
  15

def T.rfl() -> U32:
  17

def T.rwt() -> U32:
  18

# the machine's own cells: frames (the kernel's App, Let, Tup, Rwt and Min
# with a hole), the arguments and locals of a walk, and work for a copy and a
# check

def K.app_arg() -> U32:
  32

def K.app_val() -> U32:
  33

def K.app_fun() -> U32:
  34

def K.let_in() -> U32:
  35

def K.tup_b() -> U32:
  36

def K.tup_a() -> U32:
  37

def K.rwt() -> U32:
  38

def K.min_b() -> U32:
  39

def K.min_a() -> U32:
  40

def K.arg() -> U32:
  41

def K.check() -> U32:
  44

def K.root() -> U32:
  45

# the flags

def F.value() -> U32:
  256

def F.data() -> U32:
  512

def F.static() -> U32:
  1024

def F.known() -> U32:
  2048

def F.owned() -> U32:
  4096

# the most that fv holds: a cell whose fv is this is never shared
def F.fv_max() -> U32:
  524287

# the cells that the image holds first (Mach.image): the labels of the names
# 0 to 10, then constant terms, the cache of the input's bytes, and a table
# by tag

def I.lab(id: U32) -> U32:
  U32.inc(id)

def I.nil() -> U32:
  12

def I.true() -> U32:
  13

def I.false() -> U32:
  14

def I.wnil() -> U32:
  15

# the word of 24 False bits, then WNil: 24 levels of 3 cells
def I.z24() -> U32:
  16

def I.ref_main() -> U32:
  88

def I.cache() -> U32:
  89

# by tag t, the cell I.table() + t holds the mask of its pointers in field 2
# (1 for field 2, 2 for 3, 4 for 4), the binders above each in field 3 (2
# bits each, the field 2's lowest) and 1 in field 4 when a term of the tag is
# a value by its form
def I.table() -> U32:
  345

# the first cell of the book's defs
def I.book() -> U32:
  364

# the names that the machine knows, by number

def N.unit() -> U32:
  0

def N.nil() -> U32:
  1

def N.con() -> U32:
  2

def N.u32() -> U32:
  3

def N.wnil() -> U32:
  4

def N.wcon() -> U32:
  5

def N.true() -> U32:
  6

def N.false() -> U32:
  7

def N.q0() -> U32:
  8

def N.q1() -> U32:
  9

def N.q2() -> U32:
  10

def N.main() -> U32:
  11

# the parts of a cell

def M.tag(c: Cir.Expr) -> Cir.Expr:
  M.and(M.f(0n, c), M.c(63))

def M.q(c: Cir.Expr) -> Cir.Expr:
  M.and(M.shr(M.f(0n, c), M.c(6)), M.c(3))

def M.flag(c: Cir.Expr, flag: U32) -> Cir.Expr:
  M.ne(M.and(M.f(0n, c), M.c(flag)), M.c(0))

def M.fv(c: Cir.Expr) -> Cir.Expr:
  M.shr(M.f(0n, c), M.c(13))

# the entry of the table by tag for the cell c, a term
def M.entry(k: Nat, c: Cir.Expr) -> Cir.Expr:
  M.f(k, M.add(M.c(I.table()), M.tag(c)))

# the cell in register r gains a pointer, unless it is none or one of the
# image's
def M.inc(+r: Nat) -> Cir.Stmt:
  M.when(M.ne(M.g(r), M.c(0)),
    M.when(M.not(M.flag(M.g(r), F.static())),
      M.st(1n, M.g(r), M.add(M.f(1n, M.g(r)), M.c(1)))))

# the cell in register r loses a pointer; at 0 it goes to the list of cells
# to reuse, the pend list
def M.dec(+r: Nat) -> Cir.Stmt:
  M.when(M.ne(M.g(r), M.c(0)),
    M.when(M.not(M.flag(M.g(r), F.static())), M.do([
      M.set(R.dr(), M.sub(M.f(1n, M.g(r)), M.c(1))),
      M.st(1n, M.g(r), M.g(R.dr())),
      M.when(M.eq(M.g(R.dr()), M.c(0)), M.do([
        M.st(1n, M.g(r), M.g(R.pend())),
        M.set(R.pend(), M.g(r))]))])))

# the part in field k of the cell aq loses a pointer, when the mask am says it
# is one
def M.dec.part(k: Nat, bit: U32) -> Cir.Stmt:
  M.when(M.ne(M.and(M.g(R.am()), M.c(bit)), M.c(0)), M.do([
    M.set(R.dx(), M.f(k, M.g(R.aq()))),
    M.dec(R.dx())]))

# register r gets a cell, all zeros: the first of the pend list, whose parts
# then lose a pointer, or a new one
def M.alloc(+r: Nat) -> Cir.Stmt:
  M.if(M.ne(M.g(R.pend()), M.c(0)), M.do([
    M.set(R.aq(), M.g(R.pend())),
    M.set(R.pend(), M.f(1n, M.g(R.aq()))),
    M.if(M.lt(M.tag(M.g(R.aq())), M.c(32)),
      M.set(R.am(), M.entry(2n, M.g(R.aq()))),
      M.set(R.am(), M.c(0))),
    M.dec.part(2n, 1),
    M.dec.part(3n, 2),
    M.dec.part(4n, 4),
    M.st(0n, M.g(R.aq()), M.c(0)),
    M.st(1n, M.g(R.aq()), M.c(0)),
    M.st(2n, M.g(R.aq()), M.c(0)),
    M.st(3n, M.g(R.aq()), M.c(0)),
    M.st(4n, M.g(R.aq()), M.c(0)),
    M.set(r, M.g(R.aq()))]),
    Cir.Stmt.alloc{r})

# register r gets a new cell: the header h, one pointer to it, and the fields
# a, b and c
def M.make(+r: Nat, h: Cir.Expr, a: Cir.Expr, b: Cir.Expr, c: Cir.Expr) -> Cir.Stmt:
  M.do([
    M.alloc(r),
    M.st(0n, M.g(r), h),
    M.st(1n, M.g(r), M.c(1)),
    M.st(2n, M.g(r), a),
    M.st(3n, M.g(r), b),
    M.st(4n, M.g(r), c)])

# the machine's own cell in register r goes to the pend list: its parts lose
# no pointer when it is reused
def M.release(+r: Nat) -> Cir.Stmt:
  M.do([
    M.st(1n, M.g(r), M.g(R.pend())),
    M.set(R.pend(), M.g(r))])

# a new frame on the stack: the header h, and the fields a and b
def M.push(h: Cir.Expr, a: Cir.Expr, b: Cir.Expr) -> Cir.Stmt:
  M.do([
    M.alloc(R.fr()),
    M.st(0n, M.g(R.fr()), h),
    M.st(1n, M.g(R.fr()), M.g(R.sp())),
    M.st(2n, M.g(R.fr()), a),
    M.st(3n, M.g(R.fr()), b),
    M.set(R.sp(), M.g(R.fr()))])

# the top frame leaves the stack, and goes to the pend list
def M.pop() -> Cir.Stmt:
  M.do([
    M.set(R.fr(), M.g(R.sp())),
    M.set(R.sp(), M.f(1n, M.g(R.fr()))),
    M.release(R.fr())])

# a header of the kind k, the quantity q and the flags fl
def M.header(k: U32, q: Cir.Expr, fl: Cir.Expr) -> Cir.Expr:
  M.or(M.or(M.c(k), M.shl(q, M.c(6))), fl)

# Data: register dok gets 1 when the term in register r is Data (Lab, Rfl, or a
# pair of Data whose first field is Data or dead), else 0. Each cell that the
# check reaches is flagged DATA at once, and is not checked again: when the
# check fails, the run ends with no result, so no flag is ever read wrong
def M.data(+r: Nat) -> Cir.Stmt:
  M.do([
    M.set(R.dok(), M.c(1)),
    M.set(R.ds(), M.c(0)),
    M.make(R.dc(), M.c(K.check()), M.g(r), M.c(0), M.c(0)),
    M.st(1n, M.g(R.dc()), M.g(R.ds())),
    M.set(R.ds(), M.g(R.dc())),
    M.while(M.and(M.ne(M.g(R.ds()), M.c(0)), M.g(R.dok())), M.do([
      M.set(R.dc(), M.g(R.ds())),
      M.set(R.ds(), M.f(1n, M.g(R.dc()))),
      M.set(R.t1(), M.f(2n, M.g(R.dc()))),
      M.release(R.dc()),
      M.when(M.not(M.flag(M.g(R.t1()), F.data())),
        M.if(M.or(M.eq(M.tag(M.g(R.t1())), M.c(T.lab())), M.eq(M.tag(M.g(R.t1())), M.c(T.rfl()))),
          M.st(0n, M.g(R.t1()), M.or(M.f(0n, M.g(R.t1())), M.c(F.data()))),
          M.if(M.eq(M.tag(M.g(R.t1())), M.c(T.tup())), M.do([
            M.st(0n, M.g(R.t1()), M.or(M.f(0n, M.g(R.t1())), M.c(F.data()))),
            M.make(R.dc(), M.c(K.check()), M.f(3n, M.g(R.t1())), M.c(0), M.c(0)),
            M.st(1n, M.g(R.dc()), M.g(R.ds())),
            M.set(R.ds(), M.g(R.dc())),
            M.when(M.ne(M.q(M.g(R.t1())), M.c(0)), M.do([
              M.make(R.dc(), M.c(K.check()), M.f(2n, M.g(R.t1())), M.c(0), M.c(0)),
              M.st(1n, M.g(R.dc()), M.g(R.ds())),
              M.set(R.ds(), M.g(R.dc()))]))]),
            M.set(R.dok(), M.c(0)))))])),
    M.while(M.ne(M.g(R.ds()), M.c(0)), M.do([
      M.set(R.dc(), M.g(R.ds())),
      M.set(R.ds(), M.f(1n, M.g(R.dc()))),
      M.release(R.dc())]))])

# a when c is 1, b when c is 0: by masks, with no branch
def M.pick(+c: Cir.Expr, a: Cir.Expr, b: Cir.Expr) -> Cir.Expr:
  M.or(M.and(a, M.sub(M.c(0), c)), M.and(b, M.sub(c, M.c(1))))

def M.max(+a: Cir.Expr, +b: Cir.Expr) -> Cir.Expr:
  M.pick(M.gt(a, b), a, b)

# field k (2, 3 or 4, in register rk) of the cell in register rd gets v
def M.put(+rd: Nat, +rk: Nat, +v: Cir.Expr) -> Cir.Stmt:
  M.if(M.eq(M.g(rk), M.c(2)), M.st(2n, M.g(rd), v),
    M.if(M.eq(M.g(rk), M.c(3)), M.st(3n, M.g(rd), v), M.st(4n, M.g(rd), v)))

# field k (2, 3 or 4) of the cell c
def M.get(+c: Cir.Expr, +k: Cir.Expr) -> Cir.Expr:
  M.pick(M.eq(k, M.c(2)), M.f(2n, c), M.pick(M.eq(k, M.c(3)), M.f(3n, c), M.f(4n, c)))

# the binders above field k (2, 3 or 4) of the term cell c, by the table
def M.bump(+c: Cir.Expr, +k: Cir.Expr) -> Cir.Expr:
  M.and(M.shr(M.entry(3n, c), M.shl(M.sub(k, M.c(2)), M.c(1))), M.c(3))

# A copy makes its new cells in place: a new cell holds the parts of its
# source until each is copied in turn, and bits 8 to 10 of its field 0 (for
# fields 2 to 4) say which are still to copy. The new cells whose parts are
# not all copied form a stack, linked by field 1, each above the cell that
# holds it; a register holds the depth of the top one, under the binders of
# the copy. A cell leaves the stack once its parts are copied: its fv is then
# known, and field 1 counts its one pointer. A root cell, a Prj, holds the
# result.

# the bit, among those still to copy, of field k
def M.todo.bit(+k: Cir.Expr) -> Cir.Expr:
  M.shl(M.c(64), k)

# the bits of the parts that the new cell c still has to copy
def M.todo(+c: Cir.Expr) -> Cir.Expr:
  M.and(M.f(0n, c), M.c(1792))

# the first field that the new cell c still has to copy
def M.todo.first(+c: Cir.Expr) -> Cir.Expr:
  M.pick(M.ne(M.and(M.f(0n, c), M.c(256)), M.c(0)), M.c(2),
    M.pick(M.ne(M.and(M.f(0n, c), M.c(512)), M.c(0)), M.c(3), M.c(4)))

# the field of the new cell c that its last copied part is in: the highest
# of its pointers that it does not still have to copy
def M.todo.last(+c: Cir.Expr) -> Cir.Expr:
  M.pick(M.eq(M.and(M.sub(M.entry(2n, c), M.shr(M.todo(c), M.c(8))), M.c(4)), M.c(4)), M.c(4),
    M.pick(M.eq(M.and(M.sub(M.entry(2n, c), M.shr(M.todo(c), M.c(8))), M.c(2)), M.c(2)), M.c(3), M.c(2)))

# fv of a part: in t1, its contribution to the fv of the cell c, whose field
# k it is, under the binders of the table
def M.fv.part(+c: Nat, k: Nat, bit: U32, shift: U32) -> Cir.Stmt:
  M.when(M.ne(M.and(M.entry(2n, M.g(c)), M.c(bit)), M.c(0)), M.do([
    M.set(R.t1(), M.fv(M.f(k, M.g(c)))),
    M.set(R.t2(), M.and(M.shr(M.entry(3n, M.g(c)), M.c(shift)), M.c(3))),
    M.if(M.eq(M.g(R.t1()), M.c(F.fv_max())),
      M.set(R.cm(), M.c(F.fv_max())),
      M.when(M.gt(M.g(R.t1()), M.g(R.t2())),
        M.when(M.gt(M.sub(M.g(R.t1()), M.g(R.t2())), M.g(R.cm())),
          M.when(M.ne(M.g(R.cm()), M.c(F.fv_max())),
            M.set(R.cm(), M.sub(M.g(R.t1()), M.g(R.t2())))))))]))

# the new cell c, once its parts are copied, leaves the stack: its fv is the
# most of its parts' fv, less the binders above each, at most fv_max; and one
# pointer points to it
def M.finish(+c: Nat) -> Cir.Stmt:
  M.do([
    M.st(1n, M.g(c), M.c(1)),
    M.set(R.cm(), M.c(0)),
    M.fv.part(c, 2n, 1, 0),
    M.fv.part(c, 3n, 2, 2),
    M.fv.part(c, 4n, 4, 4),
    M.st(0n, M.g(c), M.or(M.and(M.f(0n, M.g(c)), M.c(255)), M.shl(M.g(R.cm()), M.c(13))))])

# v when small is 1, fv_max when it is 0: by masks, with no branch
def M.if.e(+small: Cir.Expr, v: Cir.Expr) -> Cir.Expr:
  M.or(M.and(v, M.sub(M.c(0), small)), M.and(M.c(F.fv_max()), M.sub(small, M.c(1))))

# a new variable i in register r: its fv is i + 1, at most fv_max
def M.var(+r: Nat, +i: Cir.Expr) -> Cir.Stmt:
  M.make(r, M.or(M.c(T.var()), M.shl(
    M.if.e(M.lt(i, M.c(524286)), M.add(i, M.c(1))), M.c(13))), i, M.c(0), M.c(0))

# register r gets a new cell for the part in register src, which the cell in
# register top holds in field k: the source's fields, all to copy; it goes on
# the stack in register s
def M.copy.push(+r: Nat, +src: Nat, +top: Nat, +k: Nat, +s: Nat) -> Cir.Stmt:
  M.do([
    M.make(r, M.or(M.and(M.f(0n, M.g(src)), M.c(255)), M.shl(M.entry(2n, M.g(src)), M.c(8))),
      M.f(2n, M.g(src)), M.f(3n, M.g(src)), M.f(4n, M.g(src))),
    M.st(1n, M.g(r), M.g(s)),
    M.put(top, k, M.g(r)),
    M.set(s, M.g(r))])

# the root of a copy of the term in register src, in register r: a Prj whose
# part is to copy
def M.copy.root(+r: Nat, +src: Nat) -> Cir.Stmt:
  M.do([
    M.make(r, M.c(U32.or(T.prj(), 256)), M.g(src), M.c(0), M.c(0)),
    M.st(1n, M.g(r), M.c(0))])

# register r gets the copy's result in the root cell in register root; the
# root goes to the pend list, as a cell whose parts lose no pointer
def M.copy.end(+r: Nat, +root: Nat) -> Cir.Stmt:
  M.do([
    M.set(r, M.f(2n, M.g(root))),
    M.st(0n, M.g(root), M.c(K.root())),
    M.release(root)])

# register r gets the term in register v with each free variable from the
# cutoff 0 on moved up by samt, as Term.shift does; a part whose free
# variables are all below its cutoff is shared
def M.shift(+r: Nat, +v: Nat) -> Cir.Stmt:
  M.do([
    M.copy.root(R.sroot(), v),
    M.set(R.ss(), M.g(R.sroot())),
    M.set(R.scut(), M.c(0)),
    M.while(M.ne(M.g(R.ss()), M.c(0)), M.do([
      M.set(R.snew(), M.g(R.ss())),
      M.if(M.eq(M.todo(M.g(R.snew())), M.c(0)), M.do([
        M.set(R.ss(), M.f(1n, M.g(R.snew()))),
        M.finish(R.snew()),
        M.when(M.ne(M.g(R.ss()), M.c(0)),
          M.set(R.scut(), M.sub(M.g(R.scut()), M.bump(M.g(R.ss()), M.todo.last(M.g(R.ss()))))))]),
      M.do([
        M.set(R.sk(), M.todo.first(M.g(R.snew()))),
        M.st(0n, M.g(R.snew()), M.sub(M.f(0n, M.g(R.snew())), M.todo.bit(M.g(R.sk())))),
        M.set(R.ssrc(), M.get(M.g(R.snew()), M.g(R.sk()))),
        M.set(R.sdep(), M.add(M.g(R.scut()), M.bump(M.g(R.snew()), M.g(R.sk())))),
        M.if(M.and(M.lt(M.fv(M.g(R.ssrc())), M.c(F.fv_max())), M.le(M.fv(M.g(R.ssrc())), M.g(R.sdep()))),
          M.inc(R.ssrc()),
          M.if(M.eq(M.tag(M.g(R.ssrc())), M.c(T.var())),
            M.if(M.lt(M.f(2n, M.g(R.ssrc())), M.g(R.sdep())),
              M.inc(R.ssrc()),
              M.do([
                M.var(R.t1(), M.add(M.f(2n, M.g(R.ssrc())), M.g(R.samt()))),
                M.put(R.snew(), R.sk(), M.g(R.t1()))])),
            M.do([
              M.copy.push(R.t1(), R.ssrc(), R.snew(), R.sk(), R.ss()),
              M.set(R.scut(), M.g(R.sdep()))])))]))])),
    M.copy.end(r, R.sroot())])

# the part in register csrc, which the new cell cnew holds in field ck, at
# the depth cj: shared, when its free variables are all below cj; for a
# variable cj + j, the local j of the list in cenv, of clen locals, shifted
# by cj; for a variable past them, as the kernel's Env.sub does, j - clen;
# else a new cell on the stack
def M.copy.part() -> Cir.Stmt:
  M.if(M.and(M.lt(M.fv(M.g(R.csrc())), M.c(F.fv_max())), M.le(M.fv(M.g(R.csrc())), M.g(R.cj()))),
    M.inc(R.csrc()),
    M.if(M.eq(M.tag(M.g(R.csrc())), M.c(T.var())),
      M.if(M.lt(M.f(2n, M.g(R.csrc())), M.g(R.cj())),
        M.inc(R.csrc()),
        M.do([
          M.set(R.t1(), M.sub(M.f(2n, M.g(R.csrc())), M.g(R.cj()))),
          M.if(M.lt(M.g(R.t1()), M.g(R.clen())), M.do([
            M.set(R.t2(), M.g(R.cenv())),
            M.while(M.ne(M.g(R.t1()), M.c(0)), M.do([
              M.set(R.t2(), M.f(1n, M.g(R.t2()))),
              M.set(R.t1(), M.sub(M.g(R.t1()), M.c(1)))])),
            M.set(R.t2(), M.f(2n, M.g(R.t2()))),
            M.if(M.or(M.eq(M.fv(M.g(R.t2())), M.c(0)), M.eq(M.g(R.cj()), M.c(0))),
              M.do([M.inc(R.t2()), M.put(R.cnew(), R.ck(), M.g(R.t2()))]),
              M.do([
                M.set(R.samt(), M.g(R.cj())),
                M.shift(R.sres(), R.t2()),
                M.put(R.cnew(), R.ck(), M.g(R.sres()))]))]),
          M.do([
            M.var(R.t2(), M.sub(M.f(2n, M.g(R.csrc())), M.g(R.clen()))),
            M.put(R.cnew(), R.ck(), M.g(R.t2()))]))])),
      M.do([
        M.copy.push(R.t2(), R.csrc(), R.cnew(), R.ck(), R.cs()),
        M.set(R.cd(), M.g(R.cj()))])))

# register r gets the copy of the term in register src, as Term.subst gives
# it at the depth 0, with the list of locals in cenv, of clen locals
def M.copy(+r: Nat, +src: Nat) -> Cir.Stmt:
  M.do([
    M.copy.root(R.croot(), src),
    M.set(R.cs(), M.g(R.croot())),
    M.set(R.cd(), M.c(0)),
    M.while(M.ne(M.g(R.cs()), M.c(0)), M.do([
      M.set(R.cnew(), M.g(R.cs())),
      M.if(M.eq(M.todo(M.g(R.cnew())), M.c(0)), M.do([
        M.set(R.cs(), M.f(1n, M.g(R.cnew()))),
        M.finish(R.cnew()),
        M.when(M.ne(M.g(R.cs()), M.c(0)),
          M.set(R.cd(), M.sub(M.g(R.cd()), M.bump(M.g(R.cs()), M.todo.last(M.g(R.cs()))))))]),
      M.do([
        M.set(R.ck(), M.todo.first(M.g(R.cnew()))),
        M.st(0n, M.g(R.cnew()), M.sub(M.f(0n, M.g(R.cnew())), M.todo.bit(M.g(R.ck())))),
        M.set(R.csrc(), M.get(M.g(R.cnew()), M.g(R.ck()))),
        M.set(R.cj(), M.add(M.g(R.cd()), M.bump(M.g(R.cnew()), M.g(R.ck())))),
        M.copy.part()]))])),
    M.copy.end(r, R.croot())])

# the run goes on when c is not 0; else it ends with no result
def M.need(c: Cir.Expr, then: Cir.Stmt) -> Cir.Stmt:
  M.if(c, then, M.halt(2))

# the term of an argument cell loses a pointer when the cell owned it; the
# cell goes to the pend list
def M.release.arg(+a: Nat) -> Cir.Stmt:
  M.do([
    M.when(M.flag(M.g(a), F.owned()), M.do([M.set(R.dx(), M.f(2n, M.g(a))), M.dec(R.dx())])),
    M.release(a)])

# all the cells of the list in register l go to the pend list
def M.release.all(+l: Nat) -> Cir.Stmt:
  M.while(M.ne(M.g(l), M.c(0)), M.do([
    M.set(R.wa(), M.g(l)),
    M.set(l, M.f(1n, M.g(R.wa()))),
    M.release.arg(R.wa())]))

# the quantity of a pair's first field, the pair's in register r used at q
def M.fld(+r: Cir.Expr, q: Cir.Expr) -> Cir.Expr:
  M.pick(M.eq(r, M.c(1)), q, r)

# a λ, a λ-match or Efq: a node of a case tree, which takes an argument, by
# its tag t
def M.takes(+t: Cir.Expr) -> Cir.Expr:
  M.or(M.or(M.eq(t, M.c(T.lam())), M.eq(t, M.c(T.prj()))), M.or(M.eq(t, M.c(T.mat())), M.eq(t, M.c(T.efq()))))

# a λ of the case tree binds the first argument: both live or both dead, and
# Data when the λ's quantity is 2
def M.walk.lam() -> Cir.Stmt:
  M.if(M.eq(M.g(R.wargs()), M.c(0)), M.set(R.wres(), M.c(2)), M.do([
    M.set(R.wa(), M.g(R.wargs())),
    M.set(R.wq(), M.q(M.g(R.wa()))),
    M.set(R.wx(), M.f(2n, M.g(R.wa()))),
    M.set(R.wok(), M.eq(M.ne(M.q(M.g(R.wt())), M.c(0)), M.ne(M.g(R.wq()), M.c(0)))),
    M.when(M.and(M.g(R.wok()), M.eq(M.q(M.g(R.wt())), M.c(2))), M.do([
      M.data(R.wx()),
      M.set(R.wok(), M.g(R.dok()))])),
    M.if(M.g(R.wok()), M.do([
      M.set(R.wargs(), M.f(1n, M.g(R.wa()))),
      M.st(1n, M.g(R.wa()), M.g(R.wenv())),
      M.set(R.wenv(), M.g(R.wa())),
      M.set(R.wn(), M.add(M.g(R.wn()), M.c(1))),
      M.set(R.wt(), M.f(2n, M.g(R.wt())))]),
      M.set(R.wres(), M.c(3)))]))

# a λ-match of pairs splits the first argument, a live pair, into its fields
def M.walk.prj() -> Cir.Stmt:
  M.if(M.eq(M.g(R.wargs()), M.c(0)), M.set(R.wres(), M.c(2)), M.do([
    M.set(R.wa(), M.g(R.wargs())),
    M.set(R.wq(), M.q(M.g(R.wa()))),
    M.set(R.wx(), M.f(2n, M.g(R.wa()))),
    M.if(M.and(M.ne(M.g(R.wq()), M.c(0)), M.eq(M.tag(M.g(R.wx())), M.c(T.tup()))), M.do([
      M.set(R.wb(), M.q(M.g(R.wx()))),
      M.make(R.wh(),
        M.header(K.arg(), M.fld(M.g(R.wb()), M.g(R.wq())),
          M.and(M.and(M.f(0n, M.g(R.wa())), M.c(F.known())), M.sub(M.c(0), M.ne(M.g(R.wb()), M.c(0))))),
        M.f(2n, M.g(R.wx())), M.c(0), M.c(0)),
      M.st(1n, M.g(R.wh()), M.g(R.wa())),
      M.st(2n, M.g(R.wa()), M.f(3n, M.g(R.wx()))),
      M.set(R.wargs(), M.g(R.wh())),
      M.set(R.wt(), M.f(2n, M.g(R.wt())))]),
      M.set(R.wres(), M.c(3)))]))

# a λ-match of labels takes its first case on the first argument's label, a
# live one; else its other case, on the same argument
def M.walk.mat() -> Cir.Stmt:
  M.if(M.eq(M.g(R.wargs()), M.c(0)), M.set(R.wres(), M.c(2)), M.do([
    M.set(R.wa(), M.g(R.wargs())),
    M.set(R.wq(), M.q(M.g(R.wa()))),
    M.set(R.wx(), M.f(2n, M.g(R.wa()))),
    M.if(M.and(M.ne(M.g(R.wq()), M.c(0)), M.eq(M.tag(M.g(R.wx())), M.c(T.lab()))),
      M.if(M.eq(M.f(2n, M.g(R.wx())), M.f(2n, M.g(R.wt()))), M.do([
        M.set(R.wargs(), M.f(1n, M.g(R.wa()))),
        M.release.arg(R.wa()),
        M.set(R.wt(), M.f(3n, M.g(R.wt())))]),
      M.do([
        M.st(0n, M.g(R.wa()), M.or(M.f(0n, M.g(R.wa())), M.c(F.known()))),
        M.set(R.wt(), M.f(4n, M.g(R.wt())))])),
      M.set(R.wres(), M.c(3)))]))

# App q f (Var v), where f's head takes an argument: the local v goes first
# among the arguments (a free variable when there is no local v); any other
# App is a leaf
def M.walk.app() -> Cir.Stmt:
  M.do([
    M.set(R.wx(), M.f(3n, M.g(R.wt()))),
    M.if(M.ne(M.tag(M.g(R.wx())), M.c(T.var())), M.set(R.wres(), M.c(1)), M.do([
      M.set(R.wh(), M.f(2n, M.g(R.wt()))),
      M.while(M.eq(M.tag(M.g(R.wh())), M.c(T.app())), M.set(R.wh(), M.f(2n, M.g(R.wh())))),
      M.set(R.wok(), M.takes(M.tag(M.g(R.wh())))),
      M.if(M.not(M.g(R.wok())), M.set(R.wres(), M.c(1)), M.do([
        M.set(R.wb(), M.f(2n, M.g(R.wx()))),
        M.if(M.lt(M.g(R.wb()), M.g(R.wn())), M.do([
          M.set(R.wh(), M.g(R.wenv())),
          M.while(M.ne(M.g(R.wb()), M.c(0)), M.do([
            M.set(R.wh(), M.f(1n, M.g(R.wh()))),
            M.set(R.wb(), M.sub(M.g(R.wb()), M.c(1)))])),
          M.make(R.wa(), M.header(K.arg(), M.q(M.g(R.wt())), M.and(M.f(0n, M.g(R.wh())), M.c(F.known()))),
            M.f(2n, M.g(R.wh())), M.c(0), M.c(0))]),
        M.do([
          M.var(R.wx(), M.sub(M.g(R.wb()), M.g(R.wn()))),
          M.make(R.wa(), M.header(K.arg(), M.q(M.g(R.wt())), M.c(F.owned())), M.g(R.wx()), M.c(0), M.c(0))])),
        M.st(1n, M.g(R.wa()), M.g(R.wargs())),
        M.set(R.wargs(), M.g(R.wa())),
        M.set(R.wt(), M.f(2n, M.g(R.wt())))]))]))])

# the walk (Eval.walk) of the case tree in register wt on the argument list
# in wargs: wres is 1 at a leaf, 2 when the tree needs more arguments, 3 when
# there is no walk; wenv holds the wn locals that its λs bound
def M.walk() -> Cir.Stmt:
  M.do([
    M.set(R.wenv(), M.c(0)),
    M.set(R.wn(), M.c(0)),
    M.set(R.wres(), M.c(0)),
    M.while(M.eq(M.g(R.wres()), M.c(0)),
      M.if(M.eq(M.tag(M.g(R.wt())), M.c(T.lam())), M.walk.lam(),
        M.if(M.eq(M.tag(M.g(R.wt())), M.c(T.prj())), M.walk.prj(),
          M.if(M.eq(M.tag(M.g(R.wt())), M.c(T.mat())), M.walk.mat(),
            M.if(M.eq(M.tag(M.g(R.wt())), M.c(T.app())), M.walk.app(),
              M.if(M.eq(M.tag(M.g(R.wt())), M.c(T.efq())),
                M.set(R.wres(), M.pick(M.eq(M.g(R.wargs()), M.c(0)), M.c(2), M.c(3))),
                M.set(R.wres(), M.c(1))))))))])

# a call (Eval.call) of the case tree in wt on the arguments in wargs: at a
# leaf, the copy of the leaf with the walk's locals is the focus, after done,
# and the arguments left are frames; when the tree needs more arguments,
# partial; else no result
def M.call(partial: Cir.Stmt, done: Cir.Stmt) -> Cir.Stmt:
  M.do([
    M.walk(),
    M.if(M.eq(M.g(R.wres()), M.c(1)), M.do([
      M.set(R.cenv(), M.g(R.wenv())),
      M.set(R.clen(), M.g(R.wn())),
      M.copy(R.n(), R.wt()),
      M.set(R.wh(), M.c(0)),
      M.while(M.ne(M.g(R.wargs()), M.c(0)), M.do([
        M.set(R.wa(), M.g(R.wargs())),
        M.set(R.wargs(), M.f(1n, M.g(R.wa()))),
        M.st(1n, M.g(R.wa()), M.g(R.wh())),
        M.set(R.wh(), M.g(R.wa()))])),
      M.while(M.ne(M.g(R.wh()), M.c(0)), M.do([
        M.set(R.wa(), M.g(R.wh())),
        M.set(R.wh(), M.f(1n, M.g(R.wa()))),
        M.set(R.wx(), M.f(2n, M.g(R.wa()))),
        M.inc(R.wx()),
        M.push(M.header(K.app_val(), M.q(M.g(R.wa())), M.and(M.f(0n, M.g(R.wa())), M.c(F.known()))), M.g(R.wx()), M.c(0)),
        M.release.arg(R.wa())])),
      M.release.all(R.wenv()),
      done,
      M.set(R.focus(), M.g(R.n())),
      M.set(R.mode(), M.c(0))]),
    M.if(M.eq(M.g(R.wres()), M.c(2)), M.do([
      M.release.all(R.wargs()),
      M.release.all(R.wenv()),
      partial]),
      M.halt(2)))])

# the locals of a copy: the one term in register r
def M.one(+r: Nat) -> Cir.Stmt:
  M.do([
    M.make(R.wa(), M.c(K.arg()), M.g(r), M.c(0), M.c(0)),
    M.st(1n, M.g(R.wa()), M.c(0)),
    M.set(R.cenv(), M.g(R.wa())),
    M.set(R.clen(), M.c(1))])

# App q f x (Eval.redex), with the quantity in q, f in x and x in y, both owned
def M.redex() -> Cir.Stmt:
  M.if(M.eq(M.tag(M.g(R.x())), M.c(T.lam())), M.do([
    M.set(R.wok(), M.eq(M.ne(M.q(M.g(R.x())), M.c(0)), M.ne(M.g(R.q()), M.c(0)))),
    M.when(M.and(M.g(R.wok()), M.eq(M.q(M.g(R.x())), M.c(2))), M.do([
      M.data(R.y()),
      M.set(R.wok(), M.g(R.dok()))])),
    M.need(M.g(R.wok()), M.do([
      M.one(R.y()),
      M.set(R.z(), M.f(2n, M.g(R.x()))),
      M.copy(R.n(), R.z()),
      M.release(R.wa()),
      M.dec(R.y()),
      M.dec(R.x()),
      M.set(R.focus(), M.g(R.n())),
      M.set(R.mode(), M.c(0))]))]),
  M.if(M.eq(M.tag(M.g(R.x())), M.c(T.prj())),
    M.need(M.and(M.ne(M.g(R.q()), M.c(0)), M.eq(M.tag(M.g(R.y())), M.c(T.tup()))), M.do([
      M.set(R.p(), M.q(M.g(R.y()))),
      M.set(R.z(), M.f(2n, M.g(R.y()))),
      M.set(R.k(), M.f(3n, M.g(R.y()))),
      M.inc(R.z()),
      M.inc(R.k()),
      M.push(M.header(K.app_val(), M.g(R.q()), M.c(F.known())), M.g(R.k()), M.c(0)),
      M.push(M.header(K.app_val(), M.fld(M.g(R.p()), M.g(R.q())),
        M.and(M.c(F.known()), M.sub(M.c(0), M.ne(M.g(R.p()), M.c(0))))), M.g(R.z()), M.c(0)),
      M.set(R.n(), M.f(2n, M.g(R.x()))),
      M.inc(R.n()),
      M.dec(R.y()),
      M.dec(R.x()),
      M.set(R.focus(), M.g(R.n())),
      M.set(R.mode(), M.c(0))])),
  M.if(M.eq(M.tag(M.g(R.x())), M.c(T.mat())),
    M.need(M.and(M.ne(M.g(R.q()), M.c(0)), M.eq(M.tag(M.g(R.y())), M.c(T.lab()))),
      M.if(M.eq(M.f(2n, M.g(R.y())), M.f(2n, M.g(R.x()))), M.do([
        M.set(R.n(), M.f(3n, M.g(R.x()))),
        M.inc(R.n()),
        M.dec(R.y()),
        M.dec(R.x()),
        M.set(R.focus(), M.g(R.n())),
        M.set(R.mode(), M.c(0))]),
      M.do([
        M.set(R.n(), M.f(4n, M.g(R.x()))),
        M.inc(R.n()),
        M.push(M.header(K.app_val(), M.g(R.q()), M.c(F.known())), M.g(R.y()), M.c(0)),
        M.dec(R.x()),
        M.set(R.focus(), M.g(R.n())),
        M.set(R.mode(), M.c(0))]))),
  M.do([
    M.make(R.wa(), M.header(K.arg(), M.g(R.q()), M.and(M.c(F.known()), M.sub(M.c(0), M.ne(M.g(R.q()), M.c(0))))),
      M.g(R.y()), M.c(0), M.c(0)),
    M.st(1n, M.g(R.wa()), M.c(0)),
    M.set(R.wargs(), M.g(R.wa())),
    M.set(R.wh(), M.g(R.x())),
    M.while(M.eq(M.tag(M.g(R.wh())), M.c(T.app())), M.do([
      M.make(R.wa(), M.header(K.arg(), M.q(M.g(R.wh())),
        M.and(M.c(F.known()), M.sub(M.c(0), M.ne(M.q(M.g(R.wh())), M.c(0))))), M.f(3n, M.g(R.wh())), M.c(0), M.c(0)),
      M.st(1n, M.g(R.wa()), M.g(R.wargs())),
      M.set(R.wargs(), M.g(R.wa())),
      M.set(R.wh(), M.f(2n, M.g(R.wh())))])),
    M.need(M.eq(M.tag(M.g(R.wh())), M.c(T.ref())), M.do([
      M.set(R.wt(), M.f(2n, M.g(R.wh()))),
      M.need(M.ne(M.g(R.wt()), M.c(0)),
        M.call(
          M.do([
            M.make(R.n(), M.or(M.header(T.app(), M.g(R.q()), M.c(F.value())),
              M.shl(M.max(M.fv(M.g(R.x())), M.fv(M.g(R.y()))), M.c(13))), M.g(R.x()), M.g(R.y()), M.c(0)),
            M.set(R.focus(), M.g(R.n())),
            M.set(R.mode(), M.c(1))]),
          M.do([M.dec(R.y()), M.dec(R.x())])))]))]))))

# the moves of the machine (the Lean machine's move), by the focus: in mode 0
# a term to evaluate, in mode 1 a value; a step of Eval, or a move that only
# finds the next step

# Ann x T: x, a step
def M.ev.ann() -> Cir.Stmt:
  M.do([
    M.set(R.n(), M.f(2n, M.g(R.c()))),
    M.inc(R.n()),
    M.dec(R.c()),
    M.set(R.focus(), M.g(R.n()))])

# Ref k: the call of k on no arguments: a step to its leaf; or, when its case
# tree takes an argument, a value
def M.ev.ref() -> Cir.Stmt:
  M.do([
    M.set(R.wt(), M.f(2n, M.g(R.c()))),
    M.need(M.ne(M.g(R.wt()), M.c(0)), M.do([
      M.set(R.wargs(), M.c(0)),
      M.call(M.set(R.mode(), M.c(1)), M.dec(R.c()))]))])

# App q f x: f, in the frame App q □ x
def M.ev.app() -> Cir.Stmt:
  M.do([
    M.set(R.x(), M.f(2n, M.g(R.c()))),
    M.set(R.y(), M.f(3n, M.g(R.c()))),
    M.inc(R.x()),
    M.inc(R.y()),
    M.push(M.header(K.app_arg(), M.q(M.g(R.c())), M.c(0)), M.g(R.y()), M.c(0)),
    M.dec(R.c()),
    M.set(R.focus(), M.g(R.x()))])

# Let q v f: v in the frame Let q □ f, when q is live; else f with v put in,
# a step
def M.ev.let() -> Cir.Stmt:
  M.if(M.ne(M.q(M.g(R.c())), M.c(0)),
    M.do([
      M.set(R.x(), M.f(2n, M.g(R.c()))),
      M.set(R.y(), M.f(3n, M.g(R.c()))),
      M.inc(R.x()),
      M.inc(R.y()),
      M.push(M.header(K.let_in(), M.q(M.g(R.c())), M.c(0)), M.g(R.y()), M.c(0)),
      M.dec(R.c()),
      M.set(R.focus(), M.g(R.x()))]),
    M.do([
      M.set(R.y(), M.f(2n, M.g(R.c()))),
      M.one(R.y()),
      M.set(R.z(), M.f(3n, M.g(R.c()))),
      M.copy(R.n(), R.z()),
      M.release(R.wa()),
      M.dec(R.c()),
      M.set(R.focus(), M.g(R.n()))]))

# Tup q a b, not known to be a value: a in the frame Tup q □ b, when q is
# live; else b in the frame Tup q a □
def M.ev.tup() -> Cir.Stmt:
  M.do([
    M.set(R.x(), M.f(2n, M.g(R.c()))),
    M.set(R.y(), M.f(3n, M.g(R.c()))),
    M.inc(R.x()),
    M.inc(R.y()),
    M.if(M.ne(M.q(M.g(R.c())), M.c(0)),
      M.do([
        M.push(M.header(K.tup_b(), M.q(M.g(R.c())), M.c(0)), M.g(R.y()), M.c(0)),
        M.set(R.focus(), M.g(R.x()))]),
      M.do([
        M.push(M.header(K.tup_a(), M.q(M.g(R.c())), M.c(0)), M.g(R.x()), M.c(0)),
        M.set(R.focus(), M.g(R.y()))])),
    M.dec(R.c())])

# Rwt e P f: e, in the frame Rwt □ P f
def M.ev.rwt() -> Cir.Stmt:
  M.do([
    M.set(R.x(), M.f(2n, M.g(R.c()))),
    M.set(R.y(), M.f(3n, M.g(R.c()))),
    M.set(R.z(), M.f(4n, M.g(R.c()))),
    M.inc(R.x()),
    M.inc(R.y()),
    M.inc(R.z()),
    M.push(M.c(K.rwt()), M.g(R.y()), M.g(R.z())),
    M.dec(R.c()),
    M.set(R.focus(), M.g(R.x()))])

# Min a b: a, in the frame Min □ b
def M.ev.min() -> Cir.Stmt:
  M.do([
    M.set(R.x(), M.f(2n, M.g(R.c()))),
    M.set(R.y(), M.f(3n, M.g(R.c()))),
    M.inc(R.x()),
    M.inc(R.y()),
    M.push(M.c(K.min_b()), M.g(R.y()), M.c(0)),
    M.dec(R.c()),
    M.set(R.focus(), M.g(R.x()))])

# mode 0: a value by its form, or flagged one, is returned; a variable, free
# in the whole term, has no step
def M.ev() -> Cir.Stmt:
  M.do([
    M.set(R.c(), M.g(R.focus())),
    M.set(R.tag(), M.tag(M.g(R.c()))),
    M.if(M.or(M.flag(M.g(R.c()), F.value()), M.ne(M.entry(4n, M.g(R.c())), M.c(0))),
      M.set(R.mode(), M.c(1)),
    M.if(M.eq(M.g(R.tag()), M.c(T.app())), M.ev.app(),
    M.if(M.eq(M.g(R.tag()), M.c(T.ref())), M.ev.ref(),
    M.if(M.eq(M.g(R.tag()), M.c(T.ann())), M.ev.ann(),
    M.if(M.eq(M.g(R.tag()), M.c(T.let())), M.ev.let(),
    M.if(M.eq(M.g(R.tag()), M.c(T.tup())), M.ev.tup(),
    M.if(M.eq(M.g(R.tag()), M.c(T.rwt())), M.ev.rwt(),
    M.if(M.eq(M.g(R.tag()), M.c(T.min())), M.ev.min(),
      M.halt(2)))))))))])

# the frame in register h, whose term is in field 2, gets the focus there and
# the header hd; its term becomes the focus, to evaluate
def M.swap(hd: Cir.Expr) -> Cir.Stmt:
  M.do([
    M.set(R.n(), M.f(2n, M.g(R.h()))),
    M.st(0n, M.g(R.h()), hd),
    M.st(2n, M.g(R.h()), M.g(R.focus())),
    M.set(R.focus(), M.g(R.n())),
    M.set(R.mode(), M.c(0))])

# Let q □ f, with the value v: f with v put in, a step, when q may hold v
def M.ret.let() -> Cir.Stmt:
  M.do([
    M.set(R.wok(), M.c(1)),
    M.when(M.eq(M.g(R.q()), M.c(2)), M.do([
      M.data(R.focus()),
      M.set(R.wok(), M.g(R.dok()))])),
    M.need(M.g(R.wok()), M.do([
      M.set(R.z(), M.f(2n, M.g(R.h()))),
      M.pop(),
      M.one(R.focus()),
      M.copy(R.n(), R.z()),
      M.release(R.wa()),
      M.dec(R.focus()),
      M.dec(R.z()),
      M.set(R.focus(), M.g(R.n())),
      M.set(R.mode(), M.c(0))]))])

# Tup q a □, with the value v: the value Tup q a v
def M.ret.tup() -> Cir.Stmt:
  M.do([
    M.set(R.x(), M.f(2n, M.g(R.h()))),
    M.pop(),
    M.make(R.n(), M.or(M.header(T.tup(), M.g(R.q()), M.c(F.value())),
      M.shl(M.max(M.fv(M.g(R.x())), M.fv(M.g(R.focus()))), M.c(13))), M.g(R.x()), M.g(R.focus()), M.c(0)),
    M.set(R.focus(), M.g(R.n()))])

# Rwt □ P f, with the value v: f, a step, when v is Rfl
def M.ret.rwt() -> Cir.Stmt:
  M.need(M.eq(M.tag(M.g(R.focus())), M.c(T.rfl())), M.do([
    M.set(R.y(), M.f(2n, M.g(R.h()))),
    M.set(R.n(), M.f(3n, M.g(R.h()))),
    M.pop(),
    M.dec(R.y()),
    M.dec(R.focus()),
    M.set(R.focus(), M.g(R.n())),
    M.set(R.mode(), M.c(0))]))

# the name i is Q0, Q1 or Q2
def M.quan(+i: Cir.Expr) -> Cir.Expr:
  M.and(M.ge(i, M.c(N.q0())), M.le(i, M.c(N.q2())))

# the least of the quantities that the names i and j name: 2 below none, and
# 0 below all
def M.qmin(+i: Cir.Expr, +j: Cir.Expr) -> Cir.Expr:
  M.pick(M.eq(i, M.c(N.q2())), j,
    M.pick(M.eq(j, M.c(N.q2())), i,
      M.pick(M.or(M.eq(i, M.c(N.q0())), M.eq(j, M.c(N.q0()))), M.c(N.q0()), M.c(N.q1()))))

# Min a □, with the value v: the meet of a and v, a step, when both are labels
# of quantities
def M.ret.min() -> Cir.Stmt:
  M.do([
    M.set(R.x(), M.f(2n, M.g(R.h()))),
    M.pop(),
    M.need(M.and(M.eq(M.tag(M.g(R.x())), M.c(T.lab())), M.eq(M.tag(M.g(R.focus())), M.c(T.lab()))), M.do([
      M.set(R.p(), M.f(2n, M.g(R.x()))),
      M.set(R.k(), M.f(2n, M.g(R.focus()))),
      M.need(M.and(M.quan(M.g(R.p())), M.quan(M.g(R.k()))), M.do([
        M.set(R.n(), M.add(M.qmin(M.g(R.p()), M.g(R.k())), M.c(1))),
        M.dec(R.x()),
        M.dec(R.focus()),
        M.set(R.focus(), M.g(R.n())),
        M.set(R.mode(), M.c(0))]))]))])

# the cell in register r is a pair at quantity 1
def M.pair(+r: Nat) -> Cir.Expr:
  M.eq(M.and(M.f(0n, M.g(r)), M.c(255)), M.c(U32.or(T.tup(), 64)))

# the cell c is the label of the name i
def M.is_lab(+c: Cir.Expr, i: U32) -> Cir.Expr:
  M.and(M.eq(M.tag(c), M.c(T.lab())), M.eq(M.f(2n, c), M.c(i)))

# the pair in register r ends a constructor's fields: its second is ()
def M.last(+r: Nat) -> Cir.Expr:
  M.is_lab(M.f(3n, M.g(r)), N.unit())

# a bit of a word, in register t1: True or False, with no fields; ov gains
# 1 << oi when it is True
def M.out.bit() -> Cir.Stmt:
  M.need(M.pair(R.t1()), M.need(M.last(R.t1()),
    M.need(M.eq(M.tag(M.f(2n, M.g(R.t1()))), M.c(T.lab())), M.do([
      M.set(R.t2(), M.f(2n, M.f(2n, M.g(R.t1())))),
      M.need(M.or(M.eq(M.g(R.t2()), M.c(N.true())), M.eq(M.g(R.t2()), M.c(N.false()))),
        M.when(M.eq(M.g(R.t2()), M.c(N.true())),
          M.set(R.ov(), M.or(M.g(R.ov()), M.shl(M.c(1), M.g(R.oi()))))))]))))

# the word of 32 bits in register ow, the lowest first, into ov
def M.out.word() -> Cir.Stmt:
  M.do([
    M.set(R.ov(), M.c(0)),
    M.set(R.oi(), M.c(0)),
    M.while(M.lt(M.g(R.oi()), M.c(32)),
      M.need(M.pair(R.ow()), M.need(M.is_lab(M.f(2n, M.g(R.ow())), N.wcon()), M.do([
        M.set(R.ow(), M.f(3n, M.g(R.ow()))),
        M.need(M.pair(R.ow()), M.do([
          M.set(R.t1(), M.f(2n, M.g(R.ow()))),
          M.out.bit(),
          M.set(R.ow(), M.f(3n, M.g(R.ow()))),
          M.need(M.pair(R.ow()), M.need(M.last(R.ow()), M.do([
            M.set(R.ow(), M.f(2n, M.g(R.ow()))),
            M.set(R.oi(), M.add(M.g(R.oi()), M.c(1)))])))]))])))),
    M.need(M.pair(R.ow()), M.need(M.is_lab(M.f(2n, M.g(R.ow())), N.wnil()), M.need(M.last(R.ow()),
      Cir.Stmt.nop{})))])

# the cell of a list in register oc, Con: its byte goes out, and oc gets the
# rest of the list
def M.out.con() -> Cir.Stmt:
  M.do([
    M.set(R.oc(), M.f(3n, M.g(R.oc()))),
    M.need(M.pair(R.oc()), M.do([
      M.set(R.ow(), M.f(2n, M.g(R.oc()))),
      M.set(R.oc(), M.f(3n, M.g(R.oc()))),
      M.need(M.pair(R.oc()), M.need(M.last(R.oc()), M.do([
        M.set(R.oc(), M.f(2n, M.g(R.oc()))),
        M.need(M.pair(R.ow()), M.need(M.is_lab(M.f(2n, M.g(R.ow())), N.u32()), M.do([
          M.set(R.ow(), M.f(3n, M.g(R.ow()))),
          M.need(M.pair(R.ow()), M.need(M.last(R.ow()), M.do([
            M.set(R.ow(), M.f(2n, M.g(R.ow()))),
            M.out.word(),
            M.need(M.lt(M.g(R.ov()), M.c(256)), Cir.Stmt.emit{M.g(R.ov())})])))])))])))]))])

# mode 1 with no frame: the run ends with the bytes of the value, when it is a
# list of bytes (Program.unbytes); else with no result
def M.out() -> Cir.Stmt:
  M.do([
    M.set(R.oc(), M.g(R.focus())),
    M.while(M.c(1),
      M.need(M.pair(R.oc()), M.need(M.eq(M.tag(M.f(2n, M.g(R.oc()))), M.c(T.lab())), M.do([
        M.set(R.ow(), M.f(2n, M.f(2n, M.g(R.oc())))),
        M.if(M.eq(M.g(R.ow()), M.c(N.nil())), M.need(M.last(R.oc()), M.halt(0)),
          M.need(M.eq(M.g(R.ow()), M.c(N.con())), M.out.con()))]))))])

# mode 1: the value v in the focus goes into the top frame
def M.ret() -> Cir.Stmt:
  M.if(M.eq(M.g(R.sp()), M.c(0)), M.out(), M.do([
    M.set(R.h(), M.g(R.sp())),
    M.set(R.tag(), M.tag(M.g(R.h()))),
    M.set(R.q(), M.q(M.g(R.h()))),
    M.if(M.or(M.eq(M.g(R.tag()), M.c(K.app_arg())), M.eq(M.g(R.tag()), M.c(K.app_val()))),
      M.if(M.and(M.ne(M.g(R.q()), M.c(0)), M.not(M.flag(M.g(R.h()), F.known()))),
        M.swap(M.header(K.app_fun(), M.g(R.q()), M.c(0))),
        M.do([
          M.set(R.x(), M.g(R.focus())),
          M.set(R.y(), M.f(2n, M.g(R.h()))),
          M.pop(),
          M.redex()])),
    M.if(M.eq(M.g(R.tag()), M.c(K.app_fun())), M.do([
      M.set(R.x(), M.f(2n, M.g(R.h()))),
      M.set(R.y(), M.g(R.focus())),
      M.pop(),
      M.redex()]),
    M.if(M.eq(M.g(R.tag()), M.c(K.let_in())), M.ret.let(),
    M.if(M.eq(M.g(R.tag()), M.c(K.tup_b())), M.swap(M.header(K.tup_a(), M.g(R.q()), M.c(0))),
    M.if(M.eq(M.g(R.tag()), M.c(K.tup_a())), M.ret.tup(),
    M.if(M.eq(M.g(R.tag()), M.c(K.rwt())), M.ret.rwt(),
    M.if(M.eq(M.g(R.tag()), M.c(K.min_b())), M.swap(M.c(K.min_a())),
      M.ret.min())))))))]))

# the header of a pair at quantity 1, a value and Data, that no count frees
def M.h.static() -> U32:
  1866

# the same, freed by its count
def M.h.data() -> U32:
  842

# the start of the run (Program.start): main, applied at quantity 1 to the
# list of the input's bytes, built from its last. A byte's U32 is made once,
# into the cache, and never freed: 8 bits over the image's 24 False bits
def M.input() -> Cir.Stmt:
  M.do([
    M.set(R.il(), M.c(I.nil())),
    M.set(R.ii(), Cir.Expr.size{}),
    M.while(M.ne(M.g(R.ii()), M.c(0)), M.do([
      M.set(R.ii(), M.sub(M.g(R.ii()), M.c(1))),
      M.set(R.ib(), Cir.Expr.byte{M.g(R.ii())}),
      M.set(R.iu(), M.f(2n, M.add(M.c(I.cache()), M.g(R.ib())))),
      M.when(M.eq(M.g(R.iu()), M.c(0)), M.do([
        M.set(R.iw(), M.c(I.z24())),
        M.set(R.ij(), M.c(8)),
        M.while(M.ne(M.g(R.ij()), M.c(0)), M.do([
          M.set(R.ij(), M.sub(M.g(R.ij()), M.c(1))),
          M.make(R.t1(), M.c(M.h.static()), M.g(R.iw()), M.c(I.lab(N.unit())), M.c(0)),
          M.make(R.t2(), M.c(M.h.static()),
            M.pick(M.and(M.shr(M.g(R.ib()), M.g(R.ij())), M.c(1)), M.c(I.true()), M.c(I.false())),
            M.g(R.t1()), M.c(0)),
          M.make(R.iw(), M.c(M.h.static()), M.c(I.lab(N.wcon())), M.g(R.t2()), M.c(0))])),
        M.make(R.t1(), M.c(M.h.static()), M.g(R.iw()), M.c(I.lab(N.unit())), M.c(0)),
        M.make(R.iu(), M.c(M.h.static()), M.c(I.lab(N.u32())), M.g(R.t1()), M.c(0)),
        M.st(2n, M.add(M.c(I.cache()), M.g(R.ib())), M.g(R.iu()))])),
      M.make(R.t1(), M.c(M.h.data()), M.g(R.il()), M.c(I.lab(N.unit())), M.c(0)),
      M.make(R.t2(), M.c(M.h.data()), M.g(R.iu()), M.g(R.t1()), M.c(0)),
      M.make(R.il(), M.c(M.h.data()), M.c(I.lab(N.con())), M.g(R.t2()), M.c(0))])),
    M.make(R.focus(), M.c(U32.or(T.app(), 64)), M.c(I.ref_main()), M.g(R.il()), M.c(0))])

# the machine (C3): the start, then a move per round, until a halt
def Mach.code() -> Cir.Stmt:
  M.do([
    M.input(),
    M.set(R.mode(), M.c(0)),
    M.while(M.c(1), M.if(M.eq(M.g(R.mode()), M.c(0)), M.ev(), M.ret()))])

# Image
# -----
#
# The cells that the module's memory holds from cell 1 (Mach.code's I.*):
# the labels of the names 0 to 10, constant terms, the cache of the input's
# bytes, the table by tag, then the bodies of the book's defs, each a tree of
# cells in pre-order. Each cell of the image is STATIC: no count frees it. A
# Ref holds the body of the first def of its name, as Book.get finds it, or
# 0; a Lab and a Mat hold the number of their name: the place of its first
# copy in a list of names whose first are the machine's (N.*).

# a def's name and the first cell of its body
type Img.Def is Data:
  Img.Def{k: List<&2, U32>, at: U32}

# the five fields of a cell, then acc
def Img.cell(f0: U32, f2: U32, f3: U32, f4: U32, acc: List<&2, Cir.Cell>) -> List<&2, Cir.Cell>:
  Con{Cir.Cell{f0, 0, f2, f3, f4}, acc}

def Img.quan(q: Quan) -> U32:
  match q:
    case Quan.Q0{}:
      0
    case Quan.Q1{}:
      1
    case Quan.Q2{}:
      2

# the nodes of a term, as a U32
def Img.size(t: Term) -> U32:
  match t:
    case Term.Var{_}:
      1
    case Term.Ref{_}:
      1
    case Term.Ann{x, T}:
      U32.inc(U32.add(Img.size(x), Img.size(T)))
    case Term.Let{_, v, f}:
      U32.inc(U32.add(Img.size(v), Img.size(f)))
    case Term.Typ{q}:
      U32.inc(Img.size(q))
    case Term.Min{a, b}:
      U32.inc(U32.add(Img.size(a), Img.size(b)))
    case Term.All{_, A, B}:
      U32.inc(U32.add(Img.size(A), Img.size(B)))
    case Term.Lam{_, f}:
      U32.inc(Img.size(f))
    case Term.App{_, f, x}:
      U32.inc(U32.add(Img.size(f), Img.size(x)))
    case Term.Sig{_, A, B}:
      U32.inc(U32.add(Img.size(A), Img.size(B)))
    case Term.Tup{_, a, b}:
      U32.inc(U32.add(Img.size(a), Img.size(b)))
    case Term.Prj{h}:
      U32.inc(Img.size(h))
    case Term.Enu{_}:
      1
    case Term.Lab{_}:
      1
    case Term.Mat{_, h, m}:
      U32.inc(U32.add(Img.size(h), Img.size(m)))
    case Term.Efq{}:
      1
    case Term.Eql{a, b, T}:
      U32.inc(U32.add(Img.size(a), U32.add(Img.size(b), Img.size(T))))
    case Term.Rfl{}:
      1
    case Term.Rwt{e, P, f}:
      U32.inc(U32.add(Img.size(e), U32.add(Img.size(P), Img.size(f))))

# fv of a part under k binders, as the cell that holds it counts it: fv_max
# stays fv_max
def Img.down(+fv: U32, +k: U32) -> U32:
  Bool.pick(U32, U32.is_eq(fv, 524287), 524287, Bool.pick(U32, U32.is_gt(fv, k), U32.sub(fv, k), 0))

# fv of a term: 1 + its highest free variable, 0 when it has none, at most
# fv_max (M.var, M.finish)
def Img.fv(t: Term) -> U32:
  match t:
    case Term.Var{i}:
      +u = U32.from_nat(i)
      Bool.pick(U32, U32.is_lt(u, 524286), U32.inc(u), 524287)
    case Term.Ref{_}:
      0
    case Term.Ann{x, T}:
      U32.max(Img.fv(x), Img.fv(T))
    case Term.Let{_, v, f}:
      U32.max(Img.fv(v), Img.down(Img.fv(f), 1))
    case Term.Typ{q}:
      Img.fv(q)
    case Term.Min{a, b}:
      U32.max(Img.fv(a), Img.fv(b))
    case Term.All{_, A, B}:
      U32.max(Img.fv(A), Img.down(Img.fv(B), 1))
    case Term.Lam{_, f}:
      Img.down(Img.fv(f), 1)
    case Term.App{_, f, x}:
      U32.max(Img.fv(f), Img.fv(x))
    case Term.Sig{_, A, B}:
      U32.max(Img.fv(A), Img.down(Img.fv(B), 1))
    case Term.Tup{_, a, b}:
      U32.max(Img.fv(a), Img.fv(b))
    case Term.Prj{h}:
      Img.fv(h)
    case Term.Enu{_}:
      0
    case Term.Lab{_}:
      0
    case Term.Mat{_, h, m}:
      U32.max(Img.fv(h), Img.fv(m))
    case Term.Efq{}:
      0
    case Term.Eql{a, b, T}:
      U32.max(Img.fv(a), U32.max(Img.fv(b), Img.fv(T)))
    case Term.Rfl{}:
      0
    case Term.Rwt{e, P, f}:
      U32.max(Img.fv(e), U32.max(Img.down(Img.fv(P), 2), Img.fv(f)))

# a value by its form alone, with no call in it: the image flags such a pair
# VALUE
def Img.is_value(t: Term) -> Bool:
  match t:
    case Term.Tup{q, a, b}:
      (Bool.not(Quan.live(q)) || Img.is_value(a)) && Img.is_value(b)
    case u:
      Term.is_former(u)

# a cell's field 0: the tag t, the quantity q, the flags fl and fv
def Img.header(+t: U32, +q: U32, +fl: U32, +fv: U32) -> U32:
  U32.or(U32.or(U32.or(t, U32.shln(q, 6n)), fl), U32.shln(fv, 13n))

# STATIC, with VALUE and DATA when they hold
def Img.flags(value: Bool, data: Bool) -> U32:
  U32.or(1024, U32.or(Bool.pick(U32, value, 256, 0), Bool.pick(U32, data, 512, 0)))

def Img.ref.if(b: Bool, +at: U32, more: Unit -> U32) -> U32:
  match b:
    case True{}:
      at
    case False{}:
      more(Unit{})

# the body of the first def of the name k, or 0 when there is none
def Img.ref(es: List<&2, Img.Def>, +k: List<&2, U32>) -> U32:
  match es:
    case Nil{}:
      0
    case Con{Img.Def{+n, +at}, rest}:
      Img.ref.if(Name.is_eq(n, k), at, u => Img.ref(rest, k))

# the number of the name k: the place of its first copy in ks, from i
def Img.id(ks: List<&2, List<&2, U32>>, +k: List<&2, U32>, +i: U32) -> U32:
  match ks:
    case Nil{}:
      i
    case Con{+n, rest}:
      Img.ref.if(Name.is_eq(n, k), i, u => Img.id(rest, k, U32.inc(i)))

# the cells of the term t from the cell at, then acc
def Img.term(t: Term, +ks: List<&2, List<&2, U32>>, +es: List<&2, Img.Def>, +at: U32, acc: List<&2, Cir.Cell>) ->
  List<&2, Cir.Cell>:
  match t:
    case Term.Var{+i}:
      Img.cell(Img.header(T.var(), 0, 1024, Img.fv(Term.Var{i})), U32.from_nat(i), 0, 0, acc)
    case Term.Ref{+k}:
      Img.cell(Img.header(T.ref(), 0, 1024, 0), Img.ref(es, k), 0, 0, acc)
    case Term.Ann{+x, +T}:
      +a = U32.inc(at)
      +b = U32.add(a, Img.size(x))
      Img.cell(Img.header(T.ann(), 0, 1024, Img.fv(Term.Ann{x, T})), a, b, 0,
        Img.term(x, ks, es, a, Img.term(T, ks, es, b, acc)))
    case Term.Let{+q, +v, +f}:
      +a = U32.inc(at)
      +b = U32.add(a, Img.size(v))
      Img.cell(Img.header(T.let(), Img.quan(q), 1024, Img.fv(Term.Let{q, v, f})), a, b, 0,
        Img.term(v, ks, es, a, Img.term(f, ks, es, b, acc)))
    case Term.Typ{+x}:
      +a = U32.inc(at)
      Img.cell(Img.header(4, 0, 1024, Img.fv(x)), a, 0, 0, Img.term(x, ks, es, a, acc))
    case Term.Min{+x, +y}:
      +a = U32.inc(at)
      +b = U32.add(a, Img.size(x))
      Img.cell(Img.header(T.min(), 0, 1024, Img.fv(Term.Min{x, y})), a, b, 0,
        Img.term(x, ks, es, a, Img.term(y, ks, es, b, acc)))
    case Term.All{+q, +A, +B}:
      +a = U32.inc(at)
      +b = U32.add(a, Img.size(A))
      Img.cell(Img.header(6, Img.quan(q), 1024, Img.fv(Term.All{q, A, B})), a, b, 0,
        Img.term(A, ks, es, a, Img.term(B, ks, es, b, acc)))
    case Term.Lam{+q, +f}:
      +a = U32.inc(at)
      Img.cell(Img.header(T.lam(), Img.quan(q), 1024, Img.fv(Term.Lam{q, f})), a, 0, 0,
        Img.term(f, ks, es, a, acc))
    case Term.App{+q, +f, +x}:
      +a = U32.inc(at)
      +b = U32.add(a, Img.size(f))
      Img.cell(Img.header(T.app(), Img.quan(q), 1024, Img.fv(Term.App{q, f, x})), a, b, 0,
        Img.term(f, ks, es, a, Img.term(x, ks, es, b, acc)))
    case Term.Sig{+q, +A, +B}:
      +a = U32.inc(at)
      +b = U32.add(a, Img.size(A))
      Img.cell(Img.header(9, Img.quan(q), 1024, Img.fv(Term.Sig{q, A, B})), a, b, 0,
        Img.term(A, ks, es, a, Img.term(B, ks, es, b, acc)))
    case Term.Tup{+q, +x, +y}:
      +a = U32.inc(at)
      +b = U32.add(a, Img.size(x))
      Img.cell(Img.header(T.tup(), Img.quan(q),
          Img.flags(Img.is_value(Term.Tup{q, x, y}), Term.is_data(Term.Tup{q, x, y})), Img.fv(Term.Tup{q, x, y})),
        a, b, 0, Img.term(x, ks, es, a, Img.term(y, ks, es, b, acc)))
    case Term.Prj{+h}:
      +a = U32.inc(at)
      Img.cell(Img.header(T.prj(), 0, 1024, Img.fv(h)), a, 0, 0, Img.term(h, ks, es, a, acc))
    case Term.Enu{_}:
      Img.cell(Img.header(12, 0, 1024, 0), 0, 0, 0, acc)
    case Term.Lab{+k}:
      Img.cell(Img.header(T.lab(), 0, 1536, 0), Img.id(ks, k, 0), 0, 0, acc)
    case Term.Mat{+k, +h, +m}:
      +a = U32.inc(at)
      +b = U32.add(a, Img.size(h))
      Img.cell(Img.header(T.mat(), 0, 1024, Img.fv(Term.Mat{k, h, m})), Img.id(ks, k, 0), a, b,
        Img.term(h, ks, es, a, Img.term(m, ks, es, b, acc)))
    case Term.Efq{}:
      Img.cell(Img.header(T.efq(), 0, 1024, 0), 0, 0, 0, acc)
    case Term.Eql{+x, +y, +T}:
      +a = U32.inc(at)
      +b = U32.add(a, Img.size(x))
      +c = U32.add(b, Img.size(y))
      Img.cell(Img.header(16, 0, 1024, Img.fv(Term.Eql{x, y, T})), a, b, c,
        Img.term(x, ks, es, a, Img.term(y, ks, es, b, Img.term(T, ks, es, c, acc))))
    case Term.Rfl{}:
      Img.cell(Img.header(T.rfl(), 0, 1536, 0), 0, 0, 0, acc)
    case Term.Rwt{+e, +P, +f}:
      +a = U32.inc(at)
      +b = U32.add(a, Img.size(e))
      +c = U32.add(b, Img.size(P))
      Img.cell(Img.header(T.rwt(), 0, 1024, Img.fv(Term.Rwt{e, P, f})), a, b, c,
        Img.term(e, ks, es, a, Img.term(P, ks, es, b, Img.term(f, ks, es, c, acc))))

# the names of the labels and λ-matches of t, then acc
def Img.names(t: Term, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match t:
    case Term.Var{_}:
      acc
    case Term.Ref{_}:
      acc
    case Term.Ann{x, T}:
      Img.names(x, Img.names(T, acc))
    case Term.Let{_, v, f}:
      Img.names(v, Img.names(f, acc))
    case Term.Typ{q}:
      Img.names(q, acc)
    case Term.Min{a, b}:
      Img.names(a, Img.names(b, acc))
    case Term.All{_, A, B}:
      Img.names(A, Img.names(B, acc))
    case Term.Lam{_, f}:
      Img.names(f, acc)
    case Term.App{_, f, x}:
      Img.names(f, Img.names(x, acc))
    case Term.Sig{_, A, B}:
      Img.names(A, Img.names(B, acc))
    case Term.Tup{_, a, b}:
      Img.names(a, Img.names(b, acc))
    case Term.Prj{h}:
      Img.names(h, acc)
    case Term.Enu{_}:
      acc
    case Term.Lab{k}:
      Con{k, acc}
    case Term.Mat{k, h, m}:
      Con{k, Img.names(h, Img.names(m, acc))}
    case Term.Efq{}:
      acc
    case Term.Eql{a, b, T}:
      Img.names(a, Img.names(b, Img.names(T, acc)))
    case Term.Rfl{}:
      acc
    case Term.Rwt{e, P, f}:
      Img.names(e, Img.names(P, Img.names(f, acc)))

# the names of the bodies of ds
def Img.names.defs(ds: List<&2, Def>) -> List<&2, List<&2, U32>>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Def{_, _, v, _}, rest}:
      Img.names(v, Img.names.defs(rest))

# the names that the machine knows (N.*), in front of the book's
def Img.known(ks: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  Con{Program.name.unit(), Con{Program.name.nil(), Con{Program.name.con(), Con{Program.name.u32(),
    Con{Program.name.wnil(), Con{Program.name.wcon(), Con{Program.name.true(), Con{Program.name.false(),
    Con{Quan.name(Quan.Q0{}), Con{Quan.name(Quan.Q1{}), Con{Quan.name(Quan.Q2{}), Con{Program.name.main(),
    ks}}}}}}}}}}}}

# each def's name and the first cell of its body, from the cell at
def Img.defs(ds: List<&2, Def>, +at: U32) -> List<&2, Img.Def>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Def{k, _, v, _}, rest}:
      Con{Img.Def{k, at}, Img.defs(rest, U32.add(at, Img.size(v)))}

# the cells of the bodies of ds, from the cell at, then acc
def Img.bodies(ds: List<&2, Def>, +ks: List<&2, List<&2, U32>>, +es: List<&2, Img.Def>, +at: U32) ->
  List<&2, Cir.Cell>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Def{_, _, +v, _}, rest}:
      Img.term(v, ks, es, at, Img.bodies(rest, ks, es, U32.add(at, Img.size(v))))

# the cells of the image: n labels, from the name i
def Img.labels(n: Nat, +i: U32, acc: List<&2, Cir.Cell>) -> List<&2, Cir.Cell>:
  match n:
    case 0n:
      acc
    case 1n+m:
      Img.cell(1549, i, 0, 0, Img.labels(m, U32.inc(i), acc))

# a pair at quantity 1, a value and Data
def Img.pair(a: U32, b: U32, acc: List<&2, Cir.Cell>) -> List<&2, Cir.Cell>:
  Img.cell(1866, a, b, 0, acc)

# n levels of a word of False bits, from the cell at, then WNil; left is n
def Img.zeros24(n: Nat, +left: U32, +at: U32, acc: List<&2, Cir.Cell>) -> List<&2, Cir.Cell>:
  match n:
    case 0n:
      acc
    case 1n+m:
      Img.pair(I.lab(N.wcon()), U32.inc(at), Img.pair(I.false(), U32.add(at, 2),
        Img.pair(Bool.pick(U32, U32.is_eq(left, 1), I.wnil(), U32.add(at, 3)), I.lab(N.unit()),
          Img.zeros24(m, U32.sub(left, 1), U32.add(at, 3), acc))))

# n cells of zeros
def Img.blank(n: Nat, acc: List<&2, Cir.Cell>) -> List<&2, Cir.Cell>:
  match n:
    case 0n:
      acc
    case 1n+m:
      Img.cell(0, 0, 0, 0, Img.blank(m, acc))

# the table by tag (I.table): the mask of the pointers, the binders above
# each, and 1 for a former
def Img.table(acc: List<&2, Cir.Cell>) -> List<&2, Cir.Cell>:
  Img.cell(0, 0, 0, 0, Img.cell(0, 0, 0, 0, Img.cell(0, 3, 0, 0, Img.cell(0, 3, 4, 0,
  Img.cell(0, 1, 0, 1, Img.cell(0, 3, 0, 0, Img.cell(0, 3, 4, 1, Img.cell(0, 1, 1, 1,
  Img.cell(0, 3, 0, 0, Img.cell(0, 3, 4, 1, Img.cell(0, 3, 0, 0, Img.cell(0, 1, 0, 1,
  Img.cell(0, 0, 0, 1, Img.cell(0, 0, 0, 1, Img.cell(0, 6, 0, 1, Img.cell(0, 0, 0, 1,
  Img.cell(0, 7, 0, 1, Img.cell(0, 0, 0, 1, Img.cell(0, 7, 8, 0, acc)))))))))))))))))))

# cells 1 to 363 (I.*), with main's body at the cell main, then acc
def Img.prefix(main: U32, acc: List<&2, Cir.Cell>) -> List<&2, Cir.Cell>:
  Img.labels(11n, 0,
    Img.pair(I.lab(N.nil()), I.lab(N.unit()), Img.pair(I.lab(N.true()), I.lab(N.unit()),
    Img.pair(I.lab(N.false()), I.lab(N.unit()), Img.pair(I.lab(N.wnil()), I.lab(N.unit()),
    Img.zeros24(24n, 24, I.z24(),
      Img.cell(1025, main, N.main(), 0,
        Img.blank(256n, Img.table(acc)))))))))

# the cells of the image of the book ds
def Img.cells(+ds: List<&2, Def>) -> List<&2, Cir.Cell>:
  +ks = Img.known(Img.names.defs(ds))
  +es = Img.defs(ds, I.book())
  Img.prefix(Img.ref(es, Program.name.main()), Img.bodies(ds, ks, es, I.book()))

def Img.small.if(full: Bool, more: Unit -> Bool) -> Bool:
  match full:
    case True{}:
      False{}
    case False{}:
      more(Unit{})

# the book's bytes are fewer than 2^26 from the n-th: enough for its numbers to
# fit in a U32, and more than a memory of 2^32 bytes can hold with them
def Img.small(xs: List<&2, U32>, +n: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{_, rest}:
      Img.small.if(U32.is_eq(n, 67108863), u => Img.small(rest, U32.inc(n)))

# Compile
# -------

# a module whose run ends at once with the status s
def Compiler.halt(s: U32) -> List<&2, U32>:
  Wasm.encode(Cir.module(Cir.Stmt.halt{s}, 0n, []))

# the module of the machine with the image's cells
def Compiler.module(cells: List<&2, Cir.Cell>) -> List<&2, U32>:
  Wasm.encode(Cir.module(Mach.code(), Mach.regs(), cells))

# the module of the book that Book.read reads, r, by the cases of the
# compiler; machine makes the machine's module of an image
def Compiler.compile.of(machine: List<&2, Cir.Cell> -> List<&2, U32>, small: Bool, r: Maybe<List<&2, Def>>) ->
  List<&2, U32>:
  match small r:
    case False{} _:
      Compiler.halt(1)
    case True{} None{}:
      Compiler.halt(2)
    case True{} Some{+ds}:
      machine(Img.cells(ds))

# the compiler of step 1: the bytes of the module of the program whose book has
# the bytes p (INVARIANTS #5). A book of 2^26 bytes or more needs more memory
# than a module can have: its module runs out of memory at once. Bytes that
# are no book give a module that gives no result
def Compiler.compile(+p: List<&2, U32>) -> List<&2, U32>:
  Compiler.compile.of(Compiler.module, Img.small(p, 0), Book.read(p))
