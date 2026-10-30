import Base

# Source
# ======
#
# The meaning of a source: a .bendtt text, as bend -o gives it, and what Eval
# gives for it. It mirrors two texts, and a person reviews it against them; no
# proof ties them:
# - bend2/bendtt.lean: Term, Def, the book, substitution and the parser;
# - bootstrap/lean/src/Step.lean: step, Eval as a function, which the
#   interpreter proves equal to Eval, and stepUntil.
# A name or a label is its UTF-8 bytes. The comment of a def names the Lean def
# that it mirrors, where one exists.

# Types
# =====

type Quan is Data:
  Q0{}
  Q1{}
  Q2{}

type Term is Data:
  Term.Var{i: Nat}
  Term.Ref{k: List<&2, Nat>}
  Term.Ann{x: Term, t: Term}
  Term.Let{q: Quan, v: Term, f: Term}
  Term.Typ{q: Term}
  Term.Min{a: Term, b: Term}
  Term.All{q: Quan, a: Term, b: Term}
  Term.Lam{q: Quan, f: Term}
  Term.App{q: Quan, f: Term, x: Term}
  Term.Sig{q: Quan, a: Term, b: Term}
  Term.Tup{q: Quan, a: Term, b: Term}
  Term.Prj{h: Term}
  Term.Enu{ks: List<&2, List<&2, Nat>>}
  Term.Lab{k: List<&2, Nat>}
  Term.Mat{k: List<&2, Nat>, h: Term, m: Term}
  Term.Efq{}
  Term.Eql{a: Term, b: Term, t: Term}
  Term.Rfl{}
  Term.Rwt{e: Term, p: Term, f: Term}

# a def: its name, type and body. o: opaque. Eval unfolds an opaque def too.
type Def is Data:
  Def{k: List<&2, Nat>, t: Term, v: Term, o: Bool}

# a spine argument and its quantity
type Arg is Data:
  Arg{q: Quan, x: Term}

# a term as its head and its spine arguments
type Spine is Data:
  Spine{head: Term, args: List<&2, Arg>}

# walk's result: Walk.need is `some none`, Walk.done is `some (some t)`, and
# Walk.fail is `none`
type Walk is Data:
  Walk.need{}
  Walk.done{t: Term}
  Walk.fail{}

# Obs, as Contract/Spec.lean has it: the plain data that a result shows
type Obs is Data:
  Obs.lab{k: List<&2, Nat>}
  Obs.rfl{}
  Obs.tup{a: Obs, b: Obs}
  Obs.tup0{b: Obs}

# Choices
# =======

# a when c holds, else b. Both are computed.
def Bool.if(-A: Type, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

# a when c holds, else b. Only the chosen one runs.
def Bool.lazy(-A: Type, c: Bool, a: Unit -> A, b: Unit -> A) -> A:
  match c:
    case True{}:
      a(Unit{})
    case False{}:
      b(Unit{})

def Bool.is_eq(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case _ _:
      False{}

# m when it is some; else k runs
def Maybe.else(-A: Data, m: Maybe<&2, A>, k: Unit -> Maybe<&2, A>) -> Maybe<&2, A>:
  match m:
    case Some{a}:
      Some{a}
    case None{}:
      k(Unit{})

# k when c holds, else none
def Maybe.when(-A: Data, c: Bool, k: Unit -> Maybe<&2, A>) -> Maybe<&2, A>:
  Bool.lazy(Maybe<&2, A>, c, k, u => None{})

# Names
# =====

def Name.is_eq(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, xs} Con{y, ys}:
      Nat.is_eq(x, y) && Name.is_eq(xs, ys)
    case _ _:
      False{}

# the bytes of an ASCII string
def Name.of(s: String) -> List<&2, Nat>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      Con{U32.to_nat(c), Name.of(t)}

# Quan
# ====

def Quan.live(q: Quan) -> Bool:
  match q:
    case Q0{}:
      False{}
    case _:
      True{}

def Quan.is_q2(q: Quan) -> Bool:
  match q:
    case Q2{}:
      True{}
    case _:
      False{}

# Quan.fld: the quantity of a pair's first field, when the pair is used at q
def Quan.fld(r: Quan, q: Quan) -> Quan:
  match r:
    case Q0{}:
      Q0{}
    case Q1{}:
      q
    case Q2{}:
      Q2{}

# Substitution
# ============

# variable i, moved up by k when it is at or above d
def Term.shift.var(+i: Nat, d: Nat, k: Nat) -> Nat:
  Bool.if(Nat, Nat.is_lt(i, d), i, Nat.add(i, k))

# Term.ren (· + k) under d binders: each variable at or above d moves up by k
def Term.shift(t: Term, +d: Nat, +k: Nat) -> Term:
  match t:
    case Term.Var{i}:
      Term.Var{Term.shift.var(i, d, k)}
    case Term.Ref{n}:
      Term.Ref{n}
    case Term.Ann{x, a}:
      Term.Ann{Term.shift(x, d, k), Term.shift(a, d, k)}
    case Term.Let{q, v, f}:
      Term.Let{q, Term.shift(v, d, k), Term.shift(f, 1n+d, k)}
    case Term.Typ{q}:
      Term.Typ{Term.shift(q, d, k)}
    case Term.Min{a, b}:
      Term.Min{Term.shift(a, d, k), Term.shift(b, d, k)}
    case Term.All{q, a, b}:
      Term.All{q, Term.shift(a, d, k), Term.shift(b, 1n+d, k)}
    case Term.Lam{q, f}:
      Term.Lam{q, Term.shift(f, 1n+d, k)}
    case Term.App{q, f, x}:
      Term.App{q, Term.shift(f, d, k), Term.shift(x, d, k)}
    case Term.Sig{q, a, b}:
      Term.Sig{q, Term.shift(a, d, k), Term.shift(b, 1n+d, k)}
    case Term.Tup{q, a, b}:
      Term.Tup{q, Term.shift(a, d, k), Term.shift(b, d, k)}
    case Term.Prj{h}:
      Term.Prj{Term.shift(h, d, k)}
    case Term.Enu{ks}:
      Term.Enu{ks}
    case Term.Lab{n}:
      Term.Lab{n}
    case Term.Mat{n, h, m}:
      Term.Mat{n, Term.shift(h, d, k), Term.shift(m, d, k)}
    case Term.Efq{}:
      Term.Efq{}
    case Term.Eql{a, b, c}:
      Term.Eql{Term.shift(a, d, k), Term.shift(b, d, k), Term.shift(c, d, k)}
    case Term.Rfl{}:
      Term.Rfl{}
    case Term.Rwt{e, p, f}:
      Term.Rwt{Term.shift(e, d, k), Term.shift(p, 2n+d, k), Term.shift(f, d, k)}

# a substitution: Subst.one v, for Term.inst, or Env.sub e, for walk's
# environment
type Sub is Data:
  Sub.one{v: Term}
  Sub.env{e: List<&2, Term>}

def Env.sub(e: List<&2, Term>, i: Nat) -> Term:
  match e i:
    case Nil{} j:
      Term.Var{j}
    case Con{x, rest} 0n:
      x
    case Con{x, rest} 1n+j:
      Env.sub(rest, j)

# s at variable i
def Sub.at(s: Sub, i: Nat) -> Term:
  match s:
    case Sub.one{v}:
      match i:
        case 0n:
          v
        case 1n+j:
          Term.Var{j}
    case Sub.env{e}:
      Env.sub(e, i)

# Subst.lift s d i; c: i is below d
def Sub.lift(c: Bool, +i: Nat, +d: Nat, s: Sub) -> Term:
  match c:
    case True{}:
      Term.Var{i}
    case False{}:
      Term.shift(Sub.at(s, Nat.sub(i, d)), 0n, d)

# Term.subk s d: Term.sub (Subst.lift s d), s under d binders, which the CLI
# runs as Term.sub. Term.inst f v is Term.sub(f, 0n, Sub.one{v}).
def Term.sub(t: Term, +d: Nat, +s: Sub) -> Term:
  match t:
    case Term.Var{+i}:
      Sub.lift(Nat.is_lt(i, d), i, d, s)
    case Term.Ref{n}:
      Term.Ref{n}
    case Term.Ann{x, a}:
      Term.Ann{Term.sub(x, d, s), Term.sub(a, d, s)}
    case Term.Let{q, x, f}:
      Term.Let{q, Term.sub(x, d, s), Term.sub(f, 1n+d, s)}
    case Term.Typ{q}:
      Term.Typ{Term.sub(q, d, s)}
    case Term.Min{a, b}:
      Term.Min{Term.sub(a, d, s), Term.sub(b, d, s)}
    case Term.All{q, a, b}:
      Term.All{q, Term.sub(a, d, s), Term.sub(b, 1n+d, s)}
    case Term.Lam{q, f}:
      Term.Lam{q, Term.sub(f, 1n+d, s)}
    case Term.App{q, f, x}:
      Term.App{q, Term.sub(f, d, s), Term.sub(x, d, s)}
    case Term.Sig{q, a, b}:
      Term.Sig{q, Term.sub(a, d, s), Term.sub(b, 1n+d, s)}
    case Term.Tup{q, a, b}:
      Term.Tup{q, Term.sub(a, d, s), Term.sub(b, d, s)}
    case Term.Prj{h}:
      Term.Prj{Term.sub(h, d, s)}
    case Term.Enu{ks}:
      Term.Enu{ks}
    case Term.Lab{n}:
      Term.Lab{n}
    case Term.Mat{n, h, m}:
      Term.Mat{n, Term.sub(h, d, s), Term.sub(m, d, s)}
    case Term.Efq{}:
      Term.Efq{}
    case Term.Eql{a, b, c}:
      Term.Eql{Term.sub(a, d, s), Term.sub(b, d, s), Term.sub(c, d, s)}
    case Term.Rfl{}:
      Term.Rfl{}
    case Term.Rwt{e, p, f}:
      Term.Rwt{Term.sub(e, d, s), Term.sub(p, 2n+d, s), Term.sub(f, d, s)}

# Spines
# ======

# Term.spine t xs, with its arguments first
def Term.spine(xs: List<&2, Arg>, t: Term) -> Term:
  match xs:
    case Nil{}:
      t
    case Con{Arg{q, x}, rest}:
      Term.spine(rest, Term.App{q, t, x})

def Term.unspine(t: Term, xs: List<&2, Arg>) -> Spine:
  match t:
    case Term.App{q, f, x}:
      Term.unspine(f, Con{Arg{q, x}, xs})
    case t:
      Spine{t, xs}

# Term.takes: a λ or a λ-match, a node of a case tree
def Term.takes(t: Term) -> Bool:
  match t:
    case Term.Lam{q, f}:
      True{}
    case Term.Prj{h}:
      True{}
    case Term.Mat{k, h, m}:
      True{}
    case Term.Efq{}:
      True{}
    case _:
      False{}

def Spine.head.takes(s: Spine) -> Bool:
  match s:
    case Spine{h, xs}:
      Term.takes(h)

# Book
# ====

# Book.get: the first def named k (a def's first copy wins)
def Book.get(bk: List<&2, Def>, +k: List<&2, Nat>) -> Maybe<&2, Def>:
  match bk:
    case Nil{}:
      None{}
    case Con{Def{+n, t, v, o}, rest}:
      Bool.lazy(Maybe<&2, Def>, Name.is_eq(n, k),
        u => Some{Def{n, t, v, o}},
        u => Book.get(rest, k))

# Walks
# =====

# isData: t is plain data (the kernel's Data)
def Term.is_data(t: Term) -> Bool:
  match t:
    case Term.Lab{k}:
      True{}
    case Term.Rfl{}:
      True{}
    case Term.Tup{q, a, b}:
      (Bool.not(Quan.live(q)) || Term.is_data(a)) && Term.is_data(b)
    case _:
      False{}

# walk t e xs: the kernel's Walk as a function
# walk at λp f, with go walking f: the next argument enters the environment
def Term.walk.lam(+p: Quan, xs: List<&2, Arg>, e: List<&2, Term>,
  go: List<&2, Term> -> List<&2, Arg> -> Walk) -> Walk:
  match xs:
    case Nil{}:
      Walk.need{}
    case Con{Arg{q, +x}, rest}:
      Bool.lazy(Walk,
        Bool.is_eq(Quan.live(p), Quan.live(q)) && (Bool.not(Quan.is_q2(p)) || Term.is_data(x)),
        u => go(Con{x, e}, rest),
        u => Walk.fail{})

# walk at λ{(,): h}, with go walking h: a live pair splits into its fields
def Term.walk.prj(xs: List<&2, Arg>, go: List<&2, Arg> -> Walk) -> Walk:
  match xs:
    case Nil{}:
      Walk.need{}
    case Con{Arg{+q, Term.Tup{r, a, b}}, rest}:
      Bool.lazy(Walk, Quan.live(q),
        u => go(Con{Arg{Quan.fld(r, q), a}, Con{Arg{q, b}, rest}}),
        u => Walk.fail{})
    case Con{_, _}:
      Walk.fail{}

# walk at λ{.k: h; m}, with hit walking h and miss walking m: a live label
# chooses between them
def Term.walk.mat(+k: List<&2, Nat>, xs: List<&2, Arg>, hit: List<&2, Arg> -> Walk,
  miss: List<&2, Arg> -> Walk) -> Walk:
  match xs:
    case Nil{}:
      Walk.need{}
    case Con{Arg{+q, Term.Lab{+j}}, +rest}:
      Bool.lazy(Walk, Quan.live(q),
        u => Bool.lazy(Walk, Name.is_eq(j, k),
          w => hit(rest),
          w => miss(Con{Arg{q, Term.Lab{j}}, rest})),
        u => Walk.fail{})
    case Con{_, _}:
      Walk.fail{}

# walk at λ{}: it takes no argument
def Term.walk.efq(xs: List<&2, Arg>) -> Walk:
  match xs:
    case Nil{}:
      Walk.need{}
    case Con{_, _}:
      Walk.fail{}

# walk t e xs: the kernel's Walk as a function
def Term.walk(t: Term, +e: List<&2, Term>, +xs: List<&2, Arg>) -> Walk:
  match t:
    case Term.Lam{p, f}:
      Term.walk.lam(p, xs, e, e2 => ys => Term.walk(f, e2, ys))
    case Term.Prj{h}:
      Term.walk.prj(xs, ys => Term.walk(h, e, ys))
    case Term.Mat{k, h, m}:
      Term.walk.mat(k, xs, ys => Term.walk(h, e, ys), ys => Term.walk(m, e, ys))
    case Term.Efq{}:
      Term.walk.efq(xs)
    case Term.App{+q, +f, Term.Var{+v}}:
      Bool.lazy(Walk, Spine.head.takes(Term.unspine(f, [])),
        u => Term.walk(f, e, Con{Arg{q, Env.sub(e, v)}, xs}),
        u => Walk.done{Term.spine(xs, Term.sub(Term.App{q, f, Term.Var{v}}, 0n, Sub.env{e}))})
    case t:
      Walk.done{Term.spine(xs, Term.sub(t, 0n, Sub.env{e}))}

def Term.walk_call.got(d: Maybe<&2, Def>, xs: List<&2, Arg>) -> Walk:
  match d:
    case Some{Def{k, t, v, o}}:
      Term.walk(v, [], xs)
    case None{}:
      Walk.fail{}

def Term.walk_call.of(bk: List<&2, Def>, s: Spine) -> Walk:
  match s:
    case Spine{Term.Ref{k}, xs}:
      Term.walk_call.got(Book.get(bk, k), xs)
    case _:
      Walk.fail{}

# walkCall: when t is a call, the walk of its def's case tree on its arguments
def Term.walk_call(bk: List<&2, Def>, t: Term) -> Walk:
  Term.walk_call.of(bk, Term.unspine(t, []))

def Walk.is_need(w: Walk) -> Bool:
  match w:
    case Walk.need{}:
      True{}
    case _:
      False{}

# stops: t is a call, and its def's case tree needs more arguments
def Term.stops(bk: List<&2, Def>, t: Term) -> Bool:
  Walk.is_need(Term.walk_call(bk, t))

# fires: when t is a call and the walk leaves its def's case tree, the term
# that Walk gives
def Walk.done_term(w: Walk) -> Maybe<&2, Term>:
  match w:
    case Walk.done{t}:
      Some{t}
    case _:
      None{}

def Term.fires(bk: List<&2, Def>, t: Term) -> Maybe<&2, Term>:
  Walk.done_term(Term.walk_call(bk, t))

# Values
# ======

# isValue bk t (args is False) and isArgs bk t (args is True) in one def, as
# Bend has no mutual recursion. isArgs: t is a spine on a Ref, and each live
# argument is a value.
def Term.is_value(t: Term, args: Bool, +bk: List<&2, Def>) -> Bool:
  match t:
    case Term.Tup{q, a, b}:
      match args:
        case True{}:
          False{}
        case False{}:
          (Bool.not(Quan.live(q)) || Term.is_value(a, False{}, bk)) && Term.is_value(b, False{}, bk)
    case Term.Ref{k}:
      match args:
        case True{}:
          True{}
        case False{}:
          Term.stops(bk, Term.Ref{k})
    case Term.App{+q, +f, +x}:
      match args:
        case True{}:
          Term.is_value(f, True{}, bk) && (Bool.not(Quan.live(q)) || Term.is_value(x, False{}, bk))
        case False{}:
          Term.is_value(f, True{}, bk) && (Bool.not(Quan.live(q)) || Term.is_value(x, False{}, bk)) &&
            Term.stops(bk, Term.App{q, f, x})
    case Term.Var{i}:
      False{}
    case Term.Ann{x, a}:
      False{}
    case Term.Let{q, v, f}:
      False{}
    case Term.Min{a, b}:
      False{}
    case Term.Rwt{e, p, f}:
      False{}
    case _:
      Bool.not(args)

# Steps
# =====

# the β step of App q (λp b) x: x enters b, when q matches p and allows x
def Term.redex.lam(+bk: List<&2, Def>, +q: Quan, +p: Quan, b: Term, +x: Term) -> Maybe<&2, Term>:
  Maybe.when(Term,
    Bool.is_eq(Quan.live(p), Quan.live(q)) &&
      (Bool.not(Quan.live(q)) || Term.is_value(x, False{}, bk)) &&
      (Bool.not(Quan.is_q2(p)) || Term.is_data(x)),
    u => Some{Term.sub(b, 0n, Sub.one{x})})

# the split step of App q λ{(,): h} x, on a live pair x that is a value
def Term.redex.prj(+bk: List<&2, Def>, +q: Quan, h: Term, x: Term) -> Maybe<&2, Term>:
  match x:
    case Term.Tup{+r, +a, +b}:
      Maybe.when(Term, Quan.live(q) && Term.is_value(Term.Tup{r, a, b}, False{}, bk),
        u => Some{Term.App{q, Term.App{Quan.fld(r, q), h, a}, b}})
    case _:
      None{}

# the hit or miss step of App q λ{.k: h; m} x, on a live label x
def Term.redex.mat(+q: Quan, +k: List<&2, Nat>, h: Term, m: Term, x: Term) -> Maybe<&2, Term>:
  match x:
    case Term.Lab{+j}:
      Maybe.when(Term, Quan.live(q),
        u => Bool.if(Maybe<&2, Term>, Name.is_eq(j, k), Some{h}, Some{Term.App{q, m, Term.Lab{j}}}))
    case _:
      None{}

# redex bk q f x: the β, split, hit or miss step of App q f x, or none
def Term.redex(bk: List<&2, Def>, q: Quan, f: Term, x: Term) -> Maybe<&2, Term>:
  match f:
    case Term.Lam{p, b}:
      Term.redex.lam(bk, q, p, b, x)
    case Term.Prj{h}:
      Term.redex.prj(bk, q, h, x)
    case Term.Mat{k, h, m}:
      Term.redex.mat(q, k, h, m, x)
    case _:
      None{}

# call bk q f x: the Eval call step of App q f x, or none
def Term.call(+bk: List<&2, Def>, +q: Quan, +f: Term, +x: Term) -> Maybe<&2, Term>:
  Bool.lazy(Maybe<&2, Term>,
    Term.is_value(f, True{}, bk) && (Bool.not(Quan.live(q)) || Term.is_value(x, False{}, bk)),
    u => Term.fires(bk, Term.App{q, f, x}),
    u => None{})

def Maybe.map_term(m: Maybe<&2, Term>, f: Term -> Term) -> Maybe<&2, Term>:
  match m:
    case Some{a}:
      Some{f(a)}
    case None{}:
      None{}

def Term.is_rfl(t: Term) -> Bool:
  match t:
    case Term.Rfl{}:
      True{}
    case _:
      False{}

# a label of QS: Q0, Q1 or Q2
def Name.is_quan(+n: List<&2, Nat>) -> Bool:
  Name.is_eq(n, Name.of("Q0")) || Name.is_eq(n, Name.of("Q1")) || Name.is_eq(n, Name.of("Q2"))

# Term.qmin on two labels of QS
def Term.qmin(+i: List<&2, Nat>, +j: List<&2, Nat>) -> Term:
  Bool.if(Term, Name.is_eq(i, Name.of("Q2")), Term.Lab{j},
    Bool.if(Term, Name.is_eq(j, Name.of("Q2")), Term.Lab{i},
      Bool.if(Term, Name.is_eq(i, Name.of("Q0")) || Name.is_eq(j, Name.of("Q0")),
        Term.Lab{Name.of("Q0")},
        Term.Lab{Name.of("Q1")})))

# the meet step of Min a b, on two labels of QS
def Term.meet(a: Term, b: Term) -> Maybe<&2, Term>:
  match a b:
    case Term.Lab{+i} Term.Lab{+j}:
      Bool.lazy(Maybe<&2, Term>, Name.is_quan(i) && Name.is_quan(j),
        u => Some{Term.qmin(i, j)},
        u => None{})
    case _ _:
      None{}

# step bk t: one Eval step from t, or none when no Eval step fits
# step at App q f x when no call fires, given the steps sf of f and sx of x: a
# step in f; else, when f is a value, a step in a live x; else a redex
def Term.step.app(+q: Quan, +f: Term, +x: Term, +bk: List<&2, Def>, sf: Unit -> Maybe<&2, Term>,
  sx: Unit -> Maybe<&2, Term>) -> Maybe<&2, Term>:
  Maybe.else(Term, Maybe.map_term(sf(Unit{}), g => Term.App{q, g, x}), u =>
    Maybe.when(Term, Term.is_value(f, False{}, bk), v =>
      Maybe.else(Term, Maybe.map_term(Maybe.when(Term, Quan.live(q), sx), y => Term.App{q, f, y}),
        z => Term.redex(bk, q, f, x))))

# step at Let q v f, given the step sv of v: a step in a live v; else v enters f,
# when q allows it
def Term.step.let(+q: Quan, +v: Term, +f: Term, +bk: List<&2, Def>,
  sv: Unit -> Maybe<&2, Term>) -> Maybe<&2, Term>:
  Maybe.else(Term, Maybe.map_term(Maybe.when(Term, Quan.live(q), sv), w => Term.Let{q, w, f}), u =>
    Maybe.when(Term,
      (Bool.not(Quan.live(q)) || Term.is_value(v, False{}, bk)) &&
        (Bool.not(Quan.is_q2(q)) || Term.is_data(v)),
      w => Some{Term.sub(f, 0n, Sub.one{v})}))

# step at Tup q a b, given the steps sa of a and sb of b: a step in a live a;
# else, when a is a value or dead, a step in b
def Term.step.tup(+q: Quan, +a: Term, +b: Term, +bk: List<&2, Def>, sa: Unit -> Maybe<&2, Term>,
  sb: Unit -> Maybe<&2, Term>) -> Maybe<&2, Term>:
  Maybe.else(Term, Maybe.map_term(Maybe.when(Term, Quan.live(q), sa), w => Term.Tup{q, w, b}), u =>
    Maybe.when(Term, Bool.not(Quan.live(q)) || Term.is_value(a, False{}, bk),
      w => Maybe.map_term(sb(Unit{}), z => Term.Tup{q, a, z})))

# step at Rwt e P f, given the step se of e: the cast when e is {==}; else a
# step in e
def Term.step.rwt(e: Term, p: Term, +f: Term, se: Unit -> Maybe<&2, Term>) -> Maybe<&2, Term>:
  Bool.lazy(Maybe<&2, Term>, Term.is_rfl(e),
    u => Some{f},
    u => Maybe.map_term(se(Unit{}), w => Term.Rwt{w, p, f}))

# step at Min a b, given the steps sa of a and sb of b: a step in a; else, when
# a is a value, a step in b; else the meet of two labels
def Term.step.min(+a: Term, +b: Term, +bk: List<&2, Def>, sa: Unit -> Maybe<&2, Term>,
  sb: Unit -> Maybe<&2, Term>) -> Maybe<&2, Term>:
  Maybe.else(Term, Maybe.map_term(sa(Unit{}), w => Term.Min{w, b}), u =>
    Maybe.when(Term, Term.is_value(a, False{}, bk),
      w => Maybe.else(Term, Maybe.map_term(sb(Unit{}), z => Term.Min{a, z}), z => Term.meet(a, b))))

# step bk t: one Eval step from t, or none when no Eval step fits
def Term.step(t: Term, +bk: List<&2, Def>) -> Maybe<&2, Term>:
  match t:
    case Term.Ann{x, a}:
      Some{x}
    case Term.Ref{k}:
      Term.fires(bk, Term.Ref{k})
    case Term.App{+q, +f, +x}:
      Maybe.else(Term, Term.call(bk, q, f, x), u =>
        Term.step.app(q, f, x, bk, w => Term.step(f, bk), w => Term.step(x, bk)))
    case Term.Let{q, +v, f}:
      Term.step.let(q, v, f, bk, u => Term.step(v, bk))
    case Term.Tup{q, +a, +b}:
      Term.step.tup(q, a, b, bk, u => Term.step(a, bk), u => Term.step(b, bk))
    case Term.Rwt{+e, p, f}:
      Term.step.rwt(e, p, f, u => Term.step(e, bk))
    case Term.Min{+a, +b}:
      Term.step.min(a, b, bk, u => Term.step(a, bk), u => Term.step(b, bk))
    case _:
      None{}

# Runs
# ====

def Term.run.next(m: Maybe<&2, Term>, t: Term, go: Term -> Maybe<&2, Term>) -> Maybe<&2, Term>:
  match m:
    case Some{u}:
      go(u)
    case None{}:
      Some{t}

def Term.run.of(v: Bool, t: Term, next: Unit -> Maybe<&2, Term>, go: Term -> Maybe<&2, Term>) ->
  Maybe<&2, Term>:
  match v:
    case True{}:
      Some{t}
    case False{}:
      Term.run.next(next(Unit{}), t, go)

# stepUntil bk (isValue bk) n t: the first term of the step chain from t that
# is a value or where no step fits; none when the first n terms do not have
# one. Its fuel comes first.
def Term.run(n: Nat, +t: Term, +bk: List<&2, Def>) -> Maybe<&2, Term>:
  match n:
    case 0n:
      None{}
    case 1n+m:
      Term.run.of(Term.is_value(t, False{}, bk), t, u => Term.step(t, bk), u => Term.run(m, u, bk))

def Obs.tup.of(b: Maybe<&2, Obs>, live: Bool, a: Maybe<&2, Obs>) -> Maybe<&2, Obs>:
  match b:
    case None{}:
      None{}
    case Some{y}:
      match live:
        case True{}:
          match a:
            case Some{x}:
              Some{Obs.tup{x, y}}
            case None{}:
              None{}
        case False{}:
          Some{Obs.tup0{y}}

# observe t: the Obs that t shows, or none when t is not plain data. It keeps
# each live field and drops each dead (q=0) field.
def Term.observe(t: Term) -> Maybe<&2, Obs>:
  match t:
    case Term.Lab{k}:
      Some{Obs.lab{k}}
    case Term.Rfl{}:
      Some{Obs.rfl{}}
    case Term.Tup{q, a, b}:
      Obs.tup.of(Term.observe(b), Quan.live(q), Term.observe(a))
    case _:
      None{}

# Parser
# ======
#
# The parser reads the text's UTF-8 bytes. A Parse(A) takes the rest of the
# text, and gives an A and the text after it, or fails. Each parser mirrors the
# one of the same name in bendtt.lean. A failure has no message: the meaning
# needs only whether the text parses.

type Parsed<-A: Data> is Data:
  Parsed.ok{value: A, rest: List<&2, Nat>}
  Parsed.fail{}

def Parse(-A: Data) -> Type:
  List<&2, Nat> -> Parsed<A>

def Parse.pure(-A: Data, a: A) -> Parse(A):
  s => Parsed.ok{a, s}

def Parse.bind.of(-A: Data, -B: Data, k: A -> Parse(B), r: Parsed<A>) -> Parsed<B>:
  match r:
    case Parsed.ok{a, s}:
      k(a, s)
    case Parsed.fail{}:
      Parsed.fail{}

def Parse.bind(-A: Data, -B: Data, p: Parse(A), k: A -> Parse(B)) -> Parse(B):
  s => Parse.bind.of(A, B, k, p(s))

def Parse.fail(-A: Data, s: List<&2, Nat>) -> Parsed<A>:
  Parsed.fail{}

# a space, as Char's isWhitespace: space, tab, CR or LF
def Byte.is_space(+b: Nat) -> Bool:
  Nat.is_eq(b, 32n) || Nat.is_eq(b, 9n) || Nat.is_eq(b, 13n) || Nat.is_eq(b, 10n)

# Parse.gap: the text from its first byte that is not a space and not in a
# comment (from # to the end of its line). c: s starts in a comment.
def Parse.gap(s: List<&2, Nat>, c: Bool) -> List<&2, Nat>:
  match s:
    case Nil{}:
      Nil{}
    case Con{+b, +rest}:
      match c:
        case True{}:
          Bool.lazy(List<&2, Nat>, Nat.is_eq(b, 10n),
            u => Parse.gap(rest, False{}),
            u => Parse.gap(rest, True{}))
        case False{}:
          Bool.lazy(List<&2, Nat>, Nat.is_eq(b, 35n),
            u => Parse.gap(rest, True{}),
            u => Bool.lazy(List<&2, Nat>, Byte.is_space(b),
              w => Parse.gap(rest, False{}),
              w => Con{b, rest}))

def Parse.peek.of(s: List<&2, Nat>) -> Parsed<Nat>:
  match s:
    case Nil{}:
      Parsed.ok{32n, Nil{}}
    case Con{+b, rest}:
      Parsed.ok{b, Con{b, rest}}

# Parse.peek: the next byte after the gap, or a space at the end
def Parse.peek(s: List<&2, Nat>) -> Parsed<Nat>:
  Parse.peek.of(Parse.gap(s, False{}))

# s without w at its start, when s starts with w (Parse.at)
def Bytes.strip(w: List<&2, Nat>, s: List<&2, Nat>) -> Maybe<&2, List<&2, Nat>>:
  match w s:
    case Nil{} t:
      Some{t}
    case Con{x, xs} Con{y, ys}:
      Bool.lazy(Maybe<&2, List<&2, Nat>>, Nat.is_eq(x, y),
        u => Bytes.strip(xs, ys),
        u => None{})
    case Con{x, xs} Nil{}:
      None{}

def Parse.take.of(m: Maybe<&2, List<&2, Nat>>, s: List<&2, Nat>) -> Parsed<Bool>:
  match m:
    case Some{rest}:
      Parsed.ok{True{}, rest}
    case None{}:
      Parsed.ok{False{}, s}

def Parse.take.at(w: List<&2, Nat>, +s: List<&2, Nat>) -> Parsed<Bool>:
  Parse.take.of(Bytes.strip(w, s), s)

# Parse.take: whether w comes next, after the gap; when it does, the text
# after w
def Parse.take(w: List<&2, Nat>, s: List<&2, Nat>) -> Parsed<Bool>:
  Parse.take.at(w, Parse.gap(s, False{}))

def Parse.sees.of(m: Maybe<&2, List<&2, Nat>>, s: List<&2, Nat>) -> Parsed<Bool>:
  match m:
    case Some{rest}:
      Parsed.ok{True{}, s}
    case None{}:
      Parsed.ok{False{}, s}

def Parse.sees.at(w: List<&2, Nat>, +s: List<&2, Nat>) -> Parsed<Bool>:
  Parse.sees.of(Bytes.strip(w, s), s)

# Parse.sees: whether w comes next, after the gap, without taking it
def Parse.sees(w: List<&2, Nat>, s: List<&2, Nat>) -> Parsed<Bool>:
  Parse.sees.at(w, Parse.gap(s, False{}))

# p when w comes next, after the gap, taking w; else q
def Parse.take_if(-A: Data, w: List<&2, Nat>, p: Parse(A), q: Parse(A)) -> Parse(A):
  Parse.bind(Bool, A, Parse.take(w), c => Bool.if(Parse(A), c, p, q))

# p when w comes next, after the gap, without taking w; else q
def Parse.sees_if(-A: Data, w: List<&2, Nat>, p: Parse(A), q: Parse(A)) -> Parse(A):
  Parse.bind(Bool, A, Parse.sees(w), c => Bool.if(Parse(A), c, p, q))

def Parse.eat(w: List<&2, Nat>) -> Parse(Unit):
  Parse.take_if(Unit, w, Parse.pure(Unit, Unit{}), Parse.fail(Unit))

# Char.is_name: an ASCII letter or digit, _ or .
def Byte.is_name(+b: Nat) -> Bool:
  (Nat.is_le(48n, b) && Nat.is_le(b, 57n)) || (Nat.is_le(65n, b) && Nat.is_le(b, 90n)) ||
    (Nat.is_le(97n, b) && Nat.is_le(b, 122n)) || Nat.is_eq(b, 95n) || Nat.is_eq(b, 46n)

def Parse.span.cons(b: Nat, r: Parsed<List<&2, Nat>>) -> Parsed<List<&2, Nat>>:
  match r:
    case Parsed.ok{n, t}:
      Parsed.ok{Con{b, n}, t}
    case Parsed.fail{}:
      Parsed.fail{}

# Parse.span: the name at the start of s, and the text after it
def Parse.span(s: List<&2, Nat>) -> Parsed<List<&2, Nat>>:
  match s:
    case Nil{}:
      Parsed.ok{Nil{}, Nil{}}
    case Con{+b, +rest}:
      Bool.lazy(Parsed<List<&2, Nat>>, Byte.is_name(b),
        u => Parse.span.cons(b, Parse.span(rest)),
        u => Parsed.ok{Nil{}, Con{b, rest}})

def Parse.name.of(r: Parsed<List<&2, Nat>>) -> Parsed<List<&2, Nat>>:
  match r:
    case Parsed.ok{Nil{}, t}:
      Parsed.fail{}
    case Parsed.ok{Con{b, n}, t}:
      Parsed.ok{Con{b, n}, t}
    case Parsed.fail{}:
      Parsed.fail{}

# Parse.name: a name after the gap; it fails on an empty one
def Parse.name(s: List<&2, Nat>) -> Parsed<List<&2, Nat>>:
  Parse.name.of(Parse.span(Parse.gap(s, False{})))

# Parse.label: a name, or ()
def Parse.label() -> Parse(List<&2, Nat>):
  Parse.take_if(List<&2, Nat>, Name.of("()"), Parse.pure(List<&2, Nat>, Name.of("()")), Parse.name)

# Parse.key: .k or ()
def Parse.key() -> Parse(List<&2, Nat>):
  Parse.take_if(List<&2, Nat>, Name.of("()"),
    Parse.pure(List<&2, Nat>, Name.of("()")),
    Parse.bind(Unit, List<&2, Nat>, Parse.eat(Name.of(".")), u => Parse.name))

def Quan.parse() -> Parse(Quan):
  Parse.take_if(Quan, Name.of("-"), Parse.pure(Quan, Q0{}),
    Parse.take_if(Quan, Name.of("+"), Parse.pure(Quan, Q2{}), Parse.pure(Quan, Q1{})))

# the index of k in vs, counted from i
def Names.find(vs: List<&2, List<&2, Nat>>, +k: List<&2, Nat>, +i: Nat) -> Maybe<&2, Nat>:
  match vs:
    case Nil{}:
      None{}
    case Con{v, rest}:
      Bool.lazy(Maybe<&2, Nat>, Name.is_eq(v, k),
        u => Some{i},
        u => Names.find(rest, k, 1n+i))

def Names.has(vs: List<&2, List<&2, Nat>>, +k: List<&2, Nat>) -> Bool:
  match vs:
    case Nil{}:
      False{}
    case Con{v, rest}:
      Name.is_eq(v, k) || Names.has(rest, k)

def Term.of_name(m: Maybe<&2, Nat>, k: List<&2, Nat>) -> Term:
  match m:
    case Some{i}:
      Term.Var{i}
    case None{}:
      Term.Ref{k}

# Term.parse_name: a variable when vs binds the name, else a def's name
def Term.parse_name(vs: List<&2, List<&2, Nat>>) -> Parse(Term):
  Parse.bind(List<&2, Nat>, Term, Parse.name, +k =>
    Parse.pure(Term, Term.of_name(Names.find(vs, k, 0n), k)))

# Term.parse_enum, after the <: ks are the labels so far, the last first
def Term.parse_enum(n: Nat, +ks: List<&2, List<&2, Nat>>) -> Parse(Term):
  match n:
    case 0n:
      Parse.fail(Term)
    case 1n+m:
      Parse.take_if(Term, Name.of(">"),
        Parse.pure(Term, Term.Enu{List.reverse(&2, List<&2, Nat>, ks)}),
        Parse.bind(List<&2, Nat>, Term, Parse.label(), +k =>
          Bool.if(Parse(Term), Names.has(ks, k),
            Parse.fail(Term),
            Parse.bind(Bool, Term, Parse.take(Name.of(",")), c => Term.parse_enum(m, Con{k, ks})))))

def Term.parse_enum.start(n: Nat) -> Parse(Term):
  do Parse<Term>:
    Parse.eat(Name.of("<"))
    Term.parse_enum(n, [])

def Term.parse_key() -> Parse(Term):
  Parse.bind(List<&2, Nat>, Term, Parse.key(), k => Parse.pure(Term, Term.Lab{k}))

def Term.parse_brace.rfl() -> Parse(Term):
  do Parse<Term>:
    Parse.eat(Name.of("}"))
    return Term.Rfl{}

def Term.parse_brace.eql(a: Term, pb: Parse(Term), pt: Parse(Term)) -> Parse(Term):
  do Parse<Term>:
    b : Term <- pb
    Parse.eat(Name.of(":"))
    t : Term <- pt
    Parse.eat(Name.of("}"))
    return Term.Eql{a, b, t}

def Term.parse_brace.ann(a: Term, pt: Parse(Term)) -> Parse(Term):
  do Parse<Term>:
    Parse.eat(Name.of(":"))
    t : Term <- pt
    Parse.eat(Name.of("}"))
    return Term.Ann{a, t}

def Term.parse_brace.term(pa: Parse(Term), pb: Parse(Term), pt: Parse(Term), pu: Parse(Term)) ->
  Parse(Term):
  Parse.bind(Term, Term, pa, +a =>
    Parse.take_if(Term, Name.of("=="), Term.parse_brace.eql(a, pb, pt), Term.parse_brace.ann(a, pu)))

# Term.parse_brace: {==}, {a == b : T} or {x : T}
def Term.parse_brace(pa: Parse(Term), pb: Parse(Term), pt: Parse(Term), pu: Parse(Term)) ->
  Parse(Term):
  do Parse<Term>:
    Parse.eat(Name.of("{"))
    Parse.take_if(Term, Name.of("=="), Term.parse_brace.rfl(), Term.parse_brace.term(pa, pb, pt, pu))

def Term.parse_typ.paren(pq: Parse(Term)) -> Parse(Term):
  do Parse<Term>:
    q : Term <- pq
    Parse.eat(Name.of(")"))
    return Term.Typ{q}

def Term.parse_typ.one() -> Parse(Term):
  do Parse<Term>:
    Parse.eat(Name.of("1"))
    return Term.Typ{Term.Lab{Name.of("Q1")}}

# Term.parse_typ: *(q), *1 (Type) or *2 (Data)
def Term.parse_typ(pq: Parse(Term)) -> Parse(Term):
  do Parse<Term>:
    Parse.eat(Name.of("*"))
    Parse.take_if(Term, Name.of("("), Term.parse_typ.paren(pq),
      Parse.take_if(Term, Name.of("2"), Parse.pure(Term, Term.Typ{Term.Lab{Name.of("Q2")}}),
        Term.parse_typ.one()))

# Term.parse_let: !q k = v; f
def Term.parse_let(pv: Parse(Term), pf: List<&2, Nat> -> Parse(Term)) -> Parse(Term):
  do Parse<Term>:
    Parse.eat(Name.of("!"))
    q : Quan <- Quan.parse()
    k : List<&2, Nat> <- Parse.name
    Parse.eat(Name.of("="))
    v : Term <- pv
    Parse.eat(Name.of(";"))
    f : Term <- pf(k)
    return Term.Let{q, v, f}

def Term.bind.of(all: Bool, q: Quan, a: Term, b: Term) -> Term:
  match all:
    case True{}:
      Term.All{q, a, b}
    case False{}:
      Term.Sig{q, a, b}

# Term.parse_bind: ∀q k : A -> B (all) or Σq k : A -> B; c is the mark
def Term.parse_bind(all: Bool, c: List<&2, Nat>, pa: Parse(Term), pb: List<&2, Nat> -> Parse(Term)) ->
  Parse(Term):
  do Parse<Term>:
    Parse.eat(c)
    q : Quan <- Quan.parse()
    k : List<&2, Nat> <- Parse.name
    Parse.eat(Name.of(":"))
    a : Term <- pa
    Parse.eat(Name.of("->"))
    b : Term <- pb(k)
    return Term.bind.of(all, q, a, b)

def Term.parse_match.prj(ph: Parse(Term)) -> Parse(Term):
  do Parse<Term>:
    Parse.eat(Name.of(":"))
    h : Term <- ph
    Parse.eat(Name.of("}"))
    return Term.Prj{h}

def Term.parse_match.mat(ph: Parse(Term), pm: Parse(Term)) -> Parse(Term):
  do Parse<Term>:
    k : List<&2, Nat> <- Parse.key()
    Parse.eat(Name.of(":"))
    h : Term <- ph
    Parse.eat(Name.of(";"))
    m : Term <- pm
    Parse.eat(Name.of("}"))
    return Term.Mat{k, h, m}

# Term.parse_match, after λ{: λ{}, λ{(,): h} or λ{.k: h; m}
def Term.parse_match(pp: Parse(Term), ph: Parse(Term), pm: Parse(Term)) -> Parse(Term):
  Parse.take_if(Term, Name.of("}"), Parse.pure(Term, Term.Efq{}),
    Parse.take_if(Term, Name.of("(,)"), Term.parse_match.prj(pp), Term.parse_match.mat(ph, pm)))

def Term.parse_lam.lam(pf: List<&2, Nat> -> Parse(Term)) -> Parse(Term):
  do Parse<Term>:
    q : Quan <- Quan.parse()
    k : List<&2, Nat> <- Parse.name
    Parse.eat(Name.of("=>"))
    f : Term <- pf(k)
    return Term.Lam{q, f}

# Term.parse_lam: λq k => f, or a λ-match
def Term.parse_lam(pp: Parse(Term), ph: Parse(Term), pm: Parse(Term),
  pf: List<&2, Nat> -> Parse(Term)) -> Parse(Term):
  do Parse<Term>:
    Parse.eat([206n, 187n])
    Parse.take_if(Term, Name.of("{"), Term.parse_match(pp, ph, pm), Term.parse_lam.lam(pf))

def Quan.is_q1(q: Quan) -> Bool:
  match q:
    case Q1{}:
      True{}
    case _:
      False{}

def Term.parse_paren.tup(q: Quan, a: Term, pb: Parse(Term)) -> Parse(Term):
  do Parse<Term>:
    b : Term <- pb
    return Term.Tup{q, a, b}

def Term.parse_paren.min(a: Term, pb: Parse(Term)) -> Parse(Term):
  do Parse<Term>:
    b : Term <- pb
    Parse.eat(Name.of(")"))
    return Term.Min{a, b}

def Term.parse_paren.plain(+a: Term, pb: Parse(Term), args: Term -> Parse(Term)) -> Parse(Term):
  Parse.take_if(Term, Name.of("<&>"), Term.parse_paren.min(a, pb), args(a))

def Term.parse_paren.after(+q: Quan, +a: Term, tup: Parse(Term), pb: Parse(Term),
  args: Term -> Parse(Term)) -> Parse(Term):
  Parse.take_if(Term, Name.of(","),
    Term.parse_paren.tup(q, a, tup),
    Bool.if(Parse(Term), Quan.is_q1(q), Term.parse_paren.plain(a, pb, args), Parse.fail(Term)))

def Term.parse_paren.inner(pa: Parse(Term), tup: Parse(Term), pb: Parse(Term),
  args: Term -> Parse(Term)) -> Parse(Term):
  do Parse<Term>:
    q : Quan <- Quan.parse()
    a : Term <- pa
    Term.parse_paren.after(q, a, tup, pb, args)

# Term.parse_paren: (), a tuple, a meet (a <&> b) or an application (f q x ..).
# tup parses the rest of a tuple; args the arguments after a head.
def Term.parse_paren(pa: Parse(Term), tup: Parse(Term), pb: Parse(Term),
  args: Term -> Parse(Term)) -> Parse(Term):
  do Parse<Term>:
    Parse.eat(Name.of("("))
    Parse.take_if(Term, Name.of(")"), Parse.pure(Term, Term.Lab{Name.of("()")}),
      Term.parse_paren.inner(pa, tup, pb, args))

def Term.parse_tup.close(a: Term) -> Parse(Term):
  do Parse<Term>:
    Parse.eat(Name.of(")"))
    return a

def Term.parse_tup.after(+q: Quan, +a: Term, rest: Parse(Term)) -> Parse(Term):
  Parse.take_if(Term, Name.of(","),
    Term.parse_paren.tup(q, a, rest),
    Bool.if(Parse(Term), Quan.is_q1(q), Term.parse_tup.close(a), Parse.fail(Term)))

# Term.parse_tup: the rest of a tuple, after a ","
def Term.parse_tup(pa: Parse(Term), rest: Parse(Term)) -> Parse(Term):
  do Parse<Term>:
    q : Quan <- Quan.parse()
    a : Term <- pa
    Term.parse_tup.after(q, a, rest)

def Term.parse_args.more(f: Term, px: Parse(Term), more: Term -> Parse(Term)) -> Parse(Term):
  do Parse<Term>:
    q : Quan <- Quan.parse()
    x : Term <- px
    more(Term.App{q, f, x})

# Term.parse_args: the arguments after the head f, up to the )
def Term.parse_args(+f: Term, px: Parse(Term), more: Term -> Parse(Term)) -> Parse(Term):
  Parse.take_if(Term, Name.of(")"), Parse.pure(Term, f), Term.parse_args.more(f, px, more))

# Term.parse_rwt: % e : x, h => P; f
def Term.parse_rwt(pe: Parse(Term), pp: List<&2, Nat> -> List<&2, Nat> -> Parse(Term),
  pf: Parse(Term)) -> Parse(Term):
  do Parse<Term>:
    Parse.eat(Name.of("%"))
    e : Term <- pe
    Parse.eat(Name.of(":"))
    x : List<&2, Nat> <- Parse.name
    Parse.eat(Name.of(","))
    h : List<&2, Nat> <- Parse.name
    Parse.eat(Name.of("=>"))
    p : Term <- pp(h, x)
    Parse.eat(Name.of(";"))
    f : Term <- pf
    return Term.Rwt{e, p, f}

# Term.parse on a byte from 128 on: ∀, Σ or λ, else a name
def Term.parse.high(all: Parse(Term), sig: Parse(Term), lam: Parse(Term), name: Parse(Term)) ->
  Parse(Term):
  Parse.sees_if(Term, [226n, 136n, 128n], all,
    Parse.sees_if(Term, [206n, 163n], sig,
      Parse.sees_if(Term, [206n, 187n], lam, name)))

# Term.parse's choice on the next byte c
def Term.parse.pick(+c: Nat, high: Parse(Term), brace: Parse(Term), typ: Parse(Term),
  let: Parse(Term), paren: Parse(Term), enum: Parse(Term), key: Parse(Term), rwt: Parse(Term),
  name: Parse(Term)) -> Parse(Term):
  Bool.if(Parse(Term), Nat.is_eq(c, 123n), brace,
    Bool.if(Parse(Term), Nat.is_eq(c, 42n), typ,
      Bool.if(Parse(Term), Nat.is_eq(c, 33n), let,
        Bool.if(Parse(Term), Nat.is_eq(c, 40n), paren,
          Bool.if(Parse(Term), Nat.is_eq(c, 60n), enum,
            Bool.if(Parse(Term), Nat.is_eq(c, 46n), key,
              Bool.if(Parse(Term), Nat.is_eq(c, 37n), rwt,
                Bool.if(Parse(Term), Nat.is_le(128n, c), high, name))))))))

# where Term.parse is: in a term, the rest of a tuple, or the arguments after
# the head f
type Mode is Data:
  Mode.term{}
  Mode.tup{}
  Mode.args{f: Term}

# Term.parse, Term.parse_tup and Term.parse_args in one def, as Bend has no
# mutual recursion; vs are the bound names, the innermost first. Each nested
# call takes one unit of fuel. Of two nested calls in a row, the second comes
# after at least one more byte, so 2 * (bytes + 1) fuel is always enough.
def Term.parse(+n: Nat, mode: Mode, +vs: List<&2, List<&2, Nat>>) -> Parse(Term):
  match n:
    case 0n:
      Parse.fail(Term)
    case 1n+m:
      match mode:
        case Mode.term{}:
          Parse.bind(Nat, Term, Parse.peek, c =>
            Term.parse.pick(c,
              Term.parse.high(
                Term.parse_bind(True{}, [226n, 136n, 128n], Term.parse(m, Mode.term{}, vs),
                  k => Term.parse(m, Mode.term{}, Con{k, vs})),
                Term.parse_bind(False{}, [206n, 163n], Term.parse(m, Mode.term{}, vs),
                  k => Term.parse(m, Mode.term{}, Con{k, vs})),
                Term.parse_lam(Term.parse(m, Mode.term{}, vs), Term.parse(m, Mode.term{}, vs),
                  Term.parse(m, Mode.term{}, vs), k => Term.parse(m, Mode.term{}, Con{k, vs})),
                Term.parse_name(vs)),
              Term.parse_brace(Term.parse(m, Mode.term{}, vs), Term.parse(m, Mode.term{}, vs),
                Term.parse(m, Mode.term{}, vs), Term.parse(m, Mode.term{}, vs)),
              Term.parse_typ(Term.parse(m, Mode.term{}, vs)),
              Term.parse_let(Term.parse(m, Mode.term{}, vs), k => Term.parse(m, Mode.term{}, Con{k, vs})),
              Term.parse_paren(Term.parse(m, Mode.term{}, vs), Term.parse(m, Mode.tup{}, vs),
                Term.parse(m, Mode.term{}, vs), g => Term.parse(m, Mode.args{g}, vs)),
              Term.parse_enum.start(m),
              Term.parse_key(),
              Term.parse_rwt(Term.parse(m, Mode.term{}, vs),
                h => x => Term.parse(m, Mode.term{}, Con{h, Con{x, vs}}),
                Term.parse(m, Mode.term{}, vs)),
              Term.parse_name(vs)))
        case Mode.tup{}:
          Term.parse_tup(Term.parse(m, Mode.term{}, vs), Term.parse(m, Mode.tup{}, vs))
        case Mode.args{f}:
          Term.parse_args(f, Term.parse(m, Mode.term{}, vs), g => Term.parse(m, Mode.args{g}, vs))

def Book.parse_defs.end.of(s: List<&2, Nat>) -> Parsed<Bool>:
  match s:
    case Nil{}:
      Parsed.ok{True{}, Nil{}}
    case Con{b, t}:
      Parsed.ok{False{}, Con{b, t}}

# whether the text ends after the gap
def Book.parse_defs.end(s: List<&2, Nat>) -> Parsed<Bool>:
  Book.parse_defs.end.of(Parse.gap(s, False{}))

# a def after its first name k; o: it is opaque, so k is the word opaque and
# the def's name comes next
def Book.parse_def.of(+o: Bool, k: List<&2, Nat>, +f: Nat, more: Parse(List<&2, Def>)) ->
  Parse(List<&2, Def>):
  do Parse<List<&2, Def>>:
    n : List<&2, Nat> <- Bool.if(Parse(List<&2, Nat>), o, Parse.name, Parse.pure(List<&2, Nat>, k))
    Parse.eat(Name.of(":"))
    t : Term <- Term.parse(f, Mode.term{}, [])
    Parse.eat(Name.of("="))
    v : Term <- Term.parse(f, Mode.term{}, [])
    ds : List<&2, Def> <- more
    return Con{Def{n, t, v, o}, ds}

# one def, then the defs that more parses; f is the fuel of each term
def Book.parse_def(+f: Nat, more: Parse(List<&2, Def>)) -> Parse(List<&2, Def>):
  Parse.bind(List<&2, Nat>, List<&2, Def>, Parse.name, +k =>
    Parse.bind(Nat, List<&2, Def>, Parse.peek, c =>
      Book.parse_def.of(Name.is_eq(k, Name.of("opaque")) && Bool.not(Nat.is_eq(c, 58n)), k, f, more)))

# Book.parse_defs: the defs up to the end of the text. Each def reads at least
# one byte, so n = bytes + 1 is enough; f is the fuel of each term.
def Book.parse_defs(n: Nat, +f: Nat) -> Parse(List<&2, Def>):
  match n:
    case 0n:
      Parse.fail(List<&2, Def>)
    case 1n+m:
      Parse.bind(Bool, List<&2, Def>, Book.parse_defs.end, e =>
        Bool.if(Parse(List<&2, Def>), e,
          Parse.pure(List<&2, Def>, []),
          Book.parse_def(f, Book.parse_defs(m, f))))

def Book.parse.of(r: Parsed<List<&2, Def>>) -> Maybe<&2, List<&2, Def>>:
  match r:
    case Parsed.ok{ds, rest}:
      Some{ds}
    case Parsed.fail{}:
      None{}

# Book.parse: the defs of a text, in order. Book.of keeps them all, and
# Book.get finds a name's first def. The CLI also refuses a text that is not
# UTF-8, as Lean's readFile does; this meaning does not.
def Book.parse(+src: List<&2, Nat>) -> Maybe<&2, List<&2, Def>>:
  +f = Nat.mul(2n, 1n+List.length(&2, Nat, src))
  Book.parse.of(Book.parse_defs(f, f, src))

# Entry
# =====

# Bytes.nat: the Nat n as a term
def Bytes.nat(n: Nat) -> Term:
  match n:
    case 0n:
      Term.Tup{Q1{}, Term.Lab{Name.of("Zero")}, Term.Lab{Name.of("()")}}
    case 1n+m:
      Term.Tup{Q1{}, Term.Lab{Name.of("Succ")}, Term.Tup{Q1{}, Bytes.nat(m), Term.Lab{Name.of("()")}}}

# Bytes.term: the list bs as a term
def Bytes.term(bs: List<&2, Nat>) -> Term:
  match bs:
    case Nil{}:
      Term.Tup{Q1{}, Term.Lab{Name.of("Nil")}, Term.Lab{Name.of("()")}}
    case Con{b, rest}:
      Term.Tup{Q1{}, Term.Lab{Name.of("Con")},
        Term.Tup{Q1{}, Bytes.nat(b), Term.Tup{Q1{}, Bytes.term(rest), Term.Lab{Name.of("()")}}}}

def Input.apply.of(d: Maybe<&2, Def>, bk: List<&2, Def>, bs: List<&2, Nat>) -> Maybe<&2, List<&2, Def>>:
  match d:
    case Some{Def{k, Term.All{q, a, b}, v, o}}:
      Some{List.append(&2, Def, bk, [
        Def{Name.of("bootstrap.input"), a, Bytes.term(bs), False{}},
        Def{Name.of("bootstrap.run"), Term.sub(b, 0n, Sub.one{Term.Ref{Name.of("bootstrap.input")}}),
          Term.App{q, Term.Ref{Name.of("main")}, Term.Ref{Name.of("bootstrap.input")}}, False{}}])}
    case _:
      None{}

# Input.apply bk bs: bk with the defs bootstrap.input : A = bs and
# bootstrap.run = main(bootstrap.input), where A is the input type of main
def Input.apply(+bk: List<&2, Def>, bs: List<&2, Nat>) -> Maybe<&2, List<&2, Def>>:
  Input.apply.of(Book.get(bk, Name.of("main")), bk, bs)

# the book and the name of the def that runs
type Entry is Data:
  Entry{bk: List<&2, Def>, k: List<&2, Nat>}

def Entry.run(m: Maybe<&2, List<&2, Def>>) -> Maybe<&2, Entry>:
  match m:
    case Some{bk}:
      Some{Entry{bk, Name.of("bootstrap.run")}}
    case None{}:
      None{}

# entry bk input: def main of bk with no input; def bootstrap.run of
# Input.apply bk bs with the input bs
def entry(input: Maybe<&2, List<&2, Nat>>, bk: List<&2, Def>) -> Maybe<&2, Entry>:
  match input:
    case None{}:
      Some{Entry{bk, Name.of("main")}}
    case Some{bs}:
      Entry.run(Input.apply(bk, bs))

# Meaning
# =======

def Maybe.observe(m: Maybe<&2, Term>) -> Maybe<&2, Obs>:
  match m:
    case Some{t}:
      Term.observe(t)
    case None{}:
      None{}

def run.at(n: Nat, e: Maybe<&2, Entry>) -> Maybe<&2, Obs>:
  match e:
    case Some{Entry{bk, k}}:
      Maybe.observe(Term.run(n, Term.Ref{k}, bk))
    case None{}:
      None{}

def run.of(n: Nat, input: Maybe<&2, List<&2, Nat>>, m: Maybe<&2, List<&2, Def>>) ->
  Maybe<&2, Obs>:
  match m:
    case Some{bk}:
      run.at(n, entry(input, bk))
    case None{}:
      None{}

# run n src input: what the source src shows after at most n steps, for
# the input (None: main takes no input), or none. It is the interpreter's
# runSteps: steps until a value or until no step fits, then observe. It does
# not check types: Eval needs none.
def run(n: Nat, src: List<&2, Nat>, input: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, Obs>:
  run.of(n, input, Book.parse(src))

# Results
# =======

def Obs.is_eq(a: Obs, b: Obs) -> Bool:
  match a b:
    case Obs.lab{x} Obs.lab{y}:
      Name.is_eq(x, y)
    case Obs.rfl{} Obs.rfl{}:
      True{}
    case Obs.tup{a1, a2} Obs.tup{b1, b2}:
      Obs.is_eq(a1, b1) && Obs.is_eq(a2, b2)
    case Obs.tup0{a2} Obs.tup0{b2}:
      Obs.is_eq(a2, b2)
    case _ _:
      False{}

# b gives the result that a gives, when a gives one
def Obs.is_kept(a: Maybe<&2, Obs>, b: Maybe<&2, Obs>) -> Bool:
  match a b:
    case None{} _:
      True{}
    case Some{x} Some{y}:
      Obs.is_eq(x, y)
    case Some{x} None{}:
      False{}
