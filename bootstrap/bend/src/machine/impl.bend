import Base
import ../source/impl.bend as Source

# Machine
# =======
#
# An environment machine that runs a def of the parsed book, as Source.run
# does, but with no substitution: a variable reads its value from an
# environment, and a term that the run does not compute yet (a dead term, or a
# λ) is a closure: the term with its environment. A list of frames holds the
# place of the machine in the term. It follows the Lean machine
# (bootstrap/lean/src/Machine/Impl.lean), and it is exact on untyped books too:
# where a case tree or a check of data reads a closure, the machine reads the
# form of the term that the closure stands for. spec.bend states that its
# result is the result of Source.Term.run.

# Types
# =====

# a value, an environment or a list of arguments, in one type, so that a def
# can go into each of them
# - nil: the empty environment, or no arguments
# - env x rest: an environment, with x for the variable 0
# - arg q x rest: the arguments x at q, then rest
# - clo t e: the term t under the environment e
# - lab, rfl, tup: a label, a proof {==}, and a pair
# - call k xs: a call of def k on xs whose case tree needs more arguments
type Val is Data:
  Val.nil{}
  Val.env{x: Val, rest: Val}
  Val.arg{q: Source.Quan, x: Val, rest: Val}
  Val.clo{t: Source.Term, e: Val}
  Val.lab{k: List<&2, Nat>}
  Val.rfl{}
  Val.tup{q: Source.Quan, a: Val, b: Val}
  Val.call{k: List<&2, Nat>, xs: Val}

# a frame: the term around the current one
# - arg q x: the function of App q _ x
# - fun q f: the argument of App q f _, where f is a value and q is live
# - let q f e: the bound value of Let q _ f, where q is live
# - fst q b e, snd q a: the first or second field of a pair
# - rwt p f e: the proof of Rwt _ p f
# - min1 b e, min2 a: the first or second side of Min
type Fr is Data:
  Fr.arg{q: Source.Quan, x: Val}
  Fr.fun{q: Source.Quan, f: Val}
  Fr.let{q: Source.Quan, f: Source.Term, e: Val}
  Fr.fst{q: Source.Quan, b: Source.Term, e: Val}
  Fr.snd{q: Source.Quan, a: Val}
  Fr.rwt{p: Source.Term, f: Source.Term, e: Val}
  Fr.min1{b: Source.Term, e: Val}
  Fr.min2{a: Val}

# a state: run t under e, or return v; then the frames, the innermost first
type St is Data:
  St.eval{t: Source.Term, e: Val, fs: List<&2, Fr>}
  St.ret{v: Val, fs: List<&2, Fr>}

# a step's result: the next state, the end with a value, or stuck
type Move is Data:
  Move.go{s: St}
  Move.done{v: Val}
  Move.stuck{}

# the end of a walk: it needs more arguments, it leaves the case tree at t
# under e with the arguments xs, or it fails
type Leaf is Data:
  Leaf.need{}
  Leaf.at{t: Source.Term, e: Val, xs: Val}
  Leaf.fail{}

# the form of the term that a value stands for, where a case tree reads it
type Form is Data:
  Form.tup{r: Source.Quan, a: Val, b: Val}
  Form.lab{k: List<&2, Nat>}
  Form.other{}

# Reading
# =======

# the value of the variable i in e; for a free variable j, the closure of
# Var j with no environment
def Env.get(e: Val, i: Nat) -> Val:
  match e i:
    case Val.env{x, rest} 0n:
      x
    case Val.env{x, rest} 1n+j:
      Env.get(rest, j)
    case _ j:
      Val.clo{Source.Term.Var{j}, Val.nil{}}

# what the variable i of e stands for: a value or a closure of a term that is
# not a variable, through closures of variables; none for a free variable
def Env.find(e: Val, i: Nat) -> Maybe<&2, Val>:
  match e i:
    case Val.env{Val.clo{Source.Term.Var{j}, e2}, rest} 0n:
      Env.find(e2, j)
    case Val.env{x, rest} 0n:
      Some{x}
    case Val.env{x, rest} 1n+j:
      Env.find(rest, j)
    case _ _:
      None{}

def Val.form.of(m: Maybe<&2, Val>) -> Form:
  match m:
    case Some{Val.clo{Source.Term.Tup{r, a, b}, +e}}:
      Form.tup{r, Val.clo{a, e}, Val.clo{b, e}}
    case Some{Val.clo{Source.Term.Lab{k}, e}}:
      Form.lab{k}
    case Some{Val.tup{r, a, b}}:
      Form.tup{r, a, b}
    case Some{Val.lab{k}}:
      Form.lab{k}
    case _:
      Form.other{}

# the form of the term that x stands for
def Val.form(x: Val) -> Form:
  Val.form.of(Env.find(Val.env{x, Val.nil{}}, 0n))

# Source.Term.is_data of the term that a value stands for. c: the term t under
# the environment e; else the value e (t is not read).
def Val.data.go(+e: Val, t: Source.Term, c: Bool) -> Bool:
  match e t c:
    case Val.env{x, rest} Source.Term.Var{0n} True{}:
      Val.data.go(x, Source.Term.Efq{}, False{})
    case Val.env{x, rest} Source.Term.Var{1n+j} True{}:
      Val.data.go(rest, Source.Term.Var{j}, True{})
    case _ Source.Term.Var{i} True{}:
      False{}
    case e Source.Term.Tup{+q, a, b} True{}:
      (Bool.not(Source.Quan.live(q)) || Val.data.go(e, a, True{})) && Val.data.go(e, b, True{})
    case _ Source.Term.Lab{k} True{}:
      True{}
    case _ Source.Term.Rfl{} True{}:
      True{}
    case _ _ True{}:
      False{}
    case Val.clo{t2, e2} _ False{}:
      Val.data.go(e2, t2, True{})
    case Val.tup{+q, a, b} +t False{}:
      (Bool.not(Source.Quan.live(q)) || Val.data.go(a, t, False{})) && Val.data.go(b, t, False{})
    case Val.lab{k} _ False{}:
      True{}
    case Val.rfl{} _ False{}:
      True{}
    case _ _ False{}:
      False{}

def Val.is_data(x: Val) -> Bool:
  Val.data.go(x, Source.Term.Efq{}, False{})

# Source.Term.observe of the value v
def Val.observe(v: Val) -> Maybe<&2, Source.Obs>:
  match v:
    case Val.lab{k}:
      Some{Source.Obs.lab{k}}
    case Val.rfl{}:
      Some{Source.Obs.rfl{}}
    case Val.tup{q, a, b}:
      Source.Obs.tup.of(Val.observe(b), Source.Quan.live(q), Val.observe(a))
    case _:
      None{}

# Walks
# =====

# Source.Term.walk on values. At λp f, with go walking f: the next argument
# enters the environment.
def Walk.lam(+p: Source.Quan, xs: Val, e: Val, go: Val -> Val -> Leaf) -> Leaf:
  match xs:
    case Val.arg{q, +x, rest}:
      Source.Bool.lazy(Leaf,
        Source.Bool.is_eq(Source.Quan.live(p), Source.Quan.live(q)) &&
          (Bool.not(Source.Quan.is_q2(p)) || Val.is_data(x)),
        u => go(Val.env{x, e}, rest),
        u => Leaf.fail{})
    case _:
      Leaf.need{}

def Walk.prj.of(f: Form, +q: Source.Quan, rest: Val, go: Val -> Leaf) -> Leaf:
  match f:
    case Form.tup{r, a, b}:
      Source.Bool.lazy(Leaf, Source.Quan.live(q),
        u => go(Val.arg{Source.Quan.fld(r, q), a, Val.arg{q, b, rest}}),
        u => Leaf.fail{})
    case _:
      Leaf.fail{}

# at λ{(,): h}, with go walking h: a live pair splits into its fields
def Walk.prj(xs: Val, go: Val -> Leaf) -> Leaf:
  match xs:
    case Val.arg{q, x, rest}:
      Walk.prj.of(Val.form(x), q, rest, go)
    case _:
      Leaf.need{}

def Walk.mat.of(f: Form, +q: Source.Quan, +k: List<&2, Nat>, +rest: Val, hit: Val -> Leaf,
  miss: Val -> Leaf) -> Leaf:
  match f:
    case Form.lab{+j}:
      Source.Bool.lazy(Leaf, Source.Quan.live(q),
        u => Source.Bool.lazy(Leaf, Source.Name.is_eq(j, k),
          w => hit(rest),
          w => miss(Val.arg{q, Val.lab{j}, rest})),
        u => Leaf.fail{})
    case _:
      Leaf.fail{}

# at λ{.k: h; m}, with hit walking h and miss walking m: a live label chooses
# between them
def Walk.mat(+k: List<&2, Nat>, xs: Val, hit: Val -> Leaf, miss: Val -> Leaf) -> Leaf:
  match xs:
    case Val.arg{q, x, rest}:
      Walk.mat.of(Val.form(x), q, k, rest, hit, miss)
    case _:
      Leaf.need{}

# at λ{}: it takes no argument
def Walk.efq(xs: Val) -> Leaf:
  match xs:
    case Val.arg{q, x, rest}:
      Leaf.fail{}
    case _:
      Leaf.need{}

# walk t e xs: the case tree t, with the environment e, on the arguments xs
def Walk.go(t: Source.Term, +e: Val, +xs: Val) -> Leaf:
  match t:
    case Source.Term.Lam{p, f}:
      Walk.lam(p, xs, e, e2 => ys => Walk.go(f, e2, ys))
    case Source.Term.Prj{h}:
      Walk.prj(xs, ys => Walk.go(h, e, ys))
    case Source.Term.Mat{k, h, m}:
      Walk.mat(k, xs, ys => Walk.go(h, e, ys), ys => Walk.go(m, e, ys))
    case Source.Term.Efq{}:
      Walk.efq(xs)
    case Source.Term.App{+q, +f, Source.Term.Var{+v}}:
      Source.Bool.lazy(Leaf, Source.Spine.head.takes(Source.Term.unspine(f, [])),
        u => Walk.go(f, e, Val.arg{q, Env.get(e, v), xs}),
        u => Leaf.at{Source.Term.App{q, f, Source.Term.Var{v}}, e, xs})
    case t:
      Leaf.at{t, e, xs}

# Calls
# =====

# the arguments xs, then x at q
def Args.snoc(xs: Val, q: Source.Quan, x: Val) -> Val:
  match xs:
    case Val.arg{p, y, rest}:
      Val.arg{p, y, Args.snoc(rest, q, x)}
    case _:
      Val.arg{q, x, Val.nil{}}

# the frames that apply a function to the arguments xs, then the frames fs
def Args.frames(xs: Val, fs: List<&2, Fr>) -> List<&2, Fr>:
  match xs:
    case Val.arg{q, x, rest}:
      Con{Fr.arg{q, x}, Args.frames(rest, fs)}
    case _:
      fs

def Call.leaf(w: Leaf, k: List<&2, Nat>, +xs: Val, fs: List<&2, Fr>) -> Move:
  match w:
    case Leaf.need{}:
      Move.go{St.ret{Val.call{k, xs}, fs}}
    case Leaf.at{t, e, rest}:
      Move.go{St.eval{t, e, Args.frames(rest, fs)}}
    case Leaf.fail{}:
      Move.stuck{}

def Call.got(d: Maybe<&2, Source.Def>, k: List<&2, Nat>, +xs: Val, fs: List<&2, Fr>) -> Move:
  match d:
    case Some{Source.Def{n, t, v, o}}:
      Call.leaf(Walk.go(v, Val.nil{}, xs), k, xs, fs)
    case None{}:
      Move.stuck{}

# the call of def k on xs: it fires when its case tree leaves, and it is a
# value when the case tree needs more arguments
def Call.try(bk: List<&2, Source.Def>, +k: List<&2, Nat>, xs: Val, fs: List<&2, Fr>) -> Move:
  Call.got(Source.Book.get(bk, k), k, xs, fs)

# Steps
# =====

def Apply.prj(l: Bool, x: Val, +q: Source.Quan, h: Source.Term, e: Val, fs: List<&2, Fr>) -> Move:
  match l x:
    case True{} Val.tup{r, a, b}:
      Move.go{St.eval{h, e, Con{Fr.arg{Source.Quan.fld(r, q), a}, Con{Fr.arg{q, b}, fs}}}}
    case _ _:
      Move.stuck{}

def Apply.mat(l: Bool, x: Val, q: Source.Quan, +k: List<&2, Nat>, h: Source.Term, m: Source.Term,
  +e: Val, +fs: List<&2, Fr>) -> Move:
  match l x:
    case True{} Val.lab{+j}:
      Source.Bool.lazy(Move, Source.Name.is_eq(j, k),
        u => Move.go{St.eval{h, e, fs}},
        u => Move.go{St.eval{m, e, Con{Fr.arg{q, Val.lab{j}}, fs}}})
    case _ _:
      Move.stuck{}

# the value f takes x at q
def Apply.go(f: Val, +q: Source.Quan, +x: Val, bk: List<&2, Source.Def>, fs: List<&2, Fr>) -> Move:
  match f:
    case Val.clo{Source.Term.Lam{+p, b}, e}:
      Source.Bool.lazy(Move,
        Source.Bool.is_eq(Source.Quan.live(p), Source.Quan.live(q)) &&
          (Bool.not(Source.Quan.is_q2(p)) || Val.is_data(x)),
        u => Move.go{St.eval{b, Val.env{x, e}, fs}},
        u => Move.stuck{})
    case Val.clo{Source.Term.Prj{h}, e}:
      Apply.prj(Source.Quan.live(q), x, q, h, e, fs)
    case Val.clo{Source.Term.Mat{k, h, m}, e}:
      Apply.mat(Source.Quan.live(q), x, q, k, h, m, e, fs)
    case Val.call{k, xs}:
      Call.try(bk, k, Args.snoc(xs, q, x), fs)
    case _:
      Move.stuck{}

# run x: a closure runs its term; a value returns
def Val.force(x: Val, fs: List<&2, Fr>) -> Move:
  match x:
    case Val.clo{t, e}:
      Move.go{St.eval{t, e, fs}}
    case v:
      Move.go{St.ret{v, fs}}

def Eval.var(m: Maybe<&2, Val>, fs: List<&2, Fr>) -> Move:
  match m:
    case Some{x}:
      Val.force(x, fs)
    case None{}:
      Move.stuck{}

# the step from St.eval t e fs
def Eval.go(t: Source.Term, +e: Val, +fs: List<&2, Fr>, bk: List<&2, Source.Def>) -> Move:
  match t:
    case Source.Term.Var{i}:
      Eval.var(Env.find(e, i), fs)
    case Source.Term.Ref{k}:
      Call.try(bk, k, Val.nil{}, fs)
    case Source.Term.Ann{x, a}:
      Move.go{St.eval{x, e, fs}}
    case Source.Term.Let{+q, +v, +f}:
      Source.Bool.lazy(Move, Source.Quan.live(q),
        u => Move.go{St.eval{v, e, Con{Fr.let{q, f, e}, fs}}},
        u => Move.go{St.eval{f, Val.env{Val.clo{v, e}, e}, fs}})
    case Source.Term.Tup{+q, +a, +b}:
      Source.Bool.lazy(Move, Source.Quan.live(q),
        u => Move.go{St.eval{a, e, Con{Fr.fst{q, b, e}, fs}}},
        u => Move.go{St.eval{b, e, Con{Fr.snd{q, Val.clo{a, e}}, fs}}})
    case Source.Term.App{q, f, x}:
      Move.go{St.eval{f, e, Con{Fr.arg{q, Val.clo{x, e}}, fs}}}
    case Source.Term.Rwt{x, p, f}:
      Move.go{St.eval{x, e, Con{Fr.rwt{p, f, e}, fs}}}
    case Source.Term.Min{a, b}:
      Move.go{St.eval{a, e, Con{Fr.min1{b, e}, fs}}}
    case Source.Term.Lab{k}:
      Move.go{St.ret{Val.lab{k}, fs}}
    case Source.Term.Rfl{}:
      Move.go{St.ret{Val.rfl{}, fs}}
    case t:
      Move.go{St.ret{Val.clo{t, e}, fs}}

def Ret.meet(a: Val, b: Val, fs: List<&2, Fr>) -> Move:
  match a b:
    case Val.lab{+i} Val.lab{+j}:
      Source.Bool.lazy(Move, Source.Name.is_quan(i) && Source.Name.is_quan(j),
        u => Move.go{St.eval{Source.Term.qmin(i, j), Val.nil{}, fs}},
        u => Move.stuck{})
    case _ _:
      Move.stuck{}

def Ret.rwt(v: Val, f: Source.Term, e: Val, fs: List<&2, Fr>) -> Move:
  match v:
    case Val.rfl{}:
      Move.go{St.eval{f, e, fs}}
    case _:
      Move.stuck{}

# the step from St.ret v (fr :: fs)
def Ret.frame(fr: Fr, +v: Val, +fs: List<&2, Fr>, bk: List<&2, Source.Def>) -> Move:
  match fr:
    case Fr.arg{+q, +x}:
      Source.Bool.lazy(Move, Source.Quan.live(q),
        u => Val.force(x, Con{Fr.fun{q, v}, fs}),
        u => Apply.go(v, q, x, bk, fs))
    case Fr.fun{q, f}:
      Apply.go(f, q, v, bk, fs)
    case Fr.let{q, f, e}:
      Source.Bool.lazy(Move, Bool.not(Source.Quan.is_q2(q)) || Val.is_data(v),
        u => Move.go{St.eval{f, Val.env{v, e}, fs}},
        u => Move.stuck{})
    case Fr.fst{q, b, e}:
      Move.go{St.eval{b, e, Con{Fr.snd{q, v}, fs}}}
    case Fr.snd{q, a}:
      Move.go{St.ret{Val.tup{q, a, v}, fs}}
    case Fr.rwt{p, f, e}:
      Ret.rwt(v, f, e, fs)
    case Fr.min1{b, e}:
      Move.go{St.eval{b, e, Con{Fr.min2{v}, fs}}}
    case Fr.min2{a}:
      Ret.meet(a, v, fs)

def Ret.go(v: Val, fs: List<&2, Fr>, bk: List<&2, Source.Def>) -> Move:
  match fs:
    case Nil{}:
      Move.done{v}
    case Con{fr, rest}:
      Ret.frame(fr, v, rest, bk)

# one step of the machine
def Machine.step(s: St, bk: List<&2, Source.Def>) -> Move:
  match s:
    case St.eval{t, e, fs}:
      Eval.go(t, e, fs, bk)
    case St.ret{v, fs}:
      Ret.go(v, fs, bk)

# Runs
# ====

def Run.next(m: Move, go: St -> Maybe<&2, Source.Obs>) -> Maybe<&2, Source.Obs>:
  match m:
    case Move.go{s}:
      go(s)
    case Move.done{v}:
      Val.observe(v)
    case Move.stuck{}:
      None{}

# what the run from s shows after at most n steps, or none: at its end, the
# value's data; none when it is stuck or when n is not enough
def Machine.run(n: Nat, s: St, +bk: List<&2, Source.Def>) -> Maybe<&2, Source.Obs>:
  match n:
    case 0n:
      None{}
    case 1n+m:
      Run.next(Machine.step(s, bk), s2 => Machine.run(m, s2, bk))

# the run of def k of bk, with at most n steps
def Machine.start(n: Nat, bk: List<&2, Source.Def>, k: List<&2, Nat>) -> Maybe<&2, Source.Obs>:
  Machine.run(n, St.eval{Source.Term.Ref{k}, Val.nil{}, []}, bk)
