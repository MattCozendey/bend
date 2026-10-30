import Base
import ../source/impl.bend as Source
import ../source/proof.bend as SP
import ../shared/impl.bend as Shared
import ./impl.bend as Machine
import ./spec.bend as Spec

# Machine proofs
# ==============
#
# Val.rb reads a value back to the term that it stands for, and St.rb a state
# to its term: the frames around the current term. Step.ok shows that each
# step keeps a state's term with a smaller measure St.mu, or makes the step
# of Source.Term.step on it, or ends at a value, or is stuck where the term is
# stuck. The laws follow by induction on the fuel: St.mu is at most the weight
# of the term, so the fuel of the machine for a run of the source sums the
# weights of its terms.

# Choices
# =======

def Bool.split(c: Bool, -P: Bool -> Type, t: {c == True{} : Bool} -> P(True{}),
  f: {c == False{} : Bool} -> P(False{})) -> P(c):
  match c:
    case True{}:
      t({==})
    case False{}:
      f({==})

def Maybe.split(-A: Data, m: Maybe<&2, A>, -P: Maybe<&2, A> -> Type,
  s: @x: A -> {m == Some{x} : Maybe<&2, A>} -> P(Some{x}), n: {m == None{} : Maybe<&2, A>} -> P(None{})) -> P(m):
  match m:
    case Some{x}:
      s(x, {==})
    case None{}:
      n({==})

def Bool.true_false(e: {True{} == False{} : Bool}) -> Empty:
  Shared.Bool.no(Equal.sym(Bool, True{}, False{}, e))

def Bool.or_true(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def Bool.and_false(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def Bool.and_true(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# Numbers
# =======

def Nat.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Nat.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def Nat.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Nat.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def Nat.add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, Nat.add_zero(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), Nat.add_succ(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %Nat.add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def Nat.add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Nat.add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

def Nat.sub_zero(i: Nat) -> {Nat.sub(i, 0n) == i : Nat}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Nat.is_lt_zero(i: Nat) -> {Nat.is_lt(i, 0n) == False{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      {==}

# c plus a is at most c plus b, when a is at most b
def Nat.is_le_mono(c: Nat, -a: Nat, -b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(c, a), Nat.add(c, b)) == True{} : Bool}:
  match c:
    case 0n:
      h
    case 1n+p:
      Nat.is_le_mono(p, a, b, h)

# v plus a is at most 1 plus a, when v is at most 1
def Nat.is_le_one(v: Nat, +a: Nat, h: {Nat.is_le(v, 1n) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(v, a), 1n+a) == True{} : Bool}:
  match v:
    case 0n:
      Shared.Nat.is_le_succ(a, a, Shared.Nat.is_le_refl(a))
    case 1n+p:
      match p:
        case 0n:
          Shared.Nat.is_le_refl(a)
        case 1n+r:
          Shared.Bool.absurd({Nat.is_le(Nat.add(2n+r, a), 1n+a) == True{} : Bool}, h)

def Nat.is_le_trans(+a: Nat, +b: Nat, +c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool},
  h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  Shared.Nat.is_le_trans(a, b, c, h1, h2)

# Readback
# ========

# the terms of an environment, from its readback
def Tm.list(t: Source.Term) -> List<&2, Source.Term>:
  match t:
    case Source.Term.Tup{q, a, b}:
      Con{a, Tm.list(b)}
    case _:
      Nil{}

# the arguments of a list of arguments, from its readback
def Tm.args(t: Source.Term) -> List<&2, Source.Arg>:
  match t:
    case Source.Term.App{q, x, rest}:
      Con{Source.Arg{q, x}, Tm.args(rest)}
    case _:
      Nil{}

# the term that a value stands for. An environment reads back to its values as
# Tups, and a list of arguments as Apps, so that one def reads all three.
def Val.rb(v: Machine.Val) -> Source.Term:
  match v:
    case Machine.Val.nil{}:
      Source.Term.Efq{}
    case Machine.Val.env{x, rest}:
      Source.Term.Tup{Source.Q1{}, Val.rb(x), Val.rb(rest)}
    case Machine.Val.arg{q, x, rest}:
      Source.Term.App{q, Val.rb(x), Val.rb(rest)}
    case Machine.Val.clo{t, e}:
      Source.Term.sub(t, 0n, Source.Sub.env{Tm.list(Val.rb(e))})
    case Machine.Val.lab{k}:
      Source.Term.Lab{k}
    case Machine.Val.rfl{}:
      Source.Term.Rfl{}
    case Machine.Val.tup{q, a, b}:
      Source.Term.Tup{q, Val.rb(a), Val.rb(b)}
    case Machine.Val.call{k, xs}:
      Source.Term.spine(Tm.args(Val.rb(xs)), Source.Term.Ref{k})

def Env.rb(e: Machine.Val) -> List<&2, Source.Term>:
  Tm.list(Val.rb(e))

def Args.rb(xs: Machine.Val) -> List<&2, Source.Arg>:
  Tm.args(Val.rb(xs))

# the term t under the environment e
def Clo.rb(t: Source.Term, e: Machine.Val) -> Source.Term:
  Source.Term.sub(t, 0n, Source.Sub.env{Env.rb(e)})

def Look.rb(l: Machine.Look) -> Source.Term:
  match l:
    case Machine.Look.val{v}:
      Val.rb(v)
    case Machine.Look.free{j}:
      Source.Term.Var{j}

# the term that the frame fr makes around u
def Fr.plug(fr: Machine.Fr, u: Source.Term) -> Source.Term:
  match fr:
    case Machine.Fr.arg{q, x}:
      Source.Term.App{q, u, Val.rb(x)}
    case Machine.Fr.fun{q, f}:
      Source.Term.App{q, Val.rb(f), u}
    case Machine.Fr.let{q, f, e}:
      Source.Term.Let{q, u, Source.Term.sub(f, 1n, Source.Sub.env{Env.rb(e)})}
    case Machine.Fr.fst{q, b, e}:
      Source.Term.Tup{q, u, Clo.rb(b, e)}
    case Machine.Fr.snd{q, a}:
      Source.Term.Tup{q, Val.rb(a), u}
    case Machine.Fr.rwt{p, f, +e}:
      Source.Term.Rwt{u, Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e)}
    case Machine.Fr.min1{b, e}:
      Source.Term.Min{u, Clo.rb(b, e)}
    case Machine.Fr.min2{a}:
      Source.Term.Min{Val.rb(a), u}

# the term that the frames fs make around u, the first the innermost
def Frs.plug(fs: List<&2, Machine.Fr>, u: Source.Term) -> Source.Term:
  match fs:
    case Nil{}:
      u
    case Con{fr, rest}:
      Frs.plug(rest, Fr.plug(fr, u))

# the term that a state stands for
def St.rb(s: Machine.St) -> Source.Term:
  match s:
    case Machine.St.eval{t, e, fs}:
      Frs.plug(fs, Clo.rb(t, e))
    case Machine.St.ret{v, fs}:
      Frs.plug(fs, Val.rb(v))

# Invariant
# =========

# what a value is: good (a value of Eval, whose form is its constructor), any
# (good, or a closure), an environment of any, or a list of arguments of any
type Mode is Data:
  Mode.good{}
  Mode.any{}
  Mode.env{}
  Mode.args{}

def Mode.field(q: Source.Quan) -> Mode:
  match q:
    case Source.Q0{}:
      Mode.any{}
    case Source.Q1{}:
      Mode.good{}
    case Source.Q2{}:
      Mode.good{}

# a λ, a λ-match or a type: a closure of it is a value
def Term.is_fun(t: Source.Term) -> Bool:
  match t:
    case Source.Term.Typ{q}:
      True{}
    case Source.Term.All{q, a, b}:
      True{}
    case Source.Term.Lam{q, f}:
      True{}
    case Source.Term.Sig{q, a, b}:
      True{}
    case Source.Term.Prj{h}:
      True{}
    case Source.Term.Enu{ks}:
      True{}
    case Source.Term.Mat{k, h, m}:
      True{}
    case Source.Term.Efq{}:
      True{}
    case Source.Term.Eql{a, b, c}:
      True{}
    case _:
      False{}

# the invariant of each value that the machine makes, in the mode m
def Val.ok(v: Machine.Val, m: Mode, +bk: List<&2, Source.Def>) -> Bool:
  match v m:
    case Machine.Val.lab{k} Mode.good{}:
      True{}
    case Machine.Val.rfl{} Mode.good{}:
      True{}
    case Machine.Val.tup{+q, a, b} Mode.good{}:
      Val.ok(a, Mode.field(q), bk) && Val.ok(b, Mode.good{}, bk)
    case Machine.Val.clo{t, e} Mode.good{}:
      Term.is_fun(t) && Val.ok(e, Mode.env{}, bk)
    case Machine.Val.call{+k, +xs} Mode.good{}:
      Val.ok(xs, Mode.args{}, bk) && Source.Term.is_value(Val.rb(Machine.Val.call{k, xs}), False{}, bk)
    case Machine.Val.lab{k} Mode.any{}:
      True{}
    case Machine.Val.rfl{} Mode.any{}:
      True{}
    case Machine.Val.tup{+q, a, b} Mode.any{}:
      Val.ok(a, Mode.field(q), bk) && Val.ok(b, Mode.good{}, bk)
    case Machine.Val.clo{t, e} Mode.any{}:
      Val.ok(e, Mode.env{}, bk)
    case Machine.Val.call{+k, +xs} Mode.any{}:
      Val.ok(xs, Mode.args{}, bk) && Source.Term.is_value(Val.rb(Machine.Val.call{k, xs}), False{}, bk)
    case Machine.Val.nil{} Mode.env{}:
      True{}
    case Machine.Val.env{x, rest} Mode.env{}:
      Val.ok(x, Mode.any{}, bk) && Val.ok(rest, Mode.env{}, bk)
    case Machine.Val.nil{} Mode.args{}:
      True{}
    case Machine.Val.arg{q, x, rest} Mode.args{}:
      Val.ok(x, Mode.any{}, bk) && Val.ok(rest, Mode.args{}, bk)
    case _ _:
      False{}

def Fr.ok(fr: Machine.Fr, +bk: List<&2, Source.Def>) -> Bool:
  match fr:
    case Machine.Fr.arg{q, x}:
      Val.ok(x, Mode.any{}, bk)
    case Machine.Fr.fun{q, f}:
      Source.Quan.live(q) && Val.ok(f, Mode.good{}, bk)
    case Machine.Fr.let{q, f, e}:
      Source.Quan.live(q) && Val.ok(e, Mode.env{}, bk)
    case Machine.Fr.fst{q, b, e}:
      Source.Quan.live(q) && Val.ok(e, Mode.env{}, bk)
    case Machine.Fr.snd{q, a}:
      Val.ok(a, Mode.field(q), bk)
    case Machine.Fr.rwt{p, f, e}:
      Val.ok(e, Mode.env{}, bk)
    case Machine.Fr.min1{b, e}:
      Val.ok(e, Mode.env{}, bk)
    case Machine.Fr.min2{a}:
      Val.ok(a, Mode.good{}, bk)

def Frs.ok(fs: List<&2, Machine.Fr>, +bk: List<&2, Source.Def>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{fr, rest}:
      Fr.ok(fr, bk) && Frs.ok(rest, bk)

def St.ok(s: Machine.St, +bk: List<&2, Source.Def>) -> Bool:
  match s:
    case Machine.St.eval{t, e, fs}:
      Val.ok(e, Mode.env{}, bk) && Frs.ok(fs, bk)
    case Machine.St.ret{v, fs}:
      Val.ok(v, Mode.good{}, bk) && Frs.ok(fs, bk)

# Measure
# =======

# n at a live quantity, else 0
def Q.w(q: Source.Quan, n: Nat) -> Nat:
  match q:
    case Source.Q0{}:
      0n
    case Source.Q1{}:
      n
    case Source.Q2{}:
      n

# a bound on the steps that the machine takes in t before an Eval step
def Term.w(t: Source.Term) -> Nat:
  match t:
    case Source.Term.App{q, f, x}:
      5n+Nat.add(Q.w(q, Term.w(x)), Term.w(f))
    case Source.Term.Tup{q, a, b}:
      5n+Nat.add(Term.w(b), Q.w(q, Term.w(a)))
    case Source.Term.Let{q, v, f}:
      5n+Q.w(q, Term.w(v))
    case Source.Term.Rwt{e, p, f}:
      5n+Term.w(e)
    case Source.Term.Min{a, b}:
      5n+Nat.add(Term.w(b), Term.w(a))
    case _:
      5n

def Term.var(t: Source.Term) -> Nat:
  match t:
    case Source.Term.Var{i}:
      1n
    case _:
      0n

# a bound on the steps that the frame fr still needs
def Fr.pend(fr: Machine.Fr) -> Nat:
  match fr:
    case Machine.Fr.arg{q, x}:
      match q:
        case Source.Q0{}:
          1n
        case Source.Q1{}:
          3n+Term.w(Val.rb(x))
        case Source.Q2{}:
          3n+Term.w(Val.rb(x))
    case Machine.Fr.fun{q, f}:
      1n
    case Machine.Fr.let{q, f, e}:
      0n
    case Machine.Fr.fst{q, b, e}:
      3n+Term.w(Clo.rb(b, e))
    case Machine.Fr.snd{q, a}:
      1n
    case Machine.Fr.rwt{p, f, e}:
      0n
    case Machine.Fr.min1{b, e}:
      3n+Term.w(Clo.rb(b, e))
    case Machine.Fr.min2{a}:
      1n

def Frs.mu(fs: List<&2, Machine.Fr>, acc: Nat) -> Nat:
  match fs:
    case Nil{}:
      acc
    case Con{fr, rest}:
      Frs.mu(rest, Nat.add(Fr.pend(fr), acc))

# a bound on the steps from s before the next Eval step
def St.mu(s: Machine.St) -> Nat:
  match s:
    case Machine.St.eval{+t, e, fs}:
      Frs.mu(fs, Nat.add(Term.var(t), Term.w(Clo.rb(t, e))))
    case Machine.St.ret{v, fs}:
      Frs.mu(fs, 0n)

# Machine.step from a state whose term is t and whose measure is mu went to m:
# a state for t with a smaller measure, a state for the term after t's step,
# the end at a value that stands for t, or stuck where t is stuck
def Moved(m: Machine.Move, t: Source.Term, mu: Nat, +bk: List<&2, Source.Def>) -> Type:
  match m:
    case Machine.Move.go{s}:
      {St.ok(s, bk) == True{} : Bool} &
        (({St.rb(s) == t : Source.Term} & {Nat.is_le(1n+St.mu(s), mu) == True{} : Bool}) |
          {Source.Term.step(t, bk) == Some{St.rb(s)} : Maybe<&2, Source.Term>})
    case Machine.Move.done{v}:
      {Val.ok(v, Mode.good{}, bk) == True{} : Bool} & {Val.rb(v) == t : Source.Term}
    case Machine.Move.stuck{}:
      {Source.Term.is_value(t, False{}, bk) == False{} : Bool} &
        {Source.Term.step(t, bk) == None{} : Maybe<&2, Source.Term>}
# Substitution
# ============

# Term.shift by 0 keeps a term
def Term.shift_zero(t: Source.Term, +d: Nat) -> {Source.Term.shift(t, d, 0n) == t : Source.Term}:
  match t:
    case Source.Term.Var{+z0}:
      %Equal.sym(Nat, Nat.add(z0, 0n), z0, Nat.add_zero(z0)) : {Source.Term.Var{Source.Bool.if(Nat, Nat.is_lt(z0, d), z0, _)} == Source.Term.Var{z0} : Source.Term}
      Shared.Bool.elim(Nat.is_lt(z0, d), x => {Source.Term.Var{Source.Bool.if(Nat, x, z0, z0)} == Source.Term.Var{z0} : Source.Term}, {==}, {==})
    case Source.Term.Ref{+z0}:
      {==}
    case Source.Term.Ann{+z0, +z1}:
      %Term.shift_zero(z0, d) : {Source.Term.Ann{Source.Term.shift(z0, d, 0n), Source.Term.shift(z1, d, 0n)} == Source.Term.Ann{_, z1} : Source.Term}
      %Term.shift_zero(z1, d) : {Source.Term.Ann{Source.Term.shift(z0, d, 0n), Source.Term.shift(z1, d, 0n)} == Source.Term.Ann{Source.Term.shift(z0, d, 0n), _} : Source.Term}
      {==}
    case Source.Term.Let{+z0, +z1, +z2}:
      %Term.shift_zero(z1, d) : {Source.Term.Let{z0, Source.Term.shift(z1, d, 0n), Source.Term.shift(z2, 1n+d, 0n)} == Source.Term.Let{z0, _, z2} : Source.Term}
      %Term.shift_zero(z2, 1n+d) : {Source.Term.Let{z0, Source.Term.shift(z1, d, 0n), Source.Term.shift(z2, 1n+d, 0n)} == Source.Term.Let{z0, Source.Term.shift(z1, d, 0n), _} : Source.Term}
      {==}
    case Source.Term.Typ{+z0}:
      %Term.shift_zero(z0, d) : {Source.Term.Typ{Source.Term.shift(z0, d, 0n)} == Source.Term.Typ{_} : Source.Term}
      {==}
    case Source.Term.Min{+z0, +z1}:
      %Term.shift_zero(z0, d) : {Source.Term.Min{Source.Term.shift(z0, d, 0n), Source.Term.shift(z1, d, 0n)} == Source.Term.Min{_, z1} : Source.Term}
      %Term.shift_zero(z1, d) : {Source.Term.Min{Source.Term.shift(z0, d, 0n), Source.Term.shift(z1, d, 0n)} == Source.Term.Min{Source.Term.shift(z0, d, 0n), _} : Source.Term}
      {==}
    case Source.Term.All{+z0, +z1, +z2}:
      %Term.shift_zero(z1, d) : {Source.Term.All{z0, Source.Term.shift(z1, d, 0n), Source.Term.shift(z2, 1n+d, 0n)} == Source.Term.All{z0, _, z2} : Source.Term}
      %Term.shift_zero(z2, 1n+d) : {Source.Term.All{z0, Source.Term.shift(z1, d, 0n), Source.Term.shift(z2, 1n+d, 0n)} == Source.Term.All{z0, Source.Term.shift(z1, d, 0n), _} : Source.Term}
      {==}
    case Source.Term.Lam{+z0, +z1}:
      %Term.shift_zero(z1, 1n+d) : {Source.Term.Lam{z0, Source.Term.shift(z1, 1n+d, 0n)} == Source.Term.Lam{z0, _} : Source.Term}
      {==}
    case Source.Term.App{+z0, +z1, +z2}:
      %Term.shift_zero(z1, d) : {Source.Term.App{z0, Source.Term.shift(z1, d, 0n), Source.Term.shift(z2, d, 0n)} == Source.Term.App{z0, _, z2} : Source.Term}
      %Term.shift_zero(z2, d) : {Source.Term.App{z0, Source.Term.shift(z1, d, 0n), Source.Term.shift(z2, d, 0n)} == Source.Term.App{z0, Source.Term.shift(z1, d, 0n), _} : Source.Term}
      {==}
    case Source.Term.Sig{+z0, +z1, +z2}:
      %Term.shift_zero(z1, d) : {Source.Term.Sig{z0, Source.Term.shift(z1, d, 0n), Source.Term.shift(z2, 1n+d, 0n)} == Source.Term.Sig{z0, _, z2} : Source.Term}
      %Term.shift_zero(z2, 1n+d) : {Source.Term.Sig{z0, Source.Term.shift(z1, d, 0n), Source.Term.shift(z2, 1n+d, 0n)} == Source.Term.Sig{z0, Source.Term.shift(z1, d, 0n), _} : Source.Term}
      {==}
    case Source.Term.Tup{+z0, +z1, +z2}:
      %Term.shift_zero(z1, d) : {Source.Term.Tup{z0, Source.Term.shift(z1, d, 0n), Source.Term.shift(z2, d, 0n)} == Source.Term.Tup{z0, _, z2} : Source.Term}
      %Term.shift_zero(z2, d) : {Source.Term.Tup{z0, Source.Term.shift(z1, d, 0n), Source.Term.shift(z2, d, 0n)} == Source.Term.Tup{z0, Source.Term.shift(z1, d, 0n), _} : Source.Term}
      {==}
    case Source.Term.Prj{+z0}:
      %Term.shift_zero(z0, d) : {Source.Term.Prj{Source.Term.shift(z0, d, 0n)} == Source.Term.Prj{_} : Source.Term}
      {==}
    case Source.Term.Enu{+z0}:
      {==}
    case Source.Term.Lab{+z0}:
      {==}
    case Source.Term.Mat{+z0, +z1, +z2}:
      %Term.shift_zero(z1, d) : {Source.Term.Mat{z0, Source.Term.shift(z1, d, 0n), Source.Term.shift(z2, d, 0n)} == Source.Term.Mat{z0, _, z2} : Source.Term}
      %Term.shift_zero(z2, d) : {Source.Term.Mat{z0, Source.Term.shift(z1, d, 0n), Source.Term.shift(z2, d, 0n)} == Source.Term.Mat{z0, Source.Term.shift(z1, d, 0n), _} : Source.Term}
      {==}
    case Source.Term.Efq{}:
      {==}
    case Source.Term.Eql{+z0, +z1, +z2}:
      %Term.shift_zero(z0, d) : {Source.Term.Eql{Source.Term.shift(z0, d, 0n), Source.Term.shift(z1, d, 0n), Source.Term.shift(z2, d, 0n)} == Source.Term.Eql{_, z1, z2} : Source.Term}
      %Term.shift_zero(z1, d) : {Source.Term.Eql{Source.Term.shift(z0, d, 0n), Source.Term.shift(z1, d, 0n), Source.Term.shift(z2, d, 0n)} == Source.Term.Eql{Source.Term.shift(z0, d, 0n), _, z2} : Source.Term}
      %Term.shift_zero(z2, d) : {Source.Term.Eql{Source.Term.shift(z0, d, 0n), Source.Term.shift(z1, d, 0n), Source.Term.shift(z2, d, 0n)} == Source.Term.Eql{Source.Term.shift(z0, d, 0n), Source.Term.shift(z1, d, 0n), _} : Source.Term}
      {==}
    case Source.Term.Rfl{}:
      {==}
    case Source.Term.Rwt{+z0, +z1, +z2}:
      %Term.shift_zero(z0, d) : {Source.Term.Rwt{Source.Term.shift(z0, d, 0n), Source.Term.shift(z1, 2n+d, 0n), Source.Term.shift(z2, d, 0n)} == Source.Term.Rwt{_, z1, z2} : Source.Term}
      %Term.shift_zero(z1, 2n+d) : {Source.Term.Rwt{Source.Term.shift(z0, d, 0n), Source.Term.shift(z1, 2n+d, 0n), Source.Term.shift(z2, d, 0n)} == Source.Term.Rwt{Source.Term.shift(z0, d, 0n), _, z2} : Source.Term}
      %Term.shift_zero(z2, d) : {Source.Term.Rwt{Source.Term.shift(z0, d, 0n), Source.Term.shift(z1, 2n+d, 0n), Source.Term.shift(z2, d, 0n)} == Source.Term.Rwt{Source.Term.shift(z0, d, 0n), Source.Term.shift(z1, 2n+d, 0n), _} : Source.Term}
      {==}

# variable i below c, or at or above it, and the numbers that Term.sub_shift
# needs in each case
type Two<-i: Nat, -c: Nat, -d: Nat> is Type:
  Two.lt{h1: {Nat.is_lt(i, c) == True{} : Bool}, h2: {Nat.is_lt(i, Nat.add(c, d)) == True{} : Bool}}
  Two.ge{h1: {Nat.is_lt(i, c) == False{} : Bool},
    h2: {Nat.is_lt(Nat.add(i, 1n+d), Nat.add(c, d)) == False{} : Bool},
    h3: {Nat.sub(Nat.add(i, 1n+d), Nat.add(c, d)) == 1n+Nat.sub(i, c) : Nat},
    h4: {Nat.add(Nat.sub(i, c), Nat.add(c, d)) == Nat.add(i, d) : Nat}}

def Nat.lt_above(+i: Nat, d: Nat) -> {Nat.is_lt(1n+Nat.add(i, d), d) == False{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(i, 1n+p), 1n+Nat.add(i, p), Nat.add_succ(i, p)) :
        {Nat.is_lt(_, p) == False{} : Bool}
      Nat.lt_above(i, p)

def Nat.sub_above(+i: Nat, d: Nat) -> {Nat.sub(1n+Nat.add(i, d), d) == 1n+i : Nat}:
  match d:
    case 0n:
      %Nat.add_zero(i) : {1n+Nat.add(i, 0n) == 1n+_ : Nat}
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(i, 1n+p), 1n+Nat.add(i, p), Nat.add_succ(i, p)) :
        {Nat.sub(_, p) == 1n+i : Nat}
      Nat.sub_above(i, p)

def Two.h2(+j: Nat, +d: Nat) -> {Nat.is_lt(Nat.add(j, 1n+d), d) == False{} : Bool}:
  %Equal.sym(Nat, Nat.add(j, 1n+d), 1n+Nat.add(j, d), Nat.add_succ(j, d)) : {Nat.is_lt(_, d) == False{} : Bool}
  Nat.lt_above(j, d)

def Two.h3(+j: Nat, +d: Nat) -> {Nat.sub(Nat.add(j, 1n+d), d) == 1n+Nat.sub(j, 0n) : Nat}:
  %Equal.sym(Nat, Nat.add(j, 1n+d), 1n+Nat.add(j, d), Nat.add_succ(j, d)) : {Nat.sub(_, d) == 1n+Nat.sub(j, 0n) : Nat}
  %Equal.sym(Nat, Nat.sub(j, 0n), j, Nat.sub_zero(j)) : {Nat.sub(1n+Nat.add(j, d), d) == 1n+_ : Nat}
  Nat.sub_above(j, d)

def Two.h4(+j: Nat, -d: Nat) -> {Nat.add(Nat.sub(j, 0n), d) == Nat.add(j, d) : Nat}:
  %Nat.sub_zero(j) : {Nat.add(Nat.sub(j, 0n), d) == Nat.add(_, d) : Nat}
  {==}

def Two.succ(+j: Nat, +p: Nat, +d: Nat, t: Two<j, p, d>) -> Two<1n+j, 1n+p, d>:
  match t:
    case Two.lt{h1, h2}:
      Two.lt{h1, h2}
    case Two.ge{h1, h2, h3, h4}:
      Two.ge{h1, h2, h3,
        Equal.trans(Nat, Nat.add(Nat.sub(j, p), 1n+Nat.add(p, d)), 1n+Nat.add(Nat.sub(j, p), Nat.add(p, d)),
          1n+Nat.add(j, d), Nat.add_succ(Nat.sub(j, p), Nat.add(p, d)),
          Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.sub(j, p), Nat.add(p, d)), Nat.add(j, d), h4))}

def Two.zero(+i: Nat, +d: Nat) -> Two<i, 0n, d>:
  Two.ge{Nat.is_lt_zero(i), Two.h2(i, d), Two.h3(i, d), Two.h4(i, d)}

def Two.of(+c: Nat, +i: Nat, +d: Nat) -> Two<i, c, d>:
  match c i:
    case 0n j:
      Two.zero(j, d)
    case 1n+p 0n:
      Two.lt{{==}, {==}}
    case 1n+p 1n+j:
      Two.succ(j, p, d, Two.of(p, j, d))

def Term.sub_shift.var(+i: Nat, +c: Nat, +d: Nat, +X: Source.Term, t: Two<i, c, d>) ->
  {Source.Term.sub(Source.Term.shift(Source.Term.Var{i}, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}) ==
    Source.Term.shift(Source.Term.Var{i}, c, d) : Source.Term}:
  match t:
    case Two.lt{+h1, +h2}:
      %Equal.sym(Bool, Nat.is_lt(i, c), True{}, h1) :
        {Source.Term.sub(Source.Term.Var{Source.Bool.if(Nat, _, i, Nat.add(i, 1n+d))}, Nat.add(c, d), Source.Sub.one{X}) ==
          Source.Term.Var{Source.Bool.if(Nat, _, i, Nat.add(i, d))} : Source.Term}
      %Equal.sym(Bool, Nat.is_lt(i, Nat.add(c, d)), True{}, h2) :
        {Source.Sub.lift(_, i, Nat.add(c, d), Source.Sub.one{X}) == Source.Term.Var{i} : Source.Term}
      {==}
    case Two.ge{+h1, +h2, +h3, +h4}:
      %Equal.sym(Bool, Nat.is_lt(i, c), False{}, h1) :
        {Source.Term.sub(Source.Term.Var{Source.Bool.if(Nat, _, i, Nat.add(i, 1n+d))}, Nat.add(c, d), Source.Sub.one{X}) ==
          Source.Term.Var{Source.Bool.if(Nat, _, i, Nat.add(i, d))} : Source.Term}
      %Equal.sym(Bool, Nat.is_lt(Nat.add(i, 1n+d), Nat.add(c, d)), False{}, h2) :
        {Source.Sub.lift(_, Nat.add(i, 1n+d), Nat.add(c, d), Source.Sub.one{X}) == Source.Term.Var{Nat.add(i, d)} : Source.Term}
      %Equal.sym(Nat, Nat.sub(Nat.add(i, 1n+d), Nat.add(c, d)), 1n+Nat.sub(i, c), h3) :
        {Source.Term.shift(Source.Sub.at(Source.Sub.one{X}, _), 0n, Nat.add(c, d)) == Source.Term.Var{Nat.add(i, d)} : Source.Term}
      %Equal.sym(Bool, Nat.is_lt(Nat.sub(i, c), 0n), False{}, Nat.is_lt_zero(Nat.sub(i, c))) :
        {Source.Term.Var{Source.Bool.if(Nat, _, Nat.sub(i, c), Nat.add(Nat.sub(i, c), Nat.add(c, d)))} ==
          Source.Term.Var{Nat.add(i, d)} : Source.Term}
      %h4 : {Source.Term.Var{Nat.add(Nat.sub(i, c), Nat.add(c, d))} == Source.Term.Var{_} : Source.Term}
      {==}

# a term shifted by 1 + d at c, with variable c + d then replaced, is the term
# shifted by d at c
def Term.sub_shift(t: Source.Term, +c: Nat, +d: Nat, +X: Source.Term) ->
  {Source.Term.sub(Source.Term.shift(t, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}) ==
    Source.Term.shift(t, c, d) : Source.Term}:
  match t:
    case Source.Term.Var{+z0}:
      Term.sub_shift.var(z0, c, d, X, Two.of(c, z0, d))
    case Source.Term.Ref{+z0}:
      {==}
    case Source.Term.Ann{+z0, +z1}:
      %Term.sub_shift(z0, c, d, X) : {Source.Term.Ann{Source.Term.sub(Source.Term.shift(z0, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X})} == Source.Term.Ann{_, Source.Term.shift(z1, c, d)} : Source.Term}
      %Term.sub_shift(z1, c, d, X) : {Source.Term.Ann{Source.Term.sub(Source.Term.shift(z0, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X})} == Source.Term.Ann{Source.Term.sub(Source.Term.shift(z0, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), _} : Source.Term}
      {==}
    case Source.Term.Let{+z0, +z1, +z2}:
      %Term.sub_shift(z1, c, d, X) : {Source.Term.Let{z0, Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z2, 1n+c, 1n+d), 1n+Nat.add(c, d), Source.Sub.one{X})} == Source.Term.Let{z0, _, Source.Term.shift(z2, 1n+c, d)} : Source.Term}
      %Term.sub_shift(z2, 1n+c, d, X) : {Source.Term.Let{z0, Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z2, 1n+c, 1n+d), 1n+Nat.add(c, d), Source.Sub.one{X})} == Source.Term.Let{z0, Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), _} : Source.Term}
      {==}
    case Source.Term.Typ{+z0}:
      %Term.sub_shift(z0, c, d, X) : {Source.Term.Typ{Source.Term.sub(Source.Term.shift(z0, c, 1n+d), Nat.add(c, d), Source.Sub.one{X})} == Source.Term.Typ{_} : Source.Term}
      {==}
    case Source.Term.Min{+z0, +z1}:
      %Term.sub_shift(z0, c, d, X) : {Source.Term.Min{Source.Term.sub(Source.Term.shift(z0, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X})} == Source.Term.Min{_, Source.Term.shift(z1, c, d)} : Source.Term}
      %Term.sub_shift(z1, c, d, X) : {Source.Term.Min{Source.Term.sub(Source.Term.shift(z0, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X})} == Source.Term.Min{Source.Term.sub(Source.Term.shift(z0, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), _} : Source.Term}
      {==}
    case Source.Term.All{+z0, +z1, +z2}:
      %Term.sub_shift(z1, c, d, X) : {Source.Term.All{z0, Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z2, 1n+c, 1n+d), 1n+Nat.add(c, d), Source.Sub.one{X})} == Source.Term.All{z0, _, Source.Term.shift(z2, 1n+c, d)} : Source.Term}
      %Term.sub_shift(z2, 1n+c, d, X) : {Source.Term.All{z0, Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z2, 1n+c, 1n+d), 1n+Nat.add(c, d), Source.Sub.one{X})} == Source.Term.All{z0, Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), _} : Source.Term}
      {==}
    case Source.Term.Lam{+z0, +z1}:
      %Term.sub_shift(z1, 1n+c, d, X) : {Source.Term.Lam{z0, Source.Term.sub(Source.Term.shift(z1, 1n+c, 1n+d), 1n+Nat.add(c, d), Source.Sub.one{X})} == Source.Term.Lam{z0, _} : Source.Term}
      {==}
    case Source.Term.App{+z0, +z1, +z2}:
      %Term.sub_shift(z1, c, d, X) : {Source.Term.App{z0, Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z2, c, 1n+d), Nat.add(c, d), Source.Sub.one{X})} == Source.Term.App{z0, _, Source.Term.shift(z2, c, d)} : Source.Term}
      %Term.sub_shift(z2, c, d, X) : {Source.Term.App{z0, Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z2, c, 1n+d), Nat.add(c, d), Source.Sub.one{X})} == Source.Term.App{z0, Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), _} : Source.Term}
      {==}
    case Source.Term.Sig{+z0, +z1, +z2}:
      %Term.sub_shift(z1, c, d, X) : {Source.Term.Sig{z0, Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z2, 1n+c, 1n+d), 1n+Nat.add(c, d), Source.Sub.one{X})} == Source.Term.Sig{z0, _, Source.Term.shift(z2, 1n+c, d)} : Source.Term}
      %Term.sub_shift(z2, 1n+c, d, X) : {Source.Term.Sig{z0, Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z2, 1n+c, 1n+d), 1n+Nat.add(c, d), Source.Sub.one{X})} == Source.Term.Sig{z0, Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), _} : Source.Term}
      {==}
    case Source.Term.Tup{+z0, +z1, +z2}:
      %Term.sub_shift(z1, c, d, X) : {Source.Term.Tup{z0, Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z2, c, 1n+d), Nat.add(c, d), Source.Sub.one{X})} == Source.Term.Tup{z0, _, Source.Term.shift(z2, c, d)} : Source.Term}
      %Term.sub_shift(z2, c, d, X) : {Source.Term.Tup{z0, Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z2, c, 1n+d), Nat.add(c, d), Source.Sub.one{X})} == Source.Term.Tup{z0, Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), _} : Source.Term}
      {==}
    case Source.Term.Prj{+z0}:
      %Term.sub_shift(z0, c, d, X) : {Source.Term.Prj{Source.Term.sub(Source.Term.shift(z0, c, 1n+d), Nat.add(c, d), Source.Sub.one{X})} == Source.Term.Prj{_} : Source.Term}
      {==}
    case Source.Term.Enu{+z0}:
      {==}
    case Source.Term.Lab{+z0}:
      {==}
    case Source.Term.Mat{+z0, +z1, +z2}:
      %Term.sub_shift(z1, c, d, X) : {Source.Term.Mat{z0, Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z2, c, 1n+d), Nat.add(c, d), Source.Sub.one{X})} == Source.Term.Mat{z0, _, Source.Term.shift(z2, c, d)} : Source.Term}
      %Term.sub_shift(z2, c, d, X) : {Source.Term.Mat{z0, Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z2, c, 1n+d), Nat.add(c, d), Source.Sub.one{X})} == Source.Term.Mat{z0, Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), _} : Source.Term}
      {==}
    case Source.Term.Efq{}:
      {==}
    case Source.Term.Eql{+z0, +z1, +z2}:
      %Term.sub_shift(z0, c, d, X) : {Source.Term.Eql{Source.Term.sub(Source.Term.shift(z0, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z2, c, 1n+d), Nat.add(c, d), Source.Sub.one{X})} == Source.Term.Eql{_, Source.Term.shift(z1, c, d), Source.Term.shift(z2, c, d)} : Source.Term}
      %Term.sub_shift(z1, c, d, X) : {Source.Term.Eql{Source.Term.sub(Source.Term.shift(z0, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z2, c, 1n+d), Nat.add(c, d), Source.Sub.one{X})} == Source.Term.Eql{Source.Term.sub(Source.Term.shift(z0, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), _, Source.Term.shift(z2, c, d)} : Source.Term}
      %Term.sub_shift(z2, c, d, X) : {Source.Term.Eql{Source.Term.sub(Source.Term.shift(z0, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z2, c, 1n+d), Nat.add(c, d), Source.Sub.one{X})} == Source.Term.Eql{Source.Term.sub(Source.Term.shift(z0, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z1, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), _} : Source.Term}
      {==}
    case Source.Term.Rfl{}:
      {==}
    case Source.Term.Rwt{+z0, +z1, +z2}:
      %Term.sub_shift(z0, c, d, X) : {Source.Term.Rwt{Source.Term.sub(Source.Term.shift(z0, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z1, 2n+c, 1n+d), 2n+Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z2, c, 1n+d), Nat.add(c, d), Source.Sub.one{X})} == Source.Term.Rwt{_, Source.Term.shift(z1, 2n+c, d), Source.Term.shift(z2, c, d)} : Source.Term}
      %Term.sub_shift(z1, 2n+c, d, X) : {Source.Term.Rwt{Source.Term.sub(Source.Term.shift(z0, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z1, 2n+c, 1n+d), 2n+Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z2, c, 1n+d), Nat.add(c, d), Source.Sub.one{X})} == Source.Term.Rwt{Source.Term.sub(Source.Term.shift(z0, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), _, Source.Term.shift(z2, c, d)} : Source.Term}
      %Term.sub_shift(z2, c, d, X) : {Source.Term.Rwt{Source.Term.sub(Source.Term.shift(z0, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z1, 2n+c, 1n+d), 2n+Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z2, c, 1n+d), Nat.add(c, d), Source.Sub.one{X})} == Source.Term.Rwt{Source.Term.sub(Source.Term.shift(z0, c, 1n+d), Nat.add(c, d), Source.Sub.one{X}), Source.Term.sub(Source.Term.shift(z1, 2n+c, 1n+d), 2n+Nat.add(c, d), Source.Sub.one{X}), _} : Source.Term}
      {==}

# variable i below d, at d, or above it, and the numbers that Term.sub_sub
# needs in each case
type Tri<-i: Nat, -d: Nat> is Type:
  Tri.lt{h1: {Nat.is_lt(i, 1n+d) == True{} : Bool}, h2: {Nat.is_lt(i, d) == True{} : Bool}}
  Tri.eq{h1: {Nat.is_lt(i, 1n+d) == True{} : Bool}, h2: {Nat.is_lt(i, d) == False{} : Bool},
    h3: {Nat.sub(i, d) == 0n : Nat}}
  Tri.gt{h1: {Nat.is_lt(i, 1n+d) == False{} : Bool}, h2: {Nat.is_lt(i, d) == False{} : Bool},
    h3: {Nat.sub(i, d) == 1n+Nat.sub(i, 1n+d) : Nat}}

def Tri.succ(-j: Nat, -p: Nat, t: Tri<j, p>) -> Tri<1n+j, 1n+p>:
  match t:
    case Tri.lt{h1, h2}:
      Tri.lt{h1, h2}
    case Tri.eq{h1, h2, h3}:
      Tri.eq{h1, h2, h3}
    case Tri.gt{h1, h2, h3}:
      Tri.gt{h1, h2, h3}

def Tri.of(+i: Nat, +d: Nat) -> Tri<i, d>:
  match i d:
    case 0n 0n:
      Tri.eq{{==}, {==}, {==}}
    case 0n 1n+p:
      Tri.lt{{==}, {==}}
    case 1n+j 0n:
      Tri.gt{Nat.is_lt_zero(j), {==},
        Equal.cong(Nat, Nat, z => 1n+z, j, Nat.sub(j, 0n), Equal.sym(Nat, Nat.sub(j, 0n), j, Nat.sub_zero(j)))}
    case 1n+j 1n+p:
      Tri.succ(j, p, Tri.of(j, p))

def Term.sub_sub.var(+i: Nat, +d: Nat, +E: List<&2, Source.Term>, +X: Source.Term, t: Tri<i, d>) ->
  {Source.Term.sub(Source.Term.sub(Source.Term.Var{i}, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}) ==
    Source.Term.sub(Source.Term.Var{i}, d, Source.Sub.env{Con{X, E}}) : Source.Term}:
  match t:
    case Tri.lt{+h1, +h2}:
      %Equal.sym(Bool, Nat.is_lt(i, 1n+d), True{}, h1) :
        {Source.Term.sub(Source.Sub.lift(_, i, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}) ==
          Source.Sub.lift(Nat.is_lt(i, d), i, d, Source.Sub.env{Con{X, E}}) : Source.Term}
      %Equal.sym(Bool, Nat.is_lt(i, d), True{}, h2) :
        {Source.Sub.lift(_, i, d, Source.Sub.one{X}) == Source.Sub.lift(_, i, d, Source.Sub.env{Con{X, E}}) : Source.Term}
      {==}
    case Tri.eq{+h1, +h2, +h3}:
      %Equal.sym(Bool, Nat.is_lt(i, 1n+d), True{}, h1) :
        {Source.Term.sub(Source.Sub.lift(_, i, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}) ==
          Source.Sub.lift(Nat.is_lt(i, d), i, d, Source.Sub.env{Con{X, E}}) : Source.Term}
      %Equal.sym(Bool, Nat.is_lt(i, d), False{}, h2) :
        {Source.Sub.lift(_, i, d, Source.Sub.one{X}) == Source.Sub.lift(_, i, d, Source.Sub.env{Con{X, E}}) : Source.Term}
      %Equal.sym(Nat, Nat.sub(i, d), 0n, h3) :
        {Source.Term.shift(Source.Sub.at(Source.Sub.one{X}, _), 0n, d) ==
          Source.Term.shift(Source.Sub.at(Source.Sub.env{Con{X, E}}, _), 0n, d) : Source.Term}
      {==}
    case Tri.gt{+h1, +h2, +h3}:
      %Equal.sym(Bool, Nat.is_lt(i, 1n+d), False{}, h1) :
        {Source.Term.sub(Source.Sub.lift(_, i, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}) ==
          Source.Sub.lift(Nat.is_lt(i, d), i, d, Source.Sub.env{Con{X, E}}) : Source.Term}
      %Equal.sym(Bool, Nat.is_lt(i, d), False{}, h2) :
        {Source.Term.sub(Source.Term.shift(Source.Env.sub(E, Nat.sub(i, 1n+d)), 0n, 1n+d), d, Source.Sub.one{X}) ==
          Source.Sub.lift(_, i, d, Source.Sub.env{Con{X, E}}) : Source.Term}
      %Equal.sym(Nat, Nat.sub(i, d), 1n+Nat.sub(i, 1n+d), h3) :
        {Source.Term.sub(Source.Term.shift(Source.Env.sub(E, Nat.sub(i, 1n+d)), 0n, 1n+d), d, Source.Sub.one{X}) ==
          Source.Term.shift(Source.Sub.at(Source.Sub.env{Con{X, E}}, _), 0n, d) : Source.Term}
      Term.sub_shift(Source.Env.sub(E, Nat.sub(i, 1n+d)), 0n, d, X)

# a term with its variables from d + 1 on taken from E, then variable d
# replaced by X, is the term with its variables from d on taken from X, E
def Term.sub_sub(t: Source.Term, +d: Nat, +E: List<&2, Source.Term>, +X: Source.Term) ->
  {Source.Term.sub(Source.Term.sub(t, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}) ==
    Source.Term.sub(t, d, Source.Sub.env{Con{X, E}}) : Source.Term}:
  match t:
    case Source.Term.Var{+z0}:
      Term.sub_sub.var(z0, d, E, X, Tri.of(z0, d))
    case Source.Term.Ref{+z0}:
      {==}
    case Source.Term.Ann{+z0, +z1}:
      %Term.sub_sub(z0, d, E, X) : {Source.Term.Ann{Source.Term.sub(Source.Term.sub(z0, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X})} == Source.Term.Ann{_, Source.Term.sub(z1, d, Source.Sub.env{Con{X, E}})} : Source.Term}
      %Term.sub_sub(z1, d, E, X) : {Source.Term.Ann{Source.Term.sub(Source.Term.sub(z0, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X})} == Source.Term.Ann{Source.Term.sub(Source.Term.sub(z0, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), _} : Source.Term}
      {==}
    case Source.Term.Let{+z0, +z1, +z2}:
      %Term.sub_sub(z1, d, E, X) : {Source.Term.Let{z0, Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z2, 2n+d, Source.Sub.env{E}), 1n+d, Source.Sub.one{X})} == Source.Term.Let{z0, _, Source.Term.sub(z2, 1n+d, Source.Sub.env{Con{X, E}})} : Source.Term}
      %Term.sub_sub(z2, 1n+d, E, X) : {Source.Term.Let{z0, Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z2, 2n+d, Source.Sub.env{E}), 1n+d, Source.Sub.one{X})} == Source.Term.Let{z0, Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), _} : Source.Term}
      {==}
    case Source.Term.Typ{+z0}:
      %Term.sub_sub(z0, d, E, X) : {Source.Term.Typ{Source.Term.sub(Source.Term.sub(z0, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X})} == Source.Term.Typ{_} : Source.Term}
      {==}
    case Source.Term.Min{+z0, +z1}:
      %Term.sub_sub(z0, d, E, X) : {Source.Term.Min{Source.Term.sub(Source.Term.sub(z0, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X})} == Source.Term.Min{_, Source.Term.sub(z1, d, Source.Sub.env{Con{X, E}})} : Source.Term}
      %Term.sub_sub(z1, d, E, X) : {Source.Term.Min{Source.Term.sub(Source.Term.sub(z0, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X})} == Source.Term.Min{Source.Term.sub(Source.Term.sub(z0, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), _} : Source.Term}
      {==}
    case Source.Term.All{+z0, +z1, +z2}:
      %Term.sub_sub(z1, d, E, X) : {Source.Term.All{z0, Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z2, 2n+d, Source.Sub.env{E}), 1n+d, Source.Sub.one{X})} == Source.Term.All{z0, _, Source.Term.sub(z2, 1n+d, Source.Sub.env{Con{X, E}})} : Source.Term}
      %Term.sub_sub(z2, 1n+d, E, X) : {Source.Term.All{z0, Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z2, 2n+d, Source.Sub.env{E}), 1n+d, Source.Sub.one{X})} == Source.Term.All{z0, Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), _} : Source.Term}
      {==}
    case Source.Term.Lam{+z0, +z1}:
      %Term.sub_sub(z1, 1n+d, E, X) : {Source.Term.Lam{z0, Source.Term.sub(Source.Term.sub(z1, 2n+d, Source.Sub.env{E}), 1n+d, Source.Sub.one{X})} == Source.Term.Lam{z0, _} : Source.Term}
      {==}
    case Source.Term.App{+z0, +z1, +z2}:
      %Term.sub_sub(z1, d, E, X) : {Source.Term.App{z0, Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z2, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X})} == Source.Term.App{z0, _, Source.Term.sub(z2, d, Source.Sub.env{Con{X, E}})} : Source.Term}
      %Term.sub_sub(z2, d, E, X) : {Source.Term.App{z0, Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z2, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X})} == Source.Term.App{z0, Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), _} : Source.Term}
      {==}
    case Source.Term.Sig{+z0, +z1, +z2}:
      %Term.sub_sub(z1, d, E, X) : {Source.Term.Sig{z0, Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z2, 2n+d, Source.Sub.env{E}), 1n+d, Source.Sub.one{X})} == Source.Term.Sig{z0, _, Source.Term.sub(z2, 1n+d, Source.Sub.env{Con{X, E}})} : Source.Term}
      %Term.sub_sub(z2, 1n+d, E, X) : {Source.Term.Sig{z0, Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z2, 2n+d, Source.Sub.env{E}), 1n+d, Source.Sub.one{X})} == Source.Term.Sig{z0, Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), _} : Source.Term}
      {==}
    case Source.Term.Tup{+z0, +z1, +z2}:
      %Term.sub_sub(z1, d, E, X) : {Source.Term.Tup{z0, Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z2, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X})} == Source.Term.Tup{z0, _, Source.Term.sub(z2, d, Source.Sub.env{Con{X, E}})} : Source.Term}
      %Term.sub_sub(z2, d, E, X) : {Source.Term.Tup{z0, Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z2, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X})} == Source.Term.Tup{z0, Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), _} : Source.Term}
      {==}
    case Source.Term.Prj{+z0}:
      %Term.sub_sub(z0, d, E, X) : {Source.Term.Prj{Source.Term.sub(Source.Term.sub(z0, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X})} == Source.Term.Prj{_} : Source.Term}
      {==}
    case Source.Term.Enu{+z0}:
      {==}
    case Source.Term.Lab{+z0}:
      {==}
    case Source.Term.Mat{+z0, +z1, +z2}:
      %Term.sub_sub(z1, d, E, X) : {Source.Term.Mat{z0, Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z2, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X})} == Source.Term.Mat{z0, _, Source.Term.sub(z2, d, Source.Sub.env{Con{X, E}})} : Source.Term}
      %Term.sub_sub(z2, d, E, X) : {Source.Term.Mat{z0, Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z2, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X})} == Source.Term.Mat{z0, Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), _} : Source.Term}
      {==}
    case Source.Term.Efq{}:
      {==}
    case Source.Term.Eql{+z0, +z1, +z2}:
      %Term.sub_sub(z0, d, E, X) : {Source.Term.Eql{Source.Term.sub(Source.Term.sub(z0, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z2, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X})} == Source.Term.Eql{_, Source.Term.sub(z1, d, Source.Sub.env{Con{X, E}}), Source.Term.sub(z2, d, Source.Sub.env{Con{X, E}})} : Source.Term}
      %Term.sub_sub(z1, d, E, X) : {Source.Term.Eql{Source.Term.sub(Source.Term.sub(z0, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z2, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X})} == Source.Term.Eql{Source.Term.sub(Source.Term.sub(z0, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), _, Source.Term.sub(z2, d, Source.Sub.env{Con{X, E}})} : Source.Term}
      %Term.sub_sub(z2, d, E, X) : {Source.Term.Eql{Source.Term.sub(Source.Term.sub(z0, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z2, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X})} == Source.Term.Eql{Source.Term.sub(Source.Term.sub(z0, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z1, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), _} : Source.Term}
      {==}
    case Source.Term.Rfl{}:
      {==}
    case Source.Term.Rwt{+z0, +z1, +z2}:
      %Term.sub_sub(z0, d, E, X) : {Source.Term.Rwt{Source.Term.sub(Source.Term.sub(z0, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z1, 3n+d, Source.Sub.env{E}), 2n+d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z2, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X})} == Source.Term.Rwt{_, Source.Term.sub(z1, 2n+d, Source.Sub.env{Con{X, E}}), Source.Term.sub(z2, d, Source.Sub.env{Con{X, E}})} : Source.Term}
      %Term.sub_sub(z1, 2n+d, E, X) : {Source.Term.Rwt{Source.Term.sub(Source.Term.sub(z0, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z1, 3n+d, Source.Sub.env{E}), 2n+d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z2, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X})} == Source.Term.Rwt{Source.Term.sub(Source.Term.sub(z0, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), _, Source.Term.sub(z2, d, Source.Sub.env{Con{X, E}})} : Source.Term}
      %Term.sub_sub(z2, d, E, X) : {Source.Term.Rwt{Source.Term.sub(Source.Term.sub(z0, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z1, 3n+d, Source.Sub.env{E}), 2n+d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z2, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X})} == Source.Term.Rwt{Source.Term.sub(Source.Term.sub(z0, 1n+d, Source.Sub.env{E}), d, Source.Sub.one{X}), Source.Term.sub(Source.Term.sub(z1, 3n+d, Source.Sub.env{E}), 2n+d, Source.Sub.one{X}), _} : Source.Term}
      {==}

# variable i under the environment L, at depth 0
def Term.sub_var(+i: Nat, +L: List<&2, Source.Term>) ->
  {Source.Term.sub(Source.Term.Var{i}, 0n, Source.Sub.env{L}) == Source.Env.sub(L, i) : Source.Term}:
  %Equal.sym(Bool, Nat.is_lt(i, 0n), False{}, Nat.is_lt_zero(i)) :
    {Source.Sub.lift(_, i, 0n, Source.Sub.env{L}) == Source.Env.sub(L, i) : Source.Term}
  %Equal.sym(Nat, Nat.sub(i, 0n), i, Nat.sub_zero(i)) :
    {Source.Term.shift(Source.Env.sub(L, _), 0n, 0n) == Source.Env.sub(L, i) : Source.Term}
  Term.shift_zero(Source.Env.sub(L, i), 0n)

# the value x entering the environment of t, as the β step's substitution
def Term.sub_one(+t: Source.Term, +L: List<&2, Source.Term>, +X: Source.Term) ->
  {Source.Term.sub(Source.Term.sub(t, 1n, Source.Sub.env{L}), 0n, Source.Sub.one{X}) ==
    Source.Term.sub(t, 0n, Source.Sub.env{Con{X, L}}) : Source.Term}:
  Term.sub_sub(t, 0n, L, X)

# Calls
# =====

# an application or a def's name: the head of a spine on a def
def Term.is_call(t: Source.Term) -> Bool:
  match t:
    case Source.Term.App{q, f, x}:
      True{}
    case Source.Term.Ref{k}:
      True{}
    case _:
      False{}

def Spine.is_call(ys: List<&2, Source.Arg>, -t: Source.Term, h: {Term.is_call(t) == True{} : Bool}) ->
  {Term.is_call(Source.Term.spine(ys, t)) == True{} : Bool}:
  match ys:
    case Nil{}:
      h
    case Con{Source.Arg{q, x}, rest}:
      Spine.is_call(rest, Source.Term.App{q, t, x}, {==})

def Call.rb_is_call(-k: List<&2, Nat>, xs: Machine.Val) ->
  {Term.is_call(Val.rb(Machine.Val.call{k, xs})) == True{} : Bool}:
  Spine.is_call(Args.rb(xs), Source.Term.Ref{k}, {==})

# a case on a call
def Call.elim(t: Source.Term, h: {Term.is_call(t) == True{} : Bool}, -P: Source.Term -> Type,
  app: @q: Source.Quan -> @f: Source.Term -> @x: Source.Term -> P(Source.Term.App{q, f, x}),
  ref: @k: List<&2, Nat> -> P(Source.Term.Ref{k})) -> P(t):
  match t:
    case Source.Term.Var{z0}:
      Shared.Bool.absurd(P(Source.Term.Var{z0}), h)
    case Source.Term.Ref{z0}:
      ref(z0)
    case Source.Term.Ann{z0, z1}:
      Shared.Bool.absurd(P(Source.Term.Ann{z0, z1}), h)
    case Source.Term.Let{z0, z1, z2}:
      Shared.Bool.absurd(P(Source.Term.Let{z0, z1, z2}), h)
    case Source.Term.Typ{z0}:
      Shared.Bool.absurd(P(Source.Term.Typ{z0}), h)
    case Source.Term.Min{z0, z1}:
      Shared.Bool.absurd(P(Source.Term.Min{z0, z1}), h)
    case Source.Term.All{z0, z1, z2}:
      Shared.Bool.absurd(P(Source.Term.All{z0, z1, z2}), h)
    case Source.Term.Lam{z0, z1}:
      Shared.Bool.absurd(P(Source.Term.Lam{z0, z1}), h)
    case Source.Term.App{z0, z1, z2}:
      app(z0, z1, z2)
    case Source.Term.Sig{z0, z1, z2}:
      Shared.Bool.absurd(P(Source.Term.Sig{z0, z1, z2}), h)
    case Source.Term.Tup{z0, z1, z2}:
      Shared.Bool.absurd(P(Source.Term.Tup{z0, z1, z2}), h)
    case Source.Term.Prj{z0}:
      Shared.Bool.absurd(P(Source.Term.Prj{z0}), h)
    case Source.Term.Enu{z0}:
      Shared.Bool.absurd(P(Source.Term.Enu{z0}), h)
    case Source.Term.Lab{z0}:
      Shared.Bool.absurd(P(Source.Term.Lab{z0}), h)
    case Source.Term.Mat{z0, z1, z2}:
      Shared.Bool.absurd(P(Source.Term.Mat{z0, z1, z2}), h)
    case Source.Term.Efq{}:
      Shared.Bool.absurd(P(Source.Term.Efq{}), h)
    case Source.Term.Eql{z0, z1, z2}:
      Shared.Bool.absurd(P(Source.Term.Eql{z0, z1, z2}), h)
    case Source.Term.Rfl{}:
      Shared.Bool.absurd(P(Source.Term.Rfl{}), h)
    case Source.Term.Rwt{z0, z1, z2}:
      Shared.Bool.absurd(P(Source.Term.Rwt{z0, z1, z2}), h)

# Variables
# =========

def Val.no_var(v: Machine.Val) -> Bool:
  match v:
    case Machine.Val.clo{Source.Term.Var{i}, e}:
      False{}
    case _:
      True{}

# what Env.find gives: a value that is not a closure of a variable
def Look.ok(l: Machine.Look, +bk: List<&2, Source.Def>) -> Bool:
  match l:
    case Machine.Look.val{+v}:
      Val.no_var(v) && Val.ok(v, Mode.any{}, bk)
    case Machine.Look.free{j}:
      True{}

def Find.res(e: Machine.Val, i: Nat, +bk: List<&2, Source.Def>) -> Type:
  {Look.ok(Machine.Env.find(e, i), bk) == True{} : Bool} &
    {Look.rb(Machine.Env.find(e, i)) == Source.Env.sub(Env.rb(e), i) : Source.Term}

def Find.chain(+j: Nat, +e2: Machine.Val, -rest: Machine.Val, +bk: List<&2, Source.Def>, r: Find.res(e2, j, bk)) ->
  Find.res(Machine.Val.env{Machine.Val.clo{Source.Term.Var{j}, e2}, rest}, 0n, bk):
  match r:
    case (ok, eq):
      (ok, Equal.trans(Source.Term, Look.rb(Machine.Env.find(e2, j)), Source.Env.sub(Env.rb(e2), j),
        Source.Term.sub(Source.Term.Var{j}, 0n, Source.Sub.env{Env.rb(e2)}), eq,
        Equal.sym(Source.Term, Source.Term.sub(Source.Term.Var{j}, 0n, Source.Sub.env{Env.rb(e2)}),
          Source.Env.sub(Env.rb(e2), j), Term.sub_var(j, Env.rb(e2)))))

# Env.find reads the term of the environment's variable i
def Find.ok(e: Machine.Val, +i: Nat, +bk: List<&2, Source.Def>, h: {Val.ok(e, Mode.env{}, bk) == True{} : Bool}) ->
  Find.res(e, i, bk):
  match e:
    case Machine.Val.nil{}:
      ({==}, {==})
    case Machine.Val.env{+v0, +v1}:
      match v0:
        case Machine.Val.nil{}:
          Shared.Bool.absurd(Find.res(Machine.Val.env{Machine.Val.nil{}, v1}, i, bk), h)
        case Machine.Val.env{+u0, +u1}:
          Shared.Bool.absurd(Find.res(Machine.Val.env{Machine.Val.env{u0, u1}, v1}, i, bk), h)
        case Machine.Val.arg{+u0, +u1, +u2}:
          Shared.Bool.absurd(Find.res(Machine.Val.env{Machine.Val.arg{u0, u1, u2}, v1}, i, bk), h)
        case Machine.Val.clo{+u0, +u1}:
          match u0:
            case Source.Term.Var{+z0}:
              match i:
                case 0n:
                  Find.chain(z0, u1, v1, bk, Find.ok(u1, z0, bk, SP.Bool.and_left(Val.ok(u1, Mode.env{}, bk), Val.ok(v1, Mode.env{}, bk), h)))
                case 1n+j:
                  Find.ok(v1, j, bk, SP.Bool.and_right(Val.ok(Machine.Val.clo{u0, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h))
            case Source.Term.Ref{+z0}:
              match i:
                case 0n:
                  (SP.Bool.and_left(Val.ok(Machine.Val.clo{Source.Term.Ref{z0}, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h), {==})
                case 1n+j:
                  Find.ok(v1, j, bk, SP.Bool.and_right(Val.ok(Machine.Val.clo{u0, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h))
            case Source.Term.Ann{+z0, +z1}:
              match i:
                case 0n:
                  (SP.Bool.and_left(Val.ok(Machine.Val.clo{Source.Term.Ann{z0, z1}, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h), {==})
                case 1n+j:
                  Find.ok(v1, j, bk, SP.Bool.and_right(Val.ok(Machine.Val.clo{u0, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h))
            case Source.Term.Let{+z0, +z1, +z2}:
              match i:
                case 0n:
                  (SP.Bool.and_left(Val.ok(Machine.Val.clo{Source.Term.Let{z0, z1, z2}, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h), {==})
                case 1n+j:
                  Find.ok(v1, j, bk, SP.Bool.and_right(Val.ok(Machine.Val.clo{u0, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h))
            case Source.Term.Typ{+z0}:
              match i:
                case 0n:
                  (SP.Bool.and_left(Val.ok(Machine.Val.clo{Source.Term.Typ{z0}, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h), {==})
                case 1n+j:
                  Find.ok(v1, j, bk, SP.Bool.and_right(Val.ok(Machine.Val.clo{u0, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h))
            case Source.Term.Min{+z0, +z1}:
              match i:
                case 0n:
                  (SP.Bool.and_left(Val.ok(Machine.Val.clo{Source.Term.Min{z0, z1}, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h), {==})
                case 1n+j:
                  Find.ok(v1, j, bk, SP.Bool.and_right(Val.ok(Machine.Val.clo{u0, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h))
            case Source.Term.All{+z0, +z1, +z2}:
              match i:
                case 0n:
                  (SP.Bool.and_left(Val.ok(Machine.Val.clo{Source.Term.All{z0, z1, z2}, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h), {==})
                case 1n+j:
                  Find.ok(v1, j, bk, SP.Bool.and_right(Val.ok(Machine.Val.clo{u0, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h))
            case Source.Term.Lam{+z0, +z1}:
              match i:
                case 0n:
                  (SP.Bool.and_left(Val.ok(Machine.Val.clo{Source.Term.Lam{z0, z1}, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h), {==})
                case 1n+j:
                  Find.ok(v1, j, bk, SP.Bool.and_right(Val.ok(Machine.Val.clo{u0, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h))
            case Source.Term.App{+z0, +z1, +z2}:
              match i:
                case 0n:
                  (SP.Bool.and_left(Val.ok(Machine.Val.clo{Source.Term.App{z0, z1, z2}, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h), {==})
                case 1n+j:
                  Find.ok(v1, j, bk, SP.Bool.and_right(Val.ok(Machine.Val.clo{u0, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h))
            case Source.Term.Sig{+z0, +z1, +z2}:
              match i:
                case 0n:
                  (SP.Bool.and_left(Val.ok(Machine.Val.clo{Source.Term.Sig{z0, z1, z2}, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h), {==})
                case 1n+j:
                  Find.ok(v1, j, bk, SP.Bool.and_right(Val.ok(Machine.Val.clo{u0, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h))
            case Source.Term.Tup{+z0, +z1, +z2}:
              match i:
                case 0n:
                  (SP.Bool.and_left(Val.ok(Machine.Val.clo{Source.Term.Tup{z0, z1, z2}, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h), {==})
                case 1n+j:
                  Find.ok(v1, j, bk, SP.Bool.and_right(Val.ok(Machine.Val.clo{u0, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h))
            case Source.Term.Prj{+z0}:
              match i:
                case 0n:
                  (SP.Bool.and_left(Val.ok(Machine.Val.clo{Source.Term.Prj{z0}, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h), {==})
                case 1n+j:
                  Find.ok(v1, j, bk, SP.Bool.and_right(Val.ok(Machine.Val.clo{u0, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h))
            case Source.Term.Enu{+z0}:
              match i:
                case 0n:
                  (SP.Bool.and_left(Val.ok(Machine.Val.clo{Source.Term.Enu{z0}, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h), {==})
                case 1n+j:
                  Find.ok(v1, j, bk, SP.Bool.and_right(Val.ok(Machine.Val.clo{u0, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h))
            case Source.Term.Lab{+z0}:
              match i:
                case 0n:
                  (SP.Bool.and_left(Val.ok(Machine.Val.clo{Source.Term.Lab{z0}, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h), {==})
                case 1n+j:
                  Find.ok(v1, j, bk, SP.Bool.and_right(Val.ok(Machine.Val.clo{u0, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h))
            case Source.Term.Mat{+z0, +z1, +z2}:
              match i:
                case 0n:
                  (SP.Bool.and_left(Val.ok(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h), {==})
                case 1n+j:
                  Find.ok(v1, j, bk, SP.Bool.and_right(Val.ok(Machine.Val.clo{u0, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h))
            case Source.Term.Efq{}:
              match i:
                case 0n:
                  (SP.Bool.and_left(Val.ok(Machine.Val.clo{Source.Term.Efq{}, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h), {==})
                case 1n+j:
                  Find.ok(v1, j, bk, SP.Bool.and_right(Val.ok(Machine.Val.clo{u0, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h))
            case Source.Term.Eql{+z0, +z1, +z2}:
              match i:
                case 0n:
                  (SP.Bool.and_left(Val.ok(Machine.Val.clo{Source.Term.Eql{z0, z1, z2}, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h), {==})
                case 1n+j:
                  Find.ok(v1, j, bk, SP.Bool.and_right(Val.ok(Machine.Val.clo{u0, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h))
            case Source.Term.Rfl{}:
              match i:
                case 0n:
                  (SP.Bool.and_left(Val.ok(Machine.Val.clo{Source.Term.Rfl{}, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h), {==})
                case 1n+j:
                  Find.ok(v1, j, bk, SP.Bool.and_right(Val.ok(Machine.Val.clo{u0, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h))
            case Source.Term.Rwt{+z0, +z1, +z2}:
              match i:
                case 0n:
                  (SP.Bool.and_left(Val.ok(Machine.Val.clo{Source.Term.Rwt{z0, z1, z2}, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h), {==})
                case 1n+j:
                  Find.ok(v1, j, bk, SP.Bool.and_right(Val.ok(Machine.Val.clo{u0, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h))
        case Machine.Val.lab{+u0}:
          match i:
            case 0n:
              (SP.Bool.and_left(Val.ok(Machine.Val.lab{u0}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h), {==})
            case 1n+j:
              Find.ok(v1, j, bk, SP.Bool.and_right(Val.ok(Machine.Val.lab{u0}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h))
        case Machine.Val.rfl{}:
          match i:
            case 0n:
              (SP.Bool.and_left(Val.ok(Machine.Val.rfl{}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h), {==})
            case 1n+j:
              Find.ok(v1, j, bk, SP.Bool.and_right(Val.ok(Machine.Val.rfl{}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h))
        case Machine.Val.tup{+u0, +u1, +u2}:
          match i:
            case 0n:
              (SP.Bool.and_left(Val.ok(Machine.Val.tup{u0, u1, u2}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h), {==})
            case 1n+j:
              Find.ok(v1, j, bk, SP.Bool.and_right(Val.ok(Machine.Val.tup{u0, u1, u2}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h))
        case Machine.Val.call{+u0, +u1}:
          match i:
            case 0n:
              (SP.Bool.and_left(Val.ok(Machine.Val.call{u0, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h), {==})
            case 1n+j:
              Find.ok(v1, j, bk, SP.Bool.and_right(Val.ok(Machine.Val.call{u0, u1}, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h))
    case Machine.Val.arg{+v0, +v1, +v2}:
      Shared.Bool.absurd(Find.res(Machine.Val.arg{v0, v1, v2}, i, bk), h)
    case Machine.Val.clo{+v0, +v1}:
      Shared.Bool.absurd(Find.res(Machine.Val.clo{v0, v1}, i, bk), h)
    case Machine.Val.lab{+v0}:
      Shared.Bool.absurd(Find.res(Machine.Val.lab{v0}, i, bk), h)
    case Machine.Val.rfl{}:
      Shared.Bool.absurd(Find.res(Machine.Val.rfl{}, i, bk), h)
    case Machine.Val.tup{+v0, +v1, +v2}:
      Shared.Bool.absurd(Find.res(Machine.Val.tup{v0, v1, v2}, i, bk), h)
    case Machine.Val.call{+v0, +v1}:
      Shared.Bool.absurd(Find.res(Machine.Val.call{v0, v1}, i, bk), h)

def Get.res(e: Machine.Val, i: Nat, +bk: List<&2, Source.Def>) -> Type:
  {Val.ok(Machine.Env.get(e, i), Mode.any{}, bk) == True{} : Bool} &
    {Val.rb(Machine.Env.get(e, i)) == Source.Env.sub(Env.rb(e), i) : Source.Term}

# Env.get reads the term of the environment's variable i
def Get.ok(e: Machine.Val, +i: Nat, +bk: List<&2, Source.Def>, h: {Val.ok(e, Mode.env{}, bk) == True{} : Bool}) ->
  Get.res(e, i, bk):
  match e:
    case Machine.Val.nil{}:
      ({==}, Term.sub_var(i, []))
    case Machine.Val.env{+v0, +v1}:
      match i:
        case 0n:
          (SP.Bool.and_left(Val.ok(v0, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h), {==})
        case 1n+j:
          Get.ok(v1, j, bk, SP.Bool.and_right(Val.ok(v0, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h))
    case Machine.Val.arg{+v0, +v1, +v2}:
      Shared.Bool.absurd(Get.res(Machine.Val.arg{v0, v1, v2}, i, bk), h)
    case Machine.Val.clo{+v0, +v1}:
      Shared.Bool.absurd(Get.res(Machine.Val.clo{v0, v1}, i, bk), h)
    case Machine.Val.lab{+v0}:
      Shared.Bool.absurd(Get.res(Machine.Val.lab{v0}, i, bk), h)
    case Machine.Val.rfl{}:
      Shared.Bool.absurd(Get.res(Machine.Val.rfl{}, i, bk), h)
    case Machine.Val.tup{+v0, +v1, +v2}:
      Shared.Bool.absurd(Get.res(Machine.Val.tup{v0, v1, v2}, i, bk), h)
    case Machine.Val.call{+v0, +v1}:
      Shared.Bool.absurd(Get.res(Machine.Val.call{v0, v1}, i, bk), h)

# Modes
# =====

# a good value is any value
def Good.any(v: Machine.Val, +bk: List<&2, Source.Def>, h: {Val.ok(v, Mode.good{}, bk) == True{} : Bool}) ->
  {Val.ok(v, Mode.any{}, bk) == True{} : Bool}:
  match v:
    case Machine.Val.nil{}:
      h
    case Machine.Val.env{+v0, +v1}:
      h
    case Machine.Val.arg{+v0, +v1, +v2}:
      h
    case Machine.Val.clo{+v0, +v1}:
      SP.Bool.and_right(Term.is_fun(v0), Val.ok(v1, Mode.env{}, bk), h)
    case Machine.Val.lab{+v0}:
      h
    case Machine.Val.rfl{}:
      h
    case Machine.Val.tup{+v0, +v1, +v2}:
      h
    case Machine.Val.call{+v0, +v1}:
      h

def Field.any(q: Source.Quan, v: Machine.Val, +bk: List<&2, Source.Def>,
  h: {Val.ok(v, Mode.field(q), bk) == True{} : Bool}) -> {Val.ok(v, Mode.any{}, bk) == True{} : Bool}:
  match q:
    case Source.Q0{}:
      h
    case Source.Q1{}:
      Good.any(v, bk, h)
    case Source.Q2{}:
      Good.any(v, bk, h)

# a good value at the mode of a field
def Good.field(q: Source.Quan, v: Machine.Val, +bk: List<&2, Source.Def>, h: {Val.ok(v, Mode.good{}, bk) == True{} : Bool}) ->
  {Val.ok(v, Mode.field(q), bk) == True{} : Bool}:
  match q:
    case Source.Q0{}:
      Good.any(v, bk, h)
    case Source.Q1{}:
      h
    case Source.Q2{}:
      h

# Data
# ====

def Mode.data(c: Bool) -> Mode:
  match c:
    case True{}:
      Mode.env{}
    case False{}:
      Mode.any{}

def Data.rb(e: Machine.Val, t: Source.Term, c: Bool) -> Source.Term:
  match c:
    case True{}:
      Clo.rb(t, e)
    case False{}:
      Val.rb(e)

def Data.tup(q: Source.Quan, -a1: Bool, a2: Bool, -b1: Bool, b2: Bool, ea: {a1 == a2 : Bool}, eb: {b1 == b2 : Bool}) ->
  {Bool.and(Bool.or(Bool.not(Source.Quan.live(q)), a1), b1) == Bool.and(Bool.or(Bool.not(Source.Quan.live(q)), a2), b2) : Bool}:
  %ea : {Bool.and(Bool.or(Bool.not(Source.Quan.live(q)), a1), b1) == Bool.and(Bool.or(Bool.not(Source.Quan.live(q)), _), b2) : Bool}
  %eb : {Bool.and(Bool.or(Bool.not(Source.Quan.live(q)), a1), b1) == Bool.and(Bool.or(Bool.not(Source.Quan.live(q)), a1), _) : Bool}
  {==}

def Data.var(-x: Source.Term, +L: List<&2, Source.Term>, +i: Nat, -b: Bool,
  ex: {b == Source.Term.is_data(Source.Env.sub(L, i)) : Bool}) ->
  {b == Source.Term.is_data(Source.Term.sub(Source.Term.Var{i}, 0n, Source.Sub.env{L})) : Bool}:
  %Equal.sym(Source.Term, Source.Term.sub(Source.Term.Var{i}, 0n, Source.Sub.env{L}), Source.Env.sub(L, i), Term.sub_var(i, L)) :
    {b == Source.Term.is_data(_) : Bool}
  ex

# Val.data.go is Source.Term.is_data of the term
def Data.eq(e: Machine.Val, +t: Source.Term, +c: Bool, +bk: List<&2, Source.Def>, +h: {Val.ok(e, Mode.data(c), bk) == True{} : Bool}) ->
  {Machine.Val.data.go(e, t, c) == Source.Term.is_data(Data.rb(e, t, c)) : Bool}:
  match e:
    case Machine.Val.nil{}:
      match t:
        case Source.Term.Var{+z0}:
          match c:
            case True{}:
              Data.var(Source.Term.Var{z0}, [], z0, False{}, {==})
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.nil{}, Source.Term.Var{z0}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.nil{})) : Bool}, h)
        case Source.Term.Ref{+z0}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.nil{}, Source.Term.Ref{z0}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.nil{})) : Bool}, h)
        case Source.Term.Ann{+z0, +z1}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.nil{}, Source.Term.Ann{z0, z1}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.nil{})) : Bool}, h)
        case Source.Term.Let{+z0, +z1, +z2}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.nil{}, Source.Term.Let{z0, z1, z2}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.nil{})) : Bool}, h)
        case Source.Term.Typ{+z0}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.nil{}, Source.Term.Typ{z0}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.nil{})) : Bool}, h)
        case Source.Term.Min{+z0, +z1}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.nil{}, Source.Term.Min{z0, z1}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.nil{})) : Bool}, h)
        case Source.Term.All{+z0, +z1, +z2}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.nil{}, Source.Term.All{z0, z1, z2}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.nil{})) : Bool}, h)
        case Source.Term.Lam{+z0, +z1}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.nil{}, Source.Term.Lam{z0, z1}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.nil{})) : Bool}, h)
        case Source.Term.App{+z0, +z1, +z2}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.nil{}, Source.Term.App{z0, z1, z2}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.nil{})) : Bool}, h)
        case Source.Term.Sig{+z0, +z1, +z2}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.nil{}, Source.Term.Sig{z0, z1, z2}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.nil{})) : Bool}, h)
        case Source.Term.Tup{+z0, +z1, +z2}:
          match c:
            case True{}:
              Data.tup(z0, Machine.Val.data.go(Machine.Val.nil{}, z1, True{}), Source.Term.is_data(Clo.rb(z1, Machine.Val.nil{})),
                Machine.Val.data.go(Machine.Val.nil{}, z2, True{}), Source.Term.is_data(Clo.rb(z2, Machine.Val.nil{})),
                Data.eq(Machine.Val.nil{}, z1, True{}, bk, h), Data.eq(Machine.Val.nil{}, z2, True{}, bk, h))
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.nil{}, Source.Term.Tup{z0, z1, z2}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.nil{})) : Bool}, h)
        case Source.Term.Prj{+z0}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.nil{}, Source.Term.Prj{z0}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.nil{})) : Bool}, h)
        case Source.Term.Enu{+z0}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.nil{}, Source.Term.Enu{z0}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.nil{})) : Bool}, h)
        case Source.Term.Lab{+z0}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.nil{}, Source.Term.Lab{z0}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.nil{})) : Bool}, h)
        case Source.Term.Mat{+z0, +z1, +z2}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.nil{}, Source.Term.Mat{z0, z1, z2}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.nil{})) : Bool}, h)
        case Source.Term.Efq{}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.nil{}, Source.Term.Efq{}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.nil{})) : Bool}, h)
        case Source.Term.Eql{+z0, +z1, +z2}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.nil{}, Source.Term.Eql{z0, z1, z2}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.nil{})) : Bool}, h)
        case Source.Term.Rfl{}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.nil{}, Source.Term.Rfl{}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.nil{})) : Bool}, h)
        case Source.Term.Rwt{+z0, +z1, +z2}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.nil{}, Source.Term.Rwt{z0, z1, z2}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.nil{})) : Bool}, h)
    case Machine.Val.env{+v0, +v1}:
      match t:
        case Source.Term.Var{+z0}:
          match z0:
            case 0n:
              match c:
                case True{}:
                  Data.var(Source.Term.Var{0n}, Env.rb(Machine.Val.env{v0, v1}), 0n, Machine.Val.data.go(v0, Source.Term.Efq{}, False{}),
                    Data.eq(v0, Source.Term.Efq{}, False{}, bk, SP.Bool.and_left(Val.ok(v0, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h)))
                case False{}:
                  Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.env{v0, v1}, Source.Term.Var{0n}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.env{v0, v1})) : Bool}, h)
            case 1n+j:
              match c:
                case True{}:
                  Data.var(Source.Term.Var{1n+j}, Env.rb(Machine.Val.env{v0, v1}), 1n+j, Machine.Val.data.go(v1, Source.Term.Var{j}, True{}),
                    Equal.trans(Bool, Machine.Val.data.go(v1, Source.Term.Var{j}, True{}), Source.Term.is_data(Source.Term.sub(Source.Term.Var{j}, 0n, Source.Sub.env{Env.rb(v1)})),
                      Source.Term.is_data(Source.Env.sub(Env.rb(v1), j)),
                      Data.eq(v1, Source.Term.Var{j}, True{}, bk, SP.Bool.and_right(Val.ok(v0, Mode.any{}, bk), Val.ok(v1, Mode.env{}, bk), h)),
                      Equal.cong(Source.Term, Bool, z => Source.Term.is_data(z), Source.Term.sub(Source.Term.Var{j}, 0n, Source.Sub.env{Env.rb(v1)}),
                        Source.Env.sub(Env.rb(v1), j), Term.sub_var(j, Env.rb(v1)))))
                case False{}:
                  Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.env{v0, v1}, Source.Term.Var{1n+j}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.env{v0, v1})) : Bool}, h)
        case Source.Term.Ref{+z0}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.env{v0, v1}, Source.Term.Ref{z0}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.env{v0, v1})) : Bool}, h)
        case Source.Term.Ann{+z0, +z1}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.env{v0, v1}, Source.Term.Ann{z0, z1}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.env{v0, v1})) : Bool}, h)
        case Source.Term.Let{+z0, +z1, +z2}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.env{v0, v1}, Source.Term.Let{z0, z1, z2}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.env{v0, v1})) : Bool}, h)
        case Source.Term.Typ{+z0}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.env{v0, v1}, Source.Term.Typ{z0}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.env{v0, v1})) : Bool}, h)
        case Source.Term.Min{+z0, +z1}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.env{v0, v1}, Source.Term.Min{z0, z1}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.env{v0, v1})) : Bool}, h)
        case Source.Term.All{+z0, +z1, +z2}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.env{v0, v1}, Source.Term.All{z0, z1, z2}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.env{v0, v1})) : Bool}, h)
        case Source.Term.Lam{+z0, +z1}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.env{v0, v1}, Source.Term.Lam{z0, z1}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.env{v0, v1})) : Bool}, h)
        case Source.Term.App{+z0, +z1, +z2}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.env{v0, v1}, Source.Term.App{z0, z1, z2}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.env{v0, v1})) : Bool}, h)
        case Source.Term.Sig{+z0, +z1, +z2}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.env{v0, v1}, Source.Term.Sig{z0, z1, z2}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.env{v0, v1})) : Bool}, h)
        case Source.Term.Tup{+z0, +z1, +z2}:
          match c:
            case True{}:
              Data.tup(z0, Machine.Val.data.go(Machine.Val.env{v0, v1}, z1, True{}), Source.Term.is_data(Clo.rb(z1, Machine.Val.env{v0, v1})),
                Machine.Val.data.go(Machine.Val.env{v0, v1}, z2, True{}), Source.Term.is_data(Clo.rb(z2, Machine.Val.env{v0, v1})),
                Data.eq(Machine.Val.env{v0, v1}, z1, True{}, bk, h), Data.eq(Machine.Val.env{v0, v1}, z2, True{}, bk, h))
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.env{v0, v1}, Source.Term.Tup{z0, z1, z2}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.env{v0, v1})) : Bool}, h)
        case Source.Term.Prj{+z0}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.env{v0, v1}, Source.Term.Prj{z0}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.env{v0, v1})) : Bool}, h)
        case Source.Term.Enu{+z0}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.env{v0, v1}, Source.Term.Enu{z0}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.env{v0, v1})) : Bool}, h)
        case Source.Term.Lab{+z0}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.env{v0, v1}, Source.Term.Lab{z0}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.env{v0, v1})) : Bool}, h)
        case Source.Term.Mat{+z0, +z1, +z2}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.env{v0, v1}, Source.Term.Mat{z0, z1, z2}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.env{v0, v1})) : Bool}, h)
        case Source.Term.Efq{}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.env{v0, v1}, Source.Term.Efq{}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.env{v0, v1})) : Bool}, h)
        case Source.Term.Eql{+z0, +z1, +z2}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.env{v0, v1}, Source.Term.Eql{z0, z1, z2}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.env{v0, v1})) : Bool}, h)
        case Source.Term.Rfl{}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.env{v0, v1}, Source.Term.Rfl{}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.env{v0, v1})) : Bool}, h)
        case Source.Term.Rwt{+z0, +z1, +z2}:
          match c:
            case True{}:
              {==}
            case False{}:
              Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.env{v0, v1}, Source.Term.Rwt{z0, z1, z2}, False{}) == Source.Term.is_data(Val.rb(Machine.Val.env{v0, v1})) : Bool}, h)
    case Machine.Val.arg{+v0, +v1, +v2}:
      match c:
        case True{}:
          Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.arg{v0, v1, v2}, t, True{}) == Source.Term.is_data(Clo.rb(t, Machine.Val.arg{v0, v1, v2})) : Bool}, h)
        case False{}:
          Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.arg{v0, v1, v2}, t, False{}) == Source.Term.is_data(Val.rb(Machine.Val.arg{v0, v1, v2})) : Bool}, h)
    case Machine.Val.clo{+v0, +v1}:
      match c:
        case True{}:
          Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.clo{v0, v1}, t, True{}) == Source.Term.is_data(Clo.rb(t, Machine.Val.clo{v0, v1})) : Bool}, h)
        case False{}:
          Data.eq(v1, v0, True{}, bk, h)
    case Machine.Val.lab{+v0}:
      match c:
        case True{}:
          Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.lab{v0}, t, True{}) == Source.Term.is_data(Clo.rb(t, Machine.Val.lab{v0})) : Bool}, h)
        case False{}:
          {==}
    case Machine.Val.rfl{}:
      match c:
        case True{}:
          Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.rfl{}, t, True{}) == Source.Term.is_data(Clo.rb(t, Machine.Val.rfl{})) : Bool}, h)
        case False{}:
          {==}
    case Machine.Val.tup{+v0, +v1, +v2}:
      match c:
        case True{}:
          Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.tup{v0, v1, v2}, t, True{}) == Source.Term.is_data(Clo.rb(t, Machine.Val.tup{v0, v1, v2})) : Bool}, h)
        case False{}:
          Data.tup(v0, Machine.Val.data.go(v1, t, False{}), Source.Term.is_data(Val.rb(v1)),
            Machine.Val.data.go(v2, t, False{}), Source.Term.is_data(Val.rb(v2)),
            Data.eq(v1, t, False{}, bk, Field.any(v0, v1, bk, SP.Bool.and_left(Val.ok(v1, Mode.field(v0), bk), Val.ok(v2, Mode.good{}, bk), h))), Data.eq(v2, t, False{}, bk, Good.any(v2, bk, SP.Bool.and_right(Val.ok(v1, Mode.field(v0), bk), Val.ok(v2, Mode.good{}, bk), h))))
    case Machine.Val.call{+v0, +v1}:
      match c:
        case True{}:
          Shared.Bool.absurd({Machine.Val.data.go(Machine.Val.call{v0, v1}, t, True{}) == Source.Term.is_data(Clo.rb(t, Machine.Val.call{v0, v1})) : Bool}, h)
        case False{}:
          Call.elim(Val.rb(Machine.Val.call{v0, v1}), Call.rb_is_call(v0, v1), z => {False{} == Source.Term.is_data(z) : Bool},
            q => f => x => {==}, n => {==})

# the data check of a value is Source.Term.is_data of its term
def Data.val(+x: Machine.Val, +bk: List<&2, Source.Def>, h: {Val.ok(x, Mode.any{}, bk) == True{} : Bool}) ->
  {Machine.Val.is_data(x) == Source.Term.is_data(Val.rb(x)) : Bool}:
  Data.eq(x, Source.Term.Efq{}, False{}, bk, h)

# Values
# ======

def Obs.dead_any(m: Maybe<&2, Source.Obs>, -a1: Maybe<&2, Source.Obs>, -a2: Maybe<&2, Source.Obs>) ->
  {Source.Obs.tup.of(m, False{}, a1) == Source.Obs.tup.of(m, False{}, a2) : Maybe<&2, Source.Obs>}:
  match m:
    case Some{y}:
      {==}
    case None{}:
      {==}

def Obs.dead_eq(+b1: Maybe<&2, Source.Obs>, -b2: Maybe<&2, Source.Obs>, -a1: Maybe<&2, Source.Obs>, -a2: Maybe<&2, Source.Obs>,
  eb: {b1 == b2 : Maybe<&2, Source.Obs>}) ->
  {Source.Obs.tup.of(b1, False{}, a1) == Source.Obs.tup.of(b2, False{}, a2) : Maybe<&2, Source.Obs>}:
  %eb : {Source.Obs.tup.of(b1, False{}, a1) == Source.Obs.tup.of(_, False{}, a2) : Maybe<&2, Source.Obs>}
  Obs.dead_any(b1, a1, a2)

def Obs.live_eq(-b1: Maybe<&2, Source.Obs>, b2: Maybe<&2, Source.Obs>, -a1: Maybe<&2, Source.Obs>, a2: Maybe<&2, Source.Obs>,
  eb: {b1 == b2 : Maybe<&2, Source.Obs>}, ea: {a1 == a2 : Maybe<&2, Source.Obs>}) ->
  {Source.Obs.tup.of(b1, True{}, a1) == Source.Obs.tup.of(b2, True{}, a2) : Maybe<&2, Source.Obs>}:
  %eb : {Source.Obs.tup.of(b1, True{}, a1) == Source.Obs.tup.of(_, True{}, a2) : Maybe<&2, Source.Obs>}
  %ea : {Source.Obs.tup.of(b1, True{}, a1) == Source.Obs.tup.of(b1, True{}, _) : Maybe<&2, Source.Obs>}
  {==}

# a good value shows what its term shows
def Obs.eq(v: Machine.Val, +bk: List<&2, Source.Def>, +h: {Val.ok(v, Mode.good{}, bk) == True{} : Bool}) ->
  {Machine.Val.observe(v) == Source.Term.observe(Val.rb(v)) : Maybe<&2, Source.Obs>}:
  match v:
    case Machine.Val.nil{}:
      Shared.Bool.absurd({Machine.Val.observe(Machine.Val.nil{}) == Source.Term.observe(Val.rb(Machine.Val.nil{})) : Maybe<&2, Source.Obs>}, h)
    case Machine.Val.env{+v0, +v1}:
      Shared.Bool.absurd({Machine.Val.observe(Machine.Val.env{v0, v1}) == Source.Term.observe(Val.rb(Machine.Val.env{v0, v1})) : Maybe<&2, Source.Obs>}, h)
    case Machine.Val.arg{+v0, +v1, +v2}:
      Shared.Bool.absurd({Machine.Val.observe(Machine.Val.arg{v0, v1, v2}) == Source.Term.observe(Val.rb(Machine.Val.arg{v0, v1, v2})) : Maybe<&2, Source.Obs>}, h)
    case Machine.Val.clo{+v0, +v1}:
      match v0:
        case Source.Term.Var{+z0}:
          Shared.Bool.absurd({Machine.Val.observe(Machine.Val.clo{Source.Term.Var{z0}, v1}) == Source.Term.observe(Val.rb(Machine.Val.clo{Source.Term.Var{z0}, v1})) : Maybe<&2, Source.Obs>}, SP.Bool.and_left(Term.is_fun(Source.Term.Var{z0}), Val.ok(v1, Mode.env{}, bk), h))
        case Source.Term.Ref{+z0}:
          Shared.Bool.absurd({Machine.Val.observe(Machine.Val.clo{Source.Term.Ref{z0}, v1}) == Source.Term.observe(Val.rb(Machine.Val.clo{Source.Term.Ref{z0}, v1})) : Maybe<&2, Source.Obs>}, SP.Bool.and_left(Term.is_fun(Source.Term.Ref{z0}), Val.ok(v1, Mode.env{}, bk), h))
        case Source.Term.Ann{+z0, +z1}:
          Shared.Bool.absurd({Machine.Val.observe(Machine.Val.clo{Source.Term.Ann{z0, z1}, v1}) == Source.Term.observe(Val.rb(Machine.Val.clo{Source.Term.Ann{z0, z1}, v1})) : Maybe<&2, Source.Obs>}, SP.Bool.and_left(Term.is_fun(Source.Term.Ann{z0, z1}), Val.ok(v1, Mode.env{}, bk), h))
        case Source.Term.Let{+z0, +z1, +z2}:
          Shared.Bool.absurd({Machine.Val.observe(Machine.Val.clo{Source.Term.Let{z0, z1, z2}, v1}) == Source.Term.observe(Val.rb(Machine.Val.clo{Source.Term.Let{z0, z1, z2}, v1})) : Maybe<&2, Source.Obs>}, SP.Bool.and_left(Term.is_fun(Source.Term.Let{z0, z1, z2}), Val.ok(v1, Mode.env{}, bk), h))
        case Source.Term.Typ{+z0}:
          {==}
        case Source.Term.Min{+z0, +z1}:
          Shared.Bool.absurd({Machine.Val.observe(Machine.Val.clo{Source.Term.Min{z0, z1}, v1}) == Source.Term.observe(Val.rb(Machine.Val.clo{Source.Term.Min{z0, z1}, v1})) : Maybe<&2, Source.Obs>}, SP.Bool.and_left(Term.is_fun(Source.Term.Min{z0, z1}), Val.ok(v1, Mode.env{}, bk), h))
        case Source.Term.All{+z0, +z1, +z2}:
          {==}
        case Source.Term.Lam{+z0, +z1}:
          {==}
        case Source.Term.App{+z0, +z1, +z2}:
          Shared.Bool.absurd({Machine.Val.observe(Machine.Val.clo{Source.Term.App{z0, z1, z2}, v1}) == Source.Term.observe(Val.rb(Machine.Val.clo{Source.Term.App{z0, z1, z2}, v1})) : Maybe<&2, Source.Obs>}, SP.Bool.and_left(Term.is_fun(Source.Term.App{z0, z1, z2}), Val.ok(v1, Mode.env{}, bk), h))
        case Source.Term.Sig{+z0, +z1, +z2}:
          {==}
        case Source.Term.Tup{+z0, +z1, +z2}:
          Shared.Bool.absurd({Machine.Val.observe(Machine.Val.clo{Source.Term.Tup{z0, z1, z2}, v1}) == Source.Term.observe(Val.rb(Machine.Val.clo{Source.Term.Tup{z0, z1, z2}, v1})) : Maybe<&2, Source.Obs>}, SP.Bool.and_left(Term.is_fun(Source.Term.Tup{z0, z1, z2}), Val.ok(v1, Mode.env{}, bk), h))
        case Source.Term.Prj{+z0}:
          {==}
        case Source.Term.Enu{+z0}:
          {==}
        case Source.Term.Lab{+z0}:
          Shared.Bool.absurd({Machine.Val.observe(Machine.Val.clo{Source.Term.Lab{z0}, v1}) == Source.Term.observe(Val.rb(Machine.Val.clo{Source.Term.Lab{z0}, v1})) : Maybe<&2, Source.Obs>}, SP.Bool.and_left(Term.is_fun(Source.Term.Lab{z0}), Val.ok(v1, Mode.env{}, bk), h))
        case Source.Term.Mat{+z0, +z1, +z2}:
          {==}
        case Source.Term.Efq{}:
          {==}
        case Source.Term.Eql{+z0, +z1, +z2}:
          {==}
        case Source.Term.Rfl{}:
          Shared.Bool.absurd({Machine.Val.observe(Machine.Val.clo{Source.Term.Rfl{}, v1}) == Source.Term.observe(Val.rb(Machine.Val.clo{Source.Term.Rfl{}, v1})) : Maybe<&2, Source.Obs>}, SP.Bool.and_left(Term.is_fun(Source.Term.Rfl{}), Val.ok(v1, Mode.env{}, bk), h))
        case Source.Term.Rwt{+z0, +z1, +z2}:
          Shared.Bool.absurd({Machine.Val.observe(Machine.Val.clo{Source.Term.Rwt{z0, z1, z2}, v1}) == Source.Term.observe(Val.rb(Machine.Val.clo{Source.Term.Rwt{z0, z1, z2}, v1})) : Maybe<&2, Source.Obs>}, SP.Bool.and_left(Term.is_fun(Source.Term.Rwt{z0, z1, z2}), Val.ok(v1, Mode.env{}, bk), h))
    case Machine.Val.lab{+v0}:
      {==}
    case Machine.Val.rfl{}:
      {==}
    case Machine.Val.tup{+v0, +v1, +v2}:
      match v0:
        case Source.Q0{}:
          Obs.dead_eq(Machine.Val.observe(v2), Source.Term.observe(Val.rb(v2)), Machine.Val.observe(v1),
            Source.Term.observe(Val.rb(v1)), Obs.eq(v2, bk, SP.Bool.and_right(Val.ok(v1, Mode.field(Source.Q0{}), bk), Val.ok(v2, Mode.good{}, bk), h)))
        case Source.Q1{}:
          Obs.live_eq(Machine.Val.observe(v2), Source.Term.observe(Val.rb(v2)), Machine.Val.observe(v1),
            Source.Term.observe(Val.rb(v1)), Obs.eq(v2, bk, SP.Bool.and_right(Val.ok(v1, Mode.field(Source.Q1{}), bk), Val.ok(v2, Mode.good{}, bk), h)), Obs.eq(v1, bk, SP.Bool.and_left(Val.ok(v1, Mode.field(Source.Q1{}), bk), Val.ok(v2, Mode.good{}, bk), h)))
        case Source.Q2{}:
          Obs.live_eq(Machine.Val.observe(v2), Source.Term.observe(Val.rb(v2)), Machine.Val.observe(v1),
            Source.Term.observe(Val.rb(v1)), Obs.eq(v2, bk, SP.Bool.and_right(Val.ok(v1, Mode.field(Source.Q2{}), bk), Val.ok(v2, Mode.good{}, bk), h)), Obs.eq(v1, bk, SP.Bool.and_left(Val.ok(v1, Mode.field(Source.Q2{}), bk), Val.ok(v2, Mode.good{}, bk), h)))
    case Machine.Val.call{+v0, +v1}:
      Call.elim(Val.rb(Machine.Val.call{v0, v1}), Call.rb_is_call(v0, v1), z => {None{} == Source.Term.observe(z) : Maybe<&2, Source.Obs>},
        q => f => x => {==}, n => {==})

# the term of a good value is a value
def Val.value(v: Machine.Val, +bk: List<&2, Source.Def>, +h: {Val.ok(v, Mode.good{}, bk) == True{} : Bool}) ->
  {Source.Term.is_value(Val.rb(v), False{}, bk) == True{} : Bool}:
  match v:
    case Machine.Val.nil{}:
      Shared.Bool.absurd({Source.Term.is_value(Val.rb(Machine.Val.nil{}), False{}, bk) == True{} : Bool}, h)
    case Machine.Val.env{+v0, +v1}:
      Shared.Bool.absurd({Source.Term.is_value(Val.rb(Machine.Val.env{v0, v1}), False{}, bk) == True{} : Bool}, h)
    case Machine.Val.arg{+v0, +v1, +v2}:
      Shared.Bool.absurd({Source.Term.is_value(Val.rb(Machine.Val.arg{v0, v1, v2}), False{}, bk) == True{} : Bool}, h)
    case Machine.Val.clo{+v0, +v1}:
      match v0:
        case Source.Term.Var{+z0}:
          Shared.Bool.absurd({Source.Term.is_value(Val.rb(Machine.Val.clo{Source.Term.Var{z0}, v1}), False{}, bk) == True{} : Bool}, SP.Bool.and_left(Term.is_fun(Source.Term.Var{z0}), Val.ok(v1, Mode.env{}, bk), h))
        case Source.Term.Ref{+z0}:
          Shared.Bool.absurd({Source.Term.is_value(Val.rb(Machine.Val.clo{Source.Term.Ref{z0}, v1}), False{}, bk) == True{} : Bool}, SP.Bool.and_left(Term.is_fun(Source.Term.Ref{z0}), Val.ok(v1, Mode.env{}, bk), h))
        case Source.Term.Ann{+z0, +z1}:
          Shared.Bool.absurd({Source.Term.is_value(Val.rb(Machine.Val.clo{Source.Term.Ann{z0, z1}, v1}), False{}, bk) == True{} : Bool}, SP.Bool.and_left(Term.is_fun(Source.Term.Ann{z0, z1}), Val.ok(v1, Mode.env{}, bk), h))
        case Source.Term.Let{+z0, +z1, +z2}:
          Shared.Bool.absurd({Source.Term.is_value(Val.rb(Machine.Val.clo{Source.Term.Let{z0, z1, z2}, v1}), False{}, bk) == True{} : Bool}, SP.Bool.and_left(Term.is_fun(Source.Term.Let{z0, z1, z2}), Val.ok(v1, Mode.env{}, bk), h))
        case Source.Term.Typ{+z0}:
          {==}
        case Source.Term.Min{+z0, +z1}:
          Shared.Bool.absurd({Source.Term.is_value(Val.rb(Machine.Val.clo{Source.Term.Min{z0, z1}, v1}), False{}, bk) == True{} : Bool}, SP.Bool.and_left(Term.is_fun(Source.Term.Min{z0, z1}), Val.ok(v1, Mode.env{}, bk), h))
        case Source.Term.All{+z0, +z1, +z2}:
          {==}
        case Source.Term.Lam{+z0, +z1}:
          {==}
        case Source.Term.App{+z0, +z1, +z2}:
          Shared.Bool.absurd({Source.Term.is_value(Val.rb(Machine.Val.clo{Source.Term.App{z0, z1, z2}, v1}), False{}, bk) == True{} : Bool}, SP.Bool.and_left(Term.is_fun(Source.Term.App{z0, z1, z2}), Val.ok(v1, Mode.env{}, bk), h))
        case Source.Term.Sig{+z0, +z1, +z2}:
          {==}
        case Source.Term.Tup{+z0, +z1, +z2}:
          Shared.Bool.absurd({Source.Term.is_value(Val.rb(Machine.Val.clo{Source.Term.Tup{z0, z1, z2}, v1}), False{}, bk) == True{} : Bool}, SP.Bool.and_left(Term.is_fun(Source.Term.Tup{z0, z1, z2}), Val.ok(v1, Mode.env{}, bk), h))
        case Source.Term.Prj{+z0}:
          {==}
        case Source.Term.Enu{+z0}:
          {==}
        case Source.Term.Lab{+z0}:
          Shared.Bool.absurd({Source.Term.is_value(Val.rb(Machine.Val.clo{Source.Term.Lab{z0}, v1}), False{}, bk) == True{} : Bool}, SP.Bool.and_left(Term.is_fun(Source.Term.Lab{z0}), Val.ok(v1, Mode.env{}, bk), h))
        case Source.Term.Mat{+z0, +z1, +z2}:
          {==}
        case Source.Term.Efq{}:
          {==}
        case Source.Term.Eql{+z0, +z1, +z2}:
          {==}
        case Source.Term.Rfl{}:
          Shared.Bool.absurd({Source.Term.is_value(Val.rb(Machine.Val.clo{Source.Term.Rfl{}, v1}), False{}, bk) == True{} : Bool}, SP.Bool.and_left(Term.is_fun(Source.Term.Rfl{}), Val.ok(v1, Mode.env{}, bk), h))
        case Source.Term.Rwt{+z0, +z1, +z2}:
          Shared.Bool.absurd({Source.Term.is_value(Val.rb(Machine.Val.clo{Source.Term.Rwt{z0, z1, z2}, v1}), False{}, bk) == True{} : Bool}, SP.Bool.and_left(Term.is_fun(Source.Term.Rwt{z0, z1, z2}), Val.ok(v1, Mode.env{}, bk), h))
    case Machine.Val.lab{+v0}:
      {==}
    case Machine.Val.rfl{}:
      {==}
    case Machine.Val.tup{+v0, +v1, +v2}:
      match v0:
        case Source.Q0{}:
          Val.value(v2, bk, SP.Bool.and_right(Val.ok(v1, Mode.any{}, bk), Val.ok(v2, Mode.good{}, bk), h))
        case Source.Q1{}:
          SP.Bool.and_intro(Source.Term.is_value(Val.rb(v1), False{}, bk), Source.Term.is_value(Val.rb(v2), False{}, bk),
            Val.value(v1, bk, SP.Bool.and_left(Val.ok(v1, Mode.good{}, bk), Val.ok(v2, Mode.good{}, bk), h)),
            Val.value(v2, bk, SP.Bool.and_right(Val.ok(v1, Mode.good{}, bk), Val.ok(v2, Mode.good{}, bk), h)))
        case Source.Q2{}:
          SP.Bool.and_intro(Source.Term.is_value(Val.rb(v1), False{}, bk), Source.Term.is_value(Val.rb(v2), False{}, bk),
            Val.value(v1, bk, SP.Bool.and_left(Val.ok(v1, Mode.good{}, bk), Val.ok(v2, Mode.good{}, bk), h)),
            Val.value(v2, bk, SP.Bool.and_right(Val.ok(v1, Mode.good{}, bk), Val.ok(v2, Mode.good{}, bk), h)))
    case Machine.Val.call{+v0, +v1}:
      SP.Bool.and_right(Val.ok(v1, Mode.args{}, bk), Source.Term.is_value(Val.rb(Machine.Val.call{v0, v1}), False{}, bk), h)

# Forms
# =====

# Source.Term.walk.prj on a term of the form f
def Form.prj(f: Machine.Form, +q: Source.Quan, R: List<&2, Source.Arg>, G: List<&2, Source.Arg> -> Source.Walk) ->
  Source.Walk:
  match f:
    case Machine.Form.tup{r, a, b}:
      Source.Bool.lazy(Source.Walk, Source.Quan.live(q),
        u => G(Con{Source.Arg{Source.Quan.fld(r, q), Val.rb(a)}, Con{Source.Arg{q, Val.rb(b)}, R}}),
        u => Source.Walk.fail{})
    case _:
      Source.Walk.fail{}

# Source.Term.walk.mat on a term of the form f
def Form.mat(f: Machine.Form, +q: Source.Quan, +k: List<&2, Nat>, +R: List<&2, Source.Arg>,
  H: List<&2, Source.Arg> -> Source.Walk, M: List<&2, Source.Arg> -> Source.Walk) -> Source.Walk:
  match f:
    case Machine.Form.lab{+j}:
      Source.Bool.lazy(Source.Walk, Source.Quan.live(q),
        u => Source.Bool.lazy(Source.Walk, Source.Name.is_eq(j, k),
          w => H(R),
          w => M(Con{Source.Arg{q, Source.Term.Lab{j}}, R})),
        u => Source.Walk.fail{})
    case _:
      Source.Walk.fail{}

# the pieces of a form
def Form.ok(f: Machine.Form, +bk: List<&2, Source.Def>) -> Bool:
  match f:
    case Machine.Form.tup{r, a, b}:
      Val.ok(a, Mode.any{}, bk) && Val.ok(b, Mode.any{}, bk)
    case _:
      True{}

def Form.prj_eq(l: Machine.Look, +q: Source.Quan, -R: List<&2, Source.Arg>, -G: List<&2, Source.Arg> -> Source.Walk, +bk: List<&2, Source.Def>,
  h: {Look.ok(l, bk) == True{} : Bool}) ->
  {Source.Term.walk.prj(Con{Source.Arg{q, Look.rb(l)}, R}, G) == Form.prj(Machine.Val.form.of(l), q, R, G) : Source.Walk}:
  match l:
    case Machine.Look.free{j}:
      {==}
    case Machine.Look.val{v}:
      match v:
        case Machine.Val.nil{}:
          Shared.Bool.absurd({Source.Term.walk.prj(Con{Source.Arg{q, Look.rb(Machine.Look.val{Machine.Val.nil{}})}, R}, G) == Form.prj(Machine.Val.form.of(Machine.Look.val{Machine.Val.nil{}}), q, R, G) : Source.Walk}, h)
        case Machine.Val.env{+v0, +v1}:
          Shared.Bool.absurd({Source.Term.walk.prj(Con{Source.Arg{q, Look.rb(Machine.Look.val{Machine.Val.env{v0, v1}})}, R}, G) == Form.prj(Machine.Val.form.of(Machine.Look.val{Machine.Val.env{v0, v1}}), q, R, G) : Source.Walk}, h)
        case Machine.Val.arg{+v0, +v1, +v2}:
          Shared.Bool.absurd({Source.Term.walk.prj(Con{Source.Arg{q, Look.rb(Machine.Look.val{Machine.Val.arg{v0, v1, v2}})}, R}, G) == Form.prj(Machine.Val.form.of(Machine.Look.val{Machine.Val.arg{v0, v1, v2}}), q, R, G) : Source.Walk}, h)
        case Machine.Val.clo{+v0, +v1}:
          match v0:
            case Source.Term.Var{+z0}:
              Shared.Bool.absurd({Source.Term.walk.prj(Con{Source.Arg{q, Look.rb(Machine.Look.val{Machine.Val.clo{Source.Term.Var{z0}, v1}})}, R}, G) == Form.prj(Machine.Val.form.of(Machine.Look.val{Machine.Val.clo{Source.Term.Var{z0}, v1}}), q, R, G) : Source.Walk}, h)
            case Source.Term.Ref{+z0}:
              {==}
            case Source.Term.Ann{+z0, +z1}:
              {==}
            case Source.Term.Let{+z0, +z1, +z2}:
              {==}
            case Source.Term.Typ{+z0}:
              {==}
            case Source.Term.Min{+z0, +z1}:
              {==}
            case Source.Term.All{+z0, +z1, +z2}:
              {==}
            case Source.Term.Lam{+z0, +z1}:
              {==}
            case Source.Term.App{+z0, +z1, +z2}:
              {==}
            case Source.Term.Sig{+z0, +z1, +z2}:
              {==}
            case Source.Term.Tup{+z0, +z1, +z2}:
              {==}
            case Source.Term.Prj{+z0}:
              {==}
            case Source.Term.Enu{+z0}:
              {==}
            case Source.Term.Lab{+z0}:
              {==}
            case Source.Term.Mat{+z0, +z1, +z2}:
              {==}
            case Source.Term.Efq{}:
              {==}
            case Source.Term.Eql{+z0, +z1, +z2}:
              {==}
            case Source.Term.Rfl{}:
              {==}
            case Source.Term.Rwt{+z0, +z1, +z2}:
              {==}
        case Machine.Val.lab{+v0}:
          {==}
        case Machine.Val.rfl{}:
          {==}
        case Machine.Val.tup{+v0, +v1, +v2}:
          {==}
        case Machine.Val.call{+v0, +v1}:
          Call.elim(Val.rb(Machine.Val.call{v0, v1}), Call.rb_is_call(v0, v1), z => {Source.Term.walk.prj(Con{Source.Arg{q, z}, R}, G) == Source.Walk.fail{} : Source.Walk},
            q2 => f => x => {==}, n => {==})

def Form.mat_eq(l: Machine.Look, +q: Source.Quan, +k: List<&2, Nat>, -R: List<&2, Source.Arg>, -H: List<&2, Source.Arg> -> Source.Walk,
  -M: List<&2, Source.Arg> -> Source.Walk, +bk: List<&2, Source.Def>, h: {Look.ok(l, bk) == True{} : Bool}) ->
  {Source.Term.walk.mat(k, Con{Source.Arg{q, Look.rb(l)}, R}, H, M) == Form.mat(Machine.Val.form.of(l), q, k, R, H, M) : Source.Walk}:
  match l:
    case Machine.Look.free{j}:
      {==}
    case Machine.Look.val{v}:
      match v:
        case Machine.Val.nil{}:
          Shared.Bool.absurd({Source.Term.walk.mat(k, Con{Source.Arg{q, Look.rb(Machine.Look.val{Machine.Val.nil{}})}, R}, H, M) == Form.mat(Machine.Val.form.of(Machine.Look.val{Machine.Val.nil{}}), q, k, R, H, M) : Source.Walk}, h)
        case Machine.Val.env{+v0, +v1}:
          Shared.Bool.absurd({Source.Term.walk.mat(k, Con{Source.Arg{q, Look.rb(Machine.Look.val{Machine.Val.env{v0, v1}})}, R}, H, M) == Form.mat(Machine.Val.form.of(Machine.Look.val{Machine.Val.env{v0, v1}}), q, k, R, H, M) : Source.Walk}, h)
        case Machine.Val.arg{+v0, +v1, +v2}:
          Shared.Bool.absurd({Source.Term.walk.mat(k, Con{Source.Arg{q, Look.rb(Machine.Look.val{Machine.Val.arg{v0, v1, v2}})}, R}, H, M) == Form.mat(Machine.Val.form.of(Machine.Look.val{Machine.Val.arg{v0, v1, v2}}), q, k, R, H, M) : Source.Walk}, h)
        case Machine.Val.clo{+v0, +v1}:
          match v0:
            case Source.Term.Var{+z0}:
              Shared.Bool.absurd({Source.Term.walk.mat(k, Con{Source.Arg{q, Look.rb(Machine.Look.val{Machine.Val.clo{Source.Term.Var{z0}, v1}})}, R}, H, M) == Form.mat(Machine.Val.form.of(Machine.Look.val{Machine.Val.clo{Source.Term.Var{z0}, v1}}), q, k, R, H, M) : Source.Walk}, h)
            case Source.Term.Ref{+z0}:
              {==}
            case Source.Term.Ann{+z0, +z1}:
              {==}
            case Source.Term.Let{+z0, +z1, +z2}:
              {==}
            case Source.Term.Typ{+z0}:
              {==}
            case Source.Term.Min{+z0, +z1}:
              {==}
            case Source.Term.All{+z0, +z1, +z2}:
              {==}
            case Source.Term.Lam{+z0, +z1}:
              {==}
            case Source.Term.App{+z0, +z1, +z2}:
              {==}
            case Source.Term.Sig{+z0, +z1, +z2}:
              {==}
            case Source.Term.Tup{+z0, +z1, +z2}:
              {==}
            case Source.Term.Prj{+z0}:
              {==}
            case Source.Term.Enu{+z0}:
              {==}
            case Source.Term.Lab{+z0}:
              {==}
            case Source.Term.Mat{+z0, +z1, +z2}:
              {==}
            case Source.Term.Efq{}:
              {==}
            case Source.Term.Eql{+z0, +z1, +z2}:
              {==}
            case Source.Term.Rfl{}:
              {==}
            case Source.Term.Rwt{+z0, +z1, +z2}:
              {==}
        case Machine.Val.lab{+v0}:
          {==}
        case Machine.Val.rfl{}:
          {==}
        case Machine.Val.tup{+v0, +v1, +v2}:
          {==}
        case Machine.Val.call{+v0, +v1}:
          Call.elim(Val.rb(Machine.Val.call{v0, v1}), Call.rb_is_call(v0, v1), z => {Source.Term.walk.mat(k, Con{Source.Arg{q, z}, R}, H, M) == Source.Walk.fail{} : Source.Walk},
            q2 => f => x => {==}, n => {==})

def Form.ok_of(l: Machine.Look, +bk: List<&2, Source.Def>, +h: {Look.ok(l, bk) == True{} : Bool}) ->
  {Form.ok(Machine.Val.form.of(l), bk) == True{} : Bool}:
  match l:
    case Machine.Look.free{j}:
      {==}
    case Machine.Look.val{v}:
      match v:
        case Machine.Val.nil{}:
          Shared.Bool.absurd({Form.ok(Machine.Val.form.of(Machine.Look.val{Machine.Val.nil{}}), bk) == True{} : Bool}, h)
        case Machine.Val.env{+v0, +v1}:
          Shared.Bool.absurd({Form.ok(Machine.Val.form.of(Machine.Look.val{Machine.Val.env{v0, v1}}), bk) == True{} : Bool}, h)
        case Machine.Val.arg{+v0, +v1, +v2}:
          Shared.Bool.absurd({Form.ok(Machine.Val.form.of(Machine.Look.val{Machine.Val.arg{v0, v1, v2}}), bk) == True{} : Bool}, h)
        case Machine.Val.clo{+v0, +v1}:
          match v0:
            case Source.Term.Var{+z0}:
              Shared.Bool.absurd({Form.ok(Machine.Val.form.of(Machine.Look.val{Machine.Val.clo{Source.Term.Var{z0}, v1}}), bk) == True{} : Bool}, h)
            case Source.Term.Ref{+z0}:
              {==}
            case Source.Term.Ann{+z0, +z1}:
              {==}
            case Source.Term.Let{+z0, +z1, +z2}:
              {==}
            case Source.Term.Typ{+z0}:
              {==}
            case Source.Term.Min{+z0, +z1}:
              {==}
            case Source.Term.All{+z0, +z1, +z2}:
              {==}
            case Source.Term.Lam{+z0, +z1}:
              {==}
            case Source.Term.App{+z0, +z1, +z2}:
              {==}
            case Source.Term.Sig{+z0, +z1, +z2}:
              {==}
            case Source.Term.Tup{+z0, +z1, +z2}:
              SP.Bool.and_intro(Val.ok(v1, Mode.env{}, bk), Val.ok(v1, Mode.env{}, bk), h, h)
            case Source.Term.Prj{+z0}:
              {==}
            case Source.Term.Enu{+z0}:
              {==}
            case Source.Term.Lab{+z0}:
              {==}
            case Source.Term.Mat{+z0, +z1, +z2}:
              {==}
            case Source.Term.Efq{}:
              {==}
            case Source.Term.Eql{+z0, +z1, +z2}:
              {==}
            case Source.Term.Rfl{}:
              {==}
            case Source.Term.Rwt{+z0, +z1, +z2}:
              {==}
        case Machine.Val.lab{+v0}:
          {==}
        case Machine.Val.rfl{}:
          {==}
        case Machine.Val.tup{+v0, +v1, +v2}:
          SP.Bool.and_intro(Val.ok(v1, Mode.any{}, bk), Val.ok(v2, Mode.any{}, bk),
            Field.any(v0, v1, bk, SP.Bool.and_left(Val.ok(v1, Mode.field(v0), bk), Val.ok(v2, Mode.good{}, bk), h)),
            Good.any(v2, bk, SP.Bool.and_right(Val.ok(v1, Mode.field(v0), bk), Val.ok(v2, Mode.good{}, bk), h)))
        case Machine.Val.call{+v0, +v1}:
          {==}

# what x stands for, through closures of variables
def Look.self(+x: Machine.Val, +bk: List<&2, Source.Def>, h: {Val.ok(x, Mode.any{}, bk) == True{} : Bool}) ->
  Find.res(Machine.Val.env{x, Machine.Val.nil{}}, 0n, bk):
  Find.ok(Machine.Val.env{x, Machine.Val.nil{}}, 0n, bk, SP.Bool.and_intro(Val.ok(x, Mode.any{}, bk), True{}, h, {==}))

# Walks
# =====

def Leaf.rb(w: Machine.Leaf) -> Source.Walk:
  match w:
    case Machine.Leaf.need{}:
      Source.Walk.need{}
    case Machine.Leaf.at{t, e, xs}:
      Source.Walk.done{Source.Term.spine(Args.rb(xs), Clo.rb(t, e))}
    case Machine.Leaf.fail{}:
      Source.Walk.fail{}

def Leaf.ok(w: Machine.Leaf, +bk: List<&2, Source.Def>) -> Bool:
  match w:
    case Machine.Leaf.at{t, e, xs}:
      Val.ok(e, Mode.env{}, bk) && Val.ok(xs, Mode.args{}, bk)
    case _:
      True{}

# the source's walk sw is the readback of the machine's walk mw, and mw is ok
def Walk.res(+bk: List<&2, Source.Def>, sw: Source.Walk, mw: Machine.Leaf) -> Type:
  {sw == Leaf.rb(mw) : Source.Walk} & {Leaf.ok(mw, bk) == True{} : Bool}

def Walk.lam_arg(+p: Source.Quan, +q: Source.Quan, +x: Machine.Val, +rest: Machine.Val, -f: Source.Term, +e: Machine.Val,
  +bk: List<&2, Source.Def>, hx: {Val.ok(x, Mode.any{}, bk) == True{} : Bool},
  go: Walk.res(bk, Source.Term.walk(f, Con{Val.rb(x), Env.rb(e)}, Args.rb(rest)), Machine.Walk.go(f, Machine.Val.env{x, e}, rest))) ->
  Walk.res(bk,
    Source.Bool.lazy(Source.Walk,
      Bool.and(Source.Bool.is_eq(Source.Quan.live(p), Source.Quan.live(q)), Bool.or(Bool.not(Source.Quan.is_q2(p)), Source.Term.is_data(Val.rb(x)))),
      u => Source.Term.walk(f, Con{Val.rb(x), Env.rb(e)}, Args.rb(rest)), u => Source.Walk.fail{}),
    Source.Bool.lazy(Machine.Leaf,
      Bool.and(Source.Bool.is_eq(Source.Quan.live(p), Source.Quan.live(q)), Bool.or(Bool.not(Source.Quan.is_q2(p)), Machine.Val.is_data(x))),
      u => Machine.Walk.go(f, Machine.Val.env{x, e}, rest), u => Machine.Leaf.fail{})):
  %Equal.sym(Bool, Machine.Val.is_data(x), Source.Term.is_data(Val.rb(x)), Data.val(x, bk, hx)) :
    Walk.res(bk,
      Source.Bool.lazy(Source.Walk,
        Bool.and(Source.Bool.is_eq(Source.Quan.live(p), Source.Quan.live(q)), Bool.or(Bool.not(Source.Quan.is_q2(p)), Source.Term.is_data(Val.rb(x)))),
        u => Source.Term.walk(f, Con{Val.rb(x), Env.rb(e)}, Args.rb(rest)), u => Source.Walk.fail{}),
      Source.Bool.lazy(Machine.Leaf,
        Bool.and(Source.Bool.is_eq(Source.Quan.live(p), Source.Quan.live(q)), Bool.or(Bool.not(Source.Quan.is_q2(p)), _)),
        u => Machine.Walk.go(f, Machine.Val.env{x, e}, rest), u => Machine.Leaf.fail{}))
  Shared.Bool.elim(
    Bool.and(Source.Bool.is_eq(Source.Quan.live(p), Source.Quan.live(q)), Bool.or(Bool.not(Source.Quan.is_q2(p)), Source.Term.is_data(Val.rb(x)))),
    c => Walk.res(bk,
      Source.Bool.lazy(Source.Walk, c, u => Source.Term.walk(f, Con{Val.rb(x), Env.rb(e)}, Args.rb(rest)), u => Source.Walk.fail{}),
      Source.Bool.lazy(Machine.Leaf, c, u => Machine.Walk.go(f, Machine.Val.env{x, e}, rest), u => Machine.Leaf.fail{})),
    go, ({==}, {==}))

def Walk.prj_f(f: Machine.Form, +q: Source.Quan, +rest: Machine.Val, -Gs: List<&2, Source.Arg> -> Source.Walk,
  -Gm: Machine.Val -> Machine.Leaf, +bk: List<&2, Source.Def>, +hf: {Form.ok(f, bk) == True{} : Bool},
  hr: {Val.ok(rest, Mode.args{}, bk) == True{} : Bool},
  ih: @ys: Machine.Val -> {Val.ok(ys, Mode.args{}, bk) == True{} : Bool} -> Walk.res(bk, Gs(Args.rb(ys)), Gm(ys))) ->
  Walk.res(bk, Form.prj(f, q, Args.rb(rest), Gs), Machine.Walk.prj.of(f, q, rest, Gm)):
  match f:
    case Machine.Form.tup{+r, +a, +b}:
      Shared.Bool.elim(Source.Quan.live(q),
        c => Walk.res(bk,
          Source.Bool.lazy(Source.Walk, c,
            u => Gs(Con{Source.Arg{Source.Quan.fld(r, q), Val.rb(a)}, Con{Source.Arg{q, Val.rb(b)}, Args.rb(rest)}}),
            u => Source.Walk.fail{}),
          Source.Bool.lazy(Machine.Leaf, c,
            u => Gm(Machine.Val.arg{Source.Quan.fld(r, q), a, Machine.Val.arg{q, b, rest}}),
            u => Machine.Leaf.fail{})),
        ih(Machine.Val.arg{Source.Quan.fld(r, q), a, Machine.Val.arg{q, b, rest}},
          SP.Bool.and_intro(Val.ok(a, Mode.any{}, bk), Bool.and(Val.ok(b, Mode.any{}, bk), Val.ok(rest, Mode.args{}, bk)),
            SP.Bool.and_left(Val.ok(a, Mode.any{}, bk), Val.ok(b, Mode.any{}, bk), hf),
            SP.Bool.and_intro(Val.ok(b, Mode.any{}, bk), Val.ok(rest, Mode.args{}, bk),
              SP.Bool.and_right(Val.ok(a, Mode.any{}, bk), Val.ok(b, Mode.any{}, bk), hf), hr))),
        ({==}, {==}))
    case Machine.Form.lab{k}:
      ({==}, {==})
    case Machine.Form.other{}:
      ({==}, {==})

def Walk.prj_x(+q: Source.Quan, +x: Machine.Val, +rest: Machine.Val, -h: Source.Term, -e: Machine.Val,
  +bk: List<&2, Source.Def>, lx: Find.res(Machine.Val.env{x, Machine.Val.nil{}}, 0n, bk),
  hr: {Val.ok(rest, Mode.args{}, bk) == True{} : Bool},
  ih: @ys: Machine.Val -> {Val.ok(ys, Mode.args{}, bk) == True{} : Bool} ->
    Walk.res(bk, Source.Term.walk(h, Env.rb(e), Args.rb(ys)), Machine.Walk.go(h, e, ys))) ->
  Walk.res(bk, Source.Term.walk.prj(Con{Source.Arg{q, Val.rb(x)}, Args.rb(rest)}, ys => Source.Term.walk(h, Env.rb(e), ys)),
    Machine.Walk.prj.of(Machine.Val.form(x), q, rest, ys => Machine.Walk.go(h, e, ys))):
  match lx:
    case (+okl, eql):
      %eql : Walk.res(bk, Source.Term.walk.prj(Con{Source.Arg{q, _}, Args.rb(rest)}, ys => Source.Term.walk(h, Env.rb(e), ys)),
        Machine.Walk.prj.of(Machine.Val.form(x), q, rest, ys => Machine.Walk.go(h, e, ys)))
      %Equal.sym(Source.Walk,
        Source.Term.walk.prj(Con{Source.Arg{q, Look.rb(Machine.Env.find(Machine.Val.env{x, Machine.Val.nil{}}, 0n))}, Args.rb(rest)},
          ys => Source.Term.walk(h, Env.rb(e), ys)),
        Form.prj(Machine.Val.form(x), q, Args.rb(rest), ys => Source.Term.walk(h, Env.rb(e), ys)),
        Form.prj_eq(Machine.Env.find(Machine.Val.env{x, Machine.Val.nil{}}, 0n), q, Args.rb(rest),
          ys => Source.Term.walk(h, Env.rb(e), ys), bk, okl)) :
        Walk.res(bk, _, Machine.Walk.prj.of(Machine.Val.form(x), q, rest, ys => Machine.Walk.go(h, e, ys)))
      Walk.prj_f(Machine.Val.form(x), q, rest, ys => Source.Term.walk(h, Env.rb(e), ys), ys => Machine.Walk.go(h, e, ys), bk,
        Form.ok_of(Machine.Env.find(Machine.Val.env{x, Machine.Val.nil{}}, 0n), bk, okl), hr, ih)

def Walk.mat_f(f: Machine.Form, +q: Source.Quan, +k: List<&2, Nat>, +rest: Machine.Val,
  -Hs: List<&2, Source.Arg> -> Source.Walk, -Ms: List<&2, Source.Arg> -> Source.Walk,
  -Hm: Machine.Val -> Machine.Leaf, -Mm: Machine.Val -> Machine.Leaf, +bk: List<&2, Source.Def>,
  +hr: {Val.ok(rest, Mode.args{}, bk) == True{} : Bool},
  ih: @ys: Machine.Val -> {Val.ok(ys, Mode.args{}, bk) == True{} : Bool} -> Walk.res(bk, Hs(Args.rb(ys)), Hm(ys)),
  im: @ys: Machine.Val -> {Val.ok(ys, Mode.args{}, bk) == True{} : Bool} -> Walk.res(bk, Ms(Args.rb(ys)), Mm(ys))) ->
  Walk.res(bk, Form.mat(f, q, k, Args.rb(rest), Hs, Ms), Machine.Walk.mat.of(f, q, k, rest, Hm, Mm)):
  match f:
    case Machine.Form.lab{+j}:
      Shared.Bool.elim(Source.Quan.live(q),
        c => Walk.res(bk,
          Source.Bool.lazy(Source.Walk, c,
            u => Source.Bool.lazy(Source.Walk, Source.Name.is_eq(j, k), z => Hs(Args.rb(rest)),
              z => Ms(Con{Source.Arg{q, Source.Term.Lab{j}}, Args.rb(rest)})),
            u => Source.Walk.fail{}),
          Source.Bool.lazy(Machine.Leaf, c,
            u => Source.Bool.lazy(Machine.Leaf, Source.Name.is_eq(j, k), z => Hm(rest),
              z => Mm(Machine.Val.arg{q, Machine.Val.lab{j}, rest})),
            u => Machine.Leaf.fail{})),
        Shared.Bool.elim(Source.Name.is_eq(j, k),
          c => Walk.res(bk,
            Source.Bool.lazy(Source.Walk, c, z => Hs(Args.rb(rest)), z => Ms(Con{Source.Arg{q, Source.Term.Lab{j}}, Args.rb(rest)})),
            Source.Bool.lazy(Machine.Leaf, c, z => Hm(rest), z => Mm(Machine.Val.arg{q, Machine.Val.lab{j}, rest}))),
          ih(rest, hr), im(Machine.Val.arg{q, Machine.Val.lab{j}, rest}, hr)),
        ({==}, {==}))
    case Machine.Form.tup{r, a, b}:
      ({==}, {==})
    case Machine.Form.other{}:
      ({==}, {==})

def Walk.mat_x(+q: Source.Quan, +k: List<&2, Nat>, +x: Machine.Val, +rest: Machine.Val, -h: Source.Term, -m: Source.Term,
  -e: Machine.Val, +bk: List<&2, Source.Def>, lx: Find.res(Machine.Val.env{x, Machine.Val.nil{}}, 0n, bk),
  hr: {Val.ok(rest, Mode.args{}, bk) == True{} : Bool},
  ih: @ys: Machine.Val -> {Val.ok(ys, Mode.args{}, bk) == True{} : Bool} ->
    Walk.res(bk, Source.Term.walk(h, Env.rb(e), Args.rb(ys)), Machine.Walk.go(h, e, ys)),
  im: @ys: Machine.Val -> {Val.ok(ys, Mode.args{}, bk) == True{} : Bool} ->
    Walk.res(bk, Source.Term.walk(m, Env.rb(e), Args.rb(ys)), Machine.Walk.go(m, e, ys))) ->
  Walk.res(bk, Source.Term.walk.mat(k, Con{Source.Arg{q, Val.rb(x)}, Args.rb(rest)}, ys => Source.Term.walk(h, Env.rb(e), ys),
      ys => Source.Term.walk(m, Env.rb(e), ys)),
    Machine.Walk.mat.of(Machine.Val.form(x), q, k, rest, ys => Machine.Walk.go(h, e, ys), ys => Machine.Walk.go(m, e, ys))):
  match lx:
    case (okl, eql):
      %eql : Walk.res(bk, Source.Term.walk.mat(k, Con{Source.Arg{q, _}, Args.rb(rest)}, ys => Source.Term.walk(h, Env.rb(e), ys),
          ys => Source.Term.walk(m, Env.rb(e), ys)),
        Machine.Walk.mat.of(Machine.Val.form(x), q, k, rest, ys => Machine.Walk.go(h, e, ys), ys => Machine.Walk.go(m, e, ys)))
      %Equal.sym(Source.Walk,
        Source.Term.walk.mat(k, Con{Source.Arg{q, Look.rb(Machine.Env.find(Machine.Val.env{x, Machine.Val.nil{}}, 0n))}, Args.rb(rest)},
          ys => Source.Term.walk(h, Env.rb(e), ys), ys => Source.Term.walk(m, Env.rb(e), ys)),
        Form.mat(Machine.Val.form(x), q, k, Args.rb(rest), ys => Source.Term.walk(h, Env.rb(e), ys), ys => Source.Term.walk(m, Env.rb(e), ys)),
        Form.mat_eq(Machine.Env.find(Machine.Val.env{x, Machine.Val.nil{}}, 0n), q, k, Args.rb(rest),
          ys => Source.Term.walk(h, Env.rb(e), ys), ys => Source.Term.walk(m, Env.rb(e), ys), bk, okl)) :
        Walk.res(bk, _, Machine.Walk.mat.of(Machine.Val.form(x), q, k, rest, ys => Machine.Walk.go(h, e, ys), ys => Machine.Walk.go(m, e, ys)))
      Walk.mat_f(Machine.Val.form(x), q, k, rest, ys => Source.Term.walk(h, Env.rb(e), ys), ys => Source.Term.walk(m, Env.rb(e), ys),
        ys => Machine.Walk.go(h, e, ys), ys => Machine.Walk.go(m, e, ys), bk, hr, ih, im)

def Walk.app_var(+q: Source.Quan, -f: Source.Term, +v: Nat, +e: Machine.Val, +xs: Machine.Val, +bk: List<&2, Source.Def>,
  g: Get.res(e, v, bk), hx: {Val.ok(xs, Mode.args{}, bk) == True{} : Bool},
  ih: {Val.ok(Machine.Val.arg{q, Machine.Env.get(e, v), xs}, Mode.args{}, bk) == True{} : Bool} ->
    Walk.res(bk, Source.Term.walk(f, Env.rb(e), Args.rb(Machine.Val.arg{q, Machine.Env.get(e, v), xs})),
      Machine.Walk.go(f, e, Machine.Val.arg{q, Machine.Env.get(e, v), xs}))) ->
  Walk.res(bk, Source.Term.walk(f, Env.rb(e), Con{Source.Arg{q, Source.Env.sub(Env.rb(e), v)}, Args.rb(xs)}),
    Machine.Walk.go(f, e, Machine.Val.arg{q, Machine.Env.get(e, v), xs})):
  match g:
    case (okg, eqg):
      %eqg : Walk.res(bk, Source.Term.walk(f, Env.rb(e), Con{Source.Arg{q, _}, Args.rb(xs)}),
        Machine.Walk.go(f, e, Machine.Val.arg{q, Machine.Env.get(e, v), xs}))
      ih(SP.Bool.and_intro(Val.ok(Machine.Env.get(e, v), Mode.any{}, bk), Val.ok(xs, Mode.args{}, bk), okg, hx))

# the machine's walk is the source's walk, read back
def Walk.eq(t: Source.Term, +e: Machine.Val, +xs: Machine.Val, +bk: List<&2, Source.Def>,
  +he: {Val.ok(e, Mode.env{}, bk) == True{} : Bool}, +hx: {Val.ok(xs, Mode.args{}, bk) == True{} : Bool}) ->
  Walk.res(bk, Source.Term.walk(t, Env.rb(e), Args.rb(xs)), Machine.Walk.go(t, e, xs)):
  match t:
    case Source.Term.Var{+z0}:
      ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
    case Source.Term.Ref{+z0}:
      ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
    case Source.Term.Ann{+z0, +z1}:
      ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
    case Source.Term.Let{+z0, +z1, +z2}:
      ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
    case Source.Term.Typ{+z0}:
      ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
    case Source.Term.Min{+z0, +z1}:
      ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
    case Source.Term.All{+z0, +z1, +z2}:
      ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
    case Source.Term.Lam{+z0, +z1}:
      match xs:
        case Machine.Val.nil{}:
          ({==}, {==})
        case Machine.Val.env{+y0, +y1}:
          Shared.Bool.absurd(Walk.res(bk, Source.Term.walk(Source.Term.Lam{z0, z1}, Env.rb(e), Args.rb(Machine.Val.env{y0, y1})), Machine.Walk.go(Source.Term.Lam{z0, z1}, e, Machine.Val.env{y0, y1})), hx)
        case Machine.Val.arg{+y0, +y1, +y2}:
          Walk.lam_arg(z0, y0, y1, y2, z1, e, bk, SP.Bool.and_left(Val.ok(y1, Mode.any{}, bk), Val.ok(y2, Mode.args{}, bk), hx),
            Walk.eq(z1, Machine.Val.env{y1, e}, y2, bk,
              SP.Bool.and_intro(Val.ok(y1, Mode.any{}, bk), Val.ok(e, Mode.env{}, bk), SP.Bool.and_left(Val.ok(y1, Mode.any{}, bk), Val.ok(y2, Mode.args{}, bk), hx), he), SP.Bool.and_right(Val.ok(y1, Mode.any{}, bk), Val.ok(y2, Mode.args{}, bk), hx)))
        case Machine.Val.clo{+y0, +y1}:
          Shared.Bool.absurd(Walk.res(bk, Source.Term.walk(Source.Term.Lam{z0, z1}, Env.rb(e), Args.rb(Machine.Val.clo{y0, y1})), Machine.Walk.go(Source.Term.Lam{z0, z1}, e, Machine.Val.clo{y0, y1})), hx)
        case Machine.Val.lab{+y0}:
          Shared.Bool.absurd(Walk.res(bk, Source.Term.walk(Source.Term.Lam{z0, z1}, Env.rb(e), Args.rb(Machine.Val.lab{y0})), Machine.Walk.go(Source.Term.Lam{z0, z1}, e, Machine.Val.lab{y0})), hx)
        case Machine.Val.rfl{}:
          Shared.Bool.absurd(Walk.res(bk, Source.Term.walk(Source.Term.Lam{z0, z1}, Env.rb(e), Args.rb(Machine.Val.rfl{})), Machine.Walk.go(Source.Term.Lam{z0, z1}, e, Machine.Val.rfl{})), hx)
        case Machine.Val.tup{+y0, +y1, +y2}:
          Shared.Bool.absurd(Walk.res(bk, Source.Term.walk(Source.Term.Lam{z0, z1}, Env.rb(e), Args.rb(Machine.Val.tup{y0, y1, y2})), Machine.Walk.go(Source.Term.Lam{z0, z1}, e, Machine.Val.tup{y0, y1, y2})), hx)
        case Machine.Val.call{+y0, +y1}:
          Shared.Bool.absurd(Walk.res(bk, Source.Term.walk(Source.Term.Lam{z0, z1}, Env.rb(e), Args.rb(Machine.Val.call{y0, y1})), Machine.Walk.go(Source.Term.Lam{z0, z1}, e, Machine.Val.call{y0, y1})), hx)
    case Source.Term.App{+z0, +z1, +z2}:
      match z2:
        case Source.Term.Var{+r0}:
          Shared.Bool.elim(Source.Spine.head.takes(Source.Term.unspine(z1, [])),
            c => Walk.res(bk,
              Source.Bool.lazy(Source.Walk, c, u => Source.Term.walk(z1, Env.rb(e), Con{Source.Arg{z0, Source.Env.sub(Env.rb(e), r0)}, Args.rb(xs)}),
                u => Source.Walk.done{Source.Term.spine(Args.rb(xs), Source.Term.sub(Source.Term.App{z0, z1, Source.Term.Var{r0}}, 0n, Source.Sub.env{Env.rb(e)}))}),
              Source.Bool.lazy(Machine.Leaf, c, u => Machine.Walk.go(z1, e, Machine.Val.arg{z0, Machine.Env.get(e, r0), xs}),
                u => Machine.Leaf.at{Source.Term.App{z0, z1, Source.Term.Var{r0}}, e, xs})),
            Walk.app_var(z0, z1, r0, e, xs, bk, Get.ok(e, r0, bk, he), hx, hy => Walk.eq(z1, e, Machine.Val.arg{z0, Machine.Env.get(e, r0), xs}, bk, he, hy)),
            ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx)))
        case Source.Term.Ref{+r0}:
          ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
        case Source.Term.Ann{+r0, +r1}:
          ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
        case Source.Term.Let{+r0, +r1, +r2}:
          ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
        case Source.Term.Typ{+r0}:
          ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
        case Source.Term.Min{+r0, +r1}:
          ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
        case Source.Term.All{+r0, +r1, +r2}:
          ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
        case Source.Term.Lam{+r0, +r1}:
          ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
        case Source.Term.App{+r0, +r1, +r2}:
          ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
        case Source.Term.Sig{+r0, +r1, +r2}:
          ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
        case Source.Term.Tup{+r0, +r1, +r2}:
          ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
        case Source.Term.Prj{+r0}:
          ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
        case Source.Term.Enu{+r0}:
          ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
        case Source.Term.Lab{+r0}:
          ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
        case Source.Term.Mat{+r0, +r1, +r2}:
          ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
        case Source.Term.Efq{}:
          ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
        case Source.Term.Eql{+r0, +r1, +r2}:
          ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
        case Source.Term.Rfl{}:
          ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
        case Source.Term.Rwt{+r0, +r1, +r2}:
          ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
    case Source.Term.Sig{+z0, +z1, +z2}:
      ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
    case Source.Term.Tup{+z0, +z1, +z2}:
      ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
    case Source.Term.Prj{+z0}:
      match xs:
        case Machine.Val.nil{}:
          ({==}, {==})
        case Machine.Val.env{+y0, +y1}:
          Shared.Bool.absurd(Walk.res(bk, Source.Term.walk(Source.Term.Prj{z0}, Env.rb(e), Args.rb(Machine.Val.env{y0, y1})), Machine.Walk.go(Source.Term.Prj{z0}, e, Machine.Val.env{y0, y1})), hx)
        case Machine.Val.arg{+y0, +y1, +y2}:
          Walk.prj_x(y0, y1, y2, z0, e, bk, Look.self(y1, bk, SP.Bool.and_left(Val.ok(y1, Mode.any{}, bk), Val.ok(y2, Mode.args{}, bk), hx)), SP.Bool.and_right(Val.ok(y1, Mode.any{}, bk), Val.ok(y2, Mode.args{}, bk), hx),
            ys => hy => Walk.eq(z0, e, ys, bk, he, hy))
        case Machine.Val.clo{+y0, +y1}:
          Shared.Bool.absurd(Walk.res(bk, Source.Term.walk(Source.Term.Prj{z0}, Env.rb(e), Args.rb(Machine.Val.clo{y0, y1})), Machine.Walk.go(Source.Term.Prj{z0}, e, Machine.Val.clo{y0, y1})), hx)
        case Machine.Val.lab{+y0}:
          Shared.Bool.absurd(Walk.res(bk, Source.Term.walk(Source.Term.Prj{z0}, Env.rb(e), Args.rb(Machine.Val.lab{y0})), Machine.Walk.go(Source.Term.Prj{z0}, e, Machine.Val.lab{y0})), hx)
        case Machine.Val.rfl{}:
          Shared.Bool.absurd(Walk.res(bk, Source.Term.walk(Source.Term.Prj{z0}, Env.rb(e), Args.rb(Machine.Val.rfl{})), Machine.Walk.go(Source.Term.Prj{z0}, e, Machine.Val.rfl{})), hx)
        case Machine.Val.tup{+y0, +y1, +y2}:
          Shared.Bool.absurd(Walk.res(bk, Source.Term.walk(Source.Term.Prj{z0}, Env.rb(e), Args.rb(Machine.Val.tup{y0, y1, y2})), Machine.Walk.go(Source.Term.Prj{z0}, e, Machine.Val.tup{y0, y1, y2})), hx)
        case Machine.Val.call{+y0, +y1}:
          Shared.Bool.absurd(Walk.res(bk, Source.Term.walk(Source.Term.Prj{z0}, Env.rb(e), Args.rb(Machine.Val.call{y0, y1})), Machine.Walk.go(Source.Term.Prj{z0}, e, Machine.Val.call{y0, y1})), hx)
    case Source.Term.Enu{+z0}:
      ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
    case Source.Term.Lab{+z0}:
      ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
    case Source.Term.Mat{+z0, +z1, +z2}:
      match xs:
        case Machine.Val.nil{}:
          ({==}, {==})
        case Machine.Val.env{+y0, +y1}:
          Shared.Bool.absurd(Walk.res(bk, Source.Term.walk(Source.Term.Mat{z0, z1, z2}, Env.rb(e), Args.rb(Machine.Val.env{y0, y1})), Machine.Walk.go(Source.Term.Mat{z0, z1, z2}, e, Machine.Val.env{y0, y1})), hx)
        case Machine.Val.arg{+y0, +y1, +y2}:
          Walk.mat_x(y0, z0, y1, y2, z1, z2, e, bk, Look.self(y1, bk, SP.Bool.and_left(Val.ok(y1, Mode.any{}, bk), Val.ok(y2, Mode.args{}, bk), hx)), SP.Bool.and_right(Val.ok(y1, Mode.any{}, bk), Val.ok(y2, Mode.args{}, bk), hx),
            ys => hy => Walk.eq(z1, e, ys, bk, he, hy), ys => hy => Walk.eq(z2, e, ys, bk, he, hy))
        case Machine.Val.clo{+y0, +y1}:
          Shared.Bool.absurd(Walk.res(bk, Source.Term.walk(Source.Term.Mat{z0, z1, z2}, Env.rb(e), Args.rb(Machine.Val.clo{y0, y1})), Machine.Walk.go(Source.Term.Mat{z0, z1, z2}, e, Machine.Val.clo{y0, y1})), hx)
        case Machine.Val.lab{+y0}:
          Shared.Bool.absurd(Walk.res(bk, Source.Term.walk(Source.Term.Mat{z0, z1, z2}, Env.rb(e), Args.rb(Machine.Val.lab{y0})), Machine.Walk.go(Source.Term.Mat{z0, z1, z2}, e, Machine.Val.lab{y0})), hx)
        case Machine.Val.rfl{}:
          Shared.Bool.absurd(Walk.res(bk, Source.Term.walk(Source.Term.Mat{z0, z1, z2}, Env.rb(e), Args.rb(Machine.Val.rfl{})), Machine.Walk.go(Source.Term.Mat{z0, z1, z2}, e, Machine.Val.rfl{})), hx)
        case Machine.Val.tup{+y0, +y1, +y2}:
          Shared.Bool.absurd(Walk.res(bk, Source.Term.walk(Source.Term.Mat{z0, z1, z2}, Env.rb(e), Args.rb(Machine.Val.tup{y0, y1, y2})), Machine.Walk.go(Source.Term.Mat{z0, z1, z2}, e, Machine.Val.tup{y0, y1, y2})), hx)
        case Machine.Val.call{+y0, +y1}:
          Shared.Bool.absurd(Walk.res(bk, Source.Term.walk(Source.Term.Mat{z0, z1, z2}, Env.rb(e), Args.rb(Machine.Val.call{y0, y1})), Machine.Walk.go(Source.Term.Mat{z0, z1, z2}, e, Machine.Val.call{y0, y1})), hx)
    case Source.Term.Efq{}:
      match xs:
        case Machine.Val.nil{}:
          ({==}, {==})
        case Machine.Val.env{+y0, +y1}:
          Shared.Bool.absurd(Walk.res(bk, Source.Term.walk(Source.Term.Efq{}, Env.rb(e), Args.rb(Machine.Val.env{y0, y1})), Machine.Walk.go(Source.Term.Efq{}, e, Machine.Val.env{y0, y1})), hx)
        case Machine.Val.arg{+y0, +y1, +y2}:
          ({==}, {==})
        case Machine.Val.clo{+y0, +y1}:
          Shared.Bool.absurd(Walk.res(bk, Source.Term.walk(Source.Term.Efq{}, Env.rb(e), Args.rb(Machine.Val.clo{y0, y1})), Machine.Walk.go(Source.Term.Efq{}, e, Machine.Val.clo{y0, y1})), hx)
        case Machine.Val.lab{+y0}:
          Shared.Bool.absurd(Walk.res(bk, Source.Term.walk(Source.Term.Efq{}, Env.rb(e), Args.rb(Machine.Val.lab{y0})), Machine.Walk.go(Source.Term.Efq{}, e, Machine.Val.lab{y0})), hx)
        case Machine.Val.rfl{}:
          Shared.Bool.absurd(Walk.res(bk, Source.Term.walk(Source.Term.Efq{}, Env.rb(e), Args.rb(Machine.Val.rfl{})), Machine.Walk.go(Source.Term.Efq{}, e, Machine.Val.rfl{})), hx)
        case Machine.Val.tup{+y0, +y1, +y2}:
          Shared.Bool.absurd(Walk.res(bk, Source.Term.walk(Source.Term.Efq{}, Env.rb(e), Args.rb(Machine.Val.tup{y0, y1, y2})), Machine.Walk.go(Source.Term.Efq{}, e, Machine.Val.tup{y0, y1, y2})), hx)
        case Machine.Val.call{+y0, +y1}:
          Shared.Bool.absurd(Walk.res(bk, Source.Term.walk(Source.Term.Efq{}, Env.rb(e), Args.rb(Machine.Val.call{y0, y1})), Machine.Walk.go(Source.Term.Efq{}, e, Machine.Val.call{y0, y1})), hx)
    case Source.Term.Eql{+z0, +z1, +z2}:
      ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
    case Source.Term.Rfl{}:
      ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
    case Source.Term.Rwt{+z0, +z1, +z2}:
      ({==}, SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(xs, Mode.args{}, bk), he, hx))
