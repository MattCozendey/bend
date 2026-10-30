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

# Booleans
# ========

def Bool.true_false(e: {True{} == False{} : Bool}) -> Empty:
  Shared.Bool.no(Equal.sym(Bool, True{}, False{}, e))

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
# Source steps
# ============

# a proof of P(x), moved to P(y)
def Eq.rw(-A: Type, -x: A, -y: A, e: {x == y : A}, -P: A -> Type, p: P(x)) -> P(y):
  %e : P(_)
  p

# the walk w, with one more argument at the end of its leaf
def Walk.snoc(w: Source.Walk, +q: Source.Quan, +x: Source.Term) -> Source.Walk:
  match w:
    case Source.Walk.done{u}:
      Source.Walk.done{Source.Term.App{q, u, x}}
    case Source.Walk.need{}:
      Source.Walk.need{}
    case Source.Walk.fail{}:
      Source.Walk.fail{}

def Walk.need_false(-A: Type, h: {Source.Walk.is_need(Source.Walk.need{}) == False{} : Bool}) -> A:
  Empty.absurd(A, Bool.true_false(h))

def Prefix.by(c: Bool, -w1: Source.Walk, -w2: Source.Walk, -q: Source.Quan, -x: Source.Term,
  h: {Source.Walk.is_need(Source.Bool.lazy(Source.Walk, c, u => w1, u => Source.Walk.fail{})) == False{} : Bool},
  ih: {Source.Walk.is_need(w1) == False{} : Bool} -> {w2 == Walk.snoc(w1, q, x) : Source.Walk}) ->
  {Source.Bool.lazy(Source.Walk, c, u => w2, u => Source.Walk.fail{}) ==
    Walk.snoc(Source.Bool.lazy(Source.Walk, c, u => w1, u => Source.Walk.fail{}), q, x) : Source.Walk}:
  match c:
    case True{}:
      ih(h)
    case False{}:
      {==}

def Prefix.by2(c: Bool, -a1: Source.Walk, -a2: Source.Walk, -b1: Source.Walk, -b2: Source.Walk, -q: Source.Quan,
  -x: Source.Term, h: {Source.Walk.is_need(Source.Bool.lazy(Source.Walk, c, u => a1, u => b1)) == False{} : Bool},
  iha: {Source.Walk.is_need(a1) == False{} : Bool} -> {a2 == Walk.snoc(a1, q, x) : Source.Walk},
  ihb: {Source.Walk.is_need(b1) == False{} : Bool} -> {b2 == Walk.snoc(b1, q, x) : Source.Walk}) ->
  {Source.Bool.lazy(Source.Walk, c, u => a2, u => b2) ==
    Walk.snoc(Source.Bool.lazy(Source.Walk, c, u => a1, u => b1), q, x) : Source.Walk}:
  match c:
    case True{}:
      iha(h)
    case False{}:
      ihb(h)

def Prefix.done(+ys: List<&2, Source.Arg>, +s: Source.Term, +q: Source.Quan, +x: Source.Term) ->
  {Source.Walk.done{Source.Term.spine(List.append(&2, Source.Arg, ys, Con{Source.Arg{q, x}, Nil{}}), s)} ==
    Walk.snoc(Source.Walk.done{Source.Term.spine(ys, s)}, q, x) : Source.Walk}:
  Equal.cong(Source.Term, Source.Walk, z => Source.Walk.done{z},
    Source.Term.spine(List.append(&2, Source.Arg, ys, Con{Source.Arg{q, x}, Nil{}}), s),
    Source.Term.App{q, Source.Term.spine(ys, s), x}, SP.Term.spine_snoc(ys, s, q, x))

# a walk that does not need more arguments gives the same leaf with one more
# argument at its end
def Walk.prefix(t: Source.Term, +e: List<&2, Source.Term>, +xs: List<&2, Source.Arg>, +q: Source.Quan,
  +x: Source.Term, h: {Source.Walk.is_need(Source.Term.walk(t, e, xs)) == False{} : Bool}) ->
  {Source.Term.walk(t, e, List.append(&2, Source.Arg, xs, Con{Source.Arg{q, x}, Nil{}})) ==
    Walk.snoc(Source.Term.walk(t, e, xs), q, x) : Source.Walk}:
  match t:
    case Source.Term.Var{+z0}:
      Prefix.done(xs, Source.Term.sub(Source.Term.Var{z0}, 0n, Source.Sub.env{e}), q, x)
    case Source.Term.Ref{+z0}:
      Prefix.done(xs, Source.Term.sub(Source.Term.Ref{z0}, 0n, Source.Sub.env{e}), q, x)
    case Source.Term.Ann{+z0, +z1}:
      Prefix.done(xs, Source.Term.sub(Source.Term.Ann{z0, z1}, 0n, Source.Sub.env{e}), q, x)
    case Source.Term.Let{+z0, +z1, +z2}:
      Prefix.done(xs, Source.Term.sub(Source.Term.Let{z0, z1, z2}, 0n, Source.Sub.env{e}), q, x)
    case Source.Term.Typ{+z0}:
      Prefix.done(xs, Source.Term.sub(Source.Term.Typ{z0}, 0n, Source.Sub.env{e}), q, x)
    case Source.Term.Min{+z0, +z1}:
      Prefix.done(xs, Source.Term.sub(Source.Term.Min{z0, z1}, 0n, Source.Sub.env{e}), q, x)
    case Source.Term.All{+z0, +z1, +z2}:
      Prefix.done(xs, Source.Term.sub(Source.Term.All{z0, z1, z2}, 0n, Source.Sub.env{e}), q, x)
    case Source.Term.Lam{+z0, +z1}:
      match xs:
        case Nil{}:
          Walk.need_false({Source.Term.walk(Source.Term.Lam{z0, z1}, e, List.append(&2, Source.Arg, Nil{}, Con{Source.Arg{q, x}, Nil{}})) == Walk.snoc(Source.Term.walk(Source.Term.Lam{z0, z1}, e, Nil{}), q, x) : Source.Walk}, h)
        case Con{Source.Arg{+aq, +ax}, +rest}:
          Prefix.by(Bool.and(Source.Bool.is_eq(Source.Quan.live(z0), Source.Quan.live(aq)), Bool.or(Bool.not(Source.Quan.is_q2(z0)), Source.Term.is_data(ax))), Source.Term.walk(z1, Con{ax, e}, rest), Source.Term.walk(z1, Con{ax, e}, List.append(&2, Source.Arg, rest, Con{Source.Arg{q, x}, Nil{}})), q, x, h,
            hh => Walk.prefix(z1, Con{ax, e}, rest, q, x, hh))
    case Source.Term.App{+z0, +z1, +z2}:
      match z2:
        case Source.Term.Var{+r0}:
          Prefix.by2(Source.Spine.head.takes(Source.Term.unspine(z1, [])), Source.Term.walk(z1, e, Con{Source.Arg{z0, Source.Env.sub(e, r0)}, xs}),
            Source.Term.walk(z1, e, List.append(&2, Source.Arg, Con{Source.Arg{z0, Source.Env.sub(e, r0)}, xs}, Con{Source.Arg{q, x}, Nil{}})), Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(Source.Term.App{z0, z1, Source.Term.Var{r0}}, 0n, Source.Sub.env{e}))},
            Source.Walk.done{Source.Term.spine(List.append(&2, Source.Arg, xs, Con{Source.Arg{q, x}, Nil{}}), Source.Term.sub(Source.Term.App{z0, z1, Source.Term.Var{r0}}, 0n, Source.Sub.env{e}))}, q, x, h,
            hh => Walk.prefix(z1, e, Con{Source.Arg{z0, Source.Env.sub(e, r0)}, xs}, q, x, hh), hh => Prefix.done(xs, Source.Term.sub(Source.Term.App{z0, z1, Source.Term.Var{r0}}, 0n, Source.Sub.env{e}), q, x))
        case Source.Term.Ref{+r0}:
          Prefix.done(xs, Source.Term.sub(Source.Term.App{z0, z1, Source.Term.Ref{r0}}, 0n, Source.Sub.env{e}), q, x)
        case Source.Term.Ann{+r0, +r1}:
          Prefix.done(xs, Source.Term.sub(Source.Term.App{z0, z1, Source.Term.Ann{r0, r1}}, 0n, Source.Sub.env{e}), q, x)
        case Source.Term.Let{+r0, +r1, +r2}:
          Prefix.done(xs, Source.Term.sub(Source.Term.App{z0, z1, Source.Term.Let{r0, r1, r2}}, 0n, Source.Sub.env{e}), q, x)
        case Source.Term.Typ{+r0}:
          Prefix.done(xs, Source.Term.sub(Source.Term.App{z0, z1, Source.Term.Typ{r0}}, 0n, Source.Sub.env{e}), q, x)
        case Source.Term.Min{+r0, +r1}:
          Prefix.done(xs, Source.Term.sub(Source.Term.App{z0, z1, Source.Term.Min{r0, r1}}, 0n, Source.Sub.env{e}), q, x)
        case Source.Term.All{+r0, +r1, +r2}:
          Prefix.done(xs, Source.Term.sub(Source.Term.App{z0, z1, Source.Term.All{r0, r1, r2}}, 0n, Source.Sub.env{e}), q, x)
        case Source.Term.Lam{+r0, +r1}:
          Prefix.done(xs, Source.Term.sub(Source.Term.App{z0, z1, Source.Term.Lam{r0, r1}}, 0n, Source.Sub.env{e}), q, x)
        case Source.Term.App{+r0, +r1, +r2}:
          Prefix.done(xs, Source.Term.sub(Source.Term.App{z0, z1, Source.Term.App{r0, r1, r2}}, 0n, Source.Sub.env{e}), q, x)
        case Source.Term.Sig{+r0, +r1, +r2}:
          Prefix.done(xs, Source.Term.sub(Source.Term.App{z0, z1, Source.Term.Sig{r0, r1, r2}}, 0n, Source.Sub.env{e}), q, x)
        case Source.Term.Tup{+r0, +r1, +r2}:
          Prefix.done(xs, Source.Term.sub(Source.Term.App{z0, z1, Source.Term.Tup{r0, r1, r2}}, 0n, Source.Sub.env{e}), q, x)
        case Source.Term.Prj{+r0}:
          Prefix.done(xs, Source.Term.sub(Source.Term.App{z0, z1, Source.Term.Prj{r0}}, 0n, Source.Sub.env{e}), q, x)
        case Source.Term.Enu{+r0}:
          Prefix.done(xs, Source.Term.sub(Source.Term.App{z0, z1, Source.Term.Enu{r0}}, 0n, Source.Sub.env{e}), q, x)
        case Source.Term.Lab{+r0}:
          Prefix.done(xs, Source.Term.sub(Source.Term.App{z0, z1, Source.Term.Lab{r0}}, 0n, Source.Sub.env{e}), q, x)
        case Source.Term.Mat{+r0, +r1, +r2}:
          Prefix.done(xs, Source.Term.sub(Source.Term.App{z0, z1, Source.Term.Mat{r0, r1, r2}}, 0n, Source.Sub.env{e}), q, x)
        case Source.Term.Efq{}:
          Prefix.done(xs, Source.Term.sub(Source.Term.App{z0, z1, Source.Term.Efq{}}, 0n, Source.Sub.env{e}), q, x)
        case Source.Term.Eql{+r0, +r1, +r2}:
          Prefix.done(xs, Source.Term.sub(Source.Term.App{z0, z1, Source.Term.Eql{r0, r1, r2}}, 0n, Source.Sub.env{e}), q, x)
        case Source.Term.Rfl{}:
          Prefix.done(xs, Source.Term.sub(Source.Term.App{z0, z1, Source.Term.Rfl{}}, 0n, Source.Sub.env{e}), q, x)
        case Source.Term.Rwt{+r0, +r1, +r2}:
          Prefix.done(xs, Source.Term.sub(Source.Term.App{z0, z1, Source.Term.Rwt{r0, r1, r2}}, 0n, Source.Sub.env{e}), q, x)
    case Source.Term.Sig{+z0, +z1, +z2}:
      Prefix.done(xs, Source.Term.sub(Source.Term.Sig{z0, z1, z2}, 0n, Source.Sub.env{e}), q, x)
    case Source.Term.Tup{+z0, +z1, +z2}:
      Prefix.done(xs, Source.Term.sub(Source.Term.Tup{z0, z1, z2}, 0n, Source.Sub.env{e}), q, x)
    case Source.Term.Prj{+z0}:
      match xs:
        case Nil{}:
          Walk.need_false({Source.Term.walk(Source.Term.Prj{z0}, e, List.append(&2, Source.Arg, Nil{}, Con{Source.Arg{q, x}, Nil{}})) == Walk.snoc(Source.Term.walk(Source.Term.Prj{z0}, e, Nil{}), q, x) : Source.Walk}, h)
        case Con{Source.Arg{+aq, ax}, +rest}:
          match ax:
            case Source.Term.Var{+r0}:
              {==}
            case Source.Term.Ref{+r0}:
              {==}
            case Source.Term.Ann{+r0, +r1}:
              {==}
            case Source.Term.Let{+r0, +r1, +r2}:
              {==}
            case Source.Term.Typ{+r0}:
              {==}
            case Source.Term.Min{+r0, +r1}:
              {==}
            case Source.Term.All{+r0, +r1, +r2}:
              {==}
            case Source.Term.Lam{+r0, +r1}:
              {==}
            case Source.Term.App{+r0, +r1, +r2}:
              {==}
            case Source.Term.Sig{+r0, +r1, +r2}:
              {==}
            case Source.Term.Tup{+r0, +r1, +r2}:
              Prefix.by(Source.Quan.live(aq), Source.Term.walk(z0, e, Con{Source.Arg{Source.Quan.fld(r0, aq), r1}, Con{Source.Arg{aq, r2}, rest}}), Source.Term.walk(z0, e, List.append(&2, Source.Arg, Con{Source.Arg{Source.Quan.fld(r0, aq), r1}, Con{Source.Arg{aq, r2}, rest}}, Con{Source.Arg{q, x}, Nil{}})), q, x, h,
                hh2 => Walk.prefix(z0, e, Con{Source.Arg{Source.Quan.fld(r0, aq), r1}, Con{Source.Arg{aq, r2}, rest}}, q, x, hh2))
            case Source.Term.Prj{+r0}:
              {==}
            case Source.Term.Enu{+r0}:
              {==}
            case Source.Term.Lab{+r0}:
              {==}
            case Source.Term.Mat{+r0, +r1, +r2}:
              {==}
            case Source.Term.Efq{}:
              {==}
            case Source.Term.Eql{+r0, +r1, +r2}:
              {==}
            case Source.Term.Rfl{}:
              {==}
            case Source.Term.Rwt{+r0, +r1, +r2}:
              {==}
    case Source.Term.Enu{+z0}:
      Prefix.done(xs, Source.Term.sub(Source.Term.Enu{z0}, 0n, Source.Sub.env{e}), q, x)
    case Source.Term.Lab{+z0}:
      Prefix.done(xs, Source.Term.sub(Source.Term.Lab{z0}, 0n, Source.Sub.env{e}), q, x)
    case Source.Term.Mat{+z0, +z1, +z2}:
      match xs:
        case Nil{}:
          Walk.need_false({Source.Term.walk(Source.Term.Mat{z0, z1, z2}, e, List.append(&2, Source.Arg, Nil{}, Con{Source.Arg{q, x}, Nil{}})) == Walk.snoc(Source.Term.walk(Source.Term.Mat{z0, z1, z2}, e, Nil{}), q, x) : Source.Walk}, h)
        case Con{Source.Arg{+aq, ax}, +rest}:
          match ax:
            case Source.Term.Var{+r0}:
              {==}
            case Source.Term.Ref{+r0}:
              {==}
            case Source.Term.Ann{+r0, +r1}:
              {==}
            case Source.Term.Let{+r0, +r1, +r2}:
              {==}
            case Source.Term.Typ{+r0}:
              {==}
            case Source.Term.Min{+r0, +r1}:
              {==}
            case Source.Term.All{+r0, +r1, +r2}:
              {==}
            case Source.Term.Lam{+r0, +r1}:
              {==}
            case Source.Term.App{+r0, +r1, +r2}:
              {==}
            case Source.Term.Sig{+r0, +r1, +r2}:
              {==}
            case Source.Term.Tup{+r0, +r1, +r2}:
              {==}
            case Source.Term.Prj{+r0}:
              {==}
            case Source.Term.Enu{+r0}:
              {==}
            case Source.Term.Lab{+r0}:
              Prefix.by(Source.Quan.live(aq), Source.Bool.lazy(Source.Walk, Source.Name.is_eq(r0, z0), w => Source.Term.walk(z1, e, rest), w => Source.Term.walk(z2, e, Con{Source.Arg{aq, Source.Term.Lab{r0}}, rest})),
                Source.Bool.lazy(Source.Walk, Source.Name.is_eq(r0, z0), w => Source.Term.walk(z1, e, List.append(&2, Source.Arg, rest, Con{Source.Arg{q, x}, Nil{}})), w => Source.Term.walk(z2, e, List.append(&2, Source.Arg, Con{Source.Arg{aq, Source.Term.Lab{r0}}, rest}, Con{Source.Arg{q, x}, Nil{}}))), q, x, h,
                hh2 => Prefix.by2(Source.Name.is_eq(r0, z0), Source.Term.walk(z1, e, rest), Source.Term.walk(z1, e, List.append(&2, Source.Arg, rest, Con{Source.Arg{q, x}, Nil{}})),
                  Source.Term.walk(z2, e, Con{Source.Arg{aq, Source.Term.Lab{r0}}, rest}), Source.Term.walk(z2, e, List.append(&2, Source.Arg, Con{Source.Arg{aq, Source.Term.Lab{r0}}, rest}, Con{Source.Arg{q, x}, Nil{}})), q, x, hh2,
                  hh3 => Walk.prefix(z1, e, rest, q, x, hh3), hh3 => Walk.prefix(z2, e, Con{Source.Arg{aq, Source.Term.Lab{r0}}, rest}, q, x, hh3)))
            case Source.Term.Mat{+r0, +r1, +r2}:
              {==}
            case Source.Term.Efq{}:
              {==}
            case Source.Term.Eql{+r0, +r1, +r2}:
              {==}
            case Source.Term.Rfl{}:
              {==}
            case Source.Term.Rwt{+r0, +r1, +r2}:
              {==}
    case Source.Term.Efq{}:
      match xs:
        case Nil{}:
          Walk.need_false({Source.Term.walk(Source.Term.Efq{}, e, List.append(&2, Source.Arg, Nil{}, Con{Source.Arg{q, x}, Nil{}})) == Walk.snoc(Source.Term.walk(Source.Term.Efq{}, e, Nil{}), q, x) : Source.Walk}, h)
        case Con{a0, rest}:
          {==}
    case Source.Term.Eql{+z0, +z1, +z2}:
      Prefix.done(xs, Source.Term.sub(Source.Term.Eql{z0, z1, z2}, 0n, Source.Sub.env{e}), q, x)
    case Source.Term.Rfl{}:
      Prefix.done(xs, Source.Term.sub(Source.Term.Rfl{}, 0n, Source.Sub.env{e}), q, x)
    case Source.Term.Rwt{+z0, +z1, +z2}:
      Prefix.done(xs, Source.Term.sub(Source.Term.Rwt{z0, z1, z2}, 0n, Source.Sub.env{e}), q, x)
# Values do not step
# ==================

def Walk.need_done(w: Source.Walk, h: {Source.Walk.is_need(w) == True{} : Bool}) ->
  {Source.Walk.done_term(w) == None{} : Maybe<&2, Source.Term>}:
  match w:
    case Source.Walk.need{}:
      {==}
    case Source.Walk.done{u}:
      Shared.Bool.absurd({Some{u} == None{} : Maybe<&2, Source.Term>}, h)
    case Source.Walk.fail{}:
      {==}

def Call.walk_eq(+bk: List<&2, Source.Def>, +k: List<&2, Nat>, +ys: List<&2, Source.Arg>) ->
  {Source.Term.walk_call(bk, Source.Term.spine(ys, Source.Term.Ref{k})) ==
    Source.Term.walk_call.got(Source.Book.get(bk, k), ys) : Source.Walk}:
  Equal.trans(Source.Walk, Source.Term.walk_call(bk, Source.Term.spine(ys, Source.Term.Ref{k})),
    Source.Term.walk_call.got(Source.Book.get(bk, k), List.append(&2, Source.Arg, ys, [])),
    Source.Term.walk_call.got(Source.Book.get(bk, k), ys),
    Equal.cong(Source.Spine, Source.Walk, z => Source.Term.walk_call.of(bk, z),
      Source.Term.unspine(Source.Term.spine(ys, Source.Term.Ref{k}), []),
      Source.Term.unspine(Source.Term.Ref{k}, List.append(&2, Source.Arg, ys, [])),
      SP.Term.unspine_spine(ys, Source.Term.Ref{k}, [])),
    Equal.cong(List<&2, Source.Arg>, Source.Walk, z => Source.Term.walk_call.got(Source.Book.get(bk, k), z),
      List.append(&2, Source.Arg, ys, []), ys, SP.List.append_nil(ys)))

def Fires.got(m: Maybe<&2, Source.Def>, +ys: List<&2, Source.Arg>, +q: Source.Quan, +x: Source.Term,
  hn: {Source.Walk.is_need(Source.Term.walk_call.got(m, ys)) == False{} : Bool}) ->
  {Source.Term.walk_call.got(m, List.append(&2, Source.Arg, ys, Con{Source.Arg{q, x}, Nil{}})) ==
    Walk.snoc(Source.Term.walk_call.got(m, ys), q, x) : Source.Walk}:
  match m:
    case None{}:
      {==}
    case Some{Source.Def{dk, dt, dv, dop}}:
      Walk.prefix(dv, [], ys, q, x, hn)

def Fires.snoc.of(-f: Source.Term, +q: Source.Quan, +x: Source.Term, +bk: List<&2, Source.Def>, ra: SP.Term.Args<bk, f>,
  hn: {Source.Walk.is_need(Source.Term.walk_call(bk, f)) == False{} : Bool}) ->
  {Source.Term.walk_call(bk, Source.Term.App{q, f, x}) == Walk.snoc(Source.Term.walk_call(bk, f), q, x) : Source.Walk}:
  match ra:
    case SP.Term.Args.of{+k, +ys, +et, vs}:
      %Equal.sym(Source.Term, f, Source.Term.spine(ys, Source.Term.Ref{k}), et) :
        {Source.Term.walk_call(bk, Source.Term.App{q, _, x}) == Walk.snoc(Source.Term.walk_call(bk, _), q, x) : Source.Walk}
      %SP.Term.spine_snoc(ys, Source.Term.Ref{k}, q, x) :
        {Source.Term.walk_call(bk, _) == Walk.snoc(Source.Term.walk_call(bk, Source.Term.spine(ys, Source.Term.Ref{k})), q, x) : Source.Walk}
      %Equal.sym(Source.Walk,
        Source.Term.walk_call(bk, Source.Term.spine(List.append(&2, Source.Arg, ys, Con{Source.Arg{q, x}, Nil{}}), Source.Term.Ref{k})),
        Source.Term.walk_call.got(Source.Book.get(bk, k), List.append(&2, Source.Arg, ys, Con{Source.Arg{q, x}, Nil{}})),
        Call.walk_eq(bk, k, List.append(&2, Source.Arg, ys, Con{Source.Arg{q, x}, Nil{}}))) :
        {_ == Walk.snoc(Source.Term.walk_call(bk, Source.Term.spine(ys, Source.Term.Ref{k})), q, x) : Source.Walk}
      %Equal.sym(Source.Walk, Source.Term.walk_call(bk, Source.Term.spine(ys, Source.Term.Ref{k})),
        Source.Term.walk_call.got(Source.Book.get(bk, k), ys), Call.walk_eq(bk, k, ys)) :
        {Source.Term.walk_call.got(Source.Book.get(bk, k), List.append(&2, Source.Arg, ys, Con{Source.Arg{q, x}, Nil{}})) ==
          Walk.snoc(_, q, x) : Source.Walk}
      Fires.got(Source.Book.get(bk, k), ys, q, x,
        Eq.rw(Source.Walk, Source.Term.walk_call(bk, Source.Term.spine(ys, Source.Term.Ref{k})),
          Source.Term.walk_call.got(Source.Book.get(bk, k), ys), Call.walk_eq(bk, k, ys),
          z => {Source.Walk.is_need(z) == False{} : Bool},
          Eq.rw(Source.Term, f, Source.Term.spine(ys, Source.Term.Ref{k}), et,
            z => {Source.Walk.is_need(Source.Term.walk_call(bk, z)) == False{} : Bool}, hn)))

# when the call f does not need more arguments, the call App q f x walks to
# f's leaf with x at its end
def Fires.snoc(+f: Source.Term, +q: Source.Quan, +x: Source.Term, +bk: List<&2, Source.Def>,
  hf: {Source.Term.is_value(f, True{}, bk) == True{} : Bool},
  hn: {Source.Walk.is_need(Source.Term.walk_call(bk, f)) == False{} : Bool}) ->
  {Source.Term.walk_call(bk, Source.Term.App{q, f, x}) == Walk.snoc(Source.Term.walk_call(bk, f), q, x) : Source.Walk}:
  Fires.snoc.of(f, q, x, bk, SP.Term.is_value_sound.go(f, True{}, bk, hf), hn)

# a spine on a def is a value when its walk needs more arguments
def Vals.stops(t: Source.Term, +bk: List<&2, Source.Def>, h: {Source.Term.is_value(t, True{}, bk) == True{} : Bool}) ->
  {Source.Term.is_value(t, False{}, bk) == Source.Term.stops(bk, t) : Bool}:
  match t:
    case Source.Term.Var{+z0}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Var{z0}, False{}, bk) == Source.Term.stops(bk, Source.Term.Var{z0}) : Bool}, h)
    case Source.Term.Ref{+z0}:
      {==}
    case Source.Term.Ann{+z0, +z1}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Ann{z0, z1}, False{}, bk) == Source.Term.stops(bk, Source.Term.Ann{z0, z1}) : Bool}, h)
    case Source.Term.Let{+z0, +z1, +z2}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Let{z0, z1, z2}, False{}, bk) == Source.Term.stops(bk, Source.Term.Let{z0, z1, z2}) : Bool}, h)
    case Source.Term.Typ{+z0}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Typ{z0}, False{}, bk) == Source.Term.stops(bk, Source.Term.Typ{z0}) : Bool}, h)
    case Source.Term.Min{+z0, +z1}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Min{z0, z1}, False{}, bk) == Source.Term.stops(bk, Source.Term.Min{z0, z1}) : Bool}, h)
    case Source.Term.All{+z0, +z1, +z2}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.All{z0, z1, z2}, False{}, bk) == Source.Term.stops(bk, Source.Term.All{z0, z1, z2}) : Bool}, h)
    case Source.Term.Lam{+z0, +z1}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Lam{z0, z1}, False{}, bk) == Source.Term.stops(bk, Source.Term.Lam{z0, z1}) : Bool}, h)
    case Source.Term.App{+z0, +z1, +z2}:
      %Equal.sym(Bool, Bool.and(Source.Term.is_value(z1, True{}, bk), Bool.or(Bool.not(Source.Quan.live(z0)), Source.Term.is_value(z2, False{}, bk))), True{}, h) :
        {Bool.and(_, Source.Term.stops(bk, Source.Term.App{z0, z1, z2})) == Source.Term.stops(bk, Source.Term.App{z0, z1, z2}) : Bool}
      {==}
    case Source.Term.Sig{+z0, +z1, +z2}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Sig{z0, z1, z2}, False{}, bk) == Source.Term.stops(bk, Source.Term.Sig{z0, z1, z2}) : Bool}, h)
    case Source.Term.Tup{+z0, +z1, +z2}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Tup{z0, z1, z2}, False{}, bk) == Source.Term.stops(bk, Source.Term.Tup{z0, z1, z2}) : Bool}, h)
    case Source.Term.Prj{+z0}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Prj{z0}, False{}, bk) == Source.Term.stops(bk, Source.Term.Prj{z0}) : Bool}, h)
    case Source.Term.Enu{+z0}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Enu{z0}, False{}, bk) == Source.Term.stops(bk, Source.Term.Enu{z0}) : Bool}, h)
    case Source.Term.Lab{+z0}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Lab{z0}, False{}, bk) == Source.Term.stops(bk, Source.Term.Lab{z0}) : Bool}, h)
    case Source.Term.Mat{+z0, +z1, +z2}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Mat{z0, z1, z2}, False{}, bk) == Source.Term.stops(bk, Source.Term.Mat{z0, z1, z2}) : Bool}, h)
    case Source.Term.Efq{}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Efq{}, False{}, bk) == Source.Term.stops(bk, Source.Term.Efq{}) : Bool}, h)
    case Source.Term.Eql{+z0, +z1, +z2}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Eql{z0, z1, z2}, False{}, bk) == Source.Term.stops(bk, Source.Term.Eql{z0, z1, z2}) : Bool}, h)
    case Source.Term.Rfl{}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Rfl{}, False{}, bk) == Source.Term.stops(bk, Source.Term.Rfl{}) : Bool}, h)
    case Source.Term.Rwt{+z0, +z1, +z2}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Rwt{z0, z1, z2}, False{}, bk) == Source.Term.stops(bk, Source.Term.Rwt{z0, z1, z2}) : Bool}, h)

def Args.is_call(t: Source.Term, +bk: List<&2, Source.Def>, h: {Source.Term.is_value(t, True{}, bk) == True{} : Bool}) ->
  {Term.is_call(t) == True{} : Bool}:
  match t:
    case Source.Term.Var{+z0}:
      Shared.Bool.absurd({Term.is_call(Source.Term.Var{z0}) == True{} : Bool}, h)
    case Source.Term.Ref{+z0}:
      {==}
    case Source.Term.Ann{+z0, +z1}:
      Shared.Bool.absurd({Term.is_call(Source.Term.Ann{z0, z1}) == True{} : Bool}, h)
    case Source.Term.Let{+z0, +z1, +z2}:
      Shared.Bool.absurd({Term.is_call(Source.Term.Let{z0, z1, z2}) == True{} : Bool}, h)
    case Source.Term.Typ{+z0}:
      Shared.Bool.absurd({Term.is_call(Source.Term.Typ{z0}) == True{} : Bool}, h)
    case Source.Term.Min{+z0, +z1}:
      Shared.Bool.absurd({Term.is_call(Source.Term.Min{z0, z1}) == True{} : Bool}, h)
    case Source.Term.All{+z0, +z1, +z2}:
      Shared.Bool.absurd({Term.is_call(Source.Term.All{z0, z1, z2}) == True{} : Bool}, h)
    case Source.Term.Lam{+z0, +z1}:
      Shared.Bool.absurd({Term.is_call(Source.Term.Lam{z0, z1}) == True{} : Bool}, h)
    case Source.Term.App{+z0, +z1, +z2}:
      {==}
    case Source.Term.Sig{+z0, +z1, +z2}:
      Shared.Bool.absurd({Term.is_call(Source.Term.Sig{z0, z1, z2}) == True{} : Bool}, h)
    case Source.Term.Tup{+z0, +z1, +z2}:
      Shared.Bool.absurd({Term.is_call(Source.Term.Tup{z0, z1, z2}) == True{} : Bool}, h)
    case Source.Term.Prj{+z0}:
      Shared.Bool.absurd({Term.is_call(Source.Term.Prj{z0}) == True{} : Bool}, h)
    case Source.Term.Enu{+z0}:
      Shared.Bool.absurd({Term.is_call(Source.Term.Enu{z0}) == True{} : Bool}, h)
    case Source.Term.Lab{+z0}:
      Shared.Bool.absurd({Term.is_call(Source.Term.Lab{z0}) == True{} : Bool}, h)
    case Source.Term.Mat{+z0, +z1, +z2}:
      Shared.Bool.absurd({Term.is_call(Source.Term.Mat{z0, z1, z2}) == True{} : Bool}, h)
    case Source.Term.Efq{}:
      Shared.Bool.absurd({Term.is_call(Source.Term.Efq{}) == True{} : Bool}, h)
    case Source.Term.Eql{+z0, +z1, +z2}:
      Shared.Bool.absurd({Term.is_call(Source.Term.Eql{z0, z1, z2}) == True{} : Bool}, h)
    case Source.Term.Rfl{}:
      Shared.Bool.absurd({Term.is_call(Source.Term.Rfl{}) == True{} : Bool}, h)
    case Source.Term.Rwt{+z0, +z1, +z2}:
      Shared.Bool.absurd({Term.is_call(Source.Term.Rwt{z0, z1, z2}) == True{} : Bool}, h)

def Redex.call(+f: Source.Term, -q: Source.Quan, -x: Source.Term, -bk: List<&2, Source.Def>, h: {Term.is_call(f) == True{} : Bool}) ->
  {Source.Term.redex(bk, q, f, x) == None{} : Maybe<&2, Source.Term>}:
  Call.elim(f, h, z => {Source.Term.redex(bk, q, z, x) == None{} : Maybe<&2, Source.Term>}, q2 => f2 => x2 => {==}, k => {==})

def App.tail.of(w: Source.Walk, +q: Source.Quan, +f: Source.Term, +x: Source.Term, +bk: List<&2, Source.Def>,
  +hw: {Source.Term.walk_call(bk, f) == w : Source.Walk},
  +hf: {Source.Term.is_value(f, True{}, bk) == True{} : Bool},
  ihf: {Source.Term.step(f, bk) == Source.Term.fires(bk, f) : Maybe<&2, Source.Term>},
  ihx: {Source.Maybe.when(Source.Term, Source.Quan.live(q), u => Source.Term.step(x, bk)) == None{} : Maybe<&2, Source.Term>},
  hfa: {Source.Term.fires(bk, Source.Term.App{q, f, x}) == None{} : Maybe<&2, Source.Term>}) ->
  {Source.Term.step.app(q, f, x, bk, u => Source.Term.step(f, bk), u => Source.Term.step(x, bk)) == None{} : Maybe<&2, Source.Term>}:
  match w:
    case Source.Walk.done{u}:
      Empty.absurd({Source.Term.step.app(q, f, x, bk, u => Source.Term.step(f, bk), u => Source.Term.step(x, bk)) == None{} : Maybe<&2, Source.Term>},
        Shared.Maybe.no_none(Source.Term, Source.Term.App{q, u, x},
          Equal.trans(Maybe<&2, Source.Term>, None{}, Source.Term.fires(bk, Source.Term.App{q, f, x}), Some{Source.Term.App{q, u, x}},
            Equal.sym(Maybe<&2, Source.Term>, Source.Term.fires(bk, Source.Term.App{q, f, x}), None{}, hfa),
            Equal.trans(Maybe<&2, Source.Term>, Source.Term.fires(bk, Source.Term.App{q, f, x}),
              Source.Walk.done_term(Walk.snoc(Source.Term.walk_call(bk, f), q, x)), Some{Source.Term.App{q, u, x}},
              Equal.cong(Source.Walk, Maybe<&2, Source.Term>, z => Source.Walk.done_term(z),
                Source.Term.walk_call(bk, Source.Term.App{q, f, x}), Walk.snoc(Source.Term.walk_call(bk, f), q, x),
                Fires.snoc(f, q, x, bk, hf,
                  Eq.rw(Source.Walk, Source.Walk.done{u}, Source.Term.walk_call(bk, f),
                    Equal.sym(Source.Walk, Source.Term.walk_call(bk, f), Source.Walk.done{u}, hw),
                    z => {Source.Walk.is_need(z) == False{} : Bool}, {==}))),
              Equal.cong(Source.Walk, Maybe<&2, Source.Term>, z => Source.Walk.done_term(Walk.snoc(z, q, x)),
                Source.Term.walk_call(bk, f), Source.Walk.done{u}, hw)))))
    case Source.Walk.need{}:
      %Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(f, bk), None{},
        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(f, bk), Source.Term.fires(bk, f), None{}, ihf,
          Equal.cong(Source.Walk, Maybe<&2, Source.Term>, z => Source.Walk.done_term(z), Source.Term.walk_call(bk, f),
            Source.Walk.need{}, hw))) :
        {Source.Term.step.app(q, f, x, bk, u => _, u => Source.Term.step(x, bk)) == None{} : Maybe<&2, Source.Term>}
      %Equal.sym(Bool, Source.Term.is_value(f, False{}, bk), True{},
        Equal.trans(Bool, Source.Term.is_value(f, False{}, bk), Source.Term.stops(bk, f), True{}, Vals.stops(f, bk, hf),
          Equal.cong(Source.Walk, Bool, z => Source.Walk.is_need(z), Source.Term.walk_call(bk, f), Source.Walk.need{}, hw))) :
        {Source.Maybe.when(Source.Term, _, v => Source.Maybe.else(Source.Term,
          Source.Maybe.map_term(Source.Maybe.when(Source.Term, Source.Quan.live(q), u => Source.Term.step(x, bk)), y => Source.Term.App{q, f, y}),
          z => Source.Term.redex(bk, q, f, x))) == None{} : Maybe<&2, Source.Term>}
      %Equal.sym(Maybe<&2, Source.Term>, Source.Maybe.when(Source.Term, Source.Quan.live(q), u => Source.Term.step(x, bk)), None{}, ihx) :
        {Source.Maybe.else(Source.Term, Source.Maybe.map_term(_, y => Source.Term.App{q, f, y}), z => Source.Term.redex(bk, q, f, x)) ==
          None{} : Maybe<&2, Source.Term>}
      Redex.call(f, q, x, bk, Args.is_call(f, bk, hf))
    case Source.Walk.fail{}:
      %Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(f, bk), None{},
        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(f, bk), Source.Term.fires(bk, f), None{}, ihf,
          Equal.cong(Source.Walk, Maybe<&2, Source.Term>, z => Source.Walk.done_term(z), Source.Term.walk_call(bk, f),
            Source.Walk.fail{}, hw))) :
        {Source.Term.step.app(q, f, x, bk, u => _, u => Source.Term.step(x, bk)) == None{} : Maybe<&2, Source.Term>}
      %Equal.sym(Bool, Source.Term.is_value(f, False{}, bk), False{},
        Equal.trans(Bool, Source.Term.is_value(f, False{}, bk), Source.Term.stops(bk, f), False{}, Vals.stops(f, bk, hf),
          Equal.cong(Source.Walk, Bool, z => Source.Walk.is_need(z), Source.Term.walk_call(bk, f), Source.Walk.fail{}, hw))) :
        {Source.Maybe.when(Source.Term, _, v => Source.Maybe.else(Source.Term,
          Source.Maybe.map_term(Source.Maybe.when(Source.Term, Source.Quan.live(q), u => Source.Term.step(x, bk)), y => Source.Term.App{q, f, y}),
          z => Source.Term.redex(bk, q, f, x))) == None{} : Maybe<&2, Source.Term>}
      {==}

# no call fires at App q f x and f is a spine on a def: no step
def App.tail(+q: Source.Quan, +f: Source.Term, +x: Source.Term, +bk: List<&2, Source.Def>,
  hf: {Source.Term.is_value(f, True{}, bk) == True{} : Bool},
  ihf: {Source.Term.step(f, bk) == Source.Term.fires(bk, f) : Maybe<&2, Source.Term>},
  ihx: {Source.Maybe.when(Source.Term, Source.Quan.live(q), u => Source.Term.step(x, bk)) == None{} : Maybe<&2, Source.Term>},
  hfa: {Source.Term.fires(bk, Source.Term.App{q, f, x}) == None{} : Maybe<&2, Source.Term>}) ->
  {Source.Term.step.app(q, f, x, bk, u => Source.Term.step(f, bk), u => Source.Term.step(x, bk)) == None{} : Maybe<&2, Source.Term>}:
  App.tail.of(Source.Term.walk_call(bk, f), q, f, x, bk, {==}, hf, ihf, ihx, hfa)

def Else.self(m: Maybe<&2, Source.Term>, -k: Unit -> Maybe<&2, Source.Term>,
  hk: {m == None{} : Maybe<&2, Source.Term>} -> {k(Unit{}) == None{} : Maybe<&2, Source.Term>}) ->
  {Source.Maybe.else(Source.Term, m, k) == m : Maybe<&2, Source.Term>}:
  match m:
    case Some{u}:
      {==}
    case None{}:
      hk({==})

# when q is live, x is a value and does not step
def App.ihx(q: Source.Quan, -x: Source.Term, -bk: List<&2, Source.Def>,
  ih: {Source.Term.is_value(x, False{}, bk) == True{} : Bool} -> {Source.Term.step(x, bk) == None{} : Maybe<&2, Source.Term>},
  h: {Bool.or(Bool.not(Source.Quan.live(q)), Source.Term.is_value(x, False{}, bk)) == True{} : Bool}) ->
  {Source.Maybe.when(Source.Term, Source.Quan.live(q), u => Source.Term.step(x, bk)) == None{} : Maybe<&2, Source.Term>}:
  match q:
    case Source.Q0{}:
      {==}
    case Source.Q1{}:
      ih(h)
    case Source.Q2{}:
      ih(h)

def App.vals.true(+q: Source.Quan, +f: Source.Term, +x: Source.Term, +bk: List<&2, Source.Def>,
  +h: {Bool.and(Source.Term.is_value(f, True{}, bk), Bool.or(Bool.not(Source.Quan.live(q)), Source.Term.is_value(x, False{}, bk))) == True{} : Bool},
  ihf: {Source.Term.step(f, bk) == Source.Term.fires(bk, f) : Maybe<&2, Source.Term>},
  ihx: {Source.Maybe.when(Source.Term, Source.Quan.live(q), u => Source.Term.step(x, bk)) == None{} : Maybe<&2, Source.Term>}) ->
  {Source.Term.step(Source.Term.App{q, f, x}, bk) == Source.Term.fires(bk, Source.Term.App{q, f, x}) : Maybe<&2, Source.Term>}:
  %Equal.sym(Bool, Bool.and(Source.Term.is_value(f, True{}, bk), Bool.or(Bool.not(Source.Quan.live(q)), Source.Term.is_value(x, False{}, bk))), True{}, h) :
    {Source.Maybe.else(Source.Term, Source.Bool.lazy(Maybe<&2, Source.Term>, _, u => Source.Term.fires(bk, Source.Term.App{q, f, x}), u => None{}),
      u => Source.Term.step.app(q, f, x, bk, w => Source.Term.step(f, bk), w => Source.Term.step(x, bk))) ==
      Source.Term.fires(bk, Source.Term.App{q, f, x}) : Maybe<&2, Source.Term>}
  Else.self(Source.Term.fires(bk, Source.Term.App{q, f, x}),
    u => Source.Term.step.app(q, f, x, bk, w => Source.Term.step(f, bk), w => Source.Term.step(x, bk)),
    hfa => App.tail(q, f, x, bk, SP.Bool.and_left(Source.Term.is_value(f, True{}, bk),
      Bool.or(Bool.not(Source.Quan.live(q)), Source.Term.is_value(x, False{}, bk)), h), ihf, ihx, hfa))

def App.vals.false(+q: Source.Quan, +f: Source.Term, +x: Source.Term, +bk: List<&2, Source.Def>,
  +h: {Bool.and(Source.Term.is_value(f, True{}, bk), Bool.or(Bool.not(Source.Quan.live(q)), Source.Term.is_value(x, False{}, bk))) == True{} : Bool},
  ihf: {Source.Term.step(f, bk) == Source.Term.fires(bk, f) : Maybe<&2, Source.Term>},
  ihx: {Source.Maybe.when(Source.Term, Source.Quan.live(q), u => Source.Term.step(x, bk)) == None{} : Maybe<&2, Source.Term>},
  hs: {Source.Term.stops(bk, Source.Term.App{q, f, x}) == True{} : Bool}) ->
  {Source.Term.step(Source.Term.App{q, f, x}, bk) == None{} : Maybe<&2, Source.Term>}:
  +hfa = Walk.need_done(Source.Term.walk_call(bk, Source.Term.App{q, f, x}), hs)
  %Equal.sym(Bool, Bool.and(Source.Term.is_value(f, True{}, bk), Bool.or(Bool.not(Source.Quan.live(q)), Source.Term.is_value(x, False{}, bk))), True{}, h) :
    {Source.Maybe.else(Source.Term, Source.Bool.lazy(Maybe<&2, Source.Term>, _, u => Source.Term.fires(bk, Source.Term.App{q, f, x}), u => None{}),
      u => Source.Term.step.app(q, f, x, bk, w => Source.Term.step(f, bk), w => Source.Term.step(x, bk))) == None{} : Maybe<&2, Source.Term>}
  %Equal.sym(Maybe<&2, Source.Term>, Source.Term.fires(bk, Source.Term.App{q, f, x}), None{}, hfa) :
    {Source.Maybe.else(Source.Term, _,
      u => Source.Term.step.app(q, f, x, bk, w => Source.Term.step(f, bk), w => Source.Term.step(x, bk))) == None{} : Maybe<&2, Source.Term>}
  App.tail(q, f, x, bk, SP.Bool.and_left(Source.Term.is_value(f, True{}, bk),
    Bool.or(Bool.not(Source.Quan.live(q)), Source.Term.is_value(x, False{}, bk)), h), ihf, ihx, hfa)


def Vals.res(args: Bool, t: Source.Term, +bk: List<&2, Source.Def>) -> Type:
  match args:
    case True{}:
      {Source.Term.step(t, bk) == Source.Term.fires(bk, t) : Maybe<&2, Source.Term>}
    case False{}:
      {Source.Term.step(t, bk) == None{} : Maybe<&2, Source.Term>}

# a value does not step (args: False), and a spine on a def steps by its call
# (args: True)
def Vals.step(t: Source.Term, +args: Bool, +bk: List<&2, Source.Def>, +h: {Source.Term.is_value(t, args, bk) == True{} : Bool}) ->
  Vals.res(args, t, bk):
  match t:
    case Source.Term.Var{+z0}:
      match args:
        case True{}:
          Shared.Bool.absurd(Vals.res(True{}, Source.Term.Var{z0}, bk), h)
        case False{}:
          Shared.Bool.absurd(Vals.res(False{}, Source.Term.Var{z0}, bk), h)
    case Source.Term.Ref{+z0}:
      match args:
        case True{}:
          {==}
        case False{}:
          Walk.need_done(Source.Term.walk_call(bk, Source.Term.Ref{z0}), h)
    case Source.Term.Ann{+z0, +z1}:
      match args:
        case True{}:
          Shared.Bool.absurd(Vals.res(True{}, Source.Term.Ann{z0, z1}, bk), h)
        case False{}:
          Shared.Bool.absurd(Vals.res(False{}, Source.Term.Ann{z0, z1}, bk), h)
    case Source.Term.Let{+z0, +z1, +z2}:
      match args:
        case True{}:
          Shared.Bool.absurd(Vals.res(True{}, Source.Term.Let{z0, z1, z2}, bk), h)
        case False{}:
          Shared.Bool.absurd(Vals.res(False{}, Source.Term.Let{z0, z1, z2}, bk), h)
    case Source.Term.Typ{+z0}:
      match args:
        case True{}:
          Shared.Bool.absurd(Vals.res(True{}, Source.Term.Typ{z0}, bk), h)
        case False{}:
          {==}
    case Source.Term.Min{+z0, +z1}:
      match args:
        case True{}:
          Shared.Bool.absurd(Vals.res(True{}, Source.Term.Min{z0, z1}, bk), h)
        case False{}:
          Shared.Bool.absurd(Vals.res(False{}, Source.Term.Min{z0, z1}, bk), h)
    case Source.Term.All{+z0, +z1, +z2}:
      match args:
        case True{}:
          Shared.Bool.absurd(Vals.res(True{}, Source.Term.All{z0, z1, z2}, bk), h)
        case False{}:
          {==}
    case Source.Term.Lam{+z0, +z1}:
      match args:
        case True{}:
          Shared.Bool.absurd(Vals.res(True{}, Source.Term.Lam{z0, z1}, bk), h)
        case False{}:
          {==}
    case Source.Term.App{+z0, +z1, +z2}:
      match args:
        case True{}:
          App.vals.true(z0, z1, z2, bk, h, Vals.step(z1, True{}, bk, SP.Bool.and_left(Source.Term.is_value(z1, True{}, bk), Bool.or(Bool.not(Source.Quan.live(z0)), Source.Term.is_value(z2, False{}, bk)), h)),
            App.ihx(z0, z2, bk,
              hx => Vals.step(z2, False{}, bk, hx), SP.Bool.and_right(Source.Term.is_value(z1, True{}, bk), Bool.or(Bool.not(Source.Quan.live(z0)), Source.Term.is_value(z2, False{}, bk)), h)))
        case False{}:
          App.vals.false(z0, z1, z2, bk, SP.Bool.and_left(Bool.and(Source.Term.is_value(z1, True{}, bk), Bool.or(Bool.not(Source.Quan.live(z0)), Source.Term.is_value(z2, False{}, bk))), Source.Term.stops(bk, Source.Term.App{z0, z1, z2}), h), Vals.step(z1, True{}, bk, SP.Bool.and_left(Source.Term.is_value(z1, True{}, bk), Bool.or(Bool.not(Source.Quan.live(z0)), Source.Term.is_value(z2, False{}, bk)), SP.Bool.and_left(Bool.and(Source.Term.is_value(z1, True{}, bk), Bool.or(Bool.not(Source.Quan.live(z0)), Source.Term.is_value(z2, False{}, bk))), Source.Term.stops(bk, Source.Term.App{z0, z1, z2}), h))),
            App.ihx(z0, z2, bk,
              hx => Vals.step(z2, False{}, bk, hx), SP.Bool.and_right(Source.Term.is_value(z1, True{}, bk), Bool.or(Bool.not(Source.Quan.live(z0)), Source.Term.is_value(z2, False{}, bk)), SP.Bool.and_left(Bool.and(Source.Term.is_value(z1, True{}, bk), Bool.or(Bool.not(Source.Quan.live(z0)), Source.Term.is_value(z2, False{}, bk))), Source.Term.stops(bk, Source.Term.App{z0, z1, z2}), h))), SP.Bool.and_right(Bool.and(Source.Term.is_value(z1, True{}, bk), Bool.or(Bool.not(Source.Quan.live(z0)), Source.Term.is_value(z2, False{}, bk))), Source.Term.stops(bk, Source.Term.App{z0, z1, z2}), h))
    case Source.Term.Sig{+z0, +z1, +z2}:
      match args:
        case True{}:
          Shared.Bool.absurd(Vals.res(True{}, Source.Term.Sig{z0, z1, z2}, bk), h)
        case False{}:
          {==}
    case Source.Term.Tup{+z0, +z1, +z2}:
      match z0:
        case Source.Q0{}:
          match args:
            case True{}:
              Shared.Bool.absurd(Vals.res(True{}, Source.Term.Tup{Source.Q0{}, z1, z2}, bk), h)
            case False{}:
              %Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(z2, bk), None{}, Vals.step(z2, False{}, bk, SP.Bool.and_right(True{}, Source.Term.is_value(z2, False{}, bk), h))) :
                {Source.Term.step.tup(Source.Q0{}, z1, z2, bk, u => Source.Term.step(z1, bk), u => _) == None{} : Maybe<&2, Source.Term>}
              {==}
        case Source.Q1{}:
          match args:
            case True{}:
              Shared.Bool.absurd(Vals.res(True{}, Source.Term.Tup{Source.Q1{}, z1, z2}, bk), h)
            case False{}:
              %Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(z2, bk), None{}, Vals.step(z2, False{}, bk, SP.Bool.and_right(Source.Term.is_value(z1, False{}, bk), Source.Term.is_value(z2, False{}, bk), h))) :
                {Source.Term.step.tup(Source.Q1{}, z1, z2, bk, u => Source.Term.step(z1, bk), u => _) == None{} : Maybe<&2, Source.Term>}
              %Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(z1, bk), None{}, Vals.step(z1, False{}, bk, SP.Bool.and_left(Source.Term.is_value(z1, False{}, bk), Source.Term.is_value(z2, False{}, bk), h))) :
                {Source.Term.step.tup(Source.Q1{}, z1, z2, bk, u => _, u => None{}) == None{} : Maybe<&2, Source.Term>}
              %Equal.sym(Bool, Source.Term.is_value(z1, False{}, bk), True{}, SP.Bool.and_left(Source.Term.is_value(z1, False{}, bk), Source.Term.is_value(z2, False{}, bk), h)) :
                {Source.Maybe.when(Source.Term, _, w => Source.Maybe.map_term(None{}, z => Source.Term.Tup{Source.Q1{}, z1, z})) == None{} : Maybe<&2, Source.Term>}
              {==}
        case Source.Q2{}:
          match args:
            case True{}:
              Shared.Bool.absurd(Vals.res(True{}, Source.Term.Tup{Source.Q2{}, z1, z2}, bk), h)
            case False{}:
              %Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(z2, bk), None{}, Vals.step(z2, False{}, bk, SP.Bool.and_right(Source.Term.is_value(z1, False{}, bk), Source.Term.is_value(z2, False{}, bk), h))) :
                {Source.Term.step.tup(Source.Q2{}, z1, z2, bk, u => Source.Term.step(z1, bk), u => _) == None{} : Maybe<&2, Source.Term>}
              %Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(z1, bk), None{}, Vals.step(z1, False{}, bk, SP.Bool.and_left(Source.Term.is_value(z1, False{}, bk), Source.Term.is_value(z2, False{}, bk), h))) :
                {Source.Term.step.tup(Source.Q2{}, z1, z2, bk, u => _, u => None{}) == None{} : Maybe<&2, Source.Term>}
              %Equal.sym(Bool, Source.Term.is_value(z1, False{}, bk), True{}, SP.Bool.and_left(Source.Term.is_value(z1, False{}, bk), Source.Term.is_value(z2, False{}, bk), h)) :
                {Source.Maybe.when(Source.Term, _, w => Source.Maybe.map_term(None{}, z => Source.Term.Tup{Source.Q2{}, z1, z})) == None{} : Maybe<&2, Source.Term>}
              {==}
    case Source.Term.Prj{+z0}:
      match args:
        case True{}:
          Shared.Bool.absurd(Vals.res(True{}, Source.Term.Prj{z0}, bk), h)
        case False{}:
          {==}
    case Source.Term.Enu{+z0}:
      match args:
        case True{}:
          Shared.Bool.absurd(Vals.res(True{}, Source.Term.Enu{z0}, bk), h)
        case False{}:
          {==}
    case Source.Term.Lab{+z0}:
      match args:
        case True{}:
          Shared.Bool.absurd(Vals.res(True{}, Source.Term.Lab{z0}, bk), h)
        case False{}:
          {==}
    case Source.Term.Mat{+z0, +z1, +z2}:
      match args:
        case True{}:
          Shared.Bool.absurd(Vals.res(True{}, Source.Term.Mat{z0, z1, z2}, bk), h)
        case False{}:
          {==}
    case Source.Term.Efq{}:
      match args:
        case True{}:
          Shared.Bool.absurd(Vals.res(True{}, Source.Term.Efq{}, bk), h)
        case False{}:
          {==}
    case Source.Term.Eql{+z0, +z1, +z2}:
      match args:
        case True{}:
          Shared.Bool.absurd(Vals.res(True{}, Source.Term.Eql{z0, z1, z2}, bk), h)
        case False{}:
          {==}
    case Source.Term.Rfl{}:
      match args:
        case True{}:
          Shared.Bool.absurd(Vals.res(True{}, Source.Term.Rfl{}, bk), h)
        case False{}:
          {==}
    case Source.Term.Rwt{+z0, +z1, +z2}:
      match args:
        case True{}:
          Shared.Bool.absurd(Vals.res(True{}, Source.Term.Rwt{z0, z1, z2}, bk), h)
        case False{}:
          Shared.Bool.absurd(Vals.res(False{}, Source.Term.Rwt{z0, z1, z2}, bk), h)
# Frames
# ======

def Map.id(m: Maybe<&2, Source.Term>) -> {Source.Maybe.map_term(m, z => z) == m : Maybe<&2, Source.Term>}:
  match m:
    case Some{u}:
      {==}
    case None{}:
      {==}

def Map.map(m: Maybe<&2, Source.Term>, -g: Source.Term -> Source.Term, -h: Source.Term -> Source.Term) ->
  {Source.Maybe.map_term(Source.Maybe.map_term(m, g), h) == Source.Maybe.map_term(m, z => h(g(z))) : Maybe<&2, Source.Term>}:
  match m:
    case Some{u}:
      {==}
    case None{}:
      {==}

def Else.none(m: Maybe<&2, Source.Term>) -> {Source.Maybe.else(Source.Term, m, w => None{}) == m : Maybe<&2, Source.Term>}:
  match m:
    case Some{u}:
      {==}
    case None{}:
      {==}

def Need.snoc(w: Source.Walk, -q: Source.Quan, -x: Source.Term, h: {Source.Walk.is_need(w) == False{} : Bool}) ->
  {Source.Walk.is_need(Walk.snoc(w, q, x)) == False{} : Bool}:
  match w:
    case Source.Walk.done{u}:
      {==}
    case Source.Walk.need{}:
      Walk.need_false({Source.Walk.is_need(Walk.snoc(Source.Walk.need{}, q, x)) == False{} : Bool}, h)
    case Source.Walk.fail{}:
      {==}

def Rfl.no(u: Source.Term, -bk: List<&2, Source.Def>, h: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) ->
  {Source.Term.is_rfl(u) == False{} : Bool}:
  match u:
    case Source.Term.Var{+z0}:
      {==}
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
      Empty.absurd({Source.Term.is_rfl(Source.Term.Rfl{}) == False{} : Bool}, Bool.true_false(h))
    case Source.Term.Rwt{+z0, +z1, +z2}:
      {==}

def Meet.no(a: Source.Term, u: Source.Term, -bk: List<&2, Source.Def>, h: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) ->
  {Source.Term.meet(a, u) == None{} : Maybe<&2, Source.Term>}:
  match a:
    case Source.Term.Var{+z0}:
      {==}
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
      match u:
        case Source.Term.Var{+r0}:
          {==}
        case Source.Term.Ref{+r0}:
          {==}
        case Source.Term.Ann{+r0, +r1}:
          {==}
        case Source.Term.Let{+r0, +r1, +r2}:
          {==}
        case Source.Term.Typ{+r0}:
          {==}
        case Source.Term.Min{+r0, +r1}:
          {==}
        case Source.Term.All{+r0, +r1, +r2}:
          {==}
        case Source.Term.Lam{+r0, +r1}:
          {==}
        case Source.Term.App{+r0, +r1, +r2}:
          {==}
        case Source.Term.Sig{+r0, +r1, +r2}:
          {==}
        case Source.Term.Tup{+r0, +r1, +r2}:
          {==}
        case Source.Term.Prj{+r0}:
          {==}
        case Source.Term.Enu{+r0}:
          {==}
        case Source.Term.Lab{+r0}:
          Empty.absurd({Source.Term.meet(Source.Term.Lab{z0}, Source.Term.Lab{r0}) == None{} : Maybe<&2, Source.Term>}, Bool.true_false(h))
        case Source.Term.Mat{+r0, +r1, +r2}:
          {==}
        case Source.Term.Efq{}:
          {==}
        case Source.Term.Eql{+r0, +r1, +r2}:
          {==}
        case Source.Term.Rfl{}:
          {==}
        case Source.Term.Rwt{+r0, +r1, +r2}:
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

# a live redex whose argument is not a value: no step
def Redex.no(q: Source.Quan, f: Source.Term, u: Source.Term, +bk: List<&2, Source.Def>,
  hq: {Source.Quan.live(q) == True{} : Bool}, +h: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) ->
  {Source.Term.redex(bk, q, f, u) == None{} : Maybe<&2, Source.Term>}:
  match q:
    case Source.Q0{}:
      Empty.absurd({Source.Term.redex(bk, Source.Q0{}, f, u) == None{} : Maybe<&2, Source.Term>}, Shared.Bool.no(hq))
    case Source.Q1{}:
      match f:
        case Source.Term.Var{+z0}:
          {==}
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
          %Equal.sym(Bool, Source.Term.is_value(u, False{}, bk), False{}, h) :
            {Source.Maybe.when(Source.Term, Bool.and(Bool.and(Source.Bool.is_eq(Source.Quan.live(z0), True{}), _),
              Bool.or(Bool.not(Source.Quan.is_q2(z0)), Source.Term.is_data(u))), w => Some{Source.Term.sub(z1, 0n, Source.Sub.one{u})}) == None{} : Maybe<&2, Source.Term>}
          %Equal.sym(Bool, Bool.and(Source.Bool.is_eq(Source.Quan.live(z0), True{}), False{}), False{}, Bool.and_false(Source.Bool.is_eq(Source.Quan.live(z0), True{}))) :
            {Source.Maybe.when(Source.Term, Bool.and(_, Bool.or(Bool.not(Source.Quan.is_q2(z0)), Source.Term.is_data(u))),
              w => Some{Source.Term.sub(z1, 0n, Source.Sub.one{u})}) == None{} : Maybe<&2, Source.Term>}
          {==}
        case Source.Term.App{+z0, +z1, +z2}:
          {==}
        case Source.Term.Sig{+z0, +z1, +z2}:
          {==}
        case Source.Term.Tup{+z0, +z1, +z2}:
          {==}
        case Source.Term.Prj{+z0}:
          match u:
            case Source.Term.Var{+r0}:
              {==}
            case Source.Term.Ref{+r0}:
              {==}
            case Source.Term.Ann{+r0, +r1}:
              {==}
            case Source.Term.Let{+r0, +r1, +r2}:
              {==}
            case Source.Term.Typ{+r0}:
              {==}
            case Source.Term.Min{+r0, +r1}:
              {==}
            case Source.Term.All{+r0, +r1, +r2}:
              {==}
            case Source.Term.Lam{+r0, +r1}:
              {==}
            case Source.Term.App{+r0, +r1, +r2}:
              {==}
            case Source.Term.Sig{+r0, +r1, +r2}:
              {==}
            case Source.Term.Tup{+r0, +r1, +r2}:
              %Equal.sym(Bool, Source.Term.is_value(Source.Term.Tup{r0, r1, r2}, False{}, bk), False{}, h) :
                {Source.Maybe.when(Source.Term, _, w => Some{Source.Term.App{Source.Q1{}, Source.Term.App{Source.Quan.fld(r0, Source.Q1{}), z0, r1}, r2}}) == None{} : Maybe<&2, Source.Term>}
              {==}
            case Source.Term.Prj{+r0}:
              {==}
            case Source.Term.Enu{+r0}:
              {==}
            case Source.Term.Lab{+r0}:
              {==}
            case Source.Term.Mat{+r0, +r1, +r2}:
              {==}
            case Source.Term.Efq{}:
              {==}
            case Source.Term.Eql{+r0, +r1, +r2}:
              {==}
            case Source.Term.Rfl{}:
              {==}
            case Source.Term.Rwt{+r0, +r1, +r2}:
              {==}
        case Source.Term.Enu{+z0}:
          {==}
        case Source.Term.Lab{+z0}:
          {==}
        case Source.Term.Mat{+z0, +z1, +z2}:
          match u:
            case Source.Term.Var{+r0}:
              {==}
            case Source.Term.Ref{+r0}:
              {==}
            case Source.Term.Ann{+r0, +r1}:
              {==}
            case Source.Term.Let{+r0, +r1, +r2}:
              {==}
            case Source.Term.Typ{+r0}:
              {==}
            case Source.Term.Min{+r0, +r1}:
              {==}
            case Source.Term.All{+r0, +r1, +r2}:
              {==}
            case Source.Term.Lam{+r0, +r1}:
              {==}
            case Source.Term.App{+r0, +r1, +r2}:
              {==}
            case Source.Term.Sig{+r0, +r1, +r2}:
              {==}
            case Source.Term.Tup{+r0, +r1, +r2}:
              {==}
            case Source.Term.Prj{+r0}:
              {==}
            case Source.Term.Enu{+r0}:
              {==}
            case Source.Term.Lab{+r0}:
              Empty.absurd({Source.Term.redex(bk, Source.Q1{}, Source.Term.Mat{z0, z1, z2}, Source.Term.Lab{r0}) == None{} : Maybe<&2, Source.Term>}, Bool.true_false(h))
            case Source.Term.Mat{+r0, +r1, +r2}:
              {==}
            case Source.Term.Efq{}:
              {==}
            case Source.Term.Eql{+r0, +r1, +r2}:
              {==}
            case Source.Term.Rfl{}:
              {==}
            case Source.Term.Rwt{+r0, +r1, +r2}:
              {==}
        case Source.Term.Efq{}:
          {==}
        case Source.Term.Eql{+z0, +z1, +z2}:
          {==}
        case Source.Term.Rfl{}:
          {==}
        case Source.Term.Rwt{+z0, +z1, +z2}:
          {==}
    case Source.Q2{}:
      match f:
        case Source.Term.Var{+z0}:
          {==}
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
          %Equal.sym(Bool, Source.Term.is_value(u, False{}, bk), False{}, h) :
            {Source.Maybe.when(Source.Term, Bool.and(Bool.and(Source.Bool.is_eq(Source.Quan.live(z0), True{}), _),
              Bool.or(Bool.not(Source.Quan.is_q2(z0)), Source.Term.is_data(u))), w => Some{Source.Term.sub(z1, 0n, Source.Sub.one{u})}) == None{} : Maybe<&2, Source.Term>}
          %Equal.sym(Bool, Bool.and(Source.Bool.is_eq(Source.Quan.live(z0), True{}), False{}), False{}, Bool.and_false(Source.Bool.is_eq(Source.Quan.live(z0), True{}))) :
            {Source.Maybe.when(Source.Term, Bool.and(_, Bool.or(Bool.not(Source.Quan.is_q2(z0)), Source.Term.is_data(u))),
              w => Some{Source.Term.sub(z1, 0n, Source.Sub.one{u})}) == None{} : Maybe<&2, Source.Term>}
          {==}
        case Source.Term.App{+z0, +z1, +z2}:
          {==}
        case Source.Term.Sig{+z0, +z1, +z2}:
          {==}
        case Source.Term.Tup{+z0, +z1, +z2}:
          {==}
        case Source.Term.Prj{+z0}:
          match u:
            case Source.Term.Var{+r0}:
              {==}
            case Source.Term.Ref{+r0}:
              {==}
            case Source.Term.Ann{+r0, +r1}:
              {==}
            case Source.Term.Let{+r0, +r1, +r2}:
              {==}
            case Source.Term.Typ{+r0}:
              {==}
            case Source.Term.Min{+r0, +r1}:
              {==}
            case Source.Term.All{+r0, +r1, +r2}:
              {==}
            case Source.Term.Lam{+r0, +r1}:
              {==}
            case Source.Term.App{+r0, +r1, +r2}:
              {==}
            case Source.Term.Sig{+r0, +r1, +r2}:
              {==}
            case Source.Term.Tup{+r0, +r1, +r2}:
              %Equal.sym(Bool, Source.Term.is_value(Source.Term.Tup{r0, r1, r2}, False{}, bk), False{}, h) :
                {Source.Maybe.when(Source.Term, _, w => Some{Source.Term.App{Source.Q2{}, Source.Term.App{Source.Quan.fld(r0, Source.Q2{}), z0, r1}, r2}}) == None{} : Maybe<&2, Source.Term>}
              {==}
            case Source.Term.Prj{+r0}:
              {==}
            case Source.Term.Enu{+r0}:
              {==}
            case Source.Term.Lab{+r0}:
              {==}
            case Source.Term.Mat{+r0, +r1, +r2}:
              {==}
            case Source.Term.Efq{}:
              {==}
            case Source.Term.Eql{+r0, +r1, +r2}:
              {==}
            case Source.Term.Rfl{}:
              {==}
            case Source.Term.Rwt{+r0, +r1, +r2}:
              {==}
        case Source.Term.Enu{+z0}:
          {==}
        case Source.Term.Lab{+z0}:
          {==}
        case Source.Term.Mat{+z0, +z1, +z2}:
          match u:
            case Source.Term.Var{+r0}:
              {==}
            case Source.Term.Ref{+r0}:
              {==}
            case Source.Term.Ann{+r0, +r1}:
              {==}
            case Source.Term.Let{+r0, +r1, +r2}:
              {==}
            case Source.Term.Typ{+r0}:
              {==}
            case Source.Term.Min{+r0, +r1}:
              {==}
            case Source.Term.All{+r0, +r1, +r2}:
              {==}
            case Source.Term.Lam{+r0, +r1}:
              {==}
            case Source.Term.App{+r0, +r1, +r2}:
              {==}
            case Source.Term.Sig{+r0, +r1, +r2}:
              {==}
            case Source.Term.Tup{+r0, +r1, +r2}:
              {==}
            case Source.Term.Prj{+r0}:
              {==}
            case Source.Term.Enu{+r0}:
              {==}
            case Source.Term.Lab{+r0}:
              Empty.absurd({Source.Term.redex(bk, Source.Q2{}, Source.Term.Mat{z0, z1, z2}, Source.Term.Lab{r0}) == None{} : Maybe<&2, Source.Term>}, Bool.true_false(h))
            case Source.Term.Mat{+r0, +r1, +r2}:
              {==}
            case Source.Term.Efq{}:
              {==}
            case Source.Term.Eql{+r0, +r1, +r2}:
              {==}
            case Source.Term.Rfl{}:
              {==}
            case Source.Term.Rwt{+r0, +r1, +r2}:
              {==}
        case Source.Term.Efq{}:
          {==}
        case Source.Term.Eql{+z0, +z1, +z2}:
          {==}
        case Source.Term.Rfl{}:
          {==}
        case Source.Term.Rwt{+z0, +z1, +z2}:
          {==}

# the step of a frame's term with u inside it, when u is not a value
def Fr.res(fr: Machine.Fr, u: Source.Term, +bk: List<&2, Source.Def>) -> Type:
  {Source.Term.is_value(Fr.plug(fr, u), False{}, bk) == False{} : Bool} & {Source.Term.step(Fr.plug(fr, u), bk) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Fr.plug(fr, z)) : Maybe<&2, Source.Term>}

def Ctx.arg_walk(w: Source.Walk, +q: Source.Quan, +x: Source.Term, h: {Source.Walk.is_need(w) == False{} : Bool}) ->
  {Source.Maybe.else(Source.Term, Source.Walk.done_term(Walk.snoc(w, q, x)),
    v => Source.Maybe.map_term(Source.Walk.done_term(w), z => Source.Term.App{q, z, x})) ==
    Source.Maybe.map_term(Source.Walk.done_term(w), z => Source.Term.App{q, z, x}) : Maybe<&2, Source.Term>}:
  match w:
    case Source.Walk.done{t}:
      {==}
    case Source.Walk.need{}:
      Walk.need_false({Source.Maybe.else(Source.Term, Source.Walk.done_term(Walk.snoc(Source.Walk.need{}, q, x)),
        v => Source.Maybe.map_term(Source.Walk.done_term(Source.Walk.need{}), z => Source.Term.App{q, z, x})) ==
        Source.Maybe.map_term(Source.Walk.done_term(Source.Walk.need{}), z => Source.Term.App{q, z, x}) : Maybe<&2, Source.Term>}, h)
    case Source.Walk.fail{}:
      {==}

def Ctx.arg_call(c: Bool, +q: Source.Quan, +u: Source.Term, +x: Source.Term, +bk: List<&2, Source.Def>,
  +hc: {Bool.and(Source.Term.is_value(u, True{}, bk), Bool.or(Bool.not(Source.Quan.live(q)), Source.Term.is_value(x, False{}, bk))) == c : Bool},
  hu: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) ->
  {Source.Maybe.else(Source.Term, Source.Bool.lazy(Maybe<&2, Source.Term>, c, w => Source.Term.fires(bk, Source.Term.App{q, u, x}), w => None{}),
    w => Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{q, z, x})) ==
    Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{q, z, x}) : Maybe<&2, Source.Term>}:
  match c:
    case False{}:
      {==}
    case True{}:
      +hv = SP.Bool.and_left(Source.Term.is_value(u, True{}, bk), Bool.or(Bool.not(Source.Quan.live(q)), Source.Term.is_value(x, False{}, bk)), hc)
      +hn = Equal.trans(Bool, Source.Walk.is_need(Source.Term.walk_call(bk, u)), Source.Term.is_value(u, False{}, bk), False{},
        Equal.sym(Bool, Source.Term.is_value(u, False{}, bk), Source.Term.stops(bk, u), Vals.stops(u, bk, hv)), hu)
      %Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(u, bk), Source.Term.fires(bk, u), Vals.step(u, True{}, bk, hv)) :
        {Source.Maybe.else(Source.Term, Source.Term.fires(bk, Source.Term.App{q, u, x}),
          w => Source.Maybe.map_term(_, z => Source.Term.App{q, z, x})) ==
          Source.Maybe.map_term(_, z => Source.Term.App{q, z, x}) : Maybe<&2, Source.Term>}
      %Equal.sym(Source.Walk, Source.Term.walk_call(bk, Source.Term.App{q, u, x}), Walk.snoc(Source.Term.walk_call(bk, u), q, x),
        Fires.snoc(u, q, x, bk, hv, hn)) :
        {Source.Maybe.else(Source.Term, Source.Walk.done_term(_),
          w => Source.Maybe.map_term(Source.Term.fires(bk, u), z => Source.Term.App{q, z, x})) ==
          Source.Maybe.map_term(Source.Term.fires(bk, u), z => Source.Term.App{q, z, x}) : Maybe<&2, Source.Term>}
      Ctx.arg_walk(Source.Term.walk_call(bk, u), q, x, hn)

def Ctx.arg_nv(c: Bool, +q: Source.Quan, +u: Source.Term, +x: Source.Term, +bk: List<&2, Source.Def>,
  +hc: {Source.Term.is_value(u, True{}, bk) == c : Bool}, hu: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) ->
  {Source.Term.is_value(Source.Term.App{q, u, x}, False{}, bk) == False{} : Bool}:
  match c:
    case False{}:
      %Equal.sym(Bool, Source.Term.is_value(u, True{}, bk), False{}, hc) :
        {Bool.and(Bool.and(_, Bool.or(Bool.not(Source.Quan.live(q)), Source.Term.is_value(x, False{}, bk))),
          Source.Term.stops(bk, Source.Term.App{q, u, x})) == False{} : Bool}
      {==}
    case True{}:
      +hn = Equal.trans(Bool, Source.Walk.is_need(Source.Term.walk_call(bk, u)), Source.Term.is_value(u, False{}, bk), False{},
        Equal.sym(Bool, Source.Term.is_value(u, False{}, bk), Source.Term.stops(bk, u), Vals.stops(u, bk, hc)), hu)
      %Equal.sym(Bool, Source.Term.stops(bk, Source.Term.App{q, u, x}), False{},
        Equal.trans(Bool, Source.Walk.is_need(Source.Term.walk_call(bk, Source.Term.App{q, u, x})),
          Source.Walk.is_need(Walk.snoc(Source.Term.walk_call(bk, u), q, x)), False{},
          Equal.cong(Source.Walk, Bool, z => Source.Walk.is_need(z), Source.Term.walk_call(bk, Source.Term.App{q, u, x}),
            Walk.snoc(Source.Term.walk_call(bk, u), q, x), Fires.snoc(u, q, x, bk, hc, hn)),
          Need.snoc(Source.Term.walk_call(bk, u), q, x, hn))) :
        {Bool.and(Bool.and(Source.Term.is_value(u, True{}, bk), Bool.or(Bool.not(Source.Quan.live(q)), Source.Term.is_value(x, False{}, bk))),
          _) == False{} : Bool}
      Bool.and_false(Bool.and(Source.Term.is_value(u, True{}, bk), Bool.or(Bool.not(Source.Quan.live(q)), Source.Term.is_value(x, False{}, bk))))

def Ctx.app_tail(+q: Source.Quan, +u: Source.Term, +x: Source.Term, +bk: List<&2, Source.Def>,
  hu: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) ->
  {Source.Term.step.app(q, u, x, bk, w => Source.Term.step(u, bk), w => Source.Term.step(x, bk)) ==
    Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{q, z, x}) : Maybe<&2, Source.Term>}:
  %Equal.sym(Bool, Source.Term.is_value(u, False{}, bk), False{}, hu) :
    {Source.Maybe.else(Source.Term, Source.Maybe.map_term(Source.Term.step(u, bk), g => Source.Term.App{q, g, x}),
      w => Source.Maybe.when(Source.Term, _, v => Source.Maybe.else(Source.Term,
        Source.Maybe.map_term(Source.Maybe.when(Source.Term, Source.Quan.live(q), y => Source.Term.step(x, bk)), y => Source.Term.App{q, u, y}),
        z => Source.Term.redex(bk, q, u, x)))) ==
      Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{q, z, x}) : Maybe<&2, Source.Term>}
  Else.none(Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{q, z, x}))

def Ctx.arg_step(+q: Source.Quan, +u: Source.Term, +x: Source.Term, +bk: List<&2, Source.Def>,
  +hu: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) ->
  {Source.Term.step(Source.Term.App{q, u, x}, bk) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{q, z, x}) : Maybe<&2, Source.Term>}:
  %Equal.sym(Maybe<&2, Source.Term>, Source.Term.step.app(q, u, x, bk, w => Source.Term.step(u, bk), w => Source.Term.step(x, bk)),
    Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{q, z, x}), Ctx.app_tail(q, u, x, bk, hu)) :
    {Source.Maybe.else(Source.Term, Source.Term.call(bk, q, u, x), w => _) ==
      Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{q, z, x}) : Maybe<&2, Source.Term>}
  Ctx.arg_call(Bool.and(Source.Term.is_value(u, True{}, bk), Bool.or(Bool.not(Source.Quan.live(q)), Source.Term.is_value(x, False{}, bk))),
    q, u, x, bk, {==}, hu)

# u under App q _ x
def Ctx.arg(+q: Source.Quan, +u: Source.Term, +x: Source.Term, +bk: List<&2, Source.Def>,
  +hu: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) ->
  {Source.Term.is_value(Source.Term.App{q, u, x}, False{}, bk) == False{} : Bool} & {Source.Term.step(Source.Term.App{q, u, x}, bk) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{q, z, x}) : Maybe<&2, Source.Term>}:
  (Ctx.arg_nv(Source.Term.is_value(u, True{}, bk), q, u, x, bk, {==}, hu),
    Ctx.arg_step(q, u, x, bk, hu))

def Ctx.fun_nv(-q: Source.Quan, +f: Source.Term, +u: Source.Term, +bk: List<&2, Source.Def>, +hu: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) ->
  {Bool.and(Bool.and(Source.Term.is_value(f, True{}, bk), Source.Term.is_value(u, False{}, bk)), Source.Term.stops(bk, Source.Term.App{q, f, u})) == False{} : Bool}:
  Eq.rw(Bool, False{}, Source.Term.is_value(u, False{}, bk), Equal.sym(Bool, Source.Term.is_value(u, False{}, bk), False{}, hu),
    z => {Bool.and(Bool.and(Source.Term.is_value(f, True{}, bk), z), Source.Term.stops(bk, Source.Term.App{q, f, u})) == False{} : Bool},
    Eq.rw(Bool, False{}, Bool.and(Source.Term.is_value(f, True{}, bk), False{}),
      Equal.sym(Bool, Bool.and(Source.Term.is_value(f, True{}, bk), False{}), False{}, Bool.and_false(Source.Term.is_value(f, True{}, bk))),
      z => {Bool.and(z, Source.Term.stops(bk, Source.Term.App{q, f, u})) == False{} : Bool}, {==}))

def Ctx.fun_step(q: Source.Quan, +f: Source.Term, +u: Source.Term, +bk: List<&2, Source.Def>,
  hq: {Source.Quan.live(q) == True{} : Bool}, +hf: {Source.Term.is_value(f, False{}, bk) == True{} : Bool}, +hu: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) ->
  {Source.Term.step(Source.Term.App{q, f, u}, bk) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{q, f, z}) : Maybe<&2, Source.Term>}:
  match q:
    case Source.Q0{}:
      Empty.absurd({Source.Term.step(Source.Term.App{Source.Q0{}, f, u}, bk) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{Source.Q0{}, f, z}) : Maybe<&2, Source.Term>}, Shared.Bool.no(hq))
    case Source.Q1{}:
      %Equal.sym(Bool, Source.Term.is_value(u, False{}, bk), False{}, hu) :
        {Source.Maybe.else(Source.Term, Source.Bool.lazy(Maybe<&2, Source.Term>, Bool.and(Source.Term.is_value(f, True{}, bk), _),
          w => Source.Term.fires(bk, Source.Term.App{Source.Q1{}, f, u}), w => None{}), w => Source.Term.step.app(Source.Q1{}, f, u, bk, w => Source.Term.step(f, bk), w => Source.Term.step(u, bk))) ==
          Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{Source.Q1{}, f, z}) : Maybe<&2, Source.Term>}
      %Equal.sym(Bool, Bool.and(Source.Term.is_value(f, True{}, bk), False{}), False{}, Bool.and_false(Source.Term.is_value(f, True{}, bk))) :
        {Source.Maybe.else(Source.Term, Source.Bool.lazy(Maybe<&2, Source.Term>, _,
          w => Source.Term.fires(bk, Source.Term.App{Source.Q1{}, f, u}), w => None{}), w => Source.Term.step.app(Source.Q1{}, f, u, bk, w => Source.Term.step(f, bk), w => Source.Term.step(u, bk))) ==
          Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{Source.Q1{}, f, z}) : Maybe<&2, Source.Term>}
      %Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(f, bk), None{}, Vals.step(f, False{}, bk, hf)) :
        {Source.Term.step.app(Source.Q1{}, f, u, bk, w => _, w => Source.Term.step(u, bk)) ==
          Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{Source.Q1{}, f, z}) : Maybe<&2, Source.Term>}
      %Equal.sym(Bool, Source.Term.is_value(f, False{}, bk), True{}, hf) :
        {Source.Maybe.when(Source.Term, _, v => Source.Maybe.else(Source.Term,
          Source.Maybe.map_term(Source.Maybe.when(Source.Term, Source.Quan.live(Source.Q1{}), y => Source.Term.step(u, bk)), y => Source.Term.App{Source.Q1{}, f, y}),
          z => Source.Term.redex(bk, Source.Q1{}, f, u))) ==
          Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{Source.Q1{}, f, z}) : Maybe<&2, Source.Term>}
      %Equal.sym(Maybe<&2, Source.Term>, Source.Term.redex(bk, Source.Q1{}, f, u), None{}, Redex.no(Source.Q1{}, f, u, bk, {==}, hu)) :
        {Source.Maybe.else(Source.Term, Source.Maybe.map_term(Source.Term.step(u, bk), y => Source.Term.App{Source.Q1{}, f, y}), z => _) ==
          Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{Source.Q1{}, f, z}) : Maybe<&2, Source.Term>}
      Else.none(Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{Source.Q1{}, f, z}))
    case Source.Q2{}:
      %Equal.sym(Bool, Source.Term.is_value(u, False{}, bk), False{}, hu) :
        {Source.Maybe.else(Source.Term, Source.Bool.lazy(Maybe<&2, Source.Term>, Bool.and(Source.Term.is_value(f, True{}, bk), _),
          w => Source.Term.fires(bk, Source.Term.App{Source.Q2{}, f, u}), w => None{}), w => Source.Term.step.app(Source.Q2{}, f, u, bk, w => Source.Term.step(f, bk), w => Source.Term.step(u, bk))) ==
          Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{Source.Q2{}, f, z}) : Maybe<&2, Source.Term>}
      %Equal.sym(Bool, Bool.and(Source.Term.is_value(f, True{}, bk), False{}), False{}, Bool.and_false(Source.Term.is_value(f, True{}, bk))) :
        {Source.Maybe.else(Source.Term, Source.Bool.lazy(Maybe<&2, Source.Term>, _,
          w => Source.Term.fires(bk, Source.Term.App{Source.Q2{}, f, u}), w => None{}), w => Source.Term.step.app(Source.Q2{}, f, u, bk, w => Source.Term.step(f, bk), w => Source.Term.step(u, bk))) ==
          Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{Source.Q2{}, f, z}) : Maybe<&2, Source.Term>}
      %Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(f, bk), None{}, Vals.step(f, False{}, bk, hf)) :
        {Source.Term.step.app(Source.Q2{}, f, u, bk, w => _, w => Source.Term.step(u, bk)) ==
          Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{Source.Q2{}, f, z}) : Maybe<&2, Source.Term>}
      %Equal.sym(Bool, Source.Term.is_value(f, False{}, bk), True{}, hf) :
        {Source.Maybe.when(Source.Term, _, v => Source.Maybe.else(Source.Term,
          Source.Maybe.map_term(Source.Maybe.when(Source.Term, Source.Quan.live(Source.Q2{}), y => Source.Term.step(u, bk)), y => Source.Term.App{Source.Q2{}, f, y}),
          z => Source.Term.redex(bk, Source.Q2{}, f, u))) ==
          Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{Source.Q2{}, f, z}) : Maybe<&2, Source.Term>}
      %Equal.sym(Maybe<&2, Source.Term>, Source.Term.redex(bk, Source.Q2{}, f, u), None{}, Redex.no(Source.Q2{}, f, u, bk, {==}, hu)) :
        {Source.Maybe.else(Source.Term, Source.Maybe.map_term(Source.Term.step(u, bk), y => Source.Term.App{Source.Q2{}, f, y}), z => _) ==
          Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{Source.Q2{}, f, z}) : Maybe<&2, Source.Term>}
      Else.none(Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{Source.Q2{}, f, z}))

# u under App q f _, with f a value and q live
def Ctx.fun(q: Source.Quan, +f: Source.Term, +u: Source.Term, +bk: List<&2, Source.Def>,
  +hq: {Source.Quan.live(q) == True{} : Bool}, +hf: {Source.Term.is_value(f, False{}, bk) == True{} : Bool}, +hu: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) ->
  {Source.Term.is_value(Source.Term.App{q, f, u}, False{}, bk) == False{} : Bool} & {Source.Term.step(Source.Term.App{q, f, u}, bk) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{q, f, z}) : Maybe<&2, Source.Term>}:
  match q:
    case Source.Q0{}:
      Empty.absurd({Source.Term.is_value(Source.Term.App{Source.Q0{}, f, u}, False{}, bk) == False{} : Bool} & {Source.Term.step(Source.Term.App{Source.Q0{}, f, u}, bk) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.App{Source.Q0{}, f, z}) : Maybe<&2, Source.Term>}, Shared.Bool.no(hq))
    case Source.Q1{}:
      (Ctx.fun_nv(Source.Q1{}, f, u, bk, hu), Ctx.fun_step(Source.Q1{}, f, u, bk, hq, hf, hu))
    case Source.Q2{}:
      (Ctx.fun_nv(Source.Q2{}, f, u, bk, hu), Ctx.fun_step(Source.Q2{}, f, u, bk, hq, hf, hu))

def Ctx.let_step.Q1(+u: Source.Term, +F: Source.Term, +bk: List<&2, Source.Def>, +hu: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) ->
  {Source.Term.step(Source.Term.Let{Source.Q1{}, u, F}, bk) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Let{Source.Q1{}, z, F}) : Maybe<&2, Source.Term>}:
  %Equal.sym(Bool, Source.Term.is_value(u, False{}, bk), False{}, hu) :
    {Source.Maybe.else(Source.Term, Source.Maybe.map_term(Source.Term.step(u, bk), w => Source.Term.Let{Source.Q1{}, w, F}), u2 => Source.Maybe.when(Source.Term, Bool.and(_, Bool.or(Bool.not(Source.Quan.is_q2(Source.Q1{})), Source.Term.is_data(u))), w => Some{Source.Term.sub(F, 0n, Source.Sub.one{u})})) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Let{Source.Q1{}, z, F}) : Maybe<&2, Source.Term>}
  Else.none(Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Let{Source.Q1{}, z, F}))

def Ctx.let_step.Q2(+u: Source.Term, +F: Source.Term, +bk: List<&2, Source.Def>, +hu: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) ->
  {Source.Term.step(Source.Term.Let{Source.Q2{}, u, F}, bk) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Let{Source.Q2{}, z, F}) : Maybe<&2, Source.Term>}:
  %Equal.sym(Bool, Source.Term.is_value(u, False{}, bk), False{}, hu) :
    {Source.Maybe.else(Source.Term, Source.Maybe.map_term(Source.Term.step(u, bk), w => Source.Term.Let{Source.Q2{}, w, F}), u2 => Source.Maybe.when(Source.Term, Bool.and(_, Bool.or(Bool.not(Source.Quan.is_q2(Source.Q2{})), Source.Term.is_data(u))), w => Some{Source.Term.sub(F, 0n, Source.Sub.one{u})})) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Let{Source.Q2{}, z, F}) : Maybe<&2, Source.Term>}
  Else.none(Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Let{Source.Q2{}, z, F}))

def Ctx.let(q: Source.Quan, +u: Source.Term, +F: Source.Term, +bk: List<&2, Source.Def>,
  hq: {Source.Quan.live(q) == True{} : Bool}, +hu: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) ->
  {Source.Term.is_value(Source.Term.Let{q, u, F}, False{}, bk) == False{} : Bool} & {Source.Term.step(Source.Term.Let{q, u, F}, bk) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Let{q, z, F}) : Maybe<&2, Source.Term>}:
  match q:
    case Source.Q0{}:
      Empty.absurd({Source.Term.is_value(Source.Term.Let{Source.Q0{}, u, F}, False{}, bk) == False{} : Bool} & {Source.Term.step(Source.Term.Let{Source.Q0{}, u, F}, bk) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Let{Source.Q0{}, z, F}) : Maybe<&2, Source.Term>}, Shared.Bool.no(hq))
    case Source.Q1{}:
      ({==}, Ctx.let_step.Q1(u, F, bk, hu))
    case Source.Q2{}:
      ({==}, Ctx.let_step.Q2(u, F, bk, hu))



def Ctx.fst_step.Q1(+u: Source.Term, +F: Source.Term, +bk: List<&2, Source.Def>, +hu: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) ->
  {Source.Term.step(Source.Term.Tup{Source.Q1{}, u, F}, bk) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Tup{Source.Q1{}, z, F}) : Maybe<&2, Source.Term>}:
  %Equal.sym(Bool, Source.Term.is_value(u, False{}, bk), False{}, hu) :
    {Source.Maybe.else(Source.Term, Source.Maybe.map_term(Source.Term.step(u, bk), w => Source.Term.Tup{Source.Q1{}, w, F}), u2 => Source.Maybe.when(Source.Term, _, w => Source.Maybe.map_term(Source.Term.step(F, bk), z => Source.Term.Tup{Source.Q1{}, u, z}))) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Tup{Source.Q1{}, z, F}) : Maybe<&2, Source.Term>}
  Else.none(Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Tup{Source.Q1{}, z, F}))

def Ctx.fst_step.Q2(+u: Source.Term, +F: Source.Term, +bk: List<&2, Source.Def>, +hu: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) ->
  {Source.Term.step(Source.Term.Tup{Source.Q2{}, u, F}, bk) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Tup{Source.Q2{}, z, F}) : Maybe<&2, Source.Term>}:
  %Equal.sym(Bool, Source.Term.is_value(u, False{}, bk), False{}, hu) :
    {Source.Maybe.else(Source.Term, Source.Maybe.map_term(Source.Term.step(u, bk), w => Source.Term.Tup{Source.Q2{}, w, F}), u2 => Source.Maybe.when(Source.Term, _, w => Source.Maybe.map_term(Source.Term.step(F, bk), z => Source.Term.Tup{Source.Q2{}, u, z}))) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Tup{Source.Q2{}, z, F}) : Maybe<&2, Source.Term>}
  Else.none(Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Tup{Source.Q2{}, z, F}))

def Ctx.fst(q: Source.Quan, +u: Source.Term, +F: Source.Term, +bk: List<&2, Source.Def>,
  hq: {Source.Quan.live(q) == True{} : Bool}, +hu: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) ->
  {Source.Term.is_value(Source.Term.Tup{q, u, F}, False{}, bk) == False{} : Bool} & {Source.Term.step(Source.Term.Tup{q, u, F}, bk) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Tup{q, z, F}) : Maybe<&2, Source.Term>}:
  match q:
    case Source.Q0{}:
      Empty.absurd({Source.Term.is_value(Source.Term.Tup{Source.Q0{}, u, F}, False{}, bk) == False{} : Bool} & {Source.Term.step(Source.Term.Tup{Source.Q0{}, u, F}, bk) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Tup{Source.Q0{}, z, F}) : Maybe<&2, Source.Term>}, Shared.Bool.no(hq))
    case Source.Q1{}:
      (Eq.rw(Bool, False{}, Source.Term.is_value(u, False{}, bk), Equal.sym(Bool, Source.Term.is_value(u, False{}, bk), False{}, hu), z => {Bool.and(z, Source.Term.is_value(F, False{}, bk)) == False{} : Bool}, {==}), Ctx.fst_step.Q1(u, F, bk, hu))
    case Source.Q2{}:
      (Eq.rw(Bool, False{}, Source.Term.is_value(u, False{}, bk), Equal.sym(Bool, Source.Term.is_value(u, False{}, bk), False{}, hu), z => {Bool.and(z, Source.Term.is_value(F, False{}, bk)) == False{} : Bool}, {==}), Ctx.fst_step.Q2(u, F, bk, hu))



def Ctx.snd_step(-q: Source.Quan, +a: Source.Term, +u: Source.Term, +bk: List<&2, Source.Def>,
  +ha: {Source.Term.is_value(a, False{}, bk) == True{} : Bool}) ->
  {Source.Maybe.else(Source.Term, Source.Maybe.map_term(Source.Term.step(a, bk), w => Source.Term.Tup{q, w, u}),
    u2 => Source.Maybe.when(Source.Term, Source.Term.is_value(a, False{}, bk), w => Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Tup{q, a, z}))) ==
    Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Tup{q, a, z}) : Maybe<&2, Source.Term>}:
  %Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(a, bk), None{}, Vals.step(a, False{}, bk, ha)) :
    {Source.Maybe.else(Source.Term, Source.Maybe.map_term(_, w => Source.Term.Tup{q, w, u}),
      u2 => Source.Maybe.when(Source.Term, Source.Term.is_value(a, False{}, bk), w => Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Tup{q, a, z}))) ==
      Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Tup{q, a, z}) : Maybe<&2, Source.Term>}
  %Equal.sym(Bool, Source.Term.is_value(a, False{}, bk), True{}, ha) :
    {Source.Maybe.when(Source.Term, _, w => Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Tup{q, a, z})) ==
      Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Tup{q, a, z}) : Maybe<&2, Source.Term>}
  {==}

def Ctx.snd(q: Source.Quan, +a: Source.Term, +u: Source.Term, +bk: List<&2, Source.Def>,
  +ha: {Bool.or(Bool.not(Source.Quan.live(q)), Source.Term.is_value(a, False{}, bk)) == True{} : Bool}, +hu: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) ->
  {Source.Term.is_value(Source.Term.Tup{q, a, u}, False{}, bk) == False{} : Bool} & {Source.Term.step(Source.Term.Tup{q, a, u}, bk) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Tup{q, a, z}) : Maybe<&2, Source.Term>}:
  match q:
    case Source.Q0{}:
      (hu, {==})
    case Source.Q1{}:
      (Eq.rw(Bool, False{}, Source.Term.is_value(u, False{}, bk), Equal.sym(Bool, Source.Term.is_value(u, False{}, bk), False{}, hu),
          z => {Bool.and(Source.Term.is_value(a, False{}, bk), z) == False{} : Bool}, Bool.and_false(Source.Term.is_value(a, False{}, bk))),
        Ctx.snd_step(Source.Q1{}, a, u, bk, ha))
    case Source.Q2{}:
      (Eq.rw(Bool, False{}, Source.Term.is_value(u, False{}, bk), Equal.sym(Bool, Source.Term.is_value(u, False{}, bk), False{}, hu),
          z => {Bool.and(Source.Term.is_value(a, False{}, bk), z) == False{} : Bool}, Bool.and_false(Source.Term.is_value(a, False{}, bk))),
        Ctx.snd_step(Source.Q2{}, a, u, bk, ha))

def Ctx.rwt(+u: Source.Term, +p: Source.Term, +f: Source.Term, +bk: List<&2, Source.Def>, +hu: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) ->
  {Source.Term.is_value(Source.Term.Rwt{u, p, f}, False{}, bk) == False{} : Bool} & {Source.Term.step(Source.Term.Rwt{u, p, f}, bk) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Rwt{z, p, f}) : Maybe<&2, Source.Term>}:
  ({==},
    Eq.rw(Bool, False{}, Source.Term.is_rfl(u), Equal.sym(Bool, Source.Term.is_rfl(u), False{}, Rfl.no(u, bk, hu)),
      z => {Source.Bool.lazy(Maybe<&2, Source.Term>, z, w => Some{f}, w => Source.Maybe.map_term(Source.Term.step(u, bk), v => Source.Term.Rwt{v, p, f})) ==
        Source.Maybe.map_term(Source.Term.step(u, bk), v => Source.Term.Rwt{v, p, f}) : Maybe<&2, Source.Term>}, {==}))

def Ctx.min1_step(+u: Source.Term, +b: Source.Term, +bk: List<&2, Source.Def>, +hu: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) ->
  {Source.Term.step(Source.Term.Min{u, b}, bk) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Min{z, b}) : Maybe<&2, Source.Term>}:
  %Equal.sym(Bool, Source.Term.is_value(u, False{}, bk), False{}, hu) :
    {Source.Maybe.else(Source.Term, Source.Maybe.map_term(Source.Term.step(u, bk), w => Source.Term.Min{w, b}),
      v => Source.Maybe.when(Source.Term, _, w => Source.Maybe.else(Source.Term, Source.Maybe.map_term(Source.Term.step(b, bk), z => Source.Term.Min{u, z}),
        z => Source.Term.meet(u, b)))) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Min{z, b}) : Maybe<&2, Source.Term>}
  Else.none(Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Min{z, b}))

def Ctx.min1(+u: Source.Term, +b: Source.Term, +bk: List<&2, Source.Def>, +hu: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) ->
  {Source.Term.is_value(Source.Term.Min{u, b}, False{}, bk) == False{} : Bool} & {Source.Term.step(Source.Term.Min{u, b}, bk) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Min{z, b}) : Maybe<&2, Source.Term>}:
  ({==}, Ctx.min1_step(u, b, bk, hu))

def Ctx.min2_step(+a: Source.Term, +u: Source.Term, +bk: List<&2, Source.Def>,
  +ha: {Source.Term.is_value(a, False{}, bk) == True{} : Bool}, +hu: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) ->
  {Source.Term.step(Source.Term.Min{a, u}, bk) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Min{a, z}) : Maybe<&2, Source.Term>}:
  %Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(a, bk), None{}, Vals.step(a, False{}, bk, ha)) :
    {Source.Term.step.min(a, u, bk, w => _, w => Source.Term.step(u, bk)) ==
      Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Min{a, z}) : Maybe<&2, Source.Term>}
  %Equal.sym(Bool, Source.Term.is_value(a, False{}, bk), True{}, ha) :
    {Source.Maybe.when(Source.Term, _, w => Source.Maybe.else(Source.Term, Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Min{a, z}),
      z => Source.Term.meet(a, u))) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Min{a, z}) : Maybe<&2, Source.Term>}
  %Equal.sym(Maybe<&2, Source.Term>, Source.Term.meet(a, u), None{}, Meet.no(a, u, bk, hu)) :
    {Source.Maybe.else(Source.Term, Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Min{a, z}), z => _) ==
      Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Min{a, z}) : Maybe<&2, Source.Term>}
  Else.none(Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Min{a, z}))

def Ctx.min2(+a: Source.Term, +u: Source.Term, +bk: List<&2, Source.Def>,
  ha: {Source.Term.is_value(a, False{}, bk) == True{} : Bool}, +hu: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) ->
  {Source.Term.is_value(Source.Term.Min{a, u}, False{}, bk) == False{} : Bool} & {Source.Term.step(Source.Term.Min{a, u}, bk) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Source.Term.Min{a, z}) : Maybe<&2, Source.Term>}:
  ({==}, Ctx.min2_step(a, u, bk, ha, hu))


def Field.value(q: Source.Quan, a: Machine.Val, +bk: List<&2, Source.Def>, h: {Val.ok(a, Mode.field(q), bk) == True{} : Bool}) ->
  {Bool.or(Bool.not(Source.Quan.live(q)), Source.Term.is_value(Val.rb(a), False{}, bk)) == True{} : Bool}:
  match q:
    case Source.Q0{}:
      {==}
    case Source.Q1{}:
      Val.value(a, bk, h)
    case Source.Q2{}:
      Val.value(a, bk, h)

# a step inside the frame fr is a step of its term
def Fr.ctx(fr: Machine.Fr, +u: Source.Term, +bk: List<&2, Source.Def>, +hfr: {Fr.ok(fr, bk) == True{} : Bool},
  +hu: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) -> Fr.res(fr, u, bk):
  match fr:
    case Machine.Fr.arg{q, x}:
      Ctx.arg(q, u, Val.rb(x), bk, hu)
    case Machine.Fr.fun{+q, +f}:
      Ctx.fun(q, Val.rb(f), u, bk, SP.Bool.and_left(Source.Quan.live(q), Val.ok(f, Mode.good{}, bk), hfr),
        Val.value(f, bk, SP.Bool.and_right(Source.Quan.live(q), Val.ok(f, Mode.good{}, bk), hfr)), hu)
    case Machine.Fr.let{+q, f, +e}:
      Ctx.let(q, u, Source.Term.sub(f, 1n, Source.Sub.env{Env.rb(e)}), bk,
        SP.Bool.and_left(Source.Quan.live(q), Val.ok(e, Mode.env{}, bk), hfr), hu)
    case Machine.Fr.fst{+q, b, +e}:
      Ctx.fst(q, u, Clo.rb(b, e), bk, SP.Bool.and_left(Source.Quan.live(q), Val.ok(e, Mode.env{}, bk), hfr), hu)
    case Machine.Fr.snd{+q, +a}:
      Ctx.snd(q, Val.rb(a), u, bk, Field.value(q, a, bk, hfr), hu)
    case Machine.Fr.rwt{p, f, +e}:
      Ctx.rwt(u, Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e), bk, hu)
    case Machine.Fr.min1{b, e}:
      Ctx.min1(u, Clo.rb(b, e), bk, hu)
    case Machine.Fr.min2{+a}:
      Ctx.min2(Val.rb(a), u, bk, Val.value(a, bk, hfr), hu)

def Frs.res(fs: List<&2, Machine.Fr>, u: Source.Term, +bk: List<&2, Source.Def>) -> Type:
  {Source.Term.is_value(Frs.plug(fs, u), False{}, bk) == False{} : Bool} &
    {Source.Term.step(Frs.plug(fs, u), bk) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Frs.plug(fs, z)) : Maybe<&2, Source.Term>}

def Frs.ctx.two(+fr: Machine.Fr, +rest: List<&2, Machine.Fr>, +u: Source.Term, +bk: List<&2, Source.Def>,
  st1: {Source.Term.step(Fr.plug(fr, u), bk) == Source.Maybe.map_term(Source.Term.step(u, bk), z => Fr.plug(fr, z)) : Maybe<&2, Source.Term>},
  r2: Frs.res(rest, Fr.plug(fr, u), bk)) -> Frs.res(Con{fr, rest}, u, bk):
  match r2:
    case (nv2, st2):
      (nv2, Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Frs.plug(rest, Fr.plug(fr, u)), bk),
        Source.Maybe.map_term(Source.Term.step(Fr.plug(fr, u), bk), z => Frs.plug(rest, z)),
        Source.Maybe.map_term(Source.Term.step(u, bk), z => Frs.plug(rest, Fr.plug(fr, z))), st2,
        Equal.trans(Maybe<&2, Source.Term>, Source.Maybe.map_term(Source.Term.step(Fr.plug(fr, u), bk), z => Frs.plug(rest, z)),
          Source.Maybe.map_term(Source.Maybe.map_term(Source.Term.step(u, bk), z => Fr.plug(fr, z)), z => Frs.plug(rest, z)),
          Source.Maybe.map_term(Source.Term.step(u, bk), z => Frs.plug(rest, Fr.plug(fr, z))),
          Equal.cong(Maybe<&2, Source.Term>, Maybe<&2, Source.Term>, m => Source.Maybe.map_term(m, z => Frs.plug(rest, z)),
            Source.Term.step(Fr.plug(fr, u), bk), Source.Maybe.map_term(Source.Term.step(u, bk), z => Fr.plug(fr, z)), st1),
          Map.map(Source.Term.step(u, bk), z => Fr.plug(fr, z), z => Frs.plug(rest, z)))))

def Frs.ctx.cons(+fr: Machine.Fr, +rest: List<&2, Machine.Fr>, +u: Source.Term, +bk: List<&2, Source.Def>,
  r1: Fr.res(fr, u, bk),
  rec: @v: Source.Term -> {Source.Term.is_value(v, False{}, bk) == False{} : Bool} -> Frs.res(rest, v, bk)) ->
  Frs.res(Con{fr, rest}, u, bk):
  match r1:
    case (nv1, st1):
      Frs.ctx.two(fr, rest, u, bk, st1, rec(Fr.plug(fr, u), nv1))

# a step inside the frames fs is a step of their term
def Frs.ctx(fs: List<&2, Machine.Fr>, +u: Source.Term, +bk: List<&2, Source.Def>, +hfs: {Frs.ok(fs, bk) == True{} : Bool},
  +hu: {Source.Term.is_value(u, False{}, bk) == False{} : Bool}) -> Frs.res(fs, u, bk):
  match fs:
    case Nil{}:
      (hu, Equal.sym(Maybe<&2, Source.Term>, Source.Maybe.map_term(Source.Term.step(u, bk), z => z), Source.Term.step(u, bk),
        Map.id(Source.Term.step(u, bk))))
    case Con{+fr, +rest}:
      Frs.ctx.cons(fr, rest, u, bk, Fr.ctx(fr, u, bk, SP.Bool.and_left(Fr.ok(fr, bk), Frs.ok(rest, bk), hfs), hu),
        v => hv => Frs.ctx(rest, v, bk, SP.Bool.and_right(Fr.ok(fr, bk), Frs.ok(rest, bk), hfs), hv))

def Ctx.go.of(-fs: List<&2, Machine.Fr>, -r: Source.Term, -r2: Source.Term, -bk: List<&2, Source.Def>, c: Frs.res(fs, r, bk),
  hs: {Source.Term.step(r, bk) == Some{r2} : Maybe<&2, Source.Term>}) ->
  {Source.Term.step(Frs.plug(fs, r), bk) == Some{Frs.plug(fs, r2)} : Maybe<&2, Source.Term>}:
  match c:
    case (nv, st):
      Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Frs.plug(fs, r), bk),
        Source.Maybe.map_term(Source.Term.step(r, bk), z => Frs.plug(fs, z)), Some{Frs.plug(fs, r2)}, st,
        Equal.cong(Maybe<&2, Source.Term>, Maybe<&2, Source.Term>, m => Source.Maybe.map_term(m, z => Frs.plug(fs, z)),
          Source.Term.step(r, bk), Some{r2}, hs))

# the step of the redex r, inside the frames fs
def Ctx.go(+fs: List<&2, Machine.Fr>, +r: Source.Term, -r2: Source.Term, +bk: List<&2, Source.Def>,
  hfs: {Frs.ok(fs, bk) == True{} : Bool}, hv: {Source.Term.is_value(r, False{}, bk) == False{} : Bool},
  hs: {Source.Term.step(r, bk) == Some{r2} : Maybe<&2, Source.Term>}) ->
  {Source.Term.step(Frs.plug(fs, r), bk) == Some{Frs.plug(fs, r2)} : Maybe<&2, Source.Term>}:
  Ctx.go.of(fs, r, r2, bk, Frs.ctx(fs, r, bk, hfs, hv), hs)

def Ctx.stuck.of(-fs: List<&2, Machine.Fr>, -r: Source.Term, -bk: List<&2, Source.Def>, c: Frs.res(fs, r, bk),
  hs: {Source.Term.step(r, bk) == None{} : Maybe<&2, Source.Term>}) ->
  {Source.Term.is_value(Frs.plug(fs, r), False{}, bk) == False{} : Bool} &
    {Source.Term.step(Frs.plug(fs, r), bk) == None{} : Maybe<&2, Source.Term>}:
  match c:
    case (nv, st):
      (nv, Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Frs.plug(fs, r), bk),
        Source.Maybe.map_term(Source.Term.step(r, bk), z => Frs.plug(fs, z)), None{}, st,
        Equal.cong(Maybe<&2, Source.Term>, Maybe<&2, Source.Term>, m => Source.Maybe.map_term(m, z => Frs.plug(fs, z)),
          Source.Term.step(r, bk), None{}, hs)))

# the redex r is stuck, inside the frames fs
def Ctx.stuck(+fs: List<&2, Machine.Fr>, +r: Source.Term, +bk: List<&2, Source.Def>,
  hfs: {Frs.ok(fs, bk) == True{} : Bool}, hv: {Source.Term.is_value(r, False{}, bk) == False{} : Bool},
  hs: {Source.Term.step(r, bk) == None{} : Maybe<&2, Source.Term>}) ->
  {Source.Term.is_value(Frs.plug(fs, r), False{}, bk) == False{} : Bool} &
    {Source.Term.step(Frs.plug(fs, r), bk) == None{} : Maybe<&2, Source.Term>}:
  Ctx.stuck.of(fs, r, bk, Frs.ctx(fs, r, bk, hfs, hv), hs)
# Measure
# =======

def Term.var_le(t: Source.Term) -> {Nat.is_le(Term.var(t), 1n) == True{} : Bool}:
  match t:
    case Source.Term.Var{z0}:
      {==}
    case Source.Term.Ref{z0}:
      {==}
    case Source.Term.Ann{z0, z1}:
      {==}
    case Source.Term.Let{z0, z1, z2}:
      {==}
    case Source.Term.Typ{z0}:
      {==}
    case Source.Term.Min{z0, z1}:
      {==}
    case Source.Term.All{z0, z1, z2}:
      {==}
    case Source.Term.Lam{z0, z1}:
      {==}
    case Source.Term.App{z0, z1, z2}:
      {==}
    case Source.Term.Sig{z0, z1, z2}:
      {==}
    case Source.Term.Tup{z0, z1, z2}:
      {==}
    case Source.Term.Prj{z0}:
      {==}
    case Source.Term.Enu{z0}:
      {==}
    case Source.Term.Lab{z0}:
      {==}
    case Source.Term.Mat{z0, z1, z2}:
      {==}
    case Source.Term.Efq{}:
      {==}
    case Source.Term.Eql{z0, z1, z2}:
      {==}
    case Source.Term.Rfl{}:
      {==}
    case Source.Term.Rwt{z0, z1, z2}:
      {==}

# a step that pushes a frame or pops one makes the measure smaller, when it does
# so at the top of the frames
def Frs.lt(fs: List<&2, Machine.Fr>, +a: Nat, +b: Nat, h: {Nat.is_le(1n+a, b) == True{} : Bool}) ->
  {Nat.is_le(1n+Frs.mu(fs, a), Frs.mu(fs, b)) == True{} : Bool}:
  match fs:
    case Nil{}:
      h
    case Con{+fr, rest}:
      Frs.lt(rest, Nat.add(Fr.pend(fr), a), Nat.add(Fr.pend(fr), b),
        Eq.rw(Nat, Nat.add(Fr.pend(fr), 1n+a), 1n+Nat.add(Fr.pend(fr), a), Nat.add_succ(Fr.pend(fr), a),
          z => {Nat.is_le(z, Nat.add(Fr.pend(fr), b)) == True{} : Bool}, Nat.is_le_mono(Fr.pend(fr), 1n+a, b, h)))

def Le.add(+a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}, +c: Nat) -> {Nat.is_le(a, Nat.add(c, b)) == True{} : Bool}:
  match c:
    case 0n:
      h
    case 1n+p:
      Shared.Nat.is_le_succ(a, Nat.add(p, b), Le.add(a, b, h, p))

def Le.step1(+t: Source.Term, +a: Nat) -> {Nat.is_le(Nat.add(Term.var(t), a), 1n+a) == True{} : Bool}:
  Nat.is_le_one(Term.var(t), a, Term.var_le(t))

# push a frame of 3 + b on a term of a
def Le.push3(+t: Source.Term, +a: Nat, +b: Nat) ->
  {Nat.is_le(1n+Nat.add(3n+b, Nat.add(Term.var(t), a)), 5n+Nat.add(b, a)) == True{} : Bool}:
  Eq.rw(Nat, Nat.add(b, 1n+a), 1n+Nat.add(b, a), Nat.add_succ(b, a),
    z => {Nat.is_le(Nat.add(b, Nat.add(Term.var(t), a)), z) == True{} : Bool},
    Nat.is_le_mono(b, Nat.add(Term.var(t), a), 1n+a, Le.step1(t, a)))

# push a frame of 1
def Le.push1(+t: Source.Term, +a: Nat) -> {Nat.is_le(1n+1n+Nat.add(Term.var(t), a), 5n+a) == True{} : Bool}:
  Le.add(Nat.add(Term.var(t), a), 1n+a, Le.step1(t, a), 2n)

def Le.push1z(+t: Source.Term, +a: Nat) -> {Nat.is_le(1n+1n+Nat.add(Term.var(t), a), 5n+Nat.add(a, 0n)) == True{} : Bool}:
  Eq.rw(Nat, a, Nat.add(a, 0n), Equal.sym(Nat, Nat.add(a, 0n), a, Nat.add_zero(a)),
    z => {Nat.is_le(1n+1n+Nat.add(Term.var(t), a), 5n+z) == True{} : Bool}, Le.push1(t, a))

# push a frame of 0
def Le.push0(+t: Source.Term, +a: Nat) -> {Nat.is_le(1n+Nat.add(Term.var(t), a), 5n+a) == True{} : Bool}:
  Le.add(Nat.add(Term.var(t), a), 1n+a, Le.step1(t, a), 3n)

# pop a frame of 3 + x, then push one of 1 on a term of x
def Le.pop3(+t: Source.Term, +x: Nat) -> {Nat.is_le(1n+1n+Nat.add(Term.var(t), x), Nat.add(3n+x, 0n)) == True{} : Bool}:
  Eq.rw(Nat, x, Nat.add(x, 0n), Equal.sym(Nat, Nat.add(x, 0n), x, Nat.add_zero(x)),
    z => {Nat.is_le(Nat.add(Term.var(t), x), 1n+z) == True{} : Bool}, Le.step1(t, x))

def Var.zero(t: Source.Term, -e: Machine.Val, h: {Val.no_var(Machine.Val.clo{t, e}) == True{} : Bool}) ->
  {Term.var(t) == 0n : Nat}:
  match t:
    case Source.Term.Var{z0}:
      Shared.Bool.absurd({Term.var(Source.Term.Var{z0}) == 0n : Nat}, h)
    case Source.Term.Ref{z0}:
      {==}
    case Source.Term.Ann{z0, z1}:
      {==}
    case Source.Term.Let{z0, z1, z2}:
      {==}
    case Source.Term.Typ{z0}:
      {==}
    case Source.Term.Min{z0, z1}:
      {==}
    case Source.Term.All{z0, z1, z2}:
      {==}
    case Source.Term.Lam{z0, z1}:
      {==}
    case Source.Term.App{z0, z1, z2}:
      {==}
    case Source.Term.Sig{z0, z1, z2}:
      {==}
    case Source.Term.Tup{z0, z1, z2}:
      {==}
    case Source.Term.Prj{z0}:
      {==}
    case Source.Term.Enu{z0}:
      {==}
    case Source.Term.Lab{z0}:
      {==}
    case Source.Term.Mat{z0, z1, z2}:
      {==}
    case Source.Term.Efq{}:
      {==}
    case Source.Term.Eql{z0, z1, z2}:
      {==}
    case Source.Term.Rfl{}:
      {==}
    case Source.Term.Rwt{z0, z1, z2}:
      {==}

# Calls and applications
# ======================

def Qmin.sub(+i: List<&2, Nat>, +j: List<&2, Nat>) ->
  {Source.Term.sub(Source.Term.qmin(i, j), 0n, Source.Sub.env{[]}) == Source.Term.qmin(i, j) : Source.Term}:
  Shared.Bool.elim(Source.Name.is_eq(i, Source.Name.of("Q2")),
    c => {Source.Term.sub(Source.Bool.if(Source.Term, c, Source.Term.Lab{j},
      Source.Bool.if(Source.Term, Source.Name.is_eq(j, Source.Name.of("Q2")), Source.Term.Lab{i},
        Source.Bool.if(Source.Term, Bool.or(Source.Name.is_eq(i, Source.Name.of("Q0")), Source.Name.is_eq(j, Source.Name.of("Q0"))),
          Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")}))), 0n, Source.Sub.env{[]}) ==
      Source.Bool.if(Source.Term, c, Source.Term.Lab{j},
      Source.Bool.if(Source.Term, Source.Name.is_eq(j, Source.Name.of("Q2")), Source.Term.Lab{i},
        Source.Bool.if(Source.Term, Bool.or(Source.Name.is_eq(i, Source.Name.of("Q0")), Source.Name.is_eq(j, Source.Name.of("Q0"))),
          Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")}))) : Source.Term},
    {==},
    Shared.Bool.elim(Source.Name.is_eq(j, Source.Name.of("Q2")),
      c => {Source.Term.sub(Source.Bool.if(Source.Term, c, Source.Term.Lab{i},
        Source.Bool.if(Source.Term, Bool.or(Source.Name.is_eq(i, Source.Name.of("Q0")), Source.Name.is_eq(j, Source.Name.of("Q0"))),
          Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")})), 0n, Source.Sub.env{[]}) ==
        Source.Bool.if(Source.Term, c, Source.Term.Lab{i},
        Source.Bool.if(Source.Term, Bool.or(Source.Name.is_eq(i, Source.Name.of("Q0")), Source.Name.is_eq(j, Source.Name.of("Q0"))),
          Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")})) : Source.Term},
      {==},
      Shared.Bool.elim(Bool.or(Source.Name.is_eq(i, Source.Name.of("Q0")), Source.Name.is_eq(j, Source.Name.of("Q0"))),
        c => {Source.Term.sub(Source.Bool.if(Source.Term, c, Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")}),
          0n, Source.Sub.env{[]}) == Source.Bool.if(Source.Term, c, Source.Term.Lab{Source.Name.of("Q0")}, Source.Term.Lab{Source.Name.of("Q1")}) : Source.Term},
        {==}, {==})))

def Args.snoc_rb(xs: Machine.Val, +q: Source.Quan, +x: Machine.Val, +bk: List<&2, Source.Def>, h: {Val.ok(xs, Mode.args{}, bk) == True{} : Bool}) ->
  {Args.rb(Machine.Args.snoc(xs, q, x)) == List.append(&2, Source.Arg, Args.rb(xs), Con{Source.Arg{q, Val.rb(x)}, Nil{}}) : List<&2, Source.Arg>}:
  match xs:
    case Machine.Val.nil{}:
      {==}
    case Machine.Val.env{+v0, +v1}:
      Shared.Bool.absurd({Args.rb(Machine.Args.snoc(Machine.Val.env{v0, v1}, q, x)) == List.append(&2, Source.Arg, Args.rb(Machine.Val.env{v0, v1}), Con{Source.Arg{q, Val.rb(x)}, Nil{}}) : List<&2, Source.Arg>}, h)
    case Machine.Val.arg{+v0, +v1, +v2}:
      Equal.cong(List<&2, Source.Arg>, List<&2, Source.Arg>, z => Con{Source.Arg{v0, Val.rb(v1)}, z},
        Args.rb(Machine.Args.snoc(v2, q, x)), List.append(&2, Source.Arg, Args.rb(v2), Con{Source.Arg{q, Val.rb(x)}, Nil{}}),
        Args.snoc_rb(v2, q, x, bk, SP.Bool.and_right(Val.ok(v1, Mode.any{}, bk), Val.ok(v2, Mode.args{}, bk), h)))
    case Machine.Val.clo{+v0, +v1}:
      Shared.Bool.absurd({Args.rb(Machine.Args.snoc(Machine.Val.clo{v0, v1}, q, x)) == List.append(&2, Source.Arg, Args.rb(Machine.Val.clo{v0, v1}), Con{Source.Arg{q, Val.rb(x)}, Nil{}}) : List<&2, Source.Arg>}, h)
    case Machine.Val.lab{+v0}:
      Shared.Bool.absurd({Args.rb(Machine.Args.snoc(Machine.Val.lab{v0}, q, x)) == List.append(&2, Source.Arg, Args.rb(Machine.Val.lab{v0}), Con{Source.Arg{q, Val.rb(x)}, Nil{}}) : List<&2, Source.Arg>}, h)
    case Machine.Val.rfl{}:
      Shared.Bool.absurd({Args.rb(Machine.Args.snoc(Machine.Val.rfl{}, q, x)) == List.append(&2, Source.Arg, Args.rb(Machine.Val.rfl{}), Con{Source.Arg{q, Val.rb(x)}, Nil{}}) : List<&2, Source.Arg>}, h)
    case Machine.Val.tup{+v0, +v1, +v2}:
      Shared.Bool.absurd({Args.rb(Machine.Args.snoc(Machine.Val.tup{v0, v1, v2}, q, x)) == List.append(&2, Source.Arg, Args.rb(Machine.Val.tup{v0, v1, v2}), Con{Source.Arg{q, Val.rb(x)}, Nil{}}) : List<&2, Source.Arg>}, h)
    case Machine.Val.call{+v0, +v1}:
      Shared.Bool.absurd({Args.rb(Machine.Args.snoc(Machine.Val.call{v0, v1}, q, x)) == List.append(&2, Source.Arg, Args.rb(Machine.Val.call{v0, v1}), Con{Source.Arg{q, Val.rb(x)}, Nil{}}) : List<&2, Source.Arg>}, h)

def Args.snoc_ok(xs: Machine.Val, +q: Source.Quan, +x: Machine.Val, +bk: List<&2, Source.Def>, +h: {Val.ok(xs, Mode.args{}, bk) == True{} : Bool},
  +hx: {Val.ok(x, Mode.any{}, bk) == True{} : Bool}) -> {Val.ok(Machine.Args.snoc(xs, q, x), Mode.args{}, bk) == True{} : Bool}:
  match xs:
    case Machine.Val.nil{}:
      SP.Bool.and_intro(Val.ok(x, Mode.any{}, bk), True{}, hx, {==})
    case Machine.Val.env{+v0, +v1}:
      Shared.Bool.absurd({Val.ok(Machine.Args.snoc(Machine.Val.env{v0, v1}, q, x), Mode.args{}, bk) == True{} : Bool}, h)
    case Machine.Val.arg{+v0, +v1, +v2}:
      SP.Bool.and_intro(Val.ok(v1, Mode.any{}, bk), Val.ok(Machine.Args.snoc(v2, q, x), Mode.args{}, bk),
        SP.Bool.and_left(Val.ok(v1, Mode.any{}, bk), Val.ok(v2, Mode.args{}, bk), h),
        Args.snoc_ok(v2, q, x, bk, SP.Bool.and_right(Val.ok(v1, Mode.any{}, bk), Val.ok(v2, Mode.args{}, bk), h), hx))
    case Machine.Val.clo{+v0, +v1}:
      Shared.Bool.absurd({Val.ok(Machine.Args.snoc(Machine.Val.clo{v0, v1}, q, x), Mode.args{}, bk) == True{} : Bool}, h)
    case Machine.Val.lab{+v0}:
      Shared.Bool.absurd({Val.ok(Machine.Args.snoc(Machine.Val.lab{v0}, q, x), Mode.args{}, bk) == True{} : Bool}, h)
    case Machine.Val.rfl{}:
      Shared.Bool.absurd({Val.ok(Machine.Args.snoc(Machine.Val.rfl{}, q, x), Mode.args{}, bk) == True{} : Bool}, h)
    case Machine.Val.tup{+v0, +v1, +v2}:
      Shared.Bool.absurd({Val.ok(Machine.Args.snoc(Machine.Val.tup{v0, v1, v2}, q, x), Mode.args{}, bk) == True{} : Bool}, h)
    case Machine.Val.call{+v0, +v1}:
      Shared.Bool.absurd({Val.ok(Machine.Args.snoc(Machine.Val.call{v0, v1}, q, x), Mode.args{}, bk) == True{} : Bool}, h)

def Frames.plug(rest: Machine.Val, +fs: List<&2, Machine.Fr>, +u: Source.Term, +bk: List<&2, Source.Def>,
  h: {Val.ok(rest, Mode.args{}, bk) == True{} : Bool}) ->
  {Frs.plug(Machine.Args.frames(rest, fs), u) == Frs.plug(fs, Source.Term.spine(Args.rb(rest), u)) : Source.Term}:
  match rest:
    case Machine.Val.nil{}:
      {==}
    case Machine.Val.env{+v0, +v1}:
      Shared.Bool.absurd({Frs.plug(Machine.Args.frames(Machine.Val.env{v0, v1}, fs), u) == Frs.plug(fs, Source.Term.spine(Args.rb(Machine.Val.env{v0, v1}), u)) : Source.Term}, h)
    case Machine.Val.arg{+v0, +v1, +v2}:
      Frames.plug(v2, fs, Source.Term.App{v0, u, Val.rb(v1)}, bk,
        SP.Bool.and_right(Val.ok(v1, Mode.any{}, bk), Val.ok(v2, Mode.args{}, bk), h))
    case Machine.Val.clo{+v0, +v1}:
      Shared.Bool.absurd({Frs.plug(Machine.Args.frames(Machine.Val.clo{v0, v1}, fs), u) == Frs.plug(fs, Source.Term.spine(Args.rb(Machine.Val.clo{v0, v1}), u)) : Source.Term}, h)
    case Machine.Val.lab{+v0}:
      Shared.Bool.absurd({Frs.plug(Machine.Args.frames(Machine.Val.lab{v0}, fs), u) == Frs.plug(fs, Source.Term.spine(Args.rb(Machine.Val.lab{v0}), u)) : Source.Term}, h)
    case Machine.Val.rfl{}:
      Shared.Bool.absurd({Frs.plug(Machine.Args.frames(Machine.Val.rfl{}, fs), u) == Frs.plug(fs, Source.Term.spine(Args.rb(Machine.Val.rfl{}), u)) : Source.Term}, h)
    case Machine.Val.tup{+v0, +v1, +v2}:
      Shared.Bool.absurd({Frs.plug(Machine.Args.frames(Machine.Val.tup{v0, v1, v2}, fs), u) == Frs.plug(fs, Source.Term.spine(Args.rb(Machine.Val.tup{v0, v1, v2}), u)) : Source.Term}, h)
    case Machine.Val.call{+v0, +v1}:
      Shared.Bool.absurd({Frs.plug(Machine.Args.frames(Machine.Val.call{v0, v1}, fs), u) == Frs.plug(fs, Source.Term.spine(Args.rb(Machine.Val.call{v0, v1}), u)) : Source.Term}, h)

def Frames.ok(rest: Machine.Val, +fs: List<&2, Machine.Fr>, +bk: List<&2, Source.Def>, +h: {Val.ok(rest, Mode.args{}, bk) == True{} : Bool},
  hfs: {Frs.ok(fs, bk) == True{} : Bool}) -> {Frs.ok(Machine.Args.frames(rest, fs), bk) == True{} : Bool}:
  match rest:
    case Machine.Val.nil{}:
      hfs
    case Machine.Val.env{+v0, +v1}:
      Shared.Bool.absurd({Frs.ok(Machine.Args.frames(Machine.Val.env{v0, v1}, fs), bk) == True{} : Bool}, h)
    case Machine.Val.arg{+v0, +v1, +v2}:
      SP.Bool.and_intro(Val.ok(v1, Mode.any{}, bk), Frs.ok(Machine.Args.frames(v2, fs), bk),
        SP.Bool.and_left(Val.ok(v1, Mode.any{}, bk), Val.ok(v2, Mode.args{}, bk), h),
        Frames.ok(v2, fs, bk, SP.Bool.and_right(Val.ok(v1, Mode.any{}, bk), Val.ok(v2, Mode.args{}, bk), h), hfs))
    case Machine.Val.clo{+v0, +v1}:
      Shared.Bool.absurd({Frs.ok(Machine.Args.frames(Machine.Val.clo{v0, v1}, fs), bk) == True{} : Bool}, h)
    case Machine.Val.lab{+v0}:
      Shared.Bool.absurd({Frs.ok(Machine.Args.frames(Machine.Val.lab{v0}, fs), bk) == True{} : Bool}, h)
    case Machine.Val.rfl{}:
      Shared.Bool.absurd({Frs.ok(Machine.Args.frames(Machine.Val.rfl{}, fs), bk) == True{} : Bool}, h)
    case Machine.Val.tup{+v0, +v1, +v2}:
      Shared.Bool.absurd({Frs.ok(Machine.Args.frames(Machine.Val.tup{v0, v1, v2}, fs), bk) == True{} : Bool}, h)
    case Machine.Val.call{+v0, +v1}:
      Shared.Bool.absurd({Frs.ok(Machine.Args.frames(Machine.Val.call{v0, v1}, fs), bk) == True{} : Bool}, h)

def Arg.ihx(q: Source.Quan, +x: Machine.Val, +bk: List<&2, Source.Def>, h: {Val.ok(x, Mode.field(q), bk) == True{} : Bool}) ->
  {Source.Maybe.when(Source.Term, Source.Quan.live(q), u => Source.Term.step(Val.rb(x), bk)) == None{} : Maybe<&2, Source.Term>}:
  match q:
    case Source.Q0{}:
      {==}
    case Source.Q1{}:
      Vals.step(Val.rb(x), False{}, bk, Val.value(x, bk, h))
    case Source.Q2{}:
      Vals.step(Val.rb(x), False{}, bk, Val.value(x, bk, h))

# the step of App q f x, with f a value and not a call, is its redex
def App.red(+q: Source.Quan, +f: Source.Term, +x: Machine.Val, +bk: List<&2, Source.Def>,
  +hfv: {Source.Term.is_value(f, False{}, bk) == True{} : Bool}, hfc: {Source.Term.is_value(f, True{}, bk) == False{} : Bool},
  hx: {Val.ok(x, Mode.field(q), bk) == True{} : Bool}) ->
  {Source.Term.step(Source.Term.App{q, f, Val.rb(x)}, bk) == Source.Term.redex(bk, q, f, Val.rb(x)) : Maybe<&2, Source.Term>}:
  %Equal.sym(Bool, Source.Term.is_value(f, True{}, bk), False{}, hfc) :
    {Source.Maybe.else(Source.Term, Source.Bool.lazy(Maybe<&2, Source.Term>, Bool.and(_, Bool.or(Bool.not(Source.Quan.live(q)), Source.Term.is_value(Val.rb(x), False{}, bk))),
      w => Source.Term.fires(bk, Source.Term.App{q, f, Val.rb(x)}), w => None{}),
      w => Source.Term.step.app(q, f, Val.rb(x), bk, v => Source.Term.step(f, bk), v => Source.Term.step(Val.rb(x), bk))) ==
      Source.Term.redex(bk, q, f, Val.rb(x)) : Maybe<&2, Source.Term>}
  %Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(f, bk), None{}, Vals.step(f, False{}, bk, hfv)) :
    {Source.Term.step.app(q, f, Val.rb(x), bk, v => _, v => Source.Term.step(Val.rb(x), bk)) == Source.Term.redex(bk, q, f, Val.rb(x)) : Maybe<&2, Source.Term>}
  %Equal.sym(Bool, Source.Term.is_value(f, False{}, bk), True{}, hfv) :
    {Source.Maybe.when(Source.Term, _, v => Source.Maybe.else(Source.Term,
      Source.Maybe.map_term(Source.Maybe.when(Source.Term, Source.Quan.live(q), y => Source.Term.step(Val.rb(x), bk)), y => Source.Term.App{q, f, y}),
      z => Source.Term.redex(bk, q, f, Val.rb(x)))) == Source.Term.redex(bk, q, f, Val.rb(x)) : Maybe<&2, Source.Term>}
  %Equal.sym(Maybe<&2, Source.Term>, Source.Maybe.when(Source.Term, Source.Quan.live(q), u => Source.Term.step(Val.rb(x), bk)), None{}, Arg.ihx(q, x, bk, hx)) :
    {Source.Maybe.else(Source.Term, Source.Maybe.map_term(_, y => Source.Term.App{q, f, y}), z => Source.Term.redex(bk, q, f, Val.rb(x))) ==
      Source.Term.redex(bk, q, f, Val.rb(x)) : Maybe<&2, Source.Term>}
  {==}

def App.nv(-q: Source.Quan, +f: Source.Term, -x: Source.Term, +bk: List<&2, Source.Def>, hfc: {Source.Term.is_value(f, True{}, bk) == False{} : Bool}) ->
  {Source.Term.is_value(Source.Term.App{q, f, x}, False{}, bk) == False{} : Bool}:
  %Equal.sym(Bool, Source.Term.is_value(f, True{}, bk), False{}, hfc) :
    {Bool.and(Bool.and(_, Bool.or(Bool.not(Source.Quan.live(q)), Source.Term.is_value(x, False{}, bk))), Source.Term.stops(bk, Source.Term.App{q, f, x})) ==
      False{} : Bool}
  {==}

# a call that is a value is a spine of values
def Call.vt(t: Source.Term, +bk: List<&2, Source.Def>, h: {Source.Term.is_value(t, False{}, bk) == True{} : Bool}, hc: {Term.is_call(t) == True{} : Bool}) ->
  {Source.Term.is_value(t, True{}, bk) == True{} : Bool}:
  match t:
    case Source.Term.Var{+z0}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Var{z0}, True{}, bk) == True{} : Bool}, hc)
    case Source.Term.Ref{+z0}:
      {==}
    case Source.Term.Ann{+z0, +z1}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Ann{z0, z1}, True{}, bk) == True{} : Bool}, hc)
    case Source.Term.Let{+z0, +z1, +z2}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Let{z0, z1, z2}, True{}, bk) == True{} : Bool}, hc)
    case Source.Term.Typ{+z0}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Typ{z0}, True{}, bk) == True{} : Bool}, hc)
    case Source.Term.Min{+z0, +z1}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Min{z0, z1}, True{}, bk) == True{} : Bool}, hc)
    case Source.Term.All{+z0, +z1, +z2}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.All{z0, z1, z2}, True{}, bk) == True{} : Bool}, hc)
    case Source.Term.Lam{+z0, +z1}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Lam{z0, z1}, True{}, bk) == True{} : Bool}, hc)
    case Source.Term.App{+z0, +z1, +z2}:
      SP.Bool.and_left(Bool.and(Source.Term.is_value(z1, True{}, bk), Bool.or(Bool.not(Source.Quan.live(z0)), Source.Term.is_value(z2, False{}, bk))),
        Source.Term.stops(bk, Source.Term.App{z0, z1, z2}), h)
    case Source.Term.Sig{+z0, +z1, +z2}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Sig{z0, z1, z2}, True{}, bk) == True{} : Bool}, hc)
    case Source.Term.Tup{+z0, +z1, +z2}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Tup{z0, z1, z2}, True{}, bk) == True{} : Bool}, hc)
    case Source.Term.Prj{+z0}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Prj{z0}, True{}, bk) == True{} : Bool}, hc)
    case Source.Term.Enu{+z0}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Enu{z0}, True{}, bk) == True{} : Bool}, hc)
    case Source.Term.Lab{+z0}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Lab{z0}, True{}, bk) == True{} : Bool}, hc)
    case Source.Term.Mat{+z0, +z1, +z2}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Mat{z0, z1, z2}, True{}, bk) == True{} : Bool}, hc)
    case Source.Term.Efq{}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Efq{}, True{}, bk) == True{} : Bool}, hc)
    case Source.Term.Eql{+z0, +z1, +z2}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Eql{z0, z1, z2}, True{}, bk) == True{} : Bool}, hc)
    case Source.Term.Rfl{}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Rfl{}, True{}, bk) == True{} : Bool}, hc)
    case Source.Term.Rwt{+z0, +z1, +z2}:
      Shared.Bool.absurd({Source.Term.is_value(Source.Term.Rwt{z0, z1, z2}, True{}, bk) == True{} : Bool}, hc)

def Snoc.rb(+k: List<&2, Nat>, +xs: Machine.Val, +q: Source.Quan, +x: Machine.Val, +bk: List<&2, Source.Def>, h: {Val.ok(xs, Mode.args{}, bk) == True{} : Bool}) ->
  {Val.rb(Machine.Val.call{k, Machine.Args.snoc(xs, q, x)}) == Source.Term.App{q, Val.rb(Machine.Val.call{k, xs}), Val.rb(x)} : Source.Term}:
  Equal.trans(Source.Term, Source.Term.spine(Args.rb(Machine.Args.snoc(xs, q, x)), Source.Term.Ref{k}),
    Source.Term.spine(List.append(&2, Source.Arg, Args.rb(xs), Con{Source.Arg{q, Val.rb(x)}, Nil{}}), Source.Term.Ref{k}),
    Source.Term.App{q, Source.Term.spine(Args.rb(xs), Source.Term.Ref{k}), Val.rb(x)},
    Equal.cong(List<&2, Source.Arg>, Source.Term, z => Source.Term.spine(z, Source.Term.Ref{k}), Args.rb(Machine.Args.snoc(xs, q, x)),
      List.append(&2, Source.Arg, Args.rb(xs), Con{Source.Arg{q, Val.rb(x)}, Nil{}}), Args.snoc_rb(xs, q, x, bk, h)),
    SP.Term.spine_snoc(Args.rb(xs), Source.Term.Ref{k}, q, Val.rb(x)))

def S.call.leaf.of(lw: Machine.Leaf, +k: List<&2, Nat>, +ys: Machine.Val, +fs: List<&2, Machine.Fr>, +bk: List<&2, Source.Def>,
  +hst: {Source.Term.step(Val.rb(Machine.Val.call{k, ys}), bk) == Source.Walk.done_term(Leaf.rb(lw)) : Maybe<&2, Source.Term>},
  +hnt: {Source.Term.is_value(Val.rb(Machine.Val.call{k, ys}), False{}, bk) == Source.Walk.is_need(Leaf.rb(lw)) : Bool},
  +hok: {Leaf.ok(lw, bk) == True{} : Bool}, hys: {Val.ok(ys, Mode.args{}, bk) == True{} : Bool},
  +hfs: {Frs.ok(fs, bk) == True{} : Bool}, -mu: Nat, hmu: {Nat.is_le(1n+Frs.mu(fs, 0n), mu) == True{} : Bool}) ->
  Moved(Machine.Call.leaf(lw, k, ys, fs), Frs.plug(fs, Val.rb(Machine.Val.call{k, ys})), mu, bk):
  match lw:
    case Machine.Leaf.need{}:
      (SP.Bool.and_intro(Val.ok(Machine.Val.call{k, ys}, Mode.good{}, bk), Frs.ok(fs, bk),
        SP.Bool.and_intro(Val.ok(ys, Mode.args{}, bk), Source.Term.is_value(Val.rb(Machine.Val.call{k, ys}), False{}, bk), hys, hnt), hfs),
        Inl{({==}, hmu)})
    case Machine.Leaf.at{+t, +e, +rest}:
      (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(Machine.Args.frames(rest, fs), bk),
        SP.Bool.and_left(Val.ok(e, Mode.env{}, bk), Val.ok(rest, Mode.args{}, bk), hok),
        Frames.ok(rest, fs, bk, SP.Bool.and_right(Val.ok(e, Mode.env{}, bk), Val.ok(rest, Mode.args{}, bk), hok), hfs)),
        Inr{Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Frs.plug(fs, Val.rb(Machine.Val.call{k, ys})), bk),
          Some{Frs.plug(fs, Source.Term.spine(Args.rb(rest), Clo.rb(t, e)))},
          Some{Frs.plug(Machine.Args.frames(rest, fs), Clo.rb(t, e))},
          Ctx.go(fs, Val.rb(Machine.Val.call{k, ys}), Source.Term.spine(Args.rb(rest), Clo.rb(t, e)), bk, hfs, hnt, hst),
          Equal.cong(Source.Term, Maybe<&2, Source.Term>, z => Some{z}, Frs.plug(fs, Source.Term.spine(Args.rb(rest), Clo.rb(t, e))),
            Frs.plug(Machine.Args.frames(rest, fs), Clo.rb(t, e)),
            Equal.sym(Source.Term, Frs.plug(Machine.Args.frames(rest, fs), Clo.rb(t, e)),
              Frs.plug(fs, Source.Term.spine(Args.rb(rest), Clo.rb(t, e))),
              Frames.plug(rest, fs, Clo.rb(t, e), bk, SP.Bool.and_right(Val.ok(e, Mode.env{}, bk), Val.ok(rest, Mode.args{}, bk), hok)))))})
    case Machine.Leaf.fail{}:
      Ctx.stuck(fs, Val.rb(Machine.Val.call{k, ys}), bk, hfs, hnt, hst)

def S.call.leaf(lw: Machine.Leaf, +k: List<&2, Nat>, +ys: Machine.Val, +fs: List<&2, Machine.Fr>, +bk: List<&2, Source.Def>,
  +hw: {Source.Term.walk_call(bk, Val.rb(Machine.Val.call{k, ys})) == Leaf.rb(lw) : Source.Walk}, +hok: {Leaf.ok(lw, bk) == True{} : Bool},
  hys: {Val.ok(ys, Mode.args{}, bk) == True{} : Bool}, +hv: {Source.Term.is_value(Val.rb(Machine.Val.call{k, ys}), True{}, bk) == True{} : Bool},
  +hfs: {Frs.ok(fs, bk) == True{} : Bool}, -mu: Nat, hmu: {Nat.is_le(1n+Frs.mu(fs, 0n), mu) == True{} : Bool}) ->
  Moved(Machine.Call.leaf(lw, k, ys, fs), Frs.plug(fs, Val.rb(Machine.Val.call{k, ys})), mu, bk):
  +hst = Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Val.rb(Machine.Val.call{k, ys}), bk), Source.Term.fires(bk, Val.rb(Machine.Val.call{k, ys})), Source.Walk.done_term(Leaf.rb(lw)),
    Vals.step(Val.rb(Machine.Val.call{k, ys}), True{}, bk, hv),
    Equal.cong(Source.Walk, Maybe<&2, Source.Term>, z => Source.Walk.done_term(z), Source.Term.walk_call(bk, Val.rb(Machine.Val.call{k, ys})), Leaf.rb(lw), hw))
  +hnt = Equal.trans(Bool, Source.Term.is_value(Val.rb(Machine.Val.call{k, ys}), False{}, bk), Source.Term.stops(bk, Val.rb(Machine.Val.call{k, ys})), Source.Walk.is_need(Leaf.rb(lw)),
    Vals.stops(Val.rb(Machine.Val.call{k, ys}), bk, hv),
    Equal.cong(Source.Walk, Bool, z => Source.Walk.is_need(z), Source.Term.walk_call(bk, Val.rb(Machine.Val.call{k, ys})), Leaf.rb(lw), hw))
  S.call.leaf.of(lw, k, ys, fs, bk, hst, hnt, hok, hys, hfs, mu, hmu)


def S.call.walk(+dv: Source.Term, +k: List<&2, Nat>, +ys: Machine.Val, +fs: List<&2, Machine.Fr>, +bk: List<&2, Source.Def>,
  +hwc: {Source.Term.walk_call(bk, Val.rb(Machine.Val.call{k, ys})) == Source.Term.walk(dv, [], Args.rb(ys)) : Source.Walk},
  r: Walk.res(bk, Source.Term.walk(dv, [], Args.rb(ys)), Machine.Walk.go(dv, Machine.Val.nil{}, ys)),
  hys: {Val.ok(ys, Mode.args{}, bk) == True{} : Bool}, +hv: {Source.Term.is_value(Val.rb(Machine.Val.call{k, ys}), True{}, bk) == True{} : Bool},
  +hfs: {Frs.ok(fs, bk) == True{} : Bool}, -mu: Nat, hmu: {Nat.is_le(1n+Frs.mu(fs, 0n), mu) == True{} : Bool}) ->
  Moved(Machine.Call.leaf(Machine.Walk.go(dv, Machine.Val.nil{}, ys), k, ys, fs), Frs.plug(fs, Val.rb(Machine.Val.call{k, ys})), mu, bk):
  match r:
    case (weq, wok):
      S.call.leaf(Machine.Walk.go(dv, Machine.Val.nil{}, ys), k, ys, fs, bk,
        Equal.trans(Source.Walk, Source.Term.walk_call(bk, Val.rb(Machine.Val.call{k, ys})), Source.Term.walk(dv, [], Args.rb(ys)),
          Leaf.rb(Machine.Walk.go(dv, Machine.Val.nil{}, ys)), hwc, weq), wok, hys, hv, hfs, mu, hmu)

def S.call.got(m: Maybe<&2, Source.Def>, +k: List<&2, Nat>, +ys: Machine.Val, +fs: List<&2, Machine.Fr>, +bk: List<&2, Source.Def>,
  +hm: {Source.Book.get(bk, k) == m : Maybe<&2, Source.Def>},
  +hys: {Val.ok(ys, Mode.args{}, bk) == True{} : Bool}, +hv: {Source.Term.is_value(Val.rb(Machine.Val.call{k, ys}), True{}, bk) == True{} : Bool},
  +hfs: {Frs.ok(fs, bk) == True{} : Bool}, -mu: Nat, hmu: {Nat.is_le(1n+Frs.mu(fs, 0n), mu) == True{} : Bool}) ->
  Moved(Machine.Call.got(m, k, ys, fs), Frs.plug(fs, Val.rb(Machine.Val.call{k, ys})), mu, bk):
  match m:
    case None{}:
      +hwc = Equal.trans(Source.Walk, Source.Term.walk_call(bk, Val.rb(Machine.Val.call{k, ys})), Source.Term.walk_call.got(Source.Book.get(bk, k), Args.rb(ys)),
        Source.Walk.fail{}, Call.walk_eq(bk, k, Args.rb(ys)),
        Equal.cong(Maybe<&2, Source.Def>, Source.Walk, z => Source.Term.walk_call.got(z, Args.rb(ys)), Source.Book.get(bk, k), None{}, hm))
      Ctx.stuck(fs, Val.rb(Machine.Val.call{k, ys}), bk, hfs,
        Equal.trans(Bool, Source.Term.is_value(Val.rb(Machine.Val.call{k, ys}), False{}, bk), Source.Term.stops(bk, Val.rb(Machine.Val.call{k, ys})), False{}, Vals.stops(Val.rb(Machine.Val.call{k, ys}), bk, hv),
          Equal.cong(Source.Walk, Bool, z => Source.Walk.is_need(z), Source.Term.walk_call(bk, Val.rb(Machine.Val.call{k, ys})), Source.Walk.fail{}, hwc)),
        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Val.rb(Machine.Val.call{k, ys}), bk), Source.Term.fires(bk, Val.rb(Machine.Val.call{k, ys})), None{}, Vals.step(Val.rb(Machine.Val.call{k, ys}), True{}, bk, hv),
          Equal.cong(Source.Walk, Maybe<&2, Source.Term>, z => Source.Walk.done_term(z), Source.Term.walk_call(bk, Val.rb(Machine.Val.call{k, ys})), Source.Walk.fail{}, hwc)))
    case Some{Source.Def{dn, dt, +dv, dop}}:
      S.call.walk(dv, k, ys, fs, bk,
        Equal.trans(Source.Walk, Source.Term.walk_call(bk, Val.rb(Machine.Val.call{k, ys})), Source.Term.walk_call.got(Source.Book.get(bk, k), Args.rb(ys)),
          Source.Term.walk(dv, [], Args.rb(ys)), Call.walk_eq(bk, k, Args.rb(ys)),
          Equal.cong(Maybe<&2, Source.Def>, Source.Walk, z => Source.Term.walk_call.got(z, Args.rb(ys)), Source.Book.get(bk, k),
            Some{Source.Def{dn, dt, dv, dop}}, hm)),
        Walk.eq(dv, Machine.Val.nil{}, ys, bk, {==}, hys), hys, hv, hfs, mu, hmu)

# the step of a call of def k on ys
def S.call(+k: List<&2, Nat>, +ys: Machine.Val, +fs: List<&2, Machine.Fr>, +bk: List<&2, Source.Def>,
  hys: {Val.ok(ys, Mode.args{}, bk) == True{} : Bool}, hv: {Source.Term.is_value(Val.rb(Machine.Val.call{k, ys}), True{}, bk) == True{} : Bool},
  hfs: {Frs.ok(fs, bk) == True{} : Bool}, -mu: Nat, hmu: {Nat.is_le(1n+Frs.mu(fs, 0n), mu) == True{} : Bool}) ->
  Moved(Machine.Call.try(bk, k, ys, fs), Frs.plug(fs, Val.rb(Machine.Val.call{k, ys})), mu, bk):
  S.call.got(Source.Book.get(bk, k), k, ys, fs, bk, {==}, hys, hv, hfs, mu, hmu)

def Prj.dead(-h: Source.Term, x: Source.Term, -bk: List<&2, Source.Def>) -> {Source.Term.redex.prj(bk, Source.Q0{}, h, x) == None{} : Maybe<&2, Source.Term>}:
  match x:
    case Source.Term.Var{z0}:
      {==}
    case Source.Term.Ref{z0}:
      {==}
    case Source.Term.Ann{z0, z1}:
      {==}
    case Source.Term.Let{z0, z1, z2}:
      {==}
    case Source.Term.Typ{z0}:
      {==}
    case Source.Term.Min{z0, z1}:
      {==}
    case Source.Term.All{z0, z1, z2}:
      {==}
    case Source.Term.Lam{z0, z1}:
      {==}
    case Source.Term.App{z0, z1, z2}:
      {==}
    case Source.Term.Sig{z0, z1, z2}:
      {==}
    case Source.Term.Tup{z0, z1, z2}:
      {==}
    case Source.Term.Prj{z0}:
      {==}
    case Source.Term.Enu{z0}:
      {==}
    case Source.Term.Lab{z0}:
      {==}
    case Source.Term.Mat{z0, z1, z2}:
      {==}
    case Source.Term.Efq{}:
      {==}
    case Source.Term.Eql{z0, z1, z2}:
      {==}
    case Source.Term.Rfl{}:
      {==}
    case Source.Term.Rwt{z0, z1, z2}:
      {==}

def Mat.dead(-k: List<&2, Nat>, -h: Source.Term, -m: Source.Term, x: Source.Term, -bk: List<&2, Source.Def>) -> {Source.Term.redex.mat(Source.Q0{}, k, h, m, x) == None{} : Maybe<&2, Source.Term>}:
  match x:
    case Source.Term.Var{z0}:
      {==}
    case Source.Term.Ref{z0}:
      {==}
    case Source.Term.Ann{z0, z1}:
      {==}
    case Source.Term.Let{z0, z1, z2}:
      {==}
    case Source.Term.Typ{z0}:
      {==}
    case Source.Term.Min{z0, z1}:
      {==}
    case Source.Term.All{z0, z1, z2}:
      {==}
    case Source.Term.Lam{z0, z1}:
      {==}
    case Source.Term.App{z0, z1, z2}:
      {==}
    case Source.Term.Sig{z0, z1, z2}:
      {==}
    case Source.Term.Tup{z0, z1, z2}:
      {==}
    case Source.Term.Prj{z0}:
      {==}
    case Source.Term.Enu{z0}:
      {==}
    case Source.Term.Lab{z0}:
      {==}
    case Source.Term.Mat{z0, z1, z2}:
      {==}
    case Source.Term.Efq{}:
      {==}
    case Source.Term.Eql{z0, z1, z2}:
      {==}
    case Source.Term.Rfl{}:
      {==}
    case Source.Term.Rwt{z0, z1, z2}:
      {==}

def Prj.live.Q1(-h: Source.Term, +r: Source.Quan, -a: Source.Term, -b: Source.Term, +bk: List<&2, Source.Def>,
  hv: {Source.Term.is_value(Source.Term.Tup{r, a, b}, False{}, bk) == True{} : Bool}) ->
  {Source.Term.redex.prj(bk, Source.Q1{}, h, Source.Term.Tup{r, a, b}) ==
    Some{Source.Term.App{Source.Q1{}, Source.Term.App{Source.Quan.fld(r, Source.Q1{}), h, a}, b}} : Maybe<&2, Source.Term>}:
  %Equal.sym(Bool, Source.Term.is_value(Source.Term.Tup{r, a, b}, False{}, bk), True{}, hv) :
    {Source.Maybe.when(Source.Term, _, w => Some{Source.Term.App{Source.Q1{}, Source.Term.App{Source.Quan.fld(r, Source.Q1{}), h, a}, b}}) ==
      Some{Source.Term.App{Source.Q1{}, Source.Term.App{Source.Quan.fld(r, Source.Q1{}), h, a}, b}} : Maybe<&2, Source.Term>}
  {==}

def Prj.live.Q2(-h: Source.Term, +r: Source.Quan, -a: Source.Term, -b: Source.Term, +bk: List<&2, Source.Def>,
  hv: {Source.Term.is_value(Source.Term.Tup{r, a, b}, False{}, bk) == True{} : Bool}) ->
  {Source.Term.redex.prj(bk, Source.Q2{}, h, Source.Term.Tup{r, a, b}) ==
    Some{Source.Term.App{Source.Q2{}, Source.Term.App{Source.Quan.fld(r, Source.Q2{}), h, a}, b}} : Maybe<&2, Source.Term>}:
  %Equal.sym(Bool, Source.Term.is_value(Source.Term.Tup{r, a, b}, False{}, bk), True{}, hv) :
    {Source.Maybe.when(Source.Term, _, w => Some{Source.Term.App{Source.Q2{}, Source.Term.App{Source.Quan.fld(r, Source.Q2{}), h, a}, b}}) ==
      Some{Source.Term.App{Source.Q2{}, Source.Term.App{Source.Quan.fld(r, Source.Q2{}), h, a}, b}} : Maybe<&2, Source.Term>}
  {==}

def Lam.step(+q: Source.Quan, +p: Source.Quan, +b: Source.Term, +x: Machine.Val, +bk: List<&2, Source.Def>,
  +hx: {Val.ok(x, Mode.field(q), bk) == True{} : Bool}) ->
  {Source.Term.step(Source.Term.App{q, Source.Term.Lam{p, b}, Val.rb(x)}, bk) ==
    Source.Maybe.when(Source.Term, Bool.and(Source.Bool.is_eq(Source.Quan.live(p), Source.Quan.live(q)), Bool.or(Bool.not(Source.Quan.is_q2(p)), Source.Term.is_data(Val.rb(x)))), w => Some{Source.Term.sub(b, 0n, Source.Sub.one{Val.rb(x)})}) : Maybe<&2, Source.Term>}:
  %Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{q, Source.Term.Lam{p, b}, Val.rb(x)}, bk), Source.Term.redex(bk, q, Source.Term.Lam{p, b}, Val.rb(x)),
    App.red(q, Source.Term.Lam{p, b}, x, bk, {==}, {==}, hx)) :
    {_ == Source.Maybe.when(Source.Term, Bool.and(Source.Bool.is_eq(Source.Quan.live(p), Source.Quan.live(q)), Bool.or(Bool.not(Source.Quan.is_q2(p)), Source.Term.is_data(Val.rb(x)))), w => Some{Source.Term.sub(b, 0n, Source.Sub.one{Val.rb(x)})}) : Maybe<&2, Source.Term>}
  %Equal.sym(Bool, Bool.or(Bool.not(Source.Quan.live(q)), Source.Term.is_value(Val.rb(x), False{}, bk)), True{}, Field.value(q, x, bk, hx)) :
    {Source.Maybe.when(Source.Term, Bool.and(Bool.and(Source.Bool.is_eq(Source.Quan.live(p), Source.Quan.live(q)), _),
      Bool.or(Bool.not(Source.Quan.is_q2(p)), Source.Term.is_data(Val.rb(x)))), w => Some{Source.Term.sub(b, 0n, Source.Sub.one{Val.rb(x)})}) ==
      Source.Maybe.when(Source.Term, Bool.and(Source.Bool.is_eq(Source.Quan.live(p), Source.Quan.live(q)), Bool.or(Bool.not(Source.Quan.is_q2(p)), Source.Term.is_data(Val.rb(x)))), w => Some{Source.Term.sub(b, 0n, Source.Sub.one{Val.rb(x)})}) : Maybe<&2, Source.Term>}
  %Equal.sym(Bool, Bool.and(Source.Bool.is_eq(Source.Quan.live(p), Source.Quan.live(q)), True{}), Source.Bool.is_eq(Source.Quan.live(p), Source.Quan.live(q)),
    Bool.and_true(Source.Bool.is_eq(Source.Quan.live(p), Source.Quan.live(q)))) :
    {Source.Maybe.when(Source.Term, Bool.and(_, Bool.or(Bool.not(Source.Quan.is_q2(p)), Source.Term.is_data(Val.rb(x)))),
      w => Some{Source.Term.sub(b, 0n, Source.Sub.one{Val.rb(x)})}) ==
      Source.Maybe.when(Source.Term, Bool.and(Source.Bool.is_eq(Source.Quan.live(p), Source.Quan.live(q)), Bool.or(Bool.not(Source.Quan.is_q2(p)), Source.Term.is_data(Val.rb(x)))), w => Some{Source.Term.sub(b, 0n, Source.Sub.one{Val.rb(x)})}) : Maybe<&2, Source.Term>}
  {==}

def S.lam.of(c: Bool, +q: Source.Quan, +p: Source.Quan, +b: Source.Term, +e: Machine.Val, +x: Machine.Val, +fs: List<&2, Machine.Fr>,
  +bk: List<&2, Source.Def>, he: {Val.ok(e, Mode.env{}, bk) == True{} : Bool}, hx: {Val.ok(x, Mode.field(q), bk) == True{} : Bool},
  +hfs: {Frs.ok(fs, bk) == True{} : Bool}, -mu: Nat,
  hst: {Source.Term.step(Source.Term.App{q, Source.Term.Lam{p, Source.Term.sub(b, 1n, Source.Sub.env{Env.rb(e)})}, Val.rb(x)}, bk) ==
    Source.Maybe.when(Source.Term, c, w => Some{Source.Term.sub(Source.Term.sub(b, 1n, Source.Sub.env{Env.rb(e)}), 0n, Source.Sub.one{Val.rb(x)})}) : Maybe<&2, Source.Term>}) ->
  Moved(Source.Bool.lazy(Machine.Move, c, u => Machine.Move.go{Machine.St.eval{b, Machine.Val.env{x, e}, fs}}, u => Machine.Move.stuck{}),
    Frs.plug(fs, Source.Term.App{q, Source.Term.Lam{p, Source.Term.sub(b, 1n, Source.Sub.env{Env.rb(e)})}, Val.rb(x)}), mu, bk):
  match c:
    case True{}:
      (SP.Bool.and_intro(Bool.and(Val.ok(x, Mode.any{}, bk), Val.ok(e, Mode.env{}, bk)), Frs.ok(fs, bk),
        SP.Bool.and_intro(Val.ok(x, Mode.any{}, bk), Val.ok(e, Mode.env{}, bk), Field.any(q, x, bk, hx), he), hfs),
        Inr{Ctx.go(fs, Source.Term.App{q, Source.Term.Lam{p, Source.Term.sub(b, 1n, Source.Sub.env{Env.rb(e)})}, Val.rb(x)}, Clo.rb(b, Machine.Val.env{x, e}), bk, hfs, {==},
          Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{q, Source.Term.Lam{p, Source.Term.sub(b, 1n, Source.Sub.env{Env.rb(e)})}, Val.rb(x)}, bk), Some{Source.Term.sub(Source.Term.sub(b, 1n, Source.Sub.env{Env.rb(e)}), 0n, Source.Sub.one{Val.rb(x)})},
            Some{Clo.rb(b, Machine.Val.env{x, e})}, hst,
            Equal.cong(Source.Term, Maybe<&2, Source.Term>, z => Some{z}, Source.Term.sub(Source.Term.sub(b, 1n, Source.Sub.env{Env.rb(e)}), 0n, Source.Sub.one{Val.rb(x)}),
              Clo.rb(b, Machine.Val.env{x, e}), Term.sub_sub(b, 0n, Env.rb(e), Val.rb(x)))))})
    case False{}:
      Ctx.stuck(fs, Source.Term.App{q, Source.Term.Lam{p, Source.Term.sub(b, 1n, Source.Sub.env{Env.rb(e)})}, Val.rb(x)}, bk, hfs, {==}, hst)

def S.lam(+q: Source.Quan, +p: Source.Quan, +b: Source.Term, +e: Machine.Val, +x: Machine.Val, +fs: List<&2, Machine.Fr>,
  +bk: List<&2, Source.Def>, he: {Val.ok(e, Mode.env{}, bk) == True{} : Bool}, +hx: {Val.ok(x, Mode.field(q), bk) == True{} : Bool},
  hfs: {Frs.ok(fs, bk) == True{} : Bool}, -mu: Nat) ->
  Moved(Source.Bool.lazy(Machine.Move,
    Bool.and(Source.Bool.is_eq(Source.Quan.live(p), Source.Quan.live(q)), Bool.or(Bool.not(Source.Quan.is_q2(p)), Machine.Val.is_data(x))),
    u => Machine.Move.go{Machine.St.eval{b, Machine.Val.env{x, e}, fs}}, u => Machine.Move.stuck{}),
    Frs.plug(fs, Source.Term.App{q, Source.Term.Lam{p, Source.Term.sub(b, 1n, Source.Sub.env{Env.rb(e)})}, Val.rb(x)}), mu, bk):
  %Equal.sym(Bool, Machine.Val.is_data(x), Source.Term.is_data(Val.rb(x)), Data.val(x, bk, Field.any(q, x, bk, hx))) :
    Moved(Source.Bool.lazy(Machine.Move,
      Bool.and(Source.Bool.is_eq(Source.Quan.live(p), Source.Quan.live(q)), Bool.or(Bool.not(Source.Quan.is_q2(p)), _)),
      u => Machine.Move.go{Machine.St.eval{b, Machine.Val.env{x, e}, fs}}, u => Machine.Move.stuck{}),
      Frs.plug(fs, Source.Term.App{q, Source.Term.Lam{p, Source.Term.sub(b, 1n, Source.Sub.env{Env.rb(e)})}, Val.rb(x)}), mu, bk)
  S.lam.of(Bool.and(Source.Bool.is_eq(Source.Quan.live(p), Source.Quan.live(q)), Bool.or(Bool.not(Source.Quan.is_q2(p)), Source.Term.is_data(Val.rb(x)))), q, p, b, e, x, fs, bk, he, hx, hfs, mu, Lam.step(q, p, Source.Term.sub(b, 1n, Source.Sub.env{Env.rb(e)}), x, bk, hx))

def S.mat.of(c: Bool, +q: Source.Quan, +k: List<&2, Nat>, +h: Source.Term, +m: Source.Term, +e: Machine.Val, +j: List<&2, Nat>,
  +fs: List<&2, Machine.Fr>, +bk: List<&2, Source.Def>, +he: {Val.ok(e, Mode.env{}, bk) == True{} : Bool},
  +hfs: {Frs.ok(fs, bk) == True{} : Bool}, -mu: Nat,
  hst: {Source.Term.step(Source.Term.App{q, Source.Term.Mat{k, Source.Term.sub(h, 0n, Source.Sub.env{Env.rb(e)}), Source.Term.sub(m, 0n, Source.Sub.env{Env.rb(e)})}, Source.Term.Lab{j}}, bk) ==
    Source.Bool.if(Maybe<&2, Source.Term>, c, Some{Source.Term.sub(h, 0n, Source.Sub.env{Env.rb(e)})}, Some{Source.Term.App{q, Source.Term.sub(m, 0n, Source.Sub.env{Env.rb(e)}), Source.Term.Lab{j}}}) : Maybe<&2, Source.Term>}) ->
  Moved(Source.Bool.lazy(Machine.Move, c, u => Machine.Move.go{Machine.St.eval{h, e, fs}},
    u => Machine.Move.go{Machine.St.eval{m, e, Con{Machine.Fr.arg{q, Machine.Val.lab{j}}, fs}}}),
    Frs.plug(fs, Source.Term.App{q, Source.Term.Mat{k, Source.Term.sub(h, 0n, Source.Sub.env{Env.rb(e)}), Source.Term.sub(m, 0n, Source.Sub.env{Env.rb(e)})}, Source.Term.Lab{j}}), mu, bk):
  match c:
    case True{}:
      (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(fs, bk), he, hfs),
        Inr{Ctx.go(fs, Source.Term.App{q, Source.Term.Mat{k, Source.Term.sub(h, 0n, Source.Sub.env{Env.rb(e)}), Source.Term.sub(m, 0n, Source.Sub.env{Env.rb(e)})}, Source.Term.Lab{j}}, Clo.rb(h, e), bk, hfs, {==}, hst)})
    case False{}:
      (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Bool.and(True{}, Frs.ok(fs, bk)), he, hfs),
        Inr{Ctx.go(fs, Source.Term.App{q, Source.Term.Mat{k, Source.Term.sub(h, 0n, Source.Sub.env{Env.rb(e)}), Source.Term.sub(m, 0n, Source.Sub.env{Env.rb(e)})}, Source.Term.Lab{j}}, Source.Term.App{q, Clo.rb(m, e), Source.Term.Lab{j}}, bk, hfs, {==}, hst)})

# the step after the value f takes x at q
def S.apply(f: Machine.Val, +q: Source.Quan, +x: Machine.Val, +fs: List<&2, Machine.Fr>, +bk: List<&2, Source.Def>,
  +hf: {Val.ok(f, Mode.good{}, bk) == True{} : Bool}, +hx: {Val.ok(x, Mode.field(q), bk) == True{} : Bool},
  +hfs: {Frs.ok(fs, bk) == True{} : Bool}, -mu: Nat, hmu: {Nat.is_le(1n+Frs.mu(fs, 0n), mu) == True{} : Bool}) ->
  Moved(Machine.Apply.go(f, q, x, bk, fs), Frs.plug(fs, Source.Term.App{q, Val.rb(f), Val.rb(x)}), mu, bk):
  match f:
    case Machine.Val.nil{}:
      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.nil{}, q, x, bk, fs), Frs.plug(fs, Source.Term.App{q, Val.rb(Machine.Val.nil{}), Val.rb(x)}), mu, bk), hf)
    case Machine.Val.env{+v0, +v1}:
      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.env{v0, v1}, q, x, bk, fs), Frs.plug(fs, Source.Term.App{q, Val.rb(Machine.Val.env{v0, v1}), Val.rb(x)}), mu, bk), hf)
    case Machine.Val.arg{+v0, +v1, +v2}:
      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.arg{v0, v1, v2}, q, x, bk, fs), Frs.plug(fs, Source.Term.App{q, Val.rb(Machine.Val.arg{v0, v1, v2}), Val.rb(x)}), mu, bk), hf)
    case Machine.Val.clo{+v0, +v1}:
      match v0:
        case Source.Term.Var{+z0}:
          Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Var{z0}, v1}, q, x, bk, fs), Frs.plug(fs, Source.Term.App{q, Val.rb(Machine.Val.clo{Source.Term.Var{z0}, v1}), Val.rb(x)}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Var{z0}), Val.ok(v1, Mode.env{}, bk), hf))
        case Source.Term.Ref{+z0}:
          Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Ref{z0}, v1}, q, x, bk, fs), Frs.plug(fs, Source.Term.App{q, Val.rb(Machine.Val.clo{Source.Term.Ref{z0}, v1}), Val.rb(x)}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Ref{z0}), Val.ok(v1, Mode.env{}, bk), hf))
        case Source.Term.Ann{+z0, +z1}:
          Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Ann{z0, z1}, v1}, q, x, bk, fs), Frs.plug(fs, Source.Term.App{q, Val.rb(Machine.Val.clo{Source.Term.Ann{z0, z1}, v1}), Val.rb(x)}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Ann{z0, z1}), Val.ok(v1, Mode.env{}, bk), hf))
        case Source.Term.Let{+z0, +z1, +z2}:
          Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Let{z0, z1, z2}, v1}, q, x, bk, fs), Frs.plug(fs, Source.Term.App{q, Val.rb(Machine.Val.clo{Source.Term.Let{z0, z1, z2}, v1}), Val.rb(x)}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Let{z0, z1, z2}), Val.ok(v1, Mode.env{}, bk), hf))
        case Source.Term.Typ{+z0}:
          Ctx.stuck(fs, Source.Term.App{q, Val.rb(Machine.Val.clo{Source.Term.Typ{z0}, v1}), Val.rb(x)}, bk, hfs, App.nv(q, Val.rb(Machine.Val.clo{Source.Term.Typ{z0}, v1}), Val.rb(x), bk, {==}),
            Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{q, Val.rb(Machine.Val.clo{Source.Term.Typ{z0}, v1}), Val.rb(x)}, bk), Source.Term.redex(bk, q, Val.rb(Machine.Val.clo{Source.Term.Typ{z0}, v1}), Val.rb(x)), None{},
              App.red(q, Val.rb(Machine.Val.clo{Source.Term.Typ{z0}, v1}), x, bk, {==}, {==}, hx), {==}))
        case Source.Term.Min{+z0, +z1}:
          Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Min{z0, z1}, v1}, q, x, bk, fs), Frs.plug(fs, Source.Term.App{q, Val.rb(Machine.Val.clo{Source.Term.Min{z0, z1}, v1}), Val.rb(x)}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Min{z0, z1}), Val.ok(v1, Mode.env{}, bk), hf))
        case Source.Term.All{+z0, +z1, +z2}:
          Ctx.stuck(fs, Source.Term.App{q, Val.rb(Machine.Val.clo{Source.Term.All{z0, z1, z2}, v1}), Val.rb(x)}, bk, hfs, App.nv(q, Val.rb(Machine.Val.clo{Source.Term.All{z0, z1, z2}, v1}), Val.rb(x), bk, {==}),
            Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{q, Val.rb(Machine.Val.clo{Source.Term.All{z0, z1, z2}, v1}), Val.rb(x)}, bk), Source.Term.redex(bk, q, Val.rb(Machine.Val.clo{Source.Term.All{z0, z1, z2}, v1}), Val.rb(x)), None{},
              App.red(q, Val.rb(Machine.Val.clo{Source.Term.All{z0, z1, z2}, v1}), x, bk, {==}, {==}, hx), {==}))
        case Source.Term.Lam{+z0, +z1}:
          S.lam(q, z0, z1, v1, x, fs, bk, hf, hx, hfs, mu)
        case Source.Term.App{+z0, +z1, +z2}:
          Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.App{z0, z1, z2}, v1}, q, x, bk, fs), Frs.plug(fs, Source.Term.App{q, Val.rb(Machine.Val.clo{Source.Term.App{z0, z1, z2}, v1}), Val.rb(x)}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.App{z0, z1, z2}), Val.ok(v1, Mode.env{}, bk), hf))
        case Source.Term.Sig{+z0, +z1, +z2}:
          Ctx.stuck(fs, Source.Term.App{q, Val.rb(Machine.Val.clo{Source.Term.Sig{z0, z1, z2}, v1}), Val.rb(x)}, bk, hfs, App.nv(q, Val.rb(Machine.Val.clo{Source.Term.Sig{z0, z1, z2}, v1}), Val.rb(x), bk, {==}),
            Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{q, Val.rb(Machine.Val.clo{Source.Term.Sig{z0, z1, z2}, v1}), Val.rb(x)}, bk), Source.Term.redex(bk, q, Val.rb(Machine.Val.clo{Source.Term.Sig{z0, z1, z2}, v1}), Val.rb(x)), None{},
              App.red(q, Val.rb(Machine.Val.clo{Source.Term.Sig{z0, z1, z2}, v1}), x, bk, {==}, {==}, hx), {==}))
        case Source.Term.Tup{+z0, +z1, +z2}:
          Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Tup{z0, z1, z2}, v1}, q, x, bk, fs), Frs.plug(fs, Source.Term.App{q, Val.rb(Machine.Val.clo{Source.Term.Tup{z0, z1, z2}, v1}), Val.rb(x)}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Tup{z0, z1, z2}), Val.ok(v1, Mode.env{}, bk), hf))
        case Source.Term.Prj{+z0}:
          match q:
            case Source.Q0{}:
              Ctx.stuck(fs, Source.Term.App{Source.Q0{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(x)}, bk, hfs, App.nv(Source.Q0{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(x), bk, {==}),
                Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q0{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(x)}, bk), Source.Term.redex(bk, Source.Q0{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(x)), None{},
                  App.red(Source.Q0{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, x, bk, {==}, {==}, hx), Prj.dead(Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)}), Val.rb(x), bk)))
            case Source.Q1{}:
              match x:
                case Machine.Val.nil{}:
                  Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q1{}, Machine.Val.nil{}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.nil{})}), mu, bk), hx)
                case Machine.Val.env{+y0, +y1}:
                  Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q1{}, Machine.Val.env{y0, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.env{y0, y1})}), mu, bk), hx)
                case Machine.Val.arg{+y0, +y1, +y2}:
                  Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q1{}, Machine.Val.arg{y0, y1, y2}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.arg{y0, y1, y2})}), mu, bk), hx)
                case Machine.Val.clo{+y0, +y1}:
                  match y0:
                    case Source.Term.Var{+s0}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q1{}, Machine.Val.clo{Source.Term.Var{s0}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.clo{Source.Term.Var{s0}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Var{s0}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Ref{+s0}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q1{}, Machine.Val.clo{Source.Term.Ref{s0}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.clo{Source.Term.Ref{s0}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Ref{s0}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Ann{+s0, +s1}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q1{}, Machine.Val.clo{Source.Term.Ann{s0, s1}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.clo{Source.Term.Ann{s0, s1}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Ann{s0, s1}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Let{+s0, +s1, +s2}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q1{}, Machine.Val.clo{Source.Term.Let{s0, s1, s2}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.clo{Source.Term.Let{s0, s1, s2}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Let{s0, s1, s2}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Typ{+s0}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Typ{s0}, y1})}, bk, hfs, App.nv(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Typ{s0}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Typ{s0}, y1})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Typ{s0}, y1})), None{},
                          App.red(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Typ{s0}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Min{+s0, +s1}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q1{}, Machine.Val.clo{Source.Term.Min{s0, s1}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.clo{Source.Term.Min{s0, s1}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Min{s0, s1}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.All{+s0, +s1, +s2}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.All{s0, s1, s2}, y1})}, bk, hfs, App.nv(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.All{s0, s1, s2}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.All{s0, s1, s2}, y1})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.All{s0, s1, s2}, y1})), None{},
                          App.red(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.All{s0, s1, s2}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Lam{+s0, +s1}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Lam{s0, s1}, y1})}, bk, hfs, App.nv(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Lam{s0, s1}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Lam{s0, s1}, y1})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Lam{s0, s1}, y1})), None{},
                          App.red(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Lam{s0, s1}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.App{+s0, +s1, +s2}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q1{}, Machine.Val.clo{Source.Term.App{s0, s1, s2}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.clo{Source.Term.App{s0, s1, s2}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.App{s0, s1, s2}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Sig{+s0, +s1, +s2}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Sig{s0, s1, s2}, y1})}, bk, hfs, App.nv(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Sig{s0, s1, s2}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Sig{s0, s1, s2}, y1})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Sig{s0, s1, s2}, y1})), None{},
                          App.red(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Sig{s0, s1, s2}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Tup{+s0, +s1, +s2}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q1{}, Machine.Val.clo{Source.Term.Tup{s0, s1, s2}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.clo{Source.Term.Tup{s0, s1, s2}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Tup{s0, s1, s2}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Prj{+s0}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Prj{s0}, y1})}, bk, hfs, App.nv(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Prj{s0}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Prj{s0}, y1})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Prj{s0}, y1})), None{},
                          App.red(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Prj{s0}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Enu{+s0}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Enu{s0}, y1})}, bk, hfs, App.nv(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Enu{s0}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Enu{s0}, y1})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Enu{s0}, y1})), None{},
                          App.red(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Enu{s0}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Lab{+s0}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q1{}, Machine.Val.clo{Source.Term.Lab{s0}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.clo{Source.Term.Lab{s0}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Lab{s0}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Mat{+s0, +s1, +s2}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Mat{s0, s1, s2}, y1})}, bk, hfs, App.nv(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Mat{s0, s1, s2}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Mat{s0, s1, s2}, y1})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Mat{s0, s1, s2}, y1})), None{},
                          App.red(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Mat{s0, s1, s2}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Efq{}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Efq{}, y1})}, bk, hfs, App.nv(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Efq{}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Efq{}, y1})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Efq{}, y1})), None{},
                          App.red(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Efq{}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Eql{+s0, +s1, +s2}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Eql{s0, s1, s2}, y1})}, bk, hfs, App.nv(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Eql{s0, s1, s2}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Eql{s0, s1, s2}, y1})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Eql{s0, s1, s2}, y1})), None{},
                          App.red(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Eql{s0, s1, s2}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Rfl{}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q1{}, Machine.Val.clo{Source.Term.Rfl{}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.clo{Source.Term.Rfl{}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Rfl{}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Rwt{+s0, +s1, +s2}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q1{}, Machine.Val.clo{Source.Term.Rwt{s0, s1, s2}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.clo{Source.Term.Rwt{s0, s1, s2}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Rwt{s0, s1, s2}), Val.ok(y1, Mode.env{}, bk), hx))
                case Machine.Val.lab{+y0}:
                  Ctx.stuck(fs, Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.lab{y0})}, bk, hfs, App.nv(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.lab{y0}), bk, {==}),
                    Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.lab{y0})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.lab{y0})), None{},
                      App.red(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.lab{y0}, bk, {==}, {==}, hx), {==}))
                case Machine.Val.rfl{}:
                  Ctx.stuck(fs, Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.rfl{})}, bk, hfs, App.nv(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.rfl{}), bk, {==}),
                    Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.rfl{})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.rfl{})), None{},
                      App.red(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.rfl{}, bk, {==}, {==}, hx), {==}))
                case Machine.Val.tup{+y0, +y1, +y2}:
                  (SP.Bool.and_intro(Val.ok(v1, Mode.env{}, bk), Bool.and(Val.ok(y1, Mode.any{}, bk), Bool.and(Val.ok(y2, Mode.any{}, bk), Frs.ok(fs, bk))), hf,
                    SP.Bool.and_intro(Val.ok(y1, Mode.any{}, bk), Bool.and(Val.ok(y2, Mode.any{}, bk), Frs.ok(fs, bk)), Field.any(y0, y1, bk, SP.Bool.and_left(Val.ok(y1, Mode.field(y0), bk), Val.ok(y2, Mode.good{}, bk), hx)),
                      SP.Bool.and_intro(Val.ok(y2, Mode.any{}, bk), Frs.ok(fs, bk), Good.any(y2, bk, SP.Bool.and_right(Val.ok(y1, Mode.field(y0), bk), Val.ok(y2, Mode.good{}, bk), hx)), hfs))),
                    Inr{Ctx.go(fs, Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.tup{y0, y1, y2})}, Source.Term.App{Source.Q1{}, Source.Term.App{Source.Quan.fld(y0, Source.Q1{}), Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)}), Val.rb(y1)}, Val.rb(y2)}, bk, hfs, {==},
                      Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.tup{y0, y1, y2})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.tup{y0, y1, y2})), Some{Source.Term.App{Source.Q1{}, Source.Term.App{Source.Quan.fld(y0, Source.Q1{}), Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)}), Val.rb(y1)}, Val.rb(y2)}},
                        App.red(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.tup{y0, y1, y2}, bk, {==}, {==}, hx), Prj.live.Q1(Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)}), y0, Val.rb(y1), Val.rb(y2), bk, Val.value(Machine.Val.tup{y0, y1, y2}, bk, hx))))})
                case Machine.Val.call{+y0, +y1}:
                  Ctx.stuck(fs, Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.call{y0, y1})}, bk, hfs, App.nv(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.call{y0, y1}), bk, {==}),
                    Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.call{y0, y1})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.call{y0, y1})), None{},
                      App.red(Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.call{y0, y1}, bk, {==}, {==}, hx), Call.elim(Val.rb(Machine.Val.call{y0, y1}), Call.rb_is_call(y0, y1), z => {Source.Term.redex(bk, Source.Q1{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, z) == None{} : Maybe<&2, Source.Term>}, q2 => f2 => x2 => {==}, n => {==})))
            case Source.Q2{}:
              match x:
                case Machine.Val.nil{}:
                  Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q2{}, Machine.Val.nil{}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.nil{})}), mu, bk), hx)
                case Machine.Val.env{+y0, +y1}:
                  Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q2{}, Machine.Val.env{y0, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.env{y0, y1})}), mu, bk), hx)
                case Machine.Val.arg{+y0, +y1, +y2}:
                  Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q2{}, Machine.Val.arg{y0, y1, y2}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.arg{y0, y1, y2})}), mu, bk), hx)
                case Machine.Val.clo{+y0, +y1}:
                  match y0:
                    case Source.Term.Var{+s0}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q2{}, Machine.Val.clo{Source.Term.Var{s0}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.clo{Source.Term.Var{s0}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Var{s0}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Ref{+s0}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q2{}, Machine.Val.clo{Source.Term.Ref{s0}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.clo{Source.Term.Ref{s0}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Ref{s0}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Ann{+s0, +s1}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q2{}, Machine.Val.clo{Source.Term.Ann{s0, s1}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.clo{Source.Term.Ann{s0, s1}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Ann{s0, s1}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Let{+s0, +s1, +s2}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q2{}, Machine.Val.clo{Source.Term.Let{s0, s1, s2}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.clo{Source.Term.Let{s0, s1, s2}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Let{s0, s1, s2}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Typ{+s0}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Typ{s0}, y1})}, bk, hfs, App.nv(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Typ{s0}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Typ{s0}, y1})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Typ{s0}, y1})), None{},
                          App.red(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Typ{s0}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Min{+s0, +s1}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q2{}, Machine.Val.clo{Source.Term.Min{s0, s1}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.clo{Source.Term.Min{s0, s1}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Min{s0, s1}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.All{+s0, +s1, +s2}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.All{s0, s1, s2}, y1})}, bk, hfs, App.nv(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.All{s0, s1, s2}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.All{s0, s1, s2}, y1})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.All{s0, s1, s2}, y1})), None{},
                          App.red(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.All{s0, s1, s2}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Lam{+s0, +s1}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Lam{s0, s1}, y1})}, bk, hfs, App.nv(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Lam{s0, s1}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Lam{s0, s1}, y1})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Lam{s0, s1}, y1})), None{},
                          App.red(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Lam{s0, s1}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.App{+s0, +s1, +s2}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q2{}, Machine.Val.clo{Source.Term.App{s0, s1, s2}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.clo{Source.Term.App{s0, s1, s2}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.App{s0, s1, s2}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Sig{+s0, +s1, +s2}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Sig{s0, s1, s2}, y1})}, bk, hfs, App.nv(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Sig{s0, s1, s2}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Sig{s0, s1, s2}, y1})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Sig{s0, s1, s2}, y1})), None{},
                          App.red(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Sig{s0, s1, s2}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Tup{+s0, +s1, +s2}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q2{}, Machine.Val.clo{Source.Term.Tup{s0, s1, s2}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.clo{Source.Term.Tup{s0, s1, s2}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Tup{s0, s1, s2}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Prj{+s0}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Prj{s0}, y1})}, bk, hfs, App.nv(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Prj{s0}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Prj{s0}, y1})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Prj{s0}, y1})), None{},
                          App.red(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Prj{s0}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Enu{+s0}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Enu{s0}, y1})}, bk, hfs, App.nv(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Enu{s0}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Enu{s0}, y1})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Enu{s0}, y1})), None{},
                          App.red(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Enu{s0}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Lab{+s0}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q2{}, Machine.Val.clo{Source.Term.Lab{s0}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.clo{Source.Term.Lab{s0}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Lab{s0}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Mat{+s0, +s1, +s2}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Mat{s0, s1, s2}, y1})}, bk, hfs, App.nv(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Mat{s0, s1, s2}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Mat{s0, s1, s2}, y1})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Mat{s0, s1, s2}, y1})), None{},
                          App.red(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Mat{s0, s1, s2}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Efq{}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Efq{}, y1})}, bk, hfs, App.nv(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Efq{}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Efq{}, y1})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Efq{}, y1})), None{},
                          App.red(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Efq{}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Eql{+s0, +s1, +s2}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Eql{s0, s1, s2}, y1})}, bk, hfs, App.nv(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Eql{s0, s1, s2}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Eql{s0, s1, s2}, y1})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Eql{s0, s1, s2}, y1})), None{},
                          App.red(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Eql{s0, s1, s2}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Rfl{}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q2{}, Machine.Val.clo{Source.Term.Rfl{}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.clo{Source.Term.Rfl{}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Rfl{}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Rwt{+s0, +s1, +s2}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Prj{z0}, v1}, Source.Q2{}, Machine.Val.clo{Source.Term.Rwt{s0, s1, s2}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Prj{z0}, v1}), Val.rb(Machine.Val.clo{Source.Term.Rwt{s0, s1, s2}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Rwt{s0, s1, s2}), Val.ok(y1, Mode.env{}, bk), hx))
                case Machine.Val.lab{+y0}:
                  Ctx.stuck(fs, Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.lab{y0})}, bk, hfs, App.nv(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.lab{y0}), bk, {==}),
                    Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.lab{y0})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.lab{y0})), None{},
                      App.red(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.lab{y0}, bk, {==}, {==}, hx), {==}))
                case Machine.Val.rfl{}:
                  Ctx.stuck(fs, Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.rfl{})}, bk, hfs, App.nv(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.rfl{}), bk, {==}),
                    Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.rfl{})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.rfl{})), None{},
                      App.red(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.rfl{}, bk, {==}, {==}, hx), {==}))
                case Machine.Val.tup{+y0, +y1, +y2}:
                  (SP.Bool.and_intro(Val.ok(v1, Mode.env{}, bk), Bool.and(Val.ok(y1, Mode.any{}, bk), Bool.and(Val.ok(y2, Mode.any{}, bk), Frs.ok(fs, bk))), hf,
                    SP.Bool.and_intro(Val.ok(y1, Mode.any{}, bk), Bool.and(Val.ok(y2, Mode.any{}, bk), Frs.ok(fs, bk)), Field.any(y0, y1, bk, SP.Bool.and_left(Val.ok(y1, Mode.field(y0), bk), Val.ok(y2, Mode.good{}, bk), hx)),
                      SP.Bool.and_intro(Val.ok(y2, Mode.any{}, bk), Frs.ok(fs, bk), Good.any(y2, bk, SP.Bool.and_right(Val.ok(y1, Mode.field(y0), bk), Val.ok(y2, Mode.good{}, bk), hx)), hfs))),
                    Inr{Ctx.go(fs, Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.tup{y0, y1, y2})}, Source.Term.App{Source.Q2{}, Source.Term.App{Source.Quan.fld(y0, Source.Q2{}), Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)}), Val.rb(y1)}, Val.rb(y2)}, bk, hfs, {==},
                      Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.tup{y0, y1, y2})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.tup{y0, y1, y2})), Some{Source.Term.App{Source.Q2{}, Source.Term.App{Source.Quan.fld(y0, Source.Q2{}), Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)}), Val.rb(y1)}, Val.rb(y2)}},
                        App.red(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.tup{y0, y1, y2}, bk, {==}, {==}, hx), Prj.live.Q2(Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)}), y0, Val.rb(y1), Val.rb(y2), bk, Val.value(Machine.Val.tup{y0, y1, y2}, bk, hx))))})
                case Machine.Val.call{+y0, +y1}:
                  Ctx.stuck(fs, Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.call{y0, y1})}, bk, hfs, App.nv(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.call{y0, y1}), bk, {==}),
                    Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.call{y0, y1})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.call{y0, y1})), None{},
                      App.red(Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.call{y0, y1}, bk, {==}, {==}, hx), Call.elim(Val.rb(Machine.Val.call{y0, y1}), Call.rb_is_call(y0, y1), z => {Source.Term.redex(bk, Source.Q2{}, Source.Term.Prj{Source.Term.sub(z0, 0n, Source.Sub.env{Env.rb(v1)})}, z) == None{} : Maybe<&2, Source.Term>}, q2 => f2 => x2 => {==}, n => {==})))
        case Source.Term.Enu{+z0}:
          Ctx.stuck(fs, Source.Term.App{q, Val.rb(Machine.Val.clo{Source.Term.Enu{z0}, v1}), Val.rb(x)}, bk, hfs, App.nv(q, Val.rb(Machine.Val.clo{Source.Term.Enu{z0}, v1}), Val.rb(x), bk, {==}),
            Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{q, Val.rb(Machine.Val.clo{Source.Term.Enu{z0}, v1}), Val.rb(x)}, bk), Source.Term.redex(bk, q, Val.rb(Machine.Val.clo{Source.Term.Enu{z0}, v1}), Val.rb(x)), None{},
              App.red(q, Val.rb(Machine.Val.clo{Source.Term.Enu{z0}, v1}), x, bk, {==}, {==}, hx), {==}))
        case Source.Term.Lab{+z0}:
          Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Lab{z0}, v1}, q, x, bk, fs), Frs.plug(fs, Source.Term.App{q, Val.rb(Machine.Val.clo{Source.Term.Lab{z0}, v1}), Val.rb(x)}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Lab{z0}), Val.ok(v1, Mode.env{}, bk), hf))
        case Source.Term.Mat{+z0, +z1, +z2}:
          match q:
            case Source.Q0{}:
              Ctx.stuck(fs, Source.Term.App{Source.Q0{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(x)}, bk, hfs, App.nv(Source.Q0{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(x), bk, {==}),
                Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q0{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(x)}, bk), Source.Term.redex(bk, Source.Q0{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(x)), None{},
                  App.red(Source.Q0{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, x, bk, {==}, {==}, hx), Mat.dead(z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)}), Val.rb(x), bk)))
            case Source.Q1{}:
              match x:
                case Machine.Val.nil{}:
                  Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q1{}, Machine.Val.nil{}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.nil{})}), mu, bk), hx)
                case Machine.Val.env{+y0, +y1}:
                  Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q1{}, Machine.Val.env{y0, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.env{y0, y1})}), mu, bk), hx)
                case Machine.Val.arg{+y0, +y1, +y2}:
                  Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q1{}, Machine.Val.arg{y0, y1, y2}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.arg{y0, y1, y2})}), mu, bk), hx)
                case Machine.Val.clo{+y0, +y1}:
                  match y0:
                    case Source.Term.Var{+s0}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q1{}, Machine.Val.clo{Source.Term.Var{s0}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.clo{Source.Term.Var{s0}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Var{s0}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Ref{+s0}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q1{}, Machine.Val.clo{Source.Term.Ref{s0}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.clo{Source.Term.Ref{s0}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Ref{s0}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Ann{+s0, +s1}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q1{}, Machine.Val.clo{Source.Term.Ann{s0, s1}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.clo{Source.Term.Ann{s0, s1}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Ann{s0, s1}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Let{+s0, +s1, +s2}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q1{}, Machine.Val.clo{Source.Term.Let{s0, s1, s2}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.clo{Source.Term.Let{s0, s1, s2}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Let{s0, s1, s2}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Typ{+s0}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Typ{s0}, y1})}, bk, hfs, App.nv(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Typ{s0}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Typ{s0}, y1})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Typ{s0}, y1})), None{},
                          App.red(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Typ{s0}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Min{+s0, +s1}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q1{}, Machine.Val.clo{Source.Term.Min{s0, s1}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.clo{Source.Term.Min{s0, s1}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Min{s0, s1}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.All{+s0, +s1, +s2}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.All{s0, s1, s2}, y1})}, bk, hfs, App.nv(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.All{s0, s1, s2}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.All{s0, s1, s2}, y1})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.All{s0, s1, s2}, y1})), None{},
                          App.red(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.All{s0, s1, s2}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Lam{+s0, +s1}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Lam{s0, s1}, y1})}, bk, hfs, App.nv(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Lam{s0, s1}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Lam{s0, s1}, y1})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Lam{s0, s1}, y1})), None{},
                          App.red(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Lam{s0, s1}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.App{+s0, +s1, +s2}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q1{}, Machine.Val.clo{Source.Term.App{s0, s1, s2}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.clo{Source.Term.App{s0, s1, s2}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.App{s0, s1, s2}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Sig{+s0, +s1, +s2}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Sig{s0, s1, s2}, y1})}, bk, hfs, App.nv(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Sig{s0, s1, s2}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Sig{s0, s1, s2}, y1})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Sig{s0, s1, s2}, y1})), None{},
                          App.red(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Sig{s0, s1, s2}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Tup{+s0, +s1, +s2}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q1{}, Machine.Val.clo{Source.Term.Tup{s0, s1, s2}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.clo{Source.Term.Tup{s0, s1, s2}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Tup{s0, s1, s2}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Prj{+s0}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Prj{s0}, y1})}, bk, hfs, App.nv(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Prj{s0}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Prj{s0}, y1})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Prj{s0}, y1})), None{},
                          App.red(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Prj{s0}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Enu{+s0}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Enu{s0}, y1})}, bk, hfs, App.nv(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Enu{s0}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Enu{s0}, y1})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Enu{s0}, y1})), None{},
                          App.red(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Enu{s0}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Lab{+s0}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q1{}, Machine.Val.clo{Source.Term.Lab{s0}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.clo{Source.Term.Lab{s0}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Lab{s0}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Mat{+s0, +s1, +s2}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Mat{s0, s1, s2}, y1})}, bk, hfs, App.nv(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Mat{s0, s1, s2}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Mat{s0, s1, s2}, y1})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Mat{s0, s1, s2}, y1})), None{},
                          App.red(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Mat{s0, s1, s2}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Efq{}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Efq{}, y1})}, bk, hfs, App.nv(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Efq{}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Efq{}, y1})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Efq{}, y1})), None{},
                          App.red(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Efq{}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Eql{+s0, +s1, +s2}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Eql{s0, s1, s2}, y1})}, bk, hfs, App.nv(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Eql{s0, s1, s2}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Eql{s0, s1, s2}, y1})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Eql{s0, s1, s2}, y1})), None{},
                          App.red(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Eql{s0, s1, s2}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Rfl{}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q1{}, Machine.Val.clo{Source.Term.Rfl{}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.clo{Source.Term.Rfl{}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Rfl{}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Rwt{+s0, +s1, +s2}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q1{}, Machine.Val.clo{Source.Term.Rwt{s0, s1, s2}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q1{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.clo{Source.Term.Rwt{s0, s1, s2}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Rwt{s0, s1, s2}), Val.ok(y1, Mode.env{}, bk), hx))
                case Machine.Val.lab{+y0}:
                  S.mat.of(Source.Name.is_eq(y0, z0), Source.Q1{}, z0, z1, z2, v1, y0, fs, bk, hf, hfs, mu,
                    App.red(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.lab{y0}, bk, {==}, {==}, hx))
                case Machine.Val.rfl{}:
                  Ctx.stuck(fs, Source.Term.App{Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.rfl{})}, bk, hfs, App.nv(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.rfl{}), bk, {==}),
                    Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.rfl{})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.rfl{})), None{},
                      App.red(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.rfl{}, bk, {==}, {==}, hx), {==}))
                case Machine.Val.tup{+y0, +y1, +y2}:
                  Ctx.stuck(fs, Source.Term.App{Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.tup{y0, y1, y2})}, bk, hfs, App.nv(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.tup{y0, y1, y2}), bk, {==}),
                    Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.tup{y0, y1, y2})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.tup{y0, y1, y2})), None{},
                      App.red(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.tup{y0, y1, y2}, bk, {==}, {==}, hx), {==}))
                case Machine.Val.call{+y0, +y1}:
                  Ctx.stuck(fs, Source.Term.App{Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.call{y0, y1})}, bk, hfs, App.nv(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.call{y0, y1}), bk, {==}),
                    Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.call{y0, y1})}, bk), Source.Term.redex(bk, Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.call{y0, y1})), None{},
                      App.red(Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.call{y0, y1}, bk, {==}, {==}, hx), Call.elim(Val.rb(Machine.Val.call{y0, y1}), Call.rb_is_call(y0, y1), z => {Source.Term.redex(bk, Source.Q1{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, z) == None{} : Maybe<&2, Source.Term>}, q2 => f2 => x2 => {==}, n => {==})))
            case Source.Q2{}:
              match x:
                case Machine.Val.nil{}:
                  Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q2{}, Machine.Val.nil{}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.nil{})}), mu, bk), hx)
                case Machine.Val.env{+y0, +y1}:
                  Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q2{}, Machine.Val.env{y0, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.env{y0, y1})}), mu, bk), hx)
                case Machine.Val.arg{+y0, +y1, +y2}:
                  Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q2{}, Machine.Val.arg{y0, y1, y2}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.arg{y0, y1, y2})}), mu, bk), hx)
                case Machine.Val.clo{+y0, +y1}:
                  match y0:
                    case Source.Term.Var{+s0}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q2{}, Machine.Val.clo{Source.Term.Var{s0}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.clo{Source.Term.Var{s0}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Var{s0}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Ref{+s0}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q2{}, Machine.Val.clo{Source.Term.Ref{s0}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.clo{Source.Term.Ref{s0}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Ref{s0}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Ann{+s0, +s1}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q2{}, Machine.Val.clo{Source.Term.Ann{s0, s1}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.clo{Source.Term.Ann{s0, s1}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Ann{s0, s1}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Let{+s0, +s1, +s2}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q2{}, Machine.Val.clo{Source.Term.Let{s0, s1, s2}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.clo{Source.Term.Let{s0, s1, s2}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Let{s0, s1, s2}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Typ{+s0}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Typ{s0}, y1})}, bk, hfs, App.nv(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Typ{s0}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Typ{s0}, y1})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Typ{s0}, y1})), None{},
                          App.red(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Typ{s0}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Min{+s0, +s1}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q2{}, Machine.Val.clo{Source.Term.Min{s0, s1}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.clo{Source.Term.Min{s0, s1}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Min{s0, s1}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.All{+s0, +s1, +s2}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.All{s0, s1, s2}, y1})}, bk, hfs, App.nv(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.All{s0, s1, s2}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.All{s0, s1, s2}, y1})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.All{s0, s1, s2}, y1})), None{},
                          App.red(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.All{s0, s1, s2}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Lam{+s0, +s1}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Lam{s0, s1}, y1})}, bk, hfs, App.nv(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Lam{s0, s1}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Lam{s0, s1}, y1})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Lam{s0, s1}, y1})), None{},
                          App.red(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Lam{s0, s1}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.App{+s0, +s1, +s2}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q2{}, Machine.Val.clo{Source.Term.App{s0, s1, s2}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.clo{Source.Term.App{s0, s1, s2}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.App{s0, s1, s2}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Sig{+s0, +s1, +s2}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Sig{s0, s1, s2}, y1})}, bk, hfs, App.nv(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Sig{s0, s1, s2}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Sig{s0, s1, s2}, y1})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Sig{s0, s1, s2}, y1})), None{},
                          App.red(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Sig{s0, s1, s2}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Tup{+s0, +s1, +s2}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q2{}, Machine.Val.clo{Source.Term.Tup{s0, s1, s2}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.clo{Source.Term.Tup{s0, s1, s2}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Tup{s0, s1, s2}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Prj{+s0}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Prj{s0}, y1})}, bk, hfs, App.nv(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Prj{s0}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Prj{s0}, y1})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Prj{s0}, y1})), None{},
                          App.red(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Prj{s0}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Enu{+s0}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Enu{s0}, y1})}, bk, hfs, App.nv(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Enu{s0}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Enu{s0}, y1})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Enu{s0}, y1})), None{},
                          App.red(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Enu{s0}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Lab{+s0}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q2{}, Machine.Val.clo{Source.Term.Lab{s0}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.clo{Source.Term.Lab{s0}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Lab{s0}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Mat{+s0, +s1, +s2}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Mat{s0, s1, s2}, y1})}, bk, hfs, App.nv(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Mat{s0, s1, s2}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Mat{s0, s1, s2}, y1})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Mat{s0, s1, s2}, y1})), None{},
                          App.red(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Mat{s0, s1, s2}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Efq{}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Efq{}, y1})}, bk, hfs, App.nv(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Efq{}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Efq{}, y1})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Efq{}, y1})), None{},
                          App.red(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Efq{}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Eql{+s0, +s1, +s2}:
                      Ctx.stuck(fs, Source.Term.App{Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Eql{s0, s1, s2}, y1})}, bk, hfs, App.nv(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Eql{s0, s1, s2}, y1}), bk, {==}),
                        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Eql{s0, s1, s2}, y1})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.clo{Source.Term.Eql{s0, s1, s2}, y1})), None{},
                          App.red(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.clo{Source.Term.Eql{s0, s1, s2}, y1}, bk, {==}, {==}, hx), {==}))
                    case Source.Term.Rfl{}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q2{}, Machine.Val.clo{Source.Term.Rfl{}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.clo{Source.Term.Rfl{}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Rfl{}), Val.ok(y1, Mode.env{}, bk), hx))
                    case Source.Term.Rwt{+s0, +s1, +s2}:
                      Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}, Source.Q2{}, Machine.Val.clo{Source.Term.Rwt{s0, s1, s2}, y1}, bk, fs), Frs.plug(fs, Source.Term.App{Source.Q2{}, Val.rb(Machine.Val.clo{Source.Term.Mat{z0, z1, z2}, v1}), Val.rb(Machine.Val.clo{Source.Term.Rwt{s0, s1, s2}, y1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Rwt{s0, s1, s2}), Val.ok(y1, Mode.env{}, bk), hx))
                case Machine.Val.lab{+y0}:
                  S.mat.of(Source.Name.is_eq(y0, z0), Source.Q2{}, z0, z1, z2, v1, y0, fs, bk, hf, hfs, mu,
                    App.red(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.lab{y0}, bk, {==}, {==}, hx))
                case Machine.Val.rfl{}:
                  Ctx.stuck(fs, Source.Term.App{Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.rfl{})}, bk, hfs, App.nv(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.rfl{}), bk, {==}),
                    Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.rfl{})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.rfl{})), None{},
                      App.red(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.rfl{}, bk, {==}, {==}, hx), {==}))
                case Machine.Val.tup{+y0, +y1, +y2}:
                  Ctx.stuck(fs, Source.Term.App{Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.tup{y0, y1, y2})}, bk, hfs, App.nv(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.tup{y0, y1, y2}), bk, {==}),
                    Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.tup{y0, y1, y2})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.tup{y0, y1, y2})), None{},
                      App.red(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.tup{y0, y1, y2}, bk, {==}, {==}, hx), {==}))
                case Machine.Val.call{+y0, +y1}:
                  Ctx.stuck(fs, Source.Term.App{Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.call{y0, y1})}, bk, hfs, App.nv(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.call{y0, y1}), bk, {==}),
                    Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.call{y0, y1})}, bk), Source.Term.redex(bk, Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Val.rb(Machine.Val.call{y0, y1})), None{},
                      App.red(Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, Machine.Val.call{y0, y1}, bk, {==}, {==}, hx), Call.elim(Val.rb(Machine.Val.call{y0, y1}), Call.rb_is_call(y0, y1), z => {Source.Term.redex(bk, Source.Q2{}, Source.Term.Mat{z0, Source.Term.sub(z1, 0n, Source.Sub.env{Env.rb(v1)}), Source.Term.sub(z2, 0n, Source.Sub.env{Env.rb(v1)})}, z) == None{} : Maybe<&2, Source.Term>}, q2 => f2 => x2 => {==}, n => {==})))
        case Source.Term.Efq{}:
          Ctx.stuck(fs, Source.Term.App{q, Val.rb(Machine.Val.clo{Source.Term.Efq{}, v1}), Val.rb(x)}, bk, hfs, App.nv(q, Val.rb(Machine.Val.clo{Source.Term.Efq{}, v1}), Val.rb(x), bk, {==}),
            Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{q, Val.rb(Machine.Val.clo{Source.Term.Efq{}, v1}), Val.rb(x)}, bk), Source.Term.redex(bk, q, Val.rb(Machine.Val.clo{Source.Term.Efq{}, v1}), Val.rb(x)), None{},
              App.red(q, Val.rb(Machine.Val.clo{Source.Term.Efq{}, v1}), x, bk, {==}, {==}, hx), {==}))
        case Source.Term.Eql{+z0, +z1, +z2}:
          Ctx.stuck(fs, Source.Term.App{q, Val.rb(Machine.Val.clo{Source.Term.Eql{z0, z1, z2}, v1}), Val.rb(x)}, bk, hfs, App.nv(q, Val.rb(Machine.Val.clo{Source.Term.Eql{z0, z1, z2}, v1}), Val.rb(x), bk, {==}),
            Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{q, Val.rb(Machine.Val.clo{Source.Term.Eql{z0, z1, z2}, v1}), Val.rb(x)}, bk), Source.Term.redex(bk, q, Val.rb(Machine.Val.clo{Source.Term.Eql{z0, z1, z2}, v1}), Val.rb(x)), None{},
              App.red(q, Val.rb(Machine.Val.clo{Source.Term.Eql{z0, z1, z2}, v1}), x, bk, {==}, {==}, hx), {==}))
        case Source.Term.Rfl{}:
          Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Rfl{}, v1}, q, x, bk, fs), Frs.plug(fs, Source.Term.App{q, Val.rb(Machine.Val.clo{Source.Term.Rfl{}, v1}), Val.rb(x)}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Rfl{}), Val.ok(v1, Mode.env{}, bk), hf))
        case Source.Term.Rwt{+z0, +z1, +z2}:
          Shared.Bool.absurd(Moved(Machine.Apply.go(Machine.Val.clo{Source.Term.Rwt{z0, z1, z2}, v1}, q, x, bk, fs), Frs.plug(fs, Source.Term.App{q, Val.rb(Machine.Val.clo{Source.Term.Rwt{z0, z1, z2}, v1}), Val.rb(x)}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Rwt{z0, z1, z2}), Val.ok(v1, Mode.env{}, bk), hf))
    case Machine.Val.lab{+v0}:
      Ctx.stuck(fs, Source.Term.App{q, Val.rb(Machine.Val.lab{v0}), Val.rb(x)}, bk, hfs, App.nv(q, Val.rb(Machine.Val.lab{v0}), Val.rb(x), bk, {==}),
        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{q, Val.rb(Machine.Val.lab{v0}), Val.rb(x)}, bk), Source.Term.redex(bk, q, Val.rb(Machine.Val.lab{v0}), Val.rb(x)), None{},
          App.red(q, Val.rb(Machine.Val.lab{v0}), x, bk, Val.value(Machine.Val.lab{v0}, bk, hf), {==}, hx), {==}))
    case Machine.Val.rfl{}:
      Ctx.stuck(fs, Source.Term.App{q, Val.rb(Machine.Val.rfl{}), Val.rb(x)}, bk, hfs, App.nv(q, Val.rb(Machine.Val.rfl{}), Val.rb(x), bk, {==}),
        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{q, Val.rb(Machine.Val.rfl{}), Val.rb(x)}, bk), Source.Term.redex(bk, q, Val.rb(Machine.Val.rfl{}), Val.rb(x)), None{},
          App.red(q, Val.rb(Machine.Val.rfl{}), x, bk, Val.value(Machine.Val.rfl{}, bk, hf), {==}, hx), {==}))
    case Machine.Val.tup{+v0, +v1, +v2}:
      Ctx.stuck(fs, Source.Term.App{q, Val.rb(Machine.Val.tup{v0, v1, v2}), Val.rb(x)}, bk, hfs, App.nv(q, Val.rb(Machine.Val.tup{v0, v1, v2}), Val.rb(x), bk, {==}),
        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.App{q, Val.rb(Machine.Val.tup{v0, v1, v2}), Val.rb(x)}, bk), Source.Term.redex(bk, q, Val.rb(Machine.Val.tup{v0, v1, v2}), Val.rb(x)), None{},
          App.red(q, Val.rb(Machine.Val.tup{v0, v1, v2}), x, bk, Val.value(Machine.Val.tup{v0, v1, v2}, bk, hf), {==}, hx), {==}))
    case Machine.Val.call{+v0, +v1}:
      Eq.rw(Source.Term, Val.rb(Machine.Val.call{v0, Machine.Args.snoc(v1, q, x)}), Source.Term.App{q, Val.rb(Machine.Val.call{v0, v1}), Val.rb(x)}, Snoc.rb(v0, v1, q, x, bk, SP.Bool.and_left(Val.ok(v1, Mode.args{}, bk), Source.Term.is_value(Val.rb(Machine.Val.call{v0, v1}), False{}, bk), hf)),
        z => Moved(Machine.Call.try(bk, v0, Machine.Args.snoc(v1, q, x), fs), Frs.plug(fs, z), mu, bk),
        S.call(v0, Machine.Args.snoc(v1, q, x), fs, bk, Args.snoc_ok(v1, q, x, bk, SP.Bool.and_left(Val.ok(v1, Mode.args{}, bk), Source.Term.is_value(Val.rb(Machine.Val.call{v0, v1}), False{}, bk), hf), Field.any(q, x, bk, hx)),
          Eq.rw(Source.Term, Source.Term.App{q, Val.rb(Machine.Val.call{v0, v1}), Val.rb(x)}, Val.rb(Machine.Val.call{v0, Machine.Args.snoc(v1, q, x)}), Equal.sym(Source.Term, Val.rb(Machine.Val.call{v0, Machine.Args.snoc(v1, q, x)}), Source.Term.App{q, Val.rb(Machine.Val.call{v0, v1}), Val.rb(x)}, Snoc.rb(v0, v1, q, x, bk, SP.Bool.and_left(Val.ok(v1, Mode.args{}, bk), Source.Term.is_value(Val.rb(Machine.Val.call{v0, v1}), False{}, bk), hf))),
            z => {Source.Term.is_value(z, True{}, bk) == True{} : Bool},
            SP.Bool.and_intro(Source.Term.is_value(Val.rb(Machine.Val.call{v0, v1}), True{}, bk), Bool.or(Bool.not(Source.Quan.live(q)), Source.Term.is_value(Val.rb(x), False{}, bk)),
              Call.vt(Val.rb(Machine.Val.call{v0, v1}), bk, SP.Bool.and_right(Val.ok(v1, Mode.args{}, bk), Source.Term.is_value(Val.rb(Machine.Val.call{v0, v1}), False{}, bk), hf), Call.rb_is_call(v0, v1)), Field.value(q, x, bk, hx))),
          hfs, mu, hmu))
# Steps
# =====

def S.var.clo(+t2: Source.Term, +e2: Machine.Val, +t0: Source.Term, +fs: List<&2, Machine.Fr>, +bk: List<&2, Source.Def>,
  hnv: {Val.no_var(Machine.Val.clo{t2, e2}) == True{} : Bool}, hok: {Val.ok(e2, Mode.env{}, bk) == True{} : Bool},
  +heq: {Clo.rb(t2, e2) == t0 : Source.Term}, hfs: {Frs.ok(fs, bk) == True{} : Bool}) ->
  Moved(Machine.Move.go{Machine.St.eval{t2, e2, fs}}, Frs.plug(fs, t0), Frs.mu(fs, 1n+Term.w(t0)), bk):
  (SP.Bool.and_intro(Val.ok(e2, Mode.env{}, bk), Frs.ok(fs, bk), hok, hfs),
    Inl{(Equal.cong(Source.Term, Source.Term, z => Frs.plug(fs, z), Clo.rb(t2, e2), t0, heq),
      Frs.lt(fs, Nat.add(Term.var(t2), Term.w(Clo.rb(t2, e2))), 1n+Term.w(t0),
        Eq.rw(Nat, 0n, Term.var(t2), Equal.sym(Nat, Term.var(t2), 0n, Var.zero(t2, e2, hnv)),
          z => {Nat.is_le(1n+Nat.add(z, Term.w(Clo.rb(t2, e2))), 1n+Term.w(t0)) == True{} : Bool},
          Eq.rw(Source.Term, t0, Clo.rb(t2, e2), Equal.sym(Source.Term, Clo.rb(t2, e2), t0, heq),
            z => {Nat.is_le(1n+Nat.add(0n, Term.w(z)), 1n+Term.w(t0)) == True{} : Bool}, Shared.Nat.is_le_refl(Term.w(t0))))))})

def S.var(l: Machine.Look, +t0: Source.Term, +fs: List<&2, Machine.Fr>, +bk: List<&2, Source.Def>,
  +hok: {Look.ok(l, bk) == True{} : Bool}, +heq: {Look.rb(l) == t0 : Source.Term}, +hfs: {Frs.ok(fs, bk) == True{} : Bool}) ->
  Moved(Machine.Eval.var(l, fs), Frs.plug(fs, t0), Frs.mu(fs, 1n+Term.w(t0)), bk):
  match l:
    case Machine.Look.free{+j}:
      Eq.rw(Source.Term, Source.Term.Var{j}, t0, heq, z => Moved(Machine.Move.stuck{}, Frs.plug(fs, z), Frs.mu(fs, 1n+Term.w(t0)), bk),
        Ctx.stuck(fs, Source.Term.Var{j}, bk, hfs, {==}, {==}))
    case Machine.Look.val{x}:
      match x:
        case Machine.Val.nil{}:
          Shared.Bool.absurd(Moved(Machine.Eval.var(Machine.Look.val{Machine.Val.nil{}}, fs), Frs.plug(fs, t0), Frs.mu(fs, 1n+Term.w(t0)), bk), hok)
        case Machine.Val.env{+v0, +v1}:
          Shared.Bool.absurd(Moved(Machine.Eval.var(Machine.Look.val{Machine.Val.env{v0, v1}}, fs), Frs.plug(fs, t0), Frs.mu(fs, 1n+Term.w(t0)), bk), hok)
        case Machine.Val.arg{+v0, +v1, +v2}:
          Shared.Bool.absurd(Moved(Machine.Eval.var(Machine.Look.val{Machine.Val.arg{v0, v1, v2}}, fs), Frs.plug(fs, t0), Frs.mu(fs, 1n+Term.w(t0)), bk), hok)
        case Machine.Val.clo{+v0, +v1}:
          S.var.clo(v0, v1, t0, fs, bk, SP.Bool.and_left(Val.no_var(Machine.Val.clo{v0, v1}), Val.ok(Machine.Val.clo{v0, v1}, Mode.any{}, bk), hok),
            SP.Bool.and_right(Val.no_var(Machine.Val.clo{v0, v1}), Val.ok(Machine.Val.clo{v0, v1}, Mode.any{}, bk), hok), heq, hfs)
        case Machine.Val.lab{+v0}:
          (SP.Bool.and_intro(Val.ok(Machine.Val.lab{v0}, Mode.good{}, bk), Frs.ok(fs, bk), hok, hfs),
            Inl{(Equal.cong(Source.Term, Source.Term, z => Frs.plug(fs, z), Val.rb(Machine.Val.lab{v0}), t0, heq),
              Frs.lt(fs, 0n, 1n+Term.w(t0), Shared.Nat.is_le_zero(Term.w(t0))))})
        case Machine.Val.rfl{}:
          (SP.Bool.and_intro(Val.ok(Machine.Val.rfl{}, Mode.good{}, bk), Frs.ok(fs, bk), hok, hfs),
            Inl{(Equal.cong(Source.Term, Source.Term, z => Frs.plug(fs, z), Val.rb(Machine.Val.rfl{}), t0, heq),
              Frs.lt(fs, 0n, 1n+Term.w(t0), Shared.Nat.is_le_zero(Term.w(t0))))})
        case Machine.Val.tup{+v0, +v1, +v2}:
          (SP.Bool.and_intro(Val.ok(Machine.Val.tup{v0, v1, v2}, Mode.good{}, bk), Frs.ok(fs, bk), hok, hfs),
            Inl{(Equal.cong(Source.Term, Source.Term, z => Frs.plug(fs, z), Val.rb(Machine.Val.tup{v0, v1, v2}), t0, heq),
              Frs.lt(fs, 0n, 1n+Term.w(t0), Shared.Nat.is_le_zero(Term.w(t0))))})
        case Machine.Val.call{+v0, +v1}:
          (SP.Bool.and_intro(Val.ok(Machine.Val.call{v0, v1}, Mode.good{}, bk), Frs.ok(fs, bk), hok, hfs),
            Inl{(Equal.cong(Source.Term, Source.Term, z => Frs.plug(fs, z), Val.rb(Machine.Val.call{v0, v1}), t0, heq),
              Frs.lt(fs, 0n, 1n+Term.w(t0), Shared.Nat.is_le_zero(Term.w(t0))))})

def S.var.of(+i: Nat, +e: Machine.Val, +fs: List<&2, Machine.Fr>, +bk: List<&2, Source.Def>, r: Find.res(e, i, bk),
  hfs: {Frs.ok(fs, bk) == True{} : Bool}) ->
  Moved(Machine.Eval.var(Machine.Env.find(e, i), fs), Frs.plug(fs, Clo.rb(Source.Term.Var{i}, e)),
    Frs.mu(fs, 1n+Term.w(Clo.rb(Source.Term.Var{i}, e))), bk):
  match r:
    case (hok, heq):
      S.var(Machine.Env.find(e, i), Clo.rb(Source.Term.Var{i}, e), fs, bk, hok,
        Equal.trans(Source.Term, Look.rb(Machine.Env.find(e, i)), Source.Env.sub(Env.rb(e), i), Clo.rb(Source.Term.Var{i}, e), heq,
          Equal.sym(Source.Term, Clo.rb(Source.Term.Var{i}, e), Source.Env.sub(Env.rb(e), i), Term.sub_var(i, Env.rb(e)))), hfs)

# the step from St.eval t e fs
def S.eval(t: Source.Term, +e: Machine.Val, +fs: List<&2, Machine.Fr>, +bk: List<&2, Source.Def>,
  +he: {Val.ok(e, Mode.env{}, bk) == True{} : Bool}, +hfs: {Frs.ok(fs, bk) == True{} : Bool}) ->
  Moved(Machine.Eval.go(t, e, fs, bk), Frs.plug(fs, Clo.rb(t, e)), Frs.mu(fs, Nat.add(Term.var(t), Term.w(Clo.rb(t, e)))), bk):
  match t:
    case Source.Term.Var{+z0}:
      S.var.of(z0, e, fs, bk, Find.ok(e, z0, bk, he), hfs)
    case Source.Term.Ref{+z0}:
      S.call(z0, Machine.Val.nil{}, fs, bk, {==}, {==}, hfs, Frs.mu(fs, 5n), Frs.lt(fs, 0n, 5n, {==}))
    case Source.Term.Ann{+z0, +z1}:
      (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(fs, bk), he, hfs), Inr{Ctx.go(fs, Source.Term.Ann{Clo.rb(z0, e), Clo.rb(z1, e)}, Clo.rb(z0, e), bk, hfs, {==}, {==})})
    case Source.Term.Let{+z0, +z1, +z2}:
      match z0:
        case Source.Q0{}:
          (SP.Bool.and_intro(Val.ok(Machine.Val.env{Machine.Val.clo{z1, e}, e}, Mode.env{}, bk), Frs.ok(fs, bk), SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Val.ok(e, Mode.env{}, bk), he, he), hfs),
            Inr{Ctx.go(fs, Source.Term.Let{Source.Q0{}, Clo.rb(z1, e), Source.Term.sub(z2, 1n, Source.Sub.env{Env.rb(e)})}, Clo.rb(z2, Machine.Val.env{Machine.Val.clo{z1, e}, e}), bk, hfs, {==},
              Equal.cong(Source.Term, Maybe<&2, Source.Term>, z => Some{z}, Source.Term.sub(Source.Term.sub(z2, 1n, Source.Sub.env{Env.rb(e)}), 0n, Source.Sub.one{Clo.rb(z1, e)}), Clo.rb(z2, Machine.Val.env{Machine.Val.clo{z1, e}, e}),
                Term.sub_sub(z2, 0n, Env.rb(e), Clo.rb(z1, e))))})
        case Source.Q1{}:
          (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(Con{Machine.Fr.let{Source.Q1{}, z2, e}, fs}, bk), he, SP.Bool.and_intro(Fr.ok(Machine.Fr.let{Source.Q1{}, z2, e}, bk), Frs.ok(fs, bk), he, hfs)), Inl{({==}, Frs.lt(fs, Nat.add(Term.var(z1), Term.w(Clo.rb(z1, e))), 5n+Term.w(Clo.rb(z1, e)), Le.push0(z1, Term.w(Clo.rb(z1, e)))))})
        case Source.Q2{}:
          (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(Con{Machine.Fr.let{Source.Q2{}, z2, e}, fs}, bk), he, SP.Bool.and_intro(Fr.ok(Machine.Fr.let{Source.Q2{}, z2, e}, bk), Frs.ok(fs, bk), he, hfs)), Inl{({==}, Frs.lt(fs, Nat.add(Term.var(z1), Term.w(Clo.rb(z1, e))), 5n+Term.w(Clo.rb(z1, e)), Le.push0(z1, Term.w(Clo.rb(z1, e)))))})
    case Source.Term.Typ{+z0}:
      (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(fs, bk), he, hfs), Inl{({==}, Frs.lt(fs, 0n, 5n, {==}))})
    case Source.Term.Min{+z0, +z1}:
      (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(Con{Machine.Fr.min1{z1, e}, fs}, bk), he, SP.Bool.and_intro(Fr.ok(Machine.Fr.min1{z1, e}, bk), Frs.ok(fs, bk), he, hfs)),
        Inl{({==}, Frs.lt(fs, Nat.add(3n+Term.w(Clo.rb(z1, e)), Nat.add(Term.var(z0), Term.w(Clo.rb(z0, e)))),
          5n+Nat.add(Term.w(Clo.rb(z1, e)), Term.w(Clo.rb(z0, e))), Le.push3(z0, Term.w(Clo.rb(z0, e)), Term.w(Clo.rb(z1, e)))))})
    case Source.Term.All{+z0, +z1, +z2}:
      (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(fs, bk), he, hfs), Inl{({==}, Frs.lt(fs, 0n, 5n, {==}))})
    case Source.Term.Lam{+z0, +z1}:
      (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(fs, bk), he, hfs), Inl{({==}, Frs.lt(fs, 0n, 5n, {==}))})
    case Source.Term.App{+z0, +z1, +z2}:
      match z0:
        case Source.Q0{}:
          (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(Con{Machine.Fr.arg{Source.Q0{}, Machine.Val.clo{z2, e}}, fs}, bk), he, SP.Bool.and_intro(Fr.ok(Machine.Fr.arg{Source.Q0{}, Machine.Val.clo{z2, e}}, bk), Frs.ok(fs, bk), he, hfs)),
            Inl{({==}, Frs.lt(fs, 1n+Nat.add(Term.var(z1), Term.w(Clo.rb(z1, e))), 5n+Term.w(Clo.rb(z1, e)), Le.push1(z1, Term.w(Clo.rb(z1, e)))))})
        case Source.Q1{}:
          (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(Con{Machine.Fr.arg{Source.Q1{}, Machine.Val.clo{z2, e}}, fs}, bk), he, SP.Bool.and_intro(Fr.ok(Machine.Fr.arg{Source.Q1{}, Machine.Val.clo{z2, e}}, bk), Frs.ok(fs, bk), he, hfs)),
            Inl{({==}, Frs.lt(fs, Nat.add(3n+Term.w(Clo.rb(z2, e)), Nat.add(Term.var(z1), Term.w(Clo.rb(z1, e)))),
              5n+Nat.add(Term.w(Clo.rb(z2, e)), Term.w(Clo.rb(z1, e))), Le.push3(z1, Term.w(Clo.rb(z1, e)), Term.w(Clo.rb(z2, e)))))})
        case Source.Q2{}:
          (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(Con{Machine.Fr.arg{Source.Q2{}, Machine.Val.clo{z2, e}}, fs}, bk), he, SP.Bool.and_intro(Fr.ok(Machine.Fr.arg{Source.Q2{}, Machine.Val.clo{z2, e}}, bk), Frs.ok(fs, bk), he, hfs)),
            Inl{({==}, Frs.lt(fs, Nat.add(3n+Term.w(Clo.rb(z2, e)), Nat.add(Term.var(z1), Term.w(Clo.rb(z1, e)))),
              5n+Nat.add(Term.w(Clo.rb(z2, e)), Term.w(Clo.rb(z1, e))), Le.push3(z1, Term.w(Clo.rb(z1, e)), Term.w(Clo.rb(z2, e)))))})
    case Source.Term.Sig{+z0, +z1, +z2}:
      (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(fs, bk), he, hfs), Inl{({==}, Frs.lt(fs, 0n, 5n, {==}))})
    case Source.Term.Tup{+z0, +z1, +z2}:
      match z0:
        case Source.Q0{}:
          (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(Con{Machine.Fr.snd{Source.Q0{}, Machine.Val.clo{z1, e}}, fs}, bk), he, SP.Bool.and_intro(Fr.ok(Machine.Fr.snd{Source.Q0{}, Machine.Val.clo{z1, e}}, bk), Frs.ok(fs, bk), he, hfs)),
            Inl{({==}, Frs.lt(fs, 1n+Nat.add(Term.var(z2), Term.w(Clo.rb(z2, e))), 5n+Nat.add(Term.w(Clo.rb(z2, e)), 0n), Le.push1z(z2, Term.w(Clo.rb(z2, e)))))})
        case Source.Q1{}:
          (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(Con{Machine.Fr.fst{Source.Q1{}, z2, e}, fs}, bk), he, SP.Bool.and_intro(Fr.ok(Machine.Fr.fst{Source.Q1{}, z2, e}, bk), Frs.ok(fs, bk), he, hfs)),
            Inl{({==}, Frs.lt(fs, Nat.add(3n+Term.w(Clo.rb(z2, e)), Nat.add(Term.var(z1), Term.w(Clo.rb(z1, e)))),
              5n+Nat.add(Term.w(Clo.rb(z2, e)), Term.w(Clo.rb(z1, e))), Le.push3(z1, Term.w(Clo.rb(z1, e)), Term.w(Clo.rb(z2, e)))))})
        case Source.Q2{}:
          (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(Con{Machine.Fr.fst{Source.Q2{}, z2, e}, fs}, bk), he, SP.Bool.and_intro(Fr.ok(Machine.Fr.fst{Source.Q2{}, z2, e}, bk), Frs.ok(fs, bk), he, hfs)),
            Inl{({==}, Frs.lt(fs, Nat.add(3n+Term.w(Clo.rb(z2, e)), Nat.add(Term.var(z1), Term.w(Clo.rb(z1, e)))),
              5n+Nat.add(Term.w(Clo.rb(z2, e)), Term.w(Clo.rb(z1, e))), Le.push3(z1, Term.w(Clo.rb(z1, e)), Term.w(Clo.rb(z2, e)))))})
    case Source.Term.Prj{+z0}:
      (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(fs, bk), he, hfs), Inl{({==}, Frs.lt(fs, 0n, 5n, {==}))})
    case Source.Term.Enu{+z0}:
      (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(fs, bk), he, hfs), Inl{({==}, Frs.lt(fs, 0n, 5n, {==}))})
    case Source.Term.Lab{+z0}:
      (hfs, Inl{({==}, Frs.lt(fs, 0n, 5n, {==}))})
    case Source.Term.Mat{+z0, +z1, +z2}:
      (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(fs, bk), he, hfs), Inl{({==}, Frs.lt(fs, 0n, 5n, {==}))})
    case Source.Term.Efq{}:
      (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(fs, bk), he, hfs), Inl{({==}, Frs.lt(fs, 0n, 5n, {==}))})
    case Source.Term.Eql{+z0, +z1, +z2}:
      (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(fs, bk), he, hfs), Inl{({==}, Frs.lt(fs, 0n, 5n, {==}))})
    case Source.Term.Rfl{}:
      (hfs, Inl{({==}, Frs.lt(fs, 0n, 5n, {==}))})
    case Source.Term.Rwt{+z0, +z1, +z2}:
      (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(Con{Machine.Fr.rwt{z1, z2, e}, fs}, bk), he, SP.Bool.and_intro(Fr.ok(Machine.Fr.rwt{z1, z2, e}, bk), Frs.ok(fs, bk), he, hfs)), Inl{({==}, Frs.lt(fs, Nat.add(Term.var(z0), Term.w(Clo.rb(z0, e))), 5n+Term.w(Clo.rb(z0, e)), Le.push0(z0, Term.w(Clo.rb(z0, e)))))})
def Let.step.Q1(+v: Machine.Val, +f: Source.Term, +bk: List<&2, Source.Def>, +hv: {Val.ok(v, Mode.good{}, bk) == True{} : Bool}) ->
  {Source.Term.step(Source.Term.Let{Source.Q1{}, Val.rb(v), f}, bk) ==
    Source.Maybe.when(Source.Term, Bool.or(Bool.not(Source.Quan.is_q2(Source.Q1{})), Source.Term.is_data(Val.rb(v))),
      w => Some{Source.Term.sub(f, 0n, Source.Sub.one{Val.rb(v)})}) : Maybe<&2, Source.Term>}:
  %Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(Val.rb(v), bk), None{}, Vals.step(Val.rb(v), False{}, bk, Val.value(v, bk, hv))) :
    {Source.Term.step.let(Source.Q1{}, Val.rb(v), f, bk, w => _) ==
      Source.Maybe.when(Source.Term, Bool.or(Bool.not(Source.Quan.is_q2(Source.Q1{})), Source.Term.is_data(Val.rb(v))),
        w => Some{Source.Term.sub(f, 0n, Source.Sub.one{Val.rb(v)})}) : Maybe<&2, Source.Term>}
  %Equal.sym(Bool, Source.Term.is_value(Val.rb(v), False{}, bk), True{}, Val.value(v, bk, hv)) :
    {Source.Maybe.when(Source.Term, Bool.and(_, Bool.or(Bool.not(Source.Quan.is_q2(Source.Q1{})), Source.Term.is_data(Val.rb(v)))),
      w => Some{Source.Term.sub(f, 0n, Source.Sub.one{Val.rb(v)})}) ==
      Source.Maybe.when(Source.Term, Bool.or(Bool.not(Source.Quan.is_q2(Source.Q1{})), Source.Term.is_data(Val.rb(v))),
        w => Some{Source.Term.sub(f, 0n, Source.Sub.one{Val.rb(v)})}) : Maybe<&2, Source.Term>}
  {==}

def S.let.of.Q1(c: Bool, +v: Machine.Val, +f: Source.Term, +e: Machine.Val, +rest: List<&2, Machine.Fr>, +bk: List<&2, Source.Def>,
  +hv: {Val.ok(v, Mode.good{}, bk) == True{} : Bool}, he: {Val.ok(e, Mode.env{}, bk) == True{} : Bool},
  +hrest: {Frs.ok(rest, bk) == True{} : Bool}, -mu: Nat,
  hst: {Source.Term.step(Source.Term.Let{Source.Q1{}, Val.rb(v), Source.Term.sub(f, 1n, Source.Sub.env{Env.rb(e)})}, bk) == Source.Maybe.when(Source.Term, c, w => Some{Source.Term.sub(Source.Term.sub(f, 1n, Source.Sub.env{Env.rb(e)}), 0n, Source.Sub.one{Val.rb(v)})}) : Maybe<&2, Source.Term>}) ->
  Moved(Source.Bool.lazy(Machine.Move, c, u => Machine.Move.go{Machine.St.eval{f, Machine.Val.env{v, e}, rest}}, u => Machine.Move.stuck{}),
    Frs.plug(rest, Source.Term.Let{Source.Q1{}, Val.rb(v), Source.Term.sub(f, 1n, Source.Sub.env{Env.rb(e)})}), mu, bk):
  match c:
    case True{}:
      (SP.Bool.and_intro(Bool.and(Val.ok(v, Mode.any{}, bk), Val.ok(e, Mode.env{}, bk)), Frs.ok(rest, bk), SP.Bool.and_intro(Val.ok(v, Mode.any{}, bk), Val.ok(e, Mode.env{}, bk), Good.any(v, bk, hv), he), hrest),
        Inr{Ctx.go(rest, Source.Term.Let{Source.Q1{}, Val.rb(v), Source.Term.sub(f, 1n, Source.Sub.env{Env.rb(e)})}, Clo.rb(f, Machine.Val.env{v, e}), bk, hrest, {==},
          Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Let{Source.Q1{}, Val.rb(v), Source.Term.sub(f, 1n, Source.Sub.env{Env.rb(e)})}, bk), Some{Source.Term.sub(Source.Term.sub(f, 1n, Source.Sub.env{Env.rb(e)}), 0n, Source.Sub.one{Val.rb(v)})},
            Some{Clo.rb(f, Machine.Val.env{v, e})}, hst,
            Equal.cong(Source.Term, Maybe<&2, Source.Term>, z => Some{z}, Source.Term.sub(Source.Term.sub(f, 1n, Source.Sub.env{Env.rb(e)}), 0n, Source.Sub.one{Val.rb(v)}),
              Clo.rb(f, Machine.Val.env{v, e}), Term.sub_sub(f, 0n, Env.rb(e), Val.rb(v)))))})
    case False{}:
      Ctx.stuck(rest, Source.Term.Let{Source.Q1{}, Val.rb(v), Source.Term.sub(f, 1n, Source.Sub.env{Env.rb(e)})}, bk, hrest, {==}, hst)

def S.let.Q1(+v: Machine.Val, +f: Source.Term, +e: Machine.Val, +rest: List<&2, Machine.Fr>, +bk: List<&2, Source.Def>,
  +hv: {Val.ok(v, Mode.good{}, bk) == True{} : Bool}, he: {Val.ok(e, Mode.env{}, bk) == True{} : Bool},
  hrest: {Frs.ok(rest, bk) == True{} : Bool}, -mu: Nat) ->
  Moved(Source.Bool.lazy(Machine.Move, Bool.or(Bool.not(Source.Quan.is_q2(Source.Q1{})), Machine.Val.is_data(v)),
    u => Machine.Move.go{Machine.St.eval{f, Machine.Val.env{v, e}, rest}}, u => Machine.Move.stuck{}),
    Frs.plug(rest, Source.Term.Let{Source.Q1{}, Val.rb(v), Source.Term.sub(f, 1n, Source.Sub.env{Env.rb(e)})}), mu, bk):
  %Equal.sym(Bool, Machine.Val.is_data(v), Source.Term.is_data(Val.rb(v)), Data.val(v, bk, Good.any(v, bk, hv))) :
    Moved(Source.Bool.lazy(Machine.Move, Bool.or(Bool.not(Source.Quan.is_q2(Source.Q1{})), _),
      u => Machine.Move.go{Machine.St.eval{f, Machine.Val.env{v, e}, rest}}, u => Machine.Move.stuck{}),
      Frs.plug(rest, Source.Term.Let{Source.Q1{}, Val.rb(v), Source.Term.sub(f, 1n, Source.Sub.env{Env.rb(e)})}), mu, bk)
  S.let.of.Q1(Bool.or(Bool.not(Source.Quan.is_q2(Source.Q1{})), Source.Term.is_data(Val.rb(v))), v, f, e, rest, bk, hv, he, hrest, mu,
    Let.step.Q1(v, Source.Term.sub(f, 1n, Source.Sub.env{Env.rb(e)}), bk, hv))

def Let.step.Q2(+v: Machine.Val, +f: Source.Term, +bk: List<&2, Source.Def>, +hv: {Val.ok(v, Mode.good{}, bk) == True{} : Bool}) ->
  {Source.Term.step(Source.Term.Let{Source.Q2{}, Val.rb(v), f}, bk) ==
    Source.Maybe.when(Source.Term, Bool.or(Bool.not(Source.Quan.is_q2(Source.Q2{})), Source.Term.is_data(Val.rb(v))),
      w => Some{Source.Term.sub(f, 0n, Source.Sub.one{Val.rb(v)})}) : Maybe<&2, Source.Term>}:
  %Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(Val.rb(v), bk), None{}, Vals.step(Val.rb(v), False{}, bk, Val.value(v, bk, hv))) :
    {Source.Term.step.let(Source.Q2{}, Val.rb(v), f, bk, w => _) ==
      Source.Maybe.when(Source.Term, Bool.or(Bool.not(Source.Quan.is_q2(Source.Q2{})), Source.Term.is_data(Val.rb(v))),
        w => Some{Source.Term.sub(f, 0n, Source.Sub.one{Val.rb(v)})}) : Maybe<&2, Source.Term>}
  %Equal.sym(Bool, Source.Term.is_value(Val.rb(v), False{}, bk), True{}, Val.value(v, bk, hv)) :
    {Source.Maybe.when(Source.Term, Bool.and(_, Bool.or(Bool.not(Source.Quan.is_q2(Source.Q2{})), Source.Term.is_data(Val.rb(v)))),
      w => Some{Source.Term.sub(f, 0n, Source.Sub.one{Val.rb(v)})}) ==
      Source.Maybe.when(Source.Term, Bool.or(Bool.not(Source.Quan.is_q2(Source.Q2{})), Source.Term.is_data(Val.rb(v))),
        w => Some{Source.Term.sub(f, 0n, Source.Sub.one{Val.rb(v)})}) : Maybe<&2, Source.Term>}
  {==}

def S.let.of.Q2(c: Bool, +v: Machine.Val, +f: Source.Term, +e: Machine.Val, +rest: List<&2, Machine.Fr>, +bk: List<&2, Source.Def>,
  +hv: {Val.ok(v, Mode.good{}, bk) == True{} : Bool}, he: {Val.ok(e, Mode.env{}, bk) == True{} : Bool},
  +hrest: {Frs.ok(rest, bk) == True{} : Bool}, -mu: Nat,
  hst: {Source.Term.step(Source.Term.Let{Source.Q2{}, Val.rb(v), Source.Term.sub(f, 1n, Source.Sub.env{Env.rb(e)})}, bk) == Source.Maybe.when(Source.Term, c, w => Some{Source.Term.sub(Source.Term.sub(f, 1n, Source.Sub.env{Env.rb(e)}), 0n, Source.Sub.one{Val.rb(v)})}) : Maybe<&2, Source.Term>}) ->
  Moved(Source.Bool.lazy(Machine.Move, c, u => Machine.Move.go{Machine.St.eval{f, Machine.Val.env{v, e}, rest}}, u => Machine.Move.stuck{}),
    Frs.plug(rest, Source.Term.Let{Source.Q2{}, Val.rb(v), Source.Term.sub(f, 1n, Source.Sub.env{Env.rb(e)})}), mu, bk):
  match c:
    case True{}:
      (SP.Bool.and_intro(Bool.and(Val.ok(v, Mode.any{}, bk), Val.ok(e, Mode.env{}, bk)), Frs.ok(rest, bk), SP.Bool.and_intro(Val.ok(v, Mode.any{}, bk), Val.ok(e, Mode.env{}, bk), Good.any(v, bk, hv), he), hrest),
        Inr{Ctx.go(rest, Source.Term.Let{Source.Q2{}, Val.rb(v), Source.Term.sub(f, 1n, Source.Sub.env{Env.rb(e)})}, Clo.rb(f, Machine.Val.env{v, e}), bk, hrest, {==},
          Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Let{Source.Q2{}, Val.rb(v), Source.Term.sub(f, 1n, Source.Sub.env{Env.rb(e)})}, bk), Some{Source.Term.sub(Source.Term.sub(f, 1n, Source.Sub.env{Env.rb(e)}), 0n, Source.Sub.one{Val.rb(v)})},
            Some{Clo.rb(f, Machine.Val.env{v, e})}, hst,
            Equal.cong(Source.Term, Maybe<&2, Source.Term>, z => Some{z}, Source.Term.sub(Source.Term.sub(f, 1n, Source.Sub.env{Env.rb(e)}), 0n, Source.Sub.one{Val.rb(v)}),
              Clo.rb(f, Machine.Val.env{v, e}), Term.sub_sub(f, 0n, Env.rb(e), Val.rb(v)))))})
    case False{}:
      Ctx.stuck(rest, Source.Term.Let{Source.Q2{}, Val.rb(v), Source.Term.sub(f, 1n, Source.Sub.env{Env.rb(e)})}, bk, hrest, {==}, hst)

def S.let.Q2(+v: Machine.Val, +f: Source.Term, +e: Machine.Val, +rest: List<&2, Machine.Fr>, +bk: List<&2, Source.Def>,
  +hv: {Val.ok(v, Mode.good{}, bk) == True{} : Bool}, he: {Val.ok(e, Mode.env{}, bk) == True{} : Bool},
  hrest: {Frs.ok(rest, bk) == True{} : Bool}, -mu: Nat) ->
  Moved(Source.Bool.lazy(Machine.Move, Bool.or(Bool.not(Source.Quan.is_q2(Source.Q2{})), Machine.Val.is_data(v)),
    u => Machine.Move.go{Machine.St.eval{f, Machine.Val.env{v, e}, rest}}, u => Machine.Move.stuck{}),
    Frs.plug(rest, Source.Term.Let{Source.Q2{}, Val.rb(v), Source.Term.sub(f, 1n, Source.Sub.env{Env.rb(e)})}), mu, bk):
  %Equal.sym(Bool, Machine.Val.is_data(v), Source.Term.is_data(Val.rb(v)), Data.val(v, bk, Good.any(v, bk, hv))) :
    Moved(Source.Bool.lazy(Machine.Move, Bool.or(Bool.not(Source.Quan.is_q2(Source.Q2{})), _),
      u => Machine.Move.go{Machine.St.eval{f, Machine.Val.env{v, e}, rest}}, u => Machine.Move.stuck{}),
      Frs.plug(rest, Source.Term.Let{Source.Q2{}, Val.rb(v), Source.Term.sub(f, 1n, Source.Sub.env{Env.rb(e)})}), mu, bk)
  S.let.of.Q2(Bool.or(Bool.not(Source.Quan.is_q2(Source.Q2{})), Source.Term.is_data(Val.rb(v))), v, f, e, rest, bk, hv, he, hrest, mu,
    Let.step.Q2(v, Source.Term.sub(f, 1n, Source.Sub.env{Env.rb(e)}), bk, hv))

def Rwt.stuck(+v: Machine.Val, +p: Source.Term, +f: Source.Term, +bk: List<&2, Source.Def>, hv: {Val.ok(v, Mode.good{}, bk) == True{} : Bool},
  hr: {Source.Term.is_rfl(Val.rb(v)) == False{} : Bool}) ->
  {Source.Term.step(Source.Term.Rwt{Val.rb(v), p, f}, bk) == None{} : Maybe<&2, Source.Term>}:
  %Equal.sym(Bool, Source.Term.is_rfl(Val.rb(v)), False{}, hr) :
    {Source.Bool.lazy(Maybe<&2, Source.Term>, _, w => Some{f}, w => Source.Maybe.map_term(Source.Term.step(Val.rb(v), bk), z => Source.Term.Rwt{z, p, f})) == None{} : Maybe<&2, Source.Term>}
  %Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(Val.rb(v), bk), None{}, Vals.step(Val.rb(v), False{}, bk, Val.value(v, bk, hv))) :
    {Source.Maybe.map_term(_, z => Source.Term.Rwt{z, p, f}) == None{} : Maybe<&2, Source.Term>}
  {==}

def Min.step(+a: Machine.Val, +v: Machine.Val, +bk: List<&2, Source.Def>, +ha: {Val.ok(a, Mode.good{}, bk) == True{} : Bool},
  +hv: {Val.ok(v, Mode.good{}, bk) == True{} : Bool}) ->
  {Source.Term.step(Source.Term.Min{Val.rb(a), Val.rb(v)}, bk) == Source.Term.meet(Val.rb(a), Val.rb(v)) : Maybe<&2, Source.Term>}:
  %Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(Val.rb(a), bk), None{}, Vals.step(Val.rb(a), False{}, bk, Val.value(a, bk, ha))) :
    {Source.Term.step.min(Val.rb(a), Val.rb(v), bk, w => _, w => Source.Term.step(Val.rb(v), bk)) == Source.Term.meet(Val.rb(a), Val.rb(v)) : Maybe<&2, Source.Term>}
  %Equal.sym(Bool, Source.Term.is_value(Val.rb(a), False{}, bk), True{}, Val.value(a, bk, ha)) :
    {Source.Maybe.when(Source.Term, _, w => Source.Maybe.else(Source.Term, Source.Maybe.map_term(Source.Term.step(Val.rb(v), bk), z => Source.Term.Min{Val.rb(a), z}),
      z => Source.Term.meet(Val.rb(a), Val.rb(v)))) == Source.Term.meet(Val.rb(a), Val.rb(v)) : Maybe<&2, Source.Term>}
  %Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(Val.rb(v), bk), None{}, Vals.step(Val.rb(v), False{}, bk, Val.value(v, bk, hv))) :
    {Source.Maybe.else(Source.Term, Source.Maybe.map_term(_, z => Source.Term.Min{Val.rb(a), z}), z => Source.Term.meet(Val.rb(a), Val.rb(v))) ==
      Source.Term.meet(Val.rb(a), Val.rb(v)) : Maybe<&2, Source.Term>}
  {==}

def S.meet.of(c: Bool, +i: List<&2, Nat>, +j: List<&2, Nat>, +rest: List<&2, Machine.Fr>, +bk: List<&2, Source.Def>,
  +hrest: {Frs.ok(rest, bk) == True{} : Bool}, -mu: Nat,
  hst: {Source.Term.step(Source.Term.Min{Source.Term.Lab{i}, Source.Term.Lab{j}}, bk) ==
    Source.Bool.lazy(Maybe<&2, Source.Term>, c, u => Some{Source.Term.qmin(i, j)}, u => None{}) : Maybe<&2, Source.Term>}) ->
  Moved(Source.Bool.lazy(Machine.Move, c, u => Machine.Move.go{Machine.St.eval{Source.Term.qmin(i, j), Machine.Val.nil{}, rest}},
    u => Machine.Move.stuck{}), Frs.plug(rest, Source.Term.Min{Source.Term.Lab{i}, Source.Term.Lab{j}}), mu, bk):
  match c:
    case True{}:
      (SP.Bool.and_intro(True{}, Frs.ok(rest, bk), {==}, hrest),
        Inr{Ctx.go(rest, Source.Term.Min{Source.Term.Lab{i}, Source.Term.Lab{j}}, Clo.rb(Source.Term.qmin(i, j), Machine.Val.nil{}), bk, hrest, {==},
          Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Source.Term.Lab{i}, Source.Term.Lab{j}}, bk), Some{Source.Term.qmin(i, j)},
            Some{Clo.rb(Source.Term.qmin(i, j), Machine.Val.nil{})}, hst,
            Equal.cong(Source.Term, Maybe<&2, Source.Term>, z => Some{z}, Source.Term.qmin(i, j), Clo.rb(Source.Term.qmin(i, j), Machine.Val.nil{}),
              Equal.sym(Source.Term, Clo.rb(Source.Term.qmin(i, j), Machine.Val.nil{}), Source.Term.qmin(i, j), Qmin.sub(i, j)))))})
    case False{}:
      Ctx.stuck(rest, Source.Term.Min{Source.Term.Lab{i}, Source.Term.Lab{j}}, bk, hrest, {==}, hst)

def S.meet(a: Machine.Val, +v: Machine.Val, +rest: List<&2, Machine.Fr>, +bk: List<&2, Source.Def>,
  +ha: {Val.ok(a, Mode.good{}, bk) == True{} : Bool}, +hv: {Val.ok(v, Mode.good{}, bk) == True{} : Bool},
  +hrest: {Frs.ok(rest, bk) == True{} : Bool}, -mu: Nat) -> Moved(Machine.Ret.meet(a, v, rest), Frs.plug(rest, Source.Term.Min{Val.rb(a), Val.rb(v)}), mu, bk):
  match a:
    case Machine.Val.nil{}:
      Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.nil{}, v, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.nil{}), Val.rb(v)}), mu, bk), ha)
    case Machine.Val.env{+u0, +u1}:
      Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.env{u0, u1}, v, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.env{u0, u1}), Val.rb(v)}), mu, bk), ha)
    case Machine.Val.arg{+u0, +u1, +u2}:
      Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.arg{u0, u1, u2}, v, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.arg{u0, u1, u2}), Val.rb(v)}), mu, bk), ha)
    case Machine.Val.clo{+u0, +u1}:
      match u0:
        case Source.Term.Var{+ut0}:
          Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.clo{Source.Term.Var{ut0}, u1}, v, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Var{ut0}, u1}), Val.rb(v)}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Var{ut0}), Val.ok(u1, Mode.env{}, bk), ha))
        case Source.Term.Ref{+ut0}:
          Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.clo{Source.Term.Ref{ut0}, u1}, v, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Ref{ut0}, u1}), Val.rb(v)}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Ref{ut0}), Val.ok(u1, Mode.env{}, bk), ha))
        case Source.Term.Ann{+ut0, +ut1}:
          Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.clo{Source.Term.Ann{ut0, ut1}, u1}, v, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Ann{ut0, ut1}, u1}), Val.rb(v)}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Ann{ut0, ut1}), Val.ok(u1, Mode.env{}, bk), ha))
        case Source.Term.Let{+ut0, +ut1, +ut2}:
          Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.clo{Source.Term.Let{ut0, ut1, ut2}, u1}, v, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Let{ut0, ut1, ut2}, u1}), Val.rb(v)}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Let{ut0, ut1, ut2}), Val.ok(u1, Mode.env{}, bk), ha))
        case Source.Term.Typ{+ut0}:
          Ctx.stuck(rest, Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Typ{ut0}, u1}), Val.rb(v)}, bk, hrest, {==},
            Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Typ{ut0}, u1}), Val.rb(v)}, bk), Source.Term.meet(Val.rb(Machine.Val.clo{Source.Term.Typ{ut0}, u1}), Val.rb(v)), None{},
              Min.step(Machine.Val.clo{Source.Term.Typ{ut0}, u1}, v, bk, ha, hv), {==}))
        case Source.Term.Min{+ut0, +ut1}:
          Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.clo{Source.Term.Min{ut0, ut1}, u1}, v, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Min{ut0, ut1}, u1}), Val.rb(v)}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Min{ut0, ut1}), Val.ok(u1, Mode.env{}, bk), ha))
        case Source.Term.All{+ut0, +ut1, +ut2}:
          Ctx.stuck(rest, Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.All{ut0, ut1, ut2}, u1}), Val.rb(v)}, bk, hrest, {==},
            Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.All{ut0, ut1, ut2}, u1}), Val.rb(v)}, bk), Source.Term.meet(Val.rb(Machine.Val.clo{Source.Term.All{ut0, ut1, ut2}, u1}), Val.rb(v)), None{},
              Min.step(Machine.Val.clo{Source.Term.All{ut0, ut1, ut2}, u1}, v, bk, ha, hv), {==}))
        case Source.Term.Lam{+ut0, +ut1}:
          Ctx.stuck(rest, Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Lam{ut0, ut1}, u1}), Val.rb(v)}, bk, hrest, {==},
            Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Lam{ut0, ut1}, u1}), Val.rb(v)}, bk), Source.Term.meet(Val.rb(Machine.Val.clo{Source.Term.Lam{ut0, ut1}, u1}), Val.rb(v)), None{},
              Min.step(Machine.Val.clo{Source.Term.Lam{ut0, ut1}, u1}, v, bk, ha, hv), {==}))
        case Source.Term.App{+ut0, +ut1, +ut2}:
          Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.clo{Source.Term.App{ut0, ut1, ut2}, u1}, v, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.App{ut0, ut1, ut2}, u1}), Val.rb(v)}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.App{ut0, ut1, ut2}), Val.ok(u1, Mode.env{}, bk), ha))
        case Source.Term.Sig{+ut0, +ut1, +ut2}:
          Ctx.stuck(rest, Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Sig{ut0, ut1, ut2}, u1}), Val.rb(v)}, bk, hrest, {==},
            Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Sig{ut0, ut1, ut2}, u1}), Val.rb(v)}, bk), Source.Term.meet(Val.rb(Machine.Val.clo{Source.Term.Sig{ut0, ut1, ut2}, u1}), Val.rb(v)), None{},
              Min.step(Machine.Val.clo{Source.Term.Sig{ut0, ut1, ut2}, u1}, v, bk, ha, hv), {==}))
        case Source.Term.Tup{+ut0, +ut1, +ut2}:
          Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.clo{Source.Term.Tup{ut0, ut1, ut2}, u1}, v, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Tup{ut0, ut1, ut2}, u1}), Val.rb(v)}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Tup{ut0, ut1, ut2}), Val.ok(u1, Mode.env{}, bk), ha))
        case Source.Term.Prj{+ut0}:
          Ctx.stuck(rest, Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Prj{ut0}, u1}), Val.rb(v)}, bk, hrest, {==},
            Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Prj{ut0}, u1}), Val.rb(v)}, bk), Source.Term.meet(Val.rb(Machine.Val.clo{Source.Term.Prj{ut0}, u1}), Val.rb(v)), None{},
              Min.step(Machine.Val.clo{Source.Term.Prj{ut0}, u1}, v, bk, ha, hv), {==}))
        case Source.Term.Enu{+ut0}:
          Ctx.stuck(rest, Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Enu{ut0}, u1}), Val.rb(v)}, bk, hrest, {==},
            Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Enu{ut0}, u1}), Val.rb(v)}, bk), Source.Term.meet(Val.rb(Machine.Val.clo{Source.Term.Enu{ut0}, u1}), Val.rb(v)), None{},
              Min.step(Machine.Val.clo{Source.Term.Enu{ut0}, u1}, v, bk, ha, hv), {==}))
        case Source.Term.Lab{+ut0}:
          Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.clo{Source.Term.Lab{ut0}, u1}, v, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Lab{ut0}, u1}), Val.rb(v)}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Lab{ut0}), Val.ok(u1, Mode.env{}, bk), ha))
        case Source.Term.Mat{+ut0, +ut1, +ut2}:
          Ctx.stuck(rest, Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Mat{ut0, ut1, ut2}, u1}), Val.rb(v)}, bk, hrest, {==},
            Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Mat{ut0, ut1, ut2}, u1}), Val.rb(v)}, bk), Source.Term.meet(Val.rb(Machine.Val.clo{Source.Term.Mat{ut0, ut1, ut2}, u1}), Val.rb(v)), None{},
              Min.step(Machine.Val.clo{Source.Term.Mat{ut0, ut1, ut2}, u1}, v, bk, ha, hv), {==}))
        case Source.Term.Efq{}:
          Ctx.stuck(rest, Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Efq{}, u1}), Val.rb(v)}, bk, hrest, {==},
            Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Efq{}, u1}), Val.rb(v)}, bk), Source.Term.meet(Val.rb(Machine.Val.clo{Source.Term.Efq{}, u1}), Val.rb(v)), None{},
              Min.step(Machine.Val.clo{Source.Term.Efq{}, u1}, v, bk, ha, hv), {==}))
        case Source.Term.Eql{+ut0, +ut1, +ut2}:
          Ctx.stuck(rest, Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Eql{ut0, ut1, ut2}, u1}), Val.rb(v)}, bk, hrest, {==},
            Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Eql{ut0, ut1, ut2}, u1}), Val.rb(v)}, bk), Source.Term.meet(Val.rb(Machine.Val.clo{Source.Term.Eql{ut0, ut1, ut2}, u1}), Val.rb(v)), None{},
              Min.step(Machine.Val.clo{Source.Term.Eql{ut0, ut1, ut2}, u1}, v, bk, ha, hv), {==}))
        case Source.Term.Rfl{}:
          Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.clo{Source.Term.Rfl{}, u1}, v, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Rfl{}, u1}), Val.rb(v)}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Rfl{}), Val.ok(u1, Mode.env{}, bk), ha))
        case Source.Term.Rwt{+ut0, +ut1, +ut2}:
          Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.clo{Source.Term.Rwt{ut0, ut1, ut2}, u1}, v, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.clo{Source.Term.Rwt{ut0, ut1, ut2}, u1}), Val.rb(v)}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Rwt{ut0, ut1, ut2}), Val.ok(u1, Mode.env{}, bk), ha))
    case Machine.Val.lab{+u0}:
      match v:
        case Machine.Val.nil{}:
          Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.lab{u0}, Machine.Val.nil{}, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.nil{})}), mu, bk), hv)
        case Machine.Val.env{+w0, +w1}:
          Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.lab{u0}, Machine.Val.env{w0, w1}, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.env{w0, w1})}), mu, bk), hv)
        case Machine.Val.arg{+w0, +w1, +w2}:
          Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.lab{u0}, Machine.Val.arg{w0, w1, w2}, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.arg{w0, w1, w2})}), mu, bk), hv)
        case Machine.Val.clo{+w0, +w1}:
          match w0:
            case Source.Term.Var{+wt0}:
              Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.lab{u0}, Machine.Val.clo{Source.Term.Var{wt0}, w1}, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Var{wt0}, w1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Var{wt0}), Val.ok(w1, Mode.env{}, bk), hv))
            case Source.Term.Ref{+wt0}:
              Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.lab{u0}, Machine.Val.clo{Source.Term.Ref{wt0}, w1}, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Ref{wt0}, w1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Ref{wt0}), Val.ok(w1, Mode.env{}, bk), hv))
            case Source.Term.Ann{+wt0, +wt1}:
              Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.lab{u0}, Machine.Val.clo{Source.Term.Ann{wt0, wt1}, w1}, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Ann{wt0, wt1}, w1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Ann{wt0, wt1}), Val.ok(w1, Mode.env{}, bk), hv))
            case Source.Term.Let{+wt0, +wt1, +wt2}:
              Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.lab{u0}, Machine.Val.clo{Source.Term.Let{wt0, wt1, wt2}, w1}, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Let{wt0, wt1, wt2}, w1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Let{wt0, wt1, wt2}), Val.ok(w1, Mode.env{}, bk), hv))
            case Source.Term.Typ{+wt0}:
              Ctx.stuck(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Typ{wt0}, w1})}, bk, hrest, {==},
                Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Typ{wt0}, w1})}, bk), Source.Term.meet(Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Typ{wt0}, w1})), None{},
                  Min.step(Machine.Val.lab{u0}, Machine.Val.clo{Source.Term.Typ{wt0}, w1}, bk, ha, hv), {==}))
            case Source.Term.Min{+wt0, +wt1}:
              Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.lab{u0}, Machine.Val.clo{Source.Term.Min{wt0, wt1}, w1}, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Min{wt0, wt1}, w1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Min{wt0, wt1}), Val.ok(w1, Mode.env{}, bk), hv))
            case Source.Term.All{+wt0, +wt1, +wt2}:
              Ctx.stuck(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.All{wt0, wt1, wt2}, w1})}, bk, hrest, {==},
                Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.All{wt0, wt1, wt2}, w1})}, bk), Source.Term.meet(Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.All{wt0, wt1, wt2}, w1})), None{},
                  Min.step(Machine.Val.lab{u0}, Machine.Val.clo{Source.Term.All{wt0, wt1, wt2}, w1}, bk, ha, hv), {==}))
            case Source.Term.Lam{+wt0, +wt1}:
              Ctx.stuck(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Lam{wt0, wt1}, w1})}, bk, hrest, {==},
                Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Lam{wt0, wt1}, w1})}, bk), Source.Term.meet(Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Lam{wt0, wt1}, w1})), None{},
                  Min.step(Machine.Val.lab{u0}, Machine.Val.clo{Source.Term.Lam{wt0, wt1}, w1}, bk, ha, hv), {==}))
            case Source.Term.App{+wt0, +wt1, +wt2}:
              Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.lab{u0}, Machine.Val.clo{Source.Term.App{wt0, wt1, wt2}, w1}, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.App{wt0, wt1, wt2}, w1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.App{wt0, wt1, wt2}), Val.ok(w1, Mode.env{}, bk), hv))
            case Source.Term.Sig{+wt0, +wt1, +wt2}:
              Ctx.stuck(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Sig{wt0, wt1, wt2}, w1})}, bk, hrest, {==},
                Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Sig{wt0, wt1, wt2}, w1})}, bk), Source.Term.meet(Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Sig{wt0, wt1, wt2}, w1})), None{},
                  Min.step(Machine.Val.lab{u0}, Machine.Val.clo{Source.Term.Sig{wt0, wt1, wt2}, w1}, bk, ha, hv), {==}))
            case Source.Term.Tup{+wt0, +wt1, +wt2}:
              Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.lab{u0}, Machine.Val.clo{Source.Term.Tup{wt0, wt1, wt2}, w1}, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Tup{wt0, wt1, wt2}, w1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Tup{wt0, wt1, wt2}), Val.ok(w1, Mode.env{}, bk), hv))
            case Source.Term.Prj{+wt0}:
              Ctx.stuck(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Prj{wt0}, w1})}, bk, hrest, {==},
                Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Prj{wt0}, w1})}, bk), Source.Term.meet(Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Prj{wt0}, w1})), None{},
                  Min.step(Machine.Val.lab{u0}, Machine.Val.clo{Source.Term.Prj{wt0}, w1}, bk, ha, hv), {==}))
            case Source.Term.Enu{+wt0}:
              Ctx.stuck(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Enu{wt0}, w1})}, bk, hrest, {==},
                Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Enu{wt0}, w1})}, bk), Source.Term.meet(Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Enu{wt0}, w1})), None{},
                  Min.step(Machine.Val.lab{u0}, Machine.Val.clo{Source.Term.Enu{wt0}, w1}, bk, ha, hv), {==}))
            case Source.Term.Lab{+wt0}:
              Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.lab{u0}, Machine.Val.clo{Source.Term.Lab{wt0}, w1}, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Lab{wt0}, w1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Lab{wt0}), Val.ok(w1, Mode.env{}, bk), hv))
            case Source.Term.Mat{+wt0, +wt1, +wt2}:
              Ctx.stuck(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Mat{wt0, wt1, wt2}, w1})}, bk, hrest, {==},
                Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Mat{wt0, wt1, wt2}, w1})}, bk), Source.Term.meet(Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Mat{wt0, wt1, wt2}, w1})), None{},
                  Min.step(Machine.Val.lab{u0}, Machine.Val.clo{Source.Term.Mat{wt0, wt1, wt2}, w1}, bk, ha, hv), {==}))
            case Source.Term.Efq{}:
              Ctx.stuck(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Efq{}, w1})}, bk, hrest, {==},
                Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Efq{}, w1})}, bk), Source.Term.meet(Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Efq{}, w1})), None{},
                  Min.step(Machine.Val.lab{u0}, Machine.Val.clo{Source.Term.Efq{}, w1}, bk, ha, hv), {==}))
            case Source.Term.Eql{+wt0, +wt1, +wt2}:
              Ctx.stuck(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Eql{wt0, wt1, wt2}, w1})}, bk, hrest, {==},
                Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Eql{wt0, wt1, wt2}, w1})}, bk), Source.Term.meet(Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Eql{wt0, wt1, wt2}, w1})), None{},
                  Min.step(Machine.Val.lab{u0}, Machine.Val.clo{Source.Term.Eql{wt0, wt1, wt2}, w1}, bk, ha, hv), {==}))
            case Source.Term.Rfl{}:
              Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.lab{u0}, Machine.Val.clo{Source.Term.Rfl{}, w1}, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Rfl{}, w1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Rfl{}), Val.ok(w1, Mode.env{}, bk), hv))
            case Source.Term.Rwt{+wt0, +wt1, +wt2}:
              Shared.Bool.absurd(Moved(Machine.Ret.meet(Machine.Val.lab{u0}, Machine.Val.clo{Source.Term.Rwt{wt0, wt1, wt2}, w1}, rest), Frs.plug(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.clo{Source.Term.Rwt{wt0, wt1, wt2}, w1})}), mu, bk), SP.Bool.and_left(Term.is_fun(Source.Term.Rwt{wt0, wt1, wt2}), Val.ok(w1, Mode.env{}, bk), hv))
        case Machine.Val.lab{+w0}:
          S.meet.of(Bool.and(Source.Name.is_quan(u0), Source.Name.is_quan(w0)), u0, w0, rest, bk, hrest, mu, {==})
        case Machine.Val.rfl{}:
          Ctx.stuck(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.rfl{})}, bk, hrest, {==},
            Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.rfl{})}, bk), Source.Term.meet(Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.rfl{})), None{},
              Min.step(Machine.Val.lab{u0}, Machine.Val.rfl{}, bk, ha, hv), {==}))
        case Machine.Val.tup{+w0, +w1, +w2}:
          Ctx.stuck(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.tup{w0, w1, w2})}, bk, hrest, {==},
            Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.tup{w0, w1, w2})}, bk), Source.Term.meet(Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.tup{w0, w1, w2})), None{},
              Min.step(Machine.Val.lab{u0}, Machine.Val.tup{w0, w1, w2}, bk, ha, hv), {==}))
        case Machine.Val.call{+w0, +w1}:
          Ctx.stuck(rest, Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.call{w0, w1})}, bk, hrest, {==},
            Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.call{w0, w1})}, bk), Source.Term.meet(Val.rb(Machine.Val.lab{u0}), Val.rb(Machine.Val.call{w0, w1})), None{},
              Min.step(Machine.Val.lab{u0}, Machine.Val.call{w0, w1}, bk, ha, hv), Call.elim(Val.rb(Machine.Val.call{w0, w1}), Call.rb_is_call(w0, w1), z => {Source.Term.meet(Source.Term.Lab{u0}, z) == None{} : Maybe<&2, Source.Term>}, q2 => f2 => x2 => {==}, n => {==})))
    case Machine.Val.rfl{}:
      Ctx.stuck(rest, Source.Term.Min{Val.rb(Machine.Val.rfl{}), Val.rb(v)}, bk, hrest, {==},
        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Val.rb(Machine.Val.rfl{}), Val.rb(v)}, bk), Source.Term.meet(Val.rb(Machine.Val.rfl{}), Val.rb(v)), None{},
          Min.step(Machine.Val.rfl{}, v, bk, ha, hv), {==}))
    case Machine.Val.tup{+u0, +u1, +u2}:
      Ctx.stuck(rest, Source.Term.Min{Val.rb(Machine.Val.tup{u0, u1, u2}), Val.rb(v)}, bk, hrest, {==},
        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Val.rb(Machine.Val.tup{u0, u1, u2}), Val.rb(v)}, bk), Source.Term.meet(Val.rb(Machine.Val.tup{u0, u1, u2}), Val.rb(v)), None{},
          Min.step(Machine.Val.tup{u0, u1, u2}, v, bk, ha, hv), {==}))
    case Machine.Val.call{+u0, +u1}:
      Ctx.stuck(rest, Source.Term.Min{Val.rb(Machine.Val.call{u0, u1}), Val.rb(v)}, bk, hrest, {==},
        Equal.trans(Maybe<&2, Source.Term>, Source.Term.step(Source.Term.Min{Val.rb(Machine.Val.call{u0, u1}), Val.rb(v)}, bk), Source.Term.meet(Val.rb(Machine.Val.call{u0, u1}), Val.rb(v)), None{},
          Min.step(Machine.Val.call{u0, u1}, v, bk, ha, hv), Call.elim(Val.rb(Machine.Val.call{u0, u1}), Call.rb_is_call(u0, u1), z => {Source.Term.meet(z, Val.rb(v)) == None{} : Maybe<&2, Source.Term>}, q2 => f2 => x2 => {==}, n => {==})))

def S.frame(fr: Machine.Fr, +v: Machine.Val, +rest: List<&2, Machine.Fr>, +bk: List<&2, Source.Def>, +hv: {Val.ok(v, Mode.good{}, bk) == True{} : Bool},
  +hfr: {Fr.ok(fr, bk) == True{} : Bool}, +hrest: {Frs.ok(rest, bk) == True{} : Bool}) -> Moved(Machine.Ret.go(v, Con{fr, rest}, bk), Frs.plug(Con{fr, rest}, Val.rb(v)), Frs.mu(Con{fr, rest}, 0n), bk):
  match fr:
    case Machine.Fr.arg{q, +x}:
      match q:
        case Source.Q0{}:
          S.apply(v, Source.Q0{}, x, rest, bk, hv, hfr, hrest, Frs.mu(rest, 1n), Frs.lt(rest, 0n, 1n, {==}))
        case Source.Q1{}:
          match x:
            case Machine.Val.nil{}:
              Shared.Bool.absurd(Moved(Machine.Ret.go(v, Con{Machine.Fr.arg{Source.Q1{}, Machine.Val.nil{}}, rest}, bk), Frs.plug(Con{Machine.Fr.arg{Source.Q1{}, Machine.Val.nil{}}, rest}, Val.rb(v)), Frs.mu(Con{Machine.Fr.arg{Source.Q1{}, Machine.Val.nil{}}, rest}, 0n), bk), hfr)
            case Machine.Val.env{+y0, +y1}:
              Shared.Bool.absurd(Moved(Machine.Ret.go(v, Con{Machine.Fr.arg{Source.Q1{}, Machine.Val.env{y0, y1}}, rest}, bk), Frs.plug(Con{Machine.Fr.arg{Source.Q1{}, Machine.Val.env{y0, y1}}, rest}, Val.rb(v)), Frs.mu(Con{Machine.Fr.arg{Source.Q1{}, Machine.Val.env{y0, y1}}, rest}, 0n), bk), hfr)
            case Machine.Val.arg{+y0, +y1, +y2}:
              Shared.Bool.absurd(Moved(Machine.Ret.go(v, Con{Machine.Fr.arg{Source.Q1{}, Machine.Val.arg{y0, y1, y2}}, rest}, bk), Frs.plug(Con{Machine.Fr.arg{Source.Q1{}, Machine.Val.arg{y0, y1, y2}}, rest}, Val.rb(v)), Frs.mu(Con{Machine.Fr.arg{Source.Q1{}, Machine.Val.arg{y0, y1, y2}}, rest}, 0n), bk), hfr)
            case Machine.Val.clo{+y0, +y1}:
              (SP.Bool.and_intro(Val.ok(y1, Mode.env{}, bk), Frs.ok(Con{Machine.Fr.fun{Source.Q1{}, v}, rest}, bk), hfr, SP.Bool.and_intro(Fr.ok(Machine.Fr.fun{Source.Q1{}, v}, bk), Frs.ok(rest, bk), hv, hrest)),
                Inl{({==}, Frs.lt(rest, 1n+Nat.add(Term.var(y0), Term.w(Clo.rb(y0, y1))), Nat.add(3n+Term.w(Clo.rb(y0, y1)), 0n),
                  Le.pop3(y0, Term.w(Clo.rb(y0, y1)))))})
            case Machine.Val.lab{+y0}:
              (SP.Bool.and_intro(Val.ok(Machine.Val.lab{y0}, Mode.good{}, bk), Frs.ok(Con{Machine.Fr.fun{Source.Q1{}, v}, rest}, bk), hfr, SP.Bool.and_intro(Fr.ok(Machine.Fr.fun{Source.Q1{}, v}, bk), Frs.ok(rest, bk), hv, hrest)),
                Inl{({==}, Frs.lt(rest, 1n, Nat.add(3n+Term.w(Val.rb(Machine.Val.lab{y0})), 0n), {==}))})
            case Machine.Val.rfl{}:
              (SP.Bool.and_intro(Val.ok(Machine.Val.rfl{}, Mode.good{}, bk), Frs.ok(Con{Machine.Fr.fun{Source.Q1{}, v}, rest}, bk), hfr, SP.Bool.and_intro(Fr.ok(Machine.Fr.fun{Source.Q1{}, v}, bk), Frs.ok(rest, bk), hv, hrest)),
                Inl{({==}, Frs.lt(rest, 1n, Nat.add(3n+Term.w(Val.rb(Machine.Val.rfl{})), 0n), {==}))})
            case Machine.Val.tup{+y0, +y1, +y2}:
              (SP.Bool.and_intro(Val.ok(Machine.Val.tup{y0, y1, y2}, Mode.good{}, bk), Frs.ok(Con{Machine.Fr.fun{Source.Q1{}, v}, rest}, bk), hfr, SP.Bool.and_intro(Fr.ok(Machine.Fr.fun{Source.Q1{}, v}, bk), Frs.ok(rest, bk), hv, hrest)),
                Inl{({==}, Frs.lt(rest, 1n, Nat.add(3n+Term.w(Val.rb(Machine.Val.tup{y0, y1, y2})), 0n), {==}))})
            case Machine.Val.call{+y0, +y1}:
              (SP.Bool.and_intro(Val.ok(Machine.Val.call{y0, y1}, Mode.good{}, bk), Frs.ok(Con{Machine.Fr.fun{Source.Q1{}, v}, rest}, bk), hfr, SP.Bool.and_intro(Fr.ok(Machine.Fr.fun{Source.Q1{}, v}, bk), Frs.ok(rest, bk), hv, hrest)),
                Inl{({==}, Frs.lt(rest, 1n, Nat.add(3n+Term.w(Val.rb(Machine.Val.call{y0, y1})), 0n), {==}))})
        case Source.Q2{}:
          match x:
            case Machine.Val.nil{}:
              Shared.Bool.absurd(Moved(Machine.Ret.go(v, Con{Machine.Fr.arg{Source.Q2{}, Machine.Val.nil{}}, rest}, bk), Frs.plug(Con{Machine.Fr.arg{Source.Q2{}, Machine.Val.nil{}}, rest}, Val.rb(v)), Frs.mu(Con{Machine.Fr.arg{Source.Q2{}, Machine.Val.nil{}}, rest}, 0n), bk), hfr)
            case Machine.Val.env{+y0, +y1}:
              Shared.Bool.absurd(Moved(Machine.Ret.go(v, Con{Machine.Fr.arg{Source.Q2{}, Machine.Val.env{y0, y1}}, rest}, bk), Frs.plug(Con{Machine.Fr.arg{Source.Q2{}, Machine.Val.env{y0, y1}}, rest}, Val.rb(v)), Frs.mu(Con{Machine.Fr.arg{Source.Q2{}, Machine.Val.env{y0, y1}}, rest}, 0n), bk), hfr)
            case Machine.Val.arg{+y0, +y1, +y2}:
              Shared.Bool.absurd(Moved(Machine.Ret.go(v, Con{Machine.Fr.arg{Source.Q2{}, Machine.Val.arg{y0, y1, y2}}, rest}, bk), Frs.plug(Con{Machine.Fr.arg{Source.Q2{}, Machine.Val.arg{y0, y1, y2}}, rest}, Val.rb(v)), Frs.mu(Con{Machine.Fr.arg{Source.Q2{}, Machine.Val.arg{y0, y1, y2}}, rest}, 0n), bk), hfr)
            case Machine.Val.clo{+y0, +y1}:
              (SP.Bool.and_intro(Val.ok(y1, Mode.env{}, bk), Frs.ok(Con{Machine.Fr.fun{Source.Q2{}, v}, rest}, bk), hfr, SP.Bool.and_intro(Fr.ok(Machine.Fr.fun{Source.Q2{}, v}, bk), Frs.ok(rest, bk), hv, hrest)),
                Inl{({==}, Frs.lt(rest, 1n+Nat.add(Term.var(y0), Term.w(Clo.rb(y0, y1))), Nat.add(3n+Term.w(Clo.rb(y0, y1)), 0n),
                  Le.pop3(y0, Term.w(Clo.rb(y0, y1)))))})
            case Machine.Val.lab{+y0}:
              (SP.Bool.and_intro(Val.ok(Machine.Val.lab{y0}, Mode.good{}, bk), Frs.ok(Con{Machine.Fr.fun{Source.Q2{}, v}, rest}, bk), hfr, SP.Bool.and_intro(Fr.ok(Machine.Fr.fun{Source.Q2{}, v}, bk), Frs.ok(rest, bk), hv, hrest)),
                Inl{({==}, Frs.lt(rest, 1n, Nat.add(3n+Term.w(Val.rb(Machine.Val.lab{y0})), 0n), {==}))})
            case Machine.Val.rfl{}:
              (SP.Bool.and_intro(Val.ok(Machine.Val.rfl{}, Mode.good{}, bk), Frs.ok(Con{Machine.Fr.fun{Source.Q2{}, v}, rest}, bk), hfr, SP.Bool.and_intro(Fr.ok(Machine.Fr.fun{Source.Q2{}, v}, bk), Frs.ok(rest, bk), hv, hrest)),
                Inl{({==}, Frs.lt(rest, 1n, Nat.add(3n+Term.w(Val.rb(Machine.Val.rfl{})), 0n), {==}))})
            case Machine.Val.tup{+y0, +y1, +y2}:
              (SP.Bool.and_intro(Val.ok(Machine.Val.tup{y0, y1, y2}, Mode.good{}, bk), Frs.ok(Con{Machine.Fr.fun{Source.Q2{}, v}, rest}, bk), hfr, SP.Bool.and_intro(Fr.ok(Machine.Fr.fun{Source.Q2{}, v}, bk), Frs.ok(rest, bk), hv, hrest)),
                Inl{({==}, Frs.lt(rest, 1n, Nat.add(3n+Term.w(Val.rb(Machine.Val.tup{y0, y1, y2})), 0n), {==}))})
            case Machine.Val.call{+y0, +y1}:
              (SP.Bool.and_intro(Val.ok(Machine.Val.call{y0, y1}, Mode.good{}, bk), Frs.ok(Con{Machine.Fr.fun{Source.Q2{}, v}, rest}, bk), hfr, SP.Bool.and_intro(Fr.ok(Machine.Fr.fun{Source.Q2{}, v}, bk), Frs.ok(rest, bk), hv, hrest)),
                Inl{({==}, Frs.lt(rest, 1n, Nat.add(3n+Term.w(Val.rb(Machine.Val.call{y0, y1})), 0n), {==}))})
    case Machine.Fr.fun{+q, +f}:
      S.apply(f, q, v, rest, bk, SP.Bool.and_right(Source.Quan.live(q), Val.ok(f, Mode.good{}, bk), hfr), Good.field(q, v, bk, hv), hrest,
        Frs.mu(rest, 1n), Frs.lt(rest, 0n, 1n, {==}))
    case Machine.Fr.let{q, +f, +e}:
      match q:
        case Source.Q0{}:
          Shared.Bool.absurd(Moved(Machine.Ret.go(v, Con{Machine.Fr.let{Source.Q0{}, f, e}, rest}, bk), Frs.plug(Con{Machine.Fr.let{Source.Q0{}, f, e}, rest}, Val.rb(v)), Frs.mu(Con{Machine.Fr.let{Source.Q0{}, f, e}, rest}, 0n), bk), hfr)
        case Source.Q1{}:
          S.let.Q1(v, f, e, rest, bk, hv, hfr, hrest, Frs.mu(rest, 0n))
        case Source.Q2{}:
          S.let.Q2(v, f, e, rest, bk, hv, hfr, hrest, Frs.mu(rest, 0n))
    case Machine.Fr.fst{+q, +b, +e}:
      (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(Con{Machine.Fr.snd{q, v}, rest}, bk), SP.Bool.and_right(Source.Quan.live(q), Val.ok(e, Mode.env{}, bk), hfr), SP.Bool.and_intro(Val.ok(v, Mode.field(q), bk), Frs.ok(rest, bk), Good.field(q, v, bk, hv), hrest)),
        Inl{({==}, Frs.lt(rest, 1n+Nat.add(Term.var(b), Term.w(Clo.rb(b, e))), Nat.add(3n+Term.w(Clo.rb(b, e)), 0n), Le.pop3(b, Term.w(Clo.rb(b, e)))))})
    case Machine.Fr.snd{+q, +a}:
      (SP.Bool.and_intro(Val.ok(Machine.Val.tup{q, a, v}, Mode.good{}, bk), Frs.ok(rest, bk), SP.Bool.and_intro(Val.ok(a, Mode.field(q), bk), Val.ok(v, Mode.good{}, bk), hfr, hv), hrest),
        Inl{({==}, Frs.lt(rest, 0n, 1n, {==}))})
    case Machine.Fr.rwt{+p, +f, +e}:
      match v:
        case Machine.Val.nil{}:
          Shared.Bool.absurd(Moved(Machine.Ret.go(Machine.Val.nil{}, Con{Machine.Fr.rwt{p, f, e}, rest}, bk), Frs.plug(Con{Machine.Fr.rwt{p, f, e}, rest}, Val.rb(Machine.Val.nil{})), Frs.mu(Con{Machine.Fr.rwt{p, f, e}, rest}, 0n), bk), hv)
        case Machine.Val.env{+w0, +w1}:
          Shared.Bool.absurd(Moved(Machine.Ret.go(Machine.Val.env{w0, w1}, Con{Machine.Fr.rwt{p, f, e}, rest}, bk), Frs.plug(Con{Machine.Fr.rwt{p, f, e}, rest}, Val.rb(Machine.Val.env{w0, w1})), Frs.mu(Con{Machine.Fr.rwt{p, f, e}, rest}, 0n), bk), hv)
        case Machine.Val.arg{+w0, +w1, +w2}:
          Shared.Bool.absurd(Moved(Machine.Ret.go(Machine.Val.arg{w0, w1, w2}, Con{Machine.Fr.rwt{p, f, e}, rest}, bk), Frs.plug(Con{Machine.Fr.rwt{p, f, e}, rest}, Val.rb(Machine.Val.arg{w0, w1, w2})), Frs.mu(Con{Machine.Fr.rwt{p, f, e}, rest}, 0n), bk), hv)
        case Machine.Val.clo{+w0, +w1}:
          match w0:
            case Source.Term.Var{+wt0}:
              Shared.Bool.absurd(Moved(Machine.Ret.go(Machine.Val.clo{Source.Term.Var{wt0}, w1}, Con{Machine.Fr.rwt{p, f, e}, rest}, bk), Frs.plug(Con{Machine.Fr.rwt{p, f, e}, rest}, Val.rb(Machine.Val.clo{Source.Term.Var{wt0}, w1})), Frs.mu(Con{Machine.Fr.rwt{p, f, e}, rest}, 0n), bk), SP.Bool.and_left(Term.is_fun(Source.Term.Var{wt0}), Val.ok(w1, Mode.env{}, bk), hv))
            case Source.Term.Ref{+wt0}:
              Shared.Bool.absurd(Moved(Machine.Ret.go(Machine.Val.clo{Source.Term.Ref{wt0}, w1}, Con{Machine.Fr.rwt{p, f, e}, rest}, bk), Frs.plug(Con{Machine.Fr.rwt{p, f, e}, rest}, Val.rb(Machine.Val.clo{Source.Term.Ref{wt0}, w1})), Frs.mu(Con{Machine.Fr.rwt{p, f, e}, rest}, 0n), bk), SP.Bool.and_left(Term.is_fun(Source.Term.Ref{wt0}), Val.ok(w1, Mode.env{}, bk), hv))
            case Source.Term.Ann{+wt0, +wt1}:
              Shared.Bool.absurd(Moved(Machine.Ret.go(Machine.Val.clo{Source.Term.Ann{wt0, wt1}, w1}, Con{Machine.Fr.rwt{p, f, e}, rest}, bk), Frs.plug(Con{Machine.Fr.rwt{p, f, e}, rest}, Val.rb(Machine.Val.clo{Source.Term.Ann{wt0, wt1}, w1})), Frs.mu(Con{Machine.Fr.rwt{p, f, e}, rest}, 0n), bk), SP.Bool.and_left(Term.is_fun(Source.Term.Ann{wt0, wt1}), Val.ok(w1, Mode.env{}, bk), hv))
            case Source.Term.Let{+wt0, +wt1, +wt2}:
              Shared.Bool.absurd(Moved(Machine.Ret.go(Machine.Val.clo{Source.Term.Let{wt0, wt1, wt2}, w1}, Con{Machine.Fr.rwt{p, f, e}, rest}, bk), Frs.plug(Con{Machine.Fr.rwt{p, f, e}, rest}, Val.rb(Machine.Val.clo{Source.Term.Let{wt0, wt1, wt2}, w1})), Frs.mu(Con{Machine.Fr.rwt{p, f, e}, rest}, 0n), bk), SP.Bool.and_left(Term.is_fun(Source.Term.Let{wt0, wt1, wt2}), Val.ok(w1, Mode.env{}, bk), hv))
            case Source.Term.Typ{+wt0}:
              Ctx.stuck(rest, Source.Term.Rwt{Val.rb(Machine.Val.clo{Source.Term.Typ{wt0}, w1}), Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e)}, bk, hrest, {==}, Rwt.stuck(Machine.Val.clo{Source.Term.Typ{wt0}, w1}, Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e), bk, hv, {==}))
            case Source.Term.Min{+wt0, +wt1}:
              Shared.Bool.absurd(Moved(Machine.Ret.go(Machine.Val.clo{Source.Term.Min{wt0, wt1}, w1}, Con{Machine.Fr.rwt{p, f, e}, rest}, bk), Frs.plug(Con{Machine.Fr.rwt{p, f, e}, rest}, Val.rb(Machine.Val.clo{Source.Term.Min{wt0, wt1}, w1})), Frs.mu(Con{Machine.Fr.rwt{p, f, e}, rest}, 0n), bk), SP.Bool.and_left(Term.is_fun(Source.Term.Min{wt0, wt1}), Val.ok(w1, Mode.env{}, bk), hv))
            case Source.Term.All{+wt0, +wt1, +wt2}:
              Ctx.stuck(rest, Source.Term.Rwt{Val.rb(Machine.Val.clo{Source.Term.All{wt0, wt1, wt2}, w1}), Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e)}, bk, hrest, {==}, Rwt.stuck(Machine.Val.clo{Source.Term.All{wt0, wt1, wt2}, w1}, Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e), bk, hv, {==}))
            case Source.Term.Lam{+wt0, +wt1}:
              Ctx.stuck(rest, Source.Term.Rwt{Val.rb(Machine.Val.clo{Source.Term.Lam{wt0, wt1}, w1}), Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e)}, bk, hrest, {==}, Rwt.stuck(Machine.Val.clo{Source.Term.Lam{wt0, wt1}, w1}, Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e), bk, hv, {==}))
            case Source.Term.App{+wt0, +wt1, +wt2}:
              Shared.Bool.absurd(Moved(Machine.Ret.go(Machine.Val.clo{Source.Term.App{wt0, wt1, wt2}, w1}, Con{Machine.Fr.rwt{p, f, e}, rest}, bk), Frs.plug(Con{Machine.Fr.rwt{p, f, e}, rest}, Val.rb(Machine.Val.clo{Source.Term.App{wt0, wt1, wt2}, w1})), Frs.mu(Con{Machine.Fr.rwt{p, f, e}, rest}, 0n), bk), SP.Bool.and_left(Term.is_fun(Source.Term.App{wt0, wt1, wt2}), Val.ok(w1, Mode.env{}, bk), hv))
            case Source.Term.Sig{+wt0, +wt1, +wt2}:
              Ctx.stuck(rest, Source.Term.Rwt{Val.rb(Machine.Val.clo{Source.Term.Sig{wt0, wt1, wt2}, w1}), Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e)}, bk, hrest, {==}, Rwt.stuck(Machine.Val.clo{Source.Term.Sig{wt0, wt1, wt2}, w1}, Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e), bk, hv, {==}))
            case Source.Term.Tup{+wt0, +wt1, +wt2}:
              Shared.Bool.absurd(Moved(Machine.Ret.go(Machine.Val.clo{Source.Term.Tup{wt0, wt1, wt2}, w1}, Con{Machine.Fr.rwt{p, f, e}, rest}, bk), Frs.plug(Con{Machine.Fr.rwt{p, f, e}, rest}, Val.rb(Machine.Val.clo{Source.Term.Tup{wt0, wt1, wt2}, w1})), Frs.mu(Con{Machine.Fr.rwt{p, f, e}, rest}, 0n), bk), SP.Bool.and_left(Term.is_fun(Source.Term.Tup{wt0, wt1, wt2}), Val.ok(w1, Mode.env{}, bk), hv))
            case Source.Term.Prj{+wt0}:
              Ctx.stuck(rest, Source.Term.Rwt{Val.rb(Machine.Val.clo{Source.Term.Prj{wt0}, w1}), Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e)}, bk, hrest, {==}, Rwt.stuck(Machine.Val.clo{Source.Term.Prj{wt0}, w1}, Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e), bk, hv, {==}))
            case Source.Term.Enu{+wt0}:
              Ctx.stuck(rest, Source.Term.Rwt{Val.rb(Machine.Val.clo{Source.Term.Enu{wt0}, w1}), Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e)}, bk, hrest, {==}, Rwt.stuck(Machine.Val.clo{Source.Term.Enu{wt0}, w1}, Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e), bk, hv, {==}))
            case Source.Term.Lab{+wt0}:
              Shared.Bool.absurd(Moved(Machine.Ret.go(Machine.Val.clo{Source.Term.Lab{wt0}, w1}, Con{Machine.Fr.rwt{p, f, e}, rest}, bk), Frs.plug(Con{Machine.Fr.rwt{p, f, e}, rest}, Val.rb(Machine.Val.clo{Source.Term.Lab{wt0}, w1})), Frs.mu(Con{Machine.Fr.rwt{p, f, e}, rest}, 0n), bk), SP.Bool.and_left(Term.is_fun(Source.Term.Lab{wt0}), Val.ok(w1, Mode.env{}, bk), hv))
            case Source.Term.Mat{+wt0, +wt1, +wt2}:
              Ctx.stuck(rest, Source.Term.Rwt{Val.rb(Machine.Val.clo{Source.Term.Mat{wt0, wt1, wt2}, w1}), Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e)}, bk, hrest, {==}, Rwt.stuck(Machine.Val.clo{Source.Term.Mat{wt0, wt1, wt2}, w1}, Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e), bk, hv, {==}))
            case Source.Term.Efq{}:
              Ctx.stuck(rest, Source.Term.Rwt{Val.rb(Machine.Val.clo{Source.Term.Efq{}, w1}), Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e)}, bk, hrest, {==}, Rwt.stuck(Machine.Val.clo{Source.Term.Efq{}, w1}, Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e), bk, hv, {==}))
            case Source.Term.Eql{+wt0, +wt1, +wt2}:
              Ctx.stuck(rest, Source.Term.Rwt{Val.rb(Machine.Val.clo{Source.Term.Eql{wt0, wt1, wt2}, w1}), Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e)}, bk, hrest, {==}, Rwt.stuck(Machine.Val.clo{Source.Term.Eql{wt0, wt1, wt2}, w1}, Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e), bk, hv, {==}))
            case Source.Term.Rfl{}:
              Shared.Bool.absurd(Moved(Machine.Ret.go(Machine.Val.clo{Source.Term.Rfl{}, w1}, Con{Machine.Fr.rwt{p, f, e}, rest}, bk), Frs.plug(Con{Machine.Fr.rwt{p, f, e}, rest}, Val.rb(Machine.Val.clo{Source.Term.Rfl{}, w1})), Frs.mu(Con{Machine.Fr.rwt{p, f, e}, rest}, 0n), bk), SP.Bool.and_left(Term.is_fun(Source.Term.Rfl{}), Val.ok(w1, Mode.env{}, bk), hv))
            case Source.Term.Rwt{+wt0, +wt1, +wt2}:
              Shared.Bool.absurd(Moved(Machine.Ret.go(Machine.Val.clo{Source.Term.Rwt{wt0, wt1, wt2}, w1}, Con{Machine.Fr.rwt{p, f, e}, rest}, bk), Frs.plug(Con{Machine.Fr.rwt{p, f, e}, rest}, Val.rb(Machine.Val.clo{Source.Term.Rwt{wt0, wt1, wt2}, w1})), Frs.mu(Con{Machine.Fr.rwt{p, f, e}, rest}, 0n), bk), SP.Bool.and_left(Term.is_fun(Source.Term.Rwt{wt0, wt1, wt2}), Val.ok(w1, Mode.env{}, bk), hv))
        case Machine.Val.lab{+w0}:
          Ctx.stuck(rest, Source.Term.Rwt{Val.rb(Machine.Val.lab{w0}), Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e)}, bk, hrest, {==}, Rwt.stuck(Machine.Val.lab{w0}, Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e), bk, hv, {==}))
        case Machine.Val.rfl{}:
          (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(rest, bk), hfr, hrest),
            Inr{Ctx.go(rest, Source.Term.Rwt{Val.rb(Machine.Val.rfl{}), Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e)}, Clo.rb(f, e), bk, hrest, {==}, {==})})
        case Machine.Val.tup{+w0, +w1, +w2}:
          Ctx.stuck(rest, Source.Term.Rwt{Val.rb(Machine.Val.tup{w0, w1, w2}), Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e)}, bk, hrest, {==}, Rwt.stuck(Machine.Val.tup{w0, w1, w2}, Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e), bk, hv, {==}))
        case Machine.Val.call{+w0, +w1}:
          Ctx.stuck(rest, Source.Term.Rwt{Val.rb(Machine.Val.call{w0, w1}), Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e)}, bk, hrest, {==}, Rwt.stuck(Machine.Val.call{w0, w1}, Source.Term.sub(p, 2n, Source.Sub.env{Env.rb(e)}), Clo.rb(f, e), bk, hv, Call.elim(Val.rb(Machine.Val.call{w0, w1}), Call.rb_is_call(w0, w1), z => {Source.Term.is_rfl(z) == False{} : Bool}, q2 => f2 => x2 => {==}, n => {==})))
    case Machine.Fr.min1{+b, +e}:
      (SP.Bool.and_intro(Val.ok(e, Mode.env{}, bk), Frs.ok(Con{Machine.Fr.min2{v}, rest}, bk), hfr, SP.Bool.and_intro(Val.ok(v, Mode.good{}, bk), Frs.ok(rest, bk), hv, hrest)),
        Inl{({==}, Frs.lt(rest, 1n+Nat.add(Term.var(b), Term.w(Clo.rb(b, e))), Nat.add(3n+Term.w(Clo.rb(b, e)), 0n), Le.pop3(b, Term.w(Clo.rb(b, e)))))})
    case Machine.Fr.min2{+a}:
      S.meet(a, v, rest, bk, hfr, hv, hrest, Frs.mu(rest, 1n))

# the step from St.ret v fs
def S.ret(+v: Machine.Val, fs: List<&2, Machine.Fr>, +bk: List<&2, Source.Def>, +hv: {Val.ok(v, Mode.good{}, bk) == True{} : Bool},
  +hfs: {Frs.ok(fs, bk) == True{} : Bool}) ->
  Moved(Machine.Ret.go(v, fs, bk), Frs.plug(fs, Val.rb(v)), Frs.mu(fs, 0n), bk):
  match fs:
    case Nil{}:
      (hv, {==})
    case Con{+fr, +rest}:
      S.frame(fr, v, rest, bk, hv, SP.Bool.and_left(Fr.ok(fr, bk), Frs.ok(rest, bk), hfs), SP.Bool.and_right(Fr.ok(fr, bk), Frs.ok(rest, bk), hfs))

# one step of the machine, from a state that keeps the invariant
def Step.ok(s: Machine.St, +bk: List<&2, Source.Def>, +h: {St.ok(s, bk) == True{} : Bool}) ->
  Moved(Machine.Machine.step(s, bk), St.rb(s), St.mu(s), bk):
  match s:
    case Machine.St.eval{t, +e, +fs}:
      S.eval(t, e, fs, bk, SP.Bool.and_left(Val.ok(e, Mode.env{}, bk), Frs.ok(fs, bk), h),
        SP.Bool.and_right(Val.ok(e, Mode.env{}, bk), Frs.ok(fs, bk), h))
    case Machine.St.ret{+v, +fs}:
      S.ret(v, fs, bk, SP.Bool.and_left(Val.ok(v, Mode.good{}, bk), Frs.ok(fs, bk), h),
        SP.Bool.and_right(Val.ok(v, Mode.good{}, bk), Frs.ok(fs, bk), h))

# Bound
# =====

def Bnd.three(+acc: Nat, +x: Nat, +wu: Nat, h: {Nat.is_le(acc, 1n+wu) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(3n+x, acc), 1n+5n+Nat.add(x, wu)) == True{} : Bool}:
  Le.add(Nat.add(x, acc), 1n+Nat.add(x, wu),
    Eq.rw(Nat, Nat.add(x, 1n+wu), 1n+Nat.add(x, wu), Nat.add_succ(x, wu),
      z => {Nat.is_le(Nat.add(x, acc), z) == True{} : Bool}, Nat.is_le_mono(x, acc, 1n+wu, h)), 2n)

def Bnd.one(+acc: Nat, +wu: Nat, +x: Nat, h: {Nat.is_le(acc, 1n+wu) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(1n, acc), 1n+5n+Nat.add(wu, x)) == True{} : Bool}:
  Le.add(acc, 1n+Nat.add(wu, x), Shared.Nat.is_le_trans(acc, 1n+wu, 1n+Nat.add(wu, x), h, Shared.Nat.is_le_add(1n+wu, x)), 4n)

def Bnd.onez(+acc: Nat, +wu: Nat, h: {Nat.is_le(acc, 1n+wu) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(1n, acc), 1n+5n+Nat.add(0n, wu)) == True{} : Bool}:
  Le.add(acc, 1n+wu, h, 4n)

def Bnd.zero(+acc: Nat, +wu: Nat, h: {Nat.is_le(acc, 1n+wu) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(0n, acc), 1n+5n+wu) == True{} : Bool}:
  Le.add(acc, 1n+wu, h, 5n)

# a frame's measure is at most the weight that it adds to the term
def Fr.bound(fr: Machine.Fr, +u: Source.Term, +acc: Nat, +bk: List<&2, Source.Def>, hfr: {Fr.ok(fr, bk) == True{} : Bool},
  h: {Nat.is_le(acc, 1n+Term.w(u)) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(Fr.pend(fr), acc), 1n+Term.w(Fr.plug(fr, u))) == True{} : Bool}:
  match fr:
    case Machine.Fr.arg{q, x}:
      match q:
        case Source.Q0{}:
          Bnd.onez(acc, Term.w(u), h)
        case Source.Q1{}:
          Bnd.three(acc, Term.w(Val.rb(x)), Term.w(u), h)
        case Source.Q2{}:
          Bnd.three(acc, Term.w(Val.rb(x)), Term.w(u), h)
    case Machine.Fr.fun{q, f}:
      match q:
        case Source.Q0{}:
          Shared.Bool.absurd({Nat.is_le(Nat.add(1n, acc), 1n+Term.w(Source.Term.App{Source.Q0{}, Val.rb(f), u})) == True{} : Bool}, hfr)
        case Source.Q1{}:
          Bnd.one(acc, Term.w(u), Term.w(Val.rb(f)), h)
        case Source.Q2{}:
          Bnd.one(acc, Term.w(u), Term.w(Val.rb(f)), h)
    case Machine.Fr.let{q, f, e}:
      match q:
        case Source.Q0{}:
          Shared.Bool.absurd({Nat.is_le(Nat.add(0n, acc), 1n+Term.w(Fr.plug(Machine.Fr.let{Source.Q0{}, f, e}, u))) == True{} : Bool}, hfr)
        case Source.Q1{}:
          Bnd.zero(acc, Term.w(u), h)
        case Source.Q2{}:
          Bnd.zero(acc, Term.w(u), h)
    case Machine.Fr.fst{q, +b, +e}:
      match q:
        case Source.Q0{}:
          Shared.Bool.absurd({Nat.is_le(Nat.add(3n+Term.w(Clo.rb(b, e)), acc), 1n+Term.w(Fr.plug(Machine.Fr.fst{Source.Q0{}, b, e}, u))) == True{} : Bool}, hfr)
        case Source.Q1{}:
          Bnd.three(acc, Term.w(Clo.rb(b, e)), Term.w(u), h)
        case Source.Q2{}:
          Bnd.three(acc, Term.w(Clo.rb(b, e)), Term.w(u), h)
    case Machine.Fr.snd{q, a}:
      Bnd.one(acc, Term.w(u), Q.w(q, Term.w(Val.rb(a))), h)
    case Machine.Fr.rwt{p, f, e}:
      Bnd.zero(acc, Term.w(u), h)
    case Machine.Fr.min1{b, e}:
      Bnd.three(acc, Term.w(Clo.rb(b, e)), Term.w(u), h)
    case Machine.Fr.min2{a}:
      Bnd.one(acc, Term.w(u), Term.w(Val.rb(a)), h)

def Frs.bound(fs: List<&2, Machine.Fr>, +u: Source.Term, +acc: Nat, +bk: List<&2, Source.Def>, +hfs: {Frs.ok(fs, bk) == True{} : Bool},
  h: {Nat.is_le(acc, 1n+Term.w(u)) == True{} : Bool}) ->
  {Nat.is_le(Frs.mu(fs, acc), 1n+Term.w(Frs.plug(fs, u))) == True{} : Bool}:
  match fs:
    case Nil{}:
      h
    case Con{+fr, +rest}:
      Frs.bound(rest, Fr.plug(fr, u), Nat.add(Fr.pend(fr), acc), bk, SP.Bool.and_right(Fr.ok(fr, bk), Frs.ok(rest, bk), hfs),
        Fr.bound(fr, u, acc, bk, SP.Bool.and_left(Fr.ok(fr, bk), Frs.ok(rest, bk), hfs), h))

# a state's measure is at most 1 plus the weight of its term
def St.bound(s: Machine.St, +bk: List<&2, Source.Def>, +hs: {St.ok(s, bk) == True{} : Bool}) ->
  {Nat.is_le(St.mu(s), 1n+Term.w(St.rb(s))) == True{} : Bool}:
  match s:
    case Machine.St.eval{+t, +e, +fs}:
      Frs.bound(fs, Clo.rb(t, e), Nat.add(Term.var(t), Term.w(Clo.rb(t, e))), bk,
        SP.Bool.and_right(Val.ok(e, Mode.env{}, bk), Frs.ok(fs, bk), hs), Le.step1(t, Term.w(Clo.rb(t, e))))
    case Machine.St.ret{+v, +fs}:
      Frs.bound(fs, Val.rb(v), 0n, bk, SP.Bool.and_right(Val.ok(v, Mode.good{}, bk), Frs.ok(fs, bk), hs), {==})

# Runs
# ====

def Run.mono.of(mv: Machine.Move, -m: Nat, +d: Nat, +bk: List<&2, Source.Def>, -o: Source.Obs,
  rec: @s2: Machine.St -> {Machine.Machine.run(m, s2, bk) == Some{o} : Maybe<&2, Source.Obs>} ->
    {Machine.Machine.run(Nat.add(m, d), s2, bk) == Some{o} : Maybe<&2, Source.Obs>},
  h: {Machine.Run.next(mv, s2 => Machine.Machine.run(m, s2, bk)) == Some{o} : Maybe<&2, Source.Obs>}) ->
  {Machine.Run.next(mv, s2 => Machine.Machine.run(Nat.add(m, d), s2, bk)) == Some{o} : Maybe<&2, Source.Obs>}:
  match mv:
    case Machine.Move.go{s2}:
      rec(s2, h)
    case Machine.Move.done{v}:
      h
    case Machine.Move.stuck{}:
      Empty.absurd({None{} == Some{o} : Maybe<&2, Source.Obs>}, Shared.Maybe.no_none(Source.Obs, o, h))

# more fuel keeps the machine's result
def Run.mono(n: Nat, +s: Machine.St, +bk: List<&2, Source.Def>, +d: Nat, -o: Source.Obs,
  h: {Machine.Machine.run(n, s, bk) == Some{o} : Maybe<&2, Source.Obs>}) ->
  {Machine.Machine.run(Nat.add(n, d), s, bk) == Some{o} : Maybe<&2, Source.Obs>}:
  match n:
    case 0n:
      Empty.absurd({Machine.Machine.run(d, s, bk) == Some{o} : Maybe<&2, Source.Obs>}, Shared.Maybe.no_none(Source.Obs, o, h))
    case 1n+m:
      Run.mono.of(Machine.Machine.step(s, bk), m, d, bk, o, s2 => h2 => Run.mono(m, s2, bk, d, o, h2), h)

def Src.mono.next(ms: Maybe<&2, Source.Term>, -t: Source.Term, -m: Nat, +bk: List<&2, Source.Def>, -u: Source.Term,
  rec: @a: Source.Term -> {Source.Term.run(m, a, bk) == Some{u} : Maybe<&2, Source.Term>} ->
    {Source.Term.run(1n+m, a, bk) == Some{u} : Maybe<&2, Source.Term>},
  h: {Source.Term.run.next(ms, t, a => Source.Term.run(m, a, bk)) == Some{u} : Maybe<&2, Source.Term>}) ->
  {Source.Term.run.next(ms, t, a => Source.Term.run(1n+m, a, bk)) == Some{u} : Maybe<&2, Source.Term>}:
  match ms:
    case Some{a}:
      rec(a, h)
    case None{}:
      h

def Src.mono.of(c: Bool, +t: Source.Term, -m: Nat, +bk: List<&2, Source.Def>, -u: Source.Term,
  rec: @a: Source.Term -> {Source.Term.run(m, a, bk) == Some{u} : Maybe<&2, Source.Term>} ->
    {Source.Term.run(1n+m, a, bk) == Some{u} : Maybe<&2, Source.Term>},
  h: {Source.Term.run.of(c, t, z => Source.Term.step(t, bk), z => Source.Term.run(m, z, bk)) == Some{u} : Maybe<&2, Source.Term>}) ->
  {Source.Term.run.of(c, t, z => Source.Term.step(t, bk), z => Source.Term.run(1n+m, z, bk)) == Some{u} : Maybe<&2, Source.Term>}:
  match c:
    case True{}:
      h
    case False{}:
      Src.mono.next(Source.Term.step(t, bk), t, m, bk, u, rec, h)

# more fuel keeps the source's result
def Src.mono(n: Nat, +t: Source.Term, +bk: List<&2, Source.Def>, -u: Source.Term,
  h: {Source.Term.run(n, t, bk) == Some{u} : Maybe<&2, Source.Term>}) ->
  {Source.Term.run(1n+n, t, bk) == Some{u} : Maybe<&2, Source.Term>}:
  match n:
    case 0n:
      Empty.absurd({Source.Term.run(1n, t, bk) == Some{u} : Maybe<&2, Source.Term>}, Shared.Maybe.no_none(Source.Term, u, h))
    case 1n+m:
      Src.mono.of(Source.Term.is_value(t, False{}, bk), t, m, bk, u, a => ha => Src.mono(m, a, bk, u, ha), h)

def Obs.mono.of(mr: Maybe<&2, Source.Term>, +t: Source.Term, +n: Nat, +bk: List<&2, Source.Def>, -o: Source.Obs,
  hr: {Source.Term.run(n, t, bk) == mr : Maybe<&2, Source.Term>}, h: {Source.Maybe.observe(mr) == Some{o} : Maybe<&2, Source.Obs>}) ->
  {Source.Maybe.observe(Source.Term.run(1n+n, t, bk)) == Some{o} : Maybe<&2, Source.Obs>}:
  match mr:
    case None{}:
      Empty.absurd({Source.Maybe.observe(Source.Term.run(1n+n, t, bk)) == Some{o} : Maybe<&2, Source.Obs>}, Shared.Maybe.no_none(Source.Obs, o, h))
    case Some{+u}:
      Eq.rw(Maybe<&2, Source.Term>, Some{u}, Source.Term.run(1n+n, t, bk),
        Equal.sym(Maybe<&2, Source.Term>, Source.Term.run(1n+n, t, bk), Some{u}, Src.mono(n, t, bk, u, hr)),
        z => {Source.Maybe.observe(z) == Some{o} : Maybe<&2, Source.Obs>}, h)

def Obs.mono(+t: Source.Term, +n: Nat, +bk: List<&2, Source.Def>, -o: Source.Obs,
  h: {Source.Maybe.observe(Source.Term.run(n, t, bk)) == Some{o} : Maybe<&2, Source.Obs>}) ->
  {Source.Maybe.observe(Source.Term.run(1n+n, t, bk)) == Some{o} : Maybe<&2, Source.Obs>}:
  Obs.mono.of(Source.Term.run(n, t, bk), t, n, bk, o, {==}, h)

def Obs.value.tup(mb: Maybe<&2, Source.Obs>, q: Source.Quan, ma: Maybe<&2, Source.Obs>, -a: Source.Term, -b: Source.Term,
  +bk: List<&2, Source.Def>, -o: Source.Obs, h: {Source.Obs.tup.of(mb, Source.Quan.live(q), ma) == Some{o} : Maybe<&2, Source.Obs>},
  hb: @y: Source.Obs -> {mb == Some{y} : Maybe<&2, Source.Obs>} -> {Source.Term.is_value(b, False{}, bk) == True{} : Bool},
  ha: @x: Source.Obs -> {ma == Some{x} : Maybe<&2, Source.Obs>} -> {Source.Term.is_value(a, False{}, bk) == True{} : Bool}) ->
  {Bool.and(Bool.or(Bool.not(Source.Quan.live(q)), Source.Term.is_value(a, False{}, bk)), Source.Term.is_value(b, False{}, bk)) == True{} : Bool}:
  match mb:
    case None{}:
      Empty.absurd({Bool.and(Bool.or(Bool.not(Source.Quan.live(q)), Source.Term.is_value(a, False{}, bk)), Source.Term.is_value(b, False{}, bk)) == True{} : Bool},
        Shared.Maybe.no_none(Source.Obs, o, h))
    case Some{y}:
      match q:
        case Source.Q0{}:
          hb(y, {==})
        case Source.Q1{}:
          match ma:
            case None{}:
              Empty.absurd({Bool.and(Source.Term.is_value(a, False{}, bk), Source.Term.is_value(b, False{}, bk)) == True{} : Bool},
                Shared.Maybe.no_none(Source.Obs, o, h))
            case Some{x}:
              SP.Bool.and_intro(Source.Term.is_value(a, False{}, bk), Source.Term.is_value(b, False{}, bk), ha(x, {==}), hb(y, {==}))
        case Source.Q2{}:
          match ma:
            case None{}:
              Empty.absurd({Bool.and(Source.Term.is_value(a, False{}, bk), Source.Term.is_value(b, False{}, bk)) == True{} : Bool},
                Shared.Maybe.no_none(Source.Obs, o, h))
            case Some{x}:
              SP.Bool.and_intro(Source.Term.is_value(a, False{}, bk), Source.Term.is_value(b, False{}, bk), ha(x, {==}), hb(y, {==}))

# a term that shows data is a value
def Obs.value(t: Source.Term, +bk: List<&2, Source.Def>, -o: Source.Obs,
  h: {Source.Term.observe(t) == Some{o} : Maybe<&2, Source.Obs>}) -> {Source.Term.is_value(t, False{}, bk) == True{} : Bool}:
  match t:
    case Source.Term.Var{+z0}:
      Empty.absurd({Source.Term.is_value(Source.Term.Var{z0}, False{}, bk) == True{} : Bool}, Shared.Maybe.no_none(Source.Obs, o, h))
    case Source.Term.Ref{+z0}:
      Empty.absurd({Source.Term.is_value(Source.Term.Ref{z0}, False{}, bk) == True{} : Bool}, Shared.Maybe.no_none(Source.Obs, o, h))
    case Source.Term.Ann{+z0, +z1}:
      Empty.absurd({Source.Term.is_value(Source.Term.Ann{z0, z1}, False{}, bk) == True{} : Bool}, Shared.Maybe.no_none(Source.Obs, o, h))
    case Source.Term.Let{+z0, +z1, +z2}:
      Empty.absurd({Source.Term.is_value(Source.Term.Let{z0, z1, z2}, False{}, bk) == True{} : Bool}, Shared.Maybe.no_none(Source.Obs, o, h))
    case Source.Term.Typ{+z0}:
      Empty.absurd({Source.Term.is_value(Source.Term.Typ{z0}, False{}, bk) == True{} : Bool}, Shared.Maybe.no_none(Source.Obs, o, h))
    case Source.Term.Min{+z0, +z1}:
      Empty.absurd({Source.Term.is_value(Source.Term.Min{z0, z1}, False{}, bk) == True{} : Bool}, Shared.Maybe.no_none(Source.Obs, o, h))
    case Source.Term.All{+z0, +z1, +z2}:
      Empty.absurd({Source.Term.is_value(Source.Term.All{z0, z1, z2}, False{}, bk) == True{} : Bool}, Shared.Maybe.no_none(Source.Obs, o, h))
    case Source.Term.Lam{+z0, +z1}:
      Empty.absurd({Source.Term.is_value(Source.Term.Lam{z0, z1}, False{}, bk) == True{} : Bool}, Shared.Maybe.no_none(Source.Obs, o, h))
    case Source.Term.App{+z0, +z1, +z2}:
      Empty.absurd({Source.Term.is_value(Source.Term.App{z0, z1, z2}, False{}, bk) == True{} : Bool}, Shared.Maybe.no_none(Source.Obs, o, h))
    case Source.Term.Sig{+z0, +z1, +z2}:
      Empty.absurd({Source.Term.is_value(Source.Term.Sig{z0, z1, z2}, False{}, bk) == True{} : Bool}, Shared.Maybe.no_none(Source.Obs, o, h))
    case Source.Term.Tup{+z0, +z1, +z2}:
      Obs.value.tup(Source.Term.observe(z2), z0, Source.Term.observe(z1), z1, z2, bk, o, h,
        y => ey => Obs.value(z2, bk, y, ey), x => ex => Obs.value(z1, bk, x, ex))
    case Source.Term.Prj{+z0}:
      Empty.absurd({Source.Term.is_value(Source.Term.Prj{z0}, False{}, bk) == True{} : Bool}, Shared.Maybe.no_none(Source.Obs, o, h))
    case Source.Term.Enu{+z0}:
      Empty.absurd({Source.Term.is_value(Source.Term.Enu{z0}, False{}, bk) == True{} : Bool}, Shared.Maybe.no_none(Source.Obs, o, h))
    case Source.Term.Lab{+z0}:
      {==}
    case Source.Term.Mat{+z0, +z1, +z2}:
      Empty.absurd({Source.Term.is_value(Source.Term.Mat{z0, z1, z2}, False{}, bk) == True{} : Bool}, Shared.Maybe.no_none(Source.Obs, o, h))
    case Source.Term.Efq{}:
      Empty.absurd({Source.Term.is_value(Source.Term.Efq{}, False{}, bk) == True{} : Bool}, Shared.Maybe.no_none(Source.Obs, o, h))
    case Source.Term.Eql{+z0, +z1, +z2}:
      Empty.absurd({Source.Term.is_value(Source.Term.Eql{z0, z1, z2}, False{}, bk) == True{} : Bool}, Shared.Maybe.no_none(Source.Obs, o, h))
    case Source.Term.Rfl{}:
      {==}
    case Source.Term.Rwt{+z0, +z1, +z2}:
      Empty.absurd({Source.Term.is_value(Source.Term.Rwt{z0, z1, z2}, False{}, bk) == True{} : Bool}, Shared.Maybe.no_none(Source.Obs, o, h))

# Keeps
# =====

# what the machine is to reach from a state of term t: a value of t that
# shows o, or the state of the term after t's step, from where a run of M
# steps shows o
type Goal<-t: Source.Term, -o: Source.Obs, -M: Nat, -bk: List<&2, Source.Def>> is Type:
  Goal.val{hv: {Source.Term.is_value(t, False{}, bk) == True{} : Bool}, ho: {Source.Term.observe(t) == Some{o} : Maybe<&2, Source.Obs>}}
  Goal.step{u: Source.Term, hst: {Source.Term.step(t, bk) == Some{u} : Maybe<&2, Source.Term>},
    next: @s2: Machine.St -> {St.ok(s2, bk) == True{} : Bool} -> {St.rb(s2) == u : Source.Term} ->
      {Machine.Machine.run(M, s2, bk) == Some{o} : Maybe<&2, Source.Obs>}}

def Inner.of(mv: Machine.Move, +j: Nat, +t: Source.Term, +mu: Nat, +M: Nat, +bk: List<&2, Source.Def>, -o: Source.Obs,
  mvd: Moved(mv, t, mu, bk), hj: {Nat.is_le(mu, j) == True{} : Bool}, g: Goal<t, o, M, bk>,
  rec: @s2: Machine.St -> {St.ok(s2, bk) == True{} : Bool} -> {Nat.is_le(1n+St.mu(s2), j) == True{} : Bool} ->
    Goal<St.rb(s2), o, M, bk> -> {Machine.Machine.run(Nat.add(j, M), s2, bk) == Some{o} : Maybe<&2, Source.Obs>}) ->
  {Machine.Run.next(mv, s2 => Machine.Machine.run(Nat.add(j, M), s2, bk)) == Some{o} : Maybe<&2, Source.Obs>}:
  match mv:
    case Machine.Move.go{+s2}:
      match mvd:
        case (ok2, r):
          match r:
            case Inl{(eq2, lt2)}:
              rec(s2, ok2, Shared.Nat.is_le_trans(1n+St.mu(s2), mu, j, lt2, hj),
                Eq.rw(Source.Term, t, St.rb(s2), Equal.sym(Source.Term, St.rb(s2), t, eq2), z => Goal<z, o, M, bk>, g))
            case Inr{st}:
              match g:
                case Goal.val{hv, ho}:
                  Empty.absurd({Machine.Machine.run(Nat.add(j, M), s2, bk) == Some{o} : Maybe<&2, Source.Obs>},
                    Shared.Maybe.no_none(Source.Term, St.rb(s2),
                      Equal.trans(Maybe<&2, Source.Term>, None{}, Source.Term.step(t, bk), Some{St.rb(s2)},
                        Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(t, bk), None{}, Vals.step(t, False{}, bk, hv)), st)))
                case Goal.step{u, hst, next}:
                  Eq.rw(Nat, Nat.add(M, j), Nat.add(j, M), Nat.add_comm(M, j),
                    z => {Machine.Machine.run(z, s2, bk) == Some{o} : Maybe<&2, Source.Obs>},
                    Run.mono(M, s2, bk, j, o, next(s2, ok2,
                      SP.Maybe.some_inj(Source.Term, St.rb(s2), u,
                        Equal.trans(Maybe<&2, Source.Term>, Some{St.rb(s2)}, Source.Term.step(t, bk), Some{u},
                          Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(t, bk), Some{St.rb(s2)}, st), hst)))))
    case Machine.Move.done{+v}:
      match mvd:
        case (okv, +eqv):
          match g:
            case Goal.val{hv, ho}:
              Equal.trans(Maybe<&2, Source.Obs>, Machine.Val.observe(v), Source.Term.observe(Val.rb(v)), Some{o}, Obs.eq(v, bk, okv),
                Equal.trans(Maybe<&2, Source.Obs>, Source.Term.observe(Val.rb(v)), Source.Term.observe(t), Some{o},
                  Equal.cong(Source.Term, Maybe<&2, Source.Obs>, z => Source.Term.observe(z), Val.rb(v), t, eqv), ho))
            case Goal.step{u, hst, next}:
              Empty.absurd({Machine.Val.observe(v) == Some{o} : Maybe<&2, Source.Obs>},
                Shared.Maybe.no_none(Source.Term, u,
                  Equal.trans(Maybe<&2, Source.Term>, None{}, Source.Term.step(t, bk), Some{u},
                    Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(t, bk), None{},
                      Eq.rw(Source.Term, Val.rb(v), t, eqv, z => {Source.Term.step(z, bk) == None{} : Maybe<&2, Source.Term>},
                        Vals.step(Val.rb(v), False{}, bk, Val.value(v, bk, okv)))), hst)))
    case Machine.Move.stuck{}:
      match mvd:
        case (nv, ns):
          match g:
            case Goal.val{hv, ho}:
              Empty.absurd({None{} == Some{o} : Maybe<&2, Source.Obs>},
                Bool.true_false(Equal.trans(Bool, True{}, Source.Term.is_value(t, False{}, bk), False{},
                  Equal.sym(Bool, Source.Term.is_value(t, False{}, bk), True{}, hv), nv)))
            case Goal.step{u, hst, next}:
              Empty.absurd({None{} == Some{o} : Maybe<&2, Source.Obs>},
                Shared.Maybe.no_none(Source.Term, u,
                  Equal.trans(Maybe<&2, Source.Term>, None{}, Source.Term.step(t, bk), Some{u},
                    Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(t, bk), None{}, ns), hst)))

# from a state whose measure is at most j, the machine reaches its goal in
# at most j + 1 steps
def Inner(+j: Nat, +s: Machine.St, +M: Nat, +bk: List<&2, Source.Def>, -o: Source.Obs, hs: {St.ok(s, bk) == True{} : Bool},
  hj: {Nat.is_le(St.mu(s), j) == True{} : Bool}, g: Goal<St.rb(s), o, M, bk>) ->
  {Machine.Machine.run(Nat.add(1n+j, M), s, bk) == Some{o} : Maybe<&2, Source.Obs>}:
  match j:
    case 0n:
      Inner.of(Machine.Machine.step(s, bk), 0n, St.rb(s), St.mu(s), M, bk, o, Step.ok(s, bk, hs), hj, g,
        s2 => ok2 => lt2 => g2 => Shared.Bool.absurd({Machine.Machine.run(M, s2, bk) == Some{o} : Maybe<&2, Source.Obs>}, lt2))
    case 1n+j2:
      Inner.of(Machine.Machine.step(s, bk), 1n+j2, St.rb(s), St.mu(s), M, bk, o, Step.ok(s, bk, hs), hj, g,
        s2 => ok2 => lt2 => g2 => Inner(j2, s2, M, bk, o, ok2, lt2, g2))

def Fuel.rest(v: Bool, ms: Maybe<&2, Source.Term>, go: Source.Term -> Nat) -> Nat:
  match v:
    case True{}:
      0n
    case False{}:
      match ms:
        case Some{u}:
          go(u)
        case None{}:
          0n

# the machine's fuel for n steps of the source from t: the weights of the
# terms of the run, and 2 for each term
def Fuel.of(n: Nat, +t: Source.Term, +bk: List<&2, Source.Def>) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+m:
      2n+Nat.add(Term.w(t), Fuel.rest(Source.Term.is_value(t, False{}, bk), Source.Term.step(t, bk), u => Fuel.of(m, u, bk)))

def Keeps.inner(+t: Source.Term, +s: Machine.St, +M: Nat, +bk: List<&2, Source.Def>, -o: Source.Obs,
  +hs: {St.ok(s, bk) == True{} : Bool}, +eq: {St.rb(s) == t : Source.Term}, g: Goal<t, o, M, bk>) ->
  {Machine.Machine.run(Nat.add(2n+Term.w(t), M), s, bk) == Some{o} : Maybe<&2, Source.Obs>}:
  Inner(1n+Term.w(t), s, M, bk, o, hs,
    Eq.rw(Source.Term, St.rb(s), t, eq, z => {Nat.is_le(St.mu(s), 1n+Term.w(z)) == True{} : Bool}, St.bound(s, bk, hs)),
    Eq.rw(Source.Term, t, St.rb(s), Equal.sym(Source.Term, St.rb(s), t, eq), z => Goal<z, o, M, bk>, g))

def Keeps.next(ms: Maybe<&2, Source.Term>, +t: Source.Term, +m: Nat, +bk: List<&2, Source.Def>, -o: Source.Obs,
  hc: {Source.Term.is_value(t, False{}, bk) == False{} : Bool}, hms: {Source.Term.step(t, bk) == ms : Maybe<&2, Source.Term>},
  h: {Source.Maybe.observe(Source.Term.run.next(ms, t, z => Source.Term.run(m, z, bk))) == Some{o} : Maybe<&2, Source.Obs>},
  +N: Nat, +s: Machine.St, +hs: {St.ok(s, bk) == True{} : Bool}, +eq: {St.rb(s) == t : Source.Term},
  rec: @u: Source.Term -> {Source.Maybe.observe(Source.Term.run(m, u, bk)) == Some{o} : Maybe<&2, Source.Obs>} ->
    @s2: Machine.St -> {St.ok(s2, bk) == True{} : Bool} -> {St.rb(s2) == u : Source.Term} ->
    {Machine.Machine.run(Nat.add(Fuel.of(m, u, bk), N), s2, bk) == Some{o} : Maybe<&2, Source.Obs>}) ->
  {Machine.Machine.run(Nat.add(2n+Nat.add(Term.w(t), Fuel.rest(False{}, ms, u => Fuel.of(m, u, bk))), N), s, bk) == Some{o} : Maybe<&2, Source.Obs>}:
  match ms:
    case Some{+u}:
      Eq.rw(Nat, Nat.add(Term.w(t), Nat.add(Fuel.of(m, u, bk), N)), Nat.add(Nat.add(Term.w(t), Fuel.of(m, u, bk)), N),
        Equal.sym(Nat, Nat.add(Nat.add(Term.w(t), Fuel.of(m, u, bk)), N), Nat.add(Term.w(t), Nat.add(Fuel.of(m, u, bk), N)),
          Nat.add_assoc(Term.w(t), Fuel.of(m, u, bk), N)),
        z => {Machine.Machine.run(2n+z, s, bk) == Some{o} : Maybe<&2, Source.Obs>},
        Keeps.inner(t, s, Nat.add(Fuel.of(m, u, bk), N), bk, o, hs, eq,
          Goal.step{u, hms, s2 => ok2 => eq2 => rec(u, h, s2, ok2, eq2)}))
    case None{}:
      Empty.absurd({Machine.Machine.run(Nat.add(2n+Nat.add(Term.w(t), 0n), N), s, bk) == Some{o} : Maybe<&2, Source.Obs>},
        Bool.true_false(Equal.trans(Bool, True{}, Source.Term.is_value(t, False{}, bk), False{},
          Equal.sym(Bool, Source.Term.is_value(t, False{}, bk), True{}, Obs.value(t, bk, o, h)), hc)))

def Keeps.of(c: Bool, +t: Source.Term, +m: Nat, +bk: List<&2, Source.Def>, -o: Source.Obs,
  hc: {Source.Term.is_value(t, False{}, bk) == c : Bool},
  h: {Source.Maybe.observe(Source.Term.run.of(c, t, z => Source.Term.step(t, bk), z => Source.Term.run(m, z, bk))) == Some{o} : Maybe<&2, Source.Obs>},
  +N: Nat, +s: Machine.St, +hs: {St.ok(s, bk) == True{} : Bool}, +eq: {St.rb(s) == t : Source.Term},
  rec: @u: Source.Term -> {Source.Maybe.observe(Source.Term.run(m, u, bk)) == Some{o} : Maybe<&2, Source.Obs>} ->
    @s2: Machine.St -> {St.ok(s2, bk) == True{} : Bool} -> {St.rb(s2) == u : Source.Term} ->
    {Machine.Machine.run(Nat.add(Fuel.of(m, u, bk), N), s2, bk) == Some{o} : Maybe<&2, Source.Obs>}) ->
  {Machine.Machine.run(Nat.add(2n+Nat.add(Term.w(t), Fuel.rest(c, Source.Term.step(t, bk), u => Fuel.of(m, u, bk))), N), s, bk) == Some{o} : Maybe<&2, Source.Obs>}:
  match c:
    case True{}:
      Eq.rw(Nat, Term.w(t), Nat.add(Term.w(t), 0n), Equal.sym(Nat, Nat.add(Term.w(t), 0n), Term.w(t), Nat.add_zero(Term.w(t))),
        z => {Machine.Machine.run(Nat.add(2n+z, N), s, bk) == Some{o} : Maybe<&2, Source.Obs>},
        Keeps.inner(t, s, N, bk, o, hs, eq, Goal.val{hc, h}))
    case False{}:
      Keeps.next(Source.Term.step(t, bk), t, m, bk, o, hc, {==}, h, N, s, hs, eq, rec)

# a result of n steps of the source from t is a result of the machine from each
# state of t, with Fuel.of(n, t) steps
def Keeps.go(+n: Nat, +t: Source.Term, +bk: List<&2, Source.Def>, -o: Source.Obs,
  h: {Source.Maybe.observe(Source.Term.run(n, t, bk)) == Some{o} : Maybe<&2, Source.Obs>},
  +N: Nat, +s: Machine.St, +hs: {St.ok(s, bk) == True{} : Bool}, +eq: {St.rb(s) == t : Source.Term}) ->
  {Machine.Machine.run(Nat.add(Fuel.of(n, t, bk), N), s, bk) == Some{o} : Maybe<&2, Source.Obs>}:
  match n:
    case 0n:
      Empty.absurd({Machine.Machine.run(N, s, bk) == Some{o} : Maybe<&2, Source.Obs>}, Shared.Maybe.no_none(Source.Obs, o, h))
    case 1n+m:
      Keeps.of(Source.Term.is_value(t, False{}, bk), t, m, bk, o, {==}, h, N, s, hs, eq,
        u => hu => s2 => hs2 => eq2 => Keeps.go(m, u, bk, o, hu, N, s2, hs2, eq2))

# Adds none
# =========

def Adds.step(c: Bool, +t: Source.Term, +m: Nat, +bk: List<&2, Source.Def>, -r: Source.Term,
  hc: {Source.Term.is_value(t, False{}, bk) == c : Bool}, st: {Source.Term.step(t, bk) == Some{r} : Maybe<&2, Source.Term>}) ->
  {Source.Term.run.of(c, t, z => Source.Term.step(t, bk), z => Source.Term.run(1n+m, z, bk)) == Source.Term.run(1n+m, r, bk) : Maybe<&2, Source.Term>}:
  match c:
    case True{}:
      Empty.absurd({Some{t} == Source.Term.run(1n+m, r, bk) : Maybe<&2, Source.Term>},
        Shared.Maybe.no_none(Source.Term, r,
          Equal.trans(Maybe<&2, Source.Term>, None{}, Source.Term.step(t, bk), Some{r},
            Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(t, bk), None{}, Vals.step(t, False{}, bk, hc)), st)))
    case False{}:
      Eq.rw(Maybe<&2, Source.Term>, Some{r}, Source.Term.step(t, bk), Equal.sym(Maybe<&2, Source.Term>, Source.Term.step(t, bk), Some{r}, st),
        z => {Source.Term.run.next(z, t, a => Source.Term.run(1n+m, a, bk)) == Source.Term.run(1n+m, r, bk) : Maybe<&2, Source.Term>}, {==})

def Adds.done(c: Bool, +t: Source.Term, -m: Nat, +bk: List<&2, Source.Def>, -o: Source.Obs,
  hc: {Source.Term.is_value(t, False{}, bk) == c : Bool}, hv: {Source.Term.is_value(t, False{}, bk) == True{} : Bool},
  ho: {Source.Term.observe(t) == Some{o} : Maybe<&2, Source.Obs>}) ->
  {Source.Maybe.observe(Source.Term.run.of(c, t, z => Source.Term.step(t, bk), z => Source.Term.run(1n+m, z, bk))) == Some{o} : Maybe<&2, Source.Obs>}:
  match c:
    case True{}:
      ho
    case False{}:
      Empty.absurd({Source.Maybe.observe(Source.Term.run.next(Source.Term.step(t, bk), t, z => Source.Term.run(1n+m, z, bk))) == Some{o} : Maybe<&2, Source.Obs>},
        Bool.true_false(Equal.trans(Bool, True{}, Source.Term.is_value(t, False{}, bk), False{},
          Equal.sym(Bool, Source.Term.is_value(t, False{}, bk), True{}, hv), hc)))

def Adds.of(mv: Machine.Move, +m: Nat, +t: Source.Term, -mu: Nat, +bk: List<&2, Source.Def>, -o: Source.Obs,
  mvd: Moved(mv, t, mu, bk), h: {Machine.Run.next(mv, s2 => Machine.Machine.run(m, s2, bk)) == Some{o} : Maybe<&2, Source.Obs>},
  rec: @s2: Machine.St -> {St.ok(s2, bk) == True{} : Bool} -> {Machine.Machine.run(m, s2, bk) == Some{o} : Maybe<&2, Source.Obs>} ->
    {Source.Maybe.observe(Source.Term.run(1n+m, St.rb(s2), bk)) == Some{o} : Maybe<&2, Source.Obs>}) ->
  {Source.Maybe.observe(Source.Term.run(2n+m, t, bk)) == Some{o} : Maybe<&2, Source.Obs>}:
  match mv:
    case Machine.Move.go{+s2}:
      match mvd:
        case (ok2, r):
          match r:
            case Inl{(eq2, lt2)}:
              Obs.mono(t, 1n+m, bk, o,
                Eq.rw(Source.Term, St.rb(s2), t, eq2, z => {Source.Maybe.observe(Source.Term.run(1n+m, z, bk)) == Some{o} : Maybe<&2, Source.Obs>},
                  rec(s2, ok2, h)))
            case Inr{st}:
              Eq.rw(Maybe<&2, Source.Term>, Source.Term.run(1n+m, St.rb(s2), bk), Source.Term.run(2n+m, t, bk),
                Equal.sym(Maybe<&2, Source.Term>, Source.Term.run(2n+m, t, bk), Source.Term.run(1n+m, St.rb(s2), bk),
                  Adds.step(Source.Term.is_value(t, False{}, bk), t, m, bk, St.rb(s2), {==}, st)),
                z => {Source.Maybe.observe(z) == Some{o} : Maybe<&2, Source.Obs>}, rec(s2, ok2, h))
    case Machine.Move.done{+v}:
      match mvd:
        case (+okv, +eqv):
          Adds.done(Source.Term.is_value(t, False{}, bk), t, m, bk, o, {==},
            Eq.rw(Source.Term, Val.rb(v), t, eqv, z => {Source.Term.is_value(z, False{}, bk) == True{} : Bool}, Val.value(v, bk, okv)),
            Equal.trans(Maybe<&2, Source.Obs>, Source.Term.observe(t), Machine.Val.observe(v), Some{o},
              Equal.trans(Maybe<&2, Source.Obs>, Source.Term.observe(t), Source.Term.observe(Val.rb(v)), Machine.Val.observe(v),
                Equal.cong(Source.Term, Maybe<&2, Source.Obs>, z => Source.Term.observe(z), t, Val.rb(v), Equal.sym(Source.Term, Val.rb(v), t, eqv)),
                Equal.sym(Maybe<&2, Source.Obs>, Machine.Val.observe(v), Source.Term.observe(Val.rb(v)), Obs.eq(v, bk, okv))), h))
    case Machine.Move.stuck{}:
      Empty.absurd({Source.Maybe.observe(Source.Term.run(2n+m, t, bk)) == Some{o} : Maybe<&2, Source.Obs>}, Shared.Maybe.no_none(Source.Obs, o, h))

# a result of the machine in n steps from s is a result of the source in n + 1
# steps from the term of s
def Adds.go(+n: Nat, +s: Machine.St, +bk: List<&2, Source.Def>, -o: Source.Obs, +hs: {St.ok(s, bk) == True{} : Bool},
  h: {Machine.Machine.run(n, s, bk) == Some{o} : Maybe<&2, Source.Obs>}) ->
  {Source.Maybe.observe(Source.Term.run(1n+n, St.rb(s), bk)) == Some{o} : Maybe<&2, Source.Obs>}:
  match n:
    case 0n:
      Empty.absurd({Source.Maybe.observe(Source.Term.run(1n, St.rb(s), bk)) == Some{o} : Maybe<&2, Source.Obs>},
        Shared.Maybe.no_none(Source.Obs, o, h))
    case 1n+m:
      Adds.of(Machine.Machine.step(s, bk), m, St.rb(s), St.mu(s), bk, o, Step.ok(s, bk, hs), h,
        s2 => hs2 => h2 => Adds.go(m, s2, bk, o, hs2, h2))

# Laws
# ====

def Obs.is_eq_self(a: Source.Obs) -> {Source.Obs.is_eq(a, a) == True{} : Bool}:
  match a:
    case Source.Obs.lab{k}:
      SP.Name.is_eq_self(k)
    case Source.Obs.rfl{}:
      {==}
    case Source.Obs.tup{+a1, +a2}:
      %Equal.sym(Bool, Source.Obs.is_eq(a1, a1), True{}, Obs.is_eq_self(a1)) :
        {Bool.and(_, Source.Obs.is_eq(a2, a2)) == True{} : Bool}
      Obs.is_eq_self(a2)
    case Source.Obs.tup0{a2}:
      Obs.is_eq_self(a2)

def Spec.fuel_m(bk, k, n):
  Fuel.of(n, Source.Term.Ref{k}, bk)

def Spec.fuel_s(bk, k, n):
  1n+n

def Keeps.law(mo: Maybe<&2, Source.Obs>, +bk: List<&2, Source.Def>, +k: List<&2, Nat>, +n: Nat,
  hm: {Source.Maybe.observe(Source.Term.run(n, Source.Term.Ref{k}, bk)) == mo : Maybe<&2, Source.Obs>}) ->
  {Source.Obs.is_kept(mo, Machine.Machine.start(Fuel.of(n, Source.Term.Ref{k}, bk), bk, k)) == True{} : Bool}:
  match mo:
    case None{}:
      {==}
    case Some{+o}:
      Eq.rw(Maybe<&2, Source.Obs>, Some{o}, Machine.Machine.start(Fuel.of(n, Source.Term.Ref{k}, bk), bk, k),
        Equal.sym(Maybe<&2, Source.Obs>, Machine.Machine.start(Fuel.of(n, Source.Term.Ref{k}, bk), bk, k), Some{o},
          Eq.rw(Nat, Nat.add(Fuel.of(n, Source.Term.Ref{k}, bk), 0n), Fuel.of(n, Source.Term.Ref{k}, bk),
            Nat.add_zero(Fuel.of(n, Source.Term.Ref{k}, bk)),
            z => {Machine.Machine.run(z, Machine.St.eval{Source.Term.Ref{k}, Machine.Val.nil{}, []}, bk) == Some{o} : Maybe<&2, Source.Obs>},
            Keeps.go(n, Source.Term.Ref{k}, bk, o, hm, 0n, Machine.St.eval{Source.Term.Ref{k}, Machine.Val.nil{}, []}, {==}, {==}))),
        z => {Source.Obs.is_kept(Some{o}, z) == True{} : Bool}, Obs.is_eq_self(o))

def Keeps.law.of(+bk: List<&2, Source.Def>, +k: List<&2, Nat>, +n: Nat) ->
  {Source.Obs.is_kept(Source.Maybe.observe(Source.Term.run(n, Source.Term.Ref{k}, bk)),
    Machine.Machine.start(Fuel.of(n, Source.Term.Ref{k}, bk), bk, k)) == True{} : Bool}:
  Keeps.law(Source.Maybe.observe(Source.Term.run(n, Source.Term.Ref{k}, bk)), bk, k, n, {==})

def Spec.keeps(bk, k, n):
  Keeps.law.of(bk, k, n)

def Adds.law(mo: Maybe<&2, Source.Obs>, +bk: List<&2, Source.Def>, +k: List<&2, Nat>, +n: Nat,
  hm: {Machine.Machine.start(n, bk, k) == mo : Maybe<&2, Source.Obs>}) ->
  {Source.Obs.is_kept(mo, Source.Maybe.observe(Source.Term.run(1n+n, Source.Term.Ref{k}, bk))) == True{} : Bool}:
  match mo:
    case None{}:
      {==}
    case Some{+o}:
      Eq.rw(Maybe<&2, Source.Obs>, Some{o}, Source.Maybe.observe(Source.Term.run(1n+n, Source.Term.Ref{k}, bk)),
        Equal.sym(Maybe<&2, Source.Obs>, Source.Maybe.observe(Source.Term.run(1n+n, Source.Term.Ref{k}, bk)), Some{o},
          Adds.go(n, Machine.St.eval{Source.Term.Ref{k}, Machine.Val.nil{}, []}, bk, o, {==}, hm)),
        z => {Source.Obs.is_kept(Some{o}, z) == True{} : Bool}, Obs.is_eq_self(o))

def Adds.law.of(+bk: List<&2, Source.Def>, +k: List<&2, Nat>, +n: Nat) ->
  {Source.Obs.is_kept(Machine.Machine.start(n, bk, k), Source.Maybe.observe(Source.Term.run(1n+n, Source.Term.Ref{k}, bk))) == True{} : Bool}:
  Adds.law(Machine.Machine.start(n, bk, k), bk, k, n, {==})

def Spec.adds_none(bk, k, n):
  Adds.law.of(bk, k, n)
