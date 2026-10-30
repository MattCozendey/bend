import Base

# F
# =
#
# A small first-order language whose values are trees. The machine (step 3) is
# an F program (step 4), and the run time in Imp runs F (step 5).
#
# A value is z, or a node: a tag and two children. The number k is the node
# {k, z, z}. Code is in A-normal form: an instruction reads atoms (a variable,
# a number or z) and puts its results at the front of the environment, so the
# variable 0 is the newest one. A call starts its function with its arguments
# as the environment, the first argument at 0.
#
# The meaning is an abstract machine: the code, its environment, and a stack
# of frames, one for each call that waits for its result.

# Types
# =====

type V is Data:
  V.z{}
  V.n{t: Nat, a: V, b: V}

# an atom: the variable i, the number t, or z
type A is Data:
  A.var{i: Nat}
  A.num{t: Nat}
  A.z{}

# an instruction, with the code k after it
# - ret a: the result of the function is a
# - mk t a b: a new node {t, a, b}
# - case a t y n: when a is a node with the tag t, its children (a, then b)
#   and y; else n
# - same a b y n: y when the nodes a and b have the same tag, else n
# - dec a z s: z when the tag of a is 0; else its tag minus 1, as a number,
#   and s
# - inc a: its tag plus 1, as a number
# - call f xs: the result of the function f on xs
# - jump f xs: the result of the function f on xs is the result
# - stop: no result
type C is Data:
  C.ret{a: A}
  C.mk{t: Nat, a: A, b: A, k: C}
  C.case{a: A, t: Nat, y: C, n: C}
  C.same{a: A, b: A, y: C, n: C}
  C.dec{a: A, z: C, s: C}
  C.inc{a: A, k: C}
  C.call{f: Nat, xs: List<&2, A>, k: C}
  C.jump{f: Nat, xs: List<&2, A>}
  C.stop{}

# a call that waits for its result: the code after it, and its environment
type Fr is Data:
  Fr{k: C, env: List<&2, V>}

# a state: run c in env, or return v; then the frames ks, the innermost first
type S is Data:
  S.run{c: C, env: List<&2, V>, ks: List<&2, Fr>}
  S.ret{v: V, ks: List<&2, Fr>}

# a step's result: the next state, the end with a value, or stuck
type Step is Data:
  Step.go{s: S}
  Step.halt{v: V}
  Step.stuck{}

# Steps
# =====

def V.num(t: Nat) -> V:
  V.n{t, V.z{}, V.z{}}

def A.get(a: A, env: List<&2, V>) -> Maybe<&2, V>:
  match a:
    case A.var{i}:
      List.get(&2, V, env, i)
    case A.num{t}:
      Some{V.num(t)}
    case A.z{}:
      Some{V.z{}}

def As.get.con(m: Maybe<&2, V>, r: Maybe<&2, List<&2, V>>) -> Maybe<&2, List<&2, V>>:
  match m r:
    case Some{x} Some{xs}:
      Some{Con{x, xs}}
    case _ _:
      None{}

def As.get(xs: List<&2, A>, +env: List<&2, V>) -> Maybe<&2, List<&2, V>>:
  match xs:
    case Nil{}:
      Some{[]}
    case Con{a, rest}:
      As.get.con(A.get(a, env), As.get(rest, env))

def Step.ret(m: Maybe<&2, V>, ks: List<&2, Fr>) -> Step:
  match m:
    case Some{v}:
      Step.go{S.ret{v, ks}}
    case None{}:
      Step.stuck{}

def Step.mk(t: Nat, ma: Maybe<&2, V>, mb: Maybe<&2, V>, k: C, env: List<&2, V>, ks: List<&2, Fr>) -> Step:
  match ma mb:
    case Some{a} Some{b}:
      Step.go{S.run{k, Con{V.n{t, a, b}, env}, ks}}
    case _ _:
      Step.stuck{}

def Step.case(m: Maybe<&2, V>, t: Nat, y: C, n: C, +env: List<&2, V>, +ks: List<&2, Fr>) -> Step:
  match m:
    case Some{V.n{u, a, b}}:
      Bool.pick(Step, Nat.is_eq(u, t), Step.go{S.run{y, Con{b, Con{a, env}}, ks}},
        Step.go{S.run{n, env, ks}})
    case Some{V.z{}}:
      Step.go{S.run{n, env, ks}}
    case None{}:
      Step.stuck{}

def Step.same(ma: Maybe<&2, V>, mb: Maybe<&2, V>, y: C, n: C, +env: List<&2, V>, +ks: List<&2, Fr>) ->
  Step:
  match ma mb:
    case Some{V.n{u, a, b}} Some{V.n{w, c, d}}:
      Bool.pick(Step, Nat.is_eq(u, w), Step.go{S.run{y, env, ks}}, Step.go{S.run{n, env, ks}})
    case _ _:
      Step.stuck{}

def Step.dec(m: Maybe<&2, V>, z: C, s: C, env: List<&2, V>, ks: List<&2, Fr>) -> Step:
  match m:
    case Some{V.n{0n, a, b}}:
      Step.go{S.run{z, env, ks}}
    case Some{V.n{1n+u, a, b}}:
      Step.go{S.run{s, Con{V.num(u), env}, ks}}
    case _:
      Step.stuck{}

def Step.inc(m: Maybe<&2, V>, k: C, env: List<&2, V>, ks: List<&2, Fr>) -> Step:
  match m:
    case Some{V.n{u, a, b}}:
      Step.go{S.run{k, Con{V.num(1n+u), env}, ks}}
    case _:
      Step.stuck{}

def Step.call(mc: Maybe<&2, C>, mxs: Maybe<&2, List<&2, V>>, ks: List<&2, Fr>) -> Step:
  match mc mxs:
    case Some{c} Some{xs}:
      Step.go{S.run{c, xs, ks}}
    case _ _:
      Step.stuck{}

# the step from S.run c env ks
def C.step(c: C, +env: List<&2, V>, +ks: List<&2, Fr>, +prog: List<&2, C>) -> Step:
  match c:
    case C.ret{a}:
      Step.ret(A.get(a, env), ks)
    case C.mk{t, a, b, k}:
      Step.mk(t, A.get(a, env), A.get(b, env), k, env, ks)
    case C.case{a, t, y, n}:
      Step.case(A.get(a, env), t, y, n, env, ks)
    case C.same{a, b, y, n}:
      Step.same(A.get(a, env), A.get(b, env), y, n, env, ks)
    case C.dec{a, z, s}:
      Step.dec(A.get(a, env), z, s, env, ks)
    case C.inc{a, k}:
      Step.inc(A.get(a, env), k, env, ks)
    case C.call{f, xs, k}:
      Step.call(List.get(&2, C, prog, f), As.get(xs, env), Con{Fr{k, env}, ks})
    case C.jump{f, xs}:
      Step.call(List.get(&2, C, prog, f), As.get(xs, env), ks)
    case C.stop{}:
      Step.stuck{}

# one step of s, in the program prog: the code of each function
def F.step(+prog: List<&2, C>, s: S) -> Step:
  match s:
    case S.run{c, env, ks}:
      C.step(c, env, ks, prog)
    case S.ret{v, Nil{}}:
      Step.halt{v}
    case S.ret{v, Con{Fr{k, env}, ks}}:
      Step.go{S.run{k, Con{v, env}, ks}}

# Runs
# ====

def Step.next(+prog: List<&2, C>, x: Step) -> Step:
  match x:
    case Step.go{s}:
      F.step(prog, s)
    case _:
      x

# x after n steps; an end stays
def F.iter(n: Nat, +prog: List<&2, C>, x: Step) -> Step:
  match n:
    case 0n:
      x
    case 1n+m:
      F.iter(m, prog, Step.next(prog, x))

def Step.out(x: Step) -> Maybe<&2, V>:
  match x:
    case Step.halt{v}:
      Some{v}
    case _:
      None{}

# the end of the run from s, after at most n steps, or none: when it is stuck
# or when n is not enough
def F.run(n: Nat, prog: List<&2, C>, s: S) -> Maybe<&2, V>:
  Step.out(F.iter(n, prog, Step.go{s}))

# s reaches t in some number of steps
def Reach(+prog: List<&2, C>, +s: Step, +t: Step) -> Type:
  Sigma<&1, &1, Nat, n => {F.iter(n, prog, s) == t : Step}>

# s reaches t in at least one step
def Reach1(+prog: List<&2, C>, +s: Step, +t: Step) -> Type:
  Sigma<&1, &1, Nat, n => {F.iter(1n+n, prog, s) == t : Step}>
