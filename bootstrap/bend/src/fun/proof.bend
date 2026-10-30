import Base
import ./impl.bend as Fun

# F lemmas
# ========
#
# Facts about runs of F that the proofs of later steps use.

# a + b steps are a steps, then b steps
def Iter.add(a: Nat, b: Nat, +prog: List<&2, Fun.C>, x: Fun.Step) ->
  {Fun.F.iter(Nat.add(a, b), prog, x) == Fun.F.iter(b, prog, Fun.F.iter(a, prog, x)) : Fun.Step}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Iter.add(p, b, prog, Fun.Step.next(prog, x))

# an end stays
def Iter.halt(n: Nat, +prog: List<&2, Fun.C>, +v: Fun.V) ->
  {Fun.F.iter(n, prog, Fun.Step.halt{v}) == Fun.Step.halt{v} : Fun.Step}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      Iter.halt(m, prog, v)

def Iter.stuck(n: Nat, +prog: List<&2, Fun.C>) ->
  {Fun.F.iter(n, prog, Fun.Step.stuck{}) == Fun.Step.stuck{} : Fun.Step}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      Iter.stuck(m, prog)

# Reaching
# ========

# s reaches t in some number of steps
def Reach(+prog: List<&2, Fun.C>, +s: Fun.Step, +t: Fun.Step) -> Type:
  Sigma<&1, &1, Nat, n => {Fun.F.iter(n, prog, s) == t : Fun.Step}>

# s reaches the state after c steps
def Reach.steps(+c: Nat, +prog: List<&2, Fun.C>, +s: Fun.Step) -> Reach(prog, s, Fun.F.iter(c, prog, s)):
  (c, {==})

def Reach.trans(+prog: List<&2, Fun.C>, +s: Fun.Step, +t: Fun.Step, +u: Fun.Step, r1: Reach(prog, s, t),
  r2: Reach(prog, t, u)) -> Reach(prog, s, u):
  (+n1, +e1) = r1
  (+n2, +e2) = r2
  (Nat.add(n1, n2),
    Equal.trans(Fun.Step, Fun.F.iter(Nat.add(n1, n2), prog, s), Fun.F.iter(n2, prog, Fun.F.iter(n1, prog, s)), u,
      Iter.add(n1, n2, prog, s),
      Equal.trans(Fun.Step, Fun.F.iter(n2, prog, Fun.F.iter(n1, prog, s)), Fun.F.iter(n2, prog, t), u,
        Equal.cong(Fun.Step, Fun.Step, x => Fun.F.iter(n2, prog, x), Fun.F.iter(n1, prog, s), t, e1), e2)))
