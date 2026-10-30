import Base
import ./impl.bend as Fun
import ../shared/impl.bend as Shared

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

# s reaches the state after c steps
def Reach.steps(+c: Nat, +prog: List<&2, Fun.C>, +s: Fun.Step) -> Fun.Reach(prog, s, Fun.F.iter(c, prog, s)):
  (c, {==})

def Reach.trans(+prog: List<&2, Fun.C>, +s: Fun.Step, +t: Fun.Step, +u: Fun.Step, r1: Fun.Reach(prog, s, t),
  r2: Fun.Reach(prog, t, u)) -> Fun.Reach(prog, s, u):
  (+n1, +e1) = r1
  (+n2, +e2) = r2
  (Nat.add(n1, n2),
    Equal.trans(Fun.Step, Fun.F.iter(Nat.add(n1, n2), prog, s), Fun.F.iter(n2, prog, Fun.F.iter(n1, prog, s)), u,
      Iter.add(n1, n2, prog, s),
      Equal.trans(Fun.Step, Fun.F.iter(n2, prog, Fun.F.iter(n1, prog, s)), Fun.F.iter(n2, prog, t), u,
        Equal.cong(Fun.Step, Fun.Step, x => Fun.F.iter(n2, prog, x), Fun.F.iter(n1, prog, s), t, e1), e2)))

# r, with an end that equals its end
def Reach.end(+prog: List<&2, Fun.C>, +s: Fun.Step, -t1: Fun.Step, -t2: Fun.Step, e: {t1 == t2 : Fun.Step},
  r: Fun.Reach(prog, s, t1)) -> Fun.Reach(prog, s, t2):
  %e : Fun.Reach(prog, s, _)
  r

# r, with a start that equals its start
def Reach.start(+prog: List<&2, Fun.C>, -s1: Fun.Step, -s2: Fun.Step, +t: Fun.Step, e: {s1 == s2 : Fun.Step},
  r: Fun.Reach(prog, s1, t)) -> Fun.Reach(prog, s2, t):
  %e : Fun.Reach(prog, _, t)
  r

def Reach1.of(+prog: List<&2, Fun.C>, +s: Fun.Step, +t: Fun.Step, r: Fun.Reach(prog, Fun.F.iter(1n, prog, s), t)) ->
  Fun.Reach1(prog, s, t):
  (+n, +e) = r
  (n, e)

def Reach1.reach(+prog: List<&2, Fun.C>, +s: Fun.Step, +t: Fun.Step, r: Fun.Reach1(prog, s, t)) -> Fun.Reach(prog, s, t):
  (+n, +e) = r
  (1n+n, e)

def Reach1.then(+prog: List<&2, Fun.C>, +s: Fun.Step, +t: Fun.Step, +u: Fun.Step, r: Fun.Reach1(prog, s, t),
  q: Fun.Reach(prog, t, u)) -> Fun.Reach1(prog, s, u):
  (+n, +e) = r
  (+m, +f) = q
  (Nat.add(n, m),
    Equal.trans(Fun.Step, Fun.F.iter(Nat.add(1n+n, m), prog, s), Fun.F.iter(m, prog, Fun.F.iter(1n+n, prog, s)), u,
      Iter.add(1n+n, m, prog, s),
      Equal.trans(Fun.Step, Fun.F.iter(m, prog, Fun.F.iter(1n+n, prog, s)), Fun.F.iter(m, prog, t), u,
        Equal.cong(Fun.Step, Fun.Step, x => Fun.F.iter(m, prog, x), Fun.F.iter(1n+n, prog, s), t, e), f)))

# Ends
# ====

def Step.is_go(x: Fun.Step) -> Bool:
  match x:
    case Fun.Step.go{s}:
      True{}
    case _:
      False{}

def Step.is_halt(x: Fun.Step) -> Bool:
  match x:
    case Fun.Step.halt{v}:
      True{}
    case _:
      False{}

def Step.value(x: Fun.Step, d: Fun.V) -> Fun.V:
  match x:
    case Fun.Step.halt{v}:
      v
    case _:
      d

# the ends of two runs from x are the same
def Iter.det(n: Nat, N: Nat, +prog: List<&2, Fun.C>, +x: Fun.Step, +a: Fun.V, +b: Fun.V,
  +ha: {Fun.F.iter(n, prog, x) == Fun.Step.halt{a} : Fun.Step}, +hb: {Fun.F.iter(N, prog, x) == Fun.Step.halt{b} : Fun.Step}) ->
  {a == b : Fun.V}:
  match n:
    case 0n:
      Equal.cong(Fun.Step, Fun.V, y => Step.value(y, a), Fun.Step.halt{a}, Fun.Step.halt{b},
        Equal.trans(Fun.Step, Fun.Step.halt{a}, Fun.F.iter(N, prog, Fun.Step.halt{a}), Fun.Step.halt{b},
          Equal.sym(Fun.Step, Fun.F.iter(N, prog, Fun.Step.halt{a}), Fun.Step.halt{a}, Iter.halt(N, prog, a)),
          Equal.trans(Fun.Step, Fun.F.iter(N, prog, Fun.Step.halt{a}), Fun.F.iter(N, prog, x), Fun.Step.halt{b},
            Equal.cong(Fun.Step, Fun.Step, y => Fun.F.iter(N, prog, y), Fun.Step.halt{a}, x,
              Equal.sym(Fun.Step, x, Fun.Step.halt{a}, ha)), hb)))
    case 1n+m:
      match N:
        case 0n:
          Equal.cong(Fun.Step, Fun.V, y => Step.value(y, a), Fun.Step.halt{a}, Fun.Step.halt{b},
            Equal.trans(Fun.Step, Fun.Step.halt{a}, Fun.F.iter(1n+m, prog, Fun.Step.halt{b}), Fun.Step.halt{b},
              Equal.trans(Fun.Step, Fun.Step.halt{a}, Fun.F.iter(1n+m, prog, x), Fun.F.iter(1n+m, prog, Fun.Step.halt{b}),
                Equal.sym(Fun.Step, Fun.F.iter(1n+m, prog, x), Fun.Step.halt{a}, ha),
                Equal.cong(Fun.Step, Fun.Step, y => Fun.F.iter(1n+m, prog, y), x, Fun.Step.halt{b}, hb)),
              Iter.halt(1n+m, prog, b)))
        case 1n+M:
          Iter.det(m, M, prog, Fun.Step.next(prog, x), a, b, ha, hb)

# a run that is stuck has no end
def Iter.stuck_end(n: Nat, N: Nat, +prog: List<&2, Fun.C>, +x: Fun.Step, +b: Fun.V,
  +hs: {Fun.F.iter(n, prog, x) == Fun.Step.stuck{} : Fun.Step}, +hb: {Fun.F.iter(N, prog, x) == Fun.Step.halt{b} : Fun.Step}) ->
  Empty:
  match n:
    case 0n:
      Shared.Bool.no(Equal.cong(Fun.Step, Bool, y => Step.is_halt(y), Fun.Step.stuck{}, Fun.Step.halt{b},
        Equal.trans(Fun.Step, Fun.Step.stuck{}, Fun.F.iter(N, prog, Fun.Step.stuck{}), Fun.Step.halt{b},
          Equal.sym(Fun.Step, Fun.F.iter(N, prog, Fun.Step.stuck{}), Fun.Step.stuck{}, Iter.stuck(N, prog)),
          Equal.trans(Fun.Step, Fun.F.iter(N, prog, Fun.Step.stuck{}), Fun.F.iter(N, prog, x), Fun.Step.halt{b},
            Equal.cong(Fun.Step, Fun.Step, y => Fun.F.iter(N, prog, y), Fun.Step.stuck{}, x,
              Equal.sym(Fun.Step, x, Fun.Step.stuck{}, hs)), hb))))
    case 1n+m:
      match N:
        case 0n:
          Shared.Bool.no(Equal.cong(Fun.Step, Bool, y => Step.is_halt(y), Fun.Step.stuck{}, Fun.Step.halt{b},
            Equal.trans(Fun.Step, Fun.Step.stuck{}, Fun.F.iter(1n+m, prog, Fun.Step.halt{b}), Fun.Step.halt{b},
              Equal.trans(Fun.Step, Fun.Step.stuck{}, Fun.F.iter(1n+m, prog, x), Fun.F.iter(1n+m, prog, Fun.Step.halt{b}),
                Equal.sym(Fun.Step, Fun.F.iter(1n+m, prog, x), Fun.Step.stuck{}, hs),
                Equal.cong(Fun.Step, Fun.Step, y => Fun.F.iter(1n+m, prog, y), x, Fun.Step.halt{b}, hb)),
              Iter.halt(1n+m, prog, b))))
        case 1n+M:
          Iter.stuck_end(m, M, prog, Fun.Step.next(prog, x), b, hs, hb)

def Reach.det(+prog: List<&2, Fun.C>, +x: Fun.Step, +a: Fun.V, +b: Fun.V, r: Fun.Reach(prog, x, Fun.Step.halt{a}), N: Nat,
  +hb: {Fun.F.iter(N, prog, x) == Fun.Step.halt{b} : Fun.Step}) -> {a == b : Fun.V}:
  (+n, +e) = r
  Iter.det(n, N, prog, x, a, b, e, hb)

def Reach.stuck_end(+prog: List<&2, Fun.C>, +x: Fun.Step, +b: Fun.V, r: Fun.Reach(prog, x, Fun.Step.stuck{}), N: Nat,
  +hb: {Fun.F.iter(N, prog, x) == Fun.Step.halt{b} : Fun.Step}) -> Empty:
  (+n, +e) = r
  Iter.stuck_end(n, N, prog, x, b, e, hb)

# from a run of N steps to the end w, after a state y that x reaches in at least one step: a run from y to w in
# fewer steps
def After(+prog: List<&2, Fun.C>, +N: Nat, +y: Fun.Step, +w: Fun.V) -> Type:
  Sigma<&1, &1, Nat, M => Pair({Fun.F.iter(M, prog, y) == Fun.Step.halt{w} : Fun.Step}, {Nat.is_le(1n+M, N) == True{} : Bool})>

def After.succ(+prog: List<&2, Fun.C>, +N: Nat, +y: Fun.Step, +w: Fun.V, a: After(prog, N, y, w)) ->
  After(prog, 1n+N, y, w):
  (+K, +p) = a
  (+hk, +lt) = p
  (K, (hk, Shared.Nat.is_le_succ(1n+K, N, lt)))

def Iter.after(N: Nat, n: Nat, +prog: List<&2, Fun.C>, +x: Fun.Step, +y: Fun.Step, +w: Fun.V,
  +e: {Fun.F.iter(1n+n, prog, x) == y : Fun.Step}, +hy: {Step.is_go(y) == True{} : Bool},
  +h: {Fun.F.iter(N, prog, x) == Fun.Step.halt{w} : Fun.Step}) -> After(prog, N, y, w):
  match N:
    case 0n:
      Shared.Bool.absurd(After(prog, 0n, y, w),
        Equal.trans(Bool, False{}, Step.is_go(y), True{},
          Equal.cong(Fun.Step, Bool, z => Step.is_go(z), Fun.Step.halt{w}, y,
            Equal.trans(Fun.Step, Fun.Step.halt{w}, Fun.F.iter(1n+n, prog, Fun.Step.halt{w}), y,
              Equal.sym(Fun.Step, Fun.F.iter(1n+n, prog, Fun.Step.halt{w}), Fun.Step.halt{w}, Iter.halt(1n+n, prog, w)),
              Equal.trans(Fun.Step, Fun.F.iter(1n+n, prog, Fun.Step.halt{w}), Fun.F.iter(1n+n, prog, x), y,
                Equal.cong(Fun.Step, Fun.Step, z => Fun.F.iter(1n+n, prog, z), Fun.Step.halt{w}, x,
                  Equal.sym(Fun.Step, x, Fun.Step.halt{w}, h)), e))),
          hy))
    case 1n++M:
      match n:
        case 0n:
          (M, (Equal.trans(Fun.Step, Fun.F.iter(M, prog, y), Fun.F.iter(M, prog, Fun.Step.next(prog, x)), Fun.Step.halt{w},
            Equal.cong(Fun.Step, Fun.Step, z => Fun.F.iter(M, prog, z), y, Fun.Step.next(prog, x),
              Equal.sym(Fun.Step, Fun.Step.next(prog, x), y, e)), h),
            Shared.Nat.is_le_refl(1n+M)))
        case 1n+m:
          After.succ(prog, M, y, w, Iter.after(M, m, prog, Fun.Step.next(prog, x), y, w, e, hy, h))


# Outputs
# =======

def Out.value(m: Maybe<&2, Fun.V>, d: Fun.V) -> Fun.V:
  match m:
    case Some{v}:
      v
    case None{}:
      d

# the end of a run that gives w
def Out.halt(x: Fun.Step, +w: Fun.V, h: {Fun.Step.out(x) == Some{w} : Maybe<&2, Fun.V>}) -> {x == Fun.Step.halt{w} : Fun.Step}:
  match x:
    case Fun.Step.go{s}:
      Empty.absurd({Fun.Step.go{s} == Fun.Step.halt{w} : Fun.Step}, Shared.Maybe.no_none(Fun.V, w, h))
    case Fun.Step.halt{v}:
      Equal.cong(Fun.V, Fun.Step, z => Fun.Step.halt{z}, v, w,
        Equal.cong(Maybe<&2, Fun.V>, Fun.V, m => Out.value(m, v), Some{v}, Some{w}, h))
    case Fun.Step.stuck{}:
      Empty.absurd({Fun.Step.stuck{} == Fun.Step.halt{w} : Fun.Step}, Shared.Maybe.no_none(Fun.V, w, h))
