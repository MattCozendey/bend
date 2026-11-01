# compiler: steps of the model's calls
# ====================================
#
# The simulation of proof_sim.bend runs the model's functions by PH.H.steps(n,
# st), n steps of a running function (proof_halt.bend), and composes runs by
# steps.then: n steps then m steps are n + m steps. A run that ends after n
# steps gives the call's end, with any fuel F >= n (run.call): the results,
# the memory, and some count of steps j <= n.

import Base
import ./impl.bend as C
import ./proof_need.bend as N
import ./proof_halt.bend as PH

# Kit
# ---

# a pair of two Data types, itself Data
def P2(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

# a Nat with a property, as Data
def EX(-B: Nat -> Data) -> Data:
  Sigma<&2, &2, Nat, j => B(j)>

# a step that is done
def is.done(st: C.Wasm.Step) -> Data:
  match st:
    case C.Wasm.Step.done{_, _}:
      Unit
    case C.Wasm.Step.next{_, _}:
      Empty
    case C.Wasm.Step.trap{_}:
      Empty

def done.rs(st: C.Wasm.Step) -> List<&2, U32>:
  match st:
    case C.Wasm.Step.done{rs, _}:
      rs
    case _:
      []

def done.mem(st: C.Wasm.Step) -> C.Wasm.Memory:
  match st:
    case C.Wasm.Step.done{_, m}:
      m
    case _:
      C.Wasm.Memory{0, 0, C.Wasm.Bytes.zero{}}

# a running frame is not done
def next.not_done(-fr: C.Wasm.Frame, -m: C.Wasm.Memory, -rs: List<&2, U32>, -m2: C.Wasm.Memory,
  e: {C.Wasm.Step.next{fr, m} == C.Wasm.Step.done{rs, m2} : C.Wasm.Step}) -> Empty:
  %Equal.sym(C.Wasm.Step, C.Wasm.Step.next{fr, m}, C.Wasm.Step.done{rs, m2}, e) : is.done(_)
  Unit{}

# a trap is not done
def trap.not_done(-m: C.Wasm.Memory, -rs: List<&2, U32>, -m2: C.Wasm.Memory,
  e: {C.Wasm.Step.trap{m} == C.Wasm.Step.done{rs, m2} : C.Wasm.Step}) -> Empty:
  %Equal.sym(C.Wasm.Step, C.Wasm.Step.trap{m}, C.Wasm.Step.done{rs, m2}, e) : is.done(_)
  Unit{}

# Steps
# -----

# a function that ended stays ended
def steps.done(n: Nat, -rs: List<&2, U32>, -m: C.Wasm.Memory) ->
  {PH.H.steps(n, C.Wasm.Step.done{rs, m}) == C.Wasm.Step.done{rs, m} : C.Wasm.Step}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def steps.trap(n: Nat, -m: C.Wasm.Memory) -> {PH.H.steps(n, C.Wasm.Step.trap{m}) == C.Wasm.Step.trap{m} : C.Wasm.Step}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a + b steps are a steps, then b steps
def steps.add(a: Nat, +b: Nat, +st: C.Wasm.Step) ->
  {PH.H.steps(Nat.add(a, b), st) == PH.H.steps(b, PH.H.steps(a, st)) : C.Wasm.Step}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      match st:
        case C.Wasm.Step.next{+fr, +m}:
          steps.add(p, b, C.Wasm.step(fr, m))
        case C.Wasm.Step.done{+rs, +m}:
          Equal.sym(C.Wasm.Step, PH.H.steps(b, C.Wasm.Step.done{rs, m}), C.Wasm.Step.done{rs, m}, steps.done(b, rs, m))
        case C.Wasm.Step.trap{+m}:
          Equal.sym(C.Wasm.Step, PH.H.steps(b, C.Wasm.Step.trap{m}), C.Wasm.Step.trap{m}, steps.trap(b, m))

# a steps from st reach st1, and b more reach st2
def steps.then(+a: Nat, +b: Nat, +st: C.Wasm.Step, -st1: C.Wasm.Step, -st2: C.Wasm.Step,
  e1: {PH.H.steps(a, st) == st1 : C.Wasm.Step}, e2: {PH.H.steps(b, st1) == st2 : C.Wasm.Step}) ->
  {PH.H.steps(Nat.add(a, b), st) == st2 : C.Wasm.Step}:
  Equal.trans(C.Wasm.Step, PH.H.steps(Nat.add(a, b), st), PH.H.steps(b, PH.H.steps(a, st)), st2, steps.add(a, b, st),
    Equal.trans(C.Wasm.Step, PH.H.steps(b, PH.H.steps(a, st)), PH.H.steps(b, st1), st2,
      Equal.cong(C.Wasm.Step, C.Wasm.Step, x => PH.H.steps(b, x), PH.H.steps(a, st), st1, e1), e2))

# a run that reached a done step stays there
def steps.then_done(+a: Nat, +b: Nat, +st: C.Wasm.Step, -rs: List<&2, U32>, -m: C.Wasm.Memory,
  e1: {PH.H.steps(a, st) == C.Wasm.Step.done{rs, m} : C.Wasm.Step}) ->
  {PH.H.steps(Nat.add(a, b), st) == C.Wasm.Step.done{rs, m} : C.Wasm.Step}:
  steps.then(a, b, st, C.Wasm.Step.done{rs, m}, C.Wasm.Step.done{rs, m}, e1, steps.done(b, rs, m))

# Calls
# -----

# what the call from st gives with the fuel F, when the run from st ends
# after n steps with the results rs and the memory m2
def GD(F: Nat, st: C.Wasm.Step, -rs: List<&2, U32>, -m2: C.Wasm.Memory, n: Nat) -> Data:
  match st:
    case C.Wasm.Step.next{fr, m}:
      EX(j => P2({C.Wasm.call.go(F, fr, m) == C.Wasm.Call.done{rs, m2, j} : C.Wasm.Call}, N.Le(j, n)))
    case C.Wasm.Step.done{rs1, m1}:
      P2({rs1 == rs : List<&2, U32>}, {m1 == m2 : C.Wasm.Memory})
    case C.Wasm.Step.trap{_}:
      Empty

def gd.stepped(F1: Nat, st: C.Wasm.Step, -rs: List<&2, U32>, -m2: C.Wasm.Memory, +n: Nat, q: GD(F1, st, rs, m2, n)) ->
  EX(j => P2({C.Wasm.call.stepped(st, g => mm => C.Wasm.call.go(F1, g, mm)) == C.Wasm.Call.done{rs, m2, j} : C.Wasm.Call},
    N.Le(j, 1n+n))):
  match st:
    case C.Wasm.Step.next{g, mm}:
      (+j, r) = q
      (eq, le) = r
      (1n+j, (Equal.cong(C.Wasm.Call, C.Wasm.Call, c => C.Wasm.call.plus(c), C.Wasm.call.go(F1, g, mm),
        C.Wasm.Call.done{rs, m2, j}, eq), le))
    case C.Wasm.Step.done{rs1, m1}:
      (e1, e2) = q
      +eq = {(%Equal.sym(List<&2, U32>, rs1, rs, e1) : {C.Wasm.Call.done{_, m1, 1n} == C.Wasm.Call.done{rs, m2, 1n} : C.Wasm.Call};
        %Equal.sym(C.Wasm.Memory, m1, m2, e2) : {C.Wasm.Call.done{rs, _, 1n} == C.Wasm.Call.done{rs, m2, 1n} : C.Wasm.Call};
        {==}) : {C.Wasm.Call.done{rs1, m1, 1n} == C.Wasm.Call.done{rs, m2, 1n} : C.Wasm.Call}}
      (1n, (eq, N.le_zero(n)))
    case C.Wasm.Step.trap{m}:
      Empty.absurd(EX(j => P2({C.Wasm.Call.trap{m} == C.Wasm.Call.done{rs, m2, j} : C.Wasm.Call}, N.Le(j, 1n+n))), q)

def gd.done(-rs1: List<&2, U32>, -m1: C.Wasm.Memory, -rs: List<&2, U32>, -m2: C.Wasm.Memory,
  +e: {C.Wasm.Step.done{rs1, m1} == C.Wasm.Step.done{rs, m2} : C.Wasm.Step}) ->
  P2({rs1 == rs : List<&2, U32>}, {m1 == m2 : C.Wasm.Memory}):
  (Equal.cong(C.Wasm.Step, List<&2, U32>, s => done.rs(s), C.Wasm.Step.done{rs1, m1}, C.Wasm.Step.done{rs, m2}, e),
   Equal.cong(C.Wasm.Step, C.Wasm.Memory, s => done.mem(s), C.Wasm.Step.done{rs1, m1}, C.Wasm.Step.done{rs, m2}, e))

# a run that ends after n steps gives its end with any fuel F >= n
def gd.ext(+n: Nat, +st: C.Wasm.Step, +F: Nat, -rs: List<&2, U32>, -m2: C.Wasm.Memory,
  e: {PH.H.steps(n, st) == C.Wasm.Step.done{rs, m2} : C.Wasm.Step}, h: N.Le(n, F)) -> GD(F, st, rs, m2, n):
  match n:
    case 0n:
      match st:
        case C.Wasm.Step.next{fr, m}:
          Empty.absurd(GD(F, C.Wasm.Step.next{fr, m}, rs, m2, 0n), next.not_done(fr, m, rs, m2, e))
        case C.Wasm.Step.done{rs1, m1}:
          gd.done(rs1, m1, rs, m2, e)
        case C.Wasm.Step.trap{m}:
          Empty.absurd(GD(F, C.Wasm.Step.trap{m}, rs, m2, 0n), trap.not_done(m, rs, m2, e))
    case 1n+p:
      match st:
        case C.Wasm.Step.next{+fr, +m}:
          match F:
            case 0n:
              Empty.absurd(GD(0n, C.Wasm.Step.next{fr, m}, rs, m2, 1n+p), h)
            case 1n+F1:
              gd.stepped(F1, C.Wasm.step(fr, m), rs, m2, p, gd.ext(p, C.Wasm.step(fr, m), F1, rs, m2, e, h))
        case C.Wasm.Step.done{rs1, m1}:
          gd.done(rs1, m1, rs, m2, e)
        case C.Wasm.Step.trap{m}:
          Empty.absurd(GD(F, C.Wasm.Step.trap{m}, rs, m2, 1n+p), trap.not_done(m, rs, m2, e))

# a call of a running frame that ends after n steps, with any fuel F >= n
def run.call(+n: Nat, +F: Nat, +fr: C.Wasm.Frame, +m: C.Wasm.Memory, -rs: List<&2, U32>, -m2: C.Wasm.Memory,
  e: {PH.H.steps(n, C.Wasm.Step.next{fr, m}) == C.Wasm.Step.done{rs, m2} : C.Wasm.Step}, h: N.Le(n, F)) ->
  EX(j => P2({C.Wasm.call.go(F, fr, m) == C.Wasm.Call.done{rs, m2, j} : C.Wasm.Call}, N.Le(j, n))):
  gd.ext(n, C.Wasm.Step.next{fr, m}, F, rs, m2, e, h)
