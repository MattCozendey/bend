# compiler: a run of alloc
# ========================
#
# alloc(n) (Cir.alloc) gives the input's address a = Cir.input.at(k) with
# the memory grown to the pages that Cir.alloc.pages gives, or -1 when that
# gives none (af.call): by the cases of its four tests, the end a + n wraps
# (c1) or is past 2^32 - 16 (c2), the memory holds the pages already (c3),
# or the limit allows them (c4); each path is a fixed run of at most 41
# steps.

import Base
import ./impl.bend as C
import ./proof_need.bend as N
import ./proof_halt.bend as PH
import ./proof_module.bend as M
import ./proof_sim_step.bend as S
import ./proof_sim_inv.bend as Q
import ./proof_sim_frame.bend as F
import ./proof_sim_alloc.bend as A

# The frames
# ----------

def af.a(+k: U32) -> U32:
  C.Cir.input.at(k)

def af.E(+k: U32, +len: U32) -> U32:
  U32.add(af.a(k), len)

# the pages that the end needs, as alloc computes them
def af.need(+k: U32, +len: U32) -> U32:
  U32.add(U32.shrn(U32.sub(af.E(k, len), 1), 16n), 1)

def af.LB() -> C.Wasm.Label:
  C.Wasm.Label{None{}, [C.Cir.i.get(2)], 0n}

def af.LG(+k: U32) -> C.Wasm.Label:
  C.Wasm.Label{None{}, [C.Cir.i.const(af.a(k)), C.Cir.i.set(2)], 0n}

# the inner block: the growth
def af.G(+k: U32) -> List<&2, C.Wasm.Instr>:
  [C.Cir.i.get(3), C.Wasm.Instr.memory_size{}, C.Cir.i.op(C.Wasm.Op.le_u{}), C.Wasm.Instr.br_if{0},
   C.Cir.i.get(3), C.Wasm.Instr.memory_size{}, C.Cir.i.op(C.Wasm.Op.sub{}), C.Wasm.Instr.memory_grow{},
   C.Cir.i.const(4294967295), C.Cir.i.op(C.Wasm.Op.eq{}), C.Wasm.Instr.br_if{1}]

def af.G1() -> List<&2, C.Wasm.Instr>:
  [C.Cir.i.get(3), C.Wasm.Instr.memory_size{}, C.Cir.i.op(C.Wasm.Op.sub{}), C.Wasm.Instr.memory_grow{},
   C.Cir.i.const(4294967295), C.Cir.i.op(C.Wasm.Op.eq{}), C.Wasm.Instr.br_if{1}]

# the outer block after its first test, and after its second
def af.B2(+k: U32) -> List<&2, C.Wasm.Instr>:
  [C.Cir.i.get(1), C.Cir.i.const(1), C.Cir.i.op(C.Wasm.Op.sub{}), C.Cir.i.const(16), C.Cir.i.op(C.Wasm.Op.shr_u{}),
   C.Cir.i.const(1), C.Cir.i.op(C.Wasm.Op.add{}), C.Cir.i.set(3),
   C.Wasm.Instr.block{af.G(k)},
   C.Cir.i.const(af.a(k)), C.Cir.i.set(2)]

def af.B1(+k: U32) -> List<&2, C.Wasm.Instr>:
  Con{C.Cir.i.get(1), Con{C.Cir.i.const(4294967280), Con{C.Cir.i.op(C.Wasm.Op.gt_u{}), Con{C.Wasm.Instr.br_if{0}, af.B2(k)}}}}

def af.L1(+k: U32, +len: U32) -> List<&2, U32>:
  [len, af.E(k, len), 4294967295, 0]

def af.L2(+k: U32, +len: U32) -> List<&2, U32>:
  [len, af.E(k, len), 4294967295, af.need(k, len)]

def af.L3(+k: U32, +len: U32) -> List<&2, U32>:
  [len, af.E(k, len), af.a(k), af.need(k, len)]

def af.fr0(+k: U32, +len: U32) -> C.Wasm.Frame:
  C.Wasm.Frame{M.body(C.Cir.alloc(k)), [], 1n, [], [len, 0, 0, 0]}

# The paths
# ---------

def af.s1(+k: U32, +len: U32, +mm: C.Wasm.Memory) ->
  {PH.H.steps(10n, C.Wasm.Step.next{af.fr0(k, len), mm}) ==
    Q.Cfg(Con{C.Wasm.Instr.br_if{0}, af.B1(k)}, [af.LB()], [Bool.to_u32(U32.is_lt(af.E(k, len), af.a(k)))], af.L1(k, len), mm) : C.Wasm.Step}:
  {==}

def af.s2(+k: U32, +len: U32, +mm: C.Wasm.Memory) ->
  {PH.H.steps(3n, Q.Cfg(af.B1(k), [af.LB()], [], af.L1(k, len), mm)) ==
    Q.Cfg(Con{C.Wasm.Instr.br_if{0}, af.B2(k)}, [af.LB()], [Bool.to_u32(U32.is_gt(af.E(k, len), 4294967280))], af.L1(k, len), mm) : C.Wasm.Step}:
  {==}

def af.s3(+k: U32, +len: U32, +p: U32, +lim: U32, +B: C.Wasm.Bytes) ->
  {PH.H.steps(12n, Q.Cfg(af.B2(k), [af.LB()], [], af.L1(k, len), C.Wasm.Memory{p, lim, B})) ==
    Q.Cfg(Con{C.Wasm.Instr.br_if{0}, af.G1()}, [af.LG(k), af.LB()], [Bool.to_u32(U32.is_le(af.need(k, len), p))], af.L2(k, len),
      C.Wasm.Memory{p, lim, B}) : C.Wasm.Step}:
  {==}

# a test that fails out of the outer block: alloc gives -1
def af.out(+L: List<&2, U32>, +mm: C.Wasm.Memory, +rest: List<&2, C.Wasm.Instr>, +v: U32, ez: {U32.is_zero(v) == False{} : Bool},
  eL: {List.get(&2, U32, L, 2n) == Some{4294967295} : Maybe<&2, U32>}) ->
  {PH.H.steps(3n, Q.Cfg(Con{C.Wasm.Instr.br_if{0}, rest}, [af.LB()], [v], L, mm)) == C.Wasm.Step.done{[4294967295], mm} : C.Wasm.Step}:
  S.steps.then(1n, 2n, Q.Cfg(Con{C.Wasm.Instr.br_if{0}, rest}, [af.LB()], [v], L, mm), Q.Cfg([C.Cir.i.get(2)], [], [], L, mm),
    C.Wasm.Step.done{[4294967295], mm}, A.br.ok(v, ez, rest, [C.Cir.i.get(2)], [], L, mm),
    %eL : {PH.H.steps(2n, Q.Cfg([C.Cir.i.get(2)], [], [], L, mm)) == C.Wasm.Step.done{[Maybe.default(&2, U32, _, 0)], mm} : C.Wasm.Step}
    {==})

def af.p1(+k: U32, +len: U32, +mm: C.Wasm.Memory, e1: {U32.is_lt(af.E(k, len), af.a(k)) == True{} : Bool}) ->
  {PH.H.steps(13n, C.Wasm.Step.next{af.fr0(k, len), mm}) == C.Wasm.Step.done{[4294967295], mm} : C.Wasm.Step}:
  S.steps.then(10n, 3n, C.Wasm.Step.next{af.fr0(k, len), mm},
    Q.Cfg(Con{C.Wasm.Instr.br_if{0}, af.B1(k)}, [af.LB()], [Bool.to_u32(U32.is_lt(af.E(k, len), af.a(k)))], af.L1(k, len), mm),
    C.Wasm.Step.done{[4294967295], mm}, af.s1(k, len, mm),
    af.out(af.L1(k, len), mm, af.B1(k), Bool.to_u32(U32.is_lt(af.E(k, len), af.a(k))), A.tz.t(U32.is_lt(af.E(k, len), af.a(k)), e1), {==}))

# the first test passes
def af.q1(+k: U32, +len: U32, +mm: C.Wasm.Memory, e1: {U32.is_lt(af.E(k, len), af.a(k)) == False{} : Bool}) ->
  {PH.H.steps(11n, C.Wasm.Step.next{af.fr0(k, len), mm}) == Q.Cfg(af.B1(k), [af.LB()], [], af.L1(k, len), mm) : C.Wasm.Step}:
  S.steps.then(10n, 1n, C.Wasm.Step.next{af.fr0(k, len), mm},
    Q.Cfg(Con{C.Wasm.Instr.br_if{0}, af.B1(k)}, [af.LB()], [Bool.to_u32(U32.is_lt(af.E(k, len), af.a(k)))], af.L1(k, len), mm),
    Q.Cfg(af.B1(k), [af.LB()], [], af.L1(k, len), mm), af.s1(k, len, mm),
    A.br.no(Bool.to_u32(U32.is_lt(af.E(k, len), af.a(k))), A.tz.f(U32.is_lt(af.E(k, len), af.a(k)), e1), af.B1(k), [af.LB()], af.L1(k, len), mm))

def af.p2(+k: U32, +len: U32, +mm: C.Wasm.Memory, e1: {U32.is_lt(af.E(k, len), af.a(k)) == False{} : Bool},
  e2: {U32.is_gt(af.E(k, len), 4294967280) == True{} : Bool}) ->
  {PH.H.steps(17n, C.Wasm.Step.next{af.fr0(k, len), mm}) == C.Wasm.Step.done{[4294967295], mm} : C.Wasm.Step}:
  +C1 = Q.Cfg(af.B1(k), [af.LB()], [], af.L1(k, len), mm)
  +v = Bool.to_u32(U32.is_gt(af.E(k, len), 4294967280))
  +C2 = Q.Cfg(Con{C.Wasm.Instr.br_if{0}, af.B2(k)}, [af.LB()], [v], af.L1(k, len), mm)
  S.steps.then(11n, 6n, C.Wasm.Step.next{af.fr0(k, len), mm}, C1, C.Wasm.Step.done{[4294967295], mm}, af.q1(k, len, mm, e1),
    S.steps.then(3n, 3n, C1, C2, C.Wasm.Step.done{[4294967295], mm}, af.s2(k, len, mm),
      af.out(af.L1(k, len), mm, af.B2(k), v, A.tz.t(U32.is_gt(af.E(k, len), 4294967280), e2), {==})))

# both tests pass: the pages, tested against those of the memory
def af.q2(+k: U32, +len: U32, +p: U32, +lim: U32, +B: C.Wasm.Bytes, e1: {U32.is_lt(af.E(k, len), af.a(k)) == False{} : Bool},
  e2: {U32.is_gt(af.E(k, len), 4294967280) == False{} : Bool}) ->
  {PH.H.steps(27n, C.Wasm.Step.next{af.fr0(k, len), C.Wasm.Memory{p, lim, B}}) ==
    Q.Cfg(Con{C.Wasm.Instr.br_if{0}, af.G1()}, [af.LG(k), af.LB()], [Bool.to_u32(U32.is_le(af.need(k, len), p))], af.L2(k, len),
      C.Wasm.Memory{p, lim, B}) : C.Wasm.Step}:
  +mm = {C.Wasm.Memory{p, lim, B} : C.Wasm.Memory}
  +C1 = Q.Cfg(af.B1(k), [af.LB()], [], af.L1(k, len), mm)
  +v = Bool.to_u32(U32.is_gt(af.E(k, len), 4294967280))
  +C2 = Q.Cfg(Con{C.Wasm.Instr.br_if{0}, af.B2(k)}, [af.LB()], [v], af.L1(k, len), mm)
  +C3 = Q.Cfg(af.B2(k), [af.LB()], [], af.L1(k, len), mm)
  +C4 = Q.Cfg(Con{C.Wasm.Instr.br_if{0}, af.G1()}, [af.LG(k), af.LB()], [Bool.to_u32(U32.is_le(af.need(k, len), p))], af.L2(k, len), mm)
  S.steps.then(11n, 16n, C.Wasm.Step.next{af.fr0(k, len), mm}, C1, C4, af.q1(k, len, mm, e1),
    S.steps.then(3n, 13n, C1, C2, C4, af.s2(k, len, mm),
      S.steps.then(1n, 12n, C2, C3, C4, A.br.no(v, A.tz.f(U32.is_gt(af.E(k, len), 4294967280), e2), af.B2(k), [af.LB()], af.L1(k, len), mm),
        af.s3(k, len, p, lim, B))))

# the end of the outer block: alloc gives a
def af.fin(+k: U32, +len: U32, +mm: C.Wasm.Memory) ->
  {PH.H.steps(5n, Q.Cfg([C.Cir.i.const(af.a(k)), C.Cir.i.set(2)], [af.LB()], [], af.L2(k, len), mm)) ==
    C.Wasm.Step.done{[af.a(k)], mm} : C.Wasm.Step}:
  {==}

# the memory holds the pages already
def af.p3(+k: U32, +len: U32, +p: U32, +lim: U32, +B: C.Wasm.Bytes, e1: {U32.is_lt(af.E(k, len), af.a(k)) == False{} : Bool},
  e2: {U32.is_gt(af.E(k, len), 4294967280) == False{} : Bool}, e3: {U32.is_le(af.need(k, len), p) == True{} : Bool}) ->
  {PH.H.steps(33n, C.Wasm.Step.next{af.fr0(k, len), C.Wasm.Memory{p, lim, B}}) == C.Wasm.Step.done{[af.a(k)], C.Wasm.Memory{p, lim, B}} : C.Wasm.Step}:
  +mm = {C.Wasm.Memory{p, lim, B} : C.Wasm.Memory}
  +v = Bool.to_u32(U32.is_le(af.need(k, len), p))
  +C4 = Q.Cfg(Con{C.Wasm.Instr.br_if{0}, af.G1()}, [af.LG(k), af.LB()], [v], af.L2(k, len), mm)
  +C5 = Q.Cfg([C.Cir.i.const(af.a(k)), C.Cir.i.set(2)], [af.LB()], [], af.L2(k, len), mm)
  S.steps.then(27n, 6n, C.Wasm.Step.next{af.fr0(k, len), mm}, C4, C.Wasm.Step.done{[af.a(k)], mm}, af.q2(k, len, p, lim, B, e1, e2),
    S.steps.then(1n, 5n, C4, C5, C.Wasm.Step.done{[af.a(k)], mm},
      A.br.ok(v, A.tz.t(U32.is_le(af.need(k, len), p), e3), af.G1(), [C.Cir.i.const(af.a(k)), C.Cir.i.set(2)], [af.LB()], af.L2(k, len), mm),
      af.fin(k, len, mm)))

# the growth, to its memory.grow
def af.s4(+k: U32, +len: U32, +p: U32, +lim: U32, +B: C.Wasm.Bytes) ->
  {PH.H.steps(3n, Q.Cfg(af.G1(), [af.LG(k), af.LB()], [], af.L2(k, len), C.Wasm.Memory{p, lim, B})) ==
    Q.Cfg([C.Wasm.Instr.memory_grow{}, C.Cir.i.const(4294967295), C.Cir.i.op(C.Wasm.Op.eq{}), C.Wasm.Instr.br_if{1}],
      [af.LG(k), af.LB()], [U32.sub(af.need(k, len), p)], af.L2(k, len), C.Wasm.Memory{p, lim, B}) : C.Wasm.Step}:
  {==}

def af.C4(+k: U32, +len: U32, +p: U32, +lim: U32, +B: C.Wasm.Bytes) -> C.Wasm.Step:
  Q.Cfg([C.Cir.i.const(4294967295), C.Cir.i.op(C.Wasm.Op.eq{}), C.Wasm.Instr.br_if{1}], [af.LG(k), af.LB()], [p], af.L2(k, len),
    C.Wasm.Memory{af.need(k, len), lim, B})

# memory.grow by need - p, within the limit: need pages
def af.grow(+k: U32, +len: U32, +p: U32, +lim: U32, +B: C.Wasm.Bytes, +e4: {U32.is_le(af.need(k, len), lim) == True{} : Bool},
  +hge: {U32.is_ge(af.need(k, len), p) == True{} : Bool}) ->
  {PH.H.steps(1n, Q.Cfg([C.Wasm.Instr.memory_grow{}, C.Cir.i.const(4294967295), C.Cir.i.op(C.Wasm.Op.eq{}), C.Wasm.Instr.br_if{1}],
      [af.LG(k), af.LB()], [U32.sub(af.need(k, len), p)], af.L2(k, len), C.Wasm.Memory{p, lim, B})) == af.C4(k, len, p, lim, B) : C.Wasm.Step}:
  +nd = af.need(k, len)
  +R = {[C.Cir.i.const(4294967295), C.Cir.i.op(C.Wasm.Op.eq{}), C.Wasm.Instr.br_if{1}] : List<&2, C.Wasm.Instr>}
  +LS = {[af.LG(k), af.LB()] : List<&2, C.Wasm.Label>}
  %Equal.sym(U32, U32.add(p, U32.sub(nd, p)), nd, A.U32.addsub(p, nd)) :
    {C.Wasm.step.grown(Bool.and(U32.is_ge(_, p), U32.is_le(_, lim)), p, _, lim, B, R, LS, 1n, [], af.L2(k, len)) == af.C4(k, len, p, lim, B) : C.Wasm.Step}
  %Equal.sym(Bool, U32.is_ge(nd, p), True{}, hge) :
    {C.Wasm.step.grown(Bool.and(_, U32.is_le(nd, lim)), p, nd, lim, B, R, LS, 1n, [], af.L2(k, len)) == af.C4(k, len, p, lim, B) : C.Wasm.Step}
  %Equal.sym(Bool, U32.is_le(nd, lim), True{}, e4) :
    {C.Wasm.step.grown(Bool.and(True{}, _), p, nd, lim, B, R, LS, 1n, [], af.L2(k, len)) == af.C4(k, len, p, lim, B) : C.Wasm.Step}
  {==}

def af.and.f(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# memory.grow past the limit: -1
def af.nogrow(+k: U32, +len: U32, +p: U32, +lim: U32, +B: C.Wasm.Bytes, +e4: {U32.is_le(af.need(k, len), lim) == False{} : Bool}) ->
  {PH.H.steps(1n, Q.Cfg([C.Wasm.Instr.memory_grow{}, C.Cir.i.const(4294967295), C.Cir.i.op(C.Wasm.Op.eq{}), C.Wasm.Instr.br_if{1}],
      [af.LG(k), af.LB()], [U32.sub(af.need(k, len), p)], af.L2(k, len), C.Wasm.Memory{p, lim, B})) ==
    Q.Cfg([C.Cir.i.const(4294967295), C.Cir.i.op(C.Wasm.Op.eq{}), C.Wasm.Instr.br_if{1}], [af.LG(k), af.LB()], [4294967295], af.L2(k, len),
      C.Wasm.Memory{p, lim, B}) : C.Wasm.Step}:
  +nd = af.need(k, len)
  +R = {[C.Cir.i.const(4294967295), C.Cir.i.op(C.Wasm.Op.eq{}), C.Wasm.Instr.br_if{1}] : List<&2, C.Wasm.Instr>}
  +LS = {[af.LG(k), af.LB()] : List<&2, C.Wasm.Label>}
  +G = Q.Cfg(R, LS, [4294967295], af.L2(k, len), C.Wasm.Memory{p, lim, B})
  %Equal.sym(U32, U32.add(p, U32.sub(nd, p)), nd, A.U32.addsub(p, nd)) :
    {C.Wasm.step.grown(Bool.and(U32.is_ge(_, p), U32.is_le(_, lim)), p, _, lim, B, R, LS, 1n, [], af.L2(k, len)) == G : C.Wasm.Step}
  %Equal.sym(Bool, U32.is_le(nd, lim), False{}, e4) :
    {C.Wasm.step.grown(Bool.and(U32.is_ge(nd, p), _), p, nd, lim, B, R, LS, 1n, [], af.L2(k, len)) == G : C.Wasm.Step}
  %Equal.sym(Bool, Bool.and(U32.is_ge(nd, p), False{}), False{}, af.and.f(U32.is_ge(nd, p))) :
    {C.Wasm.step.grown(_, p, nd, lim, B, R, LS, 1n, [], af.L2(k, len)) == G : C.Wasm.Step}
  {==}

# after the growth: p is not -1, so on to the end
def af.tail(+k: U32, +len: U32, +p: U32, +lim: U32, +B: C.Wasm.Bytes, +hp: {U32.is_eq(p, 4294967295) == False{} : Bool}) ->
  {PH.H.steps(9n, af.C4(k, len, p, lim, B)) == C.Wasm.Step.done{[af.a(k)], C.Wasm.Memory{af.need(k, len), lim, B}} : C.Wasm.Step}:
  +M2 = {C.Wasm.Memory{af.need(k, len), lim, B} : C.Wasm.Memory}
  +C5 = Q.Cfg([C.Wasm.Instr.br_if{1}], [af.LG(k), af.LB()], [Bool.to_u32(U32.is_eq(p, 4294967295))], af.L2(k, len), M2)
  S.steps.then(2n, 7n, af.C4(k, len, p, lim, B), C5, C.Wasm.Step.done{[af.a(k)], M2}, {==},
    %Equal.sym(Bool, U32.is_eq(p, 4294967295), False{}, hp) :
      {PH.H.steps(7n, Q.Cfg([C.Wasm.Instr.br_if{1}], [af.LG(k), af.LB()], [Bool.to_u32(_)], af.L2(k, len), M2)) ==
        C.Wasm.Step.done{[af.a(k)], M2} : C.Wasm.Step}
    {==})

# the memory lacks the pages: the run to memory.grow
def af.q3(+k: U32, +len: U32, +p: U32, +lim: U32, +B: C.Wasm.Bytes, e1: {U32.is_lt(af.E(k, len), af.a(k)) == False{} : Bool},
  e2: {U32.is_gt(af.E(k, len), 4294967280) == False{} : Bool}, e3: {U32.is_le(af.need(k, len), p) == False{} : Bool}) ->
  {PH.H.steps(31n, C.Wasm.Step.next{af.fr0(k, len), C.Wasm.Memory{p, lim, B}}) ==
    Q.Cfg([C.Wasm.Instr.memory_grow{}, C.Cir.i.const(4294967295), C.Cir.i.op(C.Wasm.Op.eq{}), C.Wasm.Instr.br_if{1}],
      [af.LG(k), af.LB()], [U32.sub(af.need(k, len), p)], af.L2(k, len), C.Wasm.Memory{p, lim, B}) : C.Wasm.Step}:
  +mm = {C.Wasm.Memory{p, lim, B} : C.Wasm.Memory}
  +v = Bool.to_u32(U32.is_le(af.need(k, len), p))
  +C4 = Q.Cfg(Con{C.Wasm.Instr.br_if{0}, af.G1()}, [af.LG(k), af.LB()], [v], af.L2(k, len), mm)
  +C5 = Q.Cfg(af.G1(), [af.LG(k), af.LB()], [], af.L2(k, len), mm)
  +C6 = Q.Cfg([C.Wasm.Instr.memory_grow{}, C.Cir.i.const(4294967295), C.Cir.i.op(C.Wasm.Op.eq{}), C.Wasm.Instr.br_if{1}],
      [af.LG(k), af.LB()], [U32.sub(af.need(k, len), p)], af.L2(k, len), mm)
  S.steps.then(27n, 4n, C.Wasm.Step.next{af.fr0(k, len), mm}, C4, C6, af.q2(k, len, p, lim, B, e1, e2),
    S.steps.then(1n, 3n, C4, C5, C6, A.br.no(v, A.tz.f(U32.is_le(af.need(k, len), p), e3), af.G1(), [af.LG(k), af.LB()], af.L2(k, len), mm),
      af.s4(k, len, p, lim, B)))

def af.p4(+k: U32, +len: U32, +p: U32, +lim: U32, +B: C.Wasm.Bytes, e1: {U32.is_lt(af.E(k, len), af.a(k)) == False{} : Bool},
  e2: {U32.is_gt(af.E(k, len), 4294967280) == False{} : Bool}, +e3: {U32.is_le(af.need(k, len), p) == False{} : Bool},
  +e4: {U32.is_le(af.need(k, len), lim) == True{} : Bool}, +hp: {U32.is_eq(p, 4294967295) == False{} : Bool}) ->
  {PH.H.steps(41n, C.Wasm.Step.next{af.fr0(k, len), C.Wasm.Memory{p, lim, B}}) ==
    C.Wasm.Step.done{[af.a(k)], C.Wasm.Memory{af.need(k, len), lim, B}} : C.Wasm.Step}:
  +nd = af.need(k, len)
  +hge = A.ge.of(nd, p, N.weaken(U32.to_nat(p), U32.to_nat(nd), A.nle.u32(nd, p, e3)))
  +C6 = Q.Cfg([C.Wasm.Instr.memory_grow{}, C.Cir.i.const(4294967295), C.Cir.i.op(C.Wasm.Op.eq{}), C.Wasm.Instr.br_if{1}],
      [af.LG(k), af.LB()], [U32.sub(nd, p)], af.L2(k, len), C.Wasm.Memory{p, lim, B})
  S.steps.then(31n, 10n, C.Wasm.Step.next{af.fr0(k, len), C.Wasm.Memory{p, lim, B}}, C6,
    C.Wasm.Step.done{[af.a(k)], C.Wasm.Memory{nd, lim, B}}, af.q3(k, len, p, lim, B, e1, e2, e3),
    S.steps.then(1n, 9n, C6, af.C4(k, len, p, lim, B), C.Wasm.Step.done{[af.a(k)], C.Wasm.Memory{nd, lim, B}},
      af.grow(k, len, p, lim, B, e4, hge), af.tail(k, len, p, lim, B, hp)))

def af.p5(+k: U32, +len: U32, +p: U32, +lim: U32, +B: C.Wasm.Bytes, e1: {U32.is_lt(af.E(k, len), af.a(k)) == False{} : Bool},
  e2: {U32.is_gt(af.E(k, len), 4294967280) == False{} : Bool}, e3: {U32.is_le(af.need(k, len), p) == False{} : Bool},
  +e4: {U32.is_le(af.need(k, len), lim) == False{} : Bool}) ->
  {PH.H.steps(37n, C.Wasm.Step.next{af.fr0(k, len), C.Wasm.Memory{p, lim, B}}) ==
    C.Wasm.Step.done{[4294967295], C.Wasm.Memory{p, lim, B}} : C.Wasm.Step}:
  +mm = {C.Wasm.Memory{p, lim, B} : C.Wasm.Memory}
  +C6 = Q.Cfg([C.Wasm.Instr.memory_grow{}, C.Cir.i.const(4294967295), C.Cir.i.op(C.Wasm.Op.eq{}), C.Wasm.Instr.br_if{1}],
      [af.LG(k), af.LB()], [U32.sub(af.need(k, len), p)], af.L2(k, len), mm)
  +C7 = Q.Cfg([C.Cir.i.const(4294967295), C.Cir.i.op(C.Wasm.Op.eq{}), C.Wasm.Instr.br_if{1}], [af.LG(k), af.LB()], [4294967295], af.L2(k, len), mm)
  S.steps.then(31n, 6n, C.Wasm.Step.next{af.fr0(k, len), mm}, C6, C.Wasm.Step.done{[4294967295], mm}, af.q3(k, len, p, lim, B, e1, e2, e3),
    S.steps.then(1n, 5n, C6, C7, C.Wasm.Step.done{[4294967295], mm}, af.nogrow(k, len, p, lim, B, e4), {==}))

# The cases
# ---------

# the run of alloc's body, by what Cir.alloc.pages gives
def AFS(r: Maybe<&2, U32>, +k: U32, +len: U32, +p: U32, +lim: U32, +B: C.Wasm.Bytes) -> Data:
  match r:
    case None{}:
      S.EX(N2 => S.P2({PH.H.steps(N2, C.Wasm.Step.next{af.fr0(k, len), C.Wasm.Memory{p, lim, B}}) ==
        C.Wasm.Step.done{[4294967295], C.Wasm.Memory{p, lim, B}} : C.Wasm.Step}, N.Le(N2, 41n)))
    case Some{+p2}:
      S.EX(N2 => S.P2({PH.H.steps(N2, C.Wasm.Step.next{af.fr0(k, len), C.Wasm.Memory{p, lim, B}}) ==
        C.Wasm.Step.done{[af.a(k)], C.Wasm.Memory{p2, lim, B}} : C.Wasm.Step}, N.Le(N2, 41n)))

def af.k4(b4: Bool, +k: U32, +len: U32, +p: U32, +lim: U32, +B: C.Wasm.Bytes, e1: {U32.is_lt(af.E(k, len), af.a(k)) == False{} : Bool},
  e2: {U32.is_gt(af.E(k, len), 4294967280) == False{} : Bool}, +e3: {U32.is_le(af.need(k, len), p) == False{} : Bool},
  +e4: {U32.is_le(af.need(k, len), lim) == b4 : Bool}, +hp: {U32.is_eq(p, 4294967295) == False{} : Bool}) ->
  AFS(C.Cir.alloc.grow(False{}, b4, p, af.need(k, len)), k, len, p, lim, B):
  match b4:
    case True{}:
      (41n, (af.p4(k, len, p, lim, B, e1, e2, e3, e4, hp), Unit{}))
    case False{}:
      (37n, (af.p5(k, len, p, lim, B, e1, e2, e3, e4), Unit{}))

def af.k3(b3: Bool, +k: U32, +len: U32, +p: U32, +lim: U32, +B: C.Wasm.Bytes, e1: {U32.is_lt(af.E(k, len), af.a(k)) == False{} : Bool},
  e2: {U32.is_gt(af.E(k, len), 4294967280) == False{} : Bool}, +e3: {U32.is_le(af.need(k, len), p) == b3 : Bool},
  +hp: {U32.is_eq(p, 4294967295) == False{} : Bool}) ->
  AFS(C.Cir.alloc.grow(b3, U32.is_le(af.need(k, len), lim), p, af.need(k, len)), k, len, p, lim, B):
  match b3:
    case True{}:
      (33n, (af.p3(k, len, p, lim, B, e1, e2, e3), Unit{}))
    case False{}:
      af.k4(U32.is_le(af.need(k, len), lim), k, len, p, lim, B, e1, e2, e3, {==}, hp)

def af.k2(b2: Bool, +k: U32, +len: U32, +p: U32, +lim: U32, +B: C.Wasm.Bytes, e1: {U32.is_lt(af.E(k, len), af.a(k)) == False{} : Bool},
  e2: {U32.is_gt(af.E(k, len), 4294967280) == b2 : Bool}, +hp: {U32.is_eq(p, 4294967295) == False{} : Bool}) ->
  AFS(C.Cir.alloc.end(Bool.or(False{}, b2), af.E(k, len), p, lim), k, len, p, lim, B):
  match b2:
    case True{}:
      (17n, (af.p2(k, len, C.Wasm.Memory{p, lim, B}, e1, e2), Unit{}))
    case False{}:
      %F.inc.add1(U32.shrn(U32.sub(af.E(k, len), 1), 16n)) :
        AFS(C.Cir.alloc.grow(U32.is_le(_, p), U32.is_le(_, lim), p, _), k, len, p, lim, B)
      af.k3(U32.is_le(af.need(k, len), p), k, len, p, lim, B, e1, e2, {==}, hp)

def af.k1(b1: Bool, +k: U32, +len: U32, +p: U32, +lim: U32, +B: C.Wasm.Bytes, e1: {U32.is_lt(af.E(k, len), af.a(k)) == b1 : Bool},
  +hp: {U32.is_eq(p, 4294967295) == False{} : Bool}) ->
  AFS(C.Cir.alloc.end(Bool.or(b1, U32.is_gt(af.E(k, len), 4294967280)), af.E(k, len), p, lim), k, len, p, lim, B):
  match b1:
    case True{}:
      (13n, (af.p1(k, len, C.Wasm.Memory{p, lim, B}, e1), Unit{}))
    case False{}:
      af.k2(U32.is_gt(af.E(k, len), 4294967280), k, len, p, lim, B, e1, {==}, hp)

def af.steps(+k: U32, +len: U32, +p: U32, +lim: U32, +B: C.Wasm.Bytes, +hp: {U32.is_eq(p, 4294967295) == False{} : Bool}) ->
  AFS(C.Cir.alloc.pages(k, len, p, lim), k, len, p, lim, B):
  af.k1(U32.is_lt(af.E(k, len), af.a(k)), k, len, p, lim, B, {==}, hp)

# The call
# --------

# what the call of alloc gives, by what Cir.alloc.pages gives
def AFC(c: C.Wasm.Call, r: Maybe<&2, U32>, +k: U32, +p: U32, +lim: U32, +B: C.Wasm.Bytes) -> Data:
  match r:
    case None{}:
      S.EX(j => S.P2({c == C.Wasm.Call.done{[4294967295], C.Wasm.Memory{p, lim, B}, j} : C.Wasm.Call}, N.Le(j, 41n)))
    case Some{+p2}:
      S.EX(j => S.P2({c == C.Wasm.Call.done{[af.a(k)], C.Wasm.Memory{p2, lim, B}, j} : C.Wasm.Call}, N.Le(j, 41n)))

def af.bnd(c: C.Wasm.Call, -rs: List<&2, U32>, -mm: C.Wasm.Memory, +N2: Nat, hN: N.Le(N2, 41n),
  q: S.EX(j => S.P2({c == C.Wasm.Call.done{rs, mm, j} : C.Wasm.Call}, N.Le(j, N2)))) ->
  S.EX(j => S.P2({c == C.Wasm.Call.done{rs, mm, j} : C.Wasm.Call}, N.Le(j, 41n))):
  (+j, r1) = q
  (ec, hj) = r1
  (j, (ec, N.le_trans(j, N2, 41n, hj, hN)))

def af.call.go(r: Maybe<&2, U32>, +k: U32, +len: U32, +p: U32, +lim: U32, +B: C.Wasm.Bytes, +F: Nat, hF: N.Le(41n, F),
  h: AFS(r, k, len, p, lim, B)) -> AFC(C.Wasm.call(F, C.Cir.alloc(k), [len], C.Wasm.Memory{p, lim, B}), r, k, p, lim, B):
  match r:
    case None{}:
      (+N2, h1) = h
      (e, +hN) = h1
      af.bnd(C.Wasm.call(F, C.Cir.alloc(k), [len], C.Wasm.Memory{p, lim, B}), [4294967295], C.Wasm.Memory{p, lim, B}, N2, hN,
        S.run.call(N2, F, af.fr0(k, len), C.Wasm.Memory{p, lim, B}, [4294967295], C.Wasm.Memory{p, lim, B}, e, N.le_trans(N2, 41n, F, hN, hF)))
    case Some{+p2}:
      (+N2, h1) = h
      (e, +hN) = h1
      af.bnd(C.Wasm.call(F, C.Cir.alloc(k), [len], C.Wasm.Memory{p, lim, B}), [af.a(k)], C.Wasm.Memory{p2, lim, B}, N2, hN,
        S.run.call(N2, F, af.fr0(k, len), C.Wasm.Memory{p, lim, B}, [af.a(k)], C.Wasm.Memory{p2, lim, B}, e, N.le_trans(N2, 41n, F, hN, hF)))

# alloc(len), with the fuel F >= 41, in a memory of p pages, p not -1
def af.call(+k: U32, +len: U32, +p: U32, +lim: U32, +B: C.Wasm.Bytes, +F: Nat, hF: N.Le(41n, F),
  +hp: {U32.is_eq(p, 4294967295) == False{} : Bool}) ->
  AFC(C.Wasm.call(F, C.Cir.alloc(k), [len], C.Wasm.Memory{p, lim, B}), C.Cir.alloc.pages(k, len, p, lim), k, p, lim, B):
  af.call.go(C.Cir.alloc.pages(k, len, p, lim), k, len, p, lim, B, F, hF, af.steps(k, len, p, lim, B, hp))
