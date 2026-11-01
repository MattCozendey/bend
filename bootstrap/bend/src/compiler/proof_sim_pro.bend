# compiler: the start of run
# ==========================
#
# run(a, n) sets the status to 2, addr to the input's end a + n and next to
# the book's k + 1, then its first loop counts next up until 20 × next >= the
# end (pr.loop: d rounds of 16 steps and an exit of 11, by induction on d),
# which stops at Cir.first(k, end) (pr.first: no round when 20 (k + 1) is at
# or past the end; else the rounds up to (end + 19) / 20, by div.twenty); then
# it enters the block of the program's code, with the label RL (pr.go).

import Base
import ./impl.bend as C
import ./proof_need.bend as N
import ./proof_halt.bend as PH
import ./proof_module.bend as M
import ./proof_sim_step.bend as S
import ./proof_sim_nat.bend as Z
import ./proof_sim_inv.bend as Q
import ./proof_sim_frame.bend as F
import ./proof_sim_alloc.bend as A
import ./proof_sim_div.bend as DV
import ./proof_sim_stmt.bend as T

# The loop
# --------

def pr.R1() -> List<&2, C.Wasm.Instr>:
  [C.Cir.i.get(C.Cir.l.next()), C.Cir.i.const(1), C.Cir.i.op(C.Wasm.Op.add{}), C.Cir.i.set(C.Cir.l.next()), C.Wasm.Instr.br{0}]

def pr.LP() -> List<&2, C.Wasm.Instr>:
  Con{C.Cir.i.get(C.Cir.l.next()), C.Cir.code.at(
    [C.Cir.i.get(C.Cir.l.addr()), C.Cir.i.op(C.Wasm.Op.ge_u{}), C.Wasm.Instr.br_if{1},
     C.Cir.i.get(C.Cir.l.next()), C.Cir.i.const(1), C.Cir.i.op(C.Wasm.Op.add{}), C.Cir.i.set(C.Cir.l.next()),
     C.Wasm.Instr.br{0}])}

def pr.LLp() -> C.Wasm.Label:
  C.Wasm.Label{Some{pr.LP()}, [], 0n}

def pr.LBk(+X: List<&2, C.Wasm.Instr>) -> C.Wasm.Label:
  C.Wasm.Label{None{}, [C.Wasm.Instr.block{X}, C.Cir.i.get(C.Cir.l.status())], 0n}

# the loop's start, with next = nx and tmp = t
def pr.LC(+X: List<&2, C.Wasm.Instr>, +a: U32, +n: U32, +nx: U32, +t: U32, +ad: U32, +rg: List<&2, U32>, +mm: C.Wasm.Memory) -> C.Wasm.Step:
  Q.Cfg(pr.LP(), [pr.LLp(), pr.LBk(X)], [], Q.Loc(a, n, 2, nx, 0, t, 0, ad, rg), mm)

# the loop's test
def pr.TC(+X: List<&2, C.Wasm.Instr>, +a: U32, +n: U32, +nx: U32, +ad: U32, +rg: List<&2, U32>, +mm: C.Wasm.Memory) -> C.Wasm.Step:
  Q.Cfg(Con{C.Wasm.Instr.br_if{1}, pr.R1()}, [pr.LLp(), pr.LBk(X)], [Bool.to_u32(U32.is_ge(C.Cir.at(nx), ad))],
    Q.Loc(a, n, 2, nx, 0, nx, 0, ad, rg), mm)

# after the loop
def pr.XC(+X: List<&2, C.Wasm.Instr>, +a: U32, +n: U32, +ad: U32, +rg: List<&2, U32>, +mm: C.Wasm.Memory, +x: U32) -> C.Wasm.Step:
  Q.Cfg([C.Wasm.Instr.block{X}, C.Cir.i.get(C.Cir.l.status())], [], [], Q.Loc(a, n, 2, x, 0, x, 0, ad, rg), mm)

def pr.test(+X: List<&2, C.Wasm.Instr>, +a: U32, +n: U32, +nx: U32, +t: U32, +ad: U32, +rg: List<&2, U32>, +mm: C.Wasm.Memory) ->
  {PH.H.steps(10n, pr.LC(X, a, n, nx, t, ad, rg, mm)) == pr.TC(X, a, n, nx, ad, rg, mm) : C.Wasm.Step}:
  {==}

def pr.exit(+X: List<&2, C.Wasm.Instr>, +a: U32, +n: U32, +nx: U32, +ad: U32, +rg: List<&2, U32>, +mm: C.Wasm.Memory,
  e: {U32.is_ge(C.Cir.at(nx), ad) == True{} : Bool}) ->
  {PH.H.steps(1n, pr.TC(X, a, n, nx, ad, rg, mm)) == pr.XC(X, a, n, ad, rg, mm, nx) : C.Wasm.Step}:
  %Equal.sym(Bool, U32.is_ge(C.Cir.at(nx), ad), True{}, e) :
    {PH.H.steps(1n, Q.Cfg(Con{C.Wasm.Instr.br_if{1}, pr.R1()}, [pr.LLp(), pr.LBk(X)], [Bool.to_u32(_)],
      Q.Loc(a, n, 2, nx, 0, nx, 0, ad, rg), mm)) == pr.XC(X, a, n, ad, rg, mm, nx) : C.Wasm.Step}
  {==}

def pr.more(+X: List<&2, C.Wasm.Instr>, +a: U32, +n: U32, +nx: U32, +ad: U32, +rg: List<&2, U32>, +mm: C.Wasm.Memory,
  e: {U32.is_ge(C.Cir.at(nx), ad) == False{} : Bool}) ->
  {PH.H.steps(6n, pr.TC(X, a, n, nx, ad, rg, mm)) == pr.LC(X, a, n, U32.add(nx, 1), nx, ad, rg, mm) : C.Wasm.Step}:
  %Equal.sym(Bool, U32.is_ge(C.Cir.at(nx), ad), False{}, e) :
    {PH.H.steps(6n, Q.Cfg(Con{C.Wasm.Instr.br_if{1}, pr.R1()}, [pr.LLp(), pr.LBk(X)], [Bool.to_u32(_)],
      Q.Loc(a, n, 2, nx, 0, nx, 0, ad, rg), mm)) == pr.LC(X, a, n, U32.add(nx, 1), nx, ad, rg, mm) : C.Wasm.Step}
  {==}

# 16 d
def s16(d: Nat) -> Nat:
  match d:
    case 0n:
      0n
    case 1n+p:
      16n+s16(p)

# x + d, by steps of 1
def addn(d: Nat, +x: U32) -> U32:
  match d:
    case 0n:
      x
    case 1n+p:
      addn(p, U32.add(x, 1))

# before the last round, 20 (X + d - 1) is below the end E
def LL(d: Nat, +X: Nat, +E: Nat) -> Data:
  match d:
    case 0n:
      Unit
    case 1n+p:
      N.Le(1n+PH.H.t20(Nat.add(X, p)), E)

# a >= b is false when a < b
def nge.rel(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(1n+x, y)) -> {Cmp.is_ge(c) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({True{} == False{} : Bool}, N.not_succ_le(y, (%r : N.Le(1n+_, y); h)))
    case GT{}:
      Empty.absurd({True{} == False{} : Bool}, N.not_succ_le(y, N.le_trans(1n+y, x, y, r, N.weaken(x, y, h))))

def nge.of(+a: U32, +b: U32, h: N.Le(1n+U32.to_nat(a), U32.to_nat(b))) -> {U32.is_ge(a, b) == False{} : Bool}:
  nge.rel(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), h)

# the bound before the last round, from nx + 1
def pr.ll(p: Nat, +Xn: Nat, +E: Nat, hl: LL(1n+p, Xn, E)) -> LL(p, 1n+Xn, E):
  match p:
    case 0n:
      Unit{}
    case 1n+q:
      N.le_rw_l(1n+PH.H.t20(Nat.add(Xn, 1n+q)), 1n+PH.H.t20(Nat.add(1n+Xn, q)), E,
        Equal.cong(Nat, Nat, z => 1n+PH.H.t20(z), Nat.add(Xn, 1n+q), Nat.add(1n+Xn, q), N.add_succ_r(Xn, q)), hl)

# the loop's d rounds and its exit, from next = nx
def pr.loop(d: Nat, +X: List<&2, C.Wasm.Instr>, +a: U32, +n: U32, +nx: U32, +t: U32, +ad: U32, +rg: List<&2, U32>, +mm: C.Wasm.Memory,
  +Xn: Nat, +eX: {U32.to_nat(nx) == Xn : Nat}, +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hx: N.Le(Nat.add(Xn, d), P), +hl: LL(d, Xn, U32.to_nat(ad)), +hf: N.Le(U32.to_nat(ad), PH.H.t20(Nat.add(Xn, d)))) ->
  {PH.H.steps(Nat.add(s16(d), 11n), pr.LC(X, a, n, nx, t, ad, rg, mm)) == pr.XC(X, a, n, ad, rg, mm, addn(d, nx)) : C.Wasm.Step}:
  match d:
    case 0n:
      +AD = U32.to_nat(ad)
      +hX = N.le_rw_l(Nat.add(Xn, 0n), U32.to_nat(nx), P, Equal.trans(Nat, Nat.add(Xn, 0n), Xn, U32.to_nat(nx), N.add_zero(Xn), Equal.sym(Nat, U32.to_nat(nx), Xn, eX)), hx)
      +eA = Equal.trans(Nat, U32.to_nat(C.Cir.at(nx)), PH.H.t20(U32.to_nat(nx)), PH.H.t20(Nat.add(Xn, 0n)), F.at.nat(nx, P, hP, hX),
        Equal.cong(Nat, Nat, z => PH.H.t20(z), U32.to_nat(nx), Nat.add(Xn, 0n), Equal.trans(Nat, U32.to_nat(nx), Xn, Nat.add(Xn, 0n), eX,
          Equal.sym(Nat, Nat.add(Xn, 0n), Xn, N.add_zero(Xn)))))
      +ge = A.ge.of(C.Cir.at(nx), ad, N.le_rw_r(AD, PH.H.t20(Nat.add(Xn, 0n)), U32.to_nat(C.Cir.at(nx)),
        Equal.sym(Nat, U32.to_nat(C.Cir.at(nx)), PH.H.t20(Nat.add(Xn, 0n)), eA), hf))
      S.steps.then(10n, 1n, pr.LC(X, a, n, nx, t, ad, rg, mm), pr.TC(X, a, n, nx, ad, rg, mm), pr.XC(X, a, n, ad, rg, mm, nx),
        pr.test(X, a, n, nx, t, ad, rg, mm), pr.exit(X, a, n, nx, ad, rg, mm, ge))
    case 1n+p:
      +AD = U32.to_nat(ad)
      # this round goes on: 20 Xn <= 20 (Xn + p) < E
      +e1 = Equal.trans(Nat, Nat.add(Xn, 1n+p), 1n+Nat.add(Xn, p), Nat.add(1n+Xn, p), N.add_succ_r(Xn, p), {==})
      +hX1 = N.le_rw_l(Nat.add(Xn, 1n+p), Nat.add(1n+Xn, p), P, e1, hx)
      +hXP = N.le_trans(1n+Xn, Nat.add(1n+Xn, p), P, N.le_add_r(1n+Xn, p), hX1)
      +hX = N.le_trans(U32.to_nat(nx), 1n+U32.to_nat(nx), P, N.le_succ(U32.to_nat(nx), U32.to_nat(nx), N.le_refl(U32.to_nat(nx))),
        N.le_rw_l(1n+Xn, 1n+U32.to_nat(nx), P, Equal.cong(Nat, Nat, z => 1n+z, Xn, U32.to_nat(nx), Equal.sym(Nat, U32.to_nat(nx), Xn, eX)), hXP))
      +eA = Equal.trans(Nat, U32.to_nat(C.Cir.at(nx)), PH.H.t20(U32.to_nat(nx)), PH.H.t20(Xn), F.at.nat(nx, P, hP, hX),
        Equal.cong(Nat, Nat, z => PH.H.t20(z), U32.to_nat(nx), Xn, eX))
      +hlt = N.le_trans(1n+PH.H.t20(Xn), 1n+PH.H.t20(Nat.add(Xn, p)), AD, PH.H.t20_mono(Xn, Nat.add(Xn, p), N.le_add_r(Xn, p)), hl)
      +nge = nge.of(C.Cir.at(nx), ad, N.le_rw_l(1n+PH.H.t20(Xn), 1n+U32.to_nat(C.Cir.at(nx)), AD,
        Equal.cong(Nat, Nat, z => 1n+z, PH.H.t20(Xn), U32.to_nat(C.Cir.at(nx)), Equal.sym(Nat, U32.to_nat(C.Cir.at(nx)), PH.H.t20(Xn), eA)), hlt))
      # the next round, from nx + 1
      +eX1 = Equal.trans(Nat, U32.to_nat(U32.add(nx, 1)), U32.to_nat(U32.inc(nx)), 1n+Xn,
        Equal.cong(U32, Nat, z => U32.to_nat(z), U32.add(nx, 1), U32.inc(nx), F.inc.add1(nx)),
        F.inc.eq(nx, Xn, eX, W, hW, N.le_rw_r(2n+Xn, PH.H.W(32n), W, Equal.sym(Nat, W, PH.H.W(32n), hW), PH.H.small(32n, Xn, P, hP, hXP))))
      +hl1 = pr.ll(p, Xn, AD, hl)
      +hf1 = N.le_rw_r(AD, PH.H.t20(Nat.add(Xn, 1n+p)), PH.H.t20(Nat.add(1n+Xn, p)),
        Equal.cong(Nat, Nat, z => PH.H.t20(z), Nat.add(Xn, 1n+p), Nat.add(1n+Xn, p), e1), hf)
      +LC1 = pr.LC(X, a, n, U32.add(nx, 1), nx, ad, rg, mm)
      S.steps.then(16n, Nat.add(s16(p), 11n), pr.LC(X, a, n, nx, t, ad, rg, mm), LC1, pr.XC(X, a, n, ad, rg, mm, addn(1n+p, nx)),
        S.steps.then(10n, 6n, pr.LC(X, a, n, nx, t, ad, rg, mm), pr.TC(X, a, n, nx, ad, rg, mm), LC1,
          pr.test(X, a, n, nx, t, ad, rg, mm), pr.more(X, a, n, nx, ad, rg, mm, nge)),
        pr.loop(p, X, a, n, U32.add(nx, 1), nx, ad, rg, mm, 1n+Xn, eX1, P, hP, W, hW, hX1, hl1, hf1))
