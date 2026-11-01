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
    case 1n+(+p):
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

# x + d after d steps of 1, below P
def addn.nat(d: Nat, +x: U32, +Xn: Nat, +eX: {U32.to_nat(x) == Xn : Nat}, +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hx: N.Le(Nat.add(Xn, d), P)) -> {U32.to_nat(addn(d, x)) == Nat.add(Xn, d) : Nat}:
  match d:
    case 0n:
      Equal.trans(Nat, U32.to_nat(x), Xn, Nat.add(Xn, 0n), eX, Equal.sym(Nat, Nat.add(Xn, 0n), Xn, N.add_zero(Xn)))
    case 1n+(+p):
      +e1 = Equal.trans(Nat, Nat.add(Xn, 1n+p), 1n+Nat.add(Xn, p), Nat.add(1n+Xn, p), N.add_succ_r(Xn, p), {==})
      +hX1 = N.le_rw_l(Nat.add(Xn, 1n+p), Nat.add(1n+Xn, p), P, e1, hx)
      +hXP = N.le_trans(1n+Xn, Nat.add(1n+Xn, p), P, N.le_add_r(1n+Xn, p), hX1)
      +eX1 = Equal.trans(Nat, U32.to_nat(U32.add(x, 1)), U32.to_nat(U32.inc(x)), 1n+Xn,
        Equal.cong(U32, Nat, z => U32.to_nat(z), U32.add(x, 1), U32.inc(x), F.inc.add1(x)),
        F.inc.eq(x, Xn, eX, W, hW, N.le_rw_r(2n+Xn, PH.H.W(32n), W, Equal.sym(Nat, W, PH.H.W(32n), hW), PH.H.small(32n, Xn, P, hP, hXP))))
      Equal.trans(Nat, U32.to_nat(addn(p, U32.add(x, 1))), Nat.add(1n+Xn, p), Nat.add(Xn, 1n+p),
        addn.nat(p, U32.add(x, 1), 1n+Xn, eX1, P, hP, W, hW, hX1), Equal.sym(Nat, Nat.add(Xn, 1n+p), Nat.add(1n+Xn, p), e1))

# 20 q as a product
def mul20(+q: Nat) -> {Nat.mul(q, 20n) == PH.H.t20(q) : Nat}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 20n+z, Nat.mul(p, 20n), PH.H.t20(p), mul20(p))

# 20 q <= 19 + 20 p gives q <= p
def t20.le19(+q: Nat, +p: Nat, h: N.Le(PH.H.t20(q), 19n+PH.H.t20(p))) -> N.Le(q, p):
  match q p:
    case 0n _:
      N.le_zero(p)
    case 1n+a 0n:
      Empty.absurd(N.Le(1n+a, 0n), N.not_succ_le(19n, N.le_trans(20n, 20n+PH.H.t20(a), 19n, N.le_add_r(20n, PH.H.t20(a)), h)))
    case 1n+a 1n+b:
      t20.le19(a, b, h)

# a quotient and a remainder by 20
def div.ex(+x: U32) -> Sigma<&2, &2, Nat, Qn => Sigma<&2, &2, Nat, Rn =>
  S.P2({Nat.add(Nat.mul(Qn, 20n), Rn) == U32.to_nat(x) : Nat}, N.Le(1n+Rn, 20n))>>:
  match x:
    case U32{+xw}:
      (Word.to_nat(32n, DV.dq(32n, U32.divmod.go(32n, xw, 20))), (U32.to_nat(DV.dr(32n, U32.divmod.go(32n, xw, 20))),
        DV.dm(32n, xw, 20, N.D(32n, 1n), Equal.cong(Nat, Nat, z => N.D(32n, z), PH.H.bn(True{}), 1n, {==}), N.D(31n, 1n),
          Equal.sym(Nat, N.D(32n, 1n), Nat.double(N.D(31n, 1n)), DV.dsucc(31n, 1n)), Unit{}, Unit{})))

# a >= b false gives a < b
def nge.to(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), e: {Cmp.is_ge(c) == False{} : Bool}) -> N.Le(1n+x, y):
  match c:
    case LT{}:
      r
    case EQ{}:
      Empty.absurd(N.Le(1n+x, y), N.true_ne_false(e))
    case GT{}:
      Empty.absurd(N.Le(1n+x, y), N.true_ne_false(e))

# The start of run
# ----------------

# run's frame as a call makes it, with the input's address a and length n
def pr.fr(+prog: C.Cir.Stmt, +regs: Nat, +k: U32, +a: U32, +n: U32) -> C.Wasm.Frame:
  C.Wasm.Frame{M.body(C.Cir.run(prog, regs, k)), [], 1n, [], List.append(&2, U32, [a, n], List.replicate(U32, 6n+regs, 0))}

def pr.code(+prog: C.Cir.Stmt) -> List<&2, C.Wasm.Instr>:
  C.Cir.code.stmt(prog, 0n, [])

def pr.rg(+regs: Nat) -> List<&2, U32>:
  List.replicate(U32, regs, 0)

def pr.pre(+prog: C.Cir.Stmt, +regs: Nat, +k: U32, +a: U32, +n: U32, +mm: C.Wasm.Memory) ->
  {PH.H.steps(10n, C.Wasm.Step.next{pr.fr(prog, regs, k, a, n), mm}) ==
    pr.LC(pr.code(prog), a, n, U32.inc(k), 0, U32.add(a, n), pr.rg(regs), mm) : C.Wasm.Step}:
  {==}

def pr.post(+X: List<&2, C.Wasm.Instr>, +a: U32, +n: U32, +ad: U32, +rg: List<&2, U32>, +mm: C.Wasm.Memory, +x: U32) ->
  {PH.H.steps(1n, pr.XC(X, a, n, ad, rg, mm, x)) == Q.Cfg(X, [T.RL()], [], Q.Loc(a, n, 2, x, 0, x, 0, ad, rg), mm) : C.Wasm.Step}:
  {==}

# the program's configuration, with next = first
def pr.PC(+prog: C.Cir.Stmt, +regs: Nat, +a: U32, +n: U32, +mm: C.Wasm.Memory, +x: U32) -> C.Wasm.Step:
  Q.Cfg(pr.code(prog), [T.RL()], [], Q.Loc(a, n, 2, x, 0, x, 0, U32.add(a, n), pr.rg(regs)), mm)

# run's start, its loop of d rounds, and the program's block
def pr.all(+d: Nat, +prog: C.Cir.Stmt, +regs: Nat, +k: U32, +a: U32, +n: U32, +mm: C.Wasm.Memory,
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hx: N.Le(Nat.add(U32.to_nat(U32.inc(k)), d), P), +hl: LL(d, U32.to_nat(U32.inc(k)), U32.to_nat(U32.add(a, n))),
  +hf: N.Le(U32.to_nat(U32.add(a, n)), PH.H.t20(Nat.add(U32.to_nat(U32.inc(k)), d)))) ->
  {PH.H.steps(Nat.add(10n, Nat.add(Nat.add(s16(d), 11n), 1n)), C.Wasm.Step.next{pr.fr(prog, regs, k, a, n), mm}) ==
    pr.PC(prog, regs, a, n, mm, addn(d, U32.inc(k))) : C.Wasm.Step}:
  +X = pr.code(prog)
  +ad = U32.add(a, n)
  +L0 = pr.LC(X, a, n, U32.inc(k), 0, ad, pr.rg(regs), mm)
  +XF = pr.XC(X, a, n, ad, pr.rg(regs), mm, addn(d, U32.inc(k)))
  S.steps.then(10n, Nat.add(Nat.add(s16(d), 11n), 1n), C.Wasm.Step.next{pr.fr(prog, regs, k, a, n), mm}, L0,
    pr.PC(prog, regs, a, n, mm, addn(d, U32.inc(k))), pr.pre(prog, regs, k, a, n, mm),
    S.steps.then(Nat.add(s16(d), 11n), 1n, L0, XF, pr.PC(prog, regs, a, n, mm, addn(d, U32.inc(k))),
      pr.loop(d, X, a, n, U32.inc(k), 0, ad, pr.rg(regs), mm, U32.to_nat(U32.inc(k)), {==}, P, hP, W, hW, hx, hl, hf),
      pr.post(X, a, n, ad, pr.rg(regs), mm, addn(d, U32.inc(k)))))

# a run of run's start that reaches the program's block with next = x
def PRE(+prog: C.Cir.Stmt, +regs: Nat, +k: U32, +a: U32, +n: U32, +mm: C.Wasm.Memory, +x: U32) -> Data:
  S.EX(N2 => {PH.H.steps(N2, C.Wasm.Step.next{pr.fr(prog, regs, k, a, n), mm}) == pr.PC(prog, regs, a, n, mm, x) : C.Wasm.Step})

# 20 (k + 1) is at or past the end: no round
def pr.at(+prog: C.Cir.Stmt, +regs: Nat, +k: U32, +a: U32, +n: U32, +mm: C.Wasm.Memory,
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hX0: N.Le(U32.to_nat(U32.inc(k)), P), e: {U32.is_ge(C.Cir.at(U32.inc(k)), U32.add(a, n)) == True{} : Bool}) ->
  PRE(prog, regs, k, a, n, mm, U32.inc(k)):
  +X0 = U32.to_nat(U32.inc(k))
  +E = U32.to_nat(U32.add(a, n))
  +hx = N.le_rw_l(X0, Nat.add(X0, 0n), P, Equal.sym(Nat, Nat.add(X0, 0n), X0, N.add_zero(X0)), hX0)
  +hge = DV.ge.le(U32.cmp(C.Cir.at(U32.inc(k)), U32.add(a, n)), U32.to_nat(C.Cir.at(U32.inc(k))), E, N.U32.rel(C.Cir.at(U32.inc(k)), U32.add(a, n)), e)
  +eA = Equal.trans(Nat, U32.to_nat(C.Cir.at(U32.inc(k))), PH.H.t20(X0), PH.H.t20(Nat.add(X0, 0n)), F.at.nat(U32.inc(k), P, hP, hX0),
    Equal.cong(Nat, Nat, z => PH.H.t20(z), X0, Nat.add(X0, 0n), Equal.sym(Nat, Nat.add(X0, 0n), X0, N.add_zero(X0))))
  +hf = N.le_rw_r(E, U32.to_nat(C.Cir.at(U32.inc(k))), PH.H.t20(Nat.add(X0, 0n)), eA, hge)
  (Nat.add(10n, Nat.add(Nat.add(s16(0n), 11n), 1n)), pr.all(0n, prog, regs, k, a, n, mm, P, hP, W, hW, hx, Unit{}, hf))

# 20 (k + 1) is before the end E, and E - 1 = 20 Qn + Rn: the rounds up to Qn + 1
def pr.q(+prog: C.Cir.Stmt, +regs: Nat, +k: U32, +a: U32, +n: U32, +mm: C.Wasm.Memory,
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hX0: N.Le(U32.to_nat(U32.inc(k)), P), +hE: N.Le(U32.to_nat(U32.add(a, n)), PH.H.t20(P)),
  +hlt0: N.Le(1n+PH.H.t20(U32.to_nat(U32.inc(k))), U32.to_nat(U32.add(a, n))),
  +Qn: Nat, +Rn: Nat, +eQ: {Nat.add(Nat.mul(Qn, 20n), Rn) == U32.to_nat(U32.sub(U32.add(a, n), 1)) : Nat}, +hR: N.Le(1n+Rn, 20n)) ->
  PRE(prog, regs, k, a, n, mm, U32.inc(U32.div(U32.sub(U32.add(a, n), 1), 20))):
  +X0 = U32.to_nat(U32.inc(k))
  +ad = U32.add(a, n)
  +E = U32.to_nat(ad)
  +TQ = PH.H.t20(Qn)
  # 1 + 20 Qn + Rn = E
  +h1E = N.le_trans(1n, 1n+PH.H.t20(X0), E, N.le_add_r(1n, PH.H.t20(X0)), hlt0)
  +eT = Equal.trans(Nat, 1n+Nat.add(TQ, Rn), 1n+U32.to_nat(U32.sub(ad, 1)), E,
    Equal.cong(Nat, Nat, z => 1n+z, Nat.add(TQ, Rn), U32.to_nat(U32.sub(ad, 1)),
      Equal.trans(Nat, Nat.add(TQ, Rn), Nat.add(Nat.mul(Qn, 20n), Rn), U32.to_nat(U32.sub(ad, 1)),
        Equal.cong(Nat, Nat, z => Nat.add(z, Rn), TQ, Nat.mul(Qn, 20n), Equal.sym(Nat, Nat.mul(Qn, 20n), TQ, mul20(Qn))), eQ)),
    Z.dec.nat(ad, h1E))
  # 1 + 20 Qn <= E <= 20 (Qn + 1)
  +hl0 = N.le_rw_r(1n+TQ, 1n+Nat.add(TQ, Rn), E, eT, N.le_add_r(1n+TQ, Rn))
  +hEQ = N.le_rw_l(1n+Nat.add(TQ, Rn), E, 20n+TQ, eT,
    N.le_rw_r(1n+Nat.add(TQ, Rn), 1n+Nat.add(TQ, 19n), 20n+TQ,
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(TQ, 19n), Nat.add(19n, TQ), Z.add.comm(TQ, 19n)),
      N.add_mono(TQ, TQ, Rn, 19n, N.le_refl(TQ), hR)))
  # X0 <= Qn < P
  +hXQ = PH.H.t20_lt(X0, 1n+Qn, N.le_trans(1n+PH.H.t20(X0), E, 20n+TQ, hlt0, hEQ))
  +hQP = PH.H.t20_lt(Qn, P, N.le_trans(1n+TQ, E, PH.H.t20(P), hl0, hE))
  +d1 = Nat.sub(Qn, X0)
  +eQd = Equal.trans(Nat, Nat.add(X0, d1), Nat.add(d1, X0), Qn, Z.add.comm(X0, d1), Z.sub.add(Qn, X0, hXQ))
  +eQd2 = Equal.trans(Nat, Nat.add(X0, 1n+d1), 1n+Nat.add(X0, d1), 1n+Qn, N.add_succ_r(X0, d1),
    Equal.cong(Nat, Nat, z => 1n+z, Nat.add(X0, d1), Qn, eQd))
  +hx = N.le_rw_l(1n+Qn, Nat.add(X0, 1n+d1), P, Equal.sym(Nat, Nat.add(X0, 1n+d1), 1n+Qn, eQd2), hQP)
  +hl = N.le_rw_l(1n+TQ, 1n+PH.H.t20(Nat.add(X0, d1)), E,
    Equal.cong(Nat, Nat, z => 1n+PH.H.t20(z), Qn, Nat.add(X0, d1), Equal.sym(Nat, Nat.add(X0, d1), Qn, eQd)), hl0)
  +hf = N.le_rw_r(E, 20n+TQ, PH.H.t20(Nat.add(X0, 1n+d1)),
    Equal.cong(Nat, Nat, z => PH.H.t20(z), 1n+Qn, Nat.add(X0, 1n+d1), Equal.sym(Nat, Nat.add(X0, 1n+d1), 1n+Qn, eQd2)), hEQ)
  # the loop stops at Qn + 1, which is (E - 1) / 20 + 1
  +F1 = addn(1n+d1, U32.inc(k))
  +eN = Equal.trans(Nat, U32.to_nat(F1), Nat.add(X0, 1n+d1), 1n+Qn, addn.nat(1n+d1, U32.inc(k), X0, {==}, P, hP, W, hW, hx), eQd2)
  +eF = Equal.trans(U32, F1, U32.from_nat(U32.to_nat(F1)), U32.inc(U32.div(U32.sub(ad, 1), 20)),
    Equal.sym(U32, U32.from_nat(U32.to_nat(F1)), F1, Z.from.to(F1)),
    Equal.trans(U32, U32.from_nat(U32.to_nat(F1)), U32.from_nat(1n+Qn), U32.inc(U32.div(U32.sub(ad, 1), 20)),
      Equal.cong(Nat, U32, z => U32.from_nat(z), U32.to_nat(F1), 1n+Qn, eN),
      Equal.cong(U32, U32, z => U32.inc(z), U32.from_nat(Qn), U32.div(U32.sub(ad, 1), 20),
        Equal.sym(U32, U32.div(U32.sub(ad, 1), 20), U32.from_nat(Qn), DV.div.twenty(U32.sub(ad, 1), Qn, Rn, eQ, hR)))))
  +N2 = Nat.add(10n, Nat.add(Nat.add(s16(1n+d1), 11n), 1n))
  (N2, (%eF : {PH.H.steps(N2, C.Wasm.Step.next{pr.fr(prog, regs, k, a, n), mm}) == pr.PC(prog, regs, a, n, mm, _) : C.Wasm.Step};
    pr.all(1n+d1, prog, regs, k, a, n, mm, P, hP, W, hW, hx, hl, hf)))

def pr.qr(+prog: C.Cir.Stmt, +regs: Nat, +k: U32, +a: U32, +n: U32, +mm: C.Wasm.Memory,
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hX0: N.Le(U32.to_nat(U32.inc(k)), P), +hE: N.Le(U32.to_nat(U32.add(a, n)), PH.H.t20(P)),
  +hlt0: N.Le(1n+PH.H.t20(U32.to_nat(U32.inc(k))), U32.to_nat(U32.add(a, n))),
  qr: Sigma<&2, &2, Nat, Qn => Sigma<&2, &2, Nat, Rn =>
    S.P2({Nat.add(Nat.mul(Qn, 20n), Rn) == U32.to_nat(U32.sub(U32.add(a, n), 1)) : Nat}, N.Le(1n+Rn, 20n))>>) ->
  PRE(prog, regs, k, a, n, mm, U32.inc(U32.div(U32.sub(U32.add(a, n), 1), 20))):
  (+Qn, q1) = qr
  (+Rn, q2) = q1
  (+eQ, +hR) = q2
  pr.q(prog, regs, k, a, n, mm, P, hP, W, hW, hX0, hE, hlt0, Qn, Rn, eQ, hR)

# by the test of 20 (k + 1) against the end
def pr.cs(b: Bool, +prog: C.Cir.Stmt, +regs: Nat, +k: U32, +a: U32, +n: U32, +mm: C.Wasm.Memory,
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hX0: N.Le(U32.to_nat(U32.inc(k)), P), +hE: N.Le(U32.to_nat(U32.add(a, n)), PH.H.t20(P)),
  e: {U32.is_ge(C.Cir.at(U32.inc(k)), U32.add(a, n)) == b : Bool}) ->
  PRE(prog, regs, k, a, n, mm, Bool.pick(U32, b, U32.inc(k), U32.inc(U32.div(U32.sub(U32.add(a, n), 1), 20)))):
  match b:
    case True{}:
      pr.at(prog, regs, k, a, n, mm, P, hP, W, hW, hX0, e)
    case False{}:
      +ad = U32.add(a, n)
      +E = U32.to_nat(ad)
      +X0 = U32.to_nat(U32.inc(k))
      +hlt0 = N.le_rw_l(1n+U32.to_nat(C.Cir.at(U32.inc(k))), 1n+PH.H.t20(X0), E,
        Equal.cong(Nat, Nat, z => 1n+z, U32.to_nat(C.Cir.at(U32.inc(k))), PH.H.t20(X0), F.at.nat(U32.inc(k), P, hP, hX0)),
        nge.to(U32.cmp(C.Cir.at(U32.inc(k)), ad), U32.to_nat(C.Cir.at(U32.inc(k))), E, N.U32.rel(C.Cir.at(U32.inc(k)), ad), e))
      pr.qr(prog, regs, k, a, n, mm, P, hP, W, hW, hX0, hE, hlt0, div.ex(U32.sub(ad, 1)))

# run's start reaches the program's block with next = Cir.first(k, a + n)
def pr.go(+prog: C.Cir.Stmt, +regs: Nat, +k: U32, +a: U32, +n: U32, +mm: C.Wasm.Memory,
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hX0: N.Le(U32.to_nat(U32.inc(k)), P), +hE: N.Le(U32.to_nat(U32.add(a, n)), PH.H.t20(P))) ->
  PRE(prog, regs, k, a, n, mm, C.Cir.first(k, U32.add(a, n))):
  pr.cs(U32.is_ge(C.Cir.at(U32.inc(k)), U32.add(a, n)), prog, regs, k, a, n, mm, P, hP, W, hW, hX0, hE, {==})
