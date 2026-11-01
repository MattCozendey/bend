# compiler: the simulation of Cir's expressions
# =============================================
#
# sim.expr: when Cir.eval(e, st) == Some{v} and the run holds st (Inv of
# proof_sim_inv.bend), the code of e pushes v in cost(e) steps, and changes
# no local but tmp, to tmpE(e, t, st).

import Base
import ./impl.bend as C
import ./proof_need.bend as N
import ./proof_instrs.bend as I
import ./proof_halt.bend as PH
import ./proof_module.bend as M
import ./proof_valid.bend as V
import ./proof_sim_step.bend as S
import ./proof_sim_mem.bend as Y
import ./proof_sim_inv.bend as Q

# Inversions of Cir.eval
# ----------------------
#
# What a value of Cir.eval says of the values of its parts, with D(m), the
# value of m, for the value that each part has.

def D(m: Maybe<&2, U32>) -> U32:
  Maybe.default(&2, U32, m, 0)

def inv.op.a(+o: C.Wasm.Op, ma: Maybe<&2, U32>, mb: Maybe<&2, U32>, -v: U32,
  e: {C.Cir.eval.op(o, ma, mb) == Some{v} : Maybe<&2, U32>}) -> {ma == Some{D(ma)} : Maybe<&2, U32>}:
  match ma mb:
    case Some{+x} Some{+y}:
      {==}
    case None{} _:
      Empty.absurd({None{} == Some{D(None{})} : Maybe<&2, U32>}, Q.none.some(v, e))
    case Some{+x} None{}:
      {==}

def inv.op.b(+o: C.Wasm.Op, ma: Maybe<&2, U32>, mb: Maybe<&2, U32>, -v: U32,
  e: {C.Cir.eval.op(o, ma, mb) == Some{v} : Maybe<&2, U32>}) -> {mb == Some{D(mb)} : Maybe<&2, U32>}:
  match ma mb:
    case Some{+x} Some{+y}:
      {==}
    case None{} Some{+y}:
      {==}
    case _ None{}:
      Empty.absurd({None{} == Some{D(None{})} : Maybe<&2, U32>}, Q.none.some(v, e))

def inv.op.v(+o: C.Wasm.Op, ma: Maybe<&2, U32>, mb: Maybe<&2, U32>, -v: U32,
  e: {C.Cir.eval.op(o, ma, mb) == Some{v} : Maybe<&2, U32>}) -> {C.Wasm.op(o, D(ma), D(mb)) == v : U32}:
  match ma mb:
    case Some{+x} Some{+y}:
      Q.some.inj(C.Wasm.op(o, x, y), v, e)
    case None{} _:
      Empty.absurd({C.Wasm.op(o, D(None{}), D(mb)) == v : U32}, Q.none.some(v, e))
    case Some{+x} None{}:
      Empty.absurd({C.Wasm.op(o, x, D(None{})) == v : U32}, Q.none.some(v, e))

def inv.eqz.a(ma: Maybe<&2, U32>, -v: U32, e: {C.Cir.eval.eqz(ma) == Some{v} : Maybe<&2, U32>}) -> {ma == Some{D(ma)} : Maybe<&2, U32>}:
  match ma:
    case Some{+x}:
      {==}
    case None{}:
      Empty.absurd({None{} == Some{D(None{})} : Maybe<&2, U32>}, Q.none.some(v, e))

def inv.eqz.v(ma: Maybe<&2, U32>, -v: U32, e: {C.Cir.eval.eqz(ma) == Some{v} : Maybe<&2, U32>}) ->
  {Bool.to_u32(U32.is_zero(D(ma))) == v : U32}:
  match ma:
    case Some{+x}:
      Q.some.inj(Bool.to_u32(U32.is_zero(x)), v, e)
    case None{}:
      Empty.absurd({Bool.to_u32(U32.is_zero(D(None{}))) == v : U32}, Q.none.some(v, e))

def inv.field.if.ok(b: Bool, +k: Nat, +cl: C.Cir.Cells, +i: U32, -v: U32,
  e: {C.Cir.eval.field.if(b, k, cl, i) == Some{v} : Maybe<&2, U32>}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Q.none.some(v, e))

def inv.field.if.v(b: Bool, +k: Nat, +cl: C.Cir.Cells, +i: U32, -v: U32,
  e: {C.Cir.eval.field.if(b, k, cl, i) == Some{v} : Maybe<&2, U32>}) -> {C.Cir.Cell.get(k, C.Cir.Cells.get(cl, i)) == v : U32}:
  match b:
    case True{}:
      Q.some.inj(C.Cir.Cell.get(k, C.Cir.Cells.get(cl, i)), v, e)
    case False{}:
      Empty.absurd({C.Cir.Cell.get(k, C.Cir.Cells.get(cl, i)) == v : U32}, Q.none.some(v, e))

def inv.field.c(+k: Nat, mc: Maybe<&2, U32>, +rg: List<&2, U32>, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32, -v: U32,
  e: {C.Cir.eval.field(k, mc, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)) == Some{v} : Maybe<&2, U32>}) ->
  {mc == Some{D(mc)} : Maybe<&2, U32>}:
  match mc:
    case Some{+i}:
      {==}
    case None{}:
      Empty.absurd({None{} == Some{D(None{})} : Maybe<&2, U32>}, Q.none.some(v, e))

def inv.field.ok(+k: Nat, mc: Maybe<&2, U32>, +rg: List<&2, U32>, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32, -v: U32,
  e: {C.Cir.eval.field(k, mc, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)) == Some{v} : Maybe<&2, U32>}) ->
  {C.Cir.is_cell(D(mc), im, fi, nx) == True{} : Bool}:
  match mc:
    case Some{+i}:
      inv.field.if.ok(C.Cir.is_cell(i, im, fi, nx), k, cl, i, v, e)
    case None{}:
      Empty.absurd({C.Cir.is_cell(D(None{}), im, fi, nx) == True{} : Bool}, Q.none.some(v, e))

def inv.field.v(+k: Nat, mc: Maybe<&2, U32>, +rg: List<&2, U32>, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32, -v: U32,
  e: {C.Cir.eval.field(k, mc, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)) == Some{v} : Maybe<&2, U32>}) ->
  {C.Cir.Cell.get(k, C.Cir.Cells.get(cl, D(mc))) == v : U32}:
  match mc:
    case Some{+i}:
      inv.field.if.v(C.Cir.is_cell(i, im, fi, nx), k, cl, i, v, e)
    case None{}:
      Empty.absurd({C.Cir.Cell.get(k, C.Cir.Cells.get(cl, D(None{}))) == v : U32}, Q.none.some(v, e))

def inv.byte.of.b(mb: Maybe<&2, U32>, -v: U32, e: {C.Cir.eval.byte.of(mb) == Some{v} : Maybe<&2, U32>}) -> {mb == Some{D(mb)} : Maybe<&2, U32>}:
  match mb:
    case Some{+b}:
      {==}
    case None{}:
      Empty.absurd({None{} == Some{D(None{})} : Maybe<&2, U32>}, Q.none.some(v, e))

def inv.byte.of.v(mb: Maybe<&2, U32>, -v: U32, e: {C.Cir.eval.byte.of(mb) == Some{v} : Maybe<&2, U32>}) -> {U32.and(D(mb), 255) == v : U32}:
  match mb:
    case Some{+b}:
      Q.some.inj(U32.and(b, 255), v, e)
    case None{}:
      Empty.absurd({U32.and(D(None{}), 255) == v : U32}, Q.none.some(v, e))

# the byte that the index i reads
def BI(mi: Maybe<&2, U32>, +inp: List<&2, U32>) -> Maybe<&2, U32>:
  List.get(&2, U32, inp, U32.to_nat(D(mi)))

def inv.byte.i(mi: Maybe<&2, U32>, +inp: List<&2, U32>, -v: U32, e: {C.Cir.eval.byte(mi, inp) == Some{v} : Maybe<&2, U32>}) ->
  {mi == Some{D(mi)} : Maybe<&2, U32>}:
  match mi:
    case Some{+x}:
      {==}
    case None{}:
      Empty.absurd({None{} == Some{D(None{})} : Maybe<&2, U32>}, Q.none.some(v, e))

def inv.byte.b(mi: Maybe<&2, U32>, +inp: List<&2, U32>, -v: U32, e: {C.Cir.eval.byte(mi, inp) == Some{v} : Maybe<&2, U32>}) ->
  {BI(mi, inp) == Some{D(BI(mi, inp))} : Maybe<&2, U32>}:
  match mi:
    case Some{+x}:
      inv.byte.of.b(List.get(&2, U32, inp, U32.to_nat(x)), v, e)
    case None{}:
      Empty.absurd({BI(None{}, inp) == Some{D(BI(None{}, inp))} : Maybe<&2, U32>}, Q.none.some(v, e))

def inv.byte.v(mi: Maybe<&2, U32>, +inp: List<&2, U32>, -v: U32, e: {C.Cir.eval.byte(mi, inp) == Some{v} : Maybe<&2, U32>}) ->
  {U32.and(D(BI(mi, inp)), 255) == v : U32}:
  match mi:
    case Some{+x}:
      inv.byte.of.v(List.get(&2, U32, inp, U32.to_nat(x)), v, e)
    case None{}:
      Empty.absurd({U32.and(D(BI(None{}, inp)), 255) == v : U32}, Q.none.some(v, e))

# Steps of the code of an expression
# ----------------------------------

# the steps that the code of e takes
def cost(e: C.Cir.Expr) -> Nat:
  match e:
    case C.Cir.Expr.const{_}:
      1n
    case C.Cir.Expr.get{_}:
      1n
    case C.Cir.Expr.op{_, a, b}:
      Nat.add(cost(a), Nat.add(cost(b), 1n))
    case C.Cir.Expr.eqz{a}:
      Nat.add(cost(a), 1n)
    case C.Cir.Expr.field{_, c}:
      Nat.add(cost(c), 8n)
    case C.Cir.Expr.byte{i}:
      Nat.add(cost(i), 5n)
    case C.Cir.Expr.size{}:
      1n

# the cell number c on the stack becomes its first byte, and tmp holds it
def at.steps(+c: U32, +k: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +stk: List<&2, U32>,
  +a: U32, +n: U32, +s: U32, +nx: U32, +on: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +mem: C.Wasm.Memory) ->
  {PH.H.steps(7n, Q.Cfg(C.Cir.code.at(k), ls, Con{c, stk}, Q.Loc(a, n, s, nx, on, t, nd, ad, rg), mem)) ==
    Q.Cfg(k, ls, Con{C.Cir.at(c), stk}, Q.Loc(a, n, s, nx, on, c, nd, ad, rg), mem) : C.Wasm.Step}:
  {==}

# a load of a word inside the memory
def load.step(+o: U32, +x: U32, +k: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +stk: List<&2, U32>,
  +loc: List<&2, U32>, +pg: U32, +lm: U32, +m: C.Wasm.Bytes,
  hin: {C.Wasm.inside(pg, x, o, 4) == True{} : Bool}) ->
  {PH.H.steps(1n, Q.Cfg(Con{C.Wasm.Instr.load{o}, k}, ls, Con{x, stk}, loc, C.Wasm.Memory{pg, lm, m})) ==
    Q.Cfg(k, ls, Con{Y.V32(m, U32.add(x, o)), stk}, loc, C.Wasm.Memory{pg, lm, m}) : C.Wasm.Step}:
  %Equal.sym(Bool, C.Wasm.inside(pg, x, o, 4), True{}, hin) :
    {C.Wasm.step.loaded(_, U32.is_eq(4, 4), U32.add(x, o), k, ls, 1n, stk, loc, C.Wasm.Memory{pg, lm, m}) ==
      Q.Cfg(k, ls, Con{Y.V32(m, U32.add(x, o)), stk}, loc, C.Wasm.Memory{pg, lm, m}) : C.Wasm.Step}
  %Equal.sym(C.Wasm.Peek, C.Wasm.read32(m, U32.add(x, o)), C.Wasm.Peek{Y.V32(m, U32.add(x, o)), m}, Y.read32.eq(m, U32.add(x, o))) :
    {C.Wasm.step.peeked(_, pg, lm, k, ls, 1n, stk, loc) ==
      Q.Cfg(k, ls, Con{Y.V32(m, U32.add(x, o)), stk}, loc, C.Wasm.Memory{pg, lm, m}) : C.Wasm.Step}
  {==}

# a load of a byte inside the memory
def load8.step(+x: U32, +k: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +stk: List<&2, U32>,
  +loc: List<&2, U32>, +pg: U32, +lm: U32, +m: C.Wasm.Bytes,
  hin: {C.Wasm.inside(pg, x, 0, 1) == True{} : Bool}) ->
  {PH.H.steps(1n, Q.Cfg(Con{C.Wasm.Instr.load8_u{0}, k}, ls, Con{x, stk}, loc, C.Wasm.Memory{pg, lm, m})) ==
    Q.Cfg(k, ls, Con{Y.R8(m, U32.add(x, 0)), stk}, loc, C.Wasm.Memory{pg, lm, m}) : C.Wasm.Step}:
  %Equal.sym(Bool, C.Wasm.inside(pg, x, 0, 1), True{}, hin) :
    {C.Wasm.step.loaded(_, U32.is_eq(1, 4), U32.add(x, 0), k, ls, 1n, stk, loc, C.Wasm.Memory{pg, lm, m}) ==
      Q.Cfg(k, ls, Con{Y.R8(m, U32.add(x, 0)), stk}, loc, C.Wasm.Memory{pg, lm, m}) : C.Wasm.Step}
  %Equal.sym(C.Wasm.Peek, C.Wasm.read8(m, U32.add(x, 0)), C.Wasm.Peek{Y.R8(m, U32.add(x, 0)), m}, Y.read8.eq(m, U32.add(x, 0))) :
    {C.Wasm.step.peeked(_, pg, lm, k, ls, 1n, stk, loc) ==
      Q.Cfg(k, ls, Con{Y.R8(m, U32.add(x, 0)), stk}, loc, C.Wasm.Memory{pg, lm, m}) : C.Wasm.Step}
  {==}

# the top of the stack, rewritten
def fix.top(-N: Nat, -X: C.Wasm.Step, -k: List<&2, C.Wasm.Instr>, -ls: List<&2, C.Wasm.Label>, -stk: List<&2, U32>,
  -loc: List<&2, U32>, -mem: C.Wasm.Memory, -x: U32, -y: U32,
  h: {PH.H.steps(N, X) == Q.Cfg(k, ls, Con{x, stk}, loc, mem) : C.Wasm.Step}, e: {x == y : U32}) ->
  {PH.H.steps(N, X) == Q.Cfg(k, ls, Con{y, stk}, loc, mem) : C.Wasm.Step}:
  %e : {PH.H.steps(N, X) == Q.Cfg(k, ls, Con{_, stk}, loc, mem) : C.Wasm.Step}
  h

# the value of tmp after the code of e
def tmpE(e: C.Cir.Expr, +t: U32, +st: C.Cir.State) -> U32:
  match e:
    case C.Cir.Expr.const{_}:
      t
    case C.Cir.Expr.get{_}:
      t
    case C.Cir.Expr.op{_, a, b}:
      tmpE(b, tmpE(a, t, st), st)
    case C.Cir.Expr.eqz{a}:
      tmpE(a, t, st)
    case C.Cir.Expr.field{_, c}:
      D(C.Cir.eval(c, st))
    case C.Cir.Expr.byte{i}:
      tmpE(i, t, st)
    case C.Cir.Expr.size{}:
      t

# The simulation of expressions
# -----------------------------

# when Cir.eval(e, st) gives v, the code of e pushes v in cost(e) steps; the
# registers are below R, and 8 + R below MX, so that register r is local
# 8 + r
def sim.expr(e: C.Cir.Expr, +rg: List<&2, U32>, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32, +v: U32,
  +ev: {C.Cir.eval(e, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)) == Some{v} : Maybe<&2, U32>},
  +R: Nat, +MX: U32, +ok: {V.ok.expr(e, R) == True{} : Bool}, +hR: N.Le(8n+R, U32.to_nat(MX)),
  +k: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +stk: List<&2, U32>,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +s: U32, +t: U32, +nd: U32, +ad: U32, +m: C.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m)) ->
  {PH.H.steps(cost(e), Q.Cfg(C.Cir.code.expr(e, k), ls, stk, Q.Loc(a, n, s, nx, on, t, nd, ad, rg), C.Wasm.Memory{pg, lm, m})) ==
    Q.Cfg(k, ls, Con{v, stk}, Q.Loc(a, n, s, nx, on, tmpE(e, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg), C.Wasm.Memory{pg, lm, m}) : C.Wasm.Step}:
  match e:
    case C.Cir.Expr.const{+c}:
      +L = Q.Loc(a, n, s, nx, on, t, nd, ad, rg)
      +MM = {C.Wasm.Memory{pg, lm, m} : C.Wasm.Memory}
      fix.top(1n, Q.Cfg(Con{C.Cir.i.const(c), k}, ls, stk, L, MM), k, ls, stk, L, MM, c, v, {==}, Q.some.inj(c, v, ev))
    case C.Cir.Expr.get{+r}:
      +L = Q.Loc(a, n, s, nx, on, t, nd, ad, rg)
      +MM = {C.Wasm.Memory{pg, lm, m} : C.Wasm.Memory}
      +le = N.le_trans(8n+r, 8n+R, U32.to_nat(MX), N.weaken(r, R, M.lt_le(r, R, ok)), hR)
      +eqr = Equal.trans(Nat, U32.to_nat(C.Cir.l.reg(r)), U32.to_nat(U32.from_nat(8n+r)), 8n+r,
        Equal.cong(U32, Nat, z => U32.to_nat(z), C.Cir.l.reg(r), U32.from_nat(8n+r), V.add8(r)), M.tofrom(8n+r, MX, le))
      +e2 = Equal.cong(Nat, U32, z => Maybe.default(&2, U32, List.get(&2, U32, L, z), 0), U32.to_nat(C.Cir.l.reg(r)), 8n+r, eqr)
      +e3 = Equal.cong(Maybe<&2, U32>, U32, z => Maybe.default(&2, U32, z, 0), List.get(&2, U32, rg, r), Some{v}, ev)
      fix.top(1n, Q.Cfg(Con{C.Cir.i.get(C.Cir.l.reg(r)), k}, ls, stk, L, MM), k, ls, stk, L, MM,
        Maybe.default(&2, U32, List.get(&2, U32, L, U32.to_nat(C.Cir.l.reg(r))), 0), v, {==},
        Equal.trans(U32, Maybe.default(&2, U32, List.get(&2, U32, L, U32.to_nat(C.Cir.l.reg(r))), 0),
          Maybe.default(&2, U32, List.get(&2, U32, rg, r), 0), v, e2, e3))
    case C.Cir.Expr.op{+o, +a1, +b1}:
      +st = Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)
      +MM = {C.Wasm.Memory{pg, lm, m} : C.Wasm.Memory}
      +ma = C.Cir.eval(a1, st)
      +mb = C.Cir.eval(b1, st)
      +va = D(ma)
      +vb = D(mb)
      +ta = tmpE(a1, t, st)
      +tb = tmpE(b1, ta, st)
      +K2 = {Con{C.Cir.i.op(o), k} : List<&2, C.Wasm.Instr>}
      +K1 = C.Cir.code.expr(b1, K2)
      +ha = sim.expr(a1, rg, cl, nx, fi, im, pg, lm, inp, ou, on, va, inv.op.a(o, ma, mb, v, ev), R, MX,
        I.and.l(V.ok.expr(a1, R), V.ok.expr(b1, R), ok), hR, K1, ls, stk, P, G, a, n, s, t, nd, ad, m, hI)
      +hb = sim.expr(b1, rg, cl, nx, fi, im, pg, lm, inp, ou, on, vb, inv.op.b(o, ma, mb, v, ev), R, MX,
        I.and.r(V.ok.expr(a1, R), V.ok.expr(b1, R), ok), hR, K2, ls, Con{va, stk}, P, G, a, n, s, ta, nd, ad, m, hI)
      +X0 = Q.Cfg(C.Cir.code.expr(a1, K1), ls, stk, Q.Loc(a, n, s, nx, on, t, nd, ad, rg), MM)
      +X1 = Q.Cfg(K1, ls, Con{va, stk}, Q.Loc(a, n, s, nx, on, ta, nd, ad, rg), MM)
      +X2 = Q.Cfg(K2, ls, Con{vb, Con{va, stk}}, Q.Loc(a, n, s, nx, on, tb, nd, ad, rg), MM)
      +X3 = Q.Cfg(k, ls, Con{C.Wasm.op(o, va, vb), stk}, Q.Loc(a, n, s, nx, on, tb, nd, ad, rg), MM)
      fix.top(Nat.add(cost(a1), Nat.add(cost(b1), 1n)), X0, k, ls, stk, Q.Loc(a, n, s, nx, on, tb, nd, ad, rg), MM,
        C.Wasm.op(o, va, vb), v,
        S.steps.then(cost(a1), Nat.add(cost(b1), 1n), X0, X1, X3, ha, S.steps.then(cost(b1), 1n, X1, X2, X3, hb, {==})),
        inv.op.v(o, ma, mb, v, ev))
    case C.Cir.Expr.eqz{+a1}:
      +st = Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)
      +MM = {C.Wasm.Memory{pg, lm, m} : C.Wasm.Memory}
      +ma = C.Cir.eval(a1, st)
      +va = D(ma)
      +ta = tmpE(a1, t, st)
      +K1 = {Con{C.Wasm.Instr.eqz{}, k} : List<&2, C.Wasm.Instr>}
      +ha = sim.expr(a1, rg, cl, nx, fi, im, pg, lm, inp, ou, on, va, inv.eqz.a(ma, v, ev), R, MX, ok, hR, K1, ls, stk,
        P, G, a, n, s, t, nd, ad, m, hI)
      +X0 = Q.Cfg(C.Cir.code.expr(a1, K1), ls, stk, Q.Loc(a, n, s, nx, on, t, nd, ad, rg), MM)
      +X1 = Q.Cfg(K1, ls, Con{va, stk}, Q.Loc(a, n, s, nx, on, ta, nd, ad, rg), MM)
      +X2 = Q.Cfg(k, ls, Con{Bool.to_u32(U32.is_zero(va)), stk}, Q.Loc(a, n, s, nx, on, ta, nd, ad, rg), MM)
      fix.top(Nat.add(cost(a1), 1n), X0, k, ls, stk, Q.Loc(a, n, s, nx, on, ta, nd, ad, rg), MM,
        Bool.to_u32(U32.is_zero(va)), v, S.steps.then(cost(a1), 1n, X0, X1, X2, ha, {==}), inv.eqz.v(ma, v, ev))
    case C.Cir.Expr.field{+kf, +c1}:
      +st = Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)
      +MM = {C.Wasm.Memory{pg, lm, m} : C.Wasm.Memory}
      +mc = C.Cir.eval(c1, st)
      +i = D(mc)
      +tc = tmpE(c1, t, st)
      +o = U32.shln(U32.from_nat(kf), 2n)
      +K2 = {Con{C.Wasm.Instr.load{o}, k} : List<&2, C.Wasm.Instr>}
      +K1 = C.Cir.code.at(K2)
      +okk = I.and.l(Nat.is_le(kf, 4n), V.ok.expr(c1, R), ok)
      +okc = I.and.r(Nat.is_le(kf, 4n), V.ok.expr(c1, R), ok)
      +cel = inv.field.ok(kf, mc, rg, cl, nx, fi, im, pg, lm, inp, ou, on, v, ev)
      +hc = sim.expr(c1, rg, cl, nx, fi, im, pg, lm, inp, ou, on, i, inv.field.c(kf, mc, rg, cl, nx, fi, im, pg, lm, inp, ou, on, v, ev),
        R, MX, okc, hR, K1, ls, stk, P, G, a, n, s, t, nd, ad, m, hI)
      +L1 = Q.Loc(a, n, s, nx, on, i, nd, ad, rg)
      +X0 = Q.Cfg(C.Cir.code.expr(c1, K1), ls, stk, Q.Loc(a, n, s, nx, on, t, nd, ad, rg), MM)
      +X1 = Q.Cfg(K1, ls, Con{i, stk}, Q.Loc(a, n, s, nx, on, tc, nd, ad, rg), MM)
      +X2 = Q.Cfg(K2, ls, Con{C.Cir.at(i), stk}, L1, MM)
      +W = Y.V32(m, U32.add(C.Cir.at(i), o))
      +X3 = Q.Cfg(k, ls, Con{W, stk}, L1, MM)
      +hat = at.steps(i, K2, ls, stk, a, n, s, nx, on, tc, nd, ad, rg, MM)
      +hld = load.step(o, C.Cir.at(i), k, ls, stk, L1, pg, lm, m,
        Q.q.field.in(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI, i, kf, cel, okk))
      +val = Equal.trans(U32, W, C.Cir.Cell.get(kf, C.Cir.Cells.get(cl, i)), v,
        Q.q.field.val(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI, i, kf, cel, okk),
        inv.field.v(kf, mc, rg, cl, nx, fi, im, pg, lm, inp, ou, on, v, ev))
      fix.top(Nat.add(cost(c1), 8n), X0, k, ls, stk, L1, MM, W, v,
        S.steps.then(cost(c1), 8n, X0, X1, X3, hc, S.steps.then(7n, 1n, X1, X2, X3, hat, hld)), val)
    case C.Cir.Expr.byte{+i1}:
      +st = Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)
      +MM = {C.Wasm.Memory{pg, lm, m} : C.Wasm.Memory}
      +mi = C.Cir.eval(i1, st)
      +x = D(mi)
      +ti = tmpE(i1, t, st)
      +L1 = Q.Loc(a, n, s, nx, on, ti, nd, ad, rg)
      +K4 = {Con{C.Cir.i.const(255), Con{C.Cir.i.op(C.Wasm.Op.and{}), k}} : List<&2, C.Wasm.Instr>}
      +K3 = {Con{C.Wasm.Instr.load8_u{0}, K4} : List<&2, C.Wasm.Instr>}
      +K1 = {Con{C.Cir.i.get(0), Con{C.Cir.i.op(C.Wasm.Op.add{}), K3}} : List<&2, C.Wasm.Instr>}
      +hi = sim.expr(i1, rg, cl, nx, fi, im, pg, lm, inp, ou, on, x, inv.byte.i(mi, inp, v, ev), R, MX, ok, hR, K1, ls, stk,
        P, G, a, n, s, t, nd, ad, m, hI)
      +bv = D(BI(mi, inp))
      +ax = U32.add(x, a)
      +rb = Y.R8(m, U32.add(ax, 0))
      +X0 = Q.Cfg(C.Cir.code.expr(i1, K1), ls, stk, Q.Loc(a, n, s, nx, on, t, nd, ad, rg), MM)
      +X1 = Q.Cfg(K1, ls, Con{x, stk}, L1, MM)
      +X2 = Q.Cfg(K3, ls, Con{ax, stk}, L1, MM)
      +X3 = Q.Cfg(K4, ls, Con{rb, stk}, L1, MM)
      +X4 = Q.Cfg(k, ls, Con{U32.and(rb, 255), stk}, L1, MM)
      +hld = load8.step(ax, K4, ls, stk, L1, pg, lm, m, Q.q.byte.in(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI, x, bv, inv.byte.b(mi, inp, v, ev)))
      +val = Equal.trans(U32, U32.and(rb, 255), U32.and(bv, 255), v,
        Equal.cong(U32, U32, z => U32.and(z, 255), rb, bv, Q.q.byte.val(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI, x, bv, inv.byte.b(mi, inp, v, ev))),
        inv.byte.v(mi, inp, v, ev))
      fix.top(Nat.add(cost(i1), 5n), X0, k, ls, stk, L1, MM, U32.and(rb, 255), v,
        S.steps.then(cost(i1), 5n, X0, X1, X4, hi, S.steps.then(2n, 3n, X1, X2, X4, {==}, S.steps.then(1n, 2n, X2, X3, X4, hld, {==}))), val)
    case C.Cir.Expr.size{}:
      +L = Q.Loc(a, n, s, nx, on, t, nd, ad, rg)
      +MM = {C.Wasm.Memory{pg, lm, m} : C.Wasm.Memory}
      fix.top(1n, Q.Cfg(Con{C.Cir.i.get(1), k}, ls, stk, L, MM), k, ls, stk, L, MM, n, v, {==},
        Equal.trans(U32, n, C.Wasm.encode.len(U32, inp), v, Q.q.size(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI),
          Q.some.inj(C.Wasm.encode.len(U32, inp), v, ev)))
