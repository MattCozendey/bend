# compiler: the simulation of Cir's statements
# ============================================
#
# SPost(o, X, K, ls, ...) says what the code X, run from the state that
# holds st (proof_sim_inv.bend), does when Cir.exec gives o:
#
#   next{st2}  it reaches the code K, with the labels ls again, an empty
#              stack and a state that holds st2;
#   halt{s}    it ends run with the results [s], with a memory from which
#              the host reads Cir's outcome (HaltOK);
#   out_of_memory  it ends run with [1];
#   trap, not_done  nothing.
#
# post.wrap prefixes and suffixes steps to an SPost; post.then composes
# Cir.exec.then. sim.stmt, at the end, is the simulation of statements, by
# induction on the fuel and on the statement.

import Base
import ./impl.bend as C
import ./proof_need.bend as N
import ./proof_instrs.bend as I
import ./proof_halt.bend as PH
import ./proof_module.bend as M
import ./proof_valid.bend as V
import ./proof_sim_step.bend as S
import ./proof_sim_mem.bend as Y
import ./proof_sim_nat.bend as Z
import ./proof_sim_inv.bend as Q
import ./proof_sim_expr.bend as E
import ./proof_sim_frame.bend as F

# Kit
# ---

def EXB(-B: C.Wasm.Bytes -> Data) -> Data:
  Sigma<&2, &2, C.Wasm.Bytes, x => B(x)>

def EXM(-B: C.Wasm.Memory -> Data) -> Data:
  Sigma<&2, &2, C.Wasm.Memory, x => B(x)>

# the label of run's block: after it, run gives its status
def RL() -> C.Wasm.Label:
  C.Wasm.Label{None{}, [C.Wasm.Instr.local_get{2}], 0n}

# a configuration of run at a statement: an empty stack, the status 2
def Cf(+X: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32,
  +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +m: C.Wasm.Bytes) -> C.Wasm.Step:
  Q.Cfg(X, ls, [], Q.Loc(a, n, 2, nx, on, t, nd, ad, rg), C.Wasm.Memory{pg, lm, m})

# Posts
# -----

# the outcome that the host reads at the end of run, for the status s0: what
# Cir.ended says, unless the output is empty and the cells end past the
# memory of pg pages (the host's check of the output's place then fails)
def HaltOK(+s0: U32, +nx: U32, +pg: U32, +ou: List<&2, U32>, +mem: C.Wasm.Memory) -> Data:
  Either<&2, &2, {C.Wasm.run.status(U32.is_eq(s0, 0), U32.is_eq(s0, 1), U32.is_eq(s0, 2), mem) ==
    C.Cir.ended.halt(U32.is_eq(s0, 0), U32.is_eq(s0, 1), U32.is_eq(s0, 2), ou) : C.Wasm.Outcome},
    S.P2({ou == Nil{} : List<&2, U32>}, N.Le(1n+Q.PB(pg), PH.H.t20(U32.to_nat(nx))))>

def SPost.next(st2: C.Cir.State, +X: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +K: List<&2, C.Wasm.Instr>, +ls1: List<&2, C.Wasm.Label>,
  +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +m: C.Wasm.Bytes,
  +P: Nat, +G: Nat) -> Data:
  match st2:
    case C.Cir.State{+rg2, +cl2, +nx2, +fi2, +im2, +pg2, +lm2, +inp2, +ou2, +on2}:
      S.EX(N2 => Q.EXU(t2 => Q.EXU(nd2 => Q.EXU(ad2 => EXB(m2 =>
        S.P2({PH.H.steps(N2, Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m)) ==
          Cf(K, ls1, a, n, t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, m2) : C.Wasm.Step},
          Q.Inv(P, G, a, n, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2, m2)))))))

def SPost.halt(+s0: U32, st2: C.Cir.State, +X: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>,
  +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +m: C.Wasm.Bytes) -> Data:
  match st2:
    case C.Cir.State{_, _, +nx2, _, _, +pg2, _, _, +ou2, _}:
      S.EX(N2 => EXM(mm => S.P2({PH.H.steps(N2, Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m)) ==
        C.Wasm.Step.done{[s0], mm} : C.Wasm.Step}, HaltOK(s0, nx2, pg2, ou2, mm))))

# what the code X does in the labels ls, from a state that holds st, when
# Cir.exec gives o; a next state is at the code K in the labels ls1
def SPost(o: C.Cir.Out, +X: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +K: List<&2, C.Wasm.Instr>, +ls1: List<&2, C.Wasm.Label>,
  +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +m: C.Wasm.Bytes,
  +P: Nat, +G: Nat) -> Data:
  match o:
    case C.Cir.Out.next{st2}:
      SPost.next(st2, X, ls, K, ls1, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G)
    case C.Cir.Out.halt{+s0, st2}:
      SPost.halt(s0, st2, X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m)
    case C.Cir.Out.out_of_memory{}:
      S.EX(N2 => EXM(mm => {PH.H.steps(N2, Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m)) ==
        C.Wasm.Step.done{[1], mm} : C.Wasm.Step}))
    case C.Cir.Out.trap{}:
      Unit
    case C.Cir.Out.not_done{}:
      Unit

# Composing posts
# ---------------

# N0 steps from X in ls reach Xi in lsi (with any state), and N1 steps from
# Ki in lsi1 reach K in ls1 (from any state), so what holds of Xi to Ki holds
# of X to K
def post.wrap(o: C.Cir.Out, +X: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +K: List<&2, C.Wasm.Instr>, +ls1: List<&2, C.Wasm.Label>,
  +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +m: C.Wasm.Bytes, +P: Nat, +G: Nat,
  +Xi: List<&2, C.Wasm.Instr>, +lsi: List<&2, C.Wasm.Label>, +Ki: List<&2, C.Wasm.Instr>, +lsi1: List<&2, C.Wasm.Label>,
  +ti: U32, +ndi: U32, +adi: U32, +rgi: List<&2, U32>, +nxi: U32, +oni: U32, +pgi: U32, +lmi: U32, +mi: C.Wasm.Bytes, +N0: Nat,
  +e0: {PH.H.steps(N0, Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m)) == Cf(Xi, lsi, a, n, ti, ndi, adi, rgi, nxi, oni, pgi, lmi, mi) : C.Wasm.Step},
  +N1: Nat, suf: @t2: U32 -> @nd2: U32 -> @ad2: U32 -> @rg2: List<&2, U32> -> @nx2: U32 -> @on2: U32 -> @pg2: U32 -> @lm2: U32 ->
    @m2: C.Wasm.Bytes -> {PH.H.steps(N1, Cf(Ki, lsi1, a, n, t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, m2)) ==
      Cf(K, ls1, a, n, t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, m2) : C.Wasm.Step},
  p: SPost(o, Xi, lsi, Ki, lsi1, a, n, ti, ndi, adi, rgi, nxi, oni, pgi, lmi, mi, P, G)) -> SPost(o, X, ls, K, ls1, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G):
  match o:
    case C.Cir.Out.next{st2}:
      match st2:
        case C.Cir.State{+rg2, +cl2, +nx2, +fi2, +im2, +pg2, +lm2, +inp2, +ou2, +on2}:
          (+N2, p1) = p
          (+t2, p2) = p1
          (+nd2, p3) = p2
          (+ad2, p4) = p3
          (+m2, p5) = p4
          (eq, hI) = p5
          +C0 = Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m)
          +C1 = Cf(Xi, lsi, a, n, ti, ndi, adi, rgi, nxi, oni, pgi, lmi, mi)
          +C2 = Cf(Ki, lsi1, a, n, t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, m2)
          +C3 = Cf(K, ls1, a, n, t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, m2)
          (Nat.add(N0, Nat.add(N2, N1)), (t2, (nd2, (ad2, (m2, (S.steps.then(N0, Nat.add(N2, N1), C0, C1, C3, e0,
            S.steps.then(N2, N1, C1, C2, C3, eq, suf(t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, m2))), hI))))))
    case C.Cir.Out.halt{+s0, st2}:
      match st2:
        case C.Cir.State{+rg2, +cl2, +nx2, +fi2, +im2, +pg2, +lm2, +inp2, +ou2, +on2}:
          (+N2, p1) = p
          (+mm, p2) = p1
          (eq, ok) = p2
          (Nat.add(N0, N2), (mm, (S.steps.then(N0, N2, Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m), Cf(Xi, lsi, a, n, ti, ndi, adi, rgi, nxi, oni, pgi, lmi, mi), C.Wasm.Step.done{[s0], mm}, e0, eq), ok)))
    case C.Cir.Out.out_of_memory{}:
      (+N2, p1) = p
      (+mm, eq) = p1
      (Nat.add(N0, N2), (mm, S.steps.then(N0, N2, Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m), Cf(Xi, lsi, a, n, ti, ndi, adi, rgi, nxi, oni, pgi, lmi, mi), C.Wasm.Step.done{[1], mm}, e0, eq)))
    case C.Cir.Out.trap{}:
      Unit{}
    case C.Cir.Out.not_done{}:
      Unit{}

# the code X in ls reaches Xi in lsi: what holds of Xi holds of X
def post.pre(o: C.Cir.Out, +X: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +K: List<&2, C.Wasm.Instr>, +ls1: List<&2, C.Wasm.Label>,
  +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +m: C.Wasm.Bytes, +P: Nat, +G: Nat, +Xi: List<&2, C.Wasm.Instr>, +lsi: List<&2, C.Wasm.Label>,
  +ti: U32, +ndi: U32, +adi: U32, +rgi: List<&2, U32>, +nxi: U32, +oni: U32, +pgi: U32, +lmi: U32, +mi: C.Wasm.Bytes, +N0: Nat,
  +e0: {PH.H.steps(N0, Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m)) == Cf(Xi, lsi, a, n, ti, ndi, adi, rgi, nxi, oni, pgi, lmi, mi) : C.Wasm.Step},
  p: SPost(o, Xi, lsi, K, ls1, a, n, ti, ndi, adi, rgi, nxi, oni, pgi, lmi, mi, P, G)) -> SPost(o, X, ls, K, ls1, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G):
  post.wrap(o, X, ls, K, ls1, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G, Xi, lsi, K, ls1, ti, ndi, adi, rgi, nxi, oni, pgi, lmi, mi, N0, e0, 0n,
    t2 => nd2 => ad2 => rg2 => nx2 => on2 => pg2 => lm2 => m2 => {==}, p)

# Cir.exec.then: what the first part does, then what the rest does from the
# state that it reaches
def post.then(o1: C.Cir.Out, more: C.Cir.State -> C.Cir.Out, +X: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>,
  +K1: List<&2, C.Wasm.Instr>, +ls1: List<&2, C.Wasm.Label>, +K: List<&2, C.Wasm.Instr>, +ls2: List<&2, C.Wasm.Label>, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +m: C.Wasm.Bytes, +P: Nat, +G: Nat,
  p: SPost(o1, X, ls, K1, ls1, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G),
  kont: @rg2: List<&2, U32> -> @cl2: C.Cir.Cells -> @nx2: U32 -> @fi2: U32 -> @im2: U32 -> @pg2: U32 -> @lm2: U32 ->
    @inp2: List<&2, U32> -> @ou2: List<&2, U32> -> @on2: U32 -> @t2: U32 -> @nd2: U32 -> @ad2: U32 -> @m2: C.Wasm.Bytes ->
    Q.Inv(P, G, a, n, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2, m2) ->
    SPost(more(C.Cir.State{rg2, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2}), K1, ls1, K, ls2, a, n, t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, m2, P, G)) ->
  SPost(C.Cir.exec.then(o1, more), X, ls, K, ls2, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G):
  match o1:
    case C.Cir.Out.next{st2}:
      match st2:
        case C.Cir.State{+rg2, +cl2, +nx2, +fi2, +im2, +pg2, +lm2, +inp2, +ou2, +on2}:
          (+N2, p1) = p
          (+t2, p2) = p1
          (+nd2, p3) = p2
          (+ad2, p4) = p3
          (+m2, p5) = p4
          (+eq, +hI) = p5
          post.pre(more(C.Cir.State{rg2, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2}), X, ls, K, ls2, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G, K1, ls1,
            t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, m2, N2, eq,
            kont(rg2, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2, t2, nd2, ad2, m2, hI))
    case C.Cir.Out.halt{+s0, st2}:
      p
    case C.Cir.Out.out_of_memory{}:
      p
    case C.Cir.Out.trap{}:
      Unit{}
    case C.Cir.Out.not_done{}:
      Unit{}

# The depth of the labels of a statement's code: the branches out of run
# from it are at most d + dep(s) levels inside run's block
def dep(s: C.Cir.Stmt) -> Nat:
  match s:
    case C.Cir.Stmt.nop{}:
      0n
    case C.Cir.Stmt.set{_, _}:
      0n
    case C.Cir.Stmt.store{_, _, _}:
      0n
    case C.Cir.Stmt.alloc{_}:
      4n
    case C.Cir.Stmt.emit{_}:
      4n
    case C.Cir.Stmt.seq{a, b}:
      Nat.add(dep(a), dep(b))
    case C.Cir.Stmt.if{_, t, e}:
      2n+Nat.add(dep(t), dep(e))
    case C.Cir.Stmt.while{_, body}:
      2n+dep(body)
    case C.Cir.Stmt.halt{_}:
      2n

# The statements that touch the memory
# ------------------------------------
#
# Each lemma is the simulation of one statement, from a state that holds st.

# store{k, c, v}, when c gives the cell i and v the value x: the cell is one
# that the machine may use (b)
def store.if(b: Bool, +k: Nat, +c: C.Cir.Expr, +v: C.Cir.Expr, +i: U32, +x: U32, +rg: List<&2, U32>, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +pg: U32, +lm: U32, +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32,
  +d: Nat, +K: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)),
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +m: C.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat}, +hk: {Nat.is_le(k, 4n) == True{} : Bool},
  +okc: {V.ok.expr(c, R) == True{} : Bool}, +okv: {V.ok.expr(v, R) == True{} : Bool},
  +evc: {C.Cir.eval(c, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)) == Some{i} : Maybe<&2, U32>},
  +evv: {C.Cir.eval(v, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)) == Some{x} : Maybe<&2, U32>},
  +eb: {C.Cir.is_cell(i, im, fi, nx) == b : Bool}) ->
  SPost(C.Cir.exec.store.if(b, k, i, x, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), C.Cir.code.stmt(C.Cir.Stmt.store{k, c, v}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G):
  match b:
    case False{}:
      Unit{}
    case True{}:
      +o = U32.shln(U32.from_nat(k), 2n)
      +St = Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)
      +Ks = {Con{C.Wasm.Instr.store{o}, K} : List<&2, C.Wasm.Instr>}
      +Kv = C.Cir.code.expr(v, Ks)
      +Ka = C.Cir.code.at(Kv)
      +tc = E.tmpE(c, t, St)
      +tv = E.tmpE(v, i, St)
      +M0 = {C.Wasm.Memory{pg, lm, m} : C.Wasm.Memory}
      +L3 = Q.Loc(a, n, 2, nx, on, tv, nd, ad, rg)
      +C0 = Cf(C.Cir.code.expr(c, Ka), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m)
      +C1 = Q.Cfg(Ka, ls, [i], Q.Loc(a, n, 2, nx, on, tc, nd, ad, rg), M0)
      +C2 = Q.Cfg(Kv, ls, [C.Cir.at(i)], Q.Loc(a, n, 2, nx, on, i, nd, ad, rg), M0)
      +C3 = Q.Cfg(Ks, ls, [x, C.Cir.at(i)], L3, M0)
      +m2 = C.Wasm.write32(m, Q.at.f(i, k), x)
      +C4 = Cf(K, ls, a, n, tv, nd, ad, rg, nx, on, pg, lm, m2)
      +e1 = E.sim.expr(c, rg, cl, nx, fi, im, pg, lm, inp, ou, on, i, evc, R, MX, okc, hR, Ka, ls, [], P, G, a, n, 2, t, nd, ad, m, hI, W, hW, hP, hG)
      +e2 = E.at.steps(i, Kv, ls, [], a, n, 2, nx, on, tc, nd, ad, rg, M0)
      +e3 = E.sim.expr(v, rg, cl, nx, fi, im, pg, lm, inp, ou, on, x, evv, R, MX, okv, hR, Ks, ls, [C.Cir.at(i)], P, G, a, n, 2, i, nd, ad, m, hI, W, hW, hP, hG)
      +hin = Q.q.field.in(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI, W, hW, hP, hG, i, k, eb, hk)
      +e4 = F.store.step(o, C.Cir.at(i), x, K, ls, [], L3, pg, lm, m, hin)
      +e34 = S.steps.then(E.cost(v), 1n, C2, C3, C4, e3, e4)
      +e24 = S.steps.then(7n, Nat.add(E.cost(v), 1n), C1, C2, C4, e2, e34)
      +e14 = S.steps.then(E.cost(c), Nat.add(7n, Nat.add(E.cost(v), 1n)), C0, C1, C4, e1, e24)
      (Nat.add(E.cost(c), Nat.add(7n, Nat.add(E.cost(v), 1n))), (tv, (nd, (ad, (m2, (e14,
        F.inv.store(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI, W, hW, hP, hG, i, k, x, hk, eb)))))))

# store{k, c, v}, by the values of c and v
def store.of(mc: Maybe<&2, U32>, mv: Maybe<&2, U32>, +k: Nat, +c: C.Cir.Expr, +v: C.Cir.Expr, +rg: List<&2, U32>, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +pg: U32, +lm: U32, +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32,
  +d: Nat, +K: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)),
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +m: C.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat}, +hk: {Nat.is_le(k, 4n) == True{} : Bool},
  +okc: {V.ok.expr(c, R) == True{} : Bool}, +okv: {V.ok.expr(v, R) == True{} : Bool},
  +evc: {C.Cir.eval(c, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)) == mc : Maybe<&2, U32>},
  +evv: {C.Cir.eval(v, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)) == mv : Maybe<&2, U32>}) ->
  SPost(C.Cir.exec.store(k, mc, mv, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), C.Cir.code.stmt(C.Cir.Stmt.store{k, c, v}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G):
  match mc mv:
    case Some{+i} Some{+x}:
      store.if(C.Cir.is_cell(i, im, fi, nx), k, c, v, i, x, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, R, MX, hR, P, G, a, n, t, nd, ad, m, hI,
        W, hW, hP, hG, hk, okc, okv, evc, evv, {==})
    case Some{i} None{}:
      Unit{}
    case None{} _:
      Unit{}

# store{k, c, v}
def sim.store(+k: Nat, +c: C.Cir.Expr, +v: C.Cir.Expr, +rg: List<&2, U32>, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32,
  +d: Nat, +K: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +hL: {List.drop(&2, C.Wasm.Label, ls, d) == [RL()] : List<&2, C.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +m: C.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat},
  +ok: {V.ok.stmt(C.Cir.Stmt.store{k, c, v}, R) == True{} : Bool}) ->
  SPost(C.Cir.exec.store(k, C.Cir.eval(c, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), C.Cir.eval(v, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), C.Cir.code.stmt(C.Cir.Stmt.store{k, c, v}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G):
  +ok01 = I.and.l(Bool.and(Nat.is_le(k, 4n), V.ok.expr(c, R)), V.ok.expr(v, R), ok)
  store.of(C.Cir.eval(c, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), C.Cir.eval(v, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)),
    k, c, v, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, R, MX, hR, P, G, a, n, t, nd, ad, m, hI, W, hW, hP, hG,
    I.and.l(Nat.is_le(k, 4n), V.ok.expr(c, R), ok01), I.and.r(Nat.is_le(k, 4n), V.ok.expr(c, R), ok01),
    I.and.r(Bool.and(Nat.is_le(k, 4n), V.ok.expr(c, R)), V.ok.expr(v, R), ok), {==}, {==})

# alloc{r}
def sim.alloc(+r: Nat, +rg: List<&2, U32>, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32,
  +d: Nat, +K: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +hL: {List.drop(&2, C.Wasm.Label, ls, d) == [RL()] : List<&2, C.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +m: C.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat},
  +ok: {V.ok.stmt(C.Cir.Stmt.alloc{r}, R) == True{} : Bool}, +hd: N.Le(Nat.add(d, 4n), U32.to_nat(MD))) ->
  SPost(C.Cir.exec.alloc(r, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), C.Cir.code.stmt(C.Cir.Stmt.alloc{r}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G):
  ?TODO

# emit{v}
def sim.emit(+v: C.Cir.Expr, +rg: List<&2, U32>, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32,
  +d: Nat, +K: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +hL: {List.drop(&2, C.Wasm.Label, ls, d) == [RL()] : List<&2, C.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +m: C.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat},
  +ok: {V.ok.stmt(C.Cir.Stmt.emit{v}, R) == True{} : Bool}, +hd: N.Le(Nat.add(d, 4n), U32.to_nat(MD))) ->
  SPost(C.Cir.exec.emit(C.Cir.eval(v, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), C.Cir.code.stmt(C.Cir.Stmt.emit{v}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G):
  ?TODO

# The halt
# --------

# the branch out of run from j labels inside it: run gives its status
def exit.steps(+j: Nat, +ls2: List<&2, C.Wasm.Label>, +hj: {List.drop(&2, C.Wasm.Label, ls2, j) == [RL()] : List<&2, C.Wasm.Label>},
  +ej: {U32.to_nat(U32.from_nat(j)) == j : Nat}, +L: List<&2, U32>, +M: C.Wasm.Memory) ->
  {PH.H.steps(3n, Q.Cfg([C.Wasm.Instr.br{U32.from_nat(j)}], ls2, [], L, M)) ==
    C.Wasm.Step.done{[Maybe.default(&2, U32, List.get(&2, U32, L, 2n), 0)], M} : C.Wasm.Step}:
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(j)), j, ej) :
    {PH.H.steps(2n, C.Wasm.step.br(List.drop(&2, C.Wasm.Label, ls2, _), 1n, [], L, M)) ==
      C.Wasm.Step.done{[Maybe.default(&2, U32, List.get(&2, U32, L, 2n), 0)], M} : C.Wasm.Step}
  %Equal.sym(List<&2, C.Wasm.Label>, List.drop(&2, C.Wasm.Label, ls2, j), [RL()], hj) :
    {PH.H.steps(2n, C.Wasm.step.br(_, 1n, [], L, M)) ==
      C.Wasm.Step.done{[Maybe.default(&2, U32, List.get(&2, U32, L, 2n), 0)], M} : C.Wasm.Step}
  {==}

# a status other than 0 needs no output
def status.nz(b1: Bool, b2: Bool, +mem: C.Wasm.Memory, +ou: List<&2, U32>) ->
  {C.Wasm.run.status(False{}, b1, b2, mem) == C.Cir.ended.halt(False{}, b1, b2, ou) : C.Wasm.Outcome}:
  match b1 b2:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# the host reads the output, at 20 × next, of on bytes
def hok.fin(+pg: U32, +lm: U32, +m2: C.Wasm.Bytes, +A0: U32, +on: U32, +ou: List<&2, U32>,
  f8: {C.Wasm.fits(pg, 0, 8) == True{} : Bool}, v0: {Y.V32(m2, 0) == A0 : U32}, v4: {Y.V32(m2, 4) == on : U32},
  fo: {C.Wasm.fits(pg, A0, on) == True{} : Bool}, rb: {Q.RB(U32.to_nat(on), m2, A0) == List.reverse(&2, U32, ou) : List<&2, U32>}) ->
  {C.Wasm.run.output(C.Wasm.Memory{pg, lm, m2}) == C.Wasm.Outcome.result{List.reverse(&2, U32, ou)} : C.Wasm.Outcome}:
  Equal.trans(C.Wasm.Outcome, C.Wasm.run.output(C.Wasm.Memory{pg, lm, m2}), C.Wasm.Outcome.result{C.Wasm.read.bytes(U32.to_nat(on), m2, A0)},
    C.Wasm.Outcome.result{List.reverse(&2, U32, ou)}, F.out.ok(pg, lm, m2, A0, on, f8, v0, v4, fo),
    Equal.cong(List<&2, U32>, C.Wasm.Outcome, l => C.Wasm.Outcome.result{l}, C.Wasm.read.bytes(U32.to_nat(on), m2, A0), List.reverse(&2, U32, ou),
      Equal.trans(List<&2, U32>, C.Wasm.read.bytes(U32.to_nat(on), m2, A0), Q.RB(U32.to_nat(on), m2, A0), List.reverse(&2, U32, ou),
        F.rb.read(U32.to_nat(on), m2, A0), rb)))

# the output after the writes of its place at bytes 0 to 7
def hok.rb(+m: C.Wasm.Bytes, +A0: U32, +on: U32, +X: Nat, +ex: {U32.to_nat(A0) == X : Nat}, +ou: List<&2, U32>,
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +h8: N.Le(8n, X), +hx: N.Le(1n+Nat.add(U32.to_nat(on), X), W),
  ro: {Q.RB(U32.to_nat(on), m, A0) == List.reverse(&2, U32, ou) : List<&2, U32>}) ->
  {Q.RB(U32.to_nat(on), C.Wasm.write32(C.Wasm.write32(m, 0, A0), 4, on), A0) == List.reverse(&2, U32, ou) : List<&2, U32>}:
  +m1 = C.Wasm.write32(m, 0, A0)
  +ON = U32.to_nat(on)
  +h16 = F.w16(P, hP, W, hW)
  Equal.trans(List<&2, U32>, Q.RB(ON, C.Wasm.write32(m1, 4, on), A0), Q.RB(ON, m1, A0), List.reverse(&2, U32, ou),
    F.RB.w32(ON, m1, 4, on, A0, X, ex, W, hW, N.le_trans(8n, 16n, W, Unit{}, h16), hx, Inr{h8}),
    Equal.trans(List<&2, U32>, Q.RB(ON, m1, A0), Q.RB(ON, m, A0), List.reverse(&2, U32, ou),
      F.RB.w32(ON, m, 0, A0, A0, X, ex, W, hW, N.le_trans(4n, 16n, W, Unit{}, h16), hx, Inr{N.le_trans(4n, 8n, X, Unit{}, h8)}), ro))

# no output: the host reads it when the cells end within the memory
def hok.z(b: Bool, +pg: U32, +lm: U32, +m: C.Wasm.Bytes, +nx: U32, +on: U32, +ou: List<&2, U32>, +X: Nat,
  +ex: {U32.to_nat(C.Cir.at(nx)) == X : Nat}, +eX: {X == PH.H.t20(U32.to_nat(nx)) : Nat}, +eb: {Nat.is_le(X, Q.PB(pg)) == b : Bool},
  +eon: {U32.to_nat(on) == 0n : Nat}, +f8: {C.Wasm.fits(pg, 0, 8) == True{} : Bool},
  +v0: {Y.V32(C.Wasm.write32(C.Wasm.write32(m, 0, C.Cir.at(nx)), 4, on), 0) == C.Cir.at(nx) : U32},
  +v4: {Y.V32(C.Wasm.write32(C.Wasm.write32(m, 0, C.Cir.at(nx)), 4, on), 4) == on : U32},
  +h20: N.Le(20n, X), +rb: {Q.RB(U32.to_nat(on), C.Wasm.write32(C.Wasm.write32(m, 0, C.Cir.at(nx)), 4, on), C.Cir.at(nx)) == List.reverse(&2, U32, ou) : List<&2, U32>},
  +ro: {Q.RB(U32.to_nat(on), m, C.Cir.at(nx)) == List.reverse(&2, U32, ou) : List<&2, U32>}) ->
  HaltOK(0, nx, pg, ou, C.Wasm.Memory{pg, lm, C.Wasm.write32(C.Wasm.write32(m, 0, C.Cir.at(nx)), 4, on)}):
  match b:
    case True{}:
      +A0 = C.Cir.at(nx)
      +m2 = C.Wasm.write32(C.Wasm.write32(m, 0, A0), 4, on)
      +e0 = Equal.trans(U32, on, U32.from_nat(U32.to_nat(on)), 0, Equal.sym(U32, U32.from_nat(U32.to_nat(on)), on, Z.from.to(on)),
        Equal.cong(Nat, U32, z => U32.from_nat(z), U32.to_nat(on), 0n, eon))
      +f0 = F.fits0(pg, A0, N.le_rw_l(1n, 1n, U32.to_nat(A0), {==}, N.le_rw_r(1n, X, U32.to_nat(A0), Equal.sym(Nat, U32.to_nat(A0), X, ex), N.le_trans(1n, 20n, X, Unit{}, h20))),
        N.le_rw_l(X, U32.to_nat(A0), Q.PB(pg), Equal.sym(Nat, U32.to_nat(A0), X, ex), N.toLe(X, Q.PB(pg), eb)))
      +fo = {(%Equal.sym(U32, on, 0, e0) : {C.Wasm.fits(pg, A0, _) == True{} : Bool}; f0) : {C.Wasm.fits(pg, A0, on) == True{} : Bool}}
      Inl{hok.fin(pg, lm, m2, A0, on, ou, f8, v0, v4, fo, rb)}
    case False{}:
      +A0 = C.Cir.at(nx)
      +ro0 = {(%eon : {Q.RB(_, m, A0) == List.reverse(&2, U32, ou) : List<&2, U32>}; ro) :
        {Q.RB(0n, m, A0) == List.reverse(&2, U32, ou) : List<&2, U32>}}
      Inr{(F.rev.nil(ou, ro0), N.le_rw_r(1n+Q.PB(pg), X, PH.H.t20(U32.to_nat(nx)), eX, F.nle.lt(X, Q.PB(pg), eb)))}

# the output of on bytes: the host reads it, unless it is empty and the cells
# end past the memory
def hok.on(ON: Nat, +pg: U32, +lm: U32, +m: C.Wasm.Bytes, +nx: U32, +on: U32, +ou: List<&2, U32>, +X: Nat,
  +ex: {U32.to_nat(C.Cir.at(nx)) == X : Nat}, +eX: {X == PH.H.t20(U32.to_nat(nx)) : Nat}, +eon: {U32.to_nat(on) == ON : Nat},
  +f8: {C.Wasm.fits(pg, 0, 8) == True{} : Bool},
  +v0: {Y.V32(C.Wasm.write32(C.Wasm.write32(m, 0, C.Cir.at(nx)), 4, on), 0) == C.Cir.at(nx) : U32},
  +v4: {Y.V32(C.Wasm.write32(C.Wasm.write32(m, 0, C.Cir.at(nx)), 4, on), 4) == on : U32},
  +h20: N.Le(20n, X), +ro: {Q.RB(U32.to_nat(on), m, C.Cir.at(nx)) == List.reverse(&2, U32, ou) : List<&2, U32>},
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hxw: N.Le(1n+X, W), +hb: N.Le(1n+Q.PB(pg), W), +hof: Q.OF(ON, U32.to_nat(nx), Q.PB(pg))) ->
  HaltOK(0, nx, pg, ou, C.Wasm.Memory{pg, lm, C.Wasm.write32(C.Wasm.write32(m, 0, C.Cir.at(nx)), 4, on)}):
  match ON:
    case 0n:
      +A0 = C.Cir.at(nx)
      +hx = {(%Equal.sym(Nat, U32.to_nat(on), 0n, eon) : N.Le(1n+Nat.add(_, X), W); hxw) : N.Le(1n+Nat.add(U32.to_nat(on), X), W)}
      hok.z(Nat.is_le(X, Q.PB(pg)), pg, lm, m, nx, on, ou, X, ex, eX, {==}, eon, f8, v0, v4, h20,
        hok.rb(m, A0, on, X, ex, ou, P, hP, W, hW, N.le_trans(8n, 20n, X, Unit{}, h20), hx, ro), ro)
    case 1n+q:
      +A0 = C.Cir.at(nx)
      +m2 = C.Wasm.write32(C.Wasm.write32(m, 0, A0), 4, on)
      +hend = N.le_rw_l(Nat.add(PH.H.t20(U32.to_nat(nx)), 1n+q), Nat.add(U32.to_nat(A0), U32.to_nat(on)), Q.PB(pg),
        Equal.trans(Nat, Nat.add(PH.H.t20(U32.to_nat(nx)), 1n+q), Nat.add(X, 1n+q), Nat.add(U32.to_nat(A0), U32.to_nat(on)),
          Equal.cong(Nat, Nat, z => Nat.add(z, 1n+q), PH.H.t20(U32.to_nat(nx)), X, Equal.sym(Nat, X, PH.H.t20(U32.to_nat(nx)), eX)),
          Equal.trans(Nat, Nat.add(X, 1n+q), Nat.add(U32.to_nat(A0), 1n+q), Nat.add(U32.to_nat(A0), U32.to_nat(on)),
            Equal.cong(Nat, Nat, z => Nat.add(z, 1n+q), X, U32.to_nat(A0), Equal.sym(Nat, U32.to_nat(A0), X, ex)),
            Equal.cong(Nat, Nat, z => Nat.add(U32.to_nat(A0), z), 1n+q, U32.to_nat(on), Equal.sym(Nat, U32.to_nat(on), 1n+q, eon)))), hof)
      +hx = N.le_trans(1n+Nat.add(U32.to_nat(on), X), 1n+Q.PB(pg), W,
        N.le_rw_l(Nat.add(U32.to_nat(A0), U32.to_nat(on)), Nat.add(U32.to_nat(on), X), Q.PB(pg),
          Equal.trans(Nat, Nat.add(U32.to_nat(A0), U32.to_nat(on)), Nat.add(X, U32.to_nat(on)), Nat.add(U32.to_nat(on), X),
            Equal.cong(Nat, Nat, z => Nat.add(z, U32.to_nat(on)), U32.to_nat(A0), X, ex), Z.add.comm(X, U32.to_nat(on))), hend), hb)
      +fo = F.fits.ok(pg, A0, on, W, hW, N.le_rw_r(1n, 1n+q, U32.to_nat(on), Equal.sym(Nat, U32.to_nat(on), 1n+q, eon), N.le_zero(q)), hend, hb)
      Inl{hok.fin(pg, lm, m2, A0, on, ou, f8, v0, v4, fo, hok.rb(m, A0, on, X, ex, ou, P, hP, W, hW, N.le_trans(8n, 20n, X, Unit{}, h20), hx, ro))}

# a halt with the status 0: the host reads the output, as Cir says, unless
# it is empty and the cells end past the memory
def haltok0(+P: Nat, +G: Nat, +a: U32, +n: U32, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32, +m: C.Wasm.Bytes, +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat}) ->
  HaltOK(0, nx, pg, ou, C.Wasm.Memory{pg, lm, C.Wasm.write32(C.Wasm.write32(m, 0, C.Cir.at(nx)), 4, on)}):
  +hB = Q.inv.bounds(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)
  +NX = U32.to_nat(nx)
  +X = PH.H.t20(NX)
  +A0 = C.Cir.at(nx)
  +m1 = C.Wasm.write32(m, 0, A0)
  +m2 = C.Wasm.write32(m1, 4, on)
  +hb = Q.pb.lt(P, G, a, nx, fi, im, pg, lm, inp, on, hB, W, hG)
  +ex = F.at.nat(nx, P, hP, Q.b.nx(P, G, a, nx, fi, im, pg, lm, inp, on, hB))
  +h20 = F.inv.x20(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)
  +f8 = F.fits.ok(pg, 0, 8, W, hW, Unit{}, N.le_trans(8n, 20n, Q.PB(pg), Unit{}, F.b.pb20(P, G, a, nx, fi, im, pg, lm, inp, on, hB)), hb)
  +v0 = Equal.trans(U32, Y.V32(m2, 0), Y.V32(m1, 0), A0, Y.V32.out32(m1, 4, on, 0, F.d04()), Y.V32.same(m, 0, A0))
  +v4 = Y.V32.same(m1, 4, on)
  hok.on(U32.to_nat(on), pg, lm, m, nx, on, ou, X, ex, {==}, {==}, f8, v0, v4, h20,
    Q.inv.out(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI), P, hP, W, hW,
    F.b.xw(G, a, nx, fi, im, pg, lm, inp, on, P, hP, W, hW, hB), hb, Q.b.of(P, G, a, nx, fi, im, pg, lm, inp, on, hB))

# halt{s0}, by the code of its result (z = s0 is 0)
def halt.z(z: Bool, +s0: U32, +rg: List<&2, U32>, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32,
  +d: Nat, +K: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +hL: {List.drop(&2, C.Wasm.Label, ls, d) == [RL()] : List<&2, C.Wasm.Label>},
  +MD: U32, +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +m: C.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat}, +hd: N.Le(Nat.add(d, 2n), U32.to_nat(MD)), +ez: {U32.is_zero(s0) == z : Bool}) ->
  SPost.halt(s0, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on), Con{C.Wasm.Instr.block{Con{C.Cir.i.const(s0), Con{C.Cir.i.set(C.Cir.l.status()),
    List.append(&2, C.Wasm.Instr, C.Cir.code.result(z), [C.Wasm.Instr.br{U32.from_nat(1n+d)}])}}}, K}, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m):
  match z:
    case False{}:
      +ej = M.tofrom(1n+d, MD, N.le_trans(1n+d, Nat.add(d, 2n), U32.to_nat(MD), N.lt_add(d, 1n), hd))
      +LS = {Con{C.Wasm.Label{None{}, K, 0n}, ls} : List<&2, C.Wasm.Label>}
      +BR = {[C.Wasm.Instr.br{U32.from_nat(1n+d)}] : List<&2, C.Wasm.Instr>}
      +L1 = Q.Loc(a, n, s0, nx, on, t, nd, ad, rg)
      +X = {Con{C.Wasm.Instr.block{Con{C.Cir.i.const(s0), Con{C.Cir.i.set(C.Cir.l.status()), List.append(&2, C.Wasm.Instr, C.Cir.code.result(False{}), BR)}}}, K} : List<&2, C.Wasm.Instr>}
      +C0 = Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m)
      +C1 = Q.Cfg(BR, LS, [], L1, C.Wasm.Memory{pg, lm, m})
      +mm = {C.Wasm.Memory{pg, lm, m} : C.Wasm.Memory}
      +ok = {(%Equal.sym(Bool, U32.is_zero(s0), False{}, ez) :
          {C.Wasm.run.status(_, U32.is_eq(s0, 1), U32.is_eq(s0, 2), mm) == C.Cir.ended.halt(_, U32.is_eq(s0, 1), U32.is_eq(s0, 2), ou) : C.Wasm.Outcome};
          status.nz(U32.is_eq(s0, 1), U32.is_eq(s0, 2), mm, ou)) :
        {C.Wasm.run.status(U32.is_eq(s0, 0), U32.is_eq(s0, 1), U32.is_eq(s0, 2), mm) == C.Cir.ended.halt(U32.is_eq(s0, 0), U32.is_eq(s0, 1), U32.is_eq(s0, 2), ou) : C.Wasm.Outcome}}
      (6n, (mm, (S.steps.then(3n, 3n, C0, C1, C.Wasm.Step.done{[s0], mm}, {==}, exit.steps(1n+d, LS, hL, ej, L1, mm)), Inl{ok})))
    case True{}:
      +ej = M.tofrom(1n+d, MD, N.le_trans(1n+d, Nat.add(d, 2n), U32.to_nat(MD), N.lt_add(d, 1n), hd))
      +LS = {Con{C.Wasm.Label{None{}, K, 0n}, ls} : List<&2, C.Wasm.Label>}
      +BR = {[C.Wasm.Instr.br{U32.from_nat(1n+d)}] : List<&2, C.Wasm.Instr>}
      +L1 = Q.Loc(a, n, s0, nx, on, t, nd, ad, rg)
      +hB = Q.inv.bounds(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)
      +hb = Q.pb.lt(P, G, a, nx, fi, im, pg, lm, inp, on, hB, W, hG)
      +p20 = F.b.pb20(P, G, a, nx, fi, im, pg, lm, inp, on, hB)
      +A0 = C.Cir.at(nx)
      +R2 = {[C.Cir.i.const(0), C.Cir.i.get(C.Cir.l.outn()), C.Wasm.Instr.store{4}, C.Wasm.Instr.br{U32.from_nat(1n+d)}] : List<&2, C.Wasm.Instr>}
      +R3 = {[C.Wasm.Instr.store{4}, C.Wasm.Instr.br{U32.from_nat(1n+d)}] : List<&2, C.Wasm.Instr>}
      +L2 = Q.Loc(a, n, s0, nx, on, nx, nd, ad, rg)
      +m1 = C.Wasm.write32(m, 0, A0)
      +m2 = C.Wasm.write32(m1, 4, on)
      +X = {Con{C.Wasm.Instr.block{Con{C.Cir.i.const(s0), Con{C.Cir.i.set(C.Cir.l.status()), List.append(&2, C.Wasm.Instr, C.Cir.code.result(True{}), BR)}}}, K} : List<&2, C.Wasm.Instr>}
      +C0 = Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m)
      +C1 = Q.Cfg(Con{C.Wasm.Instr.store{0}, R2}, LS, [A0, 0], L2, C.Wasm.Memory{pg, lm, m})
      +C2 = Q.Cfg(R2, LS, [], L2, C.Wasm.Memory{pg, lm, m1})
      +C3 = Q.Cfg(R3, LS, [on, 0], L2, C.Wasm.Memory{pg, lm, m1})
      +C4 = Q.Cfg(BR, LS, [], L2, C.Wasm.Memory{pg, lm, m2})
      +mm = {C.Wasm.Memory{pg, lm, m2} : C.Wasm.Memory}
      +hin0 = Z.inside.ok(pg, 0, 0, 4, W, hW, Unit{}, N.le_trans(4n, 20n, Q.PB(pg), Unit{}, p20), hb)
      +hin4 = Z.inside.ok(pg, 0, 4, 4, W, hW, Unit{}, N.le_trans(8n, 20n, Q.PB(pg), Unit{}, p20), hb)
      +e1 = {{==} : {PH.H.steps(12n, C0) == C1 : C.Wasm.Step}}
      +e2 = F.store.step(0, 0, A0, R2, LS, [], L2, pg, lm, m, hin0)
      +e3 = {{==} : {PH.H.steps(2n, C2) == C3 : C.Wasm.Step}}
      +e4 = F.store.step(4, 0, on, BR, LS, [], L2, pg, lm, m1, hin4)
      +e5 = exit.steps(1n+d, LS, hL, ej, L2, mm)
      +e45 = S.steps.then(1n, 3n, C3, C4, C.Wasm.Step.done{[s0], mm}, e4, e5)
      +e35 = S.steps.then(2n, 4n, C2, C3, C.Wasm.Step.done{[s0], mm}, e3, e45)
      +e25 = S.steps.then(1n, 6n, C1, C2, C.Wasm.Step.done{[s0], mm}, e2, e35)
      +e15 = S.steps.then(12n, 7n, C0, C1, C.Wasm.Step.done{[s0], mm}, e1, e25)
      +es0 = Y.U32.eq(s0, 0, ez)
      +ok = {(%Equal.sym(U32, s0, 0, es0) : HaltOK(_, nx, pg, ou, mm);
          haltok0(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI, W, hW, hP, hG)) : HaltOK(s0, nx, pg, ou, mm)}
      (19n, (mm, (e15, ok)))

# halt{s}
def sim.halt(+s0: U32, +rg: List<&2, U32>, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32,
  +d: Nat, +K: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +hL: {List.drop(&2, C.Wasm.Label, ls, d) == [RL()] : List<&2, C.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +m: C.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat}, +hd: N.Le(Nat.add(d, 2n), U32.to_nat(MD))) ->
  SPost(C.Cir.Out.halt{s0, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)}, C.Cir.code.stmt(C.Cir.Stmt.halt{s0}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G):
  halt.z(U32.is_zero(s0), s0, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, MD, P, G, a, n, t, nd, ad, m, hI, W, hW, hP, hG, hd, {==})

# Steps of the control
# --------------------

# eqz, then br_if l, of a value that is not 0: no branch
def brif.go(+vc: U32, ez: {U32.is_zero(vc) == False{} : Bool}, +l: U32, +rest: List<&2, C.Wasm.Instr>,
  +ls: List<&2, C.Wasm.Label>, +L: List<&2, U32>, +M: C.Wasm.Memory) ->
  {PH.H.steps(2n, Q.Cfg(Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{l}, rest}}, ls, [vc], L, M)) == Q.Cfg(rest, ls, [], L, M) : C.Wasm.Step}:
  %Equal.sym(Bool, U32.is_zero(vc), False{}, ez) :
    {C.Wasm.step.br_if.if(U32.is_zero(Bool.to_u32(_)), l, rest, ls, 1n, [], L, M) == Q.Cfg(rest, ls, [], L, M) : C.Wasm.Step}
  {==}

# eqz, then br_if 0, of 0: a branch to the end of the block
def brif.br0(+vc: U32, ez: {U32.is_zero(vc) == True{} : Bool}, +rest: List<&2, C.Wasm.Instr>, +after: List<&2, C.Wasm.Instr>,
  +outer: List<&2, C.Wasm.Label>, +L: List<&2, U32>, +M: C.Wasm.Memory) ->
  {PH.H.steps(2n, Q.Cfg(Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{0}, rest}}, Con{C.Wasm.Label{None{}, after, 0n}, outer}, [vc], L, M)) ==
    Q.Cfg(after, outer, [], L, M) : C.Wasm.Step}:
  %Equal.sym(Bool, U32.is_zero(vc), True{}, ez) :
    {C.Wasm.step.br_if.if(U32.is_zero(Bool.to_u32(_)), 0, rest, Con{C.Wasm.Label{None{}, after, 0n}, outer}, 1n, [], L, M) ==
      Q.Cfg(after, outer, [], L, M) : C.Wasm.Step}
  {==}

# eqz, then br_if 1, of 0: a branch to the end of the outer block
def brif.br1(+vc: U32, ez: {U32.is_zero(vc) == True{} : Bool}, +rest: List<&2, C.Wasm.Instr>, +l0: C.Wasm.Label,
  +after: List<&2, C.Wasm.Instr>, +outer: List<&2, C.Wasm.Label>, +L: List<&2, U32>, +M: C.Wasm.Memory) ->
  {PH.H.steps(2n, Q.Cfg(Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, rest}}, Con{l0, Con{C.Wasm.Label{None{}, after, 0n}, outer}}, [vc], L, M)) ==
    Q.Cfg(after, outer, [], L, M) : C.Wasm.Step}:
  %Equal.sym(Bool, U32.is_zero(vc), True{}, ez) :
    {C.Wasm.step.br_if.if(U32.is_zero(Bool.to_u32(_)), 1, rest, Con{l0, Con{C.Wasm.Label{None{}, after, 0n}, outer}}, 1n, [], L, M) ==
      Q.Cfg(after, outer, [], L, M) : C.Wasm.Step}
  {==}

# register r is local 8 + r
def reg.nat(+r: Nat, +R: Nat, +MX: U32, ok: {Nat.is_lt(r, R) == True{} : Bool}, hR: N.Le(8n+R, U32.to_nat(MX))) ->
  {U32.to_nat(C.Cir.l.reg(r)) == 8n+r : Nat}:
  +le = N.le_trans(8n+r, 8n+R, U32.to_nat(MX), N.weaken(r, R, M.lt_le(r, R, ok)), hR)
  Equal.trans(Nat, U32.to_nat(C.Cir.l.reg(r)), U32.to_nat(U32.from_nat(8n+r)), 8n+r,
    Equal.cong(U32, Nat, z => U32.to_nat(z), C.Cir.l.reg(r), U32.from_nat(8n+r), V.add8(r)), M.tofrom(8n+r, MX, le))

# local.set of register r
def set.step(+r: Nat, +v: U32, +K: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32,
  +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +m: C.Wasm.Bytes, hr: {U32.to_nat(C.Cir.l.reg(r)) == 8n+r : Nat}) ->
  {PH.H.steps(1n, Q.Cfg(Con{C.Cir.i.set(C.Cir.l.reg(r)), K}, ls, [v], Q.Loc(a, n, 2, nx, on, t, nd, ad, rg), C.Wasm.Memory{pg, lm, m})) ==
    Cf(K, ls, a, n, t, nd, ad, List.set(&2, U32, rg, r, v), nx, on, pg, lm, m) : C.Wasm.Step}:
  %Equal.sym(Nat, U32.to_nat(C.Cir.l.reg(r)), 8n+r, hr) :
    {C.Wasm.Step.next{C.Wasm.Frame{K, ls, 1n, [], List.set(&2, U32, Q.Loc(a, n, 2, nx, on, t, nd, ad, rg), _, v)}, C.Wasm.Memory{pg, lm, m}} ==
      Cf(K, ls, a, n, t, nd, ad, List.set(&2, U32, rg, r, v), nx, on, pg, lm, m) : C.Wasm.Step}
  {==}

# The code of a frame, and its labels
def st.code(st: C.Wasm.Step) -> List<&2, C.Wasm.Instr>:
  match st:
    case C.Wasm.Step.next{C.Wasm.Frame{code, _, _, _, _}, _}:
      code
    case _:
      []

def st.labels(st: C.Wasm.Step) -> List<&2, C.Wasm.Label>:
  match st:
    case C.Wasm.Step.next{C.Wasm.Frame{_, ls, _, _, _}, _}:
      ls
    case _:
      []

def ne.len(+x: Nat, e: {1n+x == x : Nat}) -> Empty:
  N.not_succ_le(x, N.le_rw_l(x, 1n+x, x, Equal.sym(Nat, 1n+x, x, e), N.le_refl(x)))

# a code is not its own tail
def code.ne(+i: C.Wasm.Instr, +K: List<&2, C.Wasm.Instr>, e: {Con{i, K} == K : List<&2, C.Wasm.Instr>}) -> Empty:
  ne.len(List.length(&2, C.Wasm.Instr, K),
    Equal.cong(List<&2, C.Wasm.Instr>, Nat, l => List.length(&2, C.Wasm.Instr, l), Con{i, K}, K, e))

def labels.ne(+l: C.Wasm.Label, +ls: List<&2, C.Wasm.Label>, e: {Con{l, ls} == ls : List<&2, C.Wasm.Label>}) -> Empty:
  ne.len(List.length(&2, C.Wasm.Label, ls),
    Equal.cong(List<&2, C.Wasm.Label>, Nat, z => List.length(&2, C.Wasm.Label, z), Con{l, ls}, ls, e))

# n steps from x, whose first two steps reach y, and that reach z, which is
# neither x nor the step after it, are n - 2 steps from y
def skip2(+N0: Nat, +fr: C.Wasm.Frame, +mm: C.Wasm.Memory, +fr1: C.Wasm.Frame, +m1: C.Wasm.Memory, +Yv: C.Wasm.Step, -Zv: C.Wasm.Step,
  e: {PH.H.steps(N0, C.Wasm.Step.next{fr, mm}) == Zv : C.Wasm.Step},
  h1: {C.Wasm.step(fr, mm) == C.Wasm.Step.next{fr1, m1} : C.Wasm.Step},
  h2: {C.Wasm.step(fr1, m1) == Yv : C.Wasm.Step},
  ne0: {C.Wasm.Step.next{fr, mm} == Zv : C.Wasm.Step} -> Empty,
  ne1: {C.Wasm.Step.next{fr1, m1} == Zv : C.Wasm.Step} -> Empty) ->
  {PH.H.steps(Nat.sub(N0, 2n), Yv) == Zv : C.Wasm.Step}:
  match N0:
    case 0n:
      Empty.absurd({PH.H.steps(0n, Yv) == Zv : C.Wasm.Step}, ne0(e))
    case 1n+N1:
      match N1:
        case 0n:
          Empty.absurd({PH.H.steps(0n, Yv) == Zv : C.Wasm.Step}, ne1(Equal.trans(C.Wasm.Step, C.Wasm.Step.next{fr1, m1}, C.Wasm.step(fr, mm), Zv,
            Equal.sym(C.Wasm.Step, C.Wasm.step(fr, mm), C.Wasm.Step.next{fr1, m1}, h1), e)))
        case 1n+N2:
          +e1 = Equal.trans(C.Wasm.Step, PH.H.steps(1n+N2, C.Wasm.Step.next{fr1, m1}), PH.H.steps(1n+N2, C.Wasm.step(fr, mm)), Zv,
            Equal.cong(C.Wasm.Step, C.Wasm.Step, x => PH.H.steps(1n+N2, x), C.Wasm.Step.next{fr1, m1}, C.Wasm.step(fr, mm),
              Equal.sym(C.Wasm.Step, C.Wasm.step(fr, mm), C.Wasm.Step.next{fr1, m1}, h1)), e)
          %Equal.sym(Nat, Nat.sub(N2, 0n), N2, Q.sub0(N2)) : {PH.H.steps(_, Yv) == Zv : C.Wasm.Step}
          Equal.trans(C.Wasm.Step, PH.H.steps(N2, Yv), PH.H.steps(N2, C.Wasm.step(fr1, m1)), Zv,
            Equal.cong(C.Wasm.Step, C.Wasm.Step, x => PH.H.steps(N2, x), Yv, C.Wasm.step(fr1, m1), Equal.sym(C.Wasm.Step, C.Wasm.step(fr1, m1), Yv, h2)), e1)

# Depths
# ------

def dep.seq.l(+d: Nat, +x: Nat, +y: Nat, +MD: U32, h: N.Le(Nat.add(d, Nat.add(x, y)), U32.to_nat(MD))) -> N.Le(Nat.add(d, x), U32.to_nat(MD)):
  N.le_trans(Nat.add(d, x), Nat.add(Nat.add(d, x), y), U32.to_nat(MD), N.le_add_r(Nat.add(d, x), y),
    N.le_rw_l(Nat.add(d, Nat.add(x, y)), Nat.add(Nat.add(d, x), y), U32.to_nat(MD),
      Equal.sym(Nat, Nat.add(Nat.add(d, x), y), Nat.add(d, Nat.add(x, y)), Z.add.assoc(d, x, y)), h))

def dep.seq.r(+d: Nat, +x: Nat, +y: Nat, +MD: U32, h: N.Le(Nat.add(d, Nat.add(x, y)), U32.to_nat(MD))) -> N.Le(Nat.add(d, y), U32.to_nat(MD)):
  dep.seq.l(d, y, x, MD, N.le_rw_l(Nat.add(d, Nat.add(x, y)), Nat.add(d, Nat.add(y, x)), U32.to_nat(MD),
    Equal.cong(Nat, Nat, z => Nat.add(d, z), Nat.add(x, y), Nat.add(y, x), Z.add.comm(x, y)), h))

def dep.two(+d: Nat, +x: Nat, +MD: U32, h: N.Le(Nat.add(d, 2n+x), U32.to_nat(MD))) -> N.Le(Nat.add(2n+d, x), U32.to_nat(MD)):
  N.le_rw_l(Nat.add(d, 2n+x), 2n+Nat.add(d, x), U32.to_nat(MD),
    Equal.trans(Nat, Nat.add(d, 2n+x), 1n+Nat.add(d, 1n+x), 2n+Nat.add(d, x), N.add_succ_r(d, 1n+x),
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(d, 1n+x), 1n+Nat.add(d, x), N.add_succ_r(d, x))), h)

def dep.if.t(+d: Nat, +x: Nat, +y: Nat, +MD: U32, h: N.Le(Nat.add(d, 2n+Nat.add(x, y)), U32.to_nat(MD))) -> N.Le(Nat.add(2n+d, x), U32.to_nat(MD)):
  dep.seq.l(2n+d, x, y, MD, dep.two(d, Nat.add(x, y), MD, h))

def dep.if.e(+d: Nat, +x: Nat, +y: Nat, +MD: U32, h: N.Le(Nat.add(d, 2n+Nat.add(x, y)), U32.to_nat(MD))) -> N.Le(Nat.add(1n+d, y), U32.to_nat(MD)):
  N.weaken(Nat.add(1n+d, y), U32.to_nat(MD), dep.seq.r(2n+d, x, y, MD, dep.two(d, Nat.add(x, y), MD, h)))

# The statements of control
# -------------------------

def set.if(b: Bool, +r: Nat, +v: U32, +e: C.Cir.Expr, +rg: List<&2, U32>, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32,
  +d: Nat, +K: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +hL: {List.drop(&2, C.Wasm.Label, ls, d) == [RL()] : List<&2, C.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +m: C.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat}, +tE: U32,
  ex: {PH.H.steps(E.cost(e), Cf(C.Cir.code.expr(e, Con{C.Cir.i.set(C.Cir.l.reg(r)), K}), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m)) ==
    Q.Cfg(Con{C.Cir.i.set(C.Cir.l.reg(r)), K}, ls, [v], Q.Loc(a, n, 2, nx, on, tE, nd, ad, rg), C.Wasm.Memory{pg, lm, m}) : C.Wasm.Step},
  hr: {U32.to_nat(C.Cir.l.reg(r)) == 8n+r : Nat}) ->
  SPost(C.Cir.exec.set.of(C.Cir.regs.set.if(b, rg, r, v), Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), C.Cir.code.stmt(C.Cir.Stmt.set{r, e}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G):
  match b:
    case True{}:
      +C0 = Cf(C.Cir.code.expr(e, Con{C.Cir.i.set(C.Cir.l.reg(r)), K}), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m)
      +C1 = Q.Cfg(Con{C.Cir.i.set(C.Cir.l.reg(r)), K}, ls, [v], Q.Loc(a, n, 2, nx, on, tE, nd, ad, rg), C.Wasm.Memory{pg, lm, m})
      +C2 = Cf(K, ls, a, n, tE, nd, ad, List.set(&2, U32, rg, r, v), nx, on, pg, lm, m)
      (Nat.add(E.cost(e), 1n), (tE, (nd, (ad, (m, (S.steps.then(E.cost(e), 1n, C0, C1, C2, ex,
        set.step(r, v, K, ls, a, n, tE, nd, ad, rg, nx, on, pg, lm, m, hr)), hI))))))
    case False{}:
      Unit{}

def set.of(mv: Maybe<&2, U32>, +r: Nat, +e: C.Cir.Expr, +rg: List<&2, U32>, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32,
  +d: Nat, +K: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +hL: {List.drop(&2, C.Wasm.Label, ls, d) == [RL()] : List<&2, C.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +m: C.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat},
  +ok: {V.ok.stmt(C.Cir.Stmt.set{r, e}, R) == True{} : Bool}, ev: {C.Cir.eval(e, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)) == mv : Maybe<&2, U32>}) ->
  SPost(C.Cir.exec.set(r, mv, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), C.Cir.code.stmt(C.Cir.Stmt.set{r, e}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G):
  match mv:
    case None{}:
      Unit{}
    case Some{+v}:
      set.if(Nat.is_lt(r, List.length(&2, U32, rg)), r, v, e, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, m, hI, W, hW, hP, hG, E.tmpE(e, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)),
        E.sim.expr(e, rg, cl, nx, fi, im, pg, lm, inp, ou, on, v, ev, R, MX, I.and.r(Nat.is_lt(r, R), V.ok.expr(e, R), ok), hR,
          Con{C.Cir.i.set(C.Cir.l.reg(r)), K}, ls, [], P, G, a, n, 2, t, nd, ad, m, hI, W, hW, hP, hG),
        reg.nat(r, R, MX, I.and.l(Nat.is_lt(r, R), V.ok.expr(e, R), ok), hR))

def if.z(z: Bool, +fuel: Nat, +c: C.Cir.Expr, +te: C.Cir.Stmt, +ee: C.Cir.Stmt, +vc: U32, +rg: List<&2, U32>, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32,
  +d: Nat, +K: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +hL: {List.drop(&2, C.Wasm.Label, ls, d) == [RL()] : List<&2, C.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +m: C.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat},
  +ez: {U32.is_zero(vc) == z : Bool},
  +ex: {PH.H.steps(E.cost(c), Q.Cfg(C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{0}, C.Cir.code.stmt(te, 2n+d, [C.Wasm.Instr.br{1}])}}), Con{C.Wasm.Label{None{}, C.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, [], Q.Loc(a, n, 2, nx, on, t, nd, ad, rg), C.Wasm.Memory{pg, lm, m})) ==
    Q.Cfg(Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{0}, C.Cir.code.stmt(te, 2n+d, [C.Wasm.Instr.br{1}])}}, Con{C.Wasm.Label{None{}, C.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, [vc], Q.Loc(a, n, 2, nx, on, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg), C.Wasm.Memory{pg, lm, m}) : C.Wasm.Step},
  pt: SPost(C.Cir.exec(fuel, te, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), C.Cir.code.stmt(te, 2n+d, [C.Wasm.Instr.br{1}]), Con{C.Wasm.Label{None{}, C.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, [C.Wasm.Instr.br{1}], Con{C.Wasm.Label{None{}, C.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, m, P, G),
  pe: SPost(C.Cir.exec(fuel, ee, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), C.Cir.code.stmt(ee, 1n+d, []), Con{C.Wasm.Label{None{}, K, 0n}, ls}, [], Con{C.Wasm.Label{None{}, K, 0n}, ls}, a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, m, P, G)) ->
  SPost(C.Cir.exec.if.of(z, u => C.Cir.exec(fuel, te, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), u => C.Cir.exec(fuel, ee, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on))),
    C.Cir.code.stmt(C.Cir.Stmt.if{c, te, ee}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G):
  match z:
    case False{}:
      +C0 = Cf(C.Cir.code.stmt(C.Cir.Stmt.if{c, te, ee}, d, K), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m)
      +C1 = Q.Cfg(C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{0}, C.Cir.code.stmt(te, 2n+d, [C.Wasm.Instr.br{1}])}}), Con{C.Wasm.Label{None{}, C.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, [], Q.Loc(a, n, 2, nx, on, t, nd, ad, rg), C.Wasm.Memory{pg, lm, m})
      +C2 = Q.Cfg(Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{0}, C.Cir.code.stmt(te, 2n+d, [C.Wasm.Instr.br{1}])}}, Con{C.Wasm.Label{None{}, C.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, [vc], Q.Loc(a, n, 2, nx, on, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg), C.Wasm.Memory{pg, lm, m})
      +C3 = Cf(C.Cir.code.stmt(te, 2n+d, [C.Wasm.Instr.br{1}]), Con{C.Wasm.Label{None{}, C.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, m)
      post.wrap(C.Cir.exec(fuel, te, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), C.Cir.code.stmt(C.Cir.Stmt.if{c, te, ee}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G,
        C.Cir.code.stmt(te, 2n+d, [C.Wasm.Instr.br{1}]), Con{C.Wasm.Label{None{}, C.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, [C.Wasm.Instr.br{1}], Con{C.Wasm.Label{None{}, C.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, m, Nat.add(2n, Nat.add(E.cost(c), 2n)),
        S.steps.then(2n, Nat.add(E.cost(c), 2n), C0, C1, C3, {==}, S.steps.then(E.cost(c), 2n, C1, C2, C3, ex,
          brif.go(vc, ez, 0, C.Cir.code.stmt(te, 2n+d, [C.Wasm.Instr.br{1}]), Con{C.Wasm.Label{None{}, C.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, Q.Loc(a, n, 2, nx, on, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg), C.Wasm.Memory{pg, lm, m}))),
        1n, t2 => nd2 => ad2 => rg2 => nx2 => on2 => pg2 => lm2 => m2 => {==}, pt)
    case True{}:
      +C0 = Cf(C.Cir.code.stmt(C.Cir.Stmt.if{c, te, ee}, d, K), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m)
      +C1 = Q.Cfg(C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{0}, C.Cir.code.stmt(te, 2n+d, [C.Wasm.Instr.br{1}])}}), Con{C.Wasm.Label{None{}, C.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, [], Q.Loc(a, n, 2, nx, on, t, nd, ad, rg), C.Wasm.Memory{pg, lm, m})
      +C2 = Q.Cfg(Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{0}, C.Cir.code.stmt(te, 2n+d, [C.Wasm.Instr.br{1}])}}, Con{C.Wasm.Label{None{}, C.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, [vc], Q.Loc(a, n, 2, nx, on, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg), C.Wasm.Memory{pg, lm, m})
      +C3 = Cf(C.Cir.code.stmt(ee, 1n+d, []), Con{C.Wasm.Label{None{}, K, 0n}, ls}, a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, m)
      post.wrap(C.Cir.exec(fuel, ee, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), C.Cir.code.stmt(C.Cir.Stmt.if{c, te, ee}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G,
        C.Cir.code.stmt(ee, 1n+d, []), Con{C.Wasm.Label{None{}, K, 0n}, ls}, [], Con{C.Wasm.Label{None{}, K, 0n}, ls}, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, m, Nat.add(2n, Nat.add(E.cost(c), 2n)),
        S.steps.then(2n, Nat.add(E.cost(c), 2n), C0, C1, C3, {==}, S.steps.then(E.cost(c), 2n, C1, C2, C3, ex,
          brif.br0(vc, ez, C.Cir.code.stmt(te, 2n+d, [C.Wasm.Instr.br{1}]), C.Cir.code.stmt(ee, 1n+d, []), Con{C.Wasm.Label{None{}, K, 0n}, ls}, Q.Loc(a, n, 2, nx, on, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg), C.Wasm.Memory{pg, lm, m}))),
        1n, t2 => nd2 => ad2 => rg2 => nx2 => on2 => pg2 => lm2 => m2 => {==}, pe)

def if.of(mv: Maybe<&2, U32>, +fuel: Nat, +c: C.Cir.Expr, +te: C.Cir.Stmt, +ee: C.Cir.Stmt, +rg: List<&2, U32>, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32,
  +d: Nat, +K: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +hL: {List.drop(&2, C.Wasm.Label, ls, d) == [RL()] : List<&2, C.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +m: C.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat},
  +okc: {V.ok.expr(c, R) == True{} : Bool}, ev: {C.Cir.eval(c, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)) == mv : Maybe<&2, U32>},
  pt: SPost(C.Cir.exec(fuel, te, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), C.Cir.code.stmt(te, 2n+d, [C.Wasm.Instr.br{1}]), Con{C.Wasm.Label{None{}, C.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, [C.Wasm.Instr.br{1}], Con{C.Wasm.Label{None{}, C.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, m, P, G),
  pe: SPost(C.Cir.exec(fuel, ee, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), C.Cir.code.stmt(ee, 1n+d, []), Con{C.Wasm.Label{None{}, K, 0n}, ls}, [], Con{C.Wasm.Label{None{}, K, 0n}, ls}, a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, m, P, G)) ->
  SPost(C.Cir.exec.if(mv, u => C.Cir.exec(fuel, te, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), u => C.Cir.exec(fuel, ee, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on))),
    C.Cir.code.stmt(C.Cir.Stmt.if{c, te, ee}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G):
  match mv:
    case None{}:
      Unit{}
    case Some{+vc}:
      if.z(U32.is_zero(vc), fuel, c, te, ee, vc, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, m, hI, W, hW, hP, hG, {==},
        E.sim.expr(c, rg, cl, nx, fi, im, pg, lm, inp, ou, on, vc, ev, R, MX, okc, hR, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{0}, C.Cir.code.stmt(te, 2n+d, [C.Wasm.Instr.br{1}])}}, Con{C.Wasm.Label{None{}, C.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, [], P, G, a, n, 2, t, nd, ad, m, hI, W, hW, hP, hG),
        pt, pe)

# a run of the loop from its start, seen from the branch back to it
def post.skip(o: C.Cir.Out, +c: C.Cir.Expr, +body: C.Cir.Stmt, +d: Nat, +K: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>,
  +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +m: C.Wasm.Bytes,
  +P: Nat, +G: Nat, p: SPost(o, C.Cir.code.stmt(C.Cir.Stmt.while{c, body}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G)) ->
  SPost(o, [C.Wasm.Instr.br{0}], Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G):
  match o:
    case C.Cir.Out.next{st2}:
      match st2:
        case C.Cir.State{+rg3, +cl3, +nx3, +fi3, +im3, +pg3, +lm3, +inp3, +ou3, +on3}:
          (+N2, p1) = p
          (+t3, p2) = p1
          (+nd3, p3) = p2
          (+ad3, p4) = p3
          (+m3, p5) = p4
          (eq, hI) = p5
          +L = Q.Loc(a, n, 2, nx, on, t, nd, ad, rg)
          +mm = {C.Wasm.Memory{pg, lm, m} : C.Wasm.Memory}
          +fr = {C.Wasm.Frame{C.Cir.code.stmt(C.Cir.Stmt.while{c, body}, d, K), ls, 1n, [], L} : C.Wasm.Frame}
          +fr1 = {C.Wasm.Frame{[C.Wasm.Instr.loop{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}], Con{C.Wasm.Label{None{}, K, 0n}, ls}, 1n, [], L} : C.Wasm.Frame}
          +Yv = Cf(C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}}), Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, a, n, t, nd, ad, rg, nx, on, pg, lm, m)
          +Cb = Cf([C.Wasm.Instr.br{0}], Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, a, n, t, nd, ad, rg, nx, on, pg, lm, m)
          +END = Cf(K, ls, a, n, t3, nd3, ad3, rg3, nx3, on3, pg3, lm3, m3)
          +sk = skip2(N2, fr, mm, fr1, mm, Yv, END, eq, {==}, {==},
            e => code.ne(C.Wasm.Instr.block{[C.Wasm.Instr.loop{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}]}, K,
              Equal.cong(C.Wasm.Step, List<&2, C.Wasm.Instr>, x => st.code(x), C.Wasm.Step.next{fr, mm}, END, e)),
            e => labels.ne(C.Wasm.Label{None{}, K, 0n}, ls, Equal.cong(C.Wasm.Step, List<&2, C.Wasm.Label>, x => st.labels(x), C.Wasm.Step.next{fr1, mm}, END, e)))
          (Nat.add(1n, Nat.sub(N2, 2n)), (t3, (nd3, (ad3, (m3, (S.steps.then(1n, Nat.sub(N2, 2n), Cb, Yv, END, {==}, sk), hI))))))
    case C.Cir.Out.halt{+s0, st2}:
      match st2:
        case C.Cir.State{+rg3, +cl3, +nx3, +fi3, +im3, +pg3, +lm3, +inp3, +ou3, +on3}:
          (+N2, p1) = p
          (+mm2, p2) = p1
          (eq, ok) = p2
          +L = Q.Loc(a, n, 2, nx, on, t, nd, ad, rg)
          +mm = {C.Wasm.Memory{pg, lm, m} : C.Wasm.Memory}
          +fr = {C.Wasm.Frame{C.Cir.code.stmt(C.Cir.Stmt.while{c, body}, d, K), ls, 1n, [], L} : C.Wasm.Frame}
          +fr1 = {C.Wasm.Frame{[C.Wasm.Instr.loop{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}], Con{C.Wasm.Label{None{}, K, 0n}, ls}, 1n, [], L} : C.Wasm.Frame}
          +Yv = Cf(C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}}), Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, a, n, t, nd, ad, rg, nx, on, pg, lm, m)
          +Cb = Cf([C.Wasm.Instr.br{0}], Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, a, n, t, nd, ad, rg, nx, on, pg, lm, m)
          +END = {C.Wasm.Step.done{[s0], mm2} : C.Wasm.Step}
          +sk = skip2(N2, fr, mm, fr1, mm, Yv, END, eq, {==}, {==}, e => S.next.not_done(fr, mm, [s0], mm2, e),
            e => S.next.not_done(fr1, mm, [s0], mm2, e))
          (Nat.add(1n, Nat.sub(N2, 2n)), (mm2, (S.steps.then(1n, Nat.sub(N2, 2n), Cb, Yv, END, {==}, sk), ok)))
    case C.Cir.Out.out_of_memory{}:
      (+N2, p1) = p
      (+mm2, eq) = p1
      +L = Q.Loc(a, n, 2, nx, on, t, nd, ad, rg)
      +mm = {C.Wasm.Memory{pg, lm, m} : C.Wasm.Memory}
      +fr = {C.Wasm.Frame{C.Cir.code.stmt(C.Cir.Stmt.while{c, body}, d, K), ls, 1n, [], L} : C.Wasm.Frame}
      +fr1 = {C.Wasm.Frame{[C.Wasm.Instr.loop{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}], Con{C.Wasm.Label{None{}, K, 0n}, ls}, 1n, [], L} : C.Wasm.Frame}
      +Yv = Cf(C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}}), Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, a, n, t, nd, ad, rg, nx, on, pg, lm, m)
      +Cb = Cf([C.Wasm.Instr.br{0}], Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, a, n, t, nd, ad, rg, nx, on, pg, lm, m)
      +END = {C.Wasm.Step.done{[1], mm2} : C.Wasm.Step}
      +sk = skip2(N2, fr, mm, fr1, mm, Yv, END, eq, {==}, {==}, e => S.next.not_done(fr, mm, [1], mm2, e),
        e => S.next.not_done(fr1, mm, [1], mm2, e))
      (Nat.add(1n, Nat.sub(N2, 2n)), (mm2, S.steps.then(1n, Nat.sub(N2, 2n), Cb, Yv, END, {==}, sk)))
    case C.Cir.Out.trap{}:
      Unit{}
    case C.Cir.Out.not_done{}:
      Unit{}

def while.z(z: Bool, +f: Nat, +c: C.Cir.Expr, +body: C.Cir.Stmt, +vc: U32, +rg: List<&2, U32>, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32,
  +d: Nat, +K: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +hL: {List.drop(&2, C.Wasm.Label, ls, d) == [RL()] : List<&2, C.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +m: C.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat},
  +ez: {U32.is_zero(vc) == z : Bool},
  +ex: {PH.H.steps(E.cost(c), Q.Cfg(C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}}), Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, [], Q.Loc(a, n, 2, nx, on, t, nd, ad, rg), C.Wasm.Memory{pg, lm, m})) ==
    Q.Cfg(Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}}, Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, [vc], Q.Loc(a, n, 2, nx, on, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg), C.Wasm.Memory{pg, lm, m}) : C.Wasm.Step},
  pb: SPost(C.Cir.exec(f, body, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}]), Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, [C.Wasm.Instr.br{0}], Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, m, P, G),
  kont: @rg2: List<&2, U32> -> @cl2: C.Cir.Cells -> @nx2: U32 -> @fi2: U32 -> @im2: U32 -> @pg2: U32 -> @lm2: U32 ->
    @inp2: List<&2, U32> -> @ou2: List<&2, U32> -> @on2: U32 -> @t2: U32 -> @nd2: U32 -> @ad2: U32 -> @m2: C.Wasm.Bytes ->
    Q.Inv(P, G, a, n, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2, m2) ->
    SPost(C.Cir.exec(f, C.Cir.Stmt.while{c, body}, C.Cir.State{rg2, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2}), [C.Wasm.Instr.br{0}], Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, K, ls,
      a, n, t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, m2, P, G)) ->
  SPost(C.Cir.exec.if.of(z, u => C.Cir.exec.then(C.Cir.exec(f, body, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), tt => C.Cir.exec(f, C.Cir.Stmt.while{c, body}, tt)),
    u => C.Cir.Out.next{Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)}), C.Cir.code.stmt(C.Cir.Stmt.while{c, body}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G):
  match z:
    case True{}:
      +C0 = Cf(C.Cir.code.stmt(C.Cir.Stmt.while{c, body}, d, K), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m)
      +Ch = Cf(C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}}), Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, a, n, t, nd, ad, rg, nx, on, pg, lm, m)
      +C2 = Q.Cfg(Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}}, Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, [vc], Q.Loc(a, n, 2, nx, on, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg), C.Wasm.Memory{pg, lm, m})
      +C3 = Cf(K, ls, a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, m)
      (Nat.add(2n, Nat.add(E.cost(c), 2n)), (E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), (nd, (ad, (m, (S.steps.then(2n, Nat.add(E.cost(c), 2n), C0, Ch, C3, {==},
        S.steps.then(E.cost(c), 2n, Ch, C2, C3, ex,
          brif.br1(vc, ez, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}]), C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, K, ls, Q.Loc(a, n, 2, nx, on, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg), C.Wasm.Memory{pg, lm, m}))), hI))))))
    case False{}:
      +C0 = Cf(C.Cir.code.stmt(C.Cir.Stmt.while{c, body}, d, K), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m)
      +Ch = Cf(C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}}), Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, a, n, t, nd, ad, rg, nx, on, pg, lm, m)
      +C2 = Q.Cfg(Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}}, Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, [vc], Q.Loc(a, n, 2, nx, on, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg), C.Wasm.Memory{pg, lm, m})
      +C3 = Cf(C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}]), Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, m)
      post.pre(C.Cir.exec.then(C.Cir.exec(f, body, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), tt => C.Cir.exec(f, C.Cir.Stmt.while{c, body}, tt)), C.Cir.code.stmt(C.Cir.Stmt.while{c, body}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G,
        C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}]), Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, m, Nat.add(2n, Nat.add(E.cost(c), 2n)),
        S.steps.then(2n, Nat.add(E.cost(c), 2n), C0, Ch, C3, {==}, S.steps.then(E.cost(c), 2n, Ch, C2, C3, ex,
          brif.go(vc, ez, 1, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}]), Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, Q.Loc(a, n, 2, nx, on, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg), C.Wasm.Memory{pg, lm, m}))),
        post.then(C.Cir.exec(f, body, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), tt => C.Cir.exec(f, C.Cir.Stmt.while{c, body}, tt), C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}]), Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, [C.Wasm.Instr.br{0}], Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}},
          K, ls, a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, m, P, G, pb, kont))

def while.of(mv: Maybe<&2, U32>, +f: Nat, +c: C.Cir.Expr, +body: C.Cir.Stmt, +rg: List<&2, U32>, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32,
  +d: Nat, +K: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +hL: {List.drop(&2, C.Wasm.Label, ls, d) == [RL()] : List<&2, C.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +m: C.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat},
  +okc: {V.ok.expr(c, R) == True{} : Bool}, ev: {C.Cir.eval(c, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)) == mv : Maybe<&2, U32>},
  pb: SPost(C.Cir.exec(f, body, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}]), Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, [C.Wasm.Instr.br{0}], Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, m, P, G),
  kont: @rg2: List<&2, U32> -> @cl2: C.Cir.Cells -> @nx2: U32 -> @fi2: U32 -> @im2: U32 -> @pg2: U32 -> @lm2: U32 ->
    @inp2: List<&2, U32> -> @ou2: List<&2, U32> -> @on2: U32 -> @t2: U32 -> @nd2: U32 -> @ad2: U32 -> @m2: C.Wasm.Bytes ->
    Q.Inv(P, G, a, n, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2, m2) ->
    SPost(C.Cir.exec(f, C.Cir.Stmt.while{c, body}, C.Cir.State{rg2, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2}), [C.Wasm.Instr.br{0}], Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, K, ls,
      a, n, t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, m2, P, G)) ->
  SPost(C.Cir.exec.if(mv, u => C.Cir.exec.then(C.Cir.exec(f, body, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), tt => C.Cir.exec(f, C.Cir.Stmt.while{c, body}, tt)),
    u => C.Cir.Out.next{Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)}), C.Cir.code.stmt(C.Cir.Stmt.while{c, body}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G):
  match mv:
    case None{}:
      Unit{}
    case Some{+vc}:
      while.z(U32.is_zero(vc), f, c, body, vc, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, m, hI, W, hW, hP, hG, {==},
        E.sim.expr(c, rg, cl, nx, fi, im, pg, lm, inp, ou, on, vc, ev, R, MX, okc, hR, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}}, Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, [], P, G, a, n, 2, t, nd, ad, m, hI, W, hW, hP, hG),
        pb, kont)

# The simulation of statements
# ----------------------------

# when the run holds st at the code of s, d levels inside run's block (hL),
# the code does what Cir.exec says (SPost), when every register of s is
# below R (ok) and its branches out of run below MD (hd)
def sim.stmt(+fuel: Nat, s: C.Cir.Stmt, +rg: List<&2, U32>, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32,
  +d: Nat, +K: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +hL: {List.drop(&2, C.Wasm.Label, ls, d) == [RL()] : List<&2, C.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +m: C.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat},
  +ok: {V.ok.stmt(s, R) == True{} : Bool}, +hd: N.Le(Nat.add(d, dep(s)), U32.to_nat(MD))) ->
  SPost(C.Cir.exec(fuel, s, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), C.Cir.code.stmt(s, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G):
  match fuel s:
    case _ C.Cir.Stmt.nop{}:
      (0n, (t, (nd, (ad, (m, ({==}, hI))))))
    case _ C.Cir.Stmt.set{+r, +e}:
      set.of(C.Cir.eval(e, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), r, e, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, m, hI, W, hW, hP, hG, ok, {==})
    case _ C.Cir.Stmt.store{+k, +c, +v}:
      sim.store(k, c, v, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, m, hI, W, hW, hP, hG, ok)
    case _ C.Cir.Stmt.alloc{+r}:
      sim.alloc(r, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, m, hI, W, hW, hP, hG, ok, hd)
    case _ C.Cir.Stmt.emit{+v}:
      sim.emit(v, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, m, hI, W, hW, hP, hG, ok, hd)
    case _ C.Cir.Stmt.seq{+sa, +sb}:
      +Kb = C.Cir.code.stmt(sb, d, K)
      +oka = I.and.l(V.ok.stmt(sa, R), V.ok.stmt(sb, R), ok)
      +okb = I.and.r(V.ok.stmt(sa, R), V.ok.stmt(sb, R), ok)
      post.then(C.Cir.exec(fuel, sa, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), tt => C.Cir.exec(fuel, sb, tt), C.Cir.code.stmt(sa, d, Kb), ls, Kb, ls, K, ls,
        a, n, t, nd, ad, rg, nx, on, pg, lm, m, P, G,
        sim.stmt(fuel, sa, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, Kb, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, m, hI, W, hW, hP, hG,
          oka, dep.seq.l(d, dep(sa), dep(sb), MD, hd)),
        rg2 => cl2 => nx2 => fi2 => im2 => pg2 => lm2 => inp2 => ou2 => on2 => t2 => nd2 => ad2 => m2 => hI2 =>
          sim.stmt(fuel, sb, rg2, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t2, nd2, ad2, m2, hI2,
            W, hW, hP, hG, okb, dep.seq.r(d, dep(sa), dep(sb), MD, hd)))
    case _ C.Cir.Stmt.if{+c, +te, +ee}:
      +c01 = I.and.l(Bool.and(V.ok.expr(c, R), V.ok.stmt(te, R)), V.ok.stmt(ee, R), ok)
      +okc = I.and.l(V.ok.expr(c, R), V.ok.stmt(te, R), c01)
      +okt = I.and.r(V.ok.expr(c, R), V.ok.stmt(te, R), c01)
      +oke = I.and.r(Bool.and(V.ok.expr(c, R), V.ok.stmt(te, R)), V.ok.stmt(ee, R), ok)
      if.of(C.Cir.eval(c, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), fuel, c, te, ee, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, m, hI, W, hW, hP, hG, okc, {==},
        sim.stmt(fuel, te, rg, cl, nx, fi, im, pg, lm, inp, ou, on, 2n+d, [C.Wasm.Instr.br{1}], Con{C.Wasm.Label{None{}, C.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, hL, R, MX, hR, MD, P, G,
          a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, m, hI, W, hW, hP, hG, okt, dep.if.t(d, dep(te), dep(ee), MD, hd)),
        sim.stmt(fuel, ee, rg, cl, nx, fi, im, pg, lm, inp, ou, on, 1n+d, [], Con{C.Wasm.Label{None{}, K, 0n}, ls}, hL, R, MX, hR, MD, P, G,
          a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, m, hI, W, hW, hP, hG, oke, dep.if.e(d, dep(te), dep(ee), MD, hd)))
    case 0n C.Cir.Stmt.while{_, _}:
      Unit{}
    case 1n+f C.Cir.Stmt.while{+c, +body}:
      +okc = I.and.l(V.ok.expr(c, R), V.ok.stmt(body, R), ok)
      +okb = I.and.r(V.ok.expr(c, R), V.ok.stmt(body, R), ok)
      while.of(C.Cir.eval(c, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), f, c, body, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, m, hI, W, hW, hP, hG, okc, {==},
        sim.stmt(f, body, rg, cl, nx, fi, im, pg, lm, inp, ou, on, 2n+d, [C.Wasm.Instr.br{0}], Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, hL, R, MX, hR, MD, P, G,
          a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, m, hI, W, hW, hP, hG, okb, dep.two(d, dep(body), MD, hd)),
        +rg2 => +cl2 => +nx2 => +fi2 => +im2 => +pg2 => +lm2 => +inp2 => +ou2 => +on2 => +t2 => +nd2 => +ad2 => +m2 => hI2 =>
          post.skip(C.Cir.exec(f, C.Cir.Stmt.while{c, body}, C.Cir.State{rg2, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2}), c, body, d, K, ls,
            a, n, t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, m2, P, G,
            sim.stmt(f, C.Cir.Stmt.while{c, body}, rg2, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2, d, K, ls, hL, R, MX, hR, MD, P, G,
              a, n, t2, nd2, ad2, m2, hI2, W, hW, hP, hG, ok, hd)))
    case _ C.Cir.Stmt.halt{+s0}:
      sim.halt(s0, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, m, hI, W, hW, hP, hG, hd)
