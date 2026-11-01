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
# Cir.ended says, unless the output is empty
def HaltOK(+s0: U32, +ou: List<&2, U32>, +mem: C.Wasm.Memory) -> Data:
  Either<&2, &2, {C.Wasm.run.status(U32.is_eq(s0, 0), U32.is_eq(s0, 1), U32.is_eq(s0, 2), mem) ==
    C.Cir.ended.halt(U32.is_eq(s0, 0), U32.is_eq(s0, 1), U32.is_eq(s0, 2), ou) : C.Wasm.Outcome}, {ou == Nil{} : List<&2, U32>}>

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
    case C.Cir.State{_, _, _, _, _, _, _, _, +ou2, _}:
      S.EX(N2 => EXM(mm => S.P2({PH.H.steps(N2, Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, m)) ==
        C.Wasm.Step.done{[s0], mm} : C.Wasm.Step}, HaltOK(s0, ou2, mm))))

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
  ?TODO

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
  ?TODO

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
      ?TODO
    case _ C.Cir.Stmt.if{+c, +te, +ee}:
      ?TODO
    case 0n C.Cir.Stmt.while{_, _}:
      Unit{}
    case 1n+f C.Cir.Stmt.while{+c, +body}:
      +okc = I.and.l(V.ok.expr(c, R), V.ok.stmt(body, R), ok)
      +okb = I.and.r(V.ok.expr(c, R), V.ok.stmt(body, R), ok)
      while.of(C.Cir.eval(c, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), f, c, body, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, m, hI, W, hW, hP, hG, okc, {==},
        sim.stmt(f, body, rg, cl, nx, fi, im, pg, lm, inp, ou, on, 2n+d, [C.Wasm.Instr.br{0}], Con{C.Wasm.Label{Some{C.Cir.code.expr(c, Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])}})}, [], 0n}, Con{C.Wasm.Label{None{}, K, 0n}, ls}}, hL, R, MX, hR, MD, P, G,
          a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, m, hI, W, hW, hP, hG, okb, dep.two(d, dep(body), MD, hd)),
        rg2 => cl2 => nx2 => fi2 => im2 => pg2 => lm2 => inp2 => ou2 => on2 => t2 => nd2 => ad2 => m2 => hI2 =>
          post.skip(C.Cir.exec(f, C.Cir.Stmt.while{c, body}, C.Cir.State{rg2, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2}), c, body, d, K, ls,
            a, n, t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, m2, P, G,
            ?TODO))
    case _ C.Cir.Stmt.halt{+s0}:
      sim.halt(s0, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, m, hI, W, hW, hP, hG, hd)
