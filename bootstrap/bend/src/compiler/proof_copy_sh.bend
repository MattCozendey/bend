# compiler: M.shift gives Term.shift
# ==================================
#
# The proof of proof_copy.bend's Sh.ok: M.shift's walk (proof_copy_walk.bend)
# with the shift's registers (sroot, ss, scut, snew, sk, ssrc, sdep) and part.
# Sh.start makes the root and the first frame; Sh.loop, by induction on the
# fuel, runs the rounds, each of which (Sh.body) makes the measure smaller;
# Sh.end reads the copy from the root and releases the root.

import Base
import ./impl.bend as C
import ./proof_term.bend as T
import ./proof_need.bend as N
import ./proof_copy.bend as D
import ./proof_copy_kit.bend as K
import ./proof_copy_walk.bend as W

# The code
# --------

# a round of M.copy.walk's loop
def Wk.body(+stack: Nat, +depth: Nat, +top: Nat, +k: Nat, +at: Nat, +under: Nat, part: C.Cir.Stmt) -> C.Cir.Stmt:
  C.M.do([
    C.M.set(top, C.M.g(stack)),
    C.M.if(C.M.eq(C.M.todo(C.M.g(top)), C.M.c(0)), C.M.do([
      C.M.set(stack, C.M.f(1n, C.M.g(top))),
      C.M.finish(top),
      C.M.when(C.M.ne(C.M.g(stack), C.M.c(0)),
        C.M.set(depth, C.M.sub(C.M.g(depth), C.M.bump(C.M.g(stack), C.M.todo.last(C.M.g(stack))))))]),
    C.M.do([
      C.M.set(k, C.M.todo.first(C.M.g(top))),
      C.M.st(0n, C.M.g(top), C.M.sub(C.M.f(0n, C.M.g(top)), C.M.todo.bit(C.M.g(k)))),
      C.M.set(at, C.M.get(C.M.g(top), C.M.g(k))),
      C.M.set(under, C.M.add(C.M.g(depth), C.M.bump(C.M.g(top), C.M.g(k)))),
      part]))])

# M.shift's part
def Sh.part() -> C.Cir.Stmt:
  C.M.if(C.M.and(C.M.lt(C.M.fv(C.M.g(C.R.ssrc())), C.M.c(C.F.fv_max())), C.M.le(C.M.fv(C.M.g(C.R.ssrc())), C.M.g(C.R.sdep()))),
    C.M.inc(C.R.ssrc()),
    C.M.if(C.M.eq(C.M.tag(C.M.g(C.R.ssrc())), C.M.c(C.T.var())),
      C.M.if(C.M.lt(C.M.f(2n, C.M.g(C.R.ssrc())), C.M.g(C.R.sdep())),
        C.M.inc(C.R.ssrc()),
        C.M.do([
          C.M.var(C.R.t1(), C.M.add(C.M.f(2n, C.M.g(C.R.ssrc())), C.M.g(C.R.samt()))),
          C.M.put(C.R.snew(), C.R.sk(), C.M.g(C.R.t1()))])),
      C.M.do([
        C.M.copy.push(C.R.t1(), C.R.ssrc(), C.R.snew(), C.R.sk(), C.R.ss()),
        C.M.set(C.R.scut(), C.M.g(C.R.sdep()))])))

def Sh.body() -> C.Cir.Stmt:
  Wk.body(C.R.ss(), C.R.scut(), C.R.snew(), C.R.sk(), C.R.ssrc(), C.R.sdep(), Sh.part())

def Sh.loop.stmt() -> C.Cir.Stmt:
  C.M.while(C.M.ne(C.M.g(C.R.ss()), C.M.c(0)), Sh.body())

# The registers
# -------------

# the registers at a round of M.shift's loop: regs0's, with pend, the stack,
# the depth and the root, and any values j for the others that it writes
def Sh.R(+regs0: List<&2, U32>, +pend: U32, +stack: U32, +depth: U32, +root: U32, +j: List<&2, U32>) -> List<&2, U32>:
  D.Ups([D.Up{3n, pend}, D.Up{4n, T.tm.reg(j, 0n)}, D.Up{5n, T.tm.reg(j, 1n)}, D.Up{6n, T.tm.reg(j, 2n)},
    D.Up{7n, T.tm.reg(j, 3n)}, D.Up{33n, T.tm.reg(j, 4n)}, D.Up{41n, T.tm.reg(j, 5n)}, D.Up{55n, stack},
    D.Up{56n, T.tm.reg(j, 6n)}, D.Up{57n, depth}, D.Up{58n, root}, D.Up{59n, T.tm.reg(j, 7n)},
    D.Up{60n, T.tm.reg(j, 8n)}, D.Up{62n, T.tm.reg(j, 9n)}, D.Up{63n, T.tm.reg(j, 10n)}], D.Rg.ex(64n, regs0, 0n))

# The invariant
# -------------

# the walk's state at a round: the frames, the garbage and its pend list, the
# counts added (inc), and the registers pend, stack, depth, root and the
# others (j)
type Wk is Data:
  Wk{frs: List<&2, W.Fr>, P: List<&2, U32>, Q: List<&2, U32>, inc: Nat, pend: U32, stack: U32, depth: U32,
    root: U32, j: List<&2, U32>}

# the invariant of M.shift's walk, of the amount a, the image's names ks and
# terms img, the image K, first F, the start's garbage P0 and next N0, the
# bound Bu and its room Wu, the roots rs and kept cells kc, the source's cell
# x and term t, and the start's measure Wm0
def Sh.WI(+a: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32, +P0: List<&2, U32>, +N0: U32,
  +Bu: U32, +Wu: U32, +E: List<&2, U32>, +rs: List<&2, D.Rt>, +kc: List<&2, D.Kc>, +x: U32, +t: C.Term, +Wm0: Nat, +m: C.Cir.Cells,
  +nx: U32, +frs: List<&2, W.Fr>, +P: List<&2, U32>, +Q: List<&2, U32>, +inc: Nat, +pend: U32, +stack: U32,
  +depth: U32, +root: U32) -> Data:
  +mo = {D.Mo.shift{U32.to_nat(a)} : D.Mo}
  +X = {List.append(&2, U32, P, Con{root, List.append(&2, U32, W.Ns(frs), E)}) : List<&2, U32>}
  D.P2({U32.is_le(363, K) == True{} : Bool},
  D.P2({U32.is_lt(K, F) == True{} : Bool},
  D.P2({U32.is_le(F, nx) == True{} : Bool},
  D.P2({C.Cir.is_cell(root, K, F, nx) == True{} : Bool},
  D.P2({U32.is_le(F, root) == True{} : Bool},
  D.P2({W.Dj(Con{root, W.Ns(frs)}, List.append(&2, U32, P, E)) == True{} : Bool},
  D.P2(W.Frs(mo, m, ks, img, K, F, X, nx, frs, stack, True{}, 0, C.Term.Efq{}, 0n),
  D.P2(W.Root(mo, m, ks, img, K, F, X, nx, frs, root, x, t),
  D.P2(W.Dp(frs, depth),
  D.P2({W.DB(frs, Wm0) == True{} : Bool},
  D.P2({D.AL(m, pend, P, Q, K, F, nx, U32.add(Bu, U32.from_nat(inc))) == True{} : Bool},
  D.P2({D.Incl(P0, N0, X, nx) == True{} : Bool},
  D.P2(D.Tb(m),
  D.P2(D.Rts(m, ks, img, K, F, List.append(&2, U32, P0, E), N0, rs),
  D.P2(D.Kcs(m, K, F, List.append(&2, U32, P0, E), N0, E, kc),
  D.P2({D.Ex.ok(E, P, F, nx) == True{} : Bool},
  D.P2({Nat.is_le(Nat.add(inc, W.Wm(frs)), Wm0) == True{} : Bool},
  D.P2({Nat.is_le(1n+Wm0, U32.to_nat(Wu)) == True{} : Bool},
  D.P2({U32.is_le(Bu, U32.add(Bu, Wu)) == True{} : Bool},
    {W.Pz(Con{root, W.Ns(frs)}, P, m) == True{} : Bool})))))))))))))))))))

# the invariant of a state, by its witness w, with the registers rg
def Sh.WI.of(+regs0: List<&2, U32>, +a: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32,
  +P0: List<&2, U32>, +N0: U32, +Bu: U32, +Wu: U32, +E: List<&2, U32>, +rs: List<&2, D.Rt>, +kc: List<&2, D.Kc>, +x: U32, +t: C.Term,
  +Wm0: Nat, w: Wk, +rg: List<&2, U32>, +m: C.Cir.Cells, +nx: U32) -> Data:
  match w:
    case Wk{+frs, +P, +Q, +inc, +pend, +stack, +depth, +root, +j}:
      D.P2({rg == Sh.R(regs0, pend, stack, depth, root, j) : List<&2, U32>},
        Sh.WI(a, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, m, nx, frs, P, Q, inc, pend, stack, depth, root))

# the measure of a witness
def Wk.m(w: Wk) -> Nat:
  match w:
    case Wk{frs, _, _, _, _, _, _, _, _}:
      W.Wm(frs)

# The rounds
# ----------

# a round of the loop: the invariant again, with a smaller measure, or out of
# memory
def Sh.body.ok(+f: Nat, +regs0: List<&2, U32>, +a: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32,
  +F: U32, +L: U32, +I: List<&2, U32>, +P0: List<&2, U32>, +N0: U32, +Bu: U32, +Wu: U32, +E: List<&2, U32>, +rs: List<&2, D.Rt>,
  +kc: List<&2, D.Kc>, +x: U32, +t: C.Term, +Wm0: Nat, +m: C.Cir.Cells, +nx: U32, +pg: U32, +fr: W.Fr,
  +frs: List<&2, W.Fr>, +P: List<&2, U32>, +Q: List<&2, U32>, +inc: Nat, +pend: U32, +stack: U32, +depth: U32,
  +root: U32, +j: List<&2, U32>, ha: {T.tm.reg(regs0, 61n) == a : U32},
  wi: Sh.WI(a, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, m, nx, Con{fr, frs}, P, Q, inc, pend, stack, depth, root)) ->
  D.Ok(C.Cir.exec(1n+f, Sh.body(), D.S(Sh.R(regs0, pend, stack, depth, root, j), m, nx, F, K, pg, L, I)), F, K, L, I,
    rg => ms => nx2 => pg2 => D.Ex(Wk, w => D.P2(Sh.WI.of(regs0, a, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, w, rg, ms, nx2),
      {Nat.is_lt(Wk.m(w), W.Wm(Con{fr, frs})) == True{} : Bool}))):
  ?TODO

# the loop's end: the frames are gone and the root's field 2 holds the copy
def Sh.fin(+regs0: List<&2, U32>, +a: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32,
  +P0: List<&2, U32>, +N0: U32, +Bu: U32, +Wu: U32, +E: List<&2, U32>, +rs: List<&2, D.Rt>, +kc: List<&2, D.Kc>, +x: U32, +t: C.Term,
  +Wm0: Nat, +rg: List<&2, U32>, +m: C.Cir.Cells, +nx: U32) -> Data:
  D.Ex(Wk, w => D.P2(Sh.WI.of(regs0, a, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, w, rg, m, nx),
    {Wk.m(w) == 0n : Nat}))

# The loop
# --------

# the stack register holds the top frame's cell, which is not 0
def Sh.nz(+a: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32, +P0: List<&2, U32>, +N0: U32,
  +Bu: U32, +Wu: U32, +E: List<&2, U32>, +rs: List<&2, D.Rt>, +kc: List<&2, D.Kc>, +x: U32, +t: C.Term, +Wm0: Nat, +m: C.Cir.Cells,
  +nx: U32, fr: W.Fr, +frs: List<&2, W.Fr>, +P: List<&2, U32>, +Q: List<&2, U32>, +inc: Nat, +pend: U32, +stack: U32,
  +depth: U32, +root: U32,
  wi: Sh.WI(a, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, m, nx, Con{fr, frs}, P, Q, inc, pend, stack, depth, root)) ->
  {U32.is_zero(stack) == False{} : Bool}:
  match fr:
    case W.Fr{+n, +h, +x2, +T0, +y2, +y3, +y4, +t2, +t3, +t4, +s2, +s3, +s4, +d}:
      (_, w1) = wi
      (hkf, w2) = w1
      (_, w3) = w2
      (_, w4) = w3
      (_, w5) = w4
      (_, w6) = w5
      (hf, _) = w6
      (hs, h2) = hf
      (fo, _) = h2
      (_, f1) = fo
      (_, f2) = f1
      (_, f3) = f2
      (_, f4) = f3
      (_, f5) = f4
      (_, f6) = f5
      (_, f7) = f6
      (_, f8) = f7
      (_, f9) = f8
      (_, f10) = f9
      (hle, _) = f10
      %Equal.sym(U32, stack, n, hs) : {U32.is_zero(_) == False{} : Bool}
      K.U.nz(n, K, F, hkf, hle)

# Sh.loop's claim
def Sh.loop.goal(+f: Nat, +regs0: List<&2, U32>, +a: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32,
  +F: U32, +L: U32, +I: List<&2, U32>, +P0: List<&2, U32>, +N0: U32, +Bu: U32, +Wu: U32, +E: List<&2, U32>, +rs: List<&2, D.Rt>,
  +kc: List<&2, D.Kc>, +x: U32, +t: C.Term, +Wm0: Nat, +m: C.Cir.Cells, +nx: U32, +pg: U32, +pend: U32, +stack: U32,
  +depth: U32, +root: U32, +j: List<&2, U32>) -> Type:
  D.Ok(C.Cir.exec(1n+f, Sh.loop.stmt(), D.S(Sh.R(regs0, pend, stack, depth, root, j), m, nx, F, K, pg, L, I)), F, K, L, I,
    rg => ms => nx2 => pg2 => Sh.fin(regs0, a, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, rg, ms, nx2))

# the loop's end, once the frames are gone
def Sh.loop.nil(+f: Nat, +regs0: List<&2, U32>, +a: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32,
  +F: U32, +L: U32, +I: List<&2, U32>, +P0: List<&2, U32>, +N0: U32, +Bu: U32, +Wu: U32, +E: List<&2, U32>, +rs: List<&2, D.Rt>,
  +kc: List<&2, D.Kc>, +x: U32, +t: C.Term, +Wm0: Nat, +m: C.Cir.Cells, +nx: U32, +pg: U32,
  +P: List<&2, U32>, +Q: List<&2, U32>, +inc: Nat, +pend: U32, +stack: U32, +depth: U32, +root: U32, +j: List<&2, U32>,
  +wi: Sh.WI(a, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, m, nx, [], P, Q, inc, pend, stack, depth, root)) ->
  Sh.loop.goal(f, regs0, a, ks, img, K, F, L, I, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, m, nx, pg, pend, stack, depth, root, j):
  (_, w1) = wi
  (_, w2) = w1
  (_, w3) = w2
  (_, w4) = w3
  (_, w5) = w4
  (_, w6) = w5
  (hs, _) = w6
  +st = D.S(Sh.R(regs0, pend, stack, depth, root, j), m, nx, F, K, pg, L, I)
  +cnd = C.M.ne(C.M.g(C.R.ss()), C.M.c(0))
  +ev = {%Equal.sym(U32, stack, 0, hs) : {Some{0} == Some{Bool.to_u32(U32.is_ne(_, 0))} : Maybe<&2, U32>}; {==} : {Some{0} == C.Cir.eval(cnd, st) : Maybe<&2, U32>}}
  K.Ok.eq(C.Cir.exec(1n+f, Sh.loop.stmt(), st), C.Cir.Out.next{st}, F, K, L, I,
    rg => ms => nx2 => pg2 => Sh.fin(regs0, a, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, rg, ms, nx2),
    Equal.sym(C.Cir.Out, C.Cir.exec(1n+f, Sh.loop.stmt(), st), C.Cir.Out.next{st}, K.X.wh0(f, cnd, Sh.body(), st, ev)),
    K.Ok.next(Sh.R(regs0, pend, stack, depth, root, j), m, nx, F, K, pg, L, I,
      rg => ms => nx2 => pg2 => Sh.fin(regs0, a, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, rg, ms, nx2),
      (Wk{[], P, Q, inc, pend, stack, depth, root, j}, (({==}, wi), {==}))))

# a round's outcome: the invariant again, with a smaller measure, so that the
# fuel left bounds it; k continues the loop from there
def Sh.loop.next(+g: Nat, +regs0: List<&2, U32>, +a: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32,
  +F: U32, +L: U32, +I: List<&2, U32>, +P0: List<&2, U32>, +N0: U32, +Bu: U32, +Wu: U32, +E: List<&2, U32>, +rs: List<&2, D.Rt>,
  +kc: List<&2, D.Kc>, +x: U32, +t: C.Term, +Wm0: Nat, +rg: List<&2, U32>, +ms: C.Cir.Cells, +nx2: U32, +pg2: U32,
  +Wold: Nat, hf: {Nat.is_le(Wold, 1n+g) == True{} : Bool},
  q: D.Ex(Wk, w => D.P2(Sh.WI.of(regs0, a, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, w, rg, ms, nx2),
    {Nat.is_lt(Wk.m(w), Wold) == True{} : Bool})),
  k: @frs: List<&2, W.Fr> -> @P: List<&2, U32> -> @Q: List<&2, U32> -> @inc: Nat -> @pend: U32 -> @stack: U32 ->
    @depth: U32 -> @root: U32 -> @j: List<&2, U32> -> {Nat.is_le(W.Wm(frs), g) == True{} : Bool} ->
    Sh.WI(a, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, ms, nx2, frs, P, Q, inc, pend, stack, depth, root) ->
    Sh.loop.goal(g, regs0, a, ks, img, K, F, L, I, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, ms, nx2, pg2, pend, stack, depth, root, j)) ->
  D.Ok(C.Cir.exec(1n+g, Sh.loop.stmt(), D.S(rg, ms, nx2, F, K, pg2, L, I)), F, K, L, I,
    rg => ms => nx2 => pg2 => Sh.fin(regs0, a, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, rg, ms, nx2)):
  (w, r2) = q
  match w:
    case Wk{+frs, +P, +Q, +inc, +pend, +stack, +depth, +root, +j}:
      (wio, hlt) = r2
      (heq, wi) = wio
      %Equal.sym(List<&2, U32>, rg, Sh.R(regs0, pend, stack, depth, root, j), heq) :
        D.Ok(C.Cir.exec(1n+g, Sh.loop.stmt(), D.S(_, ms, nx2, F, K, pg2, L, I)), F, K, L, I,
        rg => ms => nx2 => pg2 => Sh.fin(regs0, a, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, rg, ms, nx2))
      k(frs, P, Q, inc, pend, stack, depth, root, j, K.Na.lt_le(Wold, W.Wm(frs), g, hlt, hf), wi)

# the loop, from a state of the invariant whose measure is at most the fuel
def Sh.loop(f: Nat, +regs0: List<&2, U32>, +a: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32,
  +F: U32, +L: U32, +I: List<&2, U32>, +P0: List<&2, U32>, +N0: U32, +Bu: U32, +Wu: U32, +E: List<&2, U32>, +rs: List<&2, D.Rt>,
  +kc: List<&2, D.Kc>, +x: U32, +t: C.Term, +Wm0: Nat, +m: C.Cir.Cells, +nx: U32, +pg: U32, frs: List<&2, W.Fr>,
  +P: List<&2, U32>, +Q: List<&2, U32>, +inc: Nat, +pend: U32, +stack: U32, +depth: U32, +root: U32, +j: List<&2, U32>,
  +ha: {T.tm.reg(regs0, 61n) == a : U32}, hf: {Nat.is_le(W.Wm(frs), f) == True{} : Bool},
  +wi: Sh.WI(a, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, m, nx, frs, P, Q, inc, pend, stack, depth, root)) ->
  Sh.loop.goal(f, regs0, a, ks, img, K, F, L, I, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, m, nx, pg, pend, stack, depth, root, j):
  match f frs:
    case _ Nil{}:
      Sh.loop.nil(f, regs0, a, ks, img, K, F, L, I, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, m, nx, pg, P, Q, inc, pend, stack, depth, root, j, wi)
    case 0n Con{W.Fr{+n, +h, +x2, +T0, +y2, +y3, +y4, +t2, +t3, +t4, +s2, +s3, +s4, +d}, +rest}:
      K.Bo.tf(Sh.loop.goal(0n, regs0, a, ks, img, K, F, L, I, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, m, nx, pg, pend, stack, depth, root, j), hf)
    case 1n+(+g) Con{+fr, +rest}:
      +st = D.S(Sh.R(regs0, pend, stack, depth, root, j), m, nx, F, K, pg, L, I)
      +cnd = C.M.ne(C.M.g(C.R.ss()), C.M.c(0))
      +nz = Sh.nz(a, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, m, nx, fr, rest, P, Q, inc, pend, stack, depth, root, wi)
      +ev = {%Equal.sym(Bool, U32.is_zero(stack), False{}, nz) : {Some{1} == Some{Bool.to_u32(Bool.not(_))} : Maybe<&2, U32>}; {==} :
        {Some{1} == C.Cir.eval(cnd, st) : Maybe<&2, U32>}}
      K.Ok.loop(g, cnd, Sh.body(), st, 1, F, K, L, I,
        rg => ms => nx2 => pg2 => D.Ex(Wk, w => D.P2(Sh.WI.of(regs0, a, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, w, rg, ms, nx2),
          {Nat.is_lt(Wk.m(w), W.Wm(Con{fr, rest})) == True{} : Bool})),
        rg => ms => nx2 => pg2 => Sh.fin(regs0, a, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, rg, ms, nx2),
        ev, {==},
        Sh.body.ok(g, regs0, a, ks, img, K, F, L, I, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, m, nx, pg, fr, rest, P, Q, inc, pend,
          stack, depth, root, j, ha, wi),
        +rg => +ms => +nx2 => +pg2 => q => Sh.loop.next(g, regs0, a, ks, img, K, F, L, I, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, rg, ms, nx2, pg2,
          W.Wm(Con{fr, rest}), hf, q, frs2 => P2 => Q2 => inc2 => pend2 => stack2 => depth2 => root2 => j2 => hf2 => wi2 =>
            Sh.loop(g, regs0, a, ks, img, K, F, L, I, P0, N0, Bu, Wu, E, rs, kc, x, t, Wm0, ms, nx2, pg2, frs2, P2, Q2, inc2, pend2,
              stack2, depth2, root2, j2, ha, hf2, wi2)))

# The start and the end
# ---------------------

# the root cell n0: a Prj (11) whose part, in field 2, the source's cell x of
# the term t, is pending
def Sh.fr0(+n0: U32, +x: U32, +t: C.Term) -> W.Fr:
  W.Fr{n0, 11, x, C.Term.Prj{t}, x, 0, 0, t, C.Term.Efq{}, C.Term.Efq{}, W.St.pe{}, W.St.un{}, W.St.un{}, 0n}

# M.copy.root, then the stack and the depth: the invariant holds of the root
# frame, with the measure 1 + 2 × Sz(t)
def Sh.start(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +F: U32, +K: U32, +pg: U32, +L: U32,
  +I: List<&2, U32>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +P: List<&2, U32>, +Q: List<&2, U32>, +Bu: U32,
  +Wu: U32, +E: List<&2, U32>, +rs: List<&2, D.Rt>, +kc: List<&2, D.Kc>, +t: C.Term, +g: Nat, +a: U32, +B: C.Cir.Stmt,
  -R: List<&2, U32> -> C.Cir.Cells -> U32 -> U32 -> Type,
  pre: D.Pre(regs, m, nx, F, K, ks, img, P, Q, E, Bu, Wu, rs, kc),
  ht: {D.Tm(g, m, ks, img, K, F, List.append(&2, U32, P, E), nx, T.tm.reg(regs, 63n)) == Some{t} : Maybe<&2, C.Term>},
  hf: {D.Fit(t, a) == True{} : Bool},
  hw: {Nat.is_le(2n+Nat.double(D.Sz(t)), U32.to_nat(Wu)) == True{} : Bool},
  k: @ms: C.Cir.Cells -> @nx2: U32 -> @pg2: U32 -> @P2: List<&2, U32> -> @Q2: List<&2, U32> -> @pend: U32 -> @n0: U32 ->
    @j: List<&2, U32> ->
    Sh.WI(a, ks, img, K, F, P, nx, Bu, Wu, E, rs, kc, T.tm.reg(regs, 63n), t, 1n+Nat.double(D.Sz(t)), ms, nx2,
      [Sh.fr0(n0, T.tm.reg(regs, 63n), t)], P2, Q2, 0n, pend, n0, 0, n0) ->
    D.Ok(C.Cir.exec(1n+f, B, D.S(Sh.R(regs, pend, n0, 0, n0, j), ms, nx2, F, K, pg2, L, I)), F, K, L, I, R)) ->
  D.Ok(C.Cir.exec(1n+f, C.Cir.Stmt.seq{C.M.copy.root(C.R.sroot(), C.R.t2()), C.Cir.Stmt.seq{C.M.set(C.R.ss(), C.M.g(C.R.sroot())),
    C.Cir.Stmt.seq{C.M.set(C.R.scut(), C.M.c(0)), B}}}, D.S(regs, m, nx, F, K, pg, L, I)), F, K, L, I, R):
  ?TODO

# M.copy.end: sres gets the copy from the root, whose cell goes to the pend list
def Sh.end(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +F: U32, +K: U32, +pg: U32, +L: U32,
  +I: List<&2, U32>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +P: List<&2, U32>, +Bu: U32, +Wu: U32, +E: List<&2, U32>,
  +rs: List<&2, D.Rt>, +kc: List<&2, D.Kc>, +t: C.Term, +a: U32, +Wm0: Nat, +rg: List<&2, U32>, +ms: C.Cir.Cells, +nx2: U32,
  +pg2: U32, fin: Sh.fin(regs, a, ks, img, K, F, P, nx, Bu, Wu, E, rs, kc, T.tm.reg(regs, 63n), t, Wm0, rg, ms, nx2)) ->
  D.Ok(C.Cir.exec(1n+f, C.Cir.Stmt.seq{C.M.copy.end(C.R.sres(), C.R.sroot()), C.Cir.Stmt.nop{}}, D.S(rg, ms, nx2, F, K, pg2, L, I)),
    F, K, L, I, rg => ms => nx3 => pg3 => D.Ex(D.Wt, w => D.Post(D.Mo.shift{U32.to_nat(a)}, t, regs, D.Sh.scratch(), C.R.sres(),
      ks, img, K, F, P, E, nx, Bu, Wu, rs, kc, w, rg, ms, nx3))):
  ?TODO

# The claim
# ---------

# the root frame's measure
def Sh.w0(+n0: U32, +x: U32, +t: C.Term) -> {Nat.is_le(W.Wm([Sh.fr0(n0, x, t)]), 1n+Nat.double(D.Sz(t))) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.double(D.Sz(t)), 0n), Nat.double(D.Sz(t)), N.add_zero(Nat.double(D.Sz(t)))) :
    {Nat.is_le(1n+_, 1n+Nat.double(D.Sz(t))) == True{} : Bool}
  K.Na.le_refl(Nat.double(D.Sz(t)))

def D.Sh.ok(regs, m, nx, F, K, pg, L, I, ks, img, P, Q, Bu, Wu, E, rs, kc, t, g, a, pre, ht, ha, hf, hw):
  +W0 = {1n+Nat.double(D.Sz(t)) : Nat}
  +x = {T.tm.reg(regs, 63n) : U32}
  +mo = {D.Mo.shift{U32.to_nat(a)} : D.Mo}
  +fin = {C.Cir.Stmt.seq{C.M.copy.end(C.R.sres(), C.R.sroot()), C.Cir.Stmt.nop{}} : C.Cir.Stmt}
  (1n+W0, Sh.start(W0, regs, m, nx, F, K, pg, L, I, ks, img, P, Q, Bu, Wu, E, rs, kc, t, g, a,
    C.Cir.Stmt.seq{Sh.loop.stmt(), fin},
    rg => ms => nx2 => pg2 => D.Ex(D.Wt, w => D.Post(mo, t, regs, D.Sh.scratch(), C.R.sres(), ks, img, K, F, P, E, nx, Bu, Wu, rs, kc, w, rg, ms, nx2)),
    pre, ht, hf, hw,
    +ms => +nx2 => +pg2 => +P2 => +Q2 => +pend => +n0 => +j => wi =>
      K.Ok.seq(W0, Sh.loop.stmt(), fin, D.S(Sh.R(regs, pend, n0, 0, n0, j), ms, nx2, F, K, pg2, L, I), F, K, L, I,
        rg => ms3 => nx3 => pg3 => Sh.fin(regs, a, ks, img, K, F, P, nx, Bu, Wu, E, rs, kc, x, t, W0, rg, ms3, nx3),
        rg => ms3 => nx3 => pg3 => D.Ex(D.Wt, w => D.Post(mo, t, regs, D.Sh.scratch(), C.R.sres(), ks, img, K, F, P, E, nx, Bu, Wu, rs, kc, w, rg, ms3, nx3)),
        Sh.loop(W0, regs, a, ks, img, K, F, L, I, P, nx, Bu, Wu, E, rs, kc, x, t, W0, ms, nx2, pg2, [Sh.fr0(n0, x, t)], P2, Q2, 0n,
          pend, n0, 0, n0, j, ha, Sh.w0(n0, x, t), wi),
        +rg => +ms3 => +nx3 => +pg3 => fq => Sh.end(W0, regs, m, nx, F, K, pg, L, I, ks, img, P, Bu, Wu, E, rs, kc, t, a, W0, rg, ms3, nx3, pg3, fq))))
