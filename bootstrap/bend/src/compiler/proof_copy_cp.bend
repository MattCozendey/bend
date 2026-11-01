# compiler: M.copy gives Term.subst
# =================================
#
# The proof of proof_copy.bend's Cp.ok: M.copy's walk (proof_copy_walk.bend)
# with the copy's registers (croot, cs, cd, cnew, ck, csrc, cj) and part, as
# M.shift's (proof_copy_sh.bend): Cp.start makes the root and the first frame,
# Cp.loop runs the rounds (Cp.body.ok), Cp.end reads the copy. A round's part
# may shift a local by the depth: it calls M.shift (S.D.Sh.ok, proven in
# proof_copy_sh.bend) with the frames' cells as the cells E that the shift
# may not read, and their terms as its roots.

import Base
import ./impl.bend as C
import ./proof_term.bend as T
import ./proof_need.bend as N
import ./proof_copy.bend as D
import ./proof_copy_kit.bend as K
import ./proof_copy_walk.bend as W
import ./proof_copy_sh.bend as S

# The code
# --------

# M.copy's part
def Cp.part() -> C.Cir.Stmt:
  C.M.copy.part()

def Cp.body() -> C.Cir.Stmt:
  S.Wk.body(C.R.cs(), C.R.cd(), C.R.cnew(), C.R.ck(), C.R.csrc(), C.R.cj(), Cp.part())

def Cp.loop.stmt() -> C.Cir.Stmt:
  C.M.while(C.M.ne(C.M.g(C.R.cs()), C.M.c(0)), Cp.body())

# the fuel that a round's own loops need: the walk to a local, and a shift
def Cp.Bb(es: List<&2, C.Term>) -> Nat:
  +e = es
  3n+Nat.add(List.length(&2, C.Term, e), Nat.double(D.Sz.max(e)))

# The registers
# -------------

# the registers at a round of M.copy's loop: regs0's, with pend, the stack,
# the depth and the root, and any values j for the others that it writes
def Cp.R(+regs0: List<&2, U32>, +pend: U32, +stack: U32, +depth: U32, +root: U32, +j: List<&2, U32>) -> List<&2, U32>:
  D.Ups([D.Up{3n, pend}, D.Up{4n, T.tm.reg(j, 0n)}, D.Up{5n, T.tm.reg(j, 1n)}, D.Up{6n, T.tm.reg(j, 2n)},
    D.Up{7n, T.tm.reg(j, 3n)}, D.Up{30n, stack}, D.Up{31n, T.tm.reg(j, 4n)}, D.Up{32n, depth}, D.Up{33n, T.tm.reg(j, 5n)},
    D.Up{34n, T.tm.reg(j, 6n)}, D.Up{35n, T.tm.reg(j, 7n)}, D.Up{38n, T.tm.reg(j, 8n)}, D.Up{39n, root},
    D.Up{40n, T.tm.reg(j, 9n)}, D.Up{41n, T.tm.reg(j, 10n)}, D.Up{55n, T.tm.reg(j, 11n)}, D.Up{56n, T.tm.reg(j, 12n)},
    D.Up{57n, T.tm.reg(j, 13n)}, D.Up{58n, T.tm.reg(j, 14n)}, D.Up{59n, T.tm.reg(j, 15n)}, D.Up{60n, T.tm.reg(j, 16n)},
    D.Up{61n, T.tm.reg(j, 17n)}, D.Up{62n, T.tm.reg(j, 18n)}, D.Up{63n, T.tm.reg(j, 19n)}], D.Rg.ex(64n, regs0, 0n))

# The invariant
# -------------

# the invariant of M.copy's walk, of the locals es, the image's names ks and
# terms img, the image K, first F, the start's garbage P0 and next N0, the
# bound Bu and its room Wu, the roots rs and kept cells kc, the source's cell
# x and term t, and the start's measure Wm0
def Cp.WI(+es: List<&2, C.Term>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32, +P0: List<&2, U32>, +N0: U32,
  +Bu: U32, +Wu: U32, +E: List<&2, U32>, +rs: List<&2, D.Rt>, +kc: List<&2, D.Kc>, +cenv: U32, +clen: U32, +x: U32, +t: C.Term, +Wm0: Nat, +m: C.Cir.Cells,
  +nx: U32, +frs: List<&2, W.Fr>, +P: List<&2, U32>, +Q: List<&2, U32>, +inc: Nat, +pend: U32, +stack: U32,
  +depth: U32, +root: U32) -> Data:
  +mo = {D.Mo.subst{es} : D.Mo}
  +cw = {2n+Nat.double(D.Sz.max(es)) : Nat}
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
  D.P2({Nat.is_le(Nat.add(inc, Nat.mul(W.Wm(frs), cw)), Nat.mul(Wm0, cw)) == True{} : Bool},
  D.P2({Nat.is_le(Nat.mul(Wm0, cw), U32.to_nat(Wu)) == True{} : Bool},
  D.P2(D.Env(m, ks, img, K, F, List.append(&2, U32, P0, E), N0, cenv, es),
  D.P2({U32.to_nat(clen) == List.length(&2, C.Term, es) : Nat},
  D.P2({D.Fits(es, U32.from_nat(Nat.double(D.Sz(t)))) == True{} : Bool},
  D.P2({U32.is_le(Bu, U32.add(Bu, Wu)) == True{} : Bool},
    {W.Pz(Con{root, W.Ns(frs)}, P, m) == True{} : Bool}))))))))))))))))))))))

# the invariant of a state, by its witness w, with the registers rg
def Cp.WI.of(+regs0: List<&2, U32>, +es: List<&2, C.Term>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32,
  +P0: List<&2, U32>, +N0: U32, +Bu: U32, +Wu: U32, +E: List<&2, U32>, +rs: List<&2, D.Rt>, +kc: List<&2, D.Kc>, +cenv: U32, +clen: U32, +x: U32, +t: C.Term,
  +Wm0: Nat, w: S.Wk, +rg: List<&2, U32>, +m: C.Cir.Cells, +nx: U32) -> Data:
  match w:
    case S.Wk{+frs, +P, +Q, +inc, +pend, +stack, +depth, +root, +j}:
      D.P2({rg == Cp.R(regs0, pend, stack, depth, root, j) : List<&2, U32>},
        Cp.WI(es, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, m, nx, frs, P, Q, inc, pend, stack, depth, root))


# The rounds
# ----------

# a round of the loop: the invariant again, with a smaller measure, or out of
# memory
def Cp.body.ok(+f: Nat, +regs0: List<&2, U32>, +es: List<&2, C.Term>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32,
  +F: U32, +L: U32, +I: List<&2, U32>, +P0: List<&2, U32>, +N0: U32, +Bu: U32, +Wu: U32, +E: List<&2, U32>, +rs: List<&2, D.Rt>,
  +kc: List<&2, D.Kc>, +cenv: U32, +clen: U32, +x: U32, +t: C.Term, +Wm0: Nat, +m: C.Cir.Cells, +nx: U32, +pg: U32, +fr: W.Fr,
  +frs: List<&2, W.Fr>, +P: List<&2, U32>, +Q: List<&2, U32>, +inc: Nat, +pend: U32, +stack: U32, +depth: U32,
  +root: U32, +j: List<&2, U32>, hb: {Nat.is_le(Cp.Bb(es), f) == True{} : Bool},
  wi: Cp.WI(es, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, m, nx, Con{fr, frs}, P, Q, inc, pend, stack, depth, root)) ->
  D.Ok(C.Cir.exec(1n+f, Cp.body(), D.S(Cp.R(regs0, pend, stack, depth, root, j), m, nx, F, K, pg, L, I)), F, K, L, I,
    rg => ms => nx2 => pg2 => D.Ex(S.Wk, w => D.P2(Cp.WI.of(regs0, es, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, w, rg, ms, nx2),
      {Nat.is_lt(S.Wk.m(w), W.Wm(Con{fr, frs})) == True{} : Bool}))):
  ?TODO

# the loop's end: the frames are gone and the root's field 2 holds the copy
def Cp.fin(+regs0: List<&2, U32>, +es: List<&2, C.Term>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32,
  +P0: List<&2, U32>, +N0: U32, +Bu: U32, +Wu: U32, +E: List<&2, U32>, +rs: List<&2, D.Rt>, +kc: List<&2, D.Kc>, +cenv: U32, +clen: U32, +x: U32, +t: C.Term,
  +Wm0: Nat, +rg: List<&2, U32>, +m: C.Cir.Cells, +nx: U32) -> Data:
  D.Ex(S.Wk, w => D.P2(Cp.WI.of(regs0, es, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, w, rg, m, nx),
    {S.Wk.m(w) == 0n : Nat}))

# The loop
# --------

# the stack register holds the top frame's cell, which is not 0
def Cp.nz(+es: List<&2, C.Term>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32, +P0: List<&2, U32>, +N0: U32,
  +Bu: U32, +Wu: U32, +E: List<&2, U32>, +rs: List<&2, D.Rt>, +kc: List<&2, D.Kc>, +cenv: U32, +clen: U32, +x: U32, +t: C.Term, +Wm0: Nat, +m: C.Cir.Cells,
  +nx: U32, fr: W.Fr, +frs: List<&2, W.Fr>, +P: List<&2, U32>, +Q: List<&2, U32>, +inc: Nat, +pend: U32, +stack: U32,
  +depth: U32, +root: U32,
  wi: Cp.WI(es, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, m, nx, Con{fr, frs}, P, Q, inc, pend, stack, depth, root)) ->
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
def Cp.loop.goal(+f: Nat, +regs0: List<&2, U32>, +es: List<&2, C.Term>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32,
  +F: U32, +L: U32, +I: List<&2, U32>, +P0: List<&2, U32>, +N0: U32, +Bu: U32, +Wu: U32, +E: List<&2, U32>, +rs: List<&2, D.Rt>,
  +kc: List<&2, D.Kc>, +cenv: U32, +clen: U32, +x: U32, +t: C.Term, +Wm0: Nat, +m: C.Cir.Cells, +nx: U32, +pg: U32, +pend: U32, +stack: U32,
  +depth: U32, +root: U32, +j: List<&2, U32>) -> Type:
  D.Ok(C.Cir.exec(1n+f, Cp.loop.stmt(), D.S(Cp.R(regs0, pend, stack, depth, root, j), m, nx, F, K, pg, L, I)), F, K, L, I,
    rg => ms => nx2 => pg2 => Cp.fin(regs0, es, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, rg, ms, nx2))

# the loop's end, once the frames are gone
def Cp.loop.nil(+f: Nat, +regs0: List<&2, U32>, +es: List<&2, C.Term>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32,
  +F: U32, +L: U32, +I: List<&2, U32>, +P0: List<&2, U32>, +N0: U32, +Bu: U32, +Wu: U32, +E: List<&2, U32>, +rs: List<&2, D.Rt>,
  +kc: List<&2, D.Kc>, +cenv: U32, +clen: U32, +x: U32, +t: C.Term, +Wm0: Nat, +m: C.Cir.Cells, +nx: U32, +pg: U32,
  +P: List<&2, U32>, +Q: List<&2, U32>, +inc: Nat, +pend: U32, +stack: U32, +depth: U32, +root: U32, +j: List<&2, U32>,
  +wi: Cp.WI(es, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, m, nx, [], P, Q, inc, pend, stack, depth, root)) ->
  Cp.loop.goal(f, regs0, es, ks, img, K, F, L, I, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, m, nx, pg, pend, stack, depth, root, j):
  (_, w1) = wi
  (_, w2) = w1
  (_, w3) = w2
  (_, w4) = w3
  (_, w5) = w4
  (_, w6) = w5
  (hs, _) = w6
  +st = D.S(Cp.R(regs0, pend, stack, depth, root, j), m, nx, F, K, pg, L, I)
  +cnd = C.M.ne(C.M.g(C.R.cs()), C.M.c(0))
  +ev = {%Equal.sym(U32, stack, 0, hs) : {Some{0} == Some{Bool.to_u32(U32.is_ne(_, 0))} : Maybe<&2, U32>}; {==} : {Some{0} == C.Cir.eval(cnd, st) : Maybe<&2, U32>}}
  K.Ok.eq(C.Cir.exec(1n+f, Cp.loop.stmt(), st), C.Cir.Out.next{st}, F, K, L, I,
    rg => ms => nx2 => pg2 => Cp.fin(regs0, es, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, rg, ms, nx2),
    Equal.sym(C.Cir.Out, C.Cir.exec(1n+f, Cp.loop.stmt(), st), C.Cir.Out.next{st}, K.X.wh0(f, cnd, Cp.body(), st, ev)),
    K.Ok.next(Cp.R(regs0, pend, stack, depth, root, j), m, nx, F, K, pg, L, I,
      rg => ms => nx2 => pg2 => Cp.fin(regs0, es, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, rg, ms, nx2),
      (S.Wk{[], P, Q, inc, pend, stack, depth, root, j}, (({==}, wi), {==}))))

# a round's outcome: the invariant again, with a smaller measure, so that the
# fuel left bounds it; k continues the loop from there
def Cp.loop.next(+g: Nat, +regs0: List<&2, U32>, +es: List<&2, C.Term>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32,
  +F: U32, +L: U32, +I: List<&2, U32>, +P0: List<&2, U32>, +N0: U32, +Bu: U32, +Wu: U32, +E: List<&2, U32>, +rs: List<&2, D.Rt>,
  +kc: List<&2, D.Kc>, +cenv: U32, +clen: U32, +x: U32, +t: C.Term, +Wm0: Nat, +rg: List<&2, U32>, +ms: C.Cir.Cells, +nx2: U32, +pg2: U32,
  +Wold: Nat, hf: {Nat.is_le(Nat.add(Wold, Cp.Bb(es)), 1n+g) == True{} : Bool},
  q: D.Ex(S.Wk, w => D.P2(Cp.WI.of(regs0, es, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, w, rg, ms, nx2),
    {Nat.is_lt(S.Wk.m(w), Wold) == True{} : Bool})),
  k: @frs: List<&2, W.Fr> -> @P: List<&2, U32> -> @Q: List<&2, U32> -> @inc: Nat -> @pend: U32 -> @stack: U32 ->
    @depth: U32 -> @root: U32 -> @j: List<&2, U32> -> {Nat.is_le(Nat.add(W.Wm(frs), Cp.Bb(es)), g) == True{} : Bool} ->
    Cp.WI(es, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, ms, nx2, frs, P, Q, inc, pend, stack, depth, root) ->
    Cp.loop.goal(g, regs0, es, ks, img, K, F, L, I, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, ms, nx2, pg2, pend, stack, depth, root, j)) ->
  D.Ok(C.Cir.exec(1n+g, Cp.loop.stmt(), D.S(rg, ms, nx2, F, K, pg2, L, I)), F, K, L, I,
    rg => ms => nx2 => pg2 => Cp.fin(regs0, es, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, rg, ms, nx2)):
  (w, r2) = q
  match w:
    case S.Wk{+frs, +P, +Q, +inc, +pend, +stack, +depth, +root, +j}:
      (wio, hlt) = r2
      (heq, wi) = wio
      %Equal.sym(List<&2, U32>, rg, Cp.R(regs0, pend, stack, depth, root, j), heq) :
        D.Ok(C.Cir.exec(1n+g, Cp.loop.stmt(), D.S(_, ms, nx2, F, K, pg2, L, I)), F, K, L, I,
        rg => ms => nx2 => pg2 => Cp.fin(regs0, es, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, rg, ms, nx2))
      k(frs, P, Q, inc, pend, stack, depth, root, j, K.Na.lt_le_add(Wold, W.Wm(frs), Cp.Bb(es), g, hlt, hf), wi)

# the loop, from a state of the invariant whose measure is at most the fuel
def Cp.loop(f: Nat, +regs0: List<&2, U32>, +es: List<&2, C.Term>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32,
  +F: U32, +L: U32, +I: List<&2, U32>, +P0: List<&2, U32>, +N0: U32, +Bu: U32, +Wu: U32, +E: List<&2, U32>, +rs: List<&2, D.Rt>,
  +kc: List<&2, D.Kc>, +cenv: U32, +clen: U32, +x: U32, +t: C.Term, +Wm0: Nat, +m: C.Cir.Cells, +nx: U32, +pg: U32, frs: List<&2, W.Fr>,
  +P: List<&2, U32>, +Q: List<&2, U32>, +inc: Nat, +pend: U32, +stack: U32, +depth: U32, +root: U32, +j: List<&2, U32>,
  +hf: {Nat.is_le(Nat.add(W.Wm(frs), Cp.Bb(es)), f) == True{} : Bool},
  +wi: Cp.WI(es, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, m, nx, frs, P, Q, inc, pend, stack, depth, root)) ->
  Cp.loop.goal(f, regs0, es, ks, img, K, F, L, I, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, m, nx, pg, pend, stack, depth, root, j):
  match f frs:
    case _ Nil{}:
      Cp.loop.nil(f, regs0, es, ks, img, K, F, L, I, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, m, nx, pg, P, Q, inc, pend, stack, depth, root, j, wi)
    case 0n Con{W.Fr{+n, +h, +x2, +T0, +y2, +y3, +y4, +t2, +t3, +t4, +s2, +s3, +s4, +d}, +rest}:
      K.Bo.tf(Cp.loop.goal(0n, regs0, es, ks, img, K, F, L, I, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, m, nx, pg, pend, stack, depth, root, j), hf)
    case 1n+(+g) Con{W.Fr{+n, +h, +x2, +T0, +y2, +y3, +y4, +t2, +t3, +t4, +s2, +s3, +s4, +d}, +rest}:
      +fr = {W.Fr{n, h, x2, T0, y2, y3, y4, t2, t3, t4, s2, s3, s4, d} : W.Fr}
      +hb = K.Na.le_add_l(Nat.add(W.Wp(s2, t2), Nat.add(W.Wp(s3, t3), Nat.add(W.Wp(s4, t4), W.Wm(rest)))), Cp.Bb(es), g, hf)
      +st = D.S(Cp.R(regs0, pend, stack, depth, root, j), m, nx, F, K, pg, L, I)
      +cnd = C.M.ne(C.M.g(C.R.cs()), C.M.c(0))
      +nz = Cp.nz(es, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, m, nx, fr, rest, P, Q, inc, pend, stack, depth, root, wi)
      +ev = {%Equal.sym(Bool, U32.is_zero(stack), False{}, nz) : {Some{1} == Some{Bool.to_u32(Bool.not(_))} : Maybe<&2, U32>}; {==} :
        {Some{1} == C.Cir.eval(cnd, st) : Maybe<&2, U32>}}
      K.Ok.loop(g, cnd, Cp.body(), st, 1, F, K, L, I,
        rg => ms => nx2 => pg2 => D.Ex(S.Wk, w => D.P2(Cp.WI.of(regs0, es, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, w, rg, ms, nx2),
          {Nat.is_lt(S.Wk.m(w), W.Wm(Con{fr, rest})) == True{} : Bool})),
        rg => ms => nx2 => pg2 => Cp.fin(regs0, es, ks, img, K, F, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, rg, ms, nx2),
        ev, {==},
        Cp.body.ok(g, regs0, es, ks, img, K, F, L, I, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, m, nx, pg, fr, rest, P, Q, inc, pend,
          stack, depth, root, j, hb, wi),
        +rg => +ms => +nx2 => +pg2 => q => Cp.loop.next(g, regs0, es, ks, img, K, F, L, I, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, rg, ms, nx2, pg2,
          W.Wm(Con{fr, rest}), hf, q, frs2 => P2 => Q2 => inc2 => pend2 => stack2 => depth2 => root2 => j2 => hf2 => wi2 =>
            Cp.loop(g, regs0, es, ks, img, K, F, L, I, P0, N0, Bu, Wu, E, rs, kc, cenv, clen, x, t, Wm0, ms, nx2, pg2, frs2, P2, Q2, inc2, pend2,
              stack2, depth2, root2, j2, hf2, wi2)))


# The start and the end
# ---------------------

# M.copy.root, then the stack and the depth: the invariant holds of the root
# frame, with the measure 1 + 2 × Sz(t); the source's register src is none
# that the root's allocation writes
def Cp.start(+f: Nat, +src: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +F: U32, +K: U32, +pg: U32, +L: U32,
  +I: List<&2, U32>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +P: List<&2, U32>, +Q: List<&2, U32>, +Bu: U32,
  +Wu: U32, +E: List<&2, U32>, +rs: List<&2, D.Rt>, +kc: List<&2, D.Kc>, +t: C.Term, +g: Nat, +es: List<&2, C.Term>,
  +B: C.Cir.Stmt, -R: List<&2, U32> -> C.Cir.Cells -> U32 -> U32 -> Type,
  hrd: @a: List<&2, U32> -> @c: U32 -> {Some{T.tm.reg(regs, src)} == List.get(&2, U32, List.set(&2, U32, W.Rp(a, D.Rg.ex(64n, regs, 0n)), 39n, c), src) : Maybe<&2, U32>},
  pre: D.Pre(regs, m, nx, F, K, ks, img, P, Q, E, Bu, Wu, rs, kc),
  ht: {D.Tm(g, m, ks, img, K, F, List.append(&2, U32, P, E), nx, T.tm.reg(regs, src)) == Some{t} : Maybe<&2, C.Term>},
  he: D.Env(m, ks, img, K, F, List.append(&2, U32, P, E), nx, T.tm.reg(regs, 36n), es),
  hl: {U32.to_nat(T.tm.reg(regs, 37n)) == List.length(&2, C.Term, es) : Nat},
  hf: {D.Fits(es, U32.from_nat(Nat.double(D.Sz(t)))) == True{} : Bool},
  hw: {Nat.is_le(D.Cp.W(t, es), U32.to_nat(Wu)) == True{} : Bool},
  k: @ms: C.Cir.Cells -> @nx2: U32 -> @pg2: U32 -> @P2: List<&2, U32> -> @Q2: List<&2, U32> -> @pend: U32 -> @n0: U32 ->
    @j: List<&2, U32> ->
    Cp.WI(es, ks, img, K, F, P, nx, Bu, Wu, E, rs, kc, T.tm.reg(regs, 36n), T.tm.reg(regs, 37n), T.tm.reg(regs, src), t,
      1n+Nat.double(D.Sz(t)), ms, nx2, [S.Sh.fr0(n0, T.tm.reg(regs, src), t)], P2, Q2, 0n, pend, n0, 0, n0) ->
    D.Ok(C.Cir.exec(1n+f, B, D.S(Cp.R(regs, pend, n0, 0, n0, j), ms, nx2, F, K, pg2, L, I)), F, K, L, I, R)) ->
  D.Ok(C.Cir.exec(1n+f, C.Cir.Stmt.seq{C.M.copy.root(C.R.croot(), src), C.Cir.Stmt.seq{C.M.set(C.R.cs(), C.M.g(C.R.croot())),
    C.Cir.Stmt.seq{C.M.set(C.R.cd(), C.M.c(0)), B}}}, D.S(regs, m, nx, F, K, pg, L, I)), F, K, L, I, R):
  ?TODO

# M.copy.end: n gets the copy from the root, whose cell goes to the pend list
def Cp.end(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +F: U32, +K: U32, +pg: U32, +L: U32,
  +I: List<&2, U32>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +P: List<&2, U32>, +Bu: U32, +Wu: U32,
  +E: List<&2, U32>, +rs: List<&2, D.Rt>, +kc: List<&2, D.Kc>, +t: C.Term, +es: List<&2, C.Term>, +x: U32, +Wm0: Nat,
  +rg: List<&2, U32>, +ms: C.Cir.Cells, +nx2: U32, +pg2: U32,
  fin: Cp.fin(regs, es, ks, img, K, F, P, nx, Bu, Wu, E, rs, kc, T.tm.reg(regs, 36n), T.tm.reg(regs, 37n), x, t, Wm0, rg, ms, nx2)) ->
  D.Ok(C.Cir.exec(1n+f, C.Cir.Stmt.seq{C.M.copy.end(C.R.n(), C.R.croot()), C.Cir.Stmt.nop{}}, D.S(rg, ms, nx2, F, K, pg2, L, I)),
    F, K, L, I, rg => ms => nx3 => pg3 => D.Ex(D.Wt, w => D.Post(D.Mo.subst{es}, t, regs, D.Cp.scratch(C.R.n()), C.R.n(),
      ks, img, K, F, P, E, nx, Bu, Wu, rs, kc, w, rg, ms, nx3))):
  ?TODO

# The claim
# ---------

# the root frame's measure, with the rounds' own fuel
def Cp.w0(+n0: U32, +x: U32, +t: C.Term, +es: List<&2, C.Term>) ->
  {Nat.is_le(Nat.add(W.Wm([S.Sh.fr0(n0, x, t)]), Cp.Bb(es)), Nat.add(1n+Nat.double(D.Sz(t)), Cp.Bb(es))) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.double(D.Sz(t)), 0n), Nat.double(D.Sz(t)), N.add_zero(Nat.double(D.Sz(t)))) :
    {Nat.is_le(Nat.add(1n+_, Cp.Bb(es)), Nat.add(1n+Nat.double(D.Sz(t)), Cp.Bb(es))) == True{} : Bool}
  K.Na.le_refl(Nat.add(1n+Nat.double(D.Sz(t)), Cp.Bb(es)))

# M.copy with the source in the register src, by its walk
def Cp.main(+src: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +F: U32, +K: U32, +pg: U32, +L: U32,
  +I: List<&2, U32>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +P: List<&2, U32>, +Q: List<&2, U32>, +Bu: U32,
  +Wu: U32, +E: List<&2, U32>, +rs: List<&2, D.Rt>, +kc: List<&2, D.Kc>, +t: C.Term, +g: Nat, +es: List<&2, C.Term>,
  hrd: @a: List<&2, U32> -> @c: U32 -> {Some{T.tm.reg(regs, src)} == List.get(&2, U32, List.set(&2, U32, W.Rp(a, D.Rg.ex(64n, regs, 0n)), 39n, c), src) : Maybe<&2, U32>},
  pre: D.Pre(regs, m, nx, F, K, ks, img, P, Q, E, Bu, Wu, rs, kc),
  ht: {D.Tm(g, m, ks, img, K, F, List.append(&2, U32, P, E), nx, T.tm.reg(regs, src)) == Some{t} : Maybe<&2, C.Term>},
  he: D.Env(m, ks, img, K, F, List.append(&2, U32, P, E), nx, T.tm.reg(regs, 36n), es),
  hl: {U32.to_nat(T.tm.reg(regs, 37n)) == List.length(&2, C.Term, es) : Nat},
  hf: {D.Fits(es, U32.from_nat(Nat.double(D.Sz(t)))) == True{} : Bool},
  hw: {Nat.is_le(D.Cp.W(t, es), U32.to_nat(Wu)) == True{} : Bool}) ->
  D.Ok(C.Cir.exec(1n+Nat.add(1n+Nat.double(D.Sz(t)), Cp.Bb(es)), C.M.copy(C.R.n(), src), D.S(regs, m, nx, F, K, pg, L, I)), F, K, L, I,
    rg => ms => nx2 => pg2 => D.Ex(D.Wt, w => D.Post(D.Mo.subst{es}, t, regs, D.Cp.scratch(C.R.n()), C.R.n(), ks, img, K, F,
      P, E, nx, Bu, Wu, rs, kc, w, rg, ms, nx2))):
  +W0 = {1n+Nat.double(D.Sz(t)) : Nat}
  +f = {Nat.add(W0, Cp.Bb(es)) : Nat}
  +x = {T.tm.reg(regs, src) : U32}
  +cenv = {T.tm.reg(regs, 36n) : U32}
  +clen = {T.tm.reg(regs, 37n) : U32}
  +mo = {D.Mo.subst{es} : D.Mo}
  +fin = {C.Cir.Stmt.seq{C.M.copy.end(C.R.n(), C.R.croot()), C.Cir.Stmt.nop{}} : C.Cir.Stmt}
  Cp.start(f, src, regs, m, nx, F, K, pg, L, I, ks, img, P, Q, Bu, Wu, E, rs, kc, t, g, es,
    C.Cir.Stmt.seq{Cp.loop.stmt(), fin},
    rg => ms => nx2 => pg2 => D.Ex(D.Wt, w => D.Post(mo, t, regs, D.Cp.scratch(C.R.n()), C.R.n(), ks, img, K, F, P, E, nx, Bu, Wu, rs, kc, w, rg, ms, nx2)),
    hrd, pre, ht, he, hl, hf, hw,
    +ms => +nx2 => +pg2 => +P2 => +Q2 => +pend => +n0 => +j => wi =>
      K.Ok.seq(f, Cp.loop.stmt(), fin, D.S(Cp.R(regs, pend, n0, 0, n0, j), ms, nx2, F, K, pg2, L, I), F, K, L, I,
        rg => ms3 => nx3 => pg3 => Cp.fin(regs, es, ks, img, K, F, P, nx, Bu, Wu, E, rs, kc, cenv, clen, x, t, W0, rg, ms3, nx3),
        rg => ms3 => nx3 => pg3 => D.Ex(D.Wt, w => D.Post(mo, t, regs, D.Cp.scratch(C.R.n()), C.R.n(), ks, img, K, F, P, E, nx, Bu, Wu, rs, kc, w, rg, ms3, nx3)),
        Cp.loop(f, regs, es, ks, img, K, F, L, I, P, nx, Bu, Wu, E, rs, kc, cenv, clen, x, t, W0, ms, nx2, pg2, [S.Sh.fr0(n0, x, t)], P2, Q2, 0n,
          pend, n0, 0, n0, j, Cp.w0(n0, x, t, es), wi),
        +rg => +ms3 => +nx3 => +pg3 => fq => Cp.end(f, regs, m, nx, F, K, pg, L, I, ks, img, P, Bu, Wu, E, rs, kc, t, es, x, W0, rg, ms3, nx3, pg3, fq)))

def D.Cp.ok(wt, regs, m, nx, F, K, pg, L, I, ks, img, P, Q, Bu, Wu, E, rs, kc, t, g, es, pre, ht, he, hl, hf, hw):
  match wt:
    case True{}:
      (1n+Nat.add(1n+Nat.double(D.Sz(t)), Cp.Bb(es)), Cp.main(C.R.wt(), regs, m, nx, F, K, pg, L, I, ks, img, P, Q, Bu, Wu, E, rs, kc, t, g, es,
        a => c => {==}, pre, ht, he, hl, hf, hw))
    case False{}:
      (1n+Nat.add(1n+Nat.double(D.Sz(t)), Cp.Bb(es)), Cp.main(C.R.z(), regs, m, nx, F, K, pg, L, I, ks, img, P, Q, Bu, Wu, E, rs, kc, t, g, es,
        a => c => {==}, pre, ht, he, hl, hf, hw))
