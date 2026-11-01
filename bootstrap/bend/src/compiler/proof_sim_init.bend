# compiler: the memory at the start of the program
# ================================================
#
# The data segment writes the book's cells from byte 20 = 20 × 1: its bytes
# are, cell by cell, the five words of each (wb.cells: five write32 per cell,
# WC), so the cells read back as they are (rc.wc); the input written after
# them from a = 20 (k + 1) keeps them (rc.wb), and reads back itself
# (rb.wb). These give the relation Q.Inv at the start of the program.

import Base
import ./impl.bend as C
import ./proof_need.bend as N
import ./proof_halt.bend as PH
import ./proof_module.bend as M
import ./proof_sim_mem.bend as Y
import ./proof_sim_nat.bend as Z
import ./proof_sim_inv.bend as Q
import ./proof_sim_frame.bend as F
import ./proof_sim_alloc.bend as A

# Words written byte by byte
# --------------------------

def W4(+m: C.Wasm.Bytes, +x: U32, +y1: U32, +y2: U32, +y3: U32, +w: U32) -> C.Wasm.Bytes:
  C.Wasm.write8(C.Wasm.write8(C.Wasm.write8(C.Wasm.write8(m, x, U32.and(w, 255)), y1, U32.and(U32.shrn(w, 8n), 255)),
    y2, U32.and(U32.shrn(w, 16n), 255)), y3, U32.shrn(w, 24n))

# c + j, as j increments
def inc.j(+j: Nat, +x: U32) -> {Z.incn(j, x) == U32.add(x, U32.from_nat(j)) : U32}:
  Equal.trans(U32, Z.incn(j, x), U32.add(U32.from_nat(j), x), U32.add(x, U32.from_nat(j)), Z.incn.add(j, x),
    U32.add_comm(U32.from_nat(j), x))

# the four bytes of w, written from x, are write32
def wb.word(+w: U32, +acc: List<&2, U32>, +x: U32, +m: C.Wasm.Bytes) ->
  {C.Wasm.write.bytes(C.Cir.word.bytes(w, acc), x, m) == C.Wasm.write.bytes(acc, Z.incn(4n, x), C.Wasm.write32(m, x, w)) : C.Wasm.Bytes}:
  %inc.j(1n, x) : {C.Wasm.write.bytes(acc, Z.incn(4n, x), W4(m, x, Z.incn(1n, x), Z.incn(2n, x), Z.incn(3n, x), w)) ==
    C.Wasm.write.bytes(acc, Z.incn(4n, x), W4(m, x, _, U32.add(x, 2), U32.add(x, 3), w)) : C.Wasm.Bytes}
  %inc.j(2n, x) : {C.Wasm.write.bytes(acc, Z.incn(4n, x), W4(m, x, Z.incn(1n, x), Z.incn(2n, x), Z.incn(3n, x), w)) ==
    C.Wasm.write.bytes(acc, Z.incn(4n, x), W4(m, x, Z.incn(1n, x), _, U32.add(x, 3), w)) : C.Wasm.Bytes}
  %inc.j(3n, x) : {C.Wasm.write.bytes(acc, Z.incn(4n, x), W4(m, x, Z.incn(1n, x), Z.incn(2n, x), Z.incn(3n, x), w)) ==
    C.Wasm.write.bytes(acc, Z.incn(4n, x), W4(m, x, Z.incn(1n, x), Z.incn(2n, x), _, w)) : C.Wasm.Bytes}
  {==}

# the five words of a cell, written to its fields
def W5(+m: C.Wasm.Bytes, +c: U32, +x0: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32) -> C.Wasm.Bytes:
  C.Wasm.write32(C.Wasm.write32(C.Wasm.write32(C.Wasm.write32(C.Wasm.write32(m, Q.at.f(c, 0n), x0), Q.at.f(c, 1n), x1),
    Q.at.f(c, 2n), x2), Q.at.f(c, 3n), x3), Q.at.f(c, 4n), x4)

def W5x(+m: C.Wasm.Bytes, +x: U32, +x0: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32) -> C.Wasm.Bytes:
  C.Wasm.write32(C.Wasm.write32(C.Wasm.write32(C.Wasm.write32(C.Wasm.write32(m, x, x0), Z.incn(4n, x), x1),
    Z.incn(8n, x), x2), Z.incn(12n, x), x3), Z.incn(16n, x), x4)

def W5.eq(+m: C.Wasm.Bytes, +c: U32, +x0: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32) ->
  {W5x(m, C.Cir.at(c), x0, x1, x2, x3, x4) == W5(m, c, x0, x1, x2, x3, x4) : C.Wasm.Bytes}:
  +x = C.Cir.at(c)
  %Equal.sym(U32, U32.add(x, 0), x, Y.U32.add_zero(x)) : {W5x(m, x, x0, x1, x2, x3, x4) ==
    C.Wasm.write32(C.Wasm.write32(C.Wasm.write32(C.Wasm.write32(C.Wasm.write32(m, _, x0), Q.at.f(c, 1n), x1),
      Q.at.f(c, 2n), x2), Q.at.f(c, 3n), x3), Q.at.f(c, 4n), x4) : C.Wasm.Bytes}
  %inc.j(4n, x) : {W5x(m, x, x0, x1, x2, x3, x4) ==
    C.Wasm.write32(C.Wasm.write32(C.Wasm.write32(C.Wasm.write32(C.Wasm.write32(m, x, x0), _, x1),
      Q.at.f(c, 2n), x2), Q.at.f(c, 3n), x3), Q.at.f(c, 4n), x4) : C.Wasm.Bytes}
  %inc.j(8n, x) : {W5x(m, x, x0, x1, x2, x3, x4) ==
    C.Wasm.write32(C.Wasm.write32(C.Wasm.write32(C.Wasm.write32(C.Wasm.write32(m, x, x0), Z.incn(4n, x), x1),
      _, x2), Q.at.f(c, 3n), x3), Q.at.f(c, 4n), x4) : C.Wasm.Bytes}
  %inc.j(12n, x) : {W5x(m, x, x0, x1, x2, x3, x4) ==
    C.Wasm.write32(C.Wasm.write32(C.Wasm.write32(C.Wasm.write32(C.Wasm.write32(m, x, x0), Z.incn(4n, x), x1),
      Z.incn(8n, x), x2), _, x3), Q.at.f(c, 4n), x4) : C.Wasm.Bytes}
  %inc.j(16n, x) : {W5x(m, x, x0, x1, x2, x3, x4) ==
    C.Wasm.write32(C.Wasm.write32(C.Wasm.write32(C.Wasm.write32(C.Wasm.write32(m, x, x0), Z.incn(4n, x), x1),
      Z.incn(8n, x), x2), Z.incn(12n, x), x3), _, x4) : C.Wasm.Bytes}
  {==}

# a cell's bytes, written from its first byte
def wb.cell(+x0: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +R: List<&2, U32>, +x: U32, +m: C.Wasm.Bytes) ->
  {C.Wasm.write.bytes(C.Cir.word.bytes(x0, C.Cir.word.bytes(x1, C.Cir.word.bytes(x2, C.Cir.word.bytes(x3, C.Cir.word.bytes(x4, R))))), x, m) ==
    C.Wasm.write.bytes(R, Z.incn(20n, x), W5x(m, x, x0, x1, x2, x3, x4)) : C.Wasm.Bytes}:
  +m1 = C.Wasm.write32(m, x, x0)
  +m2 = C.Wasm.write32(m1, Z.incn(4n, x), x1)
  +m3 = C.Wasm.write32(m2, Z.incn(8n, x), x2)
  +m4 = C.Wasm.write32(m3, Z.incn(12n, x), x3)
  +R4 = C.Cir.word.bytes(x4, R)
  +R3 = C.Cir.word.bytes(x3, R4)
  +R2 = C.Cir.word.bytes(x2, R3)
  +R1 = C.Cir.word.bytes(x1, R2)
  Equal.trans(C.Wasm.Bytes, C.Wasm.write.bytes(C.Cir.word.bytes(x0, R1), x, m), C.Wasm.write.bytes(R1, Z.incn(4n, x), m1),
    C.Wasm.write.bytes(R, Z.incn(20n, x), W5x(m, x, x0, x1, x2, x3, x4)), wb.word(x0, R1, x, m),
  Equal.trans(C.Wasm.Bytes, C.Wasm.write.bytes(R1, Z.incn(4n, x), m1), C.Wasm.write.bytes(R2, Z.incn(8n, x), m2),
    C.Wasm.write.bytes(R, Z.incn(20n, x), W5x(m, x, x0, x1, x2, x3, x4)), wb.word(x1, R2, Z.incn(4n, x), m1),
  Equal.trans(C.Wasm.Bytes, C.Wasm.write.bytes(R2, Z.incn(8n, x), m2), C.Wasm.write.bytes(R3, Z.incn(12n, x), m3),
    C.Wasm.write.bytes(R, Z.incn(20n, x), W5x(m, x, x0, x1, x2, x3, x4)), wb.word(x2, R3, Z.incn(8n, x), m2),
  Equal.trans(C.Wasm.Bytes, C.Wasm.write.bytes(R3, Z.incn(12n, x), m3), C.Wasm.write.bytes(R4, Z.incn(16n, x), m4),
    C.Wasm.write.bytes(R, Z.incn(20n, x), W5x(m, x, x0, x1, x2, x3, x4)), wb.word(x3, R4, Z.incn(12n, x), m3),
    wb.word(x4, R, Z.incn(16n, x), m4)))))

# Cells written word by word
# --------------------------

# a U32 is its number
def u32.inj(+x: U32, +y: U32, e: {U32.to_nat(x) == U32.to_nat(y) : Nat}) -> {x == y : U32}:
  Equal.trans(U32, x, U32.from_nat(U32.to_nat(x)), y, Equal.sym(U32, U32.from_nat(U32.to_nat(x)), x, Z.from.to(x)),
    Equal.trans(U32, U32.from_nat(U32.to_nat(x)), U32.from_nat(U32.to_nat(y)), y,
      Equal.cong(Nat, U32, z => U32.from_nat(z), U32.to_nat(x), U32.to_nat(y), e), Z.from.to(y)))

# the cell after c starts 20 bytes after it
def at.inc(+c: U32, +Cn: Nat, +ec: {U32.to_nat(c) == Cn : Nat}, +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +h: N.Le(2n+Cn, P)) -> {Z.incn(20n, C.Cir.at(c)) == C.Cir.at(U32.inc(c)) : U32}:
  +x = C.Cir.at(c)
  +h1 = N.le_trans(1n+Cn, 2n+Cn, P, N.le_succ(1n+Cn, 1n+Cn, N.le_refl(1n+Cn)), h)
  +hc = N.le_rw_l(1n+Cn, 1n+U32.to_nat(c), P, Equal.cong(Nat, Nat, z => 1n+z, Cn, U32.to_nat(c), Equal.sym(Nat, U32.to_nat(c), Cn, ec)), h1)
  +eA = Equal.trans(Nat, U32.to_nat(x), PH.H.t20(U32.to_nat(c)), PH.H.t20(Cn), F.at.nat(c, P, hP, N.weaken(U32.to_nat(c), P, hc)),
    Equal.cong(Nat, Nat, z => PH.H.t20(z), U32.to_nat(c), Cn, ec))
  +hr = N.le_rw_l(21n+PH.H.t20(Cn), 21n+U32.to_nat(x), W,
    Equal.cong(Nat, Nat, z => 21n+z, PH.H.t20(Cn), U32.to_nat(x), Equal.sym(Nat, U32.to_nat(x), PH.H.t20(Cn), eA)),
    N.le_trans(21n+PH.H.t20(Cn), 36n+PH.H.t20(Cn), W, N.le_add_l(15n, 21n+PH.H.t20(Cn)), F.cell.room(Cn, P, hP, W, hW, h1)))
  +e1 = Equal.trans(Nat, U32.to_nat(Z.incn(20n, x)), U32.to_nat(U32.add(U32.from_nat(20n), x)), 20n+PH.H.t20(Cn),
    Equal.cong(U32, Nat, z => U32.to_nat(z), Z.incn(20n, x), U32.add(U32.from_nat(20n), x), Z.incn.add(20n, x)),
    Equal.trans(Nat, U32.to_nat(U32.add(U32.from_nat(20n), x)), 20n+U32.to_nat(x), 20n+PH.H.t20(Cn),
      Z.u32.add_ex(U32.from_nat(20n), x, W, hW, hr),
      Equal.cong(Nat, Nat, z => 20n+z, U32.to_nat(x), PH.H.t20(Cn), eA)))
  +ei = F.inc.eq(c, Cn, ec, W, hW, N.le_trans(2n+Cn, 3n+Cn, W, N.le_succ(2n+Cn, 2n+Cn, N.le_refl(2n+Cn)),
    N.le_rw_r(3n+Cn, PH.H.W(32n), W, Equal.sym(Nat, W, PH.H.W(32n), hW), PH.H.small(32n, 1n+Cn, P, hP, h))))
  +hci = N.le_rw_l(1n+Cn, U32.to_nat(U32.inc(c)), P, Equal.sym(Nat, U32.to_nat(U32.inc(c)), 1n+Cn, ei), h1)
  +e2 = Equal.trans(Nat, U32.to_nat(C.Cir.at(U32.inc(c))), PH.H.t20(U32.to_nat(U32.inc(c))), 20n+PH.H.t20(Cn),
    F.at.nat(U32.inc(c), P, hP, hci), Equal.cong(Nat, Nat, z => PH.H.t20(z), U32.to_nat(U32.inc(c)), 1n+Cn, ei))
  u32.inj(Z.incn(20n, x), C.Cir.at(U32.inc(c)), Equal.trans(Nat, U32.to_nat(Z.incn(20n, x)), 20n+PH.H.t20(Cn), U32.to_nat(C.Cir.at(U32.inc(c))),
    e1, Equal.sym(Nat, U32.to_nat(C.Cir.at(U32.inc(c))), 20n+PH.H.t20(Cn), e2)))

# the cells cs, from the cell c on, written word by word
def WC(cs: List<&2, C.Cir.Cell>, +c: U32, +m: C.Wasm.Bytes) -> C.Wasm.Bytes:
  match cs:
    case Nil{}:
      m
    case Con{C.Cir.Cell{+x0, +x1, +x2, +x3, +x4}, rest}:
      WC(rest, U32.inc(c), W5(m, c, x0, x1, x2, x3, x4))

# the bytes of cs, from 20 c on, are WC
def wb.cells(cs: List<&2, C.Cir.Cell>, +c: U32, +m: C.Wasm.Bytes, +Cn: Nat, +ec: {U32.to_nat(c) == Cn : Nat},
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +h: N.Le(1n+Nat.add(List.length(&2, C.Cir.Cell, cs), Cn), P)) ->
  {C.Wasm.write.bytes(C.Cir.bytes(cs), C.Cir.at(c), m) == WC(cs, c, m) : C.Wasm.Bytes}:
  match cs:
    case Nil{}:
      {==}
    case Con{C.Cir.Cell{+x0, +x1, +x2, +x3, +x4}, +rest}:
      +x = C.Cir.at(c)
      +R = C.Cir.bytes(rest)
      +m5 = W5(m, c, x0, x1, x2, x3, x4)
      +q = List.length(&2, C.Cir.Cell, rest)
      +h2 = N.le_rw_l(2n+Nat.add(q, Cn), 1n+Nat.add(q, 1n+Cn), P,
        Equal.cong(Nat, Nat, z => 1n+z, 1n+Nat.add(q, Cn), Nat.add(q, 1n+Cn), Equal.sym(Nat, Nat.add(q, 1n+Cn), 1n+Nat.add(q, Cn), N.add_succ_r(q, Cn))), h)
      +hc2 = N.le_trans(2n+Cn, 2n+Nat.add(q, Cn), P, N.le_add_l(q, Cn), h)
      +ei = F.inc.eq(c, Cn, ec, W, hW, N.le_trans(2n+Cn, 3n+Cn, W, N.le_succ(2n+Cn, 2n+Cn, N.le_refl(2n+Cn)),
        N.le_rw_r(3n+Cn, PH.H.W(32n), W, Equal.sym(Nat, W, PH.H.W(32n), hW), PH.H.small(32n, 1n+Cn, P, hP, hc2))))
      Equal.trans(C.Wasm.Bytes, C.Wasm.write.bytes(C.Cir.bytes(Con{C.Cir.Cell{x0, x1, x2, x3, x4}, rest}), x, m),
        C.Wasm.write.bytes(R, Z.incn(20n, x), W5x(m, x, x0, x1, x2, x3, x4)), WC(rest, U32.inc(c), m5),
        wb.cell(x0, x1, x2, x3, x4, R, x, m),
        %Equal.sym(U32, Z.incn(20n, x), C.Cir.at(U32.inc(c)), at.inc(c, Cn, ec, P, hP, W, hW, hc2)) :
          {C.Wasm.write.bytes(R, _, W5x(m, x, x0, x1, x2, x3, x4)) == WC(rest, U32.inc(c), m5) : C.Wasm.Bytes}
        %Equal.sym(C.Wasm.Bytes, W5x(m, x, x0, x1, x2, x3, x4), m5, W5.eq(m, c, x0, x1, x2, x3, x4)) :
          {C.Wasm.write.bytes(R, C.Cir.at(U32.inc(c)), _) == WC(rest, U32.inc(c), m5) : C.Wasm.Bytes}
        wb.cells(rest, U32.inc(c), m5, 1n+Cn, ei, P, hP, W, hW, h2))

# a cell written word by word reads back as itself
def rcell.W5(+m: C.Wasm.Bytes, +c: U32, +x0: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32,
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hc: N.Le(1n+U32.to_nat(c), P)) -> {Q.RCell(W5(m, c, x0, x1, x2, x3, x4), c) == C.Cir.Cell{x0, x1, x2, x3, x4} : C.Cir.Cell}:
  +m1 = C.Wasm.write32(m, Q.at.f(c, 0n), x0)
  +m2 = C.Wasm.write32(m1, Q.at.f(c, 1n), x1)
  +m3 = C.Wasm.write32(m2, Q.at.f(c, 2n), x2)
  +m4 = C.Wasm.write32(m3, Q.at.f(c, 3n), x3)
  +r1 = F.rcell.set(m, c, 0n, x0, P, hP, W, hW, hc, {==})
  +r2 = F.rcell.set(m1, c, 1n, x1, P, hP, W, hW, hc, {==})
  +r3 = F.rcell.set(m2, c, 2n, x2, P, hP, W, hW, hc, {==})
  +r4 = F.rcell.set(m3, c, 3n, x3, P, hP, W, hW, hc, {==})
  +r5 = F.rcell.set(m4, c, 4n, x4, P, hP, W, hW, hc, {==})
  +S1 = C.Cir.Cell.set(0n, Q.RCell(m, c), x0)
  +S2 = C.Cir.Cell.set(1n, S1, x1)
  +S3 = C.Cir.Cell.set(2n, S2, x2)
  +S4 = C.Cir.Cell.set(3n, S3, x3)
  +e2 = Equal.trans(C.Cir.Cell, Q.RCell(m2, c), C.Cir.Cell.set(1n, Q.RCell(m1, c), x1), S2, r2,
    Equal.cong(C.Cir.Cell, C.Cir.Cell, z => C.Cir.Cell.set(1n, z, x1), Q.RCell(m1, c), S1, r1))
  +e3 = Equal.trans(C.Cir.Cell, Q.RCell(m3, c), C.Cir.Cell.set(2n, Q.RCell(m2, c), x2), S3, r3,
    Equal.cong(C.Cir.Cell, C.Cir.Cell, z => C.Cir.Cell.set(2n, z, x2), Q.RCell(m2, c), S2, e2))
  +e4 = Equal.trans(C.Cir.Cell, Q.RCell(m4, c), C.Cir.Cell.set(3n, Q.RCell(m3, c), x3), S4, r4,
    Equal.cong(C.Cir.Cell, C.Cir.Cell, z => C.Cir.Cell.set(3n, z, x3), Q.RCell(m3, c), S3, e3))
  Equal.trans(C.Cir.Cell, Q.RCell(W5(m, c, x0, x1, x2, x3, x4), c), C.Cir.Cell.set(4n, Q.RCell(m4, c), x4), C.Cir.Cell{x0, x1, x2, x3, x4}, r5,
    Equal.cong(C.Cir.Cell, C.Cir.Cell, z => C.Cir.Cell.set(4n, z, x4), Q.RCell(m4, c), S4, e4))

# a word written to field j of a later cell c2 keeps the cell c
def fr.out(+m: C.Wasm.Bytes, +c: U32, +c2: U32, +j: Nat, +v: U32, +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hc: N.Le(1n+U32.to_nat(c), P), +hc2: N.Le(1n+U32.to_nat(c2), P),
  +hj: N.Le(4n+F.O(j), 20n), +hs: N.Le(1n+U32.to_nat(c), U32.to_nat(c2))) ->
  {Q.RCell(C.Wasm.write32(m, Q.at.f(c2, j), v), c) == Q.RCell(m, c) : C.Cir.Cell}:
  +a = Q.at.f(c2, j)
  +T2 = PH.H.t20(U32.to_nat(c2))
  +l = N.le_trans(PH.H.t20(1n+U32.to_nat(c)), T2, Nat.add(F.O(j), T2), PH.H.t20_mono(1n+U32.to_nat(c), U32.to_nat(c2), hs), N.le_add_l(F.O(j), T2))
  +s = {Inl{N.le_rw_r(20n+PH.H.t20(U32.to_nat(c)), Nat.add(F.O(j), T2), U32.to_nat(a),
    Equal.sym(Nat, U32.to_nat(a), Nat.add(F.O(j), T2), F.fld.nat(c2, j, P, hP, W, hW, hc2, hj)), l)} :
    Either<&2, &2, N.Le(20n+PH.H.t20(U32.to_nat(c)), U32.to_nat(a)), N.Le(4n+U32.to_nat(a), PH.H.t20(U32.to_nat(c)))>}
  F.rcell.w32(m, a, v, c, P, hP, W, hW, hc, F.fld.room(c2, j, P, hP, W, hW, hc2, hj), s)

# the five words of a later cell keep the cell c
def fr.W5(+m: C.Wasm.Bytes, +c: U32, +c2: U32, +x0: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32,
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hc: N.Le(1n+U32.to_nat(c), P), +hc2: N.Le(1n+U32.to_nat(c2), P), +hs: N.Le(1n+U32.to_nat(c), U32.to_nat(c2))) ->
  {Q.RCell(W5(m, c2, x0, x1, x2, x3, x4), c) == Q.RCell(m, c) : C.Cir.Cell}:
  +m1 = C.Wasm.write32(m, Q.at.f(c2, 0n), x0)
  +m2 = C.Wasm.write32(m1, Q.at.f(c2, 1n), x1)
  +m3 = C.Wasm.write32(m2, Q.at.f(c2, 2n), x2)
  +m4 = C.Wasm.write32(m3, Q.at.f(c2, 3n), x3)
  Equal.trans(C.Cir.Cell, Q.RCell(W5(m, c2, x0, x1, x2, x3, x4), c), Q.RCell(m4, c), Q.RCell(m, c), fr.out(m4, c, c2, 4n, x4, P, hP, W, hW, hc, hc2, Unit{}, hs),
  Equal.trans(C.Cir.Cell, Q.RCell(m4, c), Q.RCell(m3, c), Q.RCell(m, c), fr.out(m3, c, c2, 3n, x3, P, hP, W, hW, hc, hc2, Unit{}, hs),
  Equal.trans(C.Cir.Cell, Q.RCell(m3, c), Q.RCell(m2, c), Q.RCell(m, c), fr.out(m2, c, c2, 2n, x2, P, hP, W, hW, hc, hc2, Unit{}, hs),
  Equal.trans(C.Cir.Cell, Q.RCell(m2, c), Q.RCell(m1, c), Q.RCell(m, c), fr.out(m1, c, c2, 1n, x1, P, hP, W, hW, hc, hc2, Unit{}, hs),
    fr.out(m, c, c2, 0n, x0, P, hP, W, hW, hc, hc2, Unit{}, hs)))))

# the cells written from c2 on keep a cell c before them
def rcell.wc(cs: List<&2, C.Cir.Cell>, +c2: U32, +m: C.Wasm.Bytes, +c: U32, +C2n: Nat, +ec2: {U32.to_nat(c2) == C2n : Nat},
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hc: N.Le(1n+U32.to_nat(c), P), +hs: N.Le(1n+U32.to_nat(c), C2n), +h: N.Le(Nat.add(List.length(&2, C.Cir.Cell, cs), C2n), P)) ->
  {Q.RCell(WC(cs, c2, m), c) == Q.RCell(m, c) : C.Cir.Cell}:
  match cs:
    case Nil{}:
      {==}
    case Con{C.Cir.Cell{+x0, +x1, +x2, +x3, +x4}, +rest}:
      +q = List.length(&2, C.Cir.Cell, rest)
      +hq = N.le_rw_l(1n+Nat.add(q, C2n), Nat.add(q, 1n+C2n), P, Equal.sym(Nat, Nat.add(q, 1n+C2n), 1n+Nat.add(q, C2n), N.add_succ_r(q, C2n)), h)
      +h1 = N.le_trans(1n+C2n, 1n+Nat.add(q, C2n), P, N.le_add_l(q, C2n), h)
      +hc2 = N.le_rw_l(1n+C2n, 1n+U32.to_nat(c2), P, Equal.cong(Nat, Nat, z => 1n+z, C2n, U32.to_nat(c2), Equal.sym(Nat, U32.to_nat(c2), C2n, ec2)), h1)
      +hs2 = N.le_rw_r(1n+U32.to_nat(c), C2n, U32.to_nat(c2), Equal.sym(Nat, U32.to_nat(c2), C2n, ec2), hs)
      +ei = F.inc.eq(c2, C2n, ec2, W, hW, N.le_rw_r(2n+C2n, PH.H.W(32n), W, Equal.sym(Nat, W, PH.H.W(32n), hW), PH.H.small(32n, C2n, P, hP, h1)))
      +m5 = W5(m, c2, x0, x1, x2, x3, x4)
      Equal.trans(C.Cir.Cell, Q.RCell(WC(rest, U32.inc(c2), m5), c), Q.RCell(m5, c), Q.RCell(m, c),
        rcell.wc(rest, U32.inc(c2), m5, c, 1n+C2n, ei, P, hP, W, hW, hc, N.le_succ(1n+U32.to_nat(c), C2n, hs), hq),
        fr.W5(m, c, c2, x0, x1, x2, x3, x4, P, hP, W, hW, hc, hc2, hs2))

# the cells cs written from c on read back as cs
def rc.wc(cs: List<&2, C.Cir.Cell>, +c: U32, +m: C.Wasm.Bytes, +Cn: Nat, +ec: {U32.to_nat(c) == Cn : Nat},
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +h: N.Le(Nat.add(List.length(&2, C.Cir.Cell, cs), Cn), P)) ->
  {Q.RC(List.length(&2, C.Cir.Cell, cs), WC(cs, c, m), c) == cs : List<&2, C.Cir.Cell>}:
  match cs:
    case Nil{}:
      {==}
    case Con{C.Cir.Cell{+x0, +x1, +x2, +x3, +x4}, +rest}:
      +q = List.length(&2, C.Cir.Cell, rest)
      +hq = N.le_rw_l(1n+Nat.add(q, Cn), Nat.add(q, 1n+Cn), P, Equal.sym(Nat, Nat.add(q, 1n+Cn), 1n+Nat.add(q, Cn), N.add_succ_r(q, Cn)), h)
      +h1 = N.le_trans(1n+Cn, 1n+Nat.add(q, Cn), P, N.le_add_l(q, Cn), h)
      +hc = N.le_rw_l(1n+Cn, 1n+U32.to_nat(c), P, Equal.cong(Nat, Nat, z => 1n+z, Cn, U32.to_nat(c), Equal.sym(Nat, U32.to_nat(c), Cn, ec)), h1)
      +ei = F.inc.eq(c, Cn, ec, W, hW, N.le_rw_r(2n+Cn, PH.H.W(32n), W, Equal.sym(Nat, W, PH.H.W(32n), hW), PH.H.small(32n, Cn, P, hP, h1)))
      +m5 = W5(m, c, x0, x1, x2, x3, x4)
      +X = WC(rest, U32.inc(c), m5)
      +hs = N.le_rw_l(1n+Cn, 1n+U32.to_nat(c), 1n+Cn, Equal.cong(Nat, Nat, z => 1n+z, Cn, U32.to_nat(c), Equal.sym(Nat, U32.to_nat(c), Cn, ec)), N.le_refl(1n+Cn))
      F.cons.cong(C.Cir.Cell, Q.RCell(X, c), C.Cir.Cell{x0, x1, x2, x3, x4}, Q.RC(q, X, U32.inc(c)), rest,
        Equal.trans(C.Cir.Cell, Q.RCell(X, c), Q.RCell(m5, c), C.Cir.Cell{x0, x1, x2, x3, x4},
          rcell.wc(rest, U32.inc(c), m5, c, 1n+Cn, ei, P, hP, W, hW, hc, hs, hq),
          rcell.W5(m, c, x0, x1, x2, x3, x4, P, hP, W, hW, hc)),
        rc.wc(rest, U32.inc(c), m5, 1n+Cn, ei, P, hP, W, hW, hq))

# The cells as Cir loads them
# ---------------------------

# the cells loaded from c2 on keep a cell c before them
def get.load(cs: List<&2, C.Cir.Cell>, +c2: U32, +cl: C.Cir.Cells, +c: U32, +C2n: Nat, +ec2: {U32.to_nat(c2) == C2n : Nat},
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hs: N.Le(1n+U32.to_nat(c), C2n), +h: N.Le(Nat.add(List.length(&2, C.Cir.Cell, cs), C2n), P)) ->
  {C.Cir.Cells.get(C.Cir.load(cs, c2, cl), c) == C.Cir.Cells.get(cl, c) : C.Cir.Cell}:
  match cs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +q = List.length(&2, C.Cir.Cell, rest)
      +hq = N.le_rw_l(1n+Nat.add(q, C2n), Nat.add(q, 1n+C2n), P, Equal.sym(Nat, Nat.add(q, 1n+C2n), 1n+Nat.add(q, C2n), N.add_succ_r(q, C2n)), h)
      +h1 = N.le_trans(1n+C2n, 1n+Nat.add(q, C2n), P, N.le_add_l(q, C2n), h)
      +ei = F.inc.eq(c2, C2n, ec2, W, hW, N.le_rw_r(2n+C2n, PH.H.W(32n), W, Equal.sym(Nat, W, PH.H.W(32n), hW), PH.H.small(32n, C2n, P, hP, h1)))
      +hs2 = N.le_rw_r(1n+U32.to_nat(c), C2n, U32.to_nat(c2), Equal.sym(Nat, U32.to_nat(c2), C2n, ec2), hs)
      +cl2 = C.Cir.Cells.set(cl, c2, x)
      Equal.trans(C.Cir.Cell, C.Cir.Cells.get(C.Cir.load(rest, U32.inc(c2), cl2), c), C.Cir.Cells.get(cl2, c), C.Cir.Cells.get(cl, c),
        get.load(rest, U32.inc(c2), cl2, c, 1n+C2n, ei, P, hP, W, hW, N.le_succ(1n+U32.to_nat(c), C2n, hs), hq),
        F.cells.other(cl, c2, c, x, F.ne.nat(c, c2, Inl{hs2})))

# the cells cs loaded from c on are cs
def gc.load(cs: List<&2, C.Cir.Cell>, +c: U32, +cl: C.Cir.Cells, +Cn: Nat, +ec: {U32.to_nat(c) == Cn : Nat},
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +h: N.Le(Nat.add(List.length(&2, C.Cir.Cell, cs), Cn), P)) ->
  {Q.GC(List.length(&2, C.Cir.Cell, cs), C.Cir.load(cs, c, cl), c) == cs : List<&2, C.Cir.Cell>}:
  match cs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +q = List.length(&2, C.Cir.Cell, rest)
      +hq = N.le_rw_l(1n+Nat.add(q, Cn), Nat.add(q, 1n+Cn), P, Equal.sym(Nat, Nat.add(q, 1n+Cn), 1n+Nat.add(q, Cn), N.add_succ_r(q, Cn)), h)
      +h1 = N.le_trans(1n+Cn, 1n+Nat.add(q, Cn), P, N.le_add_l(q, Cn), h)
      +ei = F.inc.eq(c, Cn, ec, W, hW, N.le_rw_r(2n+Cn, PH.H.W(32n), W, Equal.sym(Nat, W, PH.H.W(32n), hW), PH.H.small(32n, Cn, P, hP, h1)))
      +cl2 = C.Cir.Cells.set(cl, c, x)
      +X = C.Cir.load(rest, U32.inc(c), cl2)
      +hs = N.le_rw_l(1n+Cn, 1n+U32.to_nat(c), 1n+Cn, Equal.cong(Nat, Nat, z => 1n+z, Cn, U32.to_nat(c), Equal.sym(Nat, U32.to_nat(c), Cn, ec)), N.le_refl(1n+Cn))
      F.cons.cong(C.Cir.Cell, C.Cir.Cells.get(X, c), x, Q.GC(q, X, U32.inc(c)), rest,
        Equal.trans(C.Cir.Cell, C.Cir.Cells.get(X, c), C.Cir.Cells.get(cl2, c), x,
          get.load(rest, U32.inc(c), cl2, c, 1n+Cn, ei, P, hP, W, hW, hs, hq), F.cells.same(cl, c, x)),
        gc.load(rest, U32.inc(c), cl2, 1n+Cn, ei, P, hP, W, hW, hq))

# The input
# ---------

# the bytes written from x on keep a byte y before them
def r8.wb(xs: List<&2, U32>, +x: U32, +m: C.Wasm.Bytes, +y: U32, +Xn: Nat, +ex: {U32.to_nat(x) == Xn : Nat},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hy: N.Le(1n+U32.to_nat(y), Xn), +hx: N.Le(1n+Nat.add(List.length(&2, U32, xs), Xn), W)) ->
  {Y.R8(C.Wasm.write.bytes(xs, x, m), y) == Y.R8(m, y) : U32}:
  match xs:
    case Nil{}:
      {==}
    case Con{+b, +rest}:
      +q = List.length(&2, U32, rest)
      +hq = N.le_rw_l(2n+Nat.add(q, Xn), 1n+Nat.add(q, 1n+Xn), W,
        Equal.cong(Nat, Nat, z => 1n+z, 1n+Nat.add(q, Xn), Nat.add(q, 1n+Xn), Equal.sym(Nat, Nat.add(q, 1n+Xn), 1n+Nat.add(q, Xn), N.add_succ_r(q, Xn))), hx)
      +ei = F.inc.eq(x, Xn, ex, W, hW, N.le_trans(2n+Xn, 2n+Nat.add(q, Xn), W, N.le_add_l(q, Xn), hx))
      +hx2 = N.le_rw_r(1n+U32.to_nat(y), Xn, U32.to_nat(x), Equal.sym(Nat, U32.to_nat(x), Xn, ex), hy)
      Equal.trans(U32, Y.R8(C.Wasm.write.bytes(rest, U32.inc(x), C.Wasm.write8(m, x, b)), y), Y.R8(C.Wasm.write8(m, x, b), y), Y.R8(m, y),
        r8.wb(rest, U32.inc(x), C.Wasm.write8(m, x, b), y, 1n+Xn, ei, W, hW, N.le_succ(1n+U32.to_nat(y), Xn, hy), hq),
        Y.R8.other(m, x, y, b, F.ne.nat(y, x, Inl{hx2})))

# the bytes xs written from x read back as xs
def rb.wb(xs: List<&2, U32>, +x: U32, +m: C.Wasm.Bytes, +Xn: Nat, +ex: {U32.to_nat(x) == Xn : Nat},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hx: N.Le(1n+Nat.add(List.length(&2, U32, xs), Xn), W)) ->
  {Q.RB(List.length(&2, U32, xs), C.Wasm.write.bytes(xs, x, m), x) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+b, +rest}:
      +q = List.length(&2, U32, rest)
      +hq = N.le_rw_l(2n+Nat.add(q, Xn), 1n+Nat.add(q, 1n+Xn), W,
        Equal.cong(Nat, Nat, z => 1n+z, 1n+Nat.add(q, Xn), Nat.add(q, 1n+Xn), Equal.sym(Nat, Nat.add(q, 1n+Xn), 1n+Nat.add(q, Xn), N.add_succ_r(q, Xn))), hx)
      +ei = F.inc.eq(x, Xn, ex, W, hW, N.le_trans(2n+Xn, 2n+Nat.add(q, Xn), W, N.le_add_l(q, Xn), hx))
      +m1 = C.Wasm.write8(m, x, b)
      +X = C.Wasm.write.bytes(rest, U32.inc(x), m1)
      +hy = N.le_rw_l(1n+Xn, 1n+U32.to_nat(x), 1n+Xn, Equal.cong(Nat, Nat, z => 1n+z, Xn, U32.to_nat(x), Equal.sym(Nat, U32.to_nat(x), Xn, ex)), N.le_refl(1n+Xn))
      F.cons.cong(U32, Y.R8(X, x), b, Q.RB(q, X, U32.inc(x)), rest,
        Equal.trans(U32, Y.R8(X, x), Y.R8(m1, x), b, r8.wb(rest, U32.inc(x), m1, x, 1n+Xn, ei, W, hW, hy, hq), Y.R8.same(m, x, b)),
        rb.wb(rest, U32.inc(x), m1, 1n+Xn, ei, W, hW, hq))

# the bytes written from x on keep the cells c to c + q - 1 before them
def rc.wb(xs: List<&2, U32>, +x: U32, +m: C.Wasm.Bytes, +q: Nat, +c: U32, +Cn: Nat, +ec: {U32.to_nat(c) == Cn : Nat},
  +Xn: Nat, +ex: {U32.to_nat(x) == Xn : Nat},
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hs: N.Le(PH.H.t20(Nat.add(q, Cn)), Xn), +hcq: N.Le(Nat.add(q, Cn), P), +hx: N.Le(1n+Nat.add(List.length(&2, U32, xs), Xn), W)) ->
  {Q.RC(q, C.Wasm.write.bytes(xs, x, m), c) == Q.RC(q, m, c) : List<&2, C.Cir.Cell>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+b, +rest}:
      +r = List.length(&2, U32, rest)
      +hq = N.le_rw_l(2n+Nat.add(r, Xn), 1n+Nat.add(r, 1n+Xn), W,
        Equal.cong(Nat, Nat, z => 1n+z, 1n+Nat.add(r, Xn), Nat.add(r, 1n+Xn), Equal.sym(Nat, Nat.add(r, 1n+Xn), 1n+Nat.add(r, Xn), N.add_succ_r(r, Xn))), hx)
      +ei = F.inc.eq(x, Xn, ex, W, hW, N.le_trans(2n+Xn, 2n+Nat.add(r, Xn), W, N.le_add_l(r, Xn), hx))
      +m1 = C.Wasm.write8(m, x, b)
      +hs2 = N.le_rw_r(PH.H.t20(Nat.add(q, Cn)), Xn, U32.to_nat(x), Equal.sym(Nat, U32.to_nat(x), Xn, ex), hs)
      Equal.trans(List<&2, C.Cir.Cell>, Q.RC(q, C.Wasm.write.bytes(rest, U32.inc(x), m1), c), Q.RC(q, m1, c), Q.RC(q, m, c),
        rc.wb(rest, U32.inc(x), m1, q, c, Cn, ec, 1n+Xn, ei, P, hP, W, hW, N.le_succ(PH.H.t20(Nat.add(q, Cn)), Xn, hs), hcq, hq),
        F.RC.w8(q, m, x, b, c, Cn, ec, P, hP, W, hW, hcq,
          {Inl{hs2} : Either<&2, &2, N.Le(PH.H.t20(Nat.add(q, Cn)), U32.to_nat(x)), N.Le(1n+U32.to_nat(x), PH.H.t20(Cn))>}))

# The relation at the start
# -------------------------

def B0(+cells: List<&2, C.Cir.Cell>) -> C.Wasm.Bytes:
  C.Wasm.write.bytes(C.Cir.bytes(cells), 20, C.Wasm.Bytes.zero{})

def B2(+cells: List<&2, C.Cir.Cell>, +i: List<&2, U32>) -> C.Wasm.Bytes:
  C.Wasm.write.bytes(i, C.Cir.input.at(C.Wasm.encode.len(C.Cir.Cell, cells)), B0(cells))

def sub.self(+x: Nat) -> {Nat.sub(x, x) == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      sub.self(p)

# the relation holds as the program starts, with next = first = fst
def inv0(+cells: List<&2, C.Cir.Cell>, +i: List<&2, U32>, +len: U32, +p2: U32, +lim: U32, +fst: U32,
  +P: Nat, +G: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +eK: {U32.to_nat(C.Wasm.encode.len(C.Cir.Cell, cells)) == List.length(&2, C.Cir.Cell, cells) : Nat},
  +hK: N.Le(2n+List.length(&2, C.Cir.Cell, cells), P),
  +eLn: {len == C.Wasm.encode.len(U32, i) : U32},
  +hEP: N.Le(Nat.add(U32.to_nat(C.Cir.input.at(C.Wasm.encode.len(C.Cir.Cell, cells))), List.length(&2, U32, i)), PH.H.t20(P)),
  +hEB: N.Le(Nat.add(U32.to_nat(C.Cir.input.at(C.Wasm.encode.len(C.Cir.Cell, cells))), List.length(&2, U32, i)), Q.PB(p2)),
  +hEF: N.Le(Nat.add(U32.to_nat(C.Cir.input.at(C.Wasm.encode.len(C.Cir.Cell, cells))), List.length(&2, U32, i)), PH.H.t20(U32.to_nat(fst))),
  +hFP: N.Le(U32.to_nat(fst), P), +hlm: N.Le(1n+U32.to_nat(lim), G), +hpl: N.Le(U32.to_nat(p2), U32.to_nat(lim))) ->
  Q.Inv(P, G, C.Cir.input.at(C.Wasm.encode.len(C.Cir.Cell, cells)), len, C.Cir.load(cells, 1, C.Cir.Cells.none{}), fst, fst,
    C.Wasm.encode.len(C.Cir.Cell, cells), p2, lim, i, [], 0, B2(cells, i)):
  +k = C.Wasm.encode.len(C.Cir.Cell, cells)
  +a = C.Cir.input.at(k)
  +A = U32.to_nat(a)
  +Kc = List.length(&2, C.Cir.Cell, cells)
  +L = List.length(&2, U32, i)
  +cl = C.Cir.load(cells, 1, C.Cir.Cells.none{})
  +m = B2(cells, i)
  +hK1 = N.le_trans(1n+Kc, 2n+Kc, P, N.le_succ(1n+Kc, 1n+Kc, N.le_refl(1n+Kc)), hK)
  # A = 20 (K + 1)
  +ei = F.inc.eq(k, Kc, eK, W, hW, N.le_trans(2n+Kc, 3n+Kc, W, N.le_succ(2n+Kc, 2n+Kc, N.le_refl(2n+Kc)),
    N.le_rw_r(3n+Kc, PH.H.W(32n), W, Equal.sym(Nat, W, PH.H.W(32n), hW), PH.H.small(32n, 1n+Kc, P, hP, hK))))
  +eA = Equal.trans(Nat, A, PH.H.t20(U32.to_nat(U32.inc(k))), PH.H.t20(1n+Kc),
    F.at.nat(U32.inc(k), P, hP, N.le_rw_l(1n+Kc, U32.to_nat(U32.inc(k)), P, Equal.sym(Nat, U32.to_nat(U32.inc(k)), 1n+Kc, ei), hK1)),
    Equal.cong(Nat, Nat, z => PH.H.t20(z), U32.to_nat(U32.inc(k)), 1n+Kc, ei))
  # the input's bytes do not wrap
  +hx = N.le_rw_l(1n+Nat.add(A, L), 1n+Nat.add(L, A), W, Equal.cong(Nat, Nat, z => 1n+z, Nat.add(A, L), Nat.add(L, A), Z.add.comm(A, L)), N.le_trans(1n+Nat.add(A, L), 1n+PH.H.t20(P), W, hEP,
    N.le_rw_r(1n+PH.H.t20(P), PH.H.W(32n), W, Equal.sym(Nat, W, PH.H.W(32n), hW),
      N.le_rw_r(1n+PH.H.t20(P), Nat.add(PH.H.W(4n), PH.H.t20(P)), PH.H.W(32n), hP, N.le_add_l(15n, PH.H.t20(P))))))
  +hx1 = {hx : N.Le(1n+Nat.add(L, A), W)}
  # the book's cells
  +hKP = N.le_rw_l(1n+Kc, Nat.add(Kc, 1n), P, Equal.trans(Nat, 1n+Kc, 1n+Nat.add(Kc, 0n), Nat.add(Kc, 1n),
    Equal.cong(Nat, Nat, z => 1n+z, Kc, Nat.add(Kc, 0n), Equal.sym(Nat, Nat.add(Kc, 0n), Kc, N.add_zero(Kc))),
    Equal.sym(Nat, Nat.add(Kc, 1n), 1n+Nat.add(Kc, 0n), N.add_succ_r(Kc, 0n))), hK1)
  +hK2 = N.le_rw_l(2n+Kc, 1n+Nat.add(Kc, 1n), P, Equal.cong(Nat, Nat, z => 1n+z, 1n+Kc, Nat.add(Kc, 1n),
    Equal.trans(Nat, 1n+Kc, 1n+Nat.add(Kc, 0n), Nat.add(Kc, 1n),
      Equal.cong(Nat, Nat, z => 1n+z, Kc, Nat.add(Kc, 0n), Equal.sym(Nat, Nat.add(Kc, 0n), Kc, N.add_zero(Kc))),
      Equal.sym(Nat, Nat.add(Kc, 1n), 1n+Nat.add(Kc, 0n), N.add_succ_r(Kc, 0n)))), hK)
  +hs = N.le_rw_r(PH.H.t20(Nat.add(Kc, 1n)), PH.H.t20(1n+Kc), A,
    Equal.sym(Nat, A, PH.H.t20(1n+Kc), eA),
    N.le_rw_r(PH.H.t20(Nat.add(Kc, 1n)), PH.H.t20(Nat.add(Kc, 1n)), PH.H.t20(1n+Kc),
      Equal.cong(Nat, Nat, z => PH.H.t20(z), Nat.add(Kc, 1n), 1n+Kc, Z.add.comm(Kc, 1n)), N.le_refl(PH.H.t20(Nat.add(Kc, 1n)))))
  +eRC = Equal.trans(List<&2, C.Cir.Cell>, Q.RC(Kc, m, 1), Q.RC(Kc, B0(cells), 1), Q.GC(Kc, cl, 1),
    rc.wb(i, a, B0(cells), Kc, 1, 1n, {==}, A, {==}, P, hP, W, hW, hs, hKP, hx1),
    Equal.trans(List<&2, C.Cir.Cell>, Q.RC(Kc, B0(cells), 1), Q.RC(Kc, WC(cells, 1, C.Wasm.Bytes.zero{}), 1), Q.GC(Kc, cl, 1),
      Equal.cong(C.Wasm.Bytes, List<&2, C.Cir.Cell>, z => Q.RC(Kc, z, 1), B0(cells), WC(cells, 1, C.Wasm.Bytes.zero{}),
        wb.cells(cells, 1, C.Wasm.Bytes.zero{}, 1n, {==}, P, hP, W, hW, hK2)),
      Equal.trans(List<&2, C.Cir.Cell>, Q.RC(Kc, WC(cells, 1, C.Wasm.Bytes.zero{}), 1), cells, Q.GC(Kc, cl, 1),
        rc.wc(cells, 1, C.Wasm.Bytes.zero{}, 1n, {==}, P, hP, W, hW, hKP),
        Equal.sym(List<&2, C.Cir.Cell>, Q.GC(Kc, cl, 1), cells, gc.load(cells, 1, C.Cir.Cells.none{}, 1n, {==}, P, hP, W, hW, hKP)))))
  +eRC2 = {(%Equal.sym(Nat, U32.to_nat(k), Kc, eK) : {Q.RC(_, m, 1) == Q.GC(_, cl, 1) : List<&2, C.Cir.Cell>}; eRC) :
    {Q.RC(U32.to_nat(k), m, 1) == Q.GC(U32.to_nat(k), cl, 1) : List<&2, C.Cir.Cell>}}
  # the input
  +eRB = rb.wb(i, a, B0(cells), A, {==}, W, hW, hx1)
  # the machine's cells: none yet
  +FI = U32.to_nat(fst)
  +eM = {(%Equal.sym(Nat, Nat.sub(FI, FI), 0n, sub.self(FI)) : {Q.RC(_, m, fst) == Q.GC(_, cl, fst) : List<&2, C.Cir.Cell>}; {==}) :
    {Q.RC(Nat.sub(FI, FI), m, fst) == Q.GC(Nat.sub(FI, FI), cl, fst) : List<&2, C.Cir.Cell>}}
  +eCF = {(%Equal.sym(Nat, Nat.sub(FI, FI), 0n, sub.self(FI)) : Q.CF(_, FI, Q.PB(p2)); Unit{}) : Q.CF(Nat.sub(FI, FI), FI, Q.PB(p2))}
  +eA2 = Equal.trans(Nat, A, PH.H.t20(1n+Kc), PH.H.t20(1n+U32.to_nat(k)), eA,
    Equal.cong(Nat, Nat, z => PH.H.t20(1n+z), Kc, U32.to_nat(k), Equal.sym(Nat, U32.to_nat(k), Kc, eK)))
  +hK3 = N.le_rw_l(1n+Kc, 1n+U32.to_nat(k), P, Equal.cong(Nat, Nat, z => 1n+z, Kc, U32.to_nat(k), Equal.sym(Nat, U32.to_nat(k), Kc, eK)), hK1)
  +bnd = (((eA2, hK3), (hEP, hEB)), ((hEF, hFP), ((eCF, Unit{}), (hlm, hpl))))
  ((({==}, eLn), (eRC2, eRB)), ((N.le_refl(FI), eM), ({==}, bnd)))
