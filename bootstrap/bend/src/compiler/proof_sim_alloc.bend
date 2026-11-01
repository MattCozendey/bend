# compiler: the cells that the machine takes, and the output's bytes
# ==================================================================
#
# The numbers of alloc's and emit's code: (x - p) + p = x on words
# (U32.subadd), so memory.grow by need - pages gives need pages; the literal
# 214748364 is P (lit.P), and a byte b needs (b >> 16) + 1 pages
# (shrn.up). A new cell is five words of 0 (z5): it reads as Cir's new cell
# (rcell.z5), and keeps every other cell and byte (RC.z5, RB.z5); the
# relation holds after a new cell (inv.alloc) and after a byte of output
# (inv.emit).

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
import ./proof_sim_frame.bend as F

# Words
# -----

# (x - p) + p = x, with the carries of the subtraction c and of the addition
# not c
def W.subadd(+n: Nat, +x: Word(n), +p: Word(n), c: Bool) ->
  {Word.adc(n, Word.adc(n, x, p, True{}, c), p, False{}, Bool.not(c)) == x : Word(n)}:
  match n:
    case 0n:
      match x p:
        case WNil{} WNil{}:
          {==}
    case 1n+q:
      match x p c:
        case WCon{False{}, +xt} WCon{False{}, +pt} False{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{False{}, z}, Word.adc(q, Word.adc(q, xt, pt, True{}, False{}), pt, False{}, True{}), xt, W.subadd(q, xt, pt, False{}))
        case WCon{False{}, +xt} WCon{False{}, +pt} True{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{False{}, z}, Word.adc(q, Word.adc(q, xt, pt, True{}, True{}), pt, False{}, False{}), xt, W.subadd(q, xt, pt, True{}))
        case WCon{False{}, +xt} WCon{True{}, +pt} False{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{False{}, z}, Word.adc(q, Word.adc(q, xt, pt, True{}, False{}), pt, False{}, True{}), xt, W.subadd(q, xt, pt, False{}))
        case WCon{False{}, +xt} WCon{True{}, +pt} True{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{False{}, z}, Word.adc(q, Word.adc(q, xt, pt, True{}, False{}), pt, False{}, True{}), xt, W.subadd(q, xt, pt, False{}))
        case WCon{True{}, +xt} WCon{False{}, +pt} False{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{True{}, z}, Word.adc(q, Word.adc(q, xt, pt, True{}, True{}), pt, False{}, False{}), xt, W.subadd(q, xt, pt, True{}))
        case WCon{True{}, +xt} WCon{False{}, +pt} True{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{True{}, z}, Word.adc(q, Word.adc(q, xt, pt, True{}, True{}), pt, False{}, False{}), xt, W.subadd(q, xt, pt, True{}))
        case WCon{True{}, +xt} WCon{True{}, +pt} False{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{True{}, z}, Word.adc(q, Word.adc(q, xt, pt, True{}, False{}), pt, False{}, True{}), xt, W.subadd(q, xt, pt, False{}))
        case WCon{True{}, +xt} WCon{True{}, +pt} True{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{True{}, z}, Word.adc(q, Word.adc(q, xt, pt, True{}, True{}), pt, False{}, False{}), xt, W.subadd(q, xt, pt, True{}))

# (x - p) + p = x
def U32.subadd(+x: U32, +p: U32) -> {U32.add(U32.sub(x, p), p) == x : U32}:
  match x p:
    case U32{+xw} U32{+pw}:
      Equal.cong(Word(32n), U32, z => U32{z}, Word.adc(32n, Word.adc(32n, xw, pw, True{}, True{}), pw, False{}, False{}), xw, W.subadd(32n, xw, pw, True{}))

# p + (x - p) = x
def U32.addsub(+p: U32, +x: U32) -> {U32.add(p, U32.sub(x, p)) == x : U32}:
  Equal.trans(U32, U32.add(p, U32.sub(x, p)), U32.add(U32.sub(x, p), p), x, U32.add_comm(p, U32.sub(x, p)), U32.subadd(x, p))

# The literal 214748364
# ---------------------

def q4(j: Nat) -> Nat:
  match j:
    case 0n:
      0n
    case 1n+q:
      4n+q4(q)

# n bits of 0x0CCC...C with j nibbles of 12 at the bottom, its lowest bit
# first; the index is n itself, so that the word of 32 bits is a Word(32n)
def wb(n: Nat, j: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n:
      WCon{False{}, WNil{}}
    case 2n:
      WCon{False{}, WCon{False{}, WNil{}}}
    case 3n:
      WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}
    case 4n+p:
      match j:
        case 0n:
          WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, wb(p, 0n)}}}}
        case 1n+q:
          WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, wb(p, q)}}}}

def wb.val(j: Nat, +n: Nat, e: {n == 4n+q4(j) : Nat}) -> {Word.to_nat(n, wb(n, j)) == PH.H.pat(j) : Nat}:
  match j:
    case 0n:
      %Equal.sym(Nat, n, 4n, e) : {Word.to_nat(_, wb(_, 0n)) == PH.H.pat(0n) : Nat}
      {==}
    case 1n+(+q):
      %Equal.sym(Nat, n, 4n+q4(1n+q), e) : {Word.to_nat(_, wb(_, 1n+q)) == PH.H.pat(1n+q) : Nat}
      %Equal.sym(Nat, Word.to_nat(q4(1n+q), wb(q4(1n+q), q)), PH.H.pat(q), wb.val(q, q4(1n+q), {==})) :
        {Nat.double(Nat.double(1n+Nat.double(1n+Nat.double(_)))) == Nat.add(12n, N.D(4n, PH.H.pat(q))) : Nat}
      {==}

def lit.wb() -> {214748364 == U32{wb(32n, 7n)} : U32}:
  {==}

def lit.pat() -> {U32.to_nat(214748364) == PH.H.pat(7n) : Nat}:
  %Equal.sym(U32, 214748364, U32{wb(32n, 7n)}, lit.wb()) : {U32.to_nat(_) == PH.H.pat(7n) : Nat}
  Equal.trans(Nat, U32.to_nat(U32{wb(32n, 7n)}), Word.to_nat(32n, wb(32n, 7n)), PH.H.pat(7n), N.u32_to_nat(wb(32n, 7n)),
    wb.val(7n, 32n, {==}))

def succ.ne0(+y: Nat, e: {0n == 1n+y : Nat}) -> Empty:
  N.le_rw_r(1n+y, 1n+y, 0n, Equal.sym(Nat, 0n, 1n+y, e), N.le_refl(1n+y))

# 20x = 20y gives x = y
def t20.inj(+x: Nat, +y: Nat, e: {PH.H.t20(x) == PH.H.t20(y) : Nat}) -> {x == y : Nat}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, succ.ne0(19n+PH.H.t20(q), e))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, succ.ne0(19n+PH.H.t20(p), Equal.sym(Nat, 20n+PH.H.t20(p), 0n, e)))
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, z => 1n+z, p, q, t20.inj(p, q, PH.H.lcancel(20n, PH.H.t20(p), PH.H.t20(q), e)))

# 20x <= 20y gives x <= y
def t20.le.inv(+x: Nat, +y: Nat, h: N.Le(PH.H.t20(x), PH.H.t20(y))) -> N.Le(x, y):
  match x y:
    case 0n _:
      N.le_zero(y)
    case 1n+p 0n:
      Empty.absurd(N.Le(1n+p, 0n), h)
    case 1n+p 1n+q:
      t20.le.inv(p, q, h)

# P, of 2^4 + 20P = 2^32, is 214748364
def P.pat(+P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}) -> {P == PH.H.pat(7n) : Nat}:
  t20.inj(P, PH.H.pat(7n), PH.H.lcancel(PH.H.W(4n), PH.H.t20(P), PH.H.t20(PH.H.pat(7n)),
    Equal.trans(Nat, Nat.add(PH.H.W(4n), PH.H.t20(P)), PH.H.W(32n), Nat.add(PH.H.W(4n), PH.H.t20(PH.H.pat(7n))), hP,
      Equal.sym(Nat, Nat.add(PH.H.W(4n), PH.H.t20(PH.H.pat(7n))), PH.H.W(32n), PH.H.hP()))))

def lit.P(+P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}) -> {U32.to_nat(214748364) == P : Nat}:
  Equal.trans(Nat, U32.to_nat(214748364), PH.H.pat(7n), P, lit.pat(), Equal.sym(Nat, P, PH.H.pat(7n), P.pat(P, hP)))

# Shifts
# ------

# x <= 2 (x >> 1) + 1
def shr.up(x: U32) -> N.Le(U32.to_nat(x), 1n+Nat.double(U32.to_nat(U32.shr(x)))):
  match x:
    case U32{w}:
      match w:
        case WCon{False{}, +t}:
          +a = Nat.double(Word.to_nat(31n, t))
          N.le_rw_r(a, 1n+a, 1n+Nat.double(Word.to_nat(32n, Word.shr.pad(31n, t))),
            Equal.cong(Nat, Nat, v => 1n+Nat.double(v), Word.to_nat(31n, t), Word.to_nat(32n, Word.shr.pad(31n, t)),
              Equal.sym(Nat, Word.to_nat(32n, Word.shr.pad(31n, t)), Word.to_nat(31n, t), V.pad.val(31n, t))),
            N.le_succ(a, a, N.le_refl(a)))
        case WCon{True{}, +t}:
          +a = Nat.double(Word.to_nat(31n, t))
          N.le_rw_r(1n+a, 1n+a, 1n+Nat.double(Word.to_nat(32n, Word.shr.pad(31n, t))),
            Equal.cong(Nat, Nat, v => 1n+Nat.double(v), Word.to_nat(31n, t), Word.to_nat(32n, Word.shr.pad(31n, t)),
              Equal.sym(Nat, Word.to_nat(32n, Word.shr.pad(31n, t)), Word.to_nat(31n, t), V.pad.val(31n, t))),
            N.le_refl(1n+a))

# x < 2^k ((x >> k) + 1)
def shrn.up(+k: Nat, +x: U32) -> N.Le(1n+U32.to_nat(x), N.D(k, 1n+U32.to_nat(U32.shrn(x, k)))):
  match k:
    case 0n:
      N.le_refl(1n+U32.to_nat(x))
    case 1n+q:
      +y = U32.shr(x)
      +Sq = U32.to_nat(U32.shrn(y, q))
      +h = N.le_trans(1n+U32.to_nat(x), Nat.double(1n+U32.to_nat(y)), Nat.double(N.D(q, 1n+Sq)), shr.up(x),
        N.double_mono(1n+U32.to_nat(y), N.D(q, 1n+Sq), shrn.up(q, y)))
      N.le_rw_r(1n+U32.to_nat(x), Nat.double(N.D(q, 1n+Sq)), Nat.double(N.D(q, 1n+U32.to_nat(U32.shrn(x, 1n+q)))),
        Equal.cong(U32, Nat, z => Nat.double(N.D(q, 1n+U32.to_nat(z))), U32.shrn(y, q), U32.shrn(x, 1n+q),
          Equal.sym(U32, U32.shrn(x, 1n+q), U32.shrn(y, q), V.shrn.succ(x, q))), h)

# Lists
# -----

# a list, after a set of its element r, has it there
def get.set(+rg: List<&2, U32>, +r: Nat, +v: U32, h: {Nat.is_lt(r, List.length(&2, U32, rg)) == True{} : Bool}) ->
  {List.get(&2, U32, List.set(&2, U32, rg, r, v), r) == Some{v} : Maybe<&2, U32>}:
  match rg r:
    case Nil{} 0n:
      Empty.absurd({List.get(&2, U32, List.set(&2, U32, Nil{}, 0n, v), 0n) == Some{v} : Maybe<&2, U32>}, N.false_ne_true(h))
    case Nil{} 1n+q:
      Empty.absurd({List.get(&2, U32, List.set(&2, U32, Nil{}, 1n+q, v), 1n+q) == Some{v} : Maybe<&2, U32>}, N.false_ne_true(h))
    case Con{x, t} 0n:
      {==}
    case Con{x, +t} 1n+q:
      get.set(t, q, v, h)

# A new cell
# ----------

# the five words of the cell i, made 0
def z5(+m: C.Wasm.Bytes, +i: U32) -> C.Wasm.Bytes:
  C.Wasm.write32(C.Wasm.write32(C.Wasm.write32(C.Wasm.write32(C.Wasm.write32(m, Q.at.f(i, 0n), 0), Q.at.f(i, 1n), 0),
    Q.at.f(i, 2n), 0), Q.at.f(i, 3n), 0), Q.at.f(i, 4n), 0)

# the new cell reads as all zeros
def rcell.z5(+m: C.Wasm.Bytes, +i: U32, +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hi: N.Le(1n+U32.to_nat(i), P)) -> {Q.RCell(z5(m, i), i) == C.Cir.Cell.zero() : C.Cir.Cell}:
  +m1 = C.Wasm.write32(m, Q.at.f(i, 0n), 0)
  +m2 = C.Wasm.write32(m1, Q.at.f(i, 1n), 0)
  +m3 = C.Wasm.write32(m2, Q.at.f(i, 2n), 0)
  +m4 = C.Wasm.write32(m3, Q.at.f(i, 3n), 0)
  +c0 = Q.RCell(m, i)
  +c1 = C.Cir.Cell.set(0n, c0, 0)
  +c2 = C.Cir.Cell.set(1n, c1, 0)
  +c3 = C.Cir.Cell.set(2n, c2, 0)
  +c4 = C.Cir.Cell.set(3n, c3, 0)
  +c5 = C.Cir.Cell.set(4n, c4, 0)
  +t1 = F.rcell.set(m, i, 0n, 0, P, hP, W, hW, hi, {==})
  +t2 = Equal.trans(C.Cir.Cell, Q.RCell(m2, i), C.Cir.Cell.set(1n, Q.RCell(m1, i), 0), c2, F.rcell.set(m1, i, 1n, 0, P, hP, W, hW, hi, {==}),
    Equal.cong(C.Cir.Cell, C.Cir.Cell, z => C.Cir.Cell.set(1n, z, 0), Q.RCell(m1, i), c1, t1))
  +t3 = Equal.trans(C.Cir.Cell, Q.RCell(m3, i), C.Cir.Cell.set(2n, Q.RCell(m2, i), 0), c3, F.rcell.set(m2, i, 2n, 0, P, hP, W, hW, hi, {==}),
    Equal.cong(C.Cir.Cell, C.Cir.Cell, z => C.Cir.Cell.set(2n, z, 0), Q.RCell(m2, i), c2, t2))
  +t4 = Equal.trans(C.Cir.Cell, Q.RCell(m4, i), C.Cir.Cell.set(3n, Q.RCell(m3, i), 0), c4, F.rcell.set(m3, i, 3n, 0, P, hP, W, hW, hi, {==}),
    Equal.cong(C.Cir.Cell, C.Cir.Cell, z => C.Cir.Cell.set(3n, z, 0), Q.RCell(m3, i), c3, t3))
  +t5 = Equal.trans(C.Cir.Cell, Q.RCell(z5(m, i), i), C.Cir.Cell.set(4n, Q.RCell(m4, i), 0), c5, F.rcell.set(m4, i, 4n, 0, P, hP, W, hW, hi, {==}),
    Equal.cong(C.Cir.Cell, C.Cir.Cell, z => C.Cir.Cell.set(4n, z, 0), Q.RCell(m4, i), c4, t4))
  Equal.trans(C.Cir.Cell, Q.RCell(z5(m, i), i), c5, C.Cir.Cell.zero(), t5, {==})

# the new cell keeps every other cell
def rcell.z5.other(+m: C.Wasm.Bytes, +i: U32, +c: U32, +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hc: N.Le(1n+U32.to_nat(c), P), +hi: N.Le(1n+U32.to_nat(i), P),
  +d: F.Ne(U32.to_nat(c), U32.to_nat(i))) -> {Q.RCell(z5(m, i), c) == Q.RCell(m, c) : C.Cir.Cell}:
  +I = U32.to_nat(i)
  +C0 = U32.to_nat(c)
  +m1 = C.Wasm.write32(m, Q.at.f(i, 0n), 0)
  +m2 = C.Wasm.write32(m1, Q.at.f(i, 1n), 0)
  +m3 = C.Wasm.write32(m2, Q.at.f(i, 2n), 0)
  +m4 = C.Wasm.write32(m3, Q.at.f(i, 3n), 0)
  +s0 = F.rw.sep(C0, U32.to_nat(Q.at.f(i, 0n)), Nat.add(F.O(0n), PH.H.t20(I)), F.fld.nat(i, 0n, P, hP, W, hW, hi, Unit{}), F.cell.sep(C0, I, F.O(0n), Unit{}, d))
  +s1 = F.rw.sep(C0, U32.to_nat(Q.at.f(i, 1n)), Nat.add(F.O(1n), PH.H.t20(I)), F.fld.nat(i, 1n, P, hP, W, hW, hi, Unit{}), F.cell.sep(C0, I, F.O(1n), Unit{}, d))
  +s2 = F.rw.sep(C0, U32.to_nat(Q.at.f(i, 2n)), Nat.add(F.O(2n), PH.H.t20(I)), F.fld.nat(i, 2n, P, hP, W, hW, hi, Unit{}), F.cell.sep(C0, I, F.O(2n), Unit{}, d))
  +s3 = F.rw.sep(C0, U32.to_nat(Q.at.f(i, 3n)), Nat.add(F.O(3n), PH.H.t20(I)), F.fld.nat(i, 3n, P, hP, W, hW, hi, Unit{}), F.cell.sep(C0, I, F.O(3n), Unit{}, d))
  +s4 = F.rw.sep(C0, U32.to_nat(Q.at.f(i, 4n)), Nat.add(F.O(4n), PH.H.t20(I)), F.fld.nat(i, 4n, P, hP, W, hW, hi, Unit{}), F.cell.sep(C0, I, F.O(4n), Unit{}, d))
  Equal.trans(C.Cir.Cell, Q.RCell(z5(m, i), c), Q.RCell(m4, c), Q.RCell(m, c),
    F.rcell.w32(m4, Q.at.f(i, 4n), 0, c, P, hP, W, hW, hc, F.fld.room(i, 4n, P, hP, W, hW, hi, Unit{}), s4),
    Equal.trans(C.Cir.Cell, Q.RCell(m4, c), Q.RCell(m3, c), Q.RCell(m, c),
      F.rcell.w32(m3, Q.at.f(i, 3n), 0, c, P, hP, W, hW, hc, F.fld.room(i, 3n, P, hP, W, hW, hi, Unit{}), s3),
      Equal.trans(C.Cir.Cell, Q.RCell(m3, c), Q.RCell(m2, c), Q.RCell(m, c),
        F.rcell.w32(m2, Q.at.f(i, 2n), 0, c, P, hP, W, hW, hc, F.fld.room(i, 2n, P, hP, W, hW, hi, Unit{}), s2),
        Equal.trans(C.Cir.Cell, Q.RCell(m2, c), Q.RCell(m1, c), Q.RCell(m, c),
          F.rcell.w32(m1, Q.at.f(i, 1n), 0, c, P, hP, W, hW, hc, F.fld.room(i, 1n, P, hP, W, hW, hi, Unit{}), s1),
          F.rcell.w32(m, Q.at.f(i, 0n), 0, c, P, hP, W, hW, hc, F.fld.room(i, 0n, P, hP, W, hW, hi, Unit{}), s0)))))

# a word of the new cell, and q cells that end before it or start after it
def z5.sepc(+q: Nat, +Cn: Nat, +I: Nat, +T: Nat, +Oj: Nat, e: {T == Nat.add(Oj, PH.H.t20(I)) : Nat}, hO: N.Le(4n+Oj, 20n),
  s: Either<&2, &2, N.Le(PH.H.t20(Nat.add(q, Cn)), PH.H.t20(I)), N.Le(20n+PH.H.t20(I), PH.H.t20(Cn))>) ->
  Either<&2, &2, N.Le(PH.H.t20(Nat.add(q, Cn)), T), N.Le(4n+T, PH.H.t20(Cn))>:
  match s:
    case Inl{l}:
      Inl{N.le_rw_r(PH.H.t20(Nat.add(q, Cn)), Nat.add(Oj, PH.H.t20(I)), T, Equal.sym(Nat, T, Nat.add(Oj, PH.H.t20(I)), e),
        N.le_trans(PH.H.t20(Nat.add(q, Cn)), PH.H.t20(I), Nat.add(Oj, PH.H.t20(I)), l, N.le_add_l(Oj, PH.H.t20(I))))}
    case Inr{r}:
      Inr{N.le_rw_l(4n+Nat.add(Oj, PH.H.t20(I)), 4n+T, PH.H.t20(Cn),
        Equal.cong(Nat, Nat, z => 4n+z, Nat.add(Oj, PH.H.t20(I)), T, Equal.sym(Nat, T, Nat.add(Oj, PH.H.t20(I)), e)),
        N.le_trans(4n+Nat.add(Oj, PH.H.t20(I)), 20n+PH.H.t20(I), PH.H.t20(Cn), F.fend(I, Oj, hO), r))}

# the new cell keeps q cells that end before it or start after it
def RC.z5(+q: Nat, +m: C.Wasm.Bytes, +i: U32, +c: U32, +Cn: Nat, +ec: {U32.to_nat(c) == Cn : Nat},
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hi: N.Le(1n+U32.to_nat(i), P), +hcq: N.Le(Nat.add(q, Cn), P),
  +s: Either<&2, &2, N.Le(PH.H.t20(Nat.add(q, Cn)), PH.H.t20(U32.to_nat(i))), N.Le(20n+PH.H.t20(U32.to_nat(i)), PH.H.t20(Cn))>) ->
  {Q.RC(q, z5(m, i), c) == Q.RC(q, m, c) : List<&2, C.Cir.Cell>}:
  +I = U32.to_nat(i)
  +m1 = C.Wasm.write32(m, Q.at.f(i, 0n), 0)
  +m2 = C.Wasm.write32(m1, Q.at.f(i, 1n), 0)
  +m3 = C.Wasm.write32(m2, Q.at.f(i, 2n), 0)
  +m4 = C.Wasm.write32(m3, Q.at.f(i, 3n), 0)
  +A0 = Q.at.f(i, 0n)
  +A1 = Q.at.f(i, 1n)
  +A2 = Q.at.f(i, 2n)
  +A3 = Q.at.f(i, 3n)
  +A4 = Q.at.f(i, 4n)
  -V = List<&2, C.Cir.Cell>
  Equal.trans(V, Q.RC(q, z5(m, i), c), Q.RC(q, m4, c), Q.RC(q, m, c),
    F.RC.w32(q, m4, A4, 0, c, Cn, ec, P, hP, W, hW, F.fld.room(i, 4n, P, hP, W, hW, hi, Unit{}), hcq,
      z5.sepc(q, Cn, I, U32.to_nat(A4), F.O(4n), F.fld.nat(i, 4n, P, hP, W, hW, hi, Unit{}), Unit{}, s)),
    Equal.trans(V, Q.RC(q, m4, c), Q.RC(q, m3, c), Q.RC(q, m, c),
      F.RC.w32(q, m3, A3, 0, c, Cn, ec, P, hP, W, hW, F.fld.room(i, 3n, P, hP, W, hW, hi, Unit{}), hcq,
        z5.sepc(q, Cn, I, U32.to_nat(A3), F.O(3n), F.fld.nat(i, 3n, P, hP, W, hW, hi, Unit{}), Unit{}, s)),
      Equal.trans(V, Q.RC(q, m3, c), Q.RC(q, m2, c), Q.RC(q, m, c),
        F.RC.w32(q, m2, A2, 0, c, Cn, ec, P, hP, W, hW, F.fld.room(i, 2n, P, hP, W, hW, hi, Unit{}), hcq,
          z5.sepc(q, Cn, I, U32.to_nat(A2), F.O(2n), F.fld.nat(i, 2n, P, hP, W, hW, hi, Unit{}), Unit{}, s)),
        Equal.trans(V, Q.RC(q, m2, c), Q.RC(q, m1, c), Q.RC(q, m, c),
          F.RC.w32(q, m1, A1, 0, c, Cn, ec, P, hP, W, hW, F.fld.room(i, 1n, P, hP, W, hW, hi, Unit{}), hcq,
            z5.sepc(q, Cn, I, U32.to_nat(A1), F.O(1n), F.fld.nat(i, 1n, P, hP, W, hW, hi, Unit{}), Unit{}, s)),
          F.RC.w32(q, m, A0, 0, c, Cn, ec, P, hP, W, hW, F.fld.room(i, 0n, P, hP, W, hW, hi, Unit{}), hcq,
            z5.sepc(q, Cn, I, U32.to_nat(A0), F.O(0n), F.fld.nat(i, 0n, P, hP, W, hW, hi, Unit{}), Unit{}, s))))))

# a word of the new cell, and q bytes that end before it or start after it
def z5.sepb(+q: Nat, +Xn: Nat, +I: Nat, +T: Nat, +Oj: Nat, e: {T == Nat.add(Oj, PH.H.t20(I)) : Nat}, hO: N.Le(4n+Oj, 20n),
  s: Either<&2, &2, N.Le(Nat.add(q, Xn), PH.H.t20(I)), N.Le(20n+PH.H.t20(I), Xn)>) ->
  Either<&2, &2, N.Le(Nat.add(q, Xn), T), N.Le(4n+T, Xn)>:
  match s:
    case Inl{l}:
      Inl{N.le_rw_r(Nat.add(q, Xn), Nat.add(Oj, PH.H.t20(I)), T, Equal.sym(Nat, T, Nat.add(Oj, PH.H.t20(I)), e),
        N.le_trans(Nat.add(q, Xn), PH.H.t20(I), Nat.add(Oj, PH.H.t20(I)), l, N.le_add_l(Oj, PH.H.t20(I))))}
    case Inr{r}:
      Inr{N.le_rw_l(4n+Nat.add(Oj, PH.H.t20(I)), 4n+T, Xn,
        Equal.cong(Nat, Nat, z => 4n+z, Nat.add(Oj, PH.H.t20(I)), T, Equal.sym(Nat, T, Nat.add(Oj, PH.H.t20(I)), e)),
        N.le_trans(4n+Nat.add(Oj, PH.H.t20(I)), 20n+PH.H.t20(I), Xn, F.fend(I, Oj, hO), r))}

# the new cell keeps q bytes that end before it or start after it
def RB.z5(+q: Nat, +m: C.Wasm.Bytes, +i: U32, +x: U32, +Xn: Nat, +ex: {U32.to_nat(x) == Xn : Nat},
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hi: N.Le(1n+U32.to_nat(i), P), +hx: N.Le(1n+Nat.add(q, Xn), W),
  +s: Either<&2, &2, N.Le(Nat.add(q, Xn), PH.H.t20(U32.to_nat(i))), N.Le(20n+PH.H.t20(U32.to_nat(i)), Xn)>) ->
  {Q.RB(q, z5(m, i), x) == Q.RB(q, m, x) : List<&2, U32>}:
  +I = U32.to_nat(i)
  +m1 = C.Wasm.write32(m, Q.at.f(i, 0n), 0)
  +m2 = C.Wasm.write32(m1, Q.at.f(i, 1n), 0)
  +m3 = C.Wasm.write32(m2, Q.at.f(i, 2n), 0)
  +m4 = C.Wasm.write32(m3, Q.at.f(i, 3n), 0)
  +A0 = Q.at.f(i, 0n)
  +A1 = Q.at.f(i, 1n)
  +A2 = Q.at.f(i, 2n)
  +A3 = Q.at.f(i, 3n)
  +A4 = Q.at.f(i, 4n)
  -V = List<&2, U32>
  Equal.trans(V, Q.RB(q, z5(m, i), x), Q.RB(q, m4, x), Q.RB(q, m, x),
    F.RB.w32(q, m4, A4, 0, x, Xn, ex, W, hW, F.fld.room(i, 4n, P, hP, W, hW, hi, Unit{}), hx,
      z5.sepb(q, Xn, I, U32.to_nat(A4), F.O(4n), F.fld.nat(i, 4n, P, hP, W, hW, hi, Unit{}), Unit{}, s)),
    Equal.trans(V, Q.RB(q, m4, x), Q.RB(q, m3, x), Q.RB(q, m, x),
      F.RB.w32(q, m3, A3, 0, x, Xn, ex, W, hW, F.fld.room(i, 3n, P, hP, W, hW, hi, Unit{}), hx,
        z5.sepb(q, Xn, I, U32.to_nat(A3), F.O(3n), F.fld.nat(i, 3n, P, hP, W, hW, hi, Unit{}), Unit{}, s)),
      Equal.trans(V, Q.RB(q, m3, x), Q.RB(q, m2, x), Q.RB(q, m, x),
        F.RB.w32(q, m2, A2, 0, x, Xn, ex, W, hW, F.fld.room(i, 2n, P, hP, W, hW, hi, Unit{}), hx,
          z5.sepb(q, Xn, I, U32.to_nat(A2), F.O(2n), F.fld.nat(i, 2n, P, hP, W, hW, hi, Unit{}), Unit{}, s)),
        Equal.trans(V, Q.RB(q, m2, x), Q.RB(q, m1, x), Q.RB(q, m, x),
          F.RB.w32(q, m1, A1, 0, x, Xn, ex, W, hW, F.fld.room(i, 1n, P, hP, W, hW, hi, Unit{}), hx,
            z5.sepb(q, Xn, I, U32.to_nat(A1), F.O(1n), F.fld.nat(i, 1n, P, hP, W, hW, hi, Unit{}), Unit{}, s)),
          F.RB.w32(q, m, A0, 0, x, Xn, ex, W, hW, F.fld.room(i, 0n, P, hP, W, hW, hi, Unit{}), hx,
            z5.sepb(q, Xn, I, U32.to_nat(A0), F.O(0n), F.fld.nat(i, 0n, P, hP, W, hW, hi, Unit{}), Unit{}, s))))))

# Cir's q cells from c, all before i, do not change when i is set
def GC.other(q: Nat, +cl: C.Cir.Cells, +i: U32, +z: C.Cir.Cell, +c: U32, +Cn: Nat, +ec: {U32.to_nat(c) == Cn : Nat},
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hcq: N.Le(Nat.add(q, Cn), P), +h: N.Le(Nat.add(q, Cn), U32.to_nat(i))) ->
  {Q.GC(q, C.Cir.Cells.set(cl, i, z), c) == Q.GC(q, cl, c) : List<&2, C.Cir.Cell>}:
  match q:
    case 0n:
      {==}
    case 1n+(+p):
      +hc = N.le_rw_l(1n+Cn, 1n+U32.to_nat(c), U32.to_nat(i), Equal.cong(Nat, Nat, x => 1n+x, Cn, U32.to_nat(c), Equal.sym(Nat, U32.to_nat(c), Cn, ec)),
        N.le_trans(1n+Cn, 1n+Nat.add(p, Cn), U32.to_nat(i), N.le_add_l(p, Cn), h))
      F.cons.cong(C.Cir.Cell, C.Cir.Cells.get(C.Cir.Cells.set(cl, i, z), c), C.Cir.Cells.get(cl, c),
        Q.GC(p, C.Cir.Cells.set(cl, i, z), U32.inc(c)), Q.GC(p, cl, U32.inc(c)),
        F.cells.other(cl, i, c, z, F.ne.nat(c, i, Inl{hc})),
        GC.other(p, cl, i, z, U32.inc(c), 1n+Cn, F.rc.inc(c, Cn, ec, p, P, hP, W, hW, hcq), P, hP, W, hW, F.rc.hcq(p, Cn, P, hcq),
          N.le_rw_l(1n+Nat.add(p, Cn), Nat.add(p, 1n+Cn), U32.to_nat(i), Equal.sym(Nat, Nat.add(p, 1n+Cn), 1n+Nat.add(p, Cn), N.add_succ_r(p, Cn)), h)))

# c, of the number of i, is i
def u32.of.nat(+c: U32, +i: U32, e: {U32.to_nat(c) == U32.to_nat(i) : Nat}) -> {c == i : U32}:
  Equal.trans(U32, c, U32.from_nat(U32.to_nat(c)), i, Equal.sym(U32, U32.from_nat(U32.to_nat(c)), c, Z.from.to(c)),
    Equal.trans(U32, U32.from_nat(U32.to_nat(c)), U32.from_nat(U32.to_nat(i)), i,
      Equal.cong(Nat, U32, z => U32.from_nat(z), U32.to_nat(c), U32.to_nat(i), e), Z.from.to(i)))

# the q cells from c, then the new cell i just after them, read as Cir's
def RC.alloc(q: Nat, +m: C.Wasm.Bytes, +cl: C.Cir.Cells, +c: U32, +Cn: Nat, +ec: {U32.to_nat(c) == Cn : Nat},
  +i: U32, +ei: {U32.to_nat(i) == Nat.add(q, Cn) : Nat},
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hi: N.Le(1n+U32.to_nat(i), P), +old: {Q.RC(q, m, c) == Q.GC(q, cl, c) : List<&2, C.Cir.Cell>}) ->
  {Q.RC(1n+q, z5(m, i), c) == Q.GC(1n+q, C.Cir.Cells.set(cl, i, C.Cir.Cell.zero()), c) : List<&2, C.Cir.Cell>}:
  match q:
    case 0n:
      +cl2 = C.Cir.Cells.set(cl, i, C.Cir.Cell.zero())
      +eci = u32.of.nat(c, i, Equal.trans(Nat, U32.to_nat(c), Cn, U32.to_nat(i), ec, Equal.sym(Nat, U32.to_nat(i), Cn, ei)))
      %Equal.sym(U32, c, i, eci) : {Con{Q.RCell(z5(m, i), _), Nil{}} == Con{C.Cir.Cells.get(cl2, _), Nil{}} : List<&2, C.Cir.Cell>}
      F.cons.cong(C.Cir.Cell, Q.RCell(z5(m, i), i), C.Cir.Cells.get(cl2, i), Nil{}, Nil{},
        Equal.trans(C.Cir.Cell, Q.RCell(z5(m, i), i), C.Cir.Cell.zero(), C.Cir.Cells.get(cl2, i), rcell.z5(m, i, P, hP, W, hW, hi),
          Equal.sym(C.Cir.Cell, C.Cir.Cells.get(cl2, i), C.Cir.Cell.zero(), F.cells.same(cl, i, C.Cir.Cell.zero()))), {==})
    case 1n+(+p):
      +cl2 = C.Cir.Cells.set(cl, i, C.Cir.Cell.zero())
      +m5 = z5(m, i)
      +I = U32.to_nat(i)
      +hci = N.le_rw_l(1n+Cn, 1n+U32.to_nat(c), I, Equal.cong(Nat, Nat, x => 1n+x, Cn, U32.to_nat(c), Equal.sym(Nat, U32.to_nat(c), Cn, ec)),
        N.le_rw_r(1n+Cn, 1n+Nat.add(p, Cn), I, Equal.sym(Nat, I, 1n+Nat.add(p, Cn), ei), N.le_add_l(p, Cn)))
      +hc = N.le_trans(1n+U32.to_nat(c), I, P, hci, N.weaken(I, P, hi))
      +hcq = N.le_rw_l(I, 1n+Nat.add(p, Cn), P, ei, N.weaken(I, P, hi))
      +oldh = Equal.cong(List<&2, C.Cir.Cell>, C.Cir.Cell, l => Q.hd.cell(l), Q.RC(1n+p, m, c), Q.GC(1n+p, cl, c), old)
      +oldt = Equal.cong(List<&2, C.Cir.Cell>, List<&2, C.Cir.Cell>, l => Q.tl.cell(l), Q.RC(1n+p, m, c), Q.GC(1n+p, cl, c), old)
      F.cons.cong(C.Cir.Cell, Q.RCell(m5, c), C.Cir.Cells.get(cl2, c), Q.RC(1n+p, m5, U32.inc(c)), Q.GC(1n+p, cl2, U32.inc(c)),
        Equal.trans(C.Cir.Cell, Q.RCell(m5, c), Q.RCell(m, c), C.Cir.Cells.get(cl2, c), rcell.z5.other(m, i, c, P, hP, W, hW, hc, hi, Inl{hci}),
          Equal.trans(C.Cir.Cell, Q.RCell(m, c), C.Cir.Cells.get(cl, c), C.Cir.Cells.get(cl2, c), oldh,
            Equal.sym(C.Cir.Cell, C.Cir.Cells.get(cl2, c), C.Cir.Cells.get(cl, c), F.cells.other(cl, i, c, C.Cir.Cell.zero(), F.ne.nat(c, i, Inl{hci}))))),
        RC.alloc(p, m, cl, U32.inc(c), 1n+Cn, F.rc.inc(c, Cn, ec, p, P, hP, W, hW, hcq), i,
          Equal.trans(Nat, I, 1n+Nat.add(p, Cn), Nat.add(p, 1n+Cn), ei, Equal.sym(Nat, Nat.add(p, 1n+Cn), 1n+Nat.add(p, Cn), N.add_succ_r(p, Cn))),
          P, hP, W, hW, hi, oldt))

# (1 + x) - f = 1 + (x - f), for f <= x
def sub.succ.l(+x: Nat, +f: Nat, h: N.Le(f, x)) -> {Nat.sub(1n+x, f) == 1n+Nat.sub(x, f) : Nat}:
  match x f:
    case _ 0n:
      Equal.cong(Nat, Nat, z => 1n+z, x, Nat.sub(x, 0n), Equal.sym(Nat, Nat.sub(x, 0n), x, Q.sub0(x)))
    case 0n 1n+q:
      Empty.absurd({Nat.sub(1n, 1n+q) == 1n+Nat.sub(0n, 1n+q) : Nat}, h)
    case 1n+p 1n+q:
      sub.succ.l(p, q, h)
