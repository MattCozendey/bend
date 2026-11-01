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

# the relation after a new cell, the cell next: the memory may have grown to
# p2 pages, which hold the cell
def inv.alloc(+P: Nat, +G: Nat, +a: U32, +n: U32, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +p2: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32, +m: C.Wasm.Bytes, +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +hG: {N.D(16n, G) == W : Nat},
  +hon: {U32.to_nat(on) == 0n : Nat}, +hnx: N.Le(1n+U32.to_nat(nx), P),
  +hroom: N.Le(PH.H.t20(1n+U32.to_nat(nx)), Q.PB(p2)), +hp: N.Le(U32.to_nat(pg), U32.to_nat(p2)),
  +hpl: N.Le(U32.to_nat(p2), U32.to_nat(lm))) ->
  Q.Inv(P, G, a, n, C.Cir.Cells.set(cl, nx, C.Cir.Cell.zero()), U32.inc(nx), fi, im, p2, lm, inp, ou, on, z5(m, nx)):
  +hB = Q.inv.bounds(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)
  +K = U32.to_nat(im)
  +NX = U32.to_nat(nx)
  +FI = U32.to_nat(fi)
  +A = U32.to_nat(a)
  +L = List.length(&2, U32, inp)
  +cl2 = C.Cir.Cells.set(cl, nx, C.Cir.Cell.zero())
  +m5 = z5(m, nx)
  +fle = Q.inv.fle(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)
  +enx1 = F.inc.nat(nx, W, hW, N.le_trans(2n+NX, 36n+PH.H.t20(NX), W, N.add_mono(2n, 36n, NX, PH.H.t20(NX), Unit{}, PH.H.le_t20(NX)),
    F.cell.room(NX, P, hP, W, hW, hnx)))
  +hEF = N.le_trans(Nat.add(A, L), PH.H.t20(FI), PH.H.t20(NX), Q.b.efi(P, G, a, nx, fi, im, pg, lm, inp, on, hB), PH.H.t20_mono(FI, NX, fle))
  +h1K = N.le_rw_l(A, PH.H.t20(1n+K), PH.H.t20(NX), Q.b.a(P, G, a, nx, fi, im, pg, lm, inp, on, hB),
    N.le_trans(A, Nat.add(A, L), PH.H.t20(NX), N.le_add_r(A, L), hEF))
  +eK1 = Equal.sym(Nat, Nat.add(K, 1n), 1n+K, I.add.one(K))
  +hcb = N.le_rw_l(1n+K, Nat.add(K, 1n), P, eK1, Q.b.k(P, G, a, nx, fi, im, pg, lm, inp, on, hB))
  +hbx = N.le_rw_l(1n+K, Nat.add(K, 1n), NX, eK1, t20.le.inv(1n+K, NX, h1K))
  +hbs = N.le_rw_l(PH.H.t20(1n+K), PH.H.t20(Nat.add(K, 1n)), PH.H.t20(NX), Equal.cong(Nat, Nat, z => PH.H.t20(z), 1n+K, Nat.add(K, 1n), eK1), h1K)
  +book = Equal.trans(List<&2, C.Cir.Cell>, Q.RC(K, m5, 1), Q.RC(K, m, 1), Q.GC(K, cl2, 1),
    RC.z5(K, m, nx, 1, 1n, {==}, P, hP, W, hW, hnx, hcb, Inl{hbs}),
    Equal.trans(List<&2, C.Cir.Cell>, Q.RC(K, m, 1), Q.GC(K, cl, 1), Q.GC(K, cl2, 1),
      Q.inv.book(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI),
      Equal.sym(List<&2, C.Cir.Cell>, Q.GC(K, cl2, 1), Q.GC(K, cl, 1), GC.other(K, cl, nx, C.Cir.Cell.zero(), 1, 1n, {==}, P, hP, W, hW, hcb, hbx))))
  +inp2 = Equal.trans(List<&2, U32>, Q.RB(L, m5, a), Q.RB(L, m, a), inp,
    RB.z5(L, m, nx, a, A, {==}, P, hP, W, hW, hnx, F.b.inw(P, G, a, nx, fi, im, pg, lm, inp, on, hP, W, hW, hB),
      Inl{N.le_rw_l(Nat.add(A, L), Nat.add(L, A), PH.H.t20(NX), Z.add.comm(A, L), hEF)}),
    Q.inv.inp(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI))
  +fle2 = {(%Equal.sym(Nat, U32.to_nat(U32.inc(nx)), 1n+NX, enx1) : N.Le(FI, _); N.le_succ(FI, NX, fle)) : N.Le(FI, U32.to_nat(U32.inc(nx)))}
  +esub = sub.succ.l(NX, FI, fle)
  +mach0 = RC.alloc(Nat.sub(NX, FI), m, cl, fi, FI, {==}, nx, Equal.sym(Nat, Nat.add(Nat.sub(NX, FI), FI), NX, Z.sub.add(NX, FI, fle)),
    P, hP, W, hW, hnx, Q.inv.mach(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI))
  +mach1 = {(%Equal.sym(Nat, Nat.sub(1n+NX, FI), 1n+Nat.sub(NX, FI), esub) :
      {Q.RC(_, m5, fi) == Q.GC(_, cl2, fi) : List<&2, C.Cir.Cell>}; mach0) :
    {Q.RC(Nat.sub(1n+NX, FI), m5, fi) == Q.GC(Nat.sub(1n+NX, FI), cl2, fi) : List<&2, C.Cir.Cell>}}
  +mach2 = {(%Equal.sym(Nat, U32.to_nat(U32.inc(nx)), 1n+NX, enx1) :
      {Q.RC(Nat.sub(_, FI), m5, fi) == Q.GC(Nat.sub(_, FI), cl2, fi) : List<&2, C.Cir.Cell>}; mach1) :
    {Q.RC(Nat.sub(U32.to_nat(U32.inc(nx)), FI), m5, fi) == Q.GC(Nat.sub(U32.to_nat(U32.inc(nx)), FI), cl2, fi) : List<&2, C.Cir.Cell>}}
  +out0 = {(%hon : {Q.RB(_, m, C.Cir.at(nx)) == List.reverse(&2, U32, ou) : List<&2, U32>};
      Q.inv.out(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)) :
    {Q.RB(0n, m, C.Cir.at(nx)) == List.reverse(&2, U32, ou) : List<&2, U32>}}
  +out2 = {(%Equal.sym(Nat, U32.to_nat(on), 0n, hon) : {Q.RB(_, m5, C.Cir.at(U32.inc(nx))) == List.reverse(&2, U32, ou) : List<&2, U32>}; out0) :
    {Q.RB(U32.to_nat(on), m5, C.Cir.at(U32.inc(nx))) == List.reverse(&2, U32, ou) : List<&2, U32>}}
  +cf1 = {(%Equal.sym(Nat, Nat.sub(1n+NX, FI), 1n+Nat.sub(NX, FI), esub) : Q.CF(_, 1n+NX, Q.PB(p2)); hroom) : Q.CF(Nat.sub(1n+NX, FI), 1n+NX, Q.PB(p2))}
  +cf2 = {(%Equal.sym(Nat, U32.to_nat(U32.inc(nx)), 1n+NX, enx1) : Q.CF(Nat.sub(_, FI), _, Q.PB(p2)); cf1) :
    Q.CF(Nat.sub(U32.to_nat(U32.inc(nx)), FI), U32.to_nat(U32.inc(nx)), Q.PB(p2))}
  +of2 = {(%Equal.sym(Nat, U32.to_nat(on), 0n, hon) : Q.OF(_, U32.to_nat(U32.inc(nx)), Q.PB(p2)); Unit{}) : Q.OF(U32.to_nat(on), U32.to_nat(U32.inc(nx)), Q.PB(p2))}
  +nxP = {(%Equal.sym(Nat, U32.to_nat(U32.inc(nx)), 1n+NX, enx1) : N.Le(_, P); hnx) : N.Le(U32.to_nat(U32.inc(nx)), P)}
  +ep2 = N.le_trans(Nat.add(A, L), Q.PB(pg), Q.PB(p2), Q.b.epb(P, G, a, nx, fi, im, pg, lm, inp, on, hB), M.D_mono(16n, U32.to_nat(pg), U32.to_nat(p2), hp))
  +hB2 = {(((Q.b.a(P, G, a, nx, fi, im, pg, lm, inp, on, hB), Q.b.k(P, G, a, nx, fi, im, pg, lm, inp, on, hB)),
      (Q.b.e20(P, G, a, nx, fi, im, pg, lm, inp, on, hB), ep2)),
     ((Q.b.efi(P, G, a, nx, fi, im, pg, lm, inp, on, hB), nxP), ((cf2, of2), (Q.b.lm(P, G, a, nx, fi, im, pg, lm, inp, on, hB), hpl)))) :
    Q.Bounds(P, G, a, U32.inc(nx), fi, im, p2, lm, inp, on)}
  (((Q.inv.ea(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI), Q.q.size(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)), (book, inp2)),
   ((fle2, mach2), (out2, hB2)))

# Steps
# -----

# the branch out of run from j labels inside it: run gives its status
def xs.exit(+j: Nat, +ls2: List<&2, C.Wasm.Label>,
  +hj: {List.drop(&2, C.Wasm.Label, ls2, j) == [C.Wasm.Label{None{}, [C.Wasm.Instr.local_get{2}], 0n}] : List<&2, C.Wasm.Label>},
  +ej: {U32.to_nat(U32.from_nat(j)) == j : Nat}, +L: List<&2, U32>, +M: C.Wasm.Memory) ->
  {PH.H.steps(3n, Q.Cfg([C.Wasm.Instr.br{U32.from_nat(j)}], ls2, [], L, M)) ==
    C.Wasm.Step.done{[Maybe.default(&2, U32, List.get(&2, U32, L, 2n), 0)], M} : C.Wasm.Step}:
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(j)), j, ej) :
    {PH.H.steps(2n, C.Wasm.step.br(List.drop(&2, C.Wasm.Label, ls2, _), 1n, [], L, M)) ==
      C.Wasm.Step.done{[Maybe.default(&2, U32, List.get(&2, U32, L, 2n), 0)], M} : C.Wasm.Step}
  %Equal.sym(List<&2, C.Wasm.Label>, List.drop(&2, C.Wasm.Label, ls2, j), [C.Wasm.Label{None{}, [C.Wasm.Instr.local_get{2}], 0n}], hj) :
    {PH.H.steps(2n, C.Wasm.step.br(_, 1n, [], L, M)) ==
      C.Wasm.Step.done{[Maybe.default(&2, U32, List.get(&2, U32, L, 2n), 0)], M} : C.Wasm.Step}
  {==}

# the code of an unless, whose condition gave v: on, when v is not 0
def un.ok(+v: U32, ez: {U32.is_zero(v) == False{} : Bool}, +d: Nat, +acc: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>,
  +L: List<&2, U32>, +M: C.Wasm.Memory) ->
  {PH.H.steps(1n, Q.Cfg(Con{C.Wasm.Instr.br_if{0}, [C.Cir.code.exit(1, 1n+d)]}, Con{C.Wasm.Label{None{}, acc, 0n}, ls}, [v], L, M)) ==
    Q.Cfg(acc, ls, [], L, M) : C.Wasm.Step}:
  %Equal.sym(Bool, U32.is_zero(v), False{}, ez) :
    {C.Wasm.step.br_if.if(_, 0, [C.Cir.code.exit(1, 1n+d)], Con{C.Wasm.Label{None{}, acc, 0n}, ls}, 1n, [], L, M) == Q.Cfg(acc, ls, [], L, M) : C.Wasm.Step}
  {==}

# the code of an unless, whose condition gave 0: run ends with the status 1
def un.fail(+v: U32, ez: {U32.is_zero(v) == True{} : Bool}, +d: Nat, +acc: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>,
  +hL: {List.drop(&2, C.Wasm.Label, ls, d) == [C.Wasm.Label{None{}, [C.Wasm.Instr.local_get{2}], 0n}] : List<&2, C.Wasm.Label>},
  +ej: {U32.to_nat(U32.from_nat(2n+d)) == 2n+d : Nat},
  +a: U32, +n: U32, +s: U32, +nx: U32, +on: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +M: C.Wasm.Memory) ->
  {PH.H.steps(7n, Q.Cfg(Con{C.Wasm.Instr.br_if{0}, [C.Cir.code.exit(1, 1n+d)]}, Con{C.Wasm.Label{None{}, acc, 0n}, ls}, [v],
    Q.Loc(a, n, s, nx, on, t, nd, ad, rg), M)) == C.Wasm.Step.done{[1], M} : C.Wasm.Step}:
  +LU = {Con{C.Wasm.Label{None{}, acc, 0n}, ls} : List<&2, C.Wasm.Label>}
  +LX = {Con{C.Wasm.Label{None{}, [], 0n}, LU} : List<&2, C.Wasm.Label>}
  +L1 = Q.Loc(a, n, 1, nx, on, t, nd, ad, rg)
  %Equal.sym(Bool, U32.is_zero(v), True{}, ez) :
    {PH.H.steps(6n, C.Wasm.step.br_if.if(_, 0, [C.Cir.code.exit(1, 1n+d)], LU, 1n, [], Q.Loc(a, n, s, nx, on, t, nd, ad, rg), M)) ==
      C.Wasm.Step.done{[1], M} : C.Wasm.Step}
  S.steps.then(3n, 3n, Q.Cfg([C.Cir.code.exit(1, 1n+d)], LU, [], Q.Loc(a, n, s, nx, on, t, nd, ad, rg), M),
    Q.Cfg([C.Wasm.Instr.br{U32.from_nat(2n+d)}], LX, [], L1, M), C.Wasm.Step.done{[1], M}, {==},
    xs.exit(2n+d, LX, hL, ej, L1, M))

# a >= b when b <= a
def ge.rel(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(y, x)) -> {Cmp.is_ge(c) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(x, N.le_trans(1n+x, y, x, r, h)))
    case EQ{}:
      {==}
    case GT{}:
      {==}

def ge.of(+a: U32, +b: U32, h: N.Le(U32.to_nat(b), U32.to_nat(a))) -> {U32.is_ge(a, b) == True{} : Bool}:
  ge.rel(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), h)

# a word of a cell, from its first byte, ends within it
def word.in(+T: Nat, +oj: Nat, h: N.Le(4n+oj, 20n)) -> N.Le(Nat.add(Nat.add(T, oj), 4n), 20n+T):
  N.le_rw_l(Nat.add(4n+oj, T), Nat.add(Nat.add(T, oj), 4n), 20n+T,
    Equal.trans(Nat, Nat.add(4n+oj, T), 4n+Nat.add(T, oj), Nat.add(Nat.add(T, oj), 4n),
      Equal.cong(Nat, Nat, z => 4n+z, Nat.add(oj, T), Nat.add(T, oj), Z.add.comm(oj, T)),
      Equal.sym(Nat, Nat.add(Nat.add(T, oj), 4n), 4n+Nat.add(T, oj), Z.add.comm(Nat.add(T, oj), 4n))),
    Z.le.add_r(4n+oj, 20n, T, h))

# the memory of p pages, at most the limit, is below W
def pb2.lt(+p: U32, +lm: U32, +G: Nat, +W: Nat, +hG: {N.D(16n, G) == W : Nat}, hpl: N.Le(U32.to_nat(p), U32.to_nat(lm)),
  hlm: N.Le(1n+U32.to_nat(lm), G)) -> N.Le(1n+Q.PB(p), W):
  +PG = U32.to_nat(p)
  N.le_trans(1n+N.D(16n, PG), N.D(16n, 1n+PG), W, Z.D.succ(16n, PG),
    N.le_rw_r(N.D(16n, 1n+PG), N.D(16n, G), W, hG, M.D_mono(16n, 1n+PG, G, N.le_trans(1n+PG, 1n+U32.to_nat(lm), G, hpl, hlm))))

# word j of the cell at the first byte A0 = 20i, inside the memory of p pages
def zin(+p: U32, +A0: U32, +o: U32, +T: Nat, +eT: {U32.to_nat(A0) == T : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +ho: N.Le(4n+U32.to_nat(o), 20n), +hroom: N.Le(20n+T, Q.PB(p)), +hb: N.Le(1n+Q.PB(p), W)) ->
  {C.Wasm.inside(p, A0, o, 4) == True{} : Bool}:
  Z.inside.ok(p, A0, o, 4, W, hW, Unit{},
    N.le_rw_l(Nat.add(Nat.add(T, U32.to_nat(o)), 4n), Nat.add(Nat.add(U32.to_nat(A0), U32.to_nat(o)), U32.to_nat(4)), Q.PB(p),
      Equal.cong(Nat, Nat, z => Nat.add(Nat.add(z, U32.to_nat(o)), 4n), T, U32.to_nat(A0), Equal.sym(Nat, U32.to_nat(A0), T, eT)),
      N.le_trans(Nat.add(Nat.add(T, U32.to_nat(o)), 4n), 20n+T, Q.PB(p), word.in(T, U32.to_nat(o), ho), hroom)), hb)

# the five stores of 0 into the cell at the first byte 20i
def zero.steps(+i: U32, +K: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +a: U32, +n: U32, +s: U32, +nx: U32, +on: U32,
  +t: U32, +nd: U32, +rg: List<&2, U32>, +p: U32, +lm: U32, +m: C.Wasm.Bytes, +T: Nat, +eT: {U32.to_nat(C.Cir.at(i)) == T : Nat},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hroom: N.Le(20n+T, Q.PB(p)), +hb: N.Le(1n+Q.PB(p), W)) ->
  {PH.H.steps(15n, Q.Cfg(C.Cir.code.zero(K), ls, [], Q.Loc(a, n, s, nx, on, t, nd, C.Cir.at(i), rg), C.Wasm.Memory{p, lm, m})) ==
    Q.Cfg(K, ls, [], Q.Loc(a, n, s, nx, on, t, nd, C.Cir.at(i), rg), C.Wasm.Memory{p, lm, z5(m, i)}) : C.Wasm.Step}:
  +A0 = C.Cir.at(i)
  +L = Q.Loc(a, n, s, nx, on, t, nd, A0, rg)
  +m1 = C.Wasm.write32(m, Q.at.f(i, 0n), 0)
  +m2 = C.Wasm.write32(m1, Q.at.f(i, 1n), 0)
  +m3 = C.Wasm.write32(m2, Q.at.f(i, 2n), 0)
  +m4 = C.Wasm.write32(m3, Q.at.f(i, 3n), 0)
  +g = {C.Wasm.Instr.local_get{7} : C.Wasm.Instr}
  +z = {C.Wasm.Instr.const{0} : C.Wasm.Instr}
  +R4 = {Con{g, Con{z, Con{C.Wasm.Instr.store{16}, K}}} : List<&2, C.Wasm.Instr>}
  +R3 = {Con{g, Con{z, Con{C.Wasm.Instr.store{12}, R4}}} : List<&2, C.Wasm.Instr>}
  +R2 = {Con{g, Con{z, Con{C.Wasm.Instr.store{8}, R3}}} : List<&2, C.Wasm.Instr>}
  +R1 = {Con{g, Con{z, Con{C.Wasm.Instr.store{4}, R2}}} : List<&2, C.Wasm.Instr>}
  +S0 = Q.Cfg(Con{C.Wasm.Instr.store{0}, R1}, ls, [0, A0], L, C.Wasm.Memory{p, lm, m})
  +S1 = Q.Cfg(Con{C.Wasm.Instr.store{4}, R2}, ls, [0, A0], L, C.Wasm.Memory{p, lm, m1})
  +S2 = Q.Cfg(Con{C.Wasm.Instr.store{8}, R3}, ls, [0, A0], L, C.Wasm.Memory{p, lm, m2})
  +S3 = Q.Cfg(Con{C.Wasm.Instr.store{12}, R4}, ls, [0, A0], L, C.Wasm.Memory{p, lm, m3})
  +S4 = Q.Cfg(Con{C.Wasm.Instr.store{16}, K}, ls, [0, A0], L, C.Wasm.Memory{p, lm, m4})
  +B0 = Q.Cfg(C.Cir.code.zero(K), ls, [], L, C.Wasm.Memory{p, lm, m})
  +B1 = Q.Cfg(R1, ls, [], L, C.Wasm.Memory{p, lm, m1})
  +B2 = Q.Cfg(R2, ls, [], L, C.Wasm.Memory{p, lm, m2})
  +B3 = Q.Cfg(R3, ls, [], L, C.Wasm.Memory{p, lm, m3})
  +B4 = Q.Cfg(R4, ls, [], L, C.Wasm.Memory{p, lm, m4})
  +E = Q.Cfg(K, ls, [], L, C.Wasm.Memory{p, lm, z5(m, i)})
  +x4 = S.steps.then(2n, 1n, B4, S4, E, {==}, F.store.step(16, A0, 0, K, ls, [], L, p, lm, m4, zin(p, A0, 16, T, eT, W, hW, Unit{}, hroom, hb)))
  +x3 = S.steps.then(2n, 1n, B3, S3, B4, {==}, F.store.step(12, A0, 0, R4, ls, [], L, p, lm, m3, zin(p, A0, 12, T, eT, W, hW, Unit{}, hroom, hb)))
  +x2 = S.steps.then(2n, 1n, B2, S2, B3, {==}, F.store.step(8, A0, 0, R3, ls, [], L, p, lm, m2, zin(p, A0, 8, T, eT, W, hW, Unit{}, hroom, hb)))
  +x1 = S.steps.then(2n, 1n, B1, S1, B2, {==}, F.store.step(4, A0, 0, R2, ls, [], L, p, lm, m1, zin(p, A0, 4, T, eT, W, hW, Unit{}, hroom, hb)))
  +x0 = S.steps.then(2n, 1n, B0, S0, B1, {==}, F.store.step(0, A0, 0, R1, ls, [], L, p, lm, m, zin(p, A0, 0, T, eT, W, hW, Unit{}, hroom, hb)))
  S.steps.then(3n, 12n, B0, B1, E, x0, S.steps.then(3n, 9n, B1, B2, E, x1, S.steps.then(3n, 6n, B2, B3, E, x2, S.steps.then(3n, 3n, B3, B4, E, x3, x4))))
