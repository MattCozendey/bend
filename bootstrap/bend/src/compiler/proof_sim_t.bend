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

# 0x0CCC...C as a word, its lowest nibble first
def cwz(j: Nat) -> Word(4n+q4(j)):
  match j:
    case 0n:
      WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}
    case 1n+q:
      WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, cwz(q)}}}}

def cwz.val(+j: Nat) -> {Word.to_nat(4n+q4(j), cwz(j)) == PH.H.pat(j) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+q:
      %Equal.sym(Nat, Word.to_nat(4n+q4(q), cwz(q)), PH.H.pat(q), cwz.val(q)) :
        {Nat.double(Nat.double(1n+Nat.double(1n+Nat.double(_)))) == Nat.add(12n, N.D(4n, PH.H.pat(q))) : Nat}
      {==}

def lit.cw() -> {214748364 == U32{cwz(7n)} : U32}:
  {==}

def lit.pat() -> {U32.to_nat(214748364) == PH.H.pat(7n) : Nat}:
  %Equal.sym(U32, 214748364, U32{cwz(7n)}, lit.cw()) : {U32.to_nat(_) == PH.H.pat(7n) : Nat}
  Equal.trans(Nat, U32.to_nat(U32{cwz(7n)}), Word.to_nat(32n, cwz(7n)), PH.H.pat(7n), N.u32_to_nat(cwz(7n)), cwz.val(7n))

def succ.ne0(+y: Nat, e: {0n == 1n+y : Nat}) -> Empty:
  N.le_rw_r(1n+y, 1n+y, 0n, Equal.sym(Nat, 0n, 1n+y, e), N.le_refl(1n+y))

# 20x = 20y gives x = y
def t20.inj(+x: Nat, +y: Nat, e: {PH.H.t20(x) == PH.H.t20(y) : Nat}) -> {x == y : Nat}:
  ?TODO

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
