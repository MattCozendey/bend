# compiler: the division of the first cell
# ========================================
#
# U32.div by b <= 2^31: the quotient q and the remainder r of Base's long
# division (U32.divmod.go) satisfy q b + r = a and r < b (dm), as the shift of
# a remainder below 2^31 never overflows; so q is the only number with
# q b <= a < q b + b (div.of), which gives Cir.first.

import Base
import ./impl.bend as C
import ./proof_need.bend as N
import ./proof_halt.bend as PH
import ./proof_sim_mem.bend as Y
import ./proof_sim_nat.bend as Z
import ./proof_valid.bend as V
import ./proof_sim_alloc.bend as A

def dq(-p: Nat, x: Word(p) & U32) -> Word(p):
  (q, r) = x
  q

def dr(-p: Nat, x: Word(p) & U32) -> U32:
  (q, r) = x
  r

# the shift with its bit out is the shift and the bit
def out.put(+n: Nat, +c: Bool, +w: Word(n)) -> {Word.shl.out(n, c, w) == (PH.H.pout(n, c, w), Word.shl.put(n, c, w)) : Bool & Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          %out.put(p, b, t) : {Word.shl.out.con(p, c, _) == (PH.H.pout(p, b, t), WCon{c, Word.shl.put(p, b, t)}) : Bool & Word(1n+p)}
          {==}

# the number of a word, by its low bit
def wt(+q: Nat, a0: Bool, +hi: Word(q)) -> {Word.to_nat(1n+q, WCon{a0, hi}) == Nat.add(PH.H.bn(a0), Nat.double(Word.to_nat(q, hi))) : Nat}:
  match a0:
    case False{}:
      {==}
    case True{}:
      {==}

# x - x = 0
def sub.self(x: Nat) -> {Nat.sub(x, x) == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      sub.self(p)

# (a + b) - b = a
def add.sub.r(a: Nat, +b: Nat) -> {Nat.sub(Nat.add(a, b), b) == a : Nat}:
  match a:
    case 0n:
      sub.self(b)
    case 1n+p:
      Equal.trans(Nat, Nat.sub(1n+Nat.add(p, b), b), 1n+Nat.sub(Nat.add(p, b), b), 1n+p,
        A.sub.succ.l(Nat.add(p, b), b, N.le_add_l(p, b)), Equal.cong(Nat, Nat, z => 1n+z, Nat.sub(Nat.add(p, b), b), p, add.sub.r(p, b)))

def sub.nat.go(c: Bool, +X: Nat, +Y0: Nat, +D0: Nat, h: N.Le(Y0, X), hd: N.Le(1n+D0, N.D(32n, 1n)),
  e: {Nat.add(X, N.D(32n, PH.H.bn(c))) == Nat.add(D0, Y0) : Nat}) -> {D0 == Nat.sub(X, Y0) : Nat}:
  match c:
    case False{}:
      +e0 = Equal.trans(Nat, X, Nat.add(X, 0n), Nat.add(D0, Y0), Equal.sym(Nat, Nat.add(X, 0n), X, N.add_zero(X)), e)
      Equal.sym(Nat, Nat.sub(X, Y0), D0, Equal.trans(Nat, Nat.sub(X, Y0), Nat.sub(Nat.add(D0, Y0), Y0), D0,
        Equal.cong(Nat, Nat, z => Nat.sub(z, Y0), X, Nat.add(D0, Y0), e0), add.sub.r(D0, Y0)))
    case True{}:
      +T = N.D(32n, 1n)
      +e1 = {(%{{==} : {PH.H.bn(True{}) == 1n : Nat}} : {Nat.add(X, N.D(32n, _)) == Nat.add(D0, Y0) : Nat}; e) : {Nat.add(X, T) == Nat.add(D0, Y0) : Nat}}
      +l1 = N.le_rw_l(Nat.add(D0, Y0), Nat.add(X, T), Nat.add(D0, Y0), Equal.sym(Nat, Nat.add(X, T), Nat.add(D0, Y0), e1), N.le_refl(Nat.add(D0, Y0)))
      +l2 = N.add_mono(D0, D0, Y0, X, N.le_refl(D0), h)
      +l3 = N.le_rw_r(1n+Nat.add(D0, X), Nat.add(T, X), Nat.add(X, T), Z.add.comm(T, X), Z.le.add_r(1n+D0, T, X, hd))
      Empty.absurd({D0 == Nat.sub(X, Y0) : Nat}, N.not_succ_le(Nat.add(D0, X),
        N.le_trans(1n+Nat.add(D0, X), Nat.add(X, T), Nat.add(D0, X), l3, N.le_trans(Nat.add(X, T), Nat.add(D0, Y0), Nat.add(D0, X), l1, l2))))

# x - y is exact for y <= x
def sub.nat(+x: U32, +y: U32, h: N.Le(U32.to_nat(y), U32.to_nat(x))) -> {U32.to_nat(U32.sub(x, y)) == Nat.sub(U32.to_nat(x), U32.to_nat(y)) : Nat}:
  match x y:
    case U32{+xw} U32{+yw}:
      +d = Word.sub(32n, xw, yw)
      +X = Word.to_nat(32n, xw)
      +Y0 = Word.to_nat(32n, yw)
      +D0 = Word.to_nat(32n, d)
      +c = PH.H.cout(32n, d, yw, False{})
      +ea = PH.H.adc(32n, d, yw, False{})
      +es = Equal.cong(U32, Nat, z => U32.to_nat(z), U32.add(U32.sub(U32{xw}, U32{yw}), U32{yw}), U32{xw}, A.U32.subadd(U32{xw}, U32{yw}))
      +es2 = {es : {Word.to_nat(32n, Word.adc(32n, d, yw, False{}, False{})) == X : Nat}}
      sub.nat.go(c, X, Y0, D0, h, V.word.lt(32n, d),
        Equal.trans(Nat, Nat.add(X, N.D(32n, PH.H.bn(c))), Nat.add(Word.to_nat(32n, Word.adc(32n, d, yw, False{}, False{})), N.D(32n, PH.H.bn(c))),
          Nat.add(D0, Y0),
          Equal.cong(Nat, Nat, z => Nat.add(z, N.D(32n, PH.H.bn(c))), X, Word.to_nat(32n, Word.adc(32n, d, yw, False{}, False{})),
            Equal.sym(Nat, Word.to_nat(32n, Word.adc(32n, d, yw, False{}, False{})), X, es2)), ea))
