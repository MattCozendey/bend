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
import ./proof_sim_step.bend as S

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
          %Equal.sym(Bool & Word(p), Word.shl.out(p, b, t), (PH.H.pout(p, b, t), Word.shl.put(p, b, t)), out.put(p, b, t)) : {Word.shl.out.con(p, c, _) == (PH.H.pout(p, b, t), WCon{c, Word.shl.put(p, b, t)}) : Bool & Word(1n+p)}
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
    case 1n+(+p):
      Equal.trans(Nat, Nat.sub(1n+Nat.add(p, b), b), 1n+Nat.sub(Nat.add(p, b), b), 1n+p,
        A.sub.succ.l(Nat.add(p, b), b, N.le_add_l(p, b)), Equal.cong(Nat, Nat, z => 1n+z, Nat.sub(Nat.add(p, b), b), p, add.sub.r(p, b)))

def sub.nat.go(c: Bool, +X: Nat, +Y0: Nat, +D0: Nat, +T: Nat, eT: {N.D(32n, PH.H.bn(True{})) == T : Nat}, h: N.Le(Y0, X), hd: N.Le(1n+D0, T),
  e: {Nat.add(X, N.D(32n, PH.H.bn(c))) == Nat.add(D0, Y0) : Nat}) -> {D0 == Nat.sub(X, Y0) : Nat}:
  match c:
    case False{}:
      +e0 = Equal.trans(Nat, X, Nat.add(X, 0n), Nat.add(D0, Y0), Equal.sym(Nat, Nat.add(X, 0n), X, N.add_zero(X)), e)
      Equal.sym(Nat, Nat.sub(X, Y0), D0, Equal.trans(Nat, Nat.sub(X, Y0), Nat.sub(Nat.add(D0, Y0), Y0), D0,
        Equal.cong(Nat, Nat, z => Nat.sub(z, Y0), X, Nat.add(D0, Y0), e0), add.sub.r(D0, Y0)))
    case True{}:
      +e1 = {(%eT : {Nat.add(X, _) == Nat.add(D0, Y0) : Nat}; e) : {Nat.add(X, T) == Nat.add(D0, Y0) : Nat}}
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
      sub.nat.go(c, X, Y0, D0, N.D(32n, 1n), Equal.cong(Nat, Nat, z => N.D(32n, z), PH.H.bn(True{}), 1n, {==}), h, V.word.lt(32n, d),
        Equal.trans(Nat, Nat.add(X, N.D(32n, PH.H.bn(c))), Nat.add(Word.to_nat(32n, Word.adc(32n, d, yw, False{}, False{})), N.D(32n, PH.H.bn(c))),
          Nat.add(D0, Y0),
          Equal.cong(Nat, Nat, z => Nat.add(z, N.D(32n, PH.H.bn(c))), X, Word.to_nat(32n, Word.adc(32n, d, yw, False{}, False{})),
            Equal.sym(Nat, Word.to_nat(32n, Word.adc(32n, d, yw, False{}, False{})), X, es2)), ea))

# The long division
# -----------------

# the quotient times b, plus the remainder, is A; the remainder below b
def DM(-p: Nat, x: Word(p) & U32, +B: Nat, +A0: Nat) -> Data:
  S.P2({Nat.add(Nat.mul(Word.to_nat(p, dq(p, x)), B), U32.to_nat(dr(p, x))) == A0 : Nat}, N.Le(1n+U32.to_nat(dr(p, x)), B))

def ge.le(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), e: {Cmp.is_ge(c) == True{} : Bool}) -> N.Le(y, x):
  match c:
    case LT{}:
      Empty.absurd(N.Le(y, x), N.false_ne_true(e))
    case EQ{}:
      %r : N.Le(_, x)
      N.le_refl(x)
    case GT{}:
      N.weaken(y, x, r)

def bn.le(a0: Bool, +x: Nat) -> N.Le(Nat.add(PH.H.bn(a0), x), 1n+x):
  match a0:
    case False{}:
      N.le_succ(x, x, N.le_refl(x))
    case True{}:
      N.le_refl(1n+x)

# the bit shifted out of a remainder below 2^31 is 0
def pout.f(b: Bool, +a0: Bool, +rw: Word(32n), +T: Nat, +eT: {N.D(32n, PH.H.bn(True{})) == T : Nat}, +H: Nat, +eH: {Nat.double(H) == T : Nat},
  +hR: N.Le(1n+Word.to_nat(32n, rw), H), +e: {PH.H.pout(32n, a0, rw) == b : Bool}) -> {PH.H.pout(32n, a0, rw) == False{} : Bool}:
  match b:
    case False{}:
      e
    case True{}:
      +V0 = Word.to_nat(32n, Word.shl.put(32n, a0, rw))
      +R0 = Word.to_nat(32n, rw)
      +ep = PH.H.put(32n, a0, rw)
      +ep1 = {(%e : {Nat.add(V0, N.D(32n, PH.H.bn(_))) == Nat.add(PH.H.bn(a0), Nat.double(R0)) : Nat}; ep) :
        {Nat.add(V0, N.D(32n, PH.H.bn(True{}))) == Nat.add(PH.H.bn(a0), Nat.double(R0)) : Nat}}
      +ep2 = {(%eT : {Nat.add(V0, _) == Nat.add(PH.H.bn(a0), Nat.double(R0)) : Nat}; ep1) : {Nat.add(V0, T) == Nat.add(PH.H.bn(a0), Nat.double(R0)) : Nat}}
      +l1 = N.le_rw_r(T, Nat.add(V0, T), Nat.add(PH.H.bn(a0), Nat.double(R0)), ep2, N.le_add_l(V0, T))
      +l2 = N.le_trans(T, Nat.add(PH.H.bn(a0), Nat.double(R0)), 1n+Nat.double(R0), l1, bn.le(a0, Nat.double(R0)))
      +l3 = N.le_rw_r(2n+Nat.double(R0), Nat.double(H), T, eH, N.double_mono(1n+R0, H, hR))
      Empty.absurd({PH.H.pout(32n, a0, rw) == False{} : Bool}, N.not_succ_le(1n+Nat.double(R0), N.le_trans(2n+Nat.double(R0), T, 1n+Nat.double(R0), l3, l2)))

# 2QB + (a + 2R) = a + 2(QB + R)
def alg1(+QB: Nat, +a: Nat, +R: Nat) -> {Nat.add(Nat.double(QB), Nat.add(a, Nat.double(R))) == Nat.add(a, Nat.double(Nat.add(QB, R))) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.double(QB), Nat.add(a, Nat.double(R))), Nat.add(a, Nat.add(Nat.double(QB), Nat.double(R))), Nat.add(a, Nat.double(Nat.add(QB, R))),
    PH.H.add_k(Nat.double(QB), a, Nat.double(R)),
    Equal.cong(Nat, Nat, z => Nat.add(a, z), Nat.add(Nat.double(QB), Nat.double(R)), Nat.double(Nat.add(QB, R)),
      Equal.sym(Nat, Nat.double(Nat.add(QB, R)), Nat.add(Nat.double(QB), Nat.double(R)), N.double_add(QB, R))))

# (B + X) + (S - B) = X + S, for B <= S
def alg2(+B: Nat, +X: Nat, +S0: Nat, h: N.Le(B, S0)) -> {Nat.add(Nat.add(B, X), Nat.sub(S0, B)) == Nat.add(X, S0) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(B, X), Nat.sub(S0, B)), Nat.add(Nat.add(X, B), Nat.sub(S0, B)), Nat.add(X, S0),
    Equal.cong(Nat, Nat, z => Nat.add(z, Nat.sub(S0, B)), Nat.add(B, X), Nat.add(X, B), Z.add.comm(B, X)),
    Equal.trans(Nat, Nat.add(Nat.add(X, B), Nat.sub(S0, B)), Nat.add(X, Nat.add(B, Nat.sub(S0, B))), Nat.add(X, S0),
      Z.add.assoc(X, B, Nat.sub(S0, B)),
      Equal.cong(Nat, Nat, z => Nat.add(X, z), Nat.add(B, Nat.sub(S0, B)), S0,
        Equal.trans(Nat, Nat.add(B, Nat.sub(S0, B)), Nat.add(Nat.sub(S0, B), B), S0, Z.add.comm(B, Nat.sub(S0, B)), Z.sub.add(S0, B, h)))))

# c + a <= c + b gives a <= b
def le.cancel.l(c: Nat, +a: Nat, +b: Nat, h: N.Le(Nat.add(c, a), Nat.add(c, b))) -> N.Le(a, b):
  match c:
    case 0n:
      h
    case 1n+p:
      le.cancel.l(p, a, b, h)

# 1 + (S - B) <= B, for B <= S < 2B
def alg3(+B: Nat, +S0: Nat, h: N.Le(B, S0), h2: N.Le(1n+S0, Nat.add(B, B))) -> N.Le(1n+Nat.sub(S0, B), B):
  +D0 = Nat.sub(S0, B)
  +h3 = N.le_rw_l(1n+S0, Nat.add(B, 1n+D0), Nat.add(B, B),
    Equal.trans(Nat, 1n+S0, 1n+Nat.add(D0, B), Nat.add(B, 1n+D0),
      Equal.cong(Nat, Nat, z => 1n+z, S0, Nat.add(D0, B), Equal.sym(Nat, Nat.add(D0, B), S0, Z.sub.add(S0, B, h))),
      Z.add.comm(1n+D0, B)), h2)
  le.cancel.l(B, 1n+D0, B, h3)

# 2x = x + x
def dbl.add(+x: Nat) -> {Nat.double(x) == Nat.add(x, x) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+(+p):
      Equal.trans(Nat, 2n+Nat.double(p), 2n+Nat.add(p, p), 1n+Nat.add(p, 1n+p),
        Equal.cong(Nat, Nat, z => 2n+z, Nat.double(p), Nat.add(p, p), dbl.add(p)),
        Equal.cong(Nat, Nat, z => 1n+z, 1n+Nat.add(p, p), Nat.add(p, 1n+p), Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), N.add_succ_r(p, p))))

# the value after a round of the division, with the bit 0 into the quotient
def dm.base(+q: Nat, +q0: Word(q), +S0: Nat, +B: Nat, +a0: Bool, +HI: Nat, +R0: Nat,
  +eih: {Nat.add(Nat.mul(Word.to_nat(q, q0), B), R0) == HI : Nat},
  +eS: {S0 == Nat.add(PH.H.bn(a0), Nat.double(R0)) : Nat}) ->
  {Nat.add(Nat.mul(Nat.double(Word.to_nat(q, q0)), B), S0) == Nat.add(PH.H.bn(a0), Nat.double(HI)) : Nat}:
  +Q0 = Word.to_nat(q, q0)
  Equal.trans(Nat, Nat.add(Nat.mul(Nat.double(Q0), B), S0), Nat.add(Nat.double(Nat.mul(Q0, B)), Nat.add(PH.H.bn(a0), Nat.double(R0))),
    Nat.add(PH.H.bn(a0), Nat.double(HI)),
    Equal.trans(Nat, Nat.add(Nat.mul(Nat.double(Q0), B), S0), Nat.add(Nat.double(Nat.mul(Q0, B)), S0), Nat.add(Nat.double(Nat.mul(Q0, B)), Nat.add(PH.H.bn(a0), Nat.double(R0))),
      Equal.cong(Nat, Nat, z => Nat.add(z, S0), Nat.mul(Nat.double(Q0), B), Nat.double(Nat.mul(Q0, B)), N.mul_double(Q0, B)),
      Equal.cong(Nat, Nat, z => Nat.add(Nat.double(Nat.mul(Q0, B)), z), S0, Nat.add(PH.H.bn(a0), Nat.double(R0)), eS)),
    Equal.trans(Nat, Nat.add(Nat.double(Nat.mul(Q0, B)), Nat.add(PH.H.bn(a0), Nat.double(R0))), Nat.add(PH.H.bn(a0), Nat.double(Nat.add(Nat.mul(Q0, B), R0))),
      Nat.add(PH.H.bn(a0), Nat.double(HI)), alg1(Nat.mul(Q0, B), PH.H.bn(a0), R0),
      Equal.cong(Nat, Nat, z => Nat.add(PH.H.bn(a0), Nat.double(z)), Nat.add(Nat.mul(Q0, B), R0), HI, eih)))

# one step of the division, by the bit g of the shifted remainder >= b
def dm.fin(g: Bool, +q: Nat, +q0: Word(q), +sput: Word(32n), +b: U32, +a0: Bool, +HI: Nat, +R0: Nat,
  +eg: {U32.is_ge(U32{sput}, b) == g : Bool},
  +eih: {Nat.add(Nat.mul(Word.to_nat(q, q0), U32.to_nat(b)), R0) == HI : Nat}, +rih: N.Le(1n+R0, U32.to_nat(b)),
  +eS: {Word.to_nat(32n, sput) == Nat.add(PH.H.bn(a0), Nat.double(R0)) : Nat}) ->
  DM(1n+q, U32.divmod.go.fin(q, q0, U32{sput}, b, g), U32.to_nat(b), Nat.add(PH.H.bn(a0), Nat.double(HI))):
  match g:
    case False{}:
      +B = U32.to_nat(b)
      +S0 = Word.to_nat(32n, sput)
      (dm.base(q, q0, S0, B, a0, HI, R0, eih, eS), PH.H.rel_nge(U32.cmp(U32{sput}, b), S0, B, N.U32.rel(U32{sput}, b), eg))
    case True{}:
      +B = U32.to_nat(b)
      +Q0 = Word.to_nat(q, q0)
      +S0 = Word.to_nat(32n, sput)
      +base = dm.base(q, q0, S0, B, a0, HI, R0, eih, eS)
      +hBS = ge.le(U32.cmp(U32{sput}, b), S0, B, N.U32.rel(U32{sput}, b), eg)
      +esub = sub.nat(U32{sput}, b, hBS)
      +eq = Equal.trans(Nat, Nat.add(Nat.add(B, Nat.mul(Nat.double(Q0), B)), U32.to_nat(U32.sub(U32{sput}, b))),
        Nat.add(Nat.add(B, Nat.mul(Nat.double(Q0), B)), Nat.sub(S0, B)), Nat.add(PH.H.bn(a0), Nat.double(HI)),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.add(B, Nat.mul(Nat.double(Q0), B)), z), U32.to_nat(U32.sub(U32{sput}, b)), Nat.sub(S0, B), esub),
        Equal.trans(Nat, Nat.add(Nat.add(B, Nat.mul(Nat.double(Q0), B)), Nat.sub(S0, B)), Nat.add(Nat.mul(Nat.double(Q0), B), S0),
          Nat.add(PH.H.bn(a0), Nat.double(HI)), alg2(B, Nat.mul(Nat.double(Q0), B), S0, hBS), base))
      +h2 = N.le_rw_r(1n+S0, Nat.double(B), Nat.add(B, B), dbl.add(B),
        N.le_trans(1n+S0, 2n+Nat.double(R0), Nat.double(B),
          N.le_rw_l(1n+Nat.add(PH.H.bn(a0), Nat.double(R0)), 1n+S0, 2n+Nat.double(R0),
            Equal.cong(Nat, Nat, z => 1n+z, Nat.add(PH.H.bn(a0), Nat.double(R0)), S0, Equal.sym(Nat, S0, Nat.add(PH.H.bn(a0), Nat.double(R0)), eS)),
            bn.le(a0, Nat.double(R0))),
          N.double_mono(1n+R0, B, rih)))
      +lt = N.le_rw_l(1n+Nat.sub(S0, B), 1n+U32.to_nat(U32.sub(U32{sput}, b)), B,
        Equal.cong(Nat, Nat, z => 1n+z, Nat.sub(S0, B), U32.to_nat(U32.sub(U32{sput}, b)), Equal.sym(Nat, U32.to_nat(U32.sub(U32{sput}, b)), Nat.sub(S0, B), esub)),
        alg3(B, S0, hBS, h2))
      (eq, lt)

# one round of the division, from the quotient and remainder of the high bits
def dm.rec(+q: Nat, +a0: Bool, +b: U32, x: Word(q) & U32, +HI: Nat, +T: Nat, +eT: {N.D(32n, PH.H.bn(True{})) == T : Nat},
  +H: Nat, +eH: {Nat.double(H) == T : Nat}, +hb: N.Le(U32.to_nat(b), H), ih: DM(q, x, U32.to_nat(b), HI)) ->
  DM(1n+q, U32.divmod.go.rec(q, a0, b, x), U32.to_nat(b), Nat.add(PH.H.bn(a0), Nat.double(HI))):
  match x:
    case Tuple{+q0, +r0}:
      match r0:
        case U32{+rw}:
          (+eih, +rih) = ih
          +R0 = Word.to_nat(32n, rw)
          +sput = Word.shl.put(32n, a0, rw)
          +B = U32.to_nat(b)
          +hR = N.le_trans(1n+R0, B, H, rih, hb)
          +pf = pout.f(PH.H.pout(32n, a0, rw), a0, rw, T, eT, H, eH, hR, {==})
          +ep = PH.H.put(32n, a0, rw)
          +ep0 = {(%pf :
              {Nat.add(Word.to_nat(32n, sput), N.D(32n, PH.H.bn(_))) == Nat.add(PH.H.bn(a0), Nat.double(R0)) : Nat}; ep) :
            {Nat.add(Word.to_nat(32n, sput), N.D(32n, PH.H.bn(False{}))) == Nat.add(PH.H.bn(a0), Nat.double(R0)) : Nat}}
          +eS = Equal.trans(Nat, Word.to_nat(32n, sput), Nat.add(Word.to_nat(32n, sput), 0n), Nat.add(PH.H.bn(a0), Nat.double(R0)),
            Equal.sym(Nat, Nat.add(Word.to_nat(32n, sput), 0n), Word.to_nat(32n, sput), N.add_zero(Word.to_nat(32n, sput))), ep0)
          %Equal.sym(Bool & Word(32n), Word.shl.out(32n, a0, rw), (PH.H.pout(32n, a0, rw), sput), out.put(32n, a0, rw)) :
            DM(1n+q, U32.divmod.go.shl(q, q0, b, _), B, Nat.add(PH.H.bn(a0), Nat.double(HI)))
          %Equal.sym(Bool, PH.H.pout(32n, a0, rw), False{}, pf) :
            DM(1n+q, U32.divmod.go.fin(q, q0, U32{sput}, b, Bool.or(_, U32.is_ge(U32{sput}, b))), B, Nat.add(PH.H.bn(a0), Nat.double(HI)))
          dm.fin(U32.is_ge(U32{sput}, b), q, q0, sput, b, a0, HI, R0, {==}, eih, rih, eS)

# the long division of a by b, for 1 <= b <= 2^31
def dm(+p: Nat, +a: Word(p), +b: U32, +T: Nat, +eT: {N.D(32n, PH.H.bn(True{})) == T : Nat},
  +H: Nat, +eH: {Nat.double(H) == T : Nat}, +hb: N.Le(U32.to_nat(b), H), +hb1: N.Le(1n, U32.to_nat(b))) ->
  DM(p, U32.divmod.go(p, a, b), U32.to_nat(b), Word.to_nat(p, a)):
  match p a:
    case 0n WNil{}:
      ({==}, hb1)
    case 1n+q WCon{+a0, +hi}:
      %Equal.sym(Nat, Word.to_nat(1n+q, WCon{a0, hi}), Nat.add(PH.H.bn(a0), Nat.double(Word.to_nat(q, hi))), wt(q, a0, hi)) :
        DM(1n+q, U32.divmod.go.rec(q, a0, b, U32.divmod.go(q, hi, b)), U32.to_nat(b), _)
      dm.rec(q, a0, b, U32.divmod.go(q, hi, b), Word.to_nat(q, hi), T, eT, H, eH, hb, dm(q, hi, b, T, eT, H, eH, hb, hb1))
