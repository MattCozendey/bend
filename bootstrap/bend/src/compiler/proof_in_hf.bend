# compiler: the first cell of the machine is past the table (layer B)
# ==================================================================
#
# hf.first: from Start's equation first = Cir.first(k, 20 (k + 1) + len),
# with 363 <= k < 2^26, the first cell is at least 345 (In.input.post's
# premise hF). Cir.first picks k + 1 when 20 (k + 1) >= end; else it is
# (end - 1) / 20 + 1 with end > 20 (k + 1), so the quotient is past k.
#
# The long division (dm and what it needs) is copied from proof_sim_div.bend
# and its imports (proof_sim_* are edited elsewhere): it gives q 20 + r = x
# with r < 20 for U32.div(x, 20) = q. Big closed numbers (2^26, 2^32,
# 214748364) only ever appear in types spelled the same, so the checker never
# expands them.

import Base
import ./impl.bend as C
import ./proof_need.bend as N
import ./proof_halt.bend as PH
import ./proof_module.bend as MO
import ./proof_instrs.bend as PI
import ./proof_img.bend as PG

# Kit (copied)
# ------------

def hf.P2(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

def hf.fst(-A: Data, -B: Data, p: hf.P2(A, B)) -> A:
  (a, b) = p
  a

def hf.snd(-A: Data, -B: Data, p: hf.P2(A, B)) -> B:
  (a, b) = p
  b

def hf.sub0(x: Nat) -> {Nat.sub(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

# (1 + x) - f = 1 + (x - f), for f <= x
def hf.sub.succ.l(+x: Nat, +f: Nat, h: N.Le(f, x)) -> {Nat.sub(1n+x, f) == 1n+Nat.sub(x, f) : Nat}:
  match x f:
    case _ 0n:
      Equal.cong(Nat, Nat, z => 1n+z, x, Nat.sub(x, 0n), Equal.sym(Nat, Nat.sub(x, 0n), x, hf.sub0(x)))
    case 0n 1n+q:
      Empty.absurd({Nat.sub(1n, 1n+q) == 1n+Nat.sub(0n, 1n+q) : Nat}, h)
    case 1n+p 1n+q:
      hf.sub.succ.l(p, q, h)

def hf.W.subadd(+n: Nat, +x: Word(n), +p: Word(n), c: Bool) ->
  {Word.adc(n, Word.adc(n, x, p, True{}, c), p, False{}, Bool.not(c)) == x : Word(n)}:
  match n:
    case 0n:
      match x p:
        case WNil{} WNil{}:
          {==}
    case 1n+q:
      match x p c:
        case WCon{False{}, +xt} WCon{False{}, +pt} False{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{False{}, z}, Word.adc(q, Word.adc(q, xt, pt, True{}, False{}), pt, False{}, True{}), xt, hf.W.subadd(q, xt, pt, False{}))
        case WCon{False{}, +xt} WCon{False{}, +pt} True{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{False{}, z}, Word.adc(q, Word.adc(q, xt, pt, True{}, True{}), pt, False{}, False{}), xt, hf.W.subadd(q, xt, pt, True{}))
        case WCon{False{}, +xt} WCon{True{}, +pt} False{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{False{}, z}, Word.adc(q, Word.adc(q, xt, pt, True{}, False{}), pt, False{}, True{}), xt, hf.W.subadd(q, xt, pt, False{}))
        case WCon{False{}, +xt} WCon{True{}, +pt} True{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{False{}, z}, Word.adc(q, Word.adc(q, xt, pt, True{}, False{}), pt, False{}, True{}), xt, hf.W.subadd(q, xt, pt, False{}))
        case WCon{True{}, +xt} WCon{False{}, +pt} False{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{True{}, z}, Word.adc(q, Word.adc(q, xt, pt, True{}, True{}), pt, False{}, False{}), xt, hf.W.subadd(q, xt, pt, True{}))
        case WCon{True{}, +xt} WCon{False{}, +pt} True{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{True{}, z}, Word.adc(q, Word.adc(q, xt, pt, True{}, True{}), pt, False{}, False{}), xt, hf.W.subadd(q, xt, pt, True{}))
        case WCon{True{}, +xt} WCon{True{}, +pt} False{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{True{}, z}, Word.adc(q, Word.adc(q, xt, pt, True{}, False{}), pt, False{}, True{}), xt, hf.W.subadd(q, xt, pt, False{}))
        case WCon{True{}, +xt} WCon{True{}, +pt} True{}:
          Equal.cong(Word(q), Word(1n+q), z => WCon{True{}, z}, Word.adc(q, Word.adc(q, xt, pt, True{}, True{}), pt, False{}, False{}), xt, hf.W.subadd(q, xt, pt, True{}))

# (x - p) + p = x
def hf.U32.subadd(+x: U32, +p: U32) -> {U32.add(U32.sub(x, p), p) == x : U32}:
  match x p:
    case U32{+xw} U32{+pw}:
      Equal.cong(Word(32n), U32, z => U32{z}, Word.adc(32n, Word.adc(32n, xw, pw, True{}, True{}), pw, False{}, False{}), xw, hf.W.subadd(32n, xw, pw, True{}))

def hf.add.comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, N.add_zero(b))
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, b), Nat.add(b, p), hf.add.comm(p, b)),
        Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), N.add_succ_r(b, p)))

def hf.add.assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), hf.add.assoc(p, b, c))

def hf.le.add_r(+a: Nat, +b: Nat, +c: Nat, h: N.Le(a, b)) -> N.Le(Nat.add(a, c), Nat.add(b, c)):
  N.add_mono(a, b, c, c, h, N.le_refl(c))

def hf.sub.add(+x: Nat, +f: Nat, h: N.Le(f, x)) -> {Nat.add(Nat.sub(x, f), f) == x : Nat}:
  match x f:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.add(Nat.sub(0n, 1n+q), 1n+q) == 0n : Nat}, h)
    case 1n+p 0n:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 0n), p, N.add_zero(p))
    case 1n+p 1n+q:
      Equal.trans(Nat, Nat.add(Nat.sub(p, q), 1n+q), 1n+Nat.add(Nat.sub(p, q), q), 1n+p, N.add_succ_r(Nat.sub(p, q), q),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.sub(p, q), q), p, hf.sub.add(p, q, h)))

# a word of n bits is below 2^n
def hf.word.lt(+n: Nat, w: Word(n)) -> N.Le(1n+Word.to_nat(n, w), N.D(n, 1n)):
  match n:
    case 0n:
      match w:
        case WNil{}:
          Unit{}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          N.lt_dd(Word.to_nat(p, t), N.D(p, 1n), hf.word.lt(p, t))
        case WCon{True{}, +t}:
          N.double_mono(1n+Word.to_nat(p, t), N.D(p, 1n), hf.word.lt(p, t))

# a U32 is below 2^32
def hf.u32.lt(x: U32) -> N.Le(1n+U32.to_nat(x), N.D(32n, 1n)):
  match x:
    case U32{+w}:
      N.le_rw_l(1n+Word.to_nat(32n, w), 1n+U32.to_nat(U32{w}), N.D(32n, 1n),
        Equal.cong(Nat, Nat, v => 1n+v, Word.to_nat(32n, w), U32.to_nat(U32{w}), Equal.sym(Nat, U32.to_nat(U32{w}), Word.to_nat(32n, w), N.u32_to_nat(w))),
        hf.word.lt(32n, w))

# The long division (copied from proof_sim_div.bend)
# -------------------------------------------------

def hf.dq(-p: Nat, x: Word(p) & U32) -> Word(p):
  (q, r) = x
  q

def hf.dr(-p: Nat, x: Word(p) & U32) -> U32:
  (q, r) = x
  r

def hf.out.put(+n: Nat, +c: Bool, +w: Word(n)) -> {Word.shl.out(n, c, w) == (PH.H.pout(n, c, w), Word.shl.put(n, c, w)) : Bool & Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          %Equal.sym(Bool & Word(p), Word.shl.out(p, b, t), (PH.H.pout(p, b, t), Word.shl.put(p, b, t)), hf.out.put(p, b, t)) : {Word.shl.out.con(p, c, _) == (PH.H.pout(p, b, t), WCon{c, Word.shl.put(p, b, t)}) : Bool & Word(1n+p)}
          {==}

def hf.wt(+q: Nat, a0: Bool, +hi: Word(q)) -> {Word.to_nat(1n+q, WCon{a0, hi}) == Nat.add(PH.H.bn(a0), Nat.double(Word.to_nat(q, hi))) : Nat}:
  match a0:
    case False{}:
      {==}
    case True{}:
      {==}

def hf.sub.self(x: Nat) -> {Nat.sub(x, x) == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      hf.sub.self(p)

def hf.add.sub.r(a: Nat, +b: Nat) -> {Nat.sub(Nat.add(a, b), b) == a : Nat}:
  match a:
    case 0n:
      hf.sub.self(b)
    case 1n+(+p):
      Equal.trans(Nat, Nat.sub(1n+Nat.add(p, b), b), 1n+Nat.sub(Nat.add(p, b), b), 1n+p,
        hf.sub.succ.l(Nat.add(p, b), b, N.le_add_l(p, b)), Equal.cong(Nat, Nat, z => 1n+z, Nat.sub(Nat.add(p, b), b), p, hf.add.sub.r(p, b)))

def hf.sub.nat.go(c: Bool, +X: Nat, +Y0: Nat, +D0: Nat, +T: Nat, eT: {N.D(32n, PH.H.bn(True{})) == T : Nat}, h: N.Le(Y0, X), hd: N.Le(1n+D0, T),
  e: {Nat.add(X, N.D(32n, PH.H.bn(c))) == Nat.add(D0, Y0) : Nat}) -> {D0 == Nat.sub(X, Y0) : Nat}:
  match c:
    case False{}:
      +e0 = Equal.trans(Nat, X, Nat.add(X, 0n), Nat.add(D0, Y0), Equal.sym(Nat, Nat.add(X, 0n), X, N.add_zero(X)), e)
      Equal.sym(Nat, Nat.sub(X, Y0), D0, Equal.trans(Nat, Nat.sub(X, Y0), Nat.sub(Nat.add(D0, Y0), Y0), D0,
        Equal.cong(Nat, Nat, z => Nat.sub(z, Y0), X, Nat.add(D0, Y0), e0), hf.add.sub.r(D0, Y0)))
    case True{}:
      +e1 = {(%eT : {Nat.add(X, _) == Nat.add(D0, Y0) : Nat}; e) : {Nat.add(X, T) == Nat.add(D0, Y0) : Nat}}
      +l1 = N.le_rw_l(Nat.add(D0, Y0), Nat.add(X, T), Nat.add(D0, Y0), Equal.sym(Nat, Nat.add(X, T), Nat.add(D0, Y0), e1), N.le_refl(Nat.add(D0, Y0)))
      +l2 = N.add_mono(D0, D0, Y0, X, N.le_refl(D0), h)
      +l3 = N.le_rw_r(1n+Nat.add(D0, X), Nat.add(T, X), Nat.add(X, T), hf.add.comm(T, X), hf.le.add_r(1n+D0, T, X, hd))
      Empty.absurd({D0 == Nat.sub(X, Y0) : Nat}, N.not_succ_le(Nat.add(D0, X),
        N.le_trans(1n+Nat.add(D0, X), Nat.add(X, T), Nat.add(D0, X), l3, N.le_trans(Nat.add(X, T), Nat.add(D0, Y0), Nat.add(D0, X), l1, l2))))

# x - y is exact for y <= x
def hf.sub.nat(+x: U32, +y: U32, h: N.Le(U32.to_nat(y), U32.to_nat(x))) -> {U32.to_nat(U32.sub(x, y)) == Nat.sub(U32.to_nat(x), U32.to_nat(y)) : Nat}:
  match x y:
    case U32{+xw} U32{+yw}:
      +d = Word.sub(32n, xw, yw)
      +X = Word.to_nat(32n, xw)
      +Y0 = Word.to_nat(32n, yw)
      +D0 = Word.to_nat(32n, d)
      +c = PH.H.cout(32n, d, yw, False{})
      +ea = PH.H.adc(32n, d, yw, False{})
      +es = Equal.cong(U32, Nat, z => U32.to_nat(z), U32.add(U32.sub(U32{xw}, U32{yw}), U32{yw}), U32{xw}, hf.U32.subadd(U32{xw}, U32{yw}))
      +es2 = {es : {Word.to_nat(32n, Word.adc(32n, d, yw, False{}, False{})) == X : Nat}}
      hf.sub.nat.go(c, X, Y0, D0, N.D(32n, 1n), Equal.cong(Nat, Nat, z => N.D(32n, z), PH.H.bn(True{}), 1n, {==}), h, hf.word.lt(32n, d),
        Equal.trans(Nat, Nat.add(X, N.D(32n, PH.H.bn(c))), Nat.add(Word.to_nat(32n, Word.adc(32n, d, yw, False{}, False{})), N.D(32n, PH.H.bn(c))),
          Nat.add(D0, Y0),
          Equal.cong(Nat, Nat, z => Nat.add(z, N.D(32n, PH.H.bn(c))), X, Word.to_nat(32n, Word.adc(32n, d, yw, False{}, False{})),
            Equal.sym(Nat, Word.to_nat(32n, Word.adc(32n, d, yw, False{}, False{})), X, es2)), ea))

def hf.DM(-p: Nat, x: Word(p) & U32, +B: Nat, +A0: Nat) -> Data:
  hf.P2({Nat.add(Nat.mul(Word.to_nat(p, hf.dq(p, x)), B), U32.to_nat(hf.dr(p, x))) == A0 : Nat}, N.Le(1n+U32.to_nat(hf.dr(p, x)), B))

def hf.ge.le(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), e: {Cmp.is_ge(c) == True{} : Bool}) -> N.Le(y, x):
  match c:
    case LT{}:
      Empty.absurd(N.Le(y, x), N.false_ne_true(e))
    case EQ{}:
      %r : N.Le(_, x)
      N.le_refl(x)
    case GT{}:
      N.weaken(y, x, r)

def hf.bn.le(a0: Bool, +x: Nat) -> N.Le(Nat.add(PH.H.bn(a0), x), 1n+x):
  match a0:
    case False{}:
      N.le_succ(x, x, N.le_refl(x))
    case True{}:
      N.le_refl(1n+x)

def hf.pout.f(b: Bool, +a0: Bool, +rw: Word(32n), +T: Nat, +eT: {N.D(32n, PH.H.bn(True{})) == T : Nat}, +H: Nat, +eH: {Nat.double(H) == T : Nat},
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
      +l2 = N.le_trans(T, Nat.add(PH.H.bn(a0), Nat.double(R0)), 1n+Nat.double(R0), l1, hf.bn.le(a0, Nat.double(R0)))
      +l3 = N.le_rw_r(2n+Nat.double(R0), Nat.double(H), T, eH, N.double_mono(1n+R0, H, hR))
      Empty.absurd({PH.H.pout(32n, a0, rw) == False{} : Bool}, N.not_succ_le(1n+Nat.double(R0), N.le_trans(2n+Nat.double(R0), T, 1n+Nat.double(R0), l3, l2)))

def hf.alg1(+QB: Nat, +a: Nat, +R: Nat) -> {Nat.add(Nat.double(QB), Nat.add(a, Nat.double(R))) == Nat.add(a, Nat.double(Nat.add(QB, R))) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.double(QB), Nat.add(a, Nat.double(R))), Nat.add(a, Nat.add(Nat.double(QB), Nat.double(R))), Nat.add(a, Nat.double(Nat.add(QB, R))),
    PH.H.add_k(Nat.double(QB), a, Nat.double(R)),
    Equal.cong(Nat, Nat, z => Nat.add(a, z), Nat.add(Nat.double(QB), Nat.double(R)), Nat.double(Nat.add(QB, R)),
      Equal.sym(Nat, Nat.double(Nat.add(QB, R)), Nat.add(Nat.double(QB), Nat.double(R)), N.double_add(QB, R))))

def hf.alg2(+B: Nat, +X: Nat, +S0: Nat, h: N.Le(B, S0)) -> {Nat.add(Nat.add(B, X), Nat.sub(S0, B)) == Nat.add(X, S0) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(B, X), Nat.sub(S0, B)), Nat.add(Nat.add(X, B), Nat.sub(S0, B)), Nat.add(X, S0),
    Equal.cong(Nat, Nat, z => Nat.add(z, Nat.sub(S0, B)), Nat.add(B, X), Nat.add(X, B), hf.add.comm(B, X)),
    Equal.trans(Nat, Nat.add(Nat.add(X, B), Nat.sub(S0, B)), Nat.add(X, Nat.add(B, Nat.sub(S0, B))), Nat.add(X, S0),
      hf.add.assoc(X, B, Nat.sub(S0, B)),
      Equal.cong(Nat, Nat, z => Nat.add(X, z), Nat.add(B, Nat.sub(S0, B)), S0,
        Equal.trans(Nat, Nat.add(B, Nat.sub(S0, B)), Nat.add(Nat.sub(S0, B), B), S0, hf.add.comm(B, Nat.sub(S0, B)), hf.sub.add(S0, B, h)))))

def hf.le.cancel.l(c: Nat, +a: Nat, +b: Nat, h: N.Le(Nat.add(c, a), Nat.add(c, b))) -> N.Le(a, b):
  match c:
    case 0n:
      h
    case 1n+p:
      hf.le.cancel.l(p, a, b, h)

def hf.alg3(+B: Nat, +S0: Nat, h: N.Le(B, S0), h2: N.Le(1n+S0, Nat.add(B, B))) -> N.Le(1n+Nat.sub(S0, B), B):
  +D0 = Nat.sub(S0, B)
  +h3 = N.le_rw_l(1n+S0, Nat.add(B, 1n+D0), Nat.add(B, B),
    Equal.trans(Nat, 1n+S0, 1n+Nat.add(D0, B), Nat.add(B, 1n+D0),
      Equal.cong(Nat, Nat, z => 1n+z, S0, Nat.add(D0, B), Equal.sym(Nat, Nat.add(D0, B), S0, hf.sub.add(S0, B, h))),
      hf.add.comm(1n+D0, B)), h2)
  hf.le.cancel.l(B, 1n+D0, B, h3)

def hf.dbl.add(+x: Nat) -> {Nat.double(x) == Nat.add(x, x) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+(+p):
      Equal.trans(Nat, 2n+Nat.double(p), 2n+Nat.add(p, p), 1n+Nat.add(p, 1n+p),
        Equal.cong(Nat, Nat, z => 2n+z, Nat.double(p), Nat.add(p, p), hf.dbl.add(p)),
        Equal.cong(Nat, Nat, z => 1n+z, 1n+Nat.add(p, p), Nat.add(p, 1n+p), Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), N.add_succ_r(p, p))))

def hf.dm.base(+q: Nat, +q0: Word(q), +S0: Nat, +B: Nat, +a0: Bool, +HI: Nat, +R0: Nat,
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
      Nat.add(PH.H.bn(a0), Nat.double(HI)), hf.alg1(Nat.mul(Q0, B), PH.H.bn(a0), R0),
      Equal.cong(Nat, Nat, z => Nat.add(PH.H.bn(a0), Nat.double(z)), Nat.add(Nat.mul(Q0, B), R0), HI, eih)))

def hf.dm.fin(g: Bool, +q: Nat, +q0: Word(q), +sput: Word(32n), +b: U32, +a0: Bool, +HI: Nat, +R0: Nat,
  +eg: {U32.is_ge(U32{sput}, b) == g : Bool},
  +eih: {Nat.add(Nat.mul(Word.to_nat(q, q0), U32.to_nat(b)), R0) == HI : Nat}, +rih: N.Le(1n+R0, U32.to_nat(b)),
  +eS: {Word.to_nat(32n, sput) == Nat.add(PH.H.bn(a0), Nat.double(R0)) : Nat}) ->
  hf.DM(1n+q, U32.divmod.go.fin(q, q0, U32{sput}, b, g), U32.to_nat(b), Nat.add(PH.H.bn(a0), Nat.double(HI))):
  match g:
    case False{}:
      +B = U32.to_nat(b)
      +S0 = Word.to_nat(32n, sput)
      (hf.dm.base(q, q0, S0, B, a0, HI, R0, eih, eS), PH.H.rel_nge(U32.cmp(U32{sput}, b), S0, B, N.U32.rel(U32{sput}, b), eg))
    case True{}:
      +B = U32.to_nat(b)
      +Q0 = Word.to_nat(q, q0)
      +S0 = Word.to_nat(32n, sput)
      +base = hf.dm.base(q, q0, S0, B, a0, HI, R0, eih, eS)
      +hBS = hf.ge.le(U32.cmp(U32{sput}, b), S0, B, N.U32.rel(U32{sput}, b), eg)
      +esub = hf.sub.nat(U32{sput}, b, hBS)
      +eq = Equal.trans(Nat, Nat.add(Nat.add(B, Nat.mul(Nat.double(Q0), B)), U32.to_nat(U32.sub(U32{sput}, b))),
        Nat.add(Nat.add(B, Nat.mul(Nat.double(Q0), B)), Nat.sub(S0, B)), Nat.add(PH.H.bn(a0), Nat.double(HI)),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.add(B, Nat.mul(Nat.double(Q0), B)), z), U32.to_nat(U32.sub(U32{sput}, b)), Nat.sub(S0, B), esub),
        Equal.trans(Nat, Nat.add(Nat.add(B, Nat.mul(Nat.double(Q0), B)), Nat.sub(S0, B)), Nat.add(Nat.mul(Nat.double(Q0), B), S0),
          Nat.add(PH.H.bn(a0), Nat.double(HI)), hf.alg2(B, Nat.mul(Nat.double(Q0), B), S0, hBS), base))
      +h2 = N.le_rw_r(1n+S0, Nat.double(B), Nat.add(B, B), hf.dbl.add(B),
        N.le_trans(1n+S0, 2n+Nat.double(R0), Nat.double(B),
          N.le_rw_l(1n+Nat.add(PH.H.bn(a0), Nat.double(R0)), 1n+S0, 2n+Nat.double(R0),
            Equal.cong(Nat, Nat, z => 1n+z, Nat.add(PH.H.bn(a0), Nat.double(R0)), S0, Equal.sym(Nat, S0, Nat.add(PH.H.bn(a0), Nat.double(R0)), eS)),
            hf.bn.le(a0, Nat.double(R0))),
          N.double_mono(1n+R0, B, rih)))
      +lt = N.le_rw_l(1n+Nat.sub(S0, B), 1n+U32.to_nat(U32.sub(U32{sput}, b)), B,
        Equal.cong(Nat, Nat, z => 1n+z, Nat.sub(S0, B), U32.to_nat(U32.sub(U32{sput}, b)), Equal.sym(Nat, U32.to_nat(U32.sub(U32{sput}, b)), Nat.sub(S0, B), esub)),
        hf.alg3(B, S0, hBS, h2))
      (eq, lt)

def hf.dm.rec(+q: Nat, +a0: Bool, +b: U32, x: Word(q) & U32, +HI: Nat, +T: Nat, +eT: {N.D(32n, PH.H.bn(True{})) == T : Nat},
  +H: Nat, +eH: {Nat.double(H) == T : Nat}, +hb: N.Le(U32.to_nat(b), H), ih: hf.DM(q, x, U32.to_nat(b), HI)) ->
  hf.DM(1n+q, U32.divmod.go.rec(q, a0, b, x), U32.to_nat(b), Nat.add(PH.H.bn(a0), Nat.double(HI))):
  match x:
    case Tuple{+q0, +r0}:
      match r0:
        case U32{+rw}:
          (+eih, +rih) = ih
          +R0 = Word.to_nat(32n, rw)
          +sput = Word.shl.put(32n, a0, rw)
          +B = U32.to_nat(b)
          +hR = N.le_trans(1n+R0, B, H, rih, hb)
          +pf = hf.pout.f(PH.H.pout(32n, a0, rw), a0, rw, T, eT, H, eH, hR, {==})
          +ep = PH.H.put(32n, a0, rw)
          +ep0 = {(%pf :
              {Nat.add(Word.to_nat(32n, sput), N.D(32n, PH.H.bn(_))) == Nat.add(PH.H.bn(a0), Nat.double(R0)) : Nat}; ep) :
            {Nat.add(Word.to_nat(32n, sput), N.D(32n, PH.H.bn(False{}))) == Nat.add(PH.H.bn(a0), Nat.double(R0)) : Nat}}
          +eS = Equal.trans(Nat, Word.to_nat(32n, sput), Nat.add(Word.to_nat(32n, sput), 0n), Nat.add(PH.H.bn(a0), Nat.double(R0)),
            Equal.sym(Nat, Nat.add(Word.to_nat(32n, sput), 0n), Word.to_nat(32n, sput), N.add_zero(Word.to_nat(32n, sput))), ep0)
          %Equal.sym(Bool & Word(32n), Word.shl.out(32n, a0, rw), (PH.H.pout(32n, a0, rw), sput), hf.out.put(32n, a0, rw)) :
            hf.DM(1n+q, U32.divmod.go.shl(q, q0, b, _), B, Nat.add(PH.H.bn(a0), Nat.double(HI)))
          %Equal.sym(Bool, PH.H.pout(32n, a0, rw), False{}, pf) :
            hf.DM(1n+q, U32.divmod.go.fin(q, q0, U32{sput}, b, Bool.or(_, U32.is_ge(U32{sput}, b))), B, Nat.add(PH.H.bn(a0), Nat.double(HI)))
          hf.dm.fin(U32.is_ge(U32{sput}, b), q, q0, sput, b, a0, HI, R0, {==}, eih, rih, eS)

# the long division of a by b, for 1 <= b <= 2^31
def hf.dm(+p: Nat, +a: Word(p), +b: U32, +T: Nat, +eT: {N.D(32n, PH.H.bn(True{})) == T : Nat},
  +H: Nat, +eH: {Nat.double(H) == T : Nat}, +hb: N.Le(U32.to_nat(b), H), +hb1: N.Le(1n, U32.to_nat(b))) ->
  hf.DM(p, U32.divmod.go(p, a, b), U32.to_nat(b), Word.to_nat(p, a)):
  match p a:
    case 0n WNil{}:
      ({==}, hb1)
    case 1n+q WCon{+a0, +hi}:
      %Equal.sym(Nat, Word.to_nat(1n+q, WCon{a0, hi}), Nat.add(PH.H.bn(a0), Nat.double(Word.to_nat(q, hi))), hf.wt(q, a0, hi)) :
        hf.DM(1n+q, U32.divmod.go.rec(q, a0, b, U32.divmod.go(q, hi, b)), U32.to_nat(b), _)
      hf.dm.rec(q, a0, b, U32.divmod.go(q, hi, b), Word.to_nat(q, hi), T, eT, H, eH, hb, hf.dm(q, hi, b, T, eT, H, eH, hb, hb1))

def hf.dsucc(+k: Nat, +x: Nat) -> {N.D(1n+k, x) == Nat.double(N.D(k, x)) : Nat}:
  {==}

def hf.mul20(+q: Nat) -> {Nat.mul(q, 20n) == PH.H.t20(q) : Nat}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 20n+z, Nat.mul(p, 20n), PH.H.t20(p), hf.mul20(p))

def hf.div.dq(x: Word(32n) & U32) -> {U32.div.fin(x) == U32{hf.dq(32n, x)} : U32}:
  match x:
    case Tuple{q, r}:
      {==}

# x / 20 by its parts: 20 q <= x <= 19 + 20 q
def hf.div.of(+xw: Word(32n), d: hf.DM(32n, U32.divmod.go(32n, xw, 20), U32.to_nat(20), Word.to_nat(32n, xw))) ->
  hf.P2(N.Le(PH.H.t20(U32.to_nat(U32.div(U32{xw}, 20))), U32.to_nat(U32{xw})),
    N.Le(U32.to_nat(U32{xw}), 19n+PH.H.t20(U32.to_nat(U32.div(U32{xw}, 20))))):
  (+eq, +lt) = d
  +Q = Word.to_nat(32n, hf.dq(32n, U32.divmod.go(32n, xw, 20)))
  +R = U32.to_nat(hf.dr(32n, U32.divmod.go(32n, xw, 20)))
  +X = Word.to_nat(32n, xw)
  +eQ = Equal.trans(Nat, U32.to_nat(U32.div(U32{xw}, 20)), U32.to_nat(U32{hf.dq(32n, U32.divmod.go(32n, xw, 20))}), Q,
    Equal.cong(U32, Nat, z => U32.to_nat(z), U32.div.fin(U32.divmod.go(32n, xw, 20)), U32{hf.dq(32n, U32.divmod.go(32n, xw, 20))},
      hf.div.dq(U32.divmod.go(32n, xw, 20))),
    N.u32_to_nat(hf.dq(32n, U32.divmod.go(32n, xw, 20))))
  +e2 = Equal.trans(Nat, Nat.add(PH.H.t20(Q), R), Nat.add(Nat.mul(Q, 20n), R), X,
    Equal.cong(Nat, Nat, z => Nat.add(z, R), PH.H.t20(Q), Nat.mul(Q, 20n), Equal.sym(Nat, Nat.mul(Q, 20n), PH.H.t20(Q), hf.mul20(Q))), eq)
  +lo = N.le_rw_r(PH.H.t20(Q), Nat.add(PH.H.t20(Q), R), X, e2, N.le_add_r(PH.H.t20(Q), R))
  +hi0 = N.add_mono(PH.H.t20(Q), PH.H.t20(Q), R, 19n, N.le_refl(PH.H.t20(Q)), lt)
  +hi1 = N.le_rw_r(Nat.add(PH.H.t20(Q), R), Nat.add(PH.H.t20(Q), 19n), 19n+PH.H.t20(Q), hf.add.comm(PH.H.t20(Q), 19n), hi0)
  +hi = N.le_rw_l(Nat.add(PH.H.t20(Q), R), X, 19n+PH.H.t20(Q), e2, hi1)
  %Equal.sym(Nat, U32.to_nat(U32.div(U32{xw}, 20)), Q, eQ) :
    hf.P2(N.Le(PH.H.t20(_), U32.to_nat(U32{xw})), N.Le(U32.to_nat(U32{xw}), 19n+PH.H.t20(_)))
  (lo, hi)

def hf.div(+x: U32) -> hf.P2(N.Le(PH.H.t20(U32.to_nat(U32.div(x, 20))), U32.to_nat(x)),
    N.Le(U32.to_nat(x), 19n+PH.H.t20(U32.to_nat(U32.div(x, 20))))):
  match x:
    case U32{+xw}:
      hf.div.of(xw, hf.dm(32n, xw, 20, N.D(32n, 1n), Equal.cong(Nat, Nat, z => N.D(32n, z), PH.H.bn(True{}), 1n, {==}), N.D(31n, 1n),
        Equal.sym(Nat, N.D(32n, 1n), Nat.double(N.D(31n, 1n)), hf.dsucc(31n, 1n)), Unit{}, Unit{}))

# Numbers
# -------

# 20 x <= 32 x
def hf.t20.D5(x: Nat) -> N.Le(PH.H.t20(x), N.D(5n, x)):
  match x:
    case 0n:
      Unit{}
    case 1n+(+p):
      N.le_trans(PH.H.t20(p), N.D(5n, p), 12n+N.D(5n, p), hf.t20.D5(p), N.le_add_l(12n, N.D(5n, p)))

# x <= y, or y < x
def hf.cmp(x: Nat, y: Nat, -G: Type, kl: N.Le(x, y) -> G, kg: N.Le(1n+y, x) -> G) -> G:
  match x y:
    case 0n _:
      kl(N.le_zero(y))
    case 1n+a 0n:
      kg(N.le_zero(a))
    case 1n+a 1n+b:
      hf.cmp(a, b, G, kl, kg)

# 4 + t <= t is false
def hf.no4(+t: Nat, h: N.Le(4n+t, t)) -> Empty:
  N.not_succ_le(t, N.le_trans(1n+t, 4n+t, t, N.le_add_l(3n, 1n+t), h))

def hf.big.gt(+X: Nat, +P: Nat, +Y: Nat, eY: {N.D(6n, X) == Y : Nat}, hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == Y : Nat},
  h: N.Le(1n+P, X)) -> Empty:
  +a = PH.H.t20_mono(1n+P, X, h)
  +b = N.le_trans(PH.H.t20(1n+P), PH.H.t20(X), N.D(6n, X), a,
    N.le_trans(PH.H.t20(X), N.D(5n, X), N.D(6n, X), hf.t20.D5(X), PG.le_double(N.D(5n, X))))
  +c = N.le_rw_r(PH.H.t20(1n+P), N.D(6n, X), Nat.add(PH.H.W(4n), PH.H.t20(P)),
    Equal.trans(Nat, N.D(6n, X), Y, Nat.add(PH.H.W(4n), PH.H.t20(P)), eY, Equal.sym(Nat, Nat.add(PH.H.W(4n), PH.H.t20(P)), Y, hP)), b)
  hf.no4(PH.H.t20(P), c)

# 2^6 X = 2^4 + 20 P gives X <= P
def hf.big(+X: Nat, +P: Nat, +Y: Nat, eY: {N.D(6n, X) == Y : Nat}, hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == Y : Nat}) -> N.Le(X, P):
  hf.cmp(X, P, N.Le(X, P), h => h, h => Empty.absurd(N.Le(X, P), hf.big.gt(X, P, Y, eY, hP, h)))

def hf.eY(+a: Nat, +b: Nat, +c: Nat, e: {Nat.add(a, b) == c : Nat}) -> {N.D(a, N.D(b, 1n)) == PH.H.W(c) : Nat}:
  N.D_add(a, b, c, 1n, e)

# 2^26 <= 214748364
def hf.M.le() -> N.Le(U32.to_nat(67108864), PH.H.pat(7n)):
  N.le_rw_l(N.D(26n, 1n), U32.to_nat(67108864), PH.H.pat(7n), Equal.sym(Nat, U32.to_nat(67108864), N.D(26n, 1n), PG.val_M2()),
    hf.big(N.D(26n, 1n), PH.H.pat(7n), PH.H.W(32n), hf.eY(6n, 26n, 32n, {==}), PH.H.hP()))

# Cir.at(c) = 20 c, for c <= P
def hf.at.val(+c: U32, +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +hx: N.Le(U32.to_nat(c), P)) ->
  {U32.to_nat(C.Cir.at(c)) == PH.H.t20(U32.to_nat(c)) : Nat}:
  match c:
    case U32{+w}:
      PH.H.tex_w(32n, w, P, hP, hx)

# k + 1, exact below 2^26
def hf.inc(+k: U32, hkM: N.Le(1n+U32.to_nat(k), U32.to_nat(67108864))) -> {U32.to_nat(U32.inc(k)) == 1n+U32.to_nat(k) : Nat}:
  PI.U32.inc_nat(k, Equal.sym(Bool, U32.is_zero(U32.inc(k)), False{}, MO.nz(k, 67108864, hkM)))

# 1 + t <= e gives t <= e - 1
def hf.le.pred(+t: Nat, +e: Nat, h: N.Le(1n+t, e)) -> N.Le(t, Nat.sub(e, 1n)):
  match e:
    case 0n:
      Empty.absurd(N.Le(t, Nat.sub(0n, 1n)), h)
    case 1n+(+q):
      N.le_rw_r(t, q, Nat.sub(1n+q, 1n), Equal.sym(Nat, Nat.sub(q, 0n), q, hf.sub0(q)), h)

# 1 + q <= 20 q, for 1 <= q
def hf.q.t20(+Q: Nat, hq: N.Le(1n, Q)) -> N.Le(1n+Q, PH.H.t20(Q)):
  match Q:
    case 0n:
      Empty.absurd(N.Le(1n, PH.H.t20(0n)), hq)
    case 1n+(+q):
      N.le_trans(q, PH.H.t20(q), 18n+PH.H.t20(q), PH.H.le_t20(q), N.le_add_l(18n, PH.H.t20(q)))

# 20 q <= x < T = 1 + Mx gives 1 + q <= Mx, for 1 <= q
def hf.qmax(+Q: Nat, +Xn: Nat, +T: Nat, +Mx: Nat, h1: N.Le(PH.H.t20(Q), Xn), h2: N.Le(1n+Xn, T), e: {1n+Mx == T : Nat},
  hq: N.Le(1n, Q)) -> N.Le(1n+Q, Mx):
  +a = N.le_trans(1n+PH.H.t20(Q), 1n+Xn, T, h1, h2)
  +b = N.le_rw_r(1n+PH.H.t20(Q), T, 1n+Mx, Equal.sym(Nat, 1n+Mx, T, e), a)
  N.le_trans(1n+Q, PH.H.t20(Q), Mx, hf.q.t20(Q, hq), b)

# The first cell
# --------------

def hf.first.t(+k: U32, +first: U32, h363: N.Le(363n, U32.to_nat(k)), hkM: N.Le(1n+U32.to_nat(k), U32.to_nat(67108864)),
  ef: {first == U32.inc(k) : U32}) -> N.Le(345n, U32.to_nat(first)):
  +e = Equal.trans(Nat, 1n+U32.to_nat(k), U32.to_nat(U32.inc(k)), U32.to_nat(first),
    Equal.sym(Nat, U32.to_nat(U32.inc(k)), 1n+U32.to_nat(k), hf.inc(k, hkM)),
    Equal.cong(U32, Nat, z => U32.to_nat(z), U32.inc(k), first, Equal.sym(U32, first, U32.inc(k), ef)))
  N.le_rw_r(345n, 1n+U32.to_nat(k), U32.to_nat(first), e,
    N.le_trans(345n, 363n, 1n+U32.to_nat(k), Unit{}, N.le_succ(363n, U32.to_nat(k), h363)))

def hf.first.f(+k: U32, +E: U32, +first: U32, h363: N.Le(363n, U32.to_nat(k)), hkM: N.Le(1n+U32.to_nat(k), U32.to_nat(67108864)),
  eb: {U32.is_ge(C.Cir.at(U32.inc(k)), E) == False{} : Bool},
  ef: {first == U32.inc(U32.div(U32.sub(E, 1), 20)) : U32}) -> N.Le(345n, U32.to_nat(first)):
  +n = U32.to_nat(k)
  +A = C.Cir.at(U32.inc(k))
  +hlt = PH.H.rel_nge(U32.cmp(A, E), U32.to_nat(A), U32.to_nat(E), N.U32.rel(A, E), eb)
  +ei = hf.inc(k, hkM)
  +hx = N.le_rw_l(1n+n, U32.to_nat(U32.inc(k)), PH.H.pat(7n), Equal.sym(Nat, U32.to_nat(U32.inc(k)), 1n+n, ei),
    N.le_trans(1n+n, U32.to_nat(67108864), PH.H.pat(7n), hkM, hf.M.le()))
  +eA = hf.at.val(U32.inc(k), PH.H.pat(7n), PH.H.hP(), hx)
  +eA2 = Equal.trans(Nat, U32.to_nat(A), PH.H.t20(U32.to_nat(U32.inc(k))), PH.H.t20(1n+n), eA,
    Equal.cong(Nat, Nat, z => PH.H.t20(z), U32.to_nat(U32.inc(k)), 1n+n, ei))
  +h1 = N.le_rw_l(1n+U32.to_nat(A), 1n+PH.H.t20(1n+n), U32.to_nat(E), Equal.cong(Nat, Nat, z => 1n+z, U32.to_nat(A), PH.H.t20(1n+n), eA2), hlt)
  +X = U32.sub(E, 1)
  +hE1 = N.le_trans(U32.to_nat(1), 1n+PH.H.t20(1n+n), U32.to_nat(E), N.le_zero(PH.H.t20(1n+n)), h1)
  +eX = hf.sub.nat(E, 1, hE1)
  +h2 = hf.le.pred(PH.H.t20(1n+n), U32.to_nat(E), h1)
  +h3 = N.le_rw_r(PH.H.t20(1n+n), Nat.sub(U32.to_nat(E), 1n), U32.to_nat(X), Equal.sym(Nat, U32.to_nat(X), Nat.sub(U32.to_nat(E), U32.to_nat(1)), eX), h2)
  +D = U32.div(X, 20)
  +Q = U32.to_nat(D)
  +dv = hf.div(X)
  +lo = hf.fst(N.Le(PH.H.t20(Q), U32.to_nat(X)), N.Le(U32.to_nat(X), 19n+PH.H.t20(Q)), dv)
  +hi = hf.snd(N.Le(PH.H.t20(Q), U32.to_nat(X)), N.Le(U32.to_nat(X), 19n+PH.H.t20(Q)), dv)
  +h4 = N.le_trans(PH.H.t20(1n+n), U32.to_nat(X), 19n+PH.H.t20(Q), h3, hi)
  +hQ = PH.H.t20_lt(1n+n, 1n+Q, h4)
  +hq1 = N.le_trans(1n, 1n+n, Q, N.le_zero(n), hQ)
  +hmax = hf.qmax(Q, U32.to_nat(X), N.D(32n, 1n), U32.to_nat(4294967295), lo, hf.u32.lt(X), MO.val_MAX(), hq1)
  +eD = PI.U32.inc_nat(D, Equal.sym(Bool, U32.is_zero(U32.inc(D)), False{}, MO.nz(D, 4294967295, hmax)))
  +e = Equal.trans(Nat, 1n+Q, U32.to_nat(U32.inc(D)), U32.to_nat(first), Equal.sym(Nat, U32.to_nat(U32.inc(D)), 1n+Q, eD),
    Equal.cong(U32, Nat, z => U32.to_nat(z), U32.inc(D), first, Equal.sym(U32, first, U32.inc(D), ef)))
  N.le_rw_r(345n, 1n+Q, U32.to_nat(first), e,
    N.le_trans(345n, 363n, 1n+Q, Unit{}, N.le_trans(363n, n, 1n+Q, h363,
      N.le_trans(n, 1n+n, 1n+Q, N.le_succ(n, n, N.le_refl(n)), N.le_succ(1n+n, Q, hQ)))))

def hf.first.of(b: Bool, +k: U32, +E: U32, +first: U32, h363: N.Le(363n, U32.to_nat(k)), hkM: N.Le(1n+U32.to_nat(k), U32.to_nat(67108864)),
  eb: {U32.is_ge(C.Cir.at(U32.inc(k)), E) == b : Bool},
  ef: {first == Bool.pick(U32, b, U32.inc(k), U32.inc(U32.div(U32.sub(E, 1), 20))) : U32}) -> N.Le(345n, U32.to_nat(first)):
  match b:
    case True{}:
      hf.first.t(k, first, h363, hkM, ef)
    case False{}:
      hf.first.f(k, E, first, h363, hkM, eb, ef)

# the first cell, Cir.first(k, 20 (k + 1) + len), is at least 345, for
# 363 <= k < 2^26
def hf.first(+k: U32, +len: U32, +first: U32, h363: N.Le(363n, U32.to_nat(k)), hkM: N.Le(1n+U32.to_nat(k), U32.to_nat(67108864)),
  ef: {first == C.Cir.first(k, U32.add(C.Cir.input.at(k), len)) : U32}) -> N.Le(345n, U32.to_nat(first)):
  hf.first.of(U32.is_ge(C.Cir.at(U32.inc(k)), U32.add(C.Cir.input.at(k), len)), k, U32.add(C.Cir.input.at(k), len), first, h363, hkM, {==}, ef)

# The image's size
# ----------------

def hf.enc_len(xs: List<&2, C.Cir.Cell>) -> {U32.from_nat(List.length(&2, C.Cir.Cell, xs)) == C.Wasm.encode.len(C.Cir.Cell, xs) : U32}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, r}:
      Equal.cong(U32, U32, y => U32.inc(y), U32.from_nat(List.length(&2, C.Cir.Cell, r)), C.Wasm.encode.len(C.Cir.Cell, r), hf.enc_len(r))

# the image of a book of fewer than 2^26 bytes has fewer than 2^26 cells
def hf.hsm(+p: List<&2, U32>, +ds: List<&2, C.Def>, rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  small: {C.Img.small(p, 0) == True{} : Bool}) -> N.Le(1n+List.length(&2, C.Cir.Cell, C.Img.cells(ds)), U32.to_nat(67108864)):
  MO.lt_le(List.length(&2, C.Cir.Cell, C.Img.cells(ds)), U32.to_nat(67108864), PG.img.small.nat(p, ds, rd, small))

# k, the image's size, as a Nat
def hf.k.nat(+ds: List<&2, C.Def>, +k: U32, ek: {k == C.Wasm.encode.len(C.Cir.Cell, C.Img.cells(ds)) : U32},
  hsm: N.Le(1n+List.length(&2, C.Cir.Cell, C.Img.cells(ds)), U32.to_nat(67108864))) ->
  {U32.to_nat(k) == List.length(&2, C.Cir.Cell, C.Img.cells(ds)) : Nat}:
  +n = List.length(&2, C.Cir.Cell, C.Img.cells(ds))
  Equal.trans(Nat, U32.to_nat(k), U32.to_nat(U32.from_nat(n)), n,
    Equal.cong(U32, Nat, z => U32.to_nat(z), k, U32.from_nat(n),
      Equal.trans(U32, k, C.Wasm.encode.len(C.Cir.Cell, C.Img.cells(ds)), U32.from_nat(n), ek,
        Equal.sym(U32, U32.from_nat(n), C.Wasm.encode.len(C.Cir.Cell, C.Img.cells(ds)), hf.enc_len(C.Img.cells(ds))))),
    MO.tofrom(n, 67108864, N.weaken(n, U32.to_nat(67108864), hsm)))

# 363 <= k
def hf.k363(+ds: List<&2, C.Def>, +k: U32, ek: {k == C.Wasm.encode.len(C.Cir.Cell, C.Img.cells(ds)) : U32},
  hsm: N.Le(1n+List.length(&2, C.Cir.Cell, C.Img.cells(ds)), U32.to_nat(67108864))) -> N.Le(363n, U32.to_nat(k)):
  N.le_rw_r(363n, Nat.add(363n, PG.Bl(ds, 0n)), U32.to_nat(k),
    Equal.sym(Nat, U32.to_nat(k), Nat.add(363n, PG.Bl(ds, 0n)),
      Equal.trans(Nat, U32.to_nat(k), List.length(&2, C.Cir.Cell, C.Img.cells(ds)), Nat.add(363n, PG.Bl(ds, 0n)), hf.k.nat(ds, k, ek, hsm), PG.cells_len(ds))),
    N.le_add_r(363n, PG.Bl(ds, 0n)))

# k < 2^26
def hf.kM(+ds: List<&2, C.Def>, +k: U32, ek: {k == C.Wasm.encode.len(C.Cir.Cell, C.Img.cells(ds)) : U32},
  +hsm: N.Le(1n+List.length(&2, C.Cir.Cell, C.Img.cells(ds)), U32.to_nat(67108864))) -> N.Le(1n+U32.to_nat(k), U32.to_nat(67108864)):
  N.le_rw_l(1n+List.length(&2, C.Cir.Cell, C.Img.cells(ds)), 1n+U32.to_nat(k), U32.to_nat(67108864),
    Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, C.Cir.Cell, C.Img.cells(ds)), U32.to_nat(k),
      Equal.sym(Nat, U32.to_nat(k), List.length(&2, C.Cir.Cell, C.Img.cells(ds)), hf.k.nat(ds, k, ek, hsm))), hsm)

# hF: the first cell is past the table, from what Cir.result computed
def hf.hF(+p: List<&2, U32>, +ds: List<&2, C.Def>, +k: U32, +len: U32, +first: U32,
  rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>}, small: {C.Img.small(p, 0) == True{} : Bool},
  +ek: {k == C.Wasm.encode.len(C.Cir.Cell, C.Img.cells(ds)) : U32},
  ef: {first == C.Cir.first(k, U32.add(C.Cir.input.at(k), len)) : U32}) -> N.Le(345n, U32.to_nat(first)):
  +hsm = hf.hsm(p, ds, rd, small)
  hf.first(k, len, first, hf.k363(ds, k, ek, hsm), hf.kM(ds, k, ek, hsm), ef)
