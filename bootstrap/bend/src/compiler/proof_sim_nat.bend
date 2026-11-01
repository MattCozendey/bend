# compiler: numbers of the simulation
# ===================================
#
# U32.from_nat after U32.to_nat is the identity (from.to); inc^j(c), the
# address j bytes after c, is from_nat(j) + c (incn.add); the sum of two
# from_nat is the from_nat of the sum (add.from). The comparisons of U32s
# say how their numbers compare (le.of, lt.of, nz.of).

import Base
import ./impl.bend as C
import ./proof_need.bend as N
import ./proof_halt.bend as PH
import ./proof_valid.bend as V
import ./proof_sim_mem.bend as Y
import ./proof_instrs.bend as I

# From Nat to words
# -----------------

# the word of n bits of k (mod 2^n)
def W.fromn(+n: Nat, k: Nat) -> Word(n):
  match k:
    case 0n:
      Word.zero(n)
    case 1n+j:
      Word.inc(n, W.fromn(n, j))

def fromn.double(+p: Nat, +k: Nat) -> {W.fromn(1n+p, Nat.double(k)) == WCon{False{}, W.fromn(p, k)} : Word(1n+p)}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      Equal.cong(Word(1n+p), Word(1n+p), z => Word.inc(1n+p, Word.inc(1n+p, z)), W.fromn(1n+p, Nat.double(j)),
        WCon{False{}, W.fromn(p, j)}, fromn.double(p, j))

def fromn.odd(+p: Nat, +k: Nat) -> {W.fromn(1n+p, 1n+Nat.double(k)) == WCon{True{}, W.fromn(p, k)} : Word(1n+p)}:
  Equal.cong(Word(1n+p), Word(1n+p), z => Word.inc(1n+p, z), W.fromn(1n+p, Nat.double(k)),
    WCon{False{}, W.fromn(p, k)}, fromn.double(p, k))

# the word of the number of w is w
def fromn.to(+n: Nat, +w: Word(n)) -> {W.fromn(n, Word.to_nat(n, w)) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          Equal.trans(Word(1n+p), W.fromn(1n+p, Nat.double(Word.to_nat(p, t))), WCon{False{}, W.fromn(p, Word.to_nat(p, t))}, WCon{False{}, t},
            fromn.double(p, Word.to_nat(p, t)),
            Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, W.fromn(p, Word.to_nat(p, t)), t, fromn.to(p, t)))
        case WCon{True{}, +t}:
          Equal.trans(Word(1n+p), W.fromn(1n+p, 1n+Nat.double(Word.to_nat(p, t))), WCon{True{}, W.fromn(p, Word.to_nat(p, t))}, WCon{True{}, t},
            fromn.odd(p, Word.to_nat(p, t)),
            Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, W.fromn(p, Word.to_nat(p, t)), t, fromn.to(p, t)))

def from.w(+k: Nat) -> {U32.from_nat(k) == U32{W.fromn(32n, k)} : U32}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      Equal.cong(U32, U32, z => U32.inc(z), U32.from_nat(j), U32{W.fromn(32n, j)}, from.w(j))

# from_nat(to_nat(x)) = x
def from.to(+x: U32) -> {U32.from_nat(U32.to_nat(x)) == x : U32}:
  match x:
    case U32{+w}:
      Equal.trans(U32, U32.from_nat(Word.to_nat(32n, w)), U32{W.fromn(32n, Word.to_nat(32n, w))}, U32{w},
        from.w(Word.to_nat(32n, w)),
        Equal.cong(Word(32n), U32, z => U32{z}, W.fromn(32n, Word.to_nat(32n, w)), w, fromn.to(32n, w)))

# Sums
# ----

# 0 + c = c
def zero.add(+c: U32) -> {U32.add(0, c) == c : U32}:
  Equal.trans(U32, U32.add(0, c), U32.add(c, 0), c, U32.add_comm(0, c), Y.U32.add_zero(c))

# (x + 1) + c = (x + c) + 1
def inc.add(+x: U32, +c: U32) -> {U32.add(U32.inc(x), c) == U32.inc(U32.add(x, c)) : U32}:
  Equal.trans(U32, U32.add(U32.inc(x), c), U32.add(c, U32.inc(x)), U32.inc(U32.add(x, c)), U32.add_comm(U32.inc(x), c),
    Equal.trans(U32, U32.add(c, U32.inc(x)), U32.inc(U32.add(c, x)), U32.inc(U32.add(x, c)), V.add.inc(c, x),
      Equal.cong(U32, U32, z => U32.inc(z), U32.add(c, x), U32.add(x, c), U32.add_comm(c, x))))

# j steps after c
def incn(j: Nat, +c: U32) -> U32:
  match j:
    case 0n:
      c
    case 1n+p:
      incn(p, U32.inc(c))

# j steps after c is j + c
def incn.add(+j: Nat, +c: U32) -> {incn(j, c) == U32.add(U32.from_nat(j), c) : U32}:
  match j:
    case 0n:
      Equal.sym(U32, U32.add(0, c), c, zero.add(c))
    case 1n+p:
      Equal.trans(U32, incn(p, U32.inc(c)), U32.add(U32.from_nat(p), U32.inc(c)), U32.add(U32.inc(U32.from_nat(p)), c),
        incn.add(p, U32.inc(c)),
        Equal.trans(U32, U32.add(U32.from_nat(p), U32.inc(c)), U32.inc(U32.add(U32.from_nat(p), c)), U32.add(U32.inc(U32.from_nat(p)), c),
          V.add.inc(U32.from_nat(p), c), Equal.sym(U32, U32.add(U32.inc(U32.from_nat(p)), c), U32.inc(U32.add(U32.from_nat(p), c)),
            inc.add(U32.from_nat(p), c))))

# from_nat(x) + from_nat(y) = from_nat(x + y)
def add.from(+x: Nat, +y: Nat) -> {U32.add(U32.from_nat(x), U32.from_nat(y)) == U32.from_nat(Nat.add(x, y)) : U32}:
  match x:
    case 0n:
      zero.add(U32.from_nat(y))
    case 1n+p:
      Equal.trans(U32, U32.add(U32.inc(U32.from_nat(p)), U32.from_nat(y)), U32.inc(U32.add(U32.from_nat(p), U32.from_nat(y))),
        U32.inc(U32.from_nat(Nat.add(p, y))), inc.add(U32.from_nat(p), U32.from_nat(y)),
        Equal.cong(U32, U32, z => U32.inc(z), U32.add(U32.from_nat(p), U32.from_nat(y)), U32.from_nat(Nat.add(p, y)), add.from(p, y)))

# (x - f) + f = x, for f <= x
def sub.add(+x: Nat, +f: Nat, h: N.Le(f, x)) -> {Nat.add(Nat.sub(x, f), f) == x : Nat}:
  match x f:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.add(Nat.sub(0n, 1n+q), 1n+q) == 0n : Nat}, h)
    case 1n+p 0n:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 0n), p, N.add_zero(p))
    case 1n+p 1n+q:
      Equal.trans(Nat, Nat.add(Nat.sub(p, q), 1n+q), 1n+Nat.add(Nat.sub(p, q), q), 1n+p, N.add_succ_r(Nat.sub(p, q), q),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.sub(p, q), q), p, sub.add(p, q, h)))

# the cell i, as i - f steps after f, for f <= i
def incn.sub(+i: U32, +f: U32, h: N.Le(U32.to_nat(f), U32.to_nat(i))) ->
  {incn(Nat.sub(U32.to_nat(i), U32.to_nat(f)), f) == i : U32}:
  +J = Nat.sub(U32.to_nat(i), U32.to_nat(f))
  Equal.trans(U32, incn(J, f), U32.add(U32.from_nat(J), f), i, incn.add(J, f),
    Equal.trans(U32, U32.add(U32.from_nat(J), f), U32.add(U32.from_nat(J), U32.from_nat(U32.to_nat(f))), i,
      Equal.cong(U32, U32, z => U32.add(U32.from_nat(J), z), f, U32.from_nat(U32.to_nat(f)), Equal.sym(U32, U32.from_nat(U32.to_nat(f)), f, from.to(f))),
      Equal.trans(U32, U32.add(U32.from_nat(J), U32.from_nat(U32.to_nat(f))), U32.from_nat(Nat.add(J, U32.to_nat(f))), i,
        add.from(J, U32.to_nat(f)),
        Equal.trans(U32, U32.from_nat(Nat.add(J, U32.to_nat(f))), U32.from_nat(U32.to_nat(i)), i,
          Equal.cong(Nat, U32, z => U32.from_nat(z), Nat.add(J, U32.to_nat(f)), U32.to_nat(i), sub.add(U32.to_nat(i), U32.to_nat(f), h)),
          from.to(i)))))

# the cell i, as i - 1 steps after 1, for 1 <= i
def incn.one(+i: U32, h: N.Le(1n, U32.to_nat(i))) -> {incn(Nat.sub(U32.to_nat(i), 1n), 1) == i : U32}:
  incn.sub(i, 1, h)

# Comparisons
# -----------

def rel.le(+c: Cmp, +x: Nat, +y: Nat, h: N.Rel(c, x, y), e: {Cmp.is_le(c) == True{} : Bool}) -> N.Le(x, y):
  N.rel_le(c, x, y, h, N.toT(Cmp.is_le(c), e))

def rel.lt(c: Cmp, +x: Nat, +y: Nat, h: N.Rel(c, x, y), e: {Cmp.is_lt(c) == True{} : Bool}) -> N.Le(1n+x, y):
  match c:
    case LT{}:
      h
    case EQ{}:
      Empty.absurd(N.Le(1n+x, y), N.false_ne_true(e))
    case GT{}:
      Empty.absurd(N.Le(1n+x, y), N.false_ne_true(e))

def rel.ne0(c: Cmp, +x: Nat, h: N.Rel(c, x, 0n), e: {Cmp.is_eq(c) == False{} : Bool}) -> N.Le(1n, x):
  match c:
    case LT{}:
      Empty.absurd(N.Le(1n, x), h)
    case EQ{}:
      Empty.absurd(N.Le(1n, x), N.true_ne_false(e))
    case GT{}:
      h

# a <= b on U32 is a <= b on their numbers
def le.of(+a: U32, +b: U32, e: {U32.is_le(a, b) == True{} : Bool}) -> N.Le(U32.to_nat(a), U32.to_nat(b)):
  rel.le(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), e)

def lt.of(+a: U32, +b: U32, e: {U32.is_lt(a, b) == True{} : Bool}) -> N.Le(1n+U32.to_nat(a), U32.to_nat(b)):
  rel.lt(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), e)

# a U32 that is not 0 is at least 1
def nz.of(+a: U32, e: {U32.is_zero(a) == False{} : Bool}) -> N.Le(1n, U32.to_nat(a)):
  rel.ne0(U32.cmp(a, 0), U32.to_nat(a), N.U32.rel(a, 0), e)

# Bool
# ----

def not.t(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, N.false_ne_true(e))

def or.r(b: Bool, +c: Bool, e: {Bool.or(b, c) == True{} : Bool}, n: {b == False{} : Bool}) -> {c == True{} : Bool}:
  match b:
    case False{}:
      e
    case True{}:
      Empty.absurd({c == True{} : Bool}, N.true_ne_false(n))

# Nat algebra
# -----------

def add.comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, N.add_zero(b))
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, b), Nat.add(b, p), add.comm(p, b)),
        Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), N.add_succ_r(b, p)))

def add.assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), add.assoc(p, b, c))

# a <= b gives a + c <= b + c
def le.add_r(+a: Nat, +b: Nat, +c: Nat, h: N.Le(a, b)) -> N.Le(Nat.add(a, c), Nat.add(b, c)):
  N.add_mono(a, b, c, c, h, N.le_refl(c))

# 1 + 2^k p <= 2^k (1 + p)
def D.succ(+k: Nat, +p: Nat) -> N.Le(1n+N.D(k, p), N.D(k, 1n+p)):
  match k:
    case 0n:
      N.le_refl(1n+p)
    case 1n+q:
      N.le_trans(1n+Nat.double(N.D(q, p)), Nat.double(1n+N.D(q, p)), Nat.double(N.D(q, 1n+p)),
        N.le_succ(1n+Nat.double(N.D(q, p)), 1n+Nat.double(N.D(q, p)), N.le_refl(1n+Nat.double(N.D(q, p)))),
        N.double_mono(1n+N.D(q, p), N.D(q, 1n+p), D.succ(q, p)))

# Exact sums of U32
# -----------------

# a sum below 2^32 (W, kept a variable) is exact
def u32.add_ex(+x: U32, +y: U32, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  h: N.Le(1n+Nat.add(U32.to_nat(x), U32.to_nat(y)), W)) ->
  {U32.to_nat(U32.add(x, y)) == Nat.add(U32.to_nat(x), U32.to_nat(y)) : Nat}:
  match x y:
    case U32{+xw} U32{+yw}:
      PH.H.add_ex(32n, xw, yw, N.le_rw_r(1n+Nat.add(Word.to_nat(32n, xw), Word.to_nat(32n, yw)), W, PH.H.W(32n), hW, h))

def nlt.rel(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(y, x)) -> {Cmp.is_lt(c) == False{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({True{} == False{} : Bool}, N.not_succ_le(x, N.le_trans(1n+x, y, x, r, h)))
    case EQ{}:
      {==}
    case GT{}:
      {==}

# a < b is false when b <= a
def nlt.of(+a: U32, +b: U32, h: N.Le(U32.to_nat(b), U32.to_nat(a))) -> {U32.is_lt(a, b) == False{} : Bool}:
  nlt.rel(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), h)

def lt.rel(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(1n+x, y)) -> {Cmp.is_lt(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(y, (%r : N.Le(1n+_, y); h)))
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(y, N.le_trans(1n+y, x, y, r, N.weaken(x, y, h))))

# a < b when the numbers say so
def lt.to(+a: U32, +b: U32, h: N.Le(1n+U32.to_nat(a), U32.to_nat(b))) -> {U32.is_lt(a, b) == True{} : Bool}:
  lt.rel(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), h)

def or.true(b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# (x - 1) + 1 = x, on words
def W.dec_inc(+n: Nat, +t: Word(n)) -> {Word.inc(n, Word.adc(n, t, Word.zero(n), True{}, False{})) == t : Word(n)}:
  match n:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+p:
      match t:
        case WCon{False{}, +r}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.inc(p, Word.adc(p, r, Word.zero(p), True{}, False{})), r, W.dec_inc(p, r))
        case WCon{True{}, +r}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, Word.adc(p, r, Word.zero(p), True{}, True{}), r, PH.H.s1(p, r))

def u32.dec_inc(+x: U32) -> {U32.inc(U32.sub(x, 1)) == x : U32}:
  match x:
    case U32{+w}:
      match w:
        case WCon{False{}, +r}:
          Equal.cong(Word(31n), U32, z => U32{WCon{False{}, z}}, Word.inc(31n, Word.adc(31n, r, Word.zero(31n), True{}, False{})), r, W.dec_inc(31n, r))
        case WCon{True{}, +r}:
          Equal.cong(Word(31n), U32, z => U32{WCon{True{}, z}}, Word.adc(31n, r, Word.zero(31n), True{}, True{}), r, PH.H.s1(31n, r))

def nz.rel(c: Cmp, +x: Nat, r: N.Rel(c, x, 0n), h: N.Le(1n, x)) -> {Cmp.is_eq(c) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({True{} == False{} : Bool}, (%r : N.Le(1n, _); h))
    case GT{}:
      {==}

# a U32 whose number is at least 1 is not 0
def nz.to(+a: U32, h: N.Le(1n, U32.to_nat(a))) -> {U32.is_zero(a) == False{} : Bool}:
  nz.rel(U32.cmp(a, 0), U32.to_nat(a), N.U32.rel(a, 0), h)

# The memory's accesses
# ---------------------

# x - 1 is one less than x, for x not 0
def dec.nat(+x: U32, h: N.Le(1n, U32.to_nat(x))) -> {1n+U32.to_nat(U32.sub(x, 1)) == U32.to_nat(x) : Nat}:
  +d = U32.sub(x, 1)
  +ez = Equal.trans(Bool, False{}, U32.is_zero(x), U32.is_zero(U32.inc(d)), Equal.sym(Bool, U32.is_zero(x), False{}, nz.to(x, h)),
    Equal.cong(U32, Bool, z => U32.is_zero(z), x, U32.inc(d), Equal.sym(U32, U32.inc(d), x, u32.dec_inc(x))))
  Equal.trans(Nat, 1n+U32.to_nat(d), U32.to_nat(U32.inc(d)), U32.to_nat(x),
    Equal.sym(Nat, U32.to_nat(U32.inc(d)), 1n+U32.to_nat(d), I.U32.inc_nat(d, ez)),
    Equal.cong(U32, Nat, z => U32.to_nat(z), U32.inc(d), x, u32.dec_inc(x)))

# an access of w bytes at x + o is inside the memory of p pages when it ends
# within them, and the memory is below W = 2^32
def inside.ok(+p: U32, +x: U32, +o: U32, +w: U32, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hw: N.Le(1n, U32.to_nat(w)),
  +h: N.Le(Nat.add(Nat.add(U32.to_nat(x), U32.to_nat(o)), U32.to_nat(w)), N.D(16n, U32.to_nat(p))),
  hb: N.Le(1n+N.D(16n, U32.to_nat(p)), W)) -> {C.Wasm.inside(p, x, o, w) == True{} : Bool}:
  +X = U32.to_nat(x)
  +O = U32.to_nat(o)
  +Wn = U32.to_nat(w)
  +XO = Nat.add(X, O)
  +Sm = Nat.add(XO, Wn)
  +PBn = N.D(16n, U32.to_nat(p))
  +hS1 = N.le_trans(1n+Sm, 1n+PBn, W, h, hb)
  +hXS = N.le_trans(1n+XO, Nat.add(XO, 1n), Sm, N.le_succ_add(XO), N.add_mono(XO, XO, 1n, Wn, N.le_refl(XO), hw))
  +hXO = N.le_trans(1n+XO, Sm, W, hXS, N.weaken(Sm, W, hS1))
  +ea = U32.add(x, o)
  +eao = u32.add_ex(x, o, W, hW, hXO)
  +E = U32.add(ea, w)
  +hEa = N.le_rw_l(1n+Sm, 1n+Nat.add(U32.to_nat(ea), Wn), W,
    Equal.cong(Nat, Nat, z => 1n+Nat.add(z, Wn), XO, U32.to_nat(ea), Equal.sym(Nat, U32.to_nat(ea), XO, eao)), hS1)
  +eE = Equal.trans(Nat, U32.to_nat(E), Nat.add(U32.to_nat(ea), Wn), Sm, u32.add_ex(ea, w, W, hW, hEa),
    Equal.cong(Nat, Nat, z => Nat.add(z, Wn), U32.to_nat(ea), XO, eao))
  +c1 = nlt.of(ea, x, N.le_rw_r(X, XO, U32.to_nat(ea), Equal.sym(Nat, U32.to_nat(ea), XO, eao), N.le_add_r(X, O)))
  +c2 = nlt.of(E, ea, N.le_rw_r(U32.to_nat(ea), Sm, U32.to_nat(E), Equal.sym(Nat, U32.to_nat(E), Sm, eE),
    N.le_rw_l(XO, U32.to_nat(ea), Sm, Equal.sym(Nat, U32.to_nat(ea), XO, eao), N.le_add_r(XO, Wn))))
  +hE1 = N.le_rw_r(1n, Sm, U32.to_nat(E), Equal.sym(Nat, U32.to_nat(E), Sm, eE), N.le_trans(1n, Wn, Sm, hw, N.le_add_l(XO, Wn)))
  +d = U32.sub(E, 1)
  +sh = U32.shrn(d, 16n)
  +ed = Equal.trans(Nat, 1n+U32.to_nat(d), U32.to_nat(E), Sm, dec.nat(E, hE1), eE)
  +h4 = N.le_trans(1n+N.D(16n, U32.to_nat(sh)), 1n+U32.to_nat(d), PBn, V.shrn.le(16n, d),
    N.le_rw_l(Sm, 1n+U32.to_nat(d), PBn, Equal.sym(Nat, 1n+U32.to_nat(d), Sm, ed), h))
  +c3 = lt.to(sh, p, V.dlt(16n, U32.to_nat(sh), U32.to_nat(p), h4))
  %Equal.sym(Bool, U32.is_lt(ea, x), False{}, c1) : {Bool.and(Bool.not(_), C.Wasm.fits(p, ea, w)) == True{} : Bool}
  %Equal.sym(Bool, U32.is_lt(E, ea), False{}, c2) : {C.Wasm.fits.end(_, p, E) == True{} : Bool}
  %Equal.sym(Bool, U32.is_lt(sh, p), True{}, c3) : {Bool.or(U32.is_zero(E), _) == True{} : Bool}
  or.true(U32.is_zero(E))
