# compiler: the proof of need.big
# ================================
#
# A book of 2^26 bytes or more needs more memory than a module can have:
#
#   need   = 64 × (|p| + S) + 2^24 >= 64 × 2^26 + 1 = 2^32 + 1
#   memory = 65536 × min(m, 65536)  <= 2^16 × 2^16  = 2^32
#
# The big numbers stay symbolic: 2^k is D(k, 1n), and the literals meet it
# only through lemmas about the words of their bits, so the checker never
# counts to them. Every lemma is stated over variables, so its proof only
# computes with variables; the final proof only chains instances of them.

import Base
import ./impl.bend as C

# Kit
# ---

# the truth of b as a type
def T(b: Bool) -> Data:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

# a <= b, as a type
def Le(a: Nat, b: Nat) -> Data:
  T(Nat.is_le(a, b))

# True is not False
def true_ne_false(e: {True{} == False{} : Bool}) -> Empty:
  %e : T(_)
  Unit{}

# False is not True
def false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : T(Bool.not(_))
  Unit{}

# a Bool equal to True is true
def toT(b: Bool, e: {b == True{} : Bool}) -> T(b):
  match b:
    case True{}:
      Unit{}
    case False{}:
      false_ne_true(e)

# Order of Nat
# ------------

# 0 is at most every number
def le_zero(b: Nat) -> Le(0n, b):
  match b:
    case 0n:
      Unit{}
    case 1n+q:
      Unit{}

# a <= a
def le_refl(a: Nat) -> Le(a, a):
  match a:
    case 0n:
      Unit{}
    case 1n+p:
      le_refl(p)

# a <= b gives a <= 1 + b
def le_succ(a: Nat, b: Nat, h: Le(a, b)) -> Le(a, 1n+b):
  match a:
    case 0n:
      Unit{}
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(Le(1n+p, 1n), h)
        case 1n+q:
          le_succ(p, q, h)

# 1 + a <= b gives a <= b
def weaken(a: Nat, b: Nat, h: Le(1n+a, b)) -> Le(a, b):
  match a:
    case 0n:
      le_zero(b)
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(Le(1n+p, 0n), h)
        case 1n+q:
          weaken(p, q, h)

# a <= b and b <= c give a <= c
def le_trans(+a: Nat, +b: Nat, +c: Nat, h1: Le(a, b), h2: Le(b, c)) -> Le(a, c):
  match a:
    case 0n:
      le_zero(c)
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(Le(1n+p, c), h1)
        case 1n+q:
          match c:
            case 0n:
              Empty.absurd(Le(1n+p, 0n), h2)
            case 1n+r:
              le_trans(p, q, r, h1, h2)

# 1 + a <= a is false
def not_succ_le(a: Nat, h: Le(1n+a, a)) -> Empty:
  match a:
    case 0n:
      h
    case 1n+p:
      not_succ_le(p, h)

# a <= b rewritten on the left
def le_rw_l(-a: Nat, -b: Nat, -c: Nat, e: {a == b : Nat}, h: Le(a, c)) -> Le(b, c):
  %e : Le(_, c)
  h

# a <= b rewritten on the right
def le_rw_r(-a: Nat, -b: Nat, -c: Nat, e: {b == c : Nat}, h: Le(a, b)) -> Le(a, c):
  %e : Le(a, _)
  h

# a Bool comparison that holds gives a <= b
def toLe(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> Le(a, b):
  toT(Nat.is_le(a, b), e)

# Addition and order
# ------------------

# a <= a + b
def le_add_r(a: Nat, b: Nat) -> Le(a, Nat.add(a, b)):
  match a:
    case 0n:
      le_zero(b)
    case 1n+p:
      le_add_r(p, b)

# d <= b + d
def le_add_l(+b: Nat, +d: Nat) -> Le(d, Nat.add(b, d)):
  match b:
    case 0n:
      le_refl(d)
    case 1n+q:
      le_succ(d, Nat.add(q, d), le_add_l(q, d))

# 1 + a <= a + 1
def le_succ_add(a: Nat) -> Le(1n+a, Nat.add(a, 1n)):
  match a:
    case 0n:
      Unit{}
    case 1n+p:
      le_succ_add(p)

# 1 + a <= a + (1 + b)
def lt_add(a: Nat, b: Nat) -> Le(1n+a, Nat.add(a, 1n+b)):
  match a:
    case 0n:
      le_zero(b)
    case 1n+p:
      lt_add(p, b)

# a <= b and c <= d give a + c <= b + d
def add_mono(+a: Nat, +b: Nat, +c: Nat, +d: Nat, h1: Le(a, b), h2: Le(c, d)) -> Le(Nat.add(a, c), Nat.add(b, d)):
  match a:
    case 0n:
      le_trans(c, d, Nat.add(b, d), h2, le_add_l(b, d))
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(Le(Nat.add(1n+p, c), d), h1)
        case 1n+q:
          add_mono(p, q, c, d, h1, h2)

# a <= b gives 2a <= 2b
def double_mono(+a: Nat, +b: Nat, h: Le(a, b)) -> Le(Nat.double(a), Nat.double(b)):
  match a:
    case 0n:
      le_zero(Nat.double(b))
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(Le(Nat.double(1n+p), 0n), h)
        case 1n+q:
          double_mono(p, q, h)

# b <= c gives a × b <= a × c
def mul_mono_r(+a: Nat, +b: Nat, +c: Nat, +h: Le(b, c)) -> Le(Nat.mul(a, b), Nat.mul(a, c)):
  match a:
    case 0n:
      Unit{}
    case 1n+p:
      add_mono(b, c, Nat.mul(p, b), Nat.mul(p, c), h, mul_mono_r(p, b, c, h))

# a <= b gives a × c <= b × c
def mul_mono_l(+a: Nat, +b: Nat, +c: Nat, h: Le(a, b)) -> Le(Nat.mul(a, c), Nat.mul(b, c)):
  match a:
    case 0n:
      le_zero(Nat.mul(b, c))
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(Le(Nat.mul(1n+p, c), 0n), h)
        case 1n+q:
          add_mono(c, c, Nat.mul(p, c), Nat.mul(q, c), le_refl(c), mul_mono_l(p, q, c, h))

# Equations of Nat
# ----------------

# a + 0 = a
def add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

# a + (1 + b) = 1 + (a + b)
def add_succ_r(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ_r(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

# 2(a + b) = 2a + 2b
def double_add(a: Nat, +b: Nat) -> {Nat.double(Nat.add(a, b)) == Nat.add(Nat.double(a), Nat.double(b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %double_add(p, b) : {2n+Nat.double(Nat.add(p, b)) == 2n+_ : Nat}
      {==}

# b + (b + x) = 2b + x
def add_double(+b: Nat, +x: Nat) -> {Nat.add(b, Nat.add(b, x)) == Nat.add(Nat.double(b), x) : Nat}:
  match b:
    case 0n:
      {==}
    case 1n+q:
      %add_double(q, x) : {1n+Nat.add(q, 1n+Nat.add(q, x)) == 2n+_ : Nat}
      %add_succ_r(q, Nat.add(q, x)) : {1n+Nat.add(q, 1n+Nat.add(q, x)) == 1n+_ : Nat}
      {==}

# 2a × b = 2(a × b)
def mul_double(+a: Nat, +b: Nat) -> {Nat.mul(Nat.double(a), b) == Nat.double(Nat.mul(a, b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.double(Nat.add(b, Nat.mul(p, b))), Nat.add(Nat.double(b), Nat.double(Nat.mul(p, b))), double_add(b, Nat.mul(p, b))) : {Nat.add(b, Nat.add(b, Nat.mul(Nat.double(p), b))) == _ : Nat}
      %mul_double(p, b) : {Nat.add(b, Nat.add(b, Nat.mul(Nat.double(p), b))) == Nat.add(Nat.double(b), _) : Nat}
      add_double(b, Nat.mul(Nat.double(p), b))

# Powers of two
# -------------

# 2^k × x
def D(k: Nat, x: Nat) -> Nat:
  match k:
    case 0n:
      x
    case 1n+q:
      Nat.double(D(q, x))

# 2^k × b, as a product
def mul_D(+k: Nat, +b: Nat) -> {Nat.mul(D(k, 1n), b) == D(k, b) : Nat}:
  match k:
    case 0n:
      add_zero(b)
    case 1n+q:
      %mul_D(q, b) : {Nat.mul(Nat.double(D(q, 1n)), b) == Nat.double(_) : Nat}
      mul_double(D(q, 1n), b)

# 2^a × 2^b × x = 2^(a + b) × x
def D_add.go(+a: Nat, +b: Nat, +x: Nat) -> {D(a, D(b, x)) == D(Nat.add(a, b), x) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %D_add.go(p, b, x) : {Nat.double(D(p, D(b, x))) == Nat.double(_) : Nat}
      {==}

# 2^a × 2^b × x = 2^c × x, when a + b = c
def D_add(+a: Nat, +b: Nat, -c: Nat, +x: Nat, e: {Nat.add(a, b) == c : Nat}) -> {D(a, D(b, x)) == D(c, x) : Nat}:
  %e : {D(a, D(b, x)) == D(_, x) : Nat}
  D_add.go(a, b, x)

# Words
# -----

# the word of n bits whose k lowest bits are set
def ones(n: Nat, k: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match k:
        case 0n:
          WCon{False{}, ones(p, 0n)}
        case 1n+q:
          WCon{True{}, ones(p, q)}

# the word of n bits whose k-th bit alone is set
def bit(n: Nat, k: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match k:
        case 0n:
          WCon{True{}, ones(p, 0n)}
        case 1n+q:
          WCon{False{}, bit(p, q)}

# the word of no set bits is 0
def ones_zero(+n: Nat) -> {Word.to_nat(n, ones(n, 0n)) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Word.to_nat(p, ones(p, 0n)), 0n, ones_zero(p)) : {Nat.double(_) == 0n : Nat}
      {==}

# k set bits make 2^k - 1
def ones_val(+n: Nat, +k: Nat, h: Le(k, n)) -> {1n+Word.to_nat(n, ones(n, k)) == D(k, 1n) : Nat}:
  match n:
    case 0n:
      match k:
        case 0n:
          {==}
        case 1n+q:
          Empty.absurd({1n+Word.to_nat(0n, ones(0n, 1n+q)) == D(1n+q, 1n) : Nat}, h)
    case 1n+p:
      match k:
        case 0n:
          %Equal.sym(Nat, Word.to_nat(p, ones(p, 0n)), 0n, ones_zero(p)) : {1n+Nat.double(_) == 1n : Nat}
          {==}
        case 1n+q:
          %ones_val(p, q, h) : {2n+Nat.double(Word.to_nat(p, ones(p, q))) == Nat.double(_) : Nat}
          {==}

# the k-th bit makes 2^k
def bit_val(+n: Nat, +k: Nat, h: Le(1n+k, n)) -> {Word.to_nat(n, bit(n, k)) == D(k, 1n) : Nat}:
  match n:
    case 0n:
      Empty.absurd({Word.to_nat(0n, bit(0n, k)) == D(k, 1n) : Nat}, h)
    case 1n+p:
      match k:
        case 0n:
          %Equal.sym(Nat, Word.to_nat(p, ones(p, 0n)), 0n, ones_zero(p)) : {1n+Nat.double(_) == 1n : Nat}
          {==}
        case 1n+q:
          %bit_val(p, q, h) : {Nat.double(Word.to_nat(p, bit(p, q))) == Nat.double(_) : Nat}
          {==}

# the number of a U32 is the number of its word
def u32_to_nat(+w: Word(32n)) -> {U32.to_nat(U32{w}) == Word.to_nat(32n, w) : Nat}:
  {==}

# the increment adds at most 1
def Word.inc_le(+n: Nat, w: Word(n)) -> Le(Word.to_nat(n, Word.inc(n, w)), 1n+Word.to_nat(n, w)):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          le_refl(1n+Nat.double(Word.to_nat(p, t)))
        case WCon{True{}, +t}:
          double_mono(Word.to_nat(p, Word.inc(p, t)), 1n+Word.to_nat(p, t), Word.inc_le(p, t))

def U32.inc_le(a: U32) -> Le(U32.to_nat(U32.inc(a)), 1n+U32.to_nat(a)):
  match a:
    case U32{w}:
      Word.inc_le(32n, w)

# Comparison of words
# -------------------

# what a comparison says of the numbers it compares
def Rel(c: Cmp, x: Nat, y: Nat) -> Type:
  match c:
    case LT{}:
      Le(1n+x, y)
    case EQ{}:
      {x == y : Nat}
    case GT{}:
      Le(1n+y, x)

# 1 + x <= y gives 1 + 2x <= 2y
def lt_dd(+x: Nat, +y: Nat, h: Le(1n+x, y)) -> Le(1n+Nat.double(x), Nat.double(y)):
  weaken(1n+Nat.double(x), Nat.double(y), double_mono(1n+x, y, h))

# x = y gives 2x = 2y
def eq_dd(-x: Nat, -y: Nat, h: {x == y : Nat}) -> {Nat.double(x) == Nat.double(y) : Nat}:
  %h : {Nat.double(x) == Nat.double(_) : Nat}
  {==}

# x = y gives 2x + 1 = 2y + 1
def eq_dd1(-x: Nat, -y: Nat, h: {x == y : Nat}) -> {1n+Nat.double(x) == 1n+Nat.double(y) : Nat}:
  %h : {1n+Nat.double(x) == 1n+Nat.double(_) : Nat}
  {==}

# x = y gives 2x + 1 <= 2y + 1
def eq_le1(+x: Nat, -y: Nat, h: {x == y : Nat}) -> Le(1n+Nat.double(x), 1n+Nat.double(y)):
  %h : Le(1n+Nat.double(x), 1n+Nat.double(_))
  le_refl(1n+Nat.double(x))

# the low bits 0 and 0
def rel.ff(c: Cmp, +x: Nat, +y: Nat, h: Rel(c, x, y)) -> Rel(Word.cmp.fin(False{}, False{}, c), Nat.double(x), Nat.double(y)):
  match c:
    case LT{}:
      lt_dd(x, y, h)
    case EQ{}:
      eq_dd(x, y, h)
    case GT{}:
      lt_dd(y, x, h)

# the low bits 0 and 1
def rel.ft(c: Cmp, +x: Nat, +y: Nat, h: Rel(c, x, y)) -> Rel(Word.cmp.fin(False{}, True{}, c), Nat.double(x), 1n+Nat.double(y)):
  match c:
    case LT{}:
      double_mono(x, y, weaken(x, y, h))
    case EQ{}:
      eq_le1(x, y, h)
    case GT{}:
      double_mono(1n+y, x, h)

# the low bits 1 and 0
def rel.tf(c: Cmp, +x: Nat, +y: Nat, h: Rel(c, x, y)) -> Rel(Word.cmp.fin(True{}, False{}, c), 1n+Nat.double(x), Nat.double(y)):
  match c:
    case LT{}:
      double_mono(1n+x, y, h)
    case EQ{}:
      eq_le1(y, x, Equal.sym(Nat, x, y, h))
    case GT{}:
      double_mono(y, x, weaken(y, x, h))

# the low bits 1 and 1
def rel.tt(c: Cmp, +x: Nat, +y: Nat, h: Rel(c, x, y)) -> Rel(Word.cmp.fin(True{}, True{}, c), 1n+Nat.double(x), 1n+Nat.double(y)):
  match c:
    case LT{}:
      lt_dd(x, y, h)
    case EQ{}:
      eq_dd1(x, y, h)
    case GT{}:
      lt_dd(y, x, h)

# a comparison of words says how their numbers compare
def Word.rel(+n: Nat, a: Word(n), b: Word(n)) -> Rel(Word.cmp(n, a, b), Word.to_nat(n, a), Word.to_nat(n, b)):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          rel.ff(Word.cmp(p, at, bt), Word.to_nat(p, at), Word.to_nat(p, bt), Word.rel(p, at, bt))
        case WCon{False{}, +at} WCon{True{}, +bt}:
          rel.ft(Word.cmp(p, at, bt), Word.to_nat(p, at), Word.to_nat(p, bt), Word.rel(p, at, bt))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          rel.tf(Word.cmp(p, at, bt), Word.to_nat(p, at), Word.to_nat(p, bt), Word.rel(p, at, bt))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          rel.tt(Word.cmp(p, at, bt), Word.to_nat(p, at), Word.to_nat(p, bt), Word.rel(p, at, bt))

# a comparison of U32s says how their numbers compare
def U32.rel(a: U32, b: U32) -> Rel(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b)):
  match a b:
    case U32{x} U32{y}:
      Word.rel(32n, x, y)

# a comparison at most EQ gives x <= y
def rel_le(c: Cmp, +x: Nat, +y: Nat, h: Rel(c, x, y), e: T(Cmp.is_le(c))) -> Le(x, y):
  match c:
    case LT{}:
      weaken(x, y, h)
    case EQ{}:
      %h : Le(x, _)
      le_refl(x)
    case GT{}:
      Empty.absurd(Le(x, y), e)

# a comparison EQ gives x = y
def rel_eq(c: Cmp, -x: Nat, -y: Nat, h: Rel(c, x, y), e: T(Cmp.is_eq(c))) -> {x == y : Nat}:
  match c:
    case LT{}:
      Empty.absurd({x == y : Nat}, e)
    case EQ{}:
      h
    case GT{}:
      Empty.absurd({x == y : Nat}, e)

# the minimum of m and k, by the branch of U32.is_le(m, k)
def min.case(b: Bool, +m: U32, +k: U32, e: {U32.is_le(m, k) == b : Bool}) -> Le(U32.to_nat(C.Wasm.min.if(b, m, k)), U32.to_nat(k)):
  match b:
    case True{}:
      rel_le(U32.cmp(m, k), U32.to_nat(m), U32.to_nat(k), U32.rel(m, k), toT(U32.is_le(m, k), e))
    case False{}:
      le_refl(U32.to_nat(k))

# the minimum of m and k is at most k
def min_le(+m: U32, +k: U32) -> Le(U32.to_nat(C.Wasm.min(m, k)), U32.to_nat(k)):
  min.case(U32.is_le(m, k), m, k, {==})

# Length of a big image
# ---------------------

# 0 + x = x, with the 0 of a U32
def zero_add(+x: Nat) -> {Nat.add(U32.to_nat(0), x) == x : Nat}:
  {==}

# one step of Img.small, for any limit M, by the branch of U32.is_eq(n, M)
def small.step(
  b: Bool, +n: U32, +M: U32, +h: U32, +rest: List<&2, U32>,
  eb: {U32.is_eq(n, M) == b : Bool},
  e: {C.Img.small.if(b, u => C.Img.small(rest, U32.inc(n))) == False{} : Bool},
  ih: {C.Img.small(rest, U32.inc(n)) == False{} : Bool} ->
    Le(1n+U32.to_nat(M), Nat.add(U32.to_nat(U32.inc(n)), List.length(&2, U32, rest)))
) -> Le(1n+U32.to_nat(M), Nat.add(U32.to_nat(n), List.length(&2, U32, Con{h, rest}))):
  match b:
    case True{}:
      +nm = rel_eq(U32.cmp(n, M), U32.to_nat(n), U32.to_nat(M), U32.rel(n, M), toT(U32.is_eq(n, M), eb))
      %Equal.sym(Nat, U32.to_nat(n), U32.to_nat(M), nm) : Le(1n+U32.to_nat(M), Nat.add(_, 1n+List.length(&2, U32, rest)))
      lt_add(U32.to_nat(M), List.length(&2, U32, rest))
    case False{}:
      %Equal.sym(Nat, Nat.add(U32.to_nat(n), 1n+List.length(&2, U32, rest)), 1n+Nat.add(U32.to_nat(n), List.length(&2, U32, rest)), add_succ_r(U32.to_nat(n), List.length(&2, U32, rest))) : Le(1n+U32.to_nat(M), _)
      le_trans(1n+U32.to_nat(M), Nat.add(U32.to_nat(U32.inc(n)), List.length(&2, U32, rest)), 1n+Nat.add(U32.to_nat(n), List.length(&2, U32, rest)), ih(e),
        add_mono(U32.to_nat(U32.inc(n)), 1n+U32.to_nat(n), List.length(&2, U32, rest), List.length(&2, U32, rest), U32.inc_le(n), le_refl(List.length(&2, U32, rest))))

# Img.small(xs, n) false: n + |xs| > 67108863
def small.len(xs: List<&2, U32>, +n: U32, e: {C.Img.small(xs, n) == False{} : Bool}) ->
  Le(1n+U32.to_nat(67108863), Nat.add(U32.to_nat(n), List.length(&2, U32, xs))):
  match xs:
    case Nil{}:
      Empty.absurd(Le(1n+U32.to_nat(67108863), Nat.add(U32.to_nat(n), List.length(&2, U32, Nil{}))), true_ne_false(e))
    case Con{+h, +rest}:
      small.step(U32.is_eq(n, 67108863), n, 67108863, h, rest, {==}, e, e2 => small.len(rest, U32.inc(n), e2))

# The literals
# ------------

# 67108863 is the word of 26 set bits
def lit_M() -> {67108863 == U32{ones(32n, 26n)} : U32}:
  {==}

# 65536 is the word of bit 16
def lit_65536() -> {65536 == U32{bit(32n, 16n)} : U32}:
  {==}

# 1 + 67108863 = 2^26
def val_M() -> {1n+U32.to_nat(67108863) == D(26n, 1n) : Nat}:
  %Equal.sym(U32, 67108863, U32{ones(32n, 26n)}, lit_M()) : {1n+U32.to_nat(_) == D(26n, 1n) : Nat}
  %Equal.sym(Nat, U32.to_nat(U32{ones(32n, 26n)}), Word.to_nat(32n, ones(32n, 26n)), u32_to_nat(ones(32n, 26n))) : {1n+_ == D(26n, 1n) : Nat}
  ones_val(32n, 26n, Unit{})

# 65536 = 2^16
def val_65536() -> {U32.to_nat(65536) == D(16n, 1n) : Nat}:
  %Equal.sym(U32, 65536, U32{bit(32n, 16n)}, lit_65536()) : {U32.to_nat(_) == D(16n, 1n) : Nat}
  %Equal.sym(Nat, U32.to_nat(U32{bit(32n, 16n)}), Word.to_nat(32n, bit(32n, 16n)), u32_to_nat(bit(32n, 16n))) : {_ == D(16n, 1n) : Nat}
  bit_val(32n, 16n, Unit{})

# 64 = 2^6
def val_64() -> {D(6n, 1n) == 64n : Nat}:
  {==}

# 65536 × 65536 = 2^32
def sq_65536() -> {Nat.mul(U32.to_nat(65536), U32.to_nat(65536)) == D(32n, 1n) : Nat}:
  %Equal.sym(Nat, U32.to_nat(65536), D(16n, 1n), val_65536()) : {Nat.mul(_, _) == D(32n, 1n) : Nat}
  Equal.trans(Nat, Nat.mul(D(16n, 1n), D(16n, 1n)), D(16n, D(16n, 1n)), D(32n, 1n),
    mul_D(16n, D(16n, 1n)), D_add(16n, 16n, 32n, 1n, {==}))

# 64 × 2^26 = 2^32
def mul_64() -> {Nat.mul(64n, D(26n, 1n)) == D(32n, 1n) : Nat}:
  %val_64() : {Nat.mul(_, D(26n, 1n)) == D(32n, 1n) : Nat}
  Equal.trans(Nat, Nat.mul(D(6n, 1n), D(26n, 1n)), D(6n, D(26n, 1n)), D(32n, 1n),
    mul_D(6n, D(26n, 1n)), D_add(6n, 26n, 32n, 1n, {==}))

# the Nat 65536 is at most the number of the U32 65536
def le_65536() -> Le(65536n, U32.to_nat(65536)):
  Unit{}

# 1 <= 2^24
def le_one() -> Le(1n, 16777216n):
  Unit{}

# The memory
# ----------

# the memory of m is at most 2^32
def memory_le(+m: U32) -> Le(Nat.mul(65536n, U32.to_nat(C.Wasm.min(m, 65536))), D(32n, 1n)):
  +y = U32.to_nat(C.Wasm.min(m, 65536))
  +t = U32.to_nat(65536)
  le_trans(Nat.mul(65536n, y), Nat.mul(t, y), D(32n, 1n),
    mul_mono_l(65536n, t, y, le_65536()),
    le_rw_r(Nat.mul(t, y), Nat.mul(t, t), D(32n, 1n), sq_65536(), mul_mono_r(t, y, t, min_le(m, 65536))))

# The need
# --------

# 64 × |p| + 1 <= the need of p
def need_ge(+p: List<&2, U32>, +s: Nat) ->
  Le(1n+Nat.mul(64n, List.length(&2, U32, p)), Nat.add(Nat.mul(64n, Nat.add(List.length(&2, U32, p), s)), 16777216n)):
  +l = List.length(&2, U32, p)
  +x = Nat.mul(64n, l)
  le_trans(1n+x, Nat.add(x, 1n), Nat.add(Nat.mul(64n, Nat.add(l, s)), 16777216n), le_succ_add(x),
    add_mono(x, Nat.mul(64n, Nat.add(l, s)), 1n, 16777216n, mul_mono_r(64n, l, Nat.add(l, s), le_add_r(l, s)), le_one()))

# a small-failing book: 2^32 <= 64 × |p|
def len_ge(+p: List<&2, U32>, small: {C.Img.small(p, 0) == False{} : Bool}) ->
  Le(D(32n, 1n), Nat.mul(64n, List.length(&2, U32, p))):
  +l = List.length(&2, U32, p)
  +h1 = le_rw_r(1n+U32.to_nat(67108863), Nat.add(U32.to_nat(0), l), l, zero_add(l), small.len(p, 0, small))
  +h2 = le_rw_l(1n+U32.to_nat(67108863), D(26n, 1n), l, val_M(), h1)
  le_rw_l(Nat.mul(64n, D(26n, 1n)), D(32n, 1n), Nat.mul(64n, l), mul_64(), mul_mono_r(64n, D(26n, 1n), l, h2))

def probe2(+m: U32) -> {C.Program.memory(m) == Nat.mul(65536n, U32.to_nat(C.Wasm.min(m, 65536))) : Nat}:
  {==}
