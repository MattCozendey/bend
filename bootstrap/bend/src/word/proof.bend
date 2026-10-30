import Base
import ../shared/impl.bend as Shared
import ./impl.bend as WD
import ../wasm/impl.bend as Wasm

# Word lemmas
# ===========
#
# Facts about the words of Base, for the proofs of the run time: U32.from_nat
# turns + into U32.add and - into U32.sub, comparisons of words compare their
# numbers, and Fits holds below each number that an i32 holds.

# Addition
# ========

# a carry in adds 1
def W.carry(n: Nat, a: Word(n), b: Word(n)) ->
  {Word.adc(n, a, b, False{}, True{}) == Word.inc(n, Word.adc(n, a, b, False{}, False{})) : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{False{}, at} WCon{False{}, bt}:
          {==}
        case WCon{False{}, at} WCon{True{}, bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, at, bt, False{}, True{}),
            Word.inc(p, Word.adc(p, at, bt, False{}, False{})), W.carry(p, at, bt))
        case WCon{True{}, at} WCon{False{}, bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, at, bt, False{}, True{}),
            Word.inc(p, Word.adc(p, at, bt, False{}, False{})), W.carry(p, at, bt))
        case WCon{True{}, at} WCon{True{}, bt}:
          {==}

# a + inc(b) is a + b with a carry in
def W.add_inc(n: Nat, a: Word(n), b: Word(n)) ->
  {Word.adc(n, a, Word.inc(n, b), False{}, False{}) == Word.adc(n, a, b, False{}, True{}) : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{False{}, at} WCon{False{}, bt}:
          {==}
        case WCon{True{}, at} WCon{False{}, bt}:
          {==}
        case WCon{False{}, at} WCon{True{}, bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, at, Word.inc(p, bt), False{}, False{}),
            Word.adc(p, at, bt, False{}, True{}), W.add_inc(p, at, bt))
        case WCon{True{}, at} WCon{True{}, bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, at, Word.inc(p, bt), False{}, False{}),
            Word.adc(p, at, bt, False{}, True{}), W.add_inc(p, at, bt))

def W.add_zero(n: Nat, a: Word(n)) -> {Word.adc(n, a, Word.zero(n), False{}, False{}) == a : Word(n)}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{False{}, at}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, at, Word.zero(p), False{}, False{}), at,
            W.add_zero(p, at))
        case WCon{True{}, at}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, at, Word.zero(p), False{}, False{}), at,
            W.add_zero(p, at))

# (x + y + c) - y, with the borrow not(c), is x
def W.sub_add(n: Nat, x: Word(n), y: Word(n), c: Bool) ->
  {Word.adc(n, Word.adc(n, x, y, False{}, c), y, True{}, Bool.not(c)) == x : Word(n)}:
  match n:
    case 0n:
      match x y:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match x y c:
        case WCon{False{}, xt} WCon{False{}, yt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, xt, yt, False{}, False{}), yt, True{}, True{}),
            xt, W.sub_add(p, xt, yt, False{}))
        case WCon{False{}, xt} WCon{False{}, yt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, xt, yt, False{}, False{}), yt, True{}, True{}),
            xt, W.sub_add(p, xt, yt, False{}))
        case WCon{False{}, xt} WCon{True{}, yt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, xt, yt, False{}, False{}), yt, True{}, True{}),
            xt, W.sub_add(p, xt, yt, False{}))
        case WCon{False{}, xt} WCon{True{}, yt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, xt, yt, False{}, True{}), yt, True{}, False{}),
            xt, W.sub_add(p, xt, yt, True{}))
        case WCon{True{}, xt} WCon{False{}, yt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, xt, yt, False{}, False{}), yt, True{}, True{}),
            xt, W.sub_add(p, xt, yt, False{}))
        case WCon{True{}, xt} WCon{False{}, yt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, xt, yt, False{}, True{}), yt, True{}, False{}),
            xt, W.sub_add(p, xt, yt, True{}))
        case WCon{True{}, xt} WCon{True{}, yt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, xt, yt, False{}, True{}), yt, True{}, False{}),
            xt, W.sub_add(p, xt, yt, True{}))
        case WCon{True{}, xt} WCon{True{}, yt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, xt, yt, False{}, True{}), yt, True{}, False{}),
            xt, W.sub_add(p, xt, yt, True{}))

# Comparison
# ==========

def Nat.cmp_dd(X: Nat, Y: Nat) -> {Nat.cmp(Nat.double(X), Nat.double(Y)) == Nat.cmp(X, Y) : Cmp}:
  match X Y:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+x 0n:
      {==}
    case 1n+x 1n+y:
      Nat.cmp_dd(x, y)

def Nat.cmp_d1(X: Nat, Y: Nat) ->
  {Nat.cmp(Nat.double(X), 1n+Nat.double(Y)) == Word.cmp.fin(False{}, True{}, Nat.cmp(X, Y)) : Cmp}:
  match X Y:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+x 0n:
      {==}
    case 1n+x 1n+y:
      Nat.cmp_d1(x, y)

def Nat.cmp_1d(X: Nat, Y: Nat) ->
  {Nat.cmp(1n+Nat.double(X), Nat.double(Y)) == Word.cmp.fin(True{}, False{}, Nat.cmp(X, Y)) : Cmp}:
  match X Y:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+x 0n:
      {==}
    case 1n+x 1n+y:
      Nat.cmp_1d(x, y)

def Cmp.fin_same(b: Bool, t: Cmp) -> {Word.cmp.fin(b, b, t) == t : Cmp}:
  match b t:
    case _ LT{}:
      {==}
    case False{} EQ{}:
      {==}
    case True{} EQ{}:
      {==}
    case _ GT{}:
      {==}

# a comparison of words compares their numbers
def W.cmp(n: Nat, x: Word(n), y: Word(n)) ->
  {Word.cmp(n, x, y) == Nat.cmp(Word.to_nat(n, x), Word.to_nat(n, y)) : Cmp}:
  match n:
    case 0n:
      match x y:
        case WNil{} WNil{}:
          {==}
    case 1n++p:
      match x y:
        case WCon{False{}, +xt} WCon{False{}, +yt}:
          %Equal.sym(Cmp, Word.cmp(p, xt, yt), Nat.cmp(Word.to_nat(p, xt), Word.to_nat(p, yt)), W.cmp(p, xt, yt)) :
            {Word.cmp.fin(False{}, False{}, _) == Nat.cmp(Nat.double(Word.to_nat(p, xt)), Nat.double(Word.to_nat(p, yt))) : Cmp}
          %Equal.sym(Cmp, Nat.cmp(Nat.double(Word.to_nat(p, xt)), Nat.double(Word.to_nat(p, yt))),
            Nat.cmp(Word.to_nat(p, xt), Word.to_nat(p, yt)), Nat.cmp_dd(Word.to_nat(p, xt), Word.to_nat(p, yt))) :
            {Word.cmp.fin(False{}, False{}, Nat.cmp(Word.to_nat(p, xt), Word.to_nat(p, yt))) == _ : Cmp}
          Cmp.fin_same(False{}, Nat.cmp(Word.to_nat(p, xt), Word.to_nat(p, yt)))
        case WCon{False{}, +xt} WCon{True{}, +yt}:
          %Equal.sym(Cmp, Word.cmp(p, xt, yt), Nat.cmp(Word.to_nat(p, xt), Word.to_nat(p, yt)), W.cmp(p, xt, yt)) :
            {Word.cmp.fin(False{}, True{}, _) == Nat.cmp(Nat.double(Word.to_nat(p, xt)), 1n+Nat.double(Word.to_nat(p, yt))) : Cmp}
          Equal.sym(Cmp, Nat.cmp(Nat.double(Word.to_nat(p, xt)), 1n+Nat.double(Word.to_nat(p, yt))),
            Word.cmp.fin(False{}, True{}, Nat.cmp(Word.to_nat(p, xt), Word.to_nat(p, yt))),
            Nat.cmp_d1(Word.to_nat(p, xt), Word.to_nat(p, yt)))
        case WCon{True{}, +xt} WCon{False{}, +yt}:
          %Equal.sym(Cmp, Word.cmp(p, xt, yt), Nat.cmp(Word.to_nat(p, xt), Word.to_nat(p, yt)), W.cmp(p, xt, yt)) :
            {Word.cmp.fin(True{}, False{}, _) == Nat.cmp(1n+Nat.double(Word.to_nat(p, xt)), Nat.double(Word.to_nat(p, yt))) : Cmp}
          Equal.sym(Cmp, Nat.cmp(1n+Nat.double(Word.to_nat(p, xt)), Nat.double(Word.to_nat(p, yt))),
            Word.cmp.fin(True{}, False{}, Nat.cmp(Word.to_nat(p, xt), Word.to_nat(p, yt))),
            Nat.cmp_1d(Word.to_nat(p, xt), Word.to_nat(p, yt)))
        case WCon{True{}, +xt} WCon{True{}, +yt}:
          %Equal.sym(Cmp, Word.cmp(p, xt, yt), Nat.cmp(Word.to_nat(p, xt), Word.to_nat(p, yt)), W.cmp(p, xt, yt)) :
            {Word.cmp.fin(True{}, True{}, _) == Nat.cmp(Nat.double(Word.to_nat(p, xt)), Nat.double(Word.to_nat(p, yt))) : Cmp}
          %Equal.sym(Cmp, Nat.cmp(Nat.double(Word.to_nat(p, xt)), Nat.double(Word.to_nat(p, yt))),
            Nat.cmp(Word.to_nat(p, xt), Word.to_nat(p, yt)), Nat.cmp_dd(Word.to_nat(p, xt), Word.to_nat(p, yt))) :
            {Word.cmp.fin(True{}, True{}, Nat.cmp(Word.to_nat(p, xt), Word.to_nat(p, yt))) == _ : Cmp}
          Cmp.fin_same(True{}, Nat.cmp(Word.to_nat(p, xt), Word.to_nat(p, yt)))

# Numbers of words
# ================

def Elim.Nat(+n: Nat, -P: Nat -> Type, z: P(0n), s: @p: Nat -> P(1n+p)) -> P(n):
  match n:
    case 0n:
      z
    case 1n+p:
      s(p)

def W.of_nat_double(+p: Nat, X: Nat) -> {WD.Word.of_nat(1n+p, Nat.double(X)) == WCon{False{}, WD.Word.of_nat(p, X)} : Word(1n+p)}:
  match X:
    case 0n:
      {==}
    case 1n+x:
      %Equal.sym(Word(1n+p), WD.Word.of_nat(1n+p, Nat.double(x)), WCon{False{}, WD.Word.of_nat(p, x)}, W.of_nat_double(p, x)) :
        {Word.inc(1n+p, Word.inc(1n+p, _)) == WCon{False{}, WD.Word.of_nat(p, 1n+x)} : Word(1n+p)}
      {==}

# a word is the word of its number
def W.of_to_nat(n: Nat, w: Word(n)) -> {WD.Word.of_nat(n, Word.to_nat(n, w)) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n++p:
      match w:
        case WCon{False{}, +t}:
          %Equal.sym(Word(1n+p), WD.Word.of_nat(1n+p, Nat.double(Word.to_nat(p, t))), WCon{False{}, WD.Word.of_nat(p, Word.to_nat(p, t))},
            W.of_nat_double(p, Word.to_nat(p, t))) : {_ == WCon{False{}, t} : Word(1n+p)}
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, WD.Word.of_nat(p, Word.to_nat(p, t)), t, W.of_to_nat(p, t))
        case WCon{True{}, +t}:
          %Equal.sym(Word(1n+p), WD.Word.of_nat(1n+p, Nat.double(Word.to_nat(p, t))), WCon{False{}, WD.Word.of_nat(p, Word.to_nat(p, t))},
            W.of_nat_double(p, Word.to_nat(p, t))) : {Word.inc(1n+p, _) == WCon{True{}, t} : Word(1n+p)}
          Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, WD.Word.of_nat(p, Word.to_nat(p, t)), t, W.of_to_nat(p, t))

def Nat.no_zero_succ(-A: Type, +m: Nat, h: {0n == 1n+m : Nat}) -> A:
  Shared.Bool.absurd(A, Equal.sym(Bool, True{}, False{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), 0n, 1n+m, h)))

# the number of inc(w), when it is not 0, is one more than the number of w
def W.inc_to_nat(n: Nat, w: Word(n), +m: Nat, h: {Word.to_nat(n, Word.inc(n, w)) == 1n+m : Nat}) ->
  {Word.to_nat(n, w) == m : Nat}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          Nat.no_zero_succ({0n == m : Nat}, m, h)
    case 1n++p:
      match w:
        case WCon{False{}, +t}:
          Equal.cong(Nat, Nat, z => Shared.Nat.dec(z), 1n+Nat.double(Word.to_nat(p, t)), 1n+m, h)
        case WCon{True{}, +t}:
          Elim.Nat(Word.to_nat(p, Word.inc(p, t)),
            z => ({Word.to_nat(p, Word.inc(p, t)) == z : Nat} -> {Nat.double(z) == 1n+m : Nat} ->
              {1n+Nat.double(Word.to_nat(p, t)) == m : Nat}),
            e => h0 => Nat.no_zero_succ({1n+Nat.double(Word.to_nat(p, t)) == m : Nat}, m, h0),
            +z => e => h1 => Equal.trans(Nat, 1n+Nat.double(Word.to_nat(p, t)), 1n+Nat.double(z), m,
              Equal.cong(Nat, Nat, x => 1n+Nat.double(x), Word.to_nat(p, t), z, W.inc_to_nat(p, t, z, e)),
              Equal.cong(Nat, Nat, x => Shared.Nat.dec(x), 2n+Nat.double(z), 1n+m, h1)))({==}, h)

# I32s
# ====

def U.from_nat_word(x: Nat) -> {U32.from_nat(x) == U32{WD.Word.of_nat(32n, x)} : U32}:
  match x:
    case 0n:
      {==}
    case 1n++p:
      Equal.cong(U32, U32, u => U32.inc(u), U32.from_nat(p), U32{WD.Word.of_nat(32n, p)}, U.from_nat_word(p))

# an i32 is the i32 of its number
def U.from_to_nat(u: U32) -> {U32.from_nat(U32.to_nat(u)) == u : U32}:
  match u:
    case U32{+w}:
      Equal.trans(U32, U32.from_nat(Word.to_nat(32n, w)), U32{WD.Word.of_nat(32n, Word.to_nat(32n, w))}, U32{w},
        U.from_nat_word(Word.to_nat(32n, w)),
        Equal.cong(Word(32n), U32, z => U32{z}, WD.Word.of_nat(32n, Word.to_nat(32n, w)), w, W.of_to_nat(32n, w)))

def U.inc_to_nat(u: U32, +m: Nat, h: {U32.to_nat(U32.inc(u)) == 1n+m : Nat}) -> {U32.to_nat(u) == m : Nat}:
  match u:
    case U32{w}:
      W.inc_to_nat(32n, w, m, h)

def U.add_zero(a: U32) -> {U32.add(a, 0) == a : U32}:
  match a:
    case U32{+w}:
      Equal.cong(Word(32n), U32, z => U32{z}, Word.adc(32n, w, Word.zero(32n), False{}, False{}), w, W.add_zero(32n, w))

def U.add_inc(a: U32, b: U32) -> {U32.add(a, U32.inc(b)) == U32.inc(U32.add(a, b)) : U32}:
  match a b:
    case U32{+x} U32{+y}:
      Equal.cong(Word(32n), U32, z => U32{z}, Word.adc(32n, x, Word.inc(32n, y), False{}, False{}),
        Word.inc(32n, Word.adc(32n, x, y, False{}, False{})),
        Equal.trans(Word(32n), Word.adc(32n, x, Word.inc(32n, y), False{}, False{}), Word.adc(32n, x, y, False{}, True{}),
          Word.inc(32n, Word.adc(32n, x, y, False{}, False{})), W.add_inc(32n, x, y), W.carry(32n, x, y)))

# U32.from_nat turns + into U32.add
def U.from_nat_add(a: Nat, +b: Nat) -> {U32.from_nat(Nat.add(a, b)) == U32.add(U32.from_nat(b), U32.from_nat(a)) : U32}:
  match a:
    case 0n:
      Equal.sym(U32, U32.add(U32.from_nat(b), 0), U32.from_nat(b), U.add_zero(U32.from_nat(b)))
    case 1n++p:
      Equal.trans(U32, U32.inc(U32.from_nat(Nat.add(p, b))), U32.inc(U32.add(U32.from_nat(b), U32.from_nat(p))),
        U32.add(U32.from_nat(b), U32.inc(U32.from_nat(p))),
        Equal.cong(U32, U32, u => U32.inc(u), U32.from_nat(Nat.add(p, b)), U32.add(U32.from_nat(b), U32.from_nat(p)),
          U.from_nat_add(p, b)),
        Equal.sym(U32, U32.add(U32.from_nat(b), U32.inc(U32.from_nat(p))), U32.inc(U32.add(U32.from_nat(b), U32.from_nat(p))),
          U.add_inc(U32.from_nat(b), U32.from_nat(p))))

def U.sub_add(x: U32, y: U32) -> {U32.sub(U32.add(x, y), y) == x : U32}:
  match x y:
    case U32{+a} U32{+b}:
      Equal.cong(Word(32n), U32, z => U32{z}, Word.adc(32n, Word.adc(32n, a, b, False{}, False{}), b, True{}, True{}), a,
        W.sub_add(32n, a, b, False{}))

# a comparison of i32s compares their numbers
def U.cmp(a: U32, b: U32) -> {U32.cmp(a, b) == Nat.cmp(U32.to_nat(a), U32.to_nat(b)) : Cmp}:
  match a b:
    case U32{x} U32{y}:
      W.cmp(32n, x, y)

# Fits
# ====

def Fits.to_nat(+u: U32) -> WD.Fits(U32.to_nat(u)):
  Equal.cong(U32, Nat, z => U32.to_nat(z), U32.from_nat(U32.to_nat(u)), u, U.from_to_nat(u))

def Fits.pred(+x: Nat, h: WD.Fits(1n+x)) -> WD.Fits(x):
  U.inc_to_nat(U32.from_nat(x), x, h)

# Fits holds for a number below one that fits
def Fits.down(d: Nat, +a: Nat, h: WD.Fits(Nat.add(d, a))) -> WD.Fits(a):
  match d:
    case 0n:
      h
    case 1n++e:
      Fits.down(e, a, Fits.pred(Nat.add(e, a), h))

# a comparison of the i32s of two numbers that fit compares the numbers
def U.cmp_nat(+a: Nat, +b: Nat, ha: WD.Fits(a), hb: WD.Fits(b)) ->
  {U32.cmp(U32.from_nat(a), U32.from_nat(b)) == Nat.cmp(a, b) : Cmp}:
  %ha : {U32.cmp(U32.from_nat(a), U32.from_nat(b)) == Nat.cmp(_, b) : Cmp}
  %hb :
    {U32.cmp(U32.from_nat(a), U32.from_nat(b)) == Nat.cmp(U32.to_nat(U32.from_nat(a)), _) : Cmp}
  U.cmp(U32.from_nat(a), U32.from_nat(b))

# Memory
# ======

def Cmp.fin_ne(t: Cmp) -> {Cmp.is_eq(Word.cmp.fin(False{}, True{}, t)) == False{} : Bool}:
  match t:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def Cmp.fin_en(t: Cmp) -> {Cmp.is_eq(Word.cmp.fin(True{}, False{}, t)) == False{} : Bool}:
  match t:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# a byte at the bits of x, after a byte set at the bits of y
def M.get_set(n: Nat, x: Word(n), y: Word(n), +m: Wasm.Mem, +v: Nat) ->
  {Wasm.Mem.get(Wasm.Word.bits(n, x), Wasm.Mem.set(Wasm.Word.bits(n, y), m, v)) ==
    Bool.pick(Nat, Cmp.is_eq(Word.cmp(n, x, y)), v, Wasm.Mem.get(Wasm.Word.bits(n, x), m)) : Nat}:
  match n:
    case 0n:
      match x y:
        case WNil{} WNil{}:
          {==}
    case 1n++p:
      match x y:
        case WCon{False{}, +xt} WCon{False{}, +yt}:
          %Equal.sym(Cmp, Word.cmp.fin(False{}, False{}, Word.cmp(p, xt, yt)), Word.cmp(p, xt, yt), Cmp.fin_same(False{}, Word.cmp(p, xt, yt))) :
            {Wasm.Mem.get(Wasm.Word.bits(p, xt), Wasm.Mem.set(Wasm.Word.bits(p, yt), Wasm.Mem.child(False{}, m), v)) ==
              Bool.pick(Nat, Cmp.is_eq(_), v, Wasm.Mem.get(Wasm.Word.bits(p, xt), Wasm.Mem.child(False{}, m))) : Nat}
          M.get_set(p, xt, yt, Wasm.Mem.child(False{}, m), v)
        case WCon{True{}, +xt} WCon{True{}, +yt}:
          %Equal.sym(Cmp, Word.cmp.fin(True{}, True{}, Word.cmp(p, xt, yt)), Word.cmp(p, xt, yt), Cmp.fin_same(True{}, Word.cmp(p, xt, yt))) :
            {Wasm.Mem.get(Wasm.Word.bits(p, xt), Wasm.Mem.set(Wasm.Word.bits(p, yt), Wasm.Mem.child(True{}, m), v)) ==
              Bool.pick(Nat, Cmp.is_eq(_), v, Wasm.Mem.get(Wasm.Word.bits(p, xt), Wasm.Mem.child(True{}, m))) : Nat}
          M.get_set(p, xt, yt, Wasm.Mem.child(True{}, m), v)
        case WCon{False{}, +xt} WCon{True{}, +yt}:
          %Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(False{}, True{}, Word.cmp(p, xt, yt))), False{}, Cmp.fin_ne(Word.cmp(p, xt, yt))) :
            {Wasm.Mem.get(Wasm.Word.bits(p, xt), Wasm.Mem.child(False{}, m)) ==
              Bool.pick(Nat, _, v, Wasm.Mem.get(Wasm.Word.bits(p, xt), Wasm.Mem.child(False{}, m))) : Nat}
          {==}
        case WCon{True{}, +xt} WCon{False{}, +yt}:
          %Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(True{}, False{}, Word.cmp(p, xt, yt))), False{}, Cmp.fin_en(Word.cmp(p, xt, yt))) :
            {Wasm.Mem.get(Wasm.Word.bits(p, xt), Wasm.Mem.child(True{}, m)) ==
              Bool.pick(Nat, _, v, Wasm.Mem.get(Wasm.Word.bits(p, xt), Wasm.Mem.child(True{}, m))) : Nat}
          {==}

def M.get_set_at(a: U32, b: U32, +m: Wasm.Mem, +v: Nat) ->
  {Wasm.Mem.get_at(a, Wasm.Mem.set_at(b, m, v)) == Bool.pick(Nat, U32.is_eq(a, b), v, Wasm.Mem.get_at(a, m)) : Nat}:
  match a b:
    case U32{x} U32{y}:
      M.get_set(32n, x, y, m, v)

# a byte at the address A, after a byte set at the address B; both fit
def M.get_set_nat(+A: Nat, +B: Nat, +m: Wasm.Mem, +v: Nat, ha: WD.Fits(A), hb: WD.Fits(B)) ->
  {Wasm.Mem.get_at(U32.from_nat(A), Wasm.Mem.set_at(U32.from_nat(B), m, v)) ==
    Bool.pick(Nat, Nat.is_eq(A, B), v, Wasm.Mem.get_at(U32.from_nat(A), m)) : Nat}:
  %U.cmp_nat(A, B, ha, hb) :
    {Wasm.Mem.get_at(U32.from_nat(A), Wasm.Mem.set_at(U32.from_nat(B), m, v)) ==
      Bool.pick(Nat, Cmp.is_eq(_), v, Wasm.Mem.get_at(U32.from_nat(A), m)) : Nat}
  M.get_set_at(U32.from_nat(A), U32.from_nat(B), m, v)

# Words in memory
# ===============

# the i32 of four bytes, the low byte first, as Mem.load reads it
def Bytes.load(+b0: Nat, +b1: Nat, +b2: Nat, +b3: Nat) -> U32:
  U32.or(U32.or(U32.from_nat(b0), U32.shln(U32.from_nat(b1), 8n)),
    U32.or(U32.shln(U32.from_nat(b2), 16n), U32.shln(U32.from_nat(b3), 24n)))

# the four bytes of v, put back together
def Bytes.join(+v: U32) -> U32:
  U32.or(U32.or(U32.and(v, 255), U32.shln(U32.and(U32.shrn(v, 8n), 255), 8n)),
    U32.or(U32.shln(U32.and(U32.shrn(v, 16n), 255), 16n), U32.shln(U32.and(U32.shrn(v, 24n), 255), 24n)))

def M.add_k(+A: Nat, +k: Nat) -> {U32.add(U32.from_nat(A), U32.from_nat(k)) == U32.from_nat(Nat.add(k, A)) : U32}:
  Equal.sym(U32, U32.from_nat(Nat.add(k, A)), U32.add(U32.from_nat(A), U32.from_nat(k)), U.from_nat_add(k, A))

def M.load_eq(+A: Nat, +m: Wasm.Mem) ->
  {Wasm.Mem.load(U32.from_nat(A), m) == Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), m), Wasm.Mem.get_at(U32.from_nat(1n+A), m),
    Wasm.Mem.get_at(U32.from_nat(2n+A), m), Wasm.Mem.get_at(U32.from_nat(3n+A), m)) : U32}:
  %M.add_k(A, 1n) : {Wasm.Mem.load(U32.from_nat(A), m) == Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), m), Wasm.Mem.get_at(_, m),
    Wasm.Mem.get_at(U32.from_nat(2n+A), m), Wasm.Mem.get_at(U32.from_nat(3n+A), m)) : U32}
  %M.add_k(A, 2n) : {Wasm.Mem.load(U32.from_nat(A), m) == Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), m),
    Wasm.Mem.get_at(U32.add(U32.from_nat(A), U32.from_nat(1n)), m), Wasm.Mem.get_at(_, m), Wasm.Mem.get_at(U32.from_nat(3n+A), m)) : U32}
  %M.add_k(A, 3n) : {Wasm.Mem.load(U32.from_nat(A), m) == Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), m),
    Wasm.Mem.get_at(U32.add(U32.from_nat(A), U32.from_nat(1n)), m), Wasm.Mem.get_at(U32.add(U32.from_nat(A), U32.from_nat(2n)), m),
    Wasm.Mem.get_at(_, m)) : U32}
  {==}

# the byte of the bits from 8k of v
def Bytes.at(+v: U32, k: Nat) -> Nat:
  U32.to_nat(U32.and(U32.shrn(v, Nat.mul(8n, k)), 255))

def Bytes.store(+B: Nat, m: Wasm.Mem, +v: U32) -> Wasm.Mem:
  Wasm.Mem.set_at(U32.from_nat(3n+B),
    Wasm.Mem.set_at(U32.from_nat(2n+B),
      Wasm.Mem.set_at(U32.from_nat(1n+B), Wasm.Mem.set_at(U32.from_nat(B), m, Bytes.at(v, 0n)), Bytes.at(v, 1n)),
      Bytes.at(v, 2n)),
    Bytes.at(v, 3n))

def M.store_eq(+B: Nat, +m: Wasm.Mem, +v: U32) -> {Wasm.Mem.store(U32.from_nat(B), m, v) == Bytes.store(B, m, v) : Wasm.Mem}:
  %M.add_k(B, 1n) : {Wasm.Mem.store(U32.from_nat(B), m, v) ==
    Wasm.Mem.set_at(U32.from_nat(3n+B), Wasm.Mem.set_at(U32.from_nat(2n+B),
      Wasm.Mem.set_at(_, Wasm.Mem.set_at(U32.from_nat(B), m, Bytes.at(v, 0n)), Bytes.at(v, 1n)), Bytes.at(v, 2n)), Bytes.at(v, 3n)) : Wasm.Mem}
  %M.add_k(B, 2n) : {Wasm.Mem.store(U32.from_nat(B), m, v) ==
    Wasm.Mem.set_at(U32.from_nat(3n+B), Wasm.Mem.set_at(_,
      Wasm.Mem.set_at(U32.add(U32.from_nat(B), U32.from_nat(1n)), Wasm.Mem.set_at(U32.from_nat(B), m, Bytes.at(v, 0n)), Bytes.at(v, 1n)),
      Bytes.at(v, 2n)), Bytes.at(v, 3n)) : Wasm.Mem}
  %M.add_k(B, 3n) : {Wasm.Mem.store(U32.from_nat(B), m, v) ==
    Wasm.Mem.set_at(_, Wasm.Mem.set_at(U32.add(U32.from_nat(B), U32.from_nat(2n)),
      Wasm.Mem.set_at(U32.add(U32.from_nat(B), U32.from_nat(1n)), Wasm.Mem.set_at(U32.from_nat(B), m, Bytes.at(v, 0n)), Bytes.at(v, 1n)),
      Bytes.at(v, 2n)), Bytes.at(v, 3n)) : Wasm.Mem}
  {==}

def Nat.is_eq_refl(a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.is_eq_refl(p)

# two numbers differ when one is below the other
def Nat.ne_lt(a: Nat, b: Nat, h: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      Shared.Bool.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Nat.ne_lt(p, q, h)

def Nat.ne_gt(a: Nat, b: Nat, h: {Nat.is_le(1n+b, a) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      Shared.Bool.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Nat.ne_gt(p, q, h)

def M.get_skip(+A: Nat, +B: Nat, +m: Wasm.Mem, +v: Nat, ha: WD.Fits(A), hb: WD.Fits(B), hne: {Nat.is_eq(A, B) == False{} : Bool}) ->
  {Wasm.Mem.get_at(U32.from_nat(A), Wasm.Mem.set_at(U32.from_nat(B), m, v)) == Wasm.Mem.get_at(U32.from_nat(A), m) : Nat}:
  %hne :
    {Wasm.Mem.get_at(U32.from_nat(A), Wasm.Mem.set_at(U32.from_nat(B), m, v)) ==
      Bool.pick(Nat, _, v, Wasm.Mem.get_at(U32.from_nat(A), m)) : Nat}
  M.get_set_nat(A, B, m, v, ha, hb)

def M.get_hit(+A: Nat, +m: Wasm.Mem, +v: Nat, +ha: {U32.to_nat(U32.from_nat(A)) == A : Nat}) ->
  {Wasm.Mem.get_at(U32.from_nat(A), Wasm.Mem.set_at(U32.from_nat(A), m, v)) == v : Nat}:
  %Nat.is_eq_refl(A) :
    {Wasm.Mem.get_at(U32.from_nat(A), Wasm.Mem.set_at(U32.from_nat(A), m, v)) ==
      Bool.pick(Nat, _, v, Wasm.Mem.get_at(U32.from_nat(A), m)) : Nat}
  M.get_set_nat(A, A, m, v, ha, ha)

# a byte at C after a store at B whose four bytes are not C
def M.get_store_far(+C: Nat, +B: Nat, +m: Wasm.Mem, +v: U32, +hc: {U32.to_nat(U32.from_nat(C)) == C : Nat},
  +hb: {U32.to_nat(U32.from_nat(3n+B)) == 3n+B : Nat},
  n0: {Nat.is_eq(C, B) == False{} : Bool}, n1: {Nat.is_eq(C, 1n+B) == False{} : Bool},
  n2: {Nat.is_eq(C, 2n+B) == False{} : Bool}, n3: {Nat.is_eq(C, 3n+B) == False{} : Bool}) ->
  {Wasm.Mem.get_at(U32.from_nat(C), Wasm.Mem.store(U32.from_nat(B), m, v)) == Wasm.Mem.get_at(U32.from_nat(C), m) : Nat}:
  %Equal.sym(Wasm.Mem, Wasm.Mem.store(U32.from_nat(B), m, v), Bytes.store(B, m, v), M.store_eq(B, m, v)) :
    {Wasm.Mem.get_at(U32.from_nat(C), _) == Wasm.Mem.get_at(U32.from_nat(C), m) : Nat}
  +s0 = Wasm.Mem.set_at(U32.from_nat(B), m, Bytes.at(v, 0n))
  +s1 = Wasm.Mem.set_at(U32.from_nat(1n+B), s0, Bytes.at(v, 1n))
  +s2 = Wasm.Mem.set_at(U32.from_nat(2n+B), s1, Bytes.at(v, 2n))
  +g = Wasm.Mem.get_at(U32.from_nat(C), m)
  Equal.trans(Nat, Wasm.Mem.get_at(U32.from_nat(C), Wasm.Mem.set_at(U32.from_nat(3n+B), s2, Bytes.at(v, 3n))),
    Wasm.Mem.get_at(U32.from_nat(C), s2), g, M.get_skip(C, 3n+B, s2, Bytes.at(v, 3n), hc, hb, n3),
    Equal.trans(Nat, Wasm.Mem.get_at(U32.from_nat(C), s2), Wasm.Mem.get_at(U32.from_nat(C), s1), g,
      M.get_skip(C, 2n+B, s1, Bytes.at(v, 2n), hc, Fits.down(1n, 2n+B, hb), n2),
      Equal.trans(Nat, Wasm.Mem.get_at(U32.from_nat(C), s1), Wasm.Mem.get_at(U32.from_nat(C), s0), g,
        M.get_skip(C, 1n+B, s0, Bytes.at(v, 1n), hc, Fits.down(2n, 1n+B, hb), n1),
        M.get_skip(C, B, m, Bytes.at(v, 0n), hc, Fits.down(3n, B, hb), n0))))

# Bytes of an i32
# ===============

# bit 0 to 7 of the bytes of an i32, put back together
def Bit.k0(+b: Bool) -> Bool:
  Bool.or(Bool.or(Bool.and(b, True{}), False{}), Bool.or(False{}, False{}))

def Bit.id0(b: Bool) -> {Bit.k0(b) == b : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# bit 8 to 15 of the bytes of an i32, put back together
def Bit.k1(+b: Bool) -> Bool:
  Bool.or(Bool.or(Bool.and(b, False{}), Bool.and(b, True{})), Bool.or(False{}, False{}))

def Bit.id1(b: Bool) -> {Bit.k1(b) == b : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# bit 16 to 23 of the bytes of an i32, put back together
def Bit.k2(+b: Bool) -> Bool:
  Bool.or(Bool.or(Bool.and(b, False{}), Bool.and(b, False{})), Bool.or(Bool.and(b, True{}), False{}))

def Bit.id2(b: Bool) -> {Bit.k2(b) == b : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# bit 24 to 31 of the bytes of an i32, put back together
def Bit.k3(+b: Bool) -> Bool:
  Bool.or(Bool.or(Bool.and(b, False{}), Bool.and(b, False{})), Bool.or(Bool.and(b, False{}), Bool.and(b, True{})))

def Bit.id3(b: Bool) -> {Bit.k3(b) == b : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# the bytes of v, put back together, are v
def U.bytes_id(v: U32) -> {Bytes.join(v) == v : U32}:
  match v:
    case U32{w0}:
      match w0:
        case WCon{+b0, w1}:
          match w1:
            case WCon{+b1, w2}:
              match w2:
                case WCon{+b2, w3}:
                  match w3:
                    case WCon{+b3, w4}:
                      match w4:
                        case WCon{+b4, w5}:
                          match w5:
                            case WCon{+b5, w6}:
                              match w6:
                                case WCon{+b6, w7}:
                                  match w7:
                                    case WCon{+b7, w8}:
                                      match w8:
                                        case WCon{+b8, w9}:
                                          match w9:
                                            case WCon{+b9, w10}:
                                              match w10:
                                                case WCon{+b10, w11}:
                                                  match w11:
                                                    case WCon{+b11, w12}:
                                                      match w12:
                                                        case WCon{+b12, w13}:
                                                          match w13:
                                                            case WCon{+b13, w14}:
                                                              match w14:
                                                                case WCon{+b14, w15}:
                                                                  match w15:
                                                                    case WCon{+b15, w16}:
                                                                      match w16:
                                                                        case WCon{+b16, w17}:
                                                                          match w17:
                                                                            case WCon{+b17, w18}:
                                                                              match w18:
                                                                                case WCon{+b18, w19}:
                                                                                  match w19:
                                                                                    case WCon{+b19, w20}:
                                                                                      match w20:
                                                                                        case WCon{+b20, w21}:
                                                                                          match w21:
                                                                                            case WCon{+b21, w22}:
                                                                                              match w22:
                                                                                                case WCon{+b22, w23}:
                                                                                                  match w23:
                                                                                                    case WCon{+b23, w24}:
                                                                                                      match w24:
                                                                                                        case WCon{+b24, w25}:
                                                                                                          match w25:
                                                                                                            case WCon{+b25, w26}:
                                                                                                              match w26:
                                                                                                                case WCon{+b26, w27}:
                                                                                                                  match w27:
                                                                                                                    case WCon{+b27, w28}:
                                                                                                                      match w28:
                                                                                                                        case WCon{+b28, w29}:
                                                                                                                          match w29:
                                                                                                                            case WCon{+b29, w30}:
                                                                                                                              match w30:
                                                                                                                                case WCon{+b30, w31}:
                                                                                                                                  match w31:
                                                                                                                                    case WCon{+b31, w32}:
                                                                                                                                      match w32:
                                                                                                                                        case WNil{}:
                                                                                                                                          %Equal.sym(Bool, Bit.k0(b0), b0, Bit.id0(b0)) : {U32{WCon{_, WCon{Bit.k0(b1), WCon{Bit.k0(b2), WCon{Bit.k0(b3), WCon{Bit.k0(b4), WCon{Bit.k0(b5), WCon{Bit.k0(b6), WCon{Bit.k0(b7), WCon{Bit.k1(b8), WCon{Bit.k1(b9), WCon{Bit.k1(b10), WCon{Bit.k1(b11), WCon{Bit.k1(b12), WCon{Bit.k1(b13), WCon{Bit.k1(b14), WCon{Bit.k1(b15), WCon{Bit.k2(b16), WCon{Bit.k2(b17), WCon{Bit.k2(b18), WCon{Bit.k2(b19), WCon{Bit.k2(b20), WCon{Bit.k2(b21), WCon{Bit.k2(b22), WCon{Bit.k2(b23), WCon{Bit.k3(b24), WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k0(b1), b1, Bit.id0(b1)) : {U32{WCon{b0, WCon{_, WCon{Bit.k0(b2), WCon{Bit.k0(b3), WCon{Bit.k0(b4), WCon{Bit.k0(b5), WCon{Bit.k0(b6), WCon{Bit.k0(b7), WCon{Bit.k1(b8), WCon{Bit.k1(b9), WCon{Bit.k1(b10), WCon{Bit.k1(b11), WCon{Bit.k1(b12), WCon{Bit.k1(b13), WCon{Bit.k1(b14), WCon{Bit.k1(b15), WCon{Bit.k2(b16), WCon{Bit.k2(b17), WCon{Bit.k2(b18), WCon{Bit.k2(b19), WCon{Bit.k2(b20), WCon{Bit.k2(b21), WCon{Bit.k2(b22), WCon{Bit.k2(b23), WCon{Bit.k3(b24), WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k0(b2), b2, Bit.id0(b2)) : {U32{WCon{b0, WCon{b1, WCon{_, WCon{Bit.k0(b3), WCon{Bit.k0(b4), WCon{Bit.k0(b5), WCon{Bit.k0(b6), WCon{Bit.k0(b7), WCon{Bit.k1(b8), WCon{Bit.k1(b9), WCon{Bit.k1(b10), WCon{Bit.k1(b11), WCon{Bit.k1(b12), WCon{Bit.k1(b13), WCon{Bit.k1(b14), WCon{Bit.k1(b15), WCon{Bit.k2(b16), WCon{Bit.k2(b17), WCon{Bit.k2(b18), WCon{Bit.k2(b19), WCon{Bit.k2(b20), WCon{Bit.k2(b21), WCon{Bit.k2(b22), WCon{Bit.k2(b23), WCon{Bit.k3(b24), WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k0(b3), b3, Bit.id0(b3)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{_, WCon{Bit.k0(b4), WCon{Bit.k0(b5), WCon{Bit.k0(b6), WCon{Bit.k0(b7), WCon{Bit.k1(b8), WCon{Bit.k1(b9), WCon{Bit.k1(b10), WCon{Bit.k1(b11), WCon{Bit.k1(b12), WCon{Bit.k1(b13), WCon{Bit.k1(b14), WCon{Bit.k1(b15), WCon{Bit.k2(b16), WCon{Bit.k2(b17), WCon{Bit.k2(b18), WCon{Bit.k2(b19), WCon{Bit.k2(b20), WCon{Bit.k2(b21), WCon{Bit.k2(b22), WCon{Bit.k2(b23), WCon{Bit.k3(b24), WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k0(b4), b4, Bit.id0(b4)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{_, WCon{Bit.k0(b5), WCon{Bit.k0(b6), WCon{Bit.k0(b7), WCon{Bit.k1(b8), WCon{Bit.k1(b9), WCon{Bit.k1(b10), WCon{Bit.k1(b11), WCon{Bit.k1(b12), WCon{Bit.k1(b13), WCon{Bit.k1(b14), WCon{Bit.k1(b15), WCon{Bit.k2(b16), WCon{Bit.k2(b17), WCon{Bit.k2(b18), WCon{Bit.k2(b19), WCon{Bit.k2(b20), WCon{Bit.k2(b21), WCon{Bit.k2(b22), WCon{Bit.k2(b23), WCon{Bit.k3(b24), WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k0(b5), b5, Bit.id0(b5)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{_, WCon{Bit.k0(b6), WCon{Bit.k0(b7), WCon{Bit.k1(b8), WCon{Bit.k1(b9), WCon{Bit.k1(b10), WCon{Bit.k1(b11), WCon{Bit.k1(b12), WCon{Bit.k1(b13), WCon{Bit.k1(b14), WCon{Bit.k1(b15), WCon{Bit.k2(b16), WCon{Bit.k2(b17), WCon{Bit.k2(b18), WCon{Bit.k2(b19), WCon{Bit.k2(b20), WCon{Bit.k2(b21), WCon{Bit.k2(b22), WCon{Bit.k2(b23), WCon{Bit.k3(b24), WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k0(b6), b6, Bit.id0(b6)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{_, WCon{Bit.k0(b7), WCon{Bit.k1(b8), WCon{Bit.k1(b9), WCon{Bit.k1(b10), WCon{Bit.k1(b11), WCon{Bit.k1(b12), WCon{Bit.k1(b13), WCon{Bit.k1(b14), WCon{Bit.k1(b15), WCon{Bit.k2(b16), WCon{Bit.k2(b17), WCon{Bit.k2(b18), WCon{Bit.k2(b19), WCon{Bit.k2(b20), WCon{Bit.k2(b21), WCon{Bit.k2(b22), WCon{Bit.k2(b23), WCon{Bit.k3(b24), WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k0(b7), b7, Bit.id0(b7)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{_, WCon{Bit.k1(b8), WCon{Bit.k1(b9), WCon{Bit.k1(b10), WCon{Bit.k1(b11), WCon{Bit.k1(b12), WCon{Bit.k1(b13), WCon{Bit.k1(b14), WCon{Bit.k1(b15), WCon{Bit.k2(b16), WCon{Bit.k2(b17), WCon{Bit.k2(b18), WCon{Bit.k2(b19), WCon{Bit.k2(b20), WCon{Bit.k2(b21), WCon{Bit.k2(b22), WCon{Bit.k2(b23), WCon{Bit.k3(b24), WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k1(b8), b8, Bit.id1(b8)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{_, WCon{Bit.k1(b9), WCon{Bit.k1(b10), WCon{Bit.k1(b11), WCon{Bit.k1(b12), WCon{Bit.k1(b13), WCon{Bit.k1(b14), WCon{Bit.k1(b15), WCon{Bit.k2(b16), WCon{Bit.k2(b17), WCon{Bit.k2(b18), WCon{Bit.k2(b19), WCon{Bit.k2(b20), WCon{Bit.k2(b21), WCon{Bit.k2(b22), WCon{Bit.k2(b23), WCon{Bit.k3(b24), WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k1(b9), b9, Bit.id1(b9)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{_, WCon{Bit.k1(b10), WCon{Bit.k1(b11), WCon{Bit.k1(b12), WCon{Bit.k1(b13), WCon{Bit.k1(b14), WCon{Bit.k1(b15), WCon{Bit.k2(b16), WCon{Bit.k2(b17), WCon{Bit.k2(b18), WCon{Bit.k2(b19), WCon{Bit.k2(b20), WCon{Bit.k2(b21), WCon{Bit.k2(b22), WCon{Bit.k2(b23), WCon{Bit.k3(b24), WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k1(b10), b10, Bit.id1(b10)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{_, WCon{Bit.k1(b11), WCon{Bit.k1(b12), WCon{Bit.k1(b13), WCon{Bit.k1(b14), WCon{Bit.k1(b15), WCon{Bit.k2(b16), WCon{Bit.k2(b17), WCon{Bit.k2(b18), WCon{Bit.k2(b19), WCon{Bit.k2(b20), WCon{Bit.k2(b21), WCon{Bit.k2(b22), WCon{Bit.k2(b23), WCon{Bit.k3(b24), WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k1(b11), b11, Bit.id1(b11)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{_, WCon{Bit.k1(b12), WCon{Bit.k1(b13), WCon{Bit.k1(b14), WCon{Bit.k1(b15), WCon{Bit.k2(b16), WCon{Bit.k2(b17), WCon{Bit.k2(b18), WCon{Bit.k2(b19), WCon{Bit.k2(b20), WCon{Bit.k2(b21), WCon{Bit.k2(b22), WCon{Bit.k2(b23), WCon{Bit.k3(b24), WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k1(b12), b12, Bit.id1(b12)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{_, WCon{Bit.k1(b13), WCon{Bit.k1(b14), WCon{Bit.k1(b15), WCon{Bit.k2(b16), WCon{Bit.k2(b17), WCon{Bit.k2(b18), WCon{Bit.k2(b19), WCon{Bit.k2(b20), WCon{Bit.k2(b21), WCon{Bit.k2(b22), WCon{Bit.k2(b23), WCon{Bit.k3(b24), WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k1(b13), b13, Bit.id1(b13)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{_, WCon{Bit.k1(b14), WCon{Bit.k1(b15), WCon{Bit.k2(b16), WCon{Bit.k2(b17), WCon{Bit.k2(b18), WCon{Bit.k2(b19), WCon{Bit.k2(b20), WCon{Bit.k2(b21), WCon{Bit.k2(b22), WCon{Bit.k2(b23), WCon{Bit.k3(b24), WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k1(b14), b14, Bit.id1(b14)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{_, WCon{Bit.k1(b15), WCon{Bit.k2(b16), WCon{Bit.k2(b17), WCon{Bit.k2(b18), WCon{Bit.k2(b19), WCon{Bit.k2(b20), WCon{Bit.k2(b21), WCon{Bit.k2(b22), WCon{Bit.k2(b23), WCon{Bit.k3(b24), WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k1(b15), b15, Bit.id1(b15)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{_, WCon{Bit.k2(b16), WCon{Bit.k2(b17), WCon{Bit.k2(b18), WCon{Bit.k2(b19), WCon{Bit.k2(b20), WCon{Bit.k2(b21), WCon{Bit.k2(b22), WCon{Bit.k2(b23), WCon{Bit.k3(b24), WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k2(b16), b16, Bit.id2(b16)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{_, WCon{Bit.k2(b17), WCon{Bit.k2(b18), WCon{Bit.k2(b19), WCon{Bit.k2(b20), WCon{Bit.k2(b21), WCon{Bit.k2(b22), WCon{Bit.k2(b23), WCon{Bit.k3(b24), WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k2(b17), b17, Bit.id2(b17)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{_, WCon{Bit.k2(b18), WCon{Bit.k2(b19), WCon{Bit.k2(b20), WCon{Bit.k2(b21), WCon{Bit.k2(b22), WCon{Bit.k2(b23), WCon{Bit.k3(b24), WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k2(b18), b18, Bit.id2(b18)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{_, WCon{Bit.k2(b19), WCon{Bit.k2(b20), WCon{Bit.k2(b21), WCon{Bit.k2(b22), WCon{Bit.k2(b23), WCon{Bit.k3(b24), WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k2(b19), b19, Bit.id2(b19)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{_, WCon{Bit.k2(b20), WCon{Bit.k2(b21), WCon{Bit.k2(b22), WCon{Bit.k2(b23), WCon{Bit.k3(b24), WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k2(b20), b20, Bit.id2(b20)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{_, WCon{Bit.k2(b21), WCon{Bit.k2(b22), WCon{Bit.k2(b23), WCon{Bit.k3(b24), WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k2(b21), b21, Bit.id2(b21)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{_, WCon{Bit.k2(b22), WCon{Bit.k2(b23), WCon{Bit.k3(b24), WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k2(b22), b22, Bit.id2(b22)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{_, WCon{Bit.k2(b23), WCon{Bit.k3(b24), WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k2(b23), b23, Bit.id2(b23)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{_, WCon{Bit.k3(b24), WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k3(b24), b24, Bit.id3(b24)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{_, WCon{Bit.k3(b25), WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k3(b25), b25, Bit.id3(b25)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{_, WCon{Bit.k3(b26), WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k3(b26), b26, Bit.id3(b26)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{_, WCon{Bit.k3(b27), WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k3(b27), b27, Bit.id3(b27)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{_, WCon{Bit.k3(b28), WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k3(b28), b28, Bit.id3(b28)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{_, WCon{Bit.k3(b29), WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k3(b29), b29, Bit.id3(b29)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{_, WCon{Bit.k3(b30), WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k3(b30), b30, Bit.id3(b30)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{_, WCon{Bit.k3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          %Equal.sym(Bool, Bit.k3(b31), b31, Bit.id3(b31)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{_, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
                                                                                                                                          {==}

# Loads after stores
# ==================

# a load at A after a store at B, when A + 4 is at most B
def M.load_store_lo(+A: Nat, +B: Nat, +m: Wasm.Mem, +v: U32, +ha: {U32.to_nat(U32.from_nat(3n+A)) == 3n+A : Nat}, +hb: {U32.to_nat(U32.from_nat(3n+B)) == 3n+B : Nat},
  +h: {Nat.is_le(4n+A, B) == True{} : Bool}) ->
  {Wasm.Mem.load(U32.from_nat(A), Wasm.Mem.store(U32.from_nat(B), m, v)) == Wasm.Mem.load(U32.from_nat(A), m) : U32}:
  %Equal.sym(U32, Wasm.Mem.load(U32.from_nat(A), m), Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), m), Wasm.Mem.get_at(U32.from_nat(1n+A), m), Wasm.Mem.get_at(U32.from_nat(2n+A), m), Wasm.Mem.get_at(U32.from_nat(3n+A), m)), M.load_eq(A, m)) :
    {Wasm.Mem.load(U32.from_nat(A), Wasm.Mem.store(U32.from_nat(B), m, v)) == _ : U32}
  %Equal.sym(U32, Wasm.Mem.load(U32.from_nat(A), Wasm.Mem.store(U32.from_nat(B), m, v)), Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), Wasm.Mem.store(U32.from_nat(B), m, v)), Wasm.Mem.get_at(U32.from_nat(1n+A), Wasm.Mem.store(U32.from_nat(B), m, v)), Wasm.Mem.get_at(U32.from_nat(2n+A), Wasm.Mem.store(U32.from_nat(B), m, v)), Wasm.Mem.get_at(U32.from_nat(3n+A), Wasm.Mem.store(U32.from_nat(B), m, v))), M.load_eq(A, Wasm.Mem.store(U32.from_nat(B), m, v))) :
    {_ == Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), m), Wasm.Mem.get_at(U32.from_nat(1n+A), m), Wasm.Mem.get_at(U32.from_nat(2n+A), m), Wasm.Mem.get_at(U32.from_nat(3n+A), m)) : U32}
  %Equal.sym(Nat, Wasm.Mem.get_at(U32.from_nat(A), Wasm.Mem.store(U32.from_nat(B), m, v)), Wasm.Mem.get_at(U32.from_nat(A), m), M.get_store_far(A, B, m, v, Fits.down(3n, A, ha), hb, Nat.ne_lt(A, B, Shared.Nat.is_le_trans(1n+A, 4n+A, B, Shared.Nat.is_le_add_left(A, 3n), Shared.Nat.is_le_trans(4n+A, B, B, h, Shared.Nat.is_le_add_left(B, 0n)))), Nat.ne_lt(A, 1n+B, Shared.Nat.is_le_trans(1n+A, 4n+A, 1n+B, Shared.Nat.is_le_add_left(A, 3n), Shared.Nat.is_le_trans(4n+A, B, 1n+B, h, Shared.Nat.is_le_add_left(B, 1n)))), Nat.ne_lt(A, 2n+B, Shared.Nat.is_le_trans(1n+A, 4n+A, 2n+B, Shared.Nat.is_le_add_left(A, 3n), Shared.Nat.is_le_trans(4n+A, B, 2n+B, h, Shared.Nat.is_le_add_left(B, 2n)))), Nat.ne_lt(A, 3n+B, Shared.Nat.is_le_trans(1n+A, 4n+A, 3n+B, Shared.Nat.is_le_add_left(A, 3n), Shared.Nat.is_le_trans(4n+A, B, 3n+B, h, Shared.Nat.is_le_add_left(B, 3n)))))) :
    {Bytes.load(_, Wasm.Mem.get_at(U32.from_nat(1n+A), Wasm.Mem.store(U32.from_nat(B), m, v)), Wasm.Mem.get_at(U32.from_nat(2n+A), Wasm.Mem.store(U32.from_nat(B), m, v)), Wasm.Mem.get_at(U32.from_nat(3n+A), Wasm.Mem.store(U32.from_nat(B), m, v))) == Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), m), Wasm.Mem.get_at(U32.from_nat(1n+A), m), Wasm.Mem.get_at(U32.from_nat(2n+A), m), Wasm.Mem.get_at(U32.from_nat(3n+A), m)) : U32}
  %Equal.sym(Nat, Wasm.Mem.get_at(U32.from_nat(1n+A), Wasm.Mem.store(U32.from_nat(B), m, v)), Wasm.Mem.get_at(U32.from_nat(1n+A), m), M.get_store_far(1n+A, B, m, v, Fits.down(2n, 1n+A, ha), hb, Nat.ne_lt(1n+A, B, Shared.Nat.is_le_trans(1n+1n+A, 4n+A, B, Shared.Nat.is_le_add_left(A, 2n), Shared.Nat.is_le_trans(4n+A, B, B, h, Shared.Nat.is_le_add_left(B, 0n)))), Nat.ne_lt(1n+A, 1n+B, Shared.Nat.is_le_trans(1n+1n+A, 4n+A, 1n+B, Shared.Nat.is_le_add_left(A, 2n), Shared.Nat.is_le_trans(4n+A, B, 1n+B, h, Shared.Nat.is_le_add_left(B, 1n)))), Nat.ne_lt(1n+A, 2n+B, Shared.Nat.is_le_trans(1n+1n+A, 4n+A, 2n+B, Shared.Nat.is_le_add_left(A, 2n), Shared.Nat.is_le_trans(4n+A, B, 2n+B, h, Shared.Nat.is_le_add_left(B, 2n)))), Nat.ne_lt(1n+A, 3n+B, Shared.Nat.is_le_trans(1n+1n+A, 4n+A, 3n+B, Shared.Nat.is_le_add_left(A, 2n), Shared.Nat.is_le_trans(4n+A, B, 3n+B, h, Shared.Nat.is_le_add_left(B, 3n)))))) :
    {Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), m), _, Wasm.Mem.get_at(U32.from_nat(2n+A), Wasm.Mem.store(U32.from_nat(B), m, v)), Wasm.Mem.get_at(U32.from_nat(3n+A), Wasm.Mem.store(U32.from_nat(B), m, v))) == Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), m), Wasm.Mem.get_at(U32.from_nat(1n+A), m), Wasm.Mem.get_at(U32.from_nat(2n+A), m), Wasm.Mem.get_at(U32.from_nat(3n+A), m)) : U32}
  %Equal.sym(Nat, Wasm.Mem.get_at(U32.from_nat(2n+A), Wasm.Mem.store(U32.from_nat(B), m, v)), Wasm.Mem.get_at(U32.from_nat(2n+A), m), M.get_store_far(2n+A, B, m, v, Fits.down(1n, 2n+A, ha), hb, Nat.ne_lt(2n+A, B, Shared.Nat.is_le_trans(1n+2n+A, 4n+A, B, Shared.Nat.is_le_add_left(A, 1n), Shared.Nat.is_le_trans(4n+A, B, B, h, Shared.Nat.is_le_add_left(B, 0n)))), Nat.ne_lt(2n+A, 1n+B, Shared.Nat.is_le_trans(1n+2n+A, 4n+A, 1n+B, Shared.Nat.is_le_add_left(A, 1n), Shared.Nat.is_le_trans(4n+A, B, 1n+B, h, Shared.Nat.is_le_add_left(B, 1n)))), Nat.ne_lt(2n+A, 2n+B, Shared.Nat.is_le_trans(1n+2n+A, 4n+A, 2n+B, Shared.Nat.is_le_add_left(A, 1n), Shared.Nat.is_le_trans(4n+A, B, 2n+B, h, Shared.Nat.is_le_add_left(B, 2n)))), Nat.ne_lt(2n+A, 3n+B, Shared.Nat.is_le_trans(1n+2n+A, 4n+A, 3n+B, Shared.Nat.is_le_add_left(A, 1n), Shared.Nat.is_le_trans(4n+A, B, 3n+B, h, Shared.Nat.is_le_add_left(B, 3n)))))) :
    {Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), m), Wasm.Mem.get_at(U32.from_nat(1n+A), m), _, Wasm.Mem.get_at(U32.from_nat(3n+A), Wasm.Mem.store(U32.from_nat(B), m, v))) == Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), m), Wasm.Mem.get_at(U32.from_nat(1n+A), m), Wasm.Mem.get_at(U32.from_nat(2n+A), m), Wasm.Mem.get_at(U32.from_nat(3n+A), m)) : U32}
  %Equal.sym(Nat, Wasm.Mem.get_at(U32.from_nat(3n+A), Wasm.Mem.store(U32.from_nat(B), m, v)), Wasm.Mem.get_at(U32.from_nat(3n+A), m), M.get_store_far(3n+A, B, m, v, ha, hb, Nat.ne_lt(3n+A, B, Shared.Nat.is_le_trans(1n+3n+A, 4n+A, B, Shared.Nat.is_le_add_left(A, 0n), Shared.Nat.is_le_trans(4n+A, B, B, h, Shared.Nat.is_le_add_left(B, 0n)))), Nat.ne_lt(3n+A, 1n+B, Shared.Nat.is_le_trans(1n+3n+A, 4n+A, 1n+B, Shared.Nat.is_le_add_left(A, 0n), Shared.Nat.is_le_trans(4n+A, B, 1n+B, h, Shared.Nat.is_le_add_left(B, 1n)))), Nat.ne_lt(3n+A, 2n+B, Shared.Nat.is_le_trans(1n+3n+A, 4n+A, 2n+B, Shared.Nat.is_le_add_left(A, 0n), Shared.Nat.is_le_trans(4n+A, B, 2n+B, h, Shared.Nat.is_le_add_left(B, 2n)))), Nat.ne_lt(3n+A, 3n+B, Shared.Nat.is_le_trans(1n+3n+A, 4n+A, 3n+B, Shared.Nat.is_le_add_left(A, 0n), Shared.Nat.is_le_trans(4n+A, B, 3n+B, h, Shared.Nat.is_le_add_left(B, 3n)))))) :
    {Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), m), Wasm.Mem.get_at(U32.from_nat(1n+A), m), Wasm.Mem.get_at(U32.from_nat(2n+A), m), _) == Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), m), Wasm.Mem.get_at(U32.from_nat(1n+A), m), Wasm.Mem.get_at(U32.from_nat(2n+A), m), Wasm.Mem.get_at(U32.from_nat(3n+A), m)) : U32}
  {==}

# a load at A after a store at B, when B + 4 is at most A
def M.load_store_hi(+A: Nat, +B: Nat, +m: Wasm.Mem, +v: U32, +ha: {U32.to_nat(U32.from_nat(3n+A)) == 3n+A : Nat}, +hb: {U32.to_nat(U32.from_nat(3n+B)) == 3n+B : Nat},
  +h: {Nat.is_le(4n+B, A) == True{} : Bool}) ->
  {Wasm.Mem.load(U32.from_nat(A), Wasm.Mem.store(U32.from_nat(B), m, v)) == Wasm.Mem.load(U32.from_nat(A), m) : U32}:
  %Equal.sym(U32, Wasm.Mem.load(U32.from_nat(A), m), Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), m), Wasm.Mem.get_at(U32.from_nat(1n+A), m), Wasm.Mem.get_at(U32.from_nat(2n+A), m), Wasm.Mem.get_at(U32.from_nat(3n+A), m)), M.load_eq(A, m)) :
    {Wasm.Mem.load(U32.from_nat(A), Wasm.Mem.store(U32.from_nat(B), m, v)) == _ : U32}
  %Equal.sym(U32, Wasm.Mem.load(U32.from_nat(A), Wasm.Mem.store(U32.from_nat(B), m, v)), Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), Wasm.Mem.store(U32.from_nat(B), m, v)), Wasm.Mem.get_at(U32.from_nat(1n+A), Wasm.Mem.store(U32.from_nat(B), m, v)), Wasm.Mem.get_at(U32.from_nat(2n+A), Wasm.Mem.store(U32.from_nat(B), m, v)), Wasm.Mem.get_at(U32.from_nat(3n+A), Wasm.Mem.store(U32.from_nat(B), m, v))), M.load_eq(A, Wasm.Mem.store(U32.from_nat(B), m, v))) :
    {_ == Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), m), Wasm.Mem.get_at(U32.from_nat(1n+A), m), Wasm.Mem.get_at(U32.from_nat(2n+A), m), Wasm.Mem.get_at(U32.from_nat(3n+A), m)) : U32}
  %Equal.sym(Nat, Wasm.Mem.get_at(U32.from_nat(A), Wasm.Mem.store(U32.from_nat(B), m, v)), Wasm.Mem.get_at(U32.from_nat(A), m), M.get_store_far(A, B, m, v, Fits.down(3n, A, ha), hb, Nat.ne_gt(A, B, Shared.Nat.is_le_trans(1n+B, 4n+B, A, Shared.Nat.is_le_add_left(B, 3n), Shared.Nat.is_le_trans(4n+B, A, A, h, Shared.Nat.is_le_add_left(A, 0n)))), Nat.ne_gt(A, 1n+B, Shared.Nat.is_le_trans(1n+1n+B, 4n+B, A, Shared.Nat.is_le_add_left(B, 2n), Shared.Nat.is_le_trans(4n+B, A, A, h, Shared.Nat.is_le_add_left(A, 0n)))), Nat.ne_gt(A, 2n+B, Shared.Nat.is_le_trans(1n+2n+B, 4n+B, A, Shared.Nat.is_le_add_left(B, 1n), Shared.Nat.is_le_trans(4n+B, A, A, h, Shared.Nat.is_le_add_left(A, 0n)))), Nat.ne_gt(A, 3n+B, Shared.Nat.is_le_trans(1n+3n+B, 4n+B, A, Shared.Nat.is_le_add_left(B, 0n), Shared.Nat.is_le_trans(4n+B, A, A, h, Shared.Nat.is_le_add_left(A, 0n)))))) :
    {Bytes.load(_, Wasm.Mem.get_at(U32.from_nat(1n+A), Wasm.Mem.store(U32.from_nat(B), m, v)), Wasm.Mem.get_at(U32.from_nat(2n+A), Wasm.Mem.store(U32.from_nat(B), m, v)), Wasm.Mem.get_at(U32.from_nat(3n+A), Wasm.Mem.store(U32.from_nat(B), m, v))) == Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), m), Wasm.Mem.get_at(U32.from_nat(1n+A), m), Wasm.Mem.get_at(U32.from_nat(2n+A), m), Wasm.Mem.get_at(U32.from_nat(3n+A), m)) : U32}
  %Equal.sym(Nat, Wasm.Mem.get_at(U32.from_nat(1n+A), Wasm.Mem.store(U32.from_nat(B), m, v)), Wasm.Mem.get_at(U32.from_nat(1n+A), m), M.get_store_far(1n+A, B, m, v, Fits.down(2n, 1n+A, ha), hb, Nat.ne_gt(1n+A, B, Shared.Nat.is_le_trans(1n+B, 4n+B, 1n+A, Shared.Nat.is_le_add_left(B, 3n), Shared.Nat.is_le_trans(4n+B, A, 1n+A, h, Shared.Nat.is_le_add_left(A, 1n)))), Nat.ne_gt(1n+A, 1n+B, Shared.Nat.is_le_trans(1n+1n+B, 4n+B, 1n+A, Shared.Nat.is_le_add_left(B, 2n), Shared.Nat.is_le_trans(4n+B, A, 1n+A, h, Shared.Nat.is_le_add_left(A, 1n)))), Nat.ne_gt(1n+A, 2n+B, Shared.Nat.is_le_trans(1n+2n+B, 4n+B, 1n+A, Shared.Nat.is_le_add_left(B, 1n), Shared.Nat.is_le_trans(4n+B, A, 1n+A, h, Shared.Nat.is_le_add_left(A, 1n)))), Nat.ne_gt(1n+A, 3n+B, Shared.Nat.is_le_trans(1n+3n+B, 4n+B, 1n+A, Shared.Nat.is_le_add_left(B, 0n), Shared.Nat.is_le_trans(4n+B, A, 1n+A, h, Shared.Nat.is_le_add_left(A, 1n)))))) :
    {Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), m), _, Wasm.Mem.get_at(U32.from_nat(2n+A), Wasm.Mem.store(U32.from_nat(B), m, v)), Wasm.Mem.get_at(U32.from_nat(3n+A), Wasm.Mem.store(U32.from_nat(B), m, v))) == Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), m), Wasm.Mem.get_at(U32.from_nat(1n+A), m), Wasm.Mem.get_at(U32.from_nat(2n+A), m), Wasm.Mem.get_at(U32.from_nat(3n+A), m)) : U32}
  %Equal.sym(Nat, Wasm.Mem.get_at(U32.from_nat(2n+A), Wasm.Mem.store(U32.from_nat(B), m, v)), Wasm.Mem.get_at(U32.from_nat(2n+A), m), M.get_store_far(2n+A, B, m, v, Fits.down(1n, 2n+A, ha), hb, Nat.ne_gt(2n+A, B, Shared.Nat.is_le_trans(1n+B, 4n+B, 2n+A, Shared.Nat.is_le_add_left(B, 3n), Shared.Nat.is_le_trans(4n+B, A, 2n+A, h, Shared.Nat.is_le_add_left(A, 2n)))), Nat.ne_gt(2n+A, 1n+B, Shared.Nat.is_le_trans(1n+1n+B, 4n+B, 2n+A, Shared.Nat.is_le_add_left(B, 2n), Shared.Nat.is_le_trans(4n+B, A, 2n+A, h, Shared.Nat.is_le_add_left(A, 2n)))), Nat.ne_gt(2n+A, 2n+B, Shared.Nat.is_le_trans(1n+2n+B, 4n+B, 2n+A, Shared.Nat.is_le_add_left(B, 1n), Shared.Nat.is_le_trans(4n+B, A, 2n+A, h, Shared.Nat.is_le_add_left(A, 2n)))), Nat.ne_gt(2n+A, 3n+B, Shared.Nat.is_le_trans(1n+3n+B, 4n+B, 2n+A, Shared.Nat.is_le_add_left(B, 0n), Shared.Nat.is_le_trans(4n+B, A, 2n+A, h, Shared.Nat.is_le_add_left(A, 2n)))))) :
    {Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), m), Wasm.Mem.get_at(U32.from_nat(1n+A), m), _, Wasm.Mem.get_at(U32.from_nat(3n+A), Wasm.Mem.store(U32.from_nat(B), m, v))) == Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), m), Wasm.Mem.get_at(U32.from_nat(1n+A), m), Wasm.Mem.get_at(U32.from_nat(2n+A), m), Wasm.Mem.get_at(U32.from_nat(3n+A), m)) : U32}
  %Equal.sym(Nat, Wasm.Mem.get_at(U32.from_nat(3n+A), Wasm.Mem.store(U32.from_nat(B), m, v)), Wasm.Mem.get_at(U32.from_nat(3n+A), m), M.get_store_far(3n+A, B, m, v, ha, hb, Nat.ne_gt(3n+A, B, Shared.Nat.is_le_trans(1n+B, 4n+B, 3n+A, Shared.Nat.is_le_add_left(B, 3n), Shared.Nat.is_le_trans(4n+B, A, 3n+A, h, Shared.Nat.is_le_add_left(A, 3n)))), Nat.ne_gt(3n+A, 1n+B, Shared.Nat.is_le_trans(1n+1n+B, 4n+B, 3n+A, Shared.Nat.is_le_add_left(B, 2n), Shared.Nat.is_le_trans(4n+B, A, 3n+A, h, Shared.Nat.is_le_add_left(A, 3n)))), Nat.ne_gt(3n+A, 2n+B, Shared.Nat.is_le_trans(1n+2n+B, 4n+B, 3n+A, Shared.Nat.is_le_add_left(B, 1n), Shared.Nat.is_le_trans(4n+B, A, 3n+A, h, Shared.Nat.is_le_add_left(A, 3n)))), Nat.ne_gt(3n+A, 3n+B, Shared.Nat.is_le_trans(1n+3n+B, 4n+B, 3n+A, Shared.Nat.is_le_add_left(B, 0n), Shared.Nat.is_le_trans(4n+B, A, 3n+A, h, Shared.Nat.is_le_add_left(A, 3n)))))) :
    {Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), m), Wasm.Mem.get_at(U32.from_nat(1n+A), m), Wasm.Mem.get_at(U32.from_nat(2n+A), m), _) == Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), m), Wasm.Mem.get_at(U32.from_nat(1n+A), m), Wasm.Mem.get_at(U32.from_nat(2n+A), m), Wasm.Mem.get_at(U32.from_nat(3n+A), m)) : U32}
  {==}

def M.get_store_0(+A: Nat, +m: Wasm.Mem, +v: U32, +ha: {U32.to_nat(U32.from_nat(3n+A)) == 3n+A : Nat}) ->
  {Wasm.Mem.get_at(U32.from_nat(A), Wasm.Mem.store(U32.from_nat(A), m, v)) == Bytes.at(v, 0n) : Nat}:
  %Equal.sym(Wasm.Mem, Wasm.Mem.store(U32.from_nat(A), m, v), Bytes.store(A, m, v), M.store_eq(A, m, v)) :
    {Wasm.Mem.get_at(U32.from_nat(A), _) == Bytes.at(v, 0n) : Nat}
  Equal.trans(Nat, Wasm.Mem.get_at(U32.from_nat(A), Wasm.Mem.set_at(U32.from_nat(3n+A), Wasm.Mem.set_at(U32.from_nat(2n+A), Wasm.Mem.set_at(U32.from_nat(1n+A), Wasm.Mem.set_at(U32.from_nat(A), m, Bytes.at(v, 0n)), Bytes.at(v, 1n)), Bytes.at(v, 2n)), Bytes.at(v, 3n))), Wasm.Mem.get_at(U32.from_nat(A), Wasm.Mem.set_at(U32.from_nat(2n+A), Wasm.Mem.set_at(U32.from_nat(1n+A), Wasm.Mem.set_at(U32.from_nat(A), m, Bytes.at(v, 0n)), Bytes.at(v, 1n)), Bytes.at(v, 2n))), Bytes.at(v, 0n),
    M.get_skip(A, 3n+A, Wasm.Mem.set_at(U32.from_nat(2n+A), Wasm.Mem.set_at(U32.from_nat(1n+A), Wasm.Mem.set_at(U32.from_nat(A), m, Bytes.at(v, 0n)), Bytes.at(v, 1n)), Bytes.at(v, 2n)), Bytes.at(v, 3n), Fits.down(3n, A, ha), ha, Nat.ne_lt(A, 3n+A, Shared.Nat.is_le_add_left(A, 2n))),
    Equal.trans(Nat, Wasm.Mem.get_at(U32.from_nat(A), Wasm.Mem.set_at(U32.from_nat(2n+A), Wasm.Mem.set_at(U32.from_nat(1n+A), Wasm.Mem.set_at(U32.from_nat(A), m, Bytes.at(v, 0n)), Bytes.at(v, 1n)), Bytes.at(v, 2n))), Wasm.Mem.get_at(U32.from_nat(A), Wasm.Mem.set_at(U32.from_nat(1n+A), Wasm.Mem.set_at(U32.from_nat(A), m, Bytes.at(v, 0n)), Bytes.at(v, 1n))), Bytes.at(v, 0n),
    M.get_skip(A, 2n+A, Wasm.Mem.set_at(U32.from_nat(1n+A), Wasm.Mem.set_at(U32.from_nat(A), m, Bytes.at(v, 0n)), Bytes.at(v, 1n)), Bytes.at(v, 2n), Fits.down(3n, A, ha), Fits.down(1n, 2n+A, ha), Nat.ne_lt(A, 2n+A, Shared.Nat.is_le_add_left(A, 1n))),
    Equal.trans(Nat, Wasm.Mem.get_at(U32.from_nat(A), Wasm.Mem.set_at(U32.from_nat(1n+A), Wasm.Mem.set_at(U32.from_nat(A), m, Bytes.at(v, 0n)), Bytes.at(v, 1n))), Wasm.Mem.get_at(U32.from_nat(A), Wasm.Mem.set_at(U32.from_nat(A), m, Bytes.at(v, 0n))), Bytes.at(v, 0n),
    M.get_skip(A, 1n+A, Wasm.Mem.set_at(U32.from_nat(A), m, Bytes.at(v, 0n)), Bytes.at(v, 1n), Fits.down(3n, A, ha), Fits.down(2n, 1n+A, ha), Nat.ne_lt(A, 1n+A, Shared.Nat.is_le_add_left(A, 0n))),
    M.get_hit(A, m, Bytes.at(v, 0n), Fits.down(3n, A, ha)))))

def M.get_store_1(+A: Nat, +m: Wasm.Mem, +v: U32, +ha: {U32.to_nat(U32.from_nat(3n+A)) == 3n+A : Nat}) ->
  {Wasm.Mem.get_at(U32.from_nat(1n+A), Wasm.Mem.store(U32.from_nat(A), m, v)) == Bytes.at(v, 1n) : Nat}:
  %Equal.sym(Wasm.Mem, Wasm.Mem.store(U32.from_nat(A), m, v), Bytes.store(A, m, v), M.store_eq(A, m, v)) :
    {Wasm.Mem.get_at(U32.from_nat(1n+A), _) == Bytes.at(v, 1n) : Nat}
  Equal.trans(Nat, Wasm.Mem.get_at(U32.from_nat(1n+A), Wasm.Mem.set_at(U32.from_nat(3n+A), Wasm.Mem.set_at(U32.from_nat(2n+A), Wasm.Mem.set_at(U32.from_nat(1n+A), Wasm.Mem.set_at(U32.from_nat(A), m, Bytes.at(v, 0n)), Bytes.at(v, 1n)), Bytes.at(v, 2n)), Bytes.at(v, 3n))), Wasm.Mem.get_at(U32.from_nat(1n+A), Wasm.Mem.set_at(U32.from_nat(2n+A), Wasm.Mem.set_at(U32.from_nat(1n+A), Wasm.Mem.set_at(U32.from_nat(A), m, Bytes.at(v, 0n)), Bytes.at(v, 1n)), Bytes.at(v, 2n))), Bytes.at(v, 1n),
    M.get_skip(1n+A, 3n+A, Wasm.Mem.set_at(U32.from_nat(2n+A), Wasm.Mem.set_at(U32.from_nat(1n+A), Wasm.Mem.set_at(U32.from_nat(A), m, Bytes.at(v, 0n)), Bytes.at(v, 1n)), Bytes.at(v, 2n)), Bytes.at(v, 3n), Fits.down(2n, 1n+A, ha), ha, Nat.ne_lt(A, 2n+A, Shared.Nat.is_le_add_left(A, 1n))),
    Equal.trans(Nat, Wasm.Mem.get_at(U32.from_nat(1n+A), Wasm.Mem.set_at(U32.from_nat(2n+A), Wasm.Mem.set_at(U32.from_nat(1n+A), Wasm.Mem.set_at(U32.from_nat(A), m, Bytes.at(v, 0n)), Bytes.at(v, 1n)), Bytes.at(v, 2n))), Wasm.Mem.get_at(U32.from_nat(1n+A), Wasm.Mem.set_at(U32.from_nat(1n+A), Wasm.Mem.set_at(U32.from_nat(A), m, Bytes.at(v, 0n)), Bytes.at(v, 1n))), Bytes.at(v, 1n),
    M.get_skip(1n+A, 2n+A, Wasm.Mem.set_at(U32.from_nat(1n+A), Wasm.Mem.set_at(U32.from_nat(A), m, Bytes.at(v, 0n)), Bytes.at(v, 1n)), Bytes.at(v, 2n), Fits.down(2n, 1n+A, ha), Fits.down(1n, 2n+A, ha), Nat.ne_lt(A, 1n+A, Shared.Nat.is_le_add_left(A, 0n))),
    M.get_hit(1n+A, Wasm.Mem.set_at(U32.from_nat(A), m, Bytes.at(v, 0n)), Bytes.at(v, 1n), Fits.down(2n, 1n+A, ha))))

def M.get_store_2(+A: Nat, +m: Wasm.Mem, +v: U32, +ha: {U32.to_nat(U32.from_nat(3n+A)) == 3n+A : Nat}) ->
  {Wasm.Mem.get_at(U32.from_nat(2n+A), Wasm.Mem.store(U32.from_nat(A), m, v)) == Bytes.at(v, 2n) : Nat}:
  %Equal.sym(Wasm.Mem, Wasm.Mem.store(U32.from_nat(A), m, v), Bytes.store(A, m, v), M.store_eq(A, m, v)) :
    {Wasm.Mem.get_at(U32.from_nat(2n+A), _) == Bytes.at(v, 2n) : Nat}
  Equal.trans(Nat, Wasm.Mem.get_at(U32.from_nat(2n+A), Wasm.Mem.set_at(U32.from_nat(3n+A), Wasm.Mem.set_at(U32.from_nat(2n+A), Wasm.Mem.set_at(U32.from_nat(1n+A), Wasm.Mem.set_at(U32.from_nat(A), m, Bytes.at(v, 0n)), Bytes.at(v, 1n)), Bytes.at(v, 2n)), Bytes.at(v, 3n))), Wasm.Mem.get_at(U32.from_nat(2n+A), Wasm.Mem.set_at(U32.from_nat(2n+A), Wasm.Mem.set_at(U32.from_nat(1n+A), Wasm.Mem.set_at(U32.from_nat(A), m, Bytes.at(v, 0n)), Bytes.at(v, 1n)), Bytes.at(v, 2n))), Bytes.at(v, 2n),
    M.get_skip(2n+A, 3n+A, Wasm.Mem.set_at(U32.from_nat(2n+A), Wasm.Mem.set_at(U32.from_nat(1n+A), Wasm.Mem.set_at(U32.from_nat(A), m, Bytes.at(v, 0n)), Bytes.at(v, 1n)), Bytes.at(v, 2n)), Bytes.at(v, 3n), Fits.down(1n, 2n+A, ha), ha, Nat.ne_lt(A, 1n+A, Shared.Nat.is_le_add_left(A, 0n))),
    M.get_hit(2n+A, Wasm.Mem.set_at(U32.from_nat(1n+A), Wasm.Mem.set_at(U32.from_nat(A), m, Bytes.at(v, 0n)), Bytes.at(v, 1n)), Bytes.at(v, 2n), Fits.down(1n, 2n+A, ha)))

def M.get_store_3(+A: Nat, +m: Wasm.Mem, +v: U32, +ha: {U32.to_nat(U32.from_nat(3n+A)) == 3n+A : Nat}) ->
  {Wasm.Mem.get_at(U32.from_nat(3n+A), Wasm.Mem.store(U32.from_nat(A), m, v)) == Bytes.at(v, 3n) : Nat}:
  %Equal.sym(Wasm.Mem, Wasm.Mem.store(U32.from_nat(A), m, v), Bytes.store(A, m, v), M.store_eq(A, m, v)) :
    {Wasm.Mem.get_at(U32.from_nat(3n+A), _) == Bytes.at(v, 3n) : Nat}
  M.get_hit(3n+A, Wasm.Mem.set_at(U32.from_nat(2n+A), Wasm.Mem.set_at(U32.from_nat(1n+A), Wasm.Mem.set_at(U32.from_nat(A), m, Bytes.at(v, 0n)), Bytes.at(v, 1n)), Bytes.at(v, 2n)), Bytes.at(v, 3n), ha)

# a load after a store at the same address gives what was stored
def M.load_store(+A: Nat, +m: Wasm.Mem, +v: U32, +ha: {U32.to_nat(U32.from_nat(3n+A)) == 3n+A : Nat}) ->
  {Wasm.Mem.load(U32.from_nat(A), Wasm.Mem.store(U32.from_nat(A), m, v)) == v : U32}:
  %Equal.sym(U32, Wasm.Mem.load(U32.from_nat(A), Wasm.Mem.store(U32.from_nat(A), m, v)), Bytes.load(Wasm.Mem.get_at(U32.from_nat(A), Wasm.Mem.store(U32.from_nat(A), m, v)), Wasm.Mem.get_at(U32.from_nat(1n+A), Wasm.Mem.store(U32.from_nat(A), m, v)), Wasm.Mem.get_at(U32.from_nat(2n+A), Wasm.Mem.store(U32.from_nat(A), m, v)), Wasm.Mem.get_at(U32.from_nat(3n+A), Wasm.Mem.store(U32.from_nat(A), m, v))), M.load_eq(A, Wasm.Mem.store(U32.from_nat(A), m, v))) :
    {_ == v : U32}
  %Equal.sym(Nat, Wasm.Mem.get_at(U32.from_nat(A), Wasm.Mem.store(U32.from_nat(A), m, v)), Bytes.at(v, 0n), M.get_store_0(A, m, v, ha)) :
    {Bytes.load(_, Wasm.Mem.get_at(U32.from_nat(1n+A), Wasm.Mem.store(U32.from_nat(A), m, v)), Wasm.Mem.get_at(U32.from_nat(2n+A), Wasm.Mem.store(U32.from_nat(A), m, v)), Wasm.Mem.get_at(U32.from_nat(3n+A), Wasm.Mem.store(U32.from_nat(A), m, v))) == v : U32}
  %Equal.sym(Nat, Wasm.Mem.get_at(U32.from_nat(1n+A), Wasm.Mem.store(U32.from_nat(A), m, v)), Bytes.at(v, 1n), M.get_store_1(A, m, v, ha)) :
    {Bytes.load(Bytes.at(v, 0n), _, Wasm.Mem.get_at(U32.from_nat(2n+A), Wasm.Mem.store(U32.from_nat(A), m, v)), Wasm.Mem.get_at(U32.from_nat(3n+A), Wasm.Mem.store(U32.from_nat(A), m, v))) == v : U32}
  %Equal.sym(Nat, Wasm.Mem.get_at(U32.from_nat(2n+A), Wasm.Mem.store(U32.from_nat(A), m, v)), Bytes.at(v, 2n), M.get_store_2(A, m, v, ha)) :
    {Bytes.load(Bytes.at(v, 0n), Bytes.at(v, 1n), _, Wasm.Mem.get_at(U32.from_nat(3n+A), Wasm.Mem.store(U32.from_nat(A), m, v))) == v : U32}
  %Equal.sym(Nat, Wasm.Mem.get_at(U32.from_nat(3n+A), Wasm.Mem.store(U32.from_nat(A), m, v)), Bytes.at(v, 3n), M.get_store_3(A, m, v, ha)) :
    {Bytes.load(Bytes.at(v, 0n), Bytes.at(v, 1n), Bytes.at(v, 2n), _) == v : U32}
  %Equal.sym(U32, U32.from_nat(U32.to_nat(U32.and(v, 255))), U32.and(v, 255), U.from_to_nat(U32.and(v, 255))) :
    {U32.or(U32.or(_, U32.shln(U32.from_nat(Bytes.at(v, 1n)), 8n)), U32.or(U32.shln(U32.from_nat(Bytes.at(v, 2n)), 16n), U32.shln(U32.from_nat(Bytes.at(v, 3n)), 24n))) == v : U32}
  %Equal.sym(U32, U32.from_nat(U32.to_nat(U32.and(U32.shrn(v, 8n), 255))), U32.and(U32.shrn(v, 8n), 255), U.from_to_nat(U32.and(U32.shrn(v, 8n), 255))) :
    {U32.or(U32.or(U32.and(v, 255), U32.shln(_, 8n)), U32.or(U32.shln(U32.from_nat(Bytes.at(v, 2n)), 16n), U32.shln(U32.from_nat(Bytes.at(v, 3n)), 24n))) == v : U32}
  %Equal.sym(U32, U32.from_nat(U32.to_nat(U32.and(U32.shrn(v, 16n), 255))), U32.and(U32.shrn(v, 16n), 255), U.from_to_nat(U32.and(U32.shrn(v, 16n), 255))) :
    {U32.or(U32.or(U32.and(v, 255), U32.shln(U32.and(U32.shrn(v, 8n), 255), 8n)), U32.or(U32.shln(_, 16n), U32.shln(U32.from_nat(Bytes.at(v, 3n)), 24n))) == v : U32}
  %Equal.sym(U32, U32.from_nat(U32.to_nat(U32.and(U32.shrn(v, 24n), 255))), U32.and(U32.shrn(v, 24n), 255), U.from_to_nat(U32.and(U32.shrn(v, 24n), 255))) :
    {U32.or(U32.or(U32.and(v, 255), U32.shln(U32.and(U32.shrn(v, 8n), 255), 8n)), U32.or(U32.shln(U32.and(U32.shrn(v, 16n), 255), 16n), U32.shln(_, 24n))) == v : U32}
  U.bytes_id(v)
