import Base
import ./impl.bend as C

# the word of n bits whose k lowest bits are set
def Word.low(n: Nat, k: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match k:
        case 0n:
          WCon{False{}, Word.low(p, 0n)}
        case 1n+q:
          WCon{True{}, Word.low(p, q)}

def lit127() -> {U32{Word.low(32n, 7n)} == 127 : U32}:
  {==}

def lit0() -> {U32{Word.zero(32n)} == 0 : U32}:
  {==}

# the bits of w where m is set, and False elsewhere (matching m first)
def Word.andm(n: Nat, w: Word(n), m: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w m:
        case WCon{a, t} WCon{True{}, mt}:
          WCon{a, Word.andm(p, t, mt)}
        case WCon{a, t} WCon{False{}, mt}:
          WCon{False{}, Word.andm(p, t, mt)}

# the bits of w where m is clear, and False elsewhere
def Word.sel(n: Nat, w: Word(n), m: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w m:
        case WCon{a, t} WCon{True{}, mt}:
          WCon{False{}, Word.sel(p, t, mt)}
        case WCon{a, t} WCon{False{}, mt}:
          WCon{a, Word.sel(p, t, mt)}

def Word.and_is_andm(n: Nat, w: Word(n), m: Word(n)) -> {Word.and(n, w, m) == Word.andm(n, w, m) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w m:
        case WCon{True{}, t} WCon{True{}, mt}:
          %Word.and_is_andm(p, t, mt) : {WCon{True{}, Word.and(p, t, mt)} == WCon{True{}, _} : Word(1n+p)}
          {==}
        case WCon{False{}, t} WCon{True{}, mt}:
          %Word.and_is_andm(p, t, mt) : {WCon{False{}, Word.and(p, t, mt)} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, t} WCon{False{}, mt}:
          %Word.and_is_andm(p, t, mt) : {WCon{False{}, Word.and(p, t, mt)} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{False{}, t} WCon{False{}, mt}:
          %Word.and_is_andm(p, t, mt) : {WCon{False{}, Word.and(p, t, mt)} == WCon{False{}, _} : Word(1n+p)}
          {==}

def T(b: Bool) -> Data:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def ft.empty(h: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, h) : T(_)
  Unit{}

# False is not True
def ft(-G: Type, h: {False{} == True{} : Bool}) -> G:
  Empty.absurd(G, ft.empty(h))

# w is the bits of w where m is set, with the bits where it is clear
def Word.or_and_sel(n: Nat, w: Word(n), m: Word(n)) ->
  {Word.or(n, Word.and(n, w, m), Word.sel(n, w, m)) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w m:
        case WCon{True{}, t} WCon{True{}, mt}:
          %Word.or_and_sel(p, t, mt) : {WCon{True{}, Word.or(p, Word.and(p, t, mt), Word.sel(p, t, mt))} == WCon{True{}, _} : Word(1n+p)}
          {==}
        case WCon{False{}, t} WCon{True{}, mt}:
          %Word.or_and_sel(p, t, mt) : {WCon{False{}, Word.or(p, Word.and(p, t, mt), Word.sel(p, t, mt))} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, t} WCon{False{}, mt}:
          %Word.or_and_sel(p, t, mt) : {WCon{True{}, Word.or(p, Word.and(p, t, mt), Word.sel(p, t, mt))} == WCon{True{}, _} : Word(1n+p)}
          {==}
        case WCon{False{}, t} WCon{False{}, mt}:
          %Word.or_and_sel(p, t, mt) : {WCon{False{}, Word.or(p, Word.and(p, t, mt), Word.sel(p, t, mt))} == WCon{False{}, _} : Word(1n+p)}
          {==}

# w with no bits cleared, then all kept, is w
def Word.and_or_zero(n: Nat, w: Word(n)) ->
  {Word.and(n, Word.or(n, w, Word.zero(n)), Word.low(n, n)) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{True{}, t}:
          %Word.and_or_zero(p, t) : {WCon{True{}, Word.and(p, Word.or(p, t, Word.zero(p)), Word.low(p, p))} == WCon{True{}, _} : Word(1n+p)}
          {==}
        case WCon{False{}, t}:
          %Word.and_or_zero(p, t) : {WCon{False{}, Word.and(p, Word.or(p, t, Word.zero(p)), Word.low(p, p))} == WCon{False{}, _} : Word(1n+p)}
          {==}

def Cmp.fin_lt(a: Bool, c: Cmp) -> {Cmp.is_lt(Word.cmp.fin(a, False{}, c)) == Cmp.is_lt(c) : Bool}:
  match a c:
    case _ LT{}:
      {==}
    case _ GT{}:
      {==}
    case True{} EQ{}:
      {==}
    case False{} EQ{}:
      {==}

# no word is below zero
def Word.not_lt_zero(n: Nat, w: Word(n)) -> {Cmp.is_lt(Word.cmp(n, w, Word.zero(n))) == False{} : Bool}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+(+p):
      match w:
        case WCon{+a, +t}:
          Equal.trans(Bool, Cmp.is_lt(Word.cmp.fin(a, False{}, Word.cmp(p, t, Word.zero(p)))),
            Cmp.is_lt(Word.cmp(p, t, Word.zero(p))), False{},
            Cmp.fin_lt(a, Word.cmp(p, t, Word.zero(p))), Word.not_lt_zero(p, t))

def Cmp.fin_eq.bit(a: Bool, c: Cmp, h: {Cmp.is_eq(Word.cmp.fin(a, False{}, c)) == True{} : Bool}) -> {a == False{} : Bool}:
  match a c:
    case True{} LT{}:
      ft({True{} == False{} : Bool}, h)
    case True{} GT{}:
      ft({True{} == False{} : Bool}, h)
    case True{} EQ{}:
      ft({True{} == False{} : Bool}, h)
    case False{} _:
      {==}

def Cmp.fin_eq.rest(a: Bool, c: Cmp, h: {Cmp.is_eq(Word.cmp.fin(a, False{}, c)) == True{} : Bool}) -> {Cmp.is_eq(c) == True{} : Bool}:
  match c:
    case LT{}:
      ft({False{} == True{} : Bool}, h)
    case GT{}:
      ft({False{} == True{} : Bool}, h)
    case EQ{}:
      {==}

# a word equal to zero is zero
def Word.eq_zero(n: Nat, w: Word(n), +h: {Cmp.is_eq(Word.cmp(n, w, Word.zero(n))) == True{} : Bool}) -> {w == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+(+p):
      match w:
        case WCon{+a, +t}:
          +c = Word.cmp(p, t, Word.zero(p))
          %Equal.sym(Bool, a, False{}, Cmp.fin_eq.bit(a, c, h)) : {WCon{_, t} == WCon{False{}, Word.zero(p)} : Word(1n+p)}
          %Equal.sym(Word(p), t, Word.zero(p), Word.eq_zero(p, t, Cmp.fin_eq.rest(a, c, h))) : {WCon{False{}, _} == WCon{False{}, Word.zero(p)} : Word(1n+p)}
          {==}

# the word of n bits without its top bit
def Word.init(n: Nat, w: Word(1n+n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          WCon{b, Word.init(p, t)}

# the 25 low bits of a word of 32
def Word.low25(w: Word(32n)) -> Word(25n):
  Word.init(25n, Word.init(26n, Word.init(27n, Word.init(28n, Word.init(29n, Word.init(30n, Word.init(31n, w)))))))

# a word of 7 bits, then 25 zeros
def Word.ext7(u: Word(7n)) -> Word(32n):
  match u:
    case WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WNil{}}}}}}}}:
      WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

# U32 facts about the low byte of a LEB128 number

def U32.and127_lt(+x: U32) -> {U32.is_lt(U32.and(x, 127), 128) == True{} : Bool}:
  match x:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, WCon{+b6, WCon{+b7, WCon{+b8, WCon{+b9, WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WCon{+b16, WCon{+b17, WCon{+b18, WCon{+b19, WCon{+b20, WCon{+b21, WCon{+b22, WCon{+b23, WCon{+b24, WCon{+b25, WCon{+b26, WCon{+b27, WCon{+b28, WCon{+b29, WCon{+b30, WCon{+b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %Equal.sym(Word(32n), Word.and(32n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, Word.low(32n, 7n)), Word.andm(32n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, Word.low(32n, 7n)), Word.and_is_andm(32n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, Word.low(32n, 7n))) : {U32.is_lt(U32{_}, 128) == True{} : Bool}
      {==}

def U32.or128_not_lt(+x: U32) -> {U32.is_lt(U32.or(U32.and(x, 127), 128), 128) == False{} : Bool}:
  match x:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, WCon{+b6, WCon{+b7, WCon{+b8, WCon{+b9, WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WCon{+b16, WCon{+b17, WCon{+b18, WCon{+b19, WCon{+b20, WCon{+b21, WCon{+b22, WCon{+b23, WCon{+b24, WCon{+b25, WCon{+b26, WCon{+b27, WCon{+b28, WCon{+b29, WCon{+b30, WCon{+b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %Equal.sym(Word(32n), Word.and(32n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, Word.low(32n, 7n)), Word.andm(32n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, Word.low(32n, 7n)), Word.and_is_andm(32n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, Word.low(32n, 7n))) : {U32.is_lt(U32.or(U32{_}, 128), 128) == False{} : Bool}
      Word.not_lt_zero(7n, Word.or(7n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WNil{}}}}}}}}, Word.zero(7n)))

def U32.or128_low(+x: U32) -> {U32.and(U32.or(U32.and(x, 127), 128), 127) == U32.and(x, 127) : U32}:
  match x:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, WCon{+b6, WCon{+b7, WCon{+b8, WCon{+b9, WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WCon{+b16, WCon{+b17, WCon{+b18, WCon{+b19, WCon{+b20, WCon{+b21, WCon{+b22, WCon{+b23, WCon{+b24, WCon{+b25, WCon{+b26, WCon{+b27, WCon{+b28, WCon{+b29, WCon{+b30, WCon{+b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %Equal.sym(Word(32n), Word.and(32n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, Word.low(32n, 7n)), Word.andm(32n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, Word.low(32n, 7n)), Word.and_is_andm(32n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, Word.low(32n, 7n))) : {U32.and(U32.or(U32{_}, 128), 127) == U32{_} : U32}
      Equal.cong(Word(7n), U32, u => U32{Word.ext7(u)},
        Word.and(7n, Word.or(7n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WNil{}}}}}}}}, Word.zero(7n)), Word.low(7n, 7n)), WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WNil{}}}}}}}},
        Word.and_or_zero(7n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WNil{}}}}}}}}))

def U32.split7(+x: U32) -> {U32.or(U32.and(x, 127), U32.shln(U32.shrn(x, 7n), 7n)) == x : U32}:
  match x:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, WCon{+b6, WCon{+b7, WCon{+b8, WCon{+b9, WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WCon{+b16, WCon{+b17, WCon{+b18, WCon{+b19, WCon{+b20, WCon{+b21, WCon{+b22, WCon{+b23, WCon{+b24, WCon{+b25, WCon{+b26, WCon{+b27, WCon{+b28, WCon{+b29, WCon{+b30, WCon{+b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Equal.cong(Word(32n), U32, u => U32{u},
        Word.or(32n, Word.and(32n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, Word.low(32n, 7n)), Word.sel(32n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, Word.low(32n, 7n))), WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},
        Word.or_and_sel(32n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, Word.low(32n, 7n)))

def U32.small_low(+x: U32, +h: {U32.is_zero(U32.shrn(x, 7n)) == True{} : Bool}) -> {U32.and(x, 127) == x : U32}:
  match x:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, WCon{+b6, WCon{+b7, WCon{+b8, WCon{+b9, WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WCon{+b16, WCon{+b17, WCon{+b18, WCon{+b19, WCon{+b20, WCon{+b21, WCon{+b22, WCon{+b23, WCon{+b24, WCon{+b25, WCon{+b26, WCon{+b27, WCon{+b28, WCon{+b29, WCon{+b30, WCon{+b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      +e = Word.eq_zero(32n, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, h)
      %Equal.sym(Word(32n), Word.and(32n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, Word.low(32n, 7n)), Word.andm(32n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, Word.low(32n, 7n)), Word.and_is_andm(32n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, Word.low(32n, 7n))) : {U32{_} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
      Equal.cong(Word(32n), U32, u => U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, Word.low25(u)}}}}}}}},
        Word.zero(32n), WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, Equal.sym(Word(32n), WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, Word.zero(32n), e))
