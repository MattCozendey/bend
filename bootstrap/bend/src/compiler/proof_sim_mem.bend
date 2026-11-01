# compiler: the bytes of the model's memory
# =========================================
#
# Wasm.Bytes is a tree over the bits of an address. B.get(n, w, m) is the
# byte at the address w; a read gives it and the same bytes (peek.eq); a
# write sets it (get.set.same) and keeps every other address (get.set.other).
# On U32 addresses: R8, the byte that read8 gives; V32, the word that read32
# gives (read32.eq), the bytes of a word put back together (recomp), and the
# words and bytes after write8 and write32.

import Base
import ./impl.bend as C
import ./proof_need.bend as N
import ./proof_instrs.bend as I
import ./proof_halt.bend as PH

# a pair of two Data types, itself Data
def P2(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

# The tree
# --------

# the byte at the address of the n bits w
def B.get(n: Nat, w: Word(n), m: C.Wasm.Bytes) -> U32:
  match n:
    case 0n:
      match m:
        case C.Wasm.Bytes.byte{b}:
          b
        case C.Wasm.Bytes.zero{}:
          0
        case C.Wasm.Bytes.node{_, _}:
          0
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          match m:
            case C.Wasm.Bytes.node{lo, _}:
              B.get(p, t, lo)
            case C.Wasm.Bytes.zero{}:
              0
            case C.Wasm.Bytes.byte{_}:
              0
        case WCon{True{}, t}:
          match m:
            case C.Wasm.Bytes.node{_, hi}:
              B.get(p, t, hi)
            case C.Wasm.Bytes.zero{}:
              0
            case C.Wasm.Bytes.byte{_}:
              0

# a peek gives the byte, and the bytes as they were
def peek.eq(+n: Nat, +w: Word(n), +m: C.Wasm.Bytes) ->
  {C.Wasm.Bytes.peek(n, w, m) == C.Wasm.Peek{B.get(n, w, m), m} : C.Wasm.Peek}:
  match n:
    case 0n:
      match m:
        case C.Wasm.Bytes.byte{+b}:
          {==}
        case C.Wasm.Bytes.zero{}:
          {==}
        case C.Wasm.Bytes.node{+lo, +hi}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          match m:
            case C.Wasm.Bytes.node{+lo, +hi}:
              Equal.cong(C.Wasm.Peek, C.Wasm.Peek, r => C.Wasm.Bytes.peek.lo(r, hi), C.Wasm.Bytes.peek(p, t, lo),
                C.Wasm.Peek{B.get(p, t, lo), lo}, peek.eq(p, t, lo))
            case C.Wasm.Bytes.zero{}:
              {==}
            case C.Wasm.Bytes.byte{+b}:
              {==}
        case WCon{True{}, +t}:
          match m:
            case C.Wasm.Bytes.node{+lo, +hi}:
              Equal.cong(C.Wasm.Peek, C.Wasm.Peek, r => C.Wasm.Bytes.peek.hi(lo, r), C.Wasm.Bytes.peek(p, t, hi),
                C.Wasm.Peek{B.get(p, t, hi), hi}, peek.eq(p, t, hi))
            case C.Wasm.Bytes.zero{}:
              {==}
            case C.Wasm.Bytes.byte{+b}:
              {==}

# the bytes that are all 0
def get.zero(+n: Nat, +w: Word(n)) -> {B.get(n, w, C.Wasm.Bytes.zero{}) == 0 : U32}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          {==}
        case WCon{True{}, t}:
          {==}

# a write sets its address
def get.set.same(+n: Nat, +w: Word(n), +m: C.Wasm.Bytes, +b: U32) ->
  {B.get(n, w, C.Wasm.Bytes.set(n, w, m, b)) == b : U32}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          match m:
            case C.Wasm.Bytes.node{+lo, +hi}:
              get.set.same(p, t, lo, b)
            case C.Wasm.Bytes.zero{}:
              get.set.same(p, t, C.Wasm.Bytes.zero{}, b)
            case C.Wasm.Bytes.byte{+x}:
              get.set.same(p, t, C.Wasm.Bytes.zero{}, b)
        case WCon{True{}, +t}:
          match m:
            case C.Wasm.Bytes.node{+lo, +hi}:
              get.set.same(p, t, hi, b)
            case C.Wasm.Bytes.zero{}:
              get.set.same(p, t, C.Wasm.Bytes.zero{}, b)
            case C.Wasm.Bytes.byte{+x}:
              get.set.same(p, t, C.Wasm.Bytes.zero{}, b)

# two equal bits leave the comparison of the rest
def fin.tt(c: Cmp) -> {Cmp.is_eq(Word.cmp.fin(True{}, True{}, c)) == Cmp.is_eq(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def fin.ff(c: Cmp) -> {Cmp.is_eq(Word.cmp.fin(False{}, False{}, c)) == Cmp.is_eq(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# the rest of two addresses whose low bits agree differ
def ne.ff(+c: Cmp, ne: {Cmp.is_eq(Word.cmp.fin(False{}, False{}, c)) == False{} : Bool}) -> {Cmp.is_eq(c) == False{} : Bool}:
  Equal.trans(Bool, Cmp.is_eq(c), Cmp.is_eq(Word.cmp.fin(False{}, False{}, c)), False{},
    Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(False{}, False{}, c)), Cmp.is_eq(c), fin.ff(c)), ne)

def ne.tt(+c: Cmp, ne: {Cmp.is_eq(Word.cmp.fin(True{}, True{}, c)) == False{} : Bool}) -> {Cmp.is_eq(c) == False{} : Bool}:
  Equal.trans(Bool, Cmp.is_eq(c), Cmp.is_eq(Word.cmp.fin(True{}, True{}, c)), False{},
    Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(True{}, True{}, c)), Cmp.is_eq(c), fin.tt(c)), ne)

# a write keeps every other address
def get.set.other(+n: Nat, +w: Word(n), +w2: Word(n), +m: C.Wasm.Bytes, +b: U32,
  ne: {Cmp.is_eq(Word.cmp(n, w2, w)) == False{} : Bool}) ->
  {B.get(n, w2, C.Wasm.Bytes.set(n, w, m, b)) == B.get(n, w2, m) : U32}:
  match n:
    case 0n:
      match w w2:
        case WNil{} WNil{}:
          Empty.absurd({B.get(0n, WNil{}, C.Wasm.Bytes.set(0n, WNil{}, m, b)) == B.get(0n, WNil{}, m) : U32}, N.true_ne_false(ne))
    case 1n+p:
      match w w2:
        case WCon{False{}, +t} WCon{False{}, +t2}:
          match m:
            case C.Wasm.Bytes.node{+lo, +hi}:
              get.set.other(p, t, t2, lo, b, ne.ff(Word.cmp(p, t2, t), ne))
            case C.Wasm.Bytes.zero{}:
              Equal.trans(U32, B.get(p, t2, C.Wasm.Bytes.set(p, t, C.Wasm.Bytes.zero{}, b)), B.get(p, t2, C.Wasm.Bytes.zero{}), 0,
                get.set.other(p, t, t2, C.Wasm.Bytes.zero{}, b, ne.ff(Word.cmp(p, t2, t), ne)), get.zero(p, t2))
            case C.Wasm.Bytes.byte{+x}:
              Equal.trans(U32, B.get(p, t2, C.Wasm.Bytes.set(p, t, C.Wasm.Bytes.zero{}, b)), B.get(p, t2, C.Wasm.Bytes.zero{}), 0,
                get.set.other(p, t, t2, C.Wasm.Bytes.zero{}, b, ne.ff(Word.cmp(p, t2, t), ne)), get.zero(p, t2))
        case WCon{True{}, +t} WCon{True{}, +t2}:
          match m:
            case C.Wasm.Bytes.node{+lo, +hi}:
              get.set.other(p, t, t2, hi, b, ne.tt(Word.cmp(p, t2, t), ne))
            case C.Wasm.Bytes.zero{}:
              Equal.trans(U32, B.get(p, t2, C.Wasm.Bytes.set(p, t, C.Wasm.Bytes.zero{}, b)), B.get(p, t2, C.Wasm.Bytes.zero{}), 0,
                get.set.other(p, t, t2, C.Wasm.Bytes.zero{}, b, ne.tt(Word.cmp(p, t2, t), ne)), get.zero(p, t2))
            case C.Wasm.Bytes.byte{+x}:
              Equal.trans(U32, B.get(p, t2, C.Wasm.Bytes.set(p, t, C.Wasm.Bytes.zero{}, b)), B.get(p, t2, C.Wasm.Bytes.zero{}), 0,
                get.set.other(p, t, t2, C.Wasm.Bytes.zero{}, b, ne.tt(Word.cmp(p, t2, t), ne)), get.zero(p, t2))
        case WCon{False{}, +t} WCon{True{}, +t2}:
          match m:
            case C.Wasm.Bytes.node{+lo, +hi}:
              {==}
            case C.Wasm.Bytes.zero{}:
              get.zero(p, t2)
            case C.Wasm.Bytes.byte{+x}:
              get.zero(p, t2)
        case WCon{True{}, +t} WCon{False{}, +t2}:
          match m:
            case C.Wasm.Bytes.node{+lo, +hi}:
              {==}
            case C.Wasm.Bytes.zero{}:
              get.zero(p, t2)
            case C.Wasm.Bytes.byte{+x}:
              get.zero(p, t2)

# Words and bytes
# ---------------
# the bit of a byte j of a word, as recomp puts it back
def g0(b: Bool) -> Bool:
  Bool.or(Bool.or(Bool.or(Bool.and(b, True{}), False{}), False{}), False{})

def g1(+b: Bool) -> Bool:
  Bool.or(Bool.or(Bool.or(Bool.and(b, False{}), Bool.and(b, True{})), False{}), False{})

def g2(+b: Bool) -> Bool:
  Bool.or(Bool.or(Bool.or(Bool.and(b, False{}), Bool.and(b, False{})), Bool.and(b, True{})), False{})

def g3(+b: Bool) -> Bool:
  Bool.or(Bool.or(Bool.or(Bool.and(b, False{}), Bool.and(b, False{})), Bool.and(b, False{})), b)

def g0.id(b: Bool) -> {g0(b) == b : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def g1.id(b: Bool) -> {g1(b) == b : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def g2.id(b: Bool) -> {g2(b) == b : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def g3.id(b: Bool) -> {g3(b) == b : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# the bytes of v, lowest first, put back together as read32 does
def recomp(+v: U32) -> U32:
  U32.or(U32.or(U32.or(U32.and(v, 255), U32.shln(U32.and(U32.shrn(v, 8n), 255), 8n)),
    U32.shln(U32.and(U32.shrn(v, 16n), 255), 16n)), U32.shln(U32.shrn(v, 24n), 24n))

# two words whose bits agree
def word32.cong(-x0: Bool, -y0: Bool, -x1: Bool, -y1: Bool, -x2: Bool, -y2: Bool, -x3: Bool, -y3: Bool, -x4: Bool, -y4: Bool, -x5: Bool, -y5: Bool, -x6: Bool, -y6: Bool, -x7: Bool, -y7: Bool, -x8: Bool, -y8: Bool, -x9: Bool, -y9: Bool, -x10: Bool, -y10: Bool, -x11: Bool, -y11: Bool, -x12: Bool, -y12: Bool, -x13: Bool, -y13: Bool, -x14: Bool, -y14: Bool, -x15: Bool, -y15: Bool, -x16: Bool, -y16: Bool, -x17: Bool, -y17: Bool, -x18: Bool, -y18: Bool, -x19: Bool, -y19: Bool, -x20: Bool, -y20: Bool, -x21: Bool, -y21: Bool, -x22: Bool, -y22: Bool, -x23: Bool, -y23: Bool, -x24: Bool, -y24: Bool, -x25: Bool, -y25: Bool, -x26: Bool, -y26: Bool, -x27: Bool, -y27: Bool, -x28: Bool, -y28: Bool, -x29: Bool, -y29: Bool, -x30: Bool, -y30: Bool, -x31: Bool, -y31: Bool,
  e0: {x0 == y0 : Bool}, e1: {x1 == y1 : Bool}, e2: {x2 == y2 : Bool}, e3: {x3 == y3 : Bool}, e4: {x4 == y4 : Bool}, e5: {x5 == y5 : Bool}, e6: {x6 == y6 : Bool}, e7: {x7 == y7 : Bool}, e8: {x8 == y8 : Bool}, e9: {x9 == y9 : Bool}, e10: {x10 == y10 : Bool}, e11: {x11 == y11 : Bool}, e12: {x12 == y12 : Bool}, e13: {x13 == y13 : Bool}, e14: {x14 == y14 : Bool}, e15: {x15 == y15 : Bool}, e16: {x16 == y16 : Bool}, e17: {x17 == y17 : Bool}, e18: {x18 == y18 : Bool}, e19: {x19 == y19 : Bool}, e20: {x20 == y20 : Bool}, e21: {x21 == y21 : Bool}, e22: {x22 == y22 : Bool}, e23: {x23 == y23 : Bool}, e24: {x24 == y24 : Bool}, e25: {x25 == y25 : Bool}, e26: {x26 == y26 : Bool}, e27: {x27 == y27 : Bool}, e28: {x28 == y28 : Bool}, e29: {x29 == y29 : Bool}, e30: {x30 == y30 : Bool}, e31: {x31 == y31 : Bool}) ->
  {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{y8, WCon{y9, WCon{y10, WCon{y11, WCon{y12, WCon{y13, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}:
  %e0 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{_, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{y8, WCon{y9, WCon{y10, WCon{y11, WCon{y12, WCon{y13, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e1 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{_, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{y8, WCon{y9, WCon{y10, WCon{y11, WCon{y12, WCon{y13, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e2 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{_, WCon{y3, WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{y8, WCon{y9, WCon{y10, WCon{y11, WCon{y12, WCon{y13, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e3 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{_, WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{y8, WCon{y9, WCon{y10, WCon{y11, WCon{y12, WCon{y13, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e4 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{_, WCon{y5, WCon{y6, WCon{y7, WCon{y8, WCon{y9, WCon{y10, WCon{y11, WCon{y12, WCon{y13, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e5 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{_, WCon{y6, WCon{y7, WCon{y8, WCon{y9, WCon{y10, WCon{y11, WCon{y12, WCon{y13, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e6 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{_, WCon{y7, WCon{y8, WCon{y9, WCon{y10, WCon{y11, WCon{y12, WCon{y13, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e7 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{_, WCon{y8, WCon{y9, WCon{y10, WCon{y11, WCon{y12, WCon{y13, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e8 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{_, WCon{y9, WCon{y10, WCon{y11, WCon{y12, WCon{y13, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e9 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{_, WCon{y10, WCon{y11, WCon{y12, WCon{y13, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e10 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{_, WCon{y11, WCon{y12, WCon{y13, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e11 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{_, WCon{y12, WCon{y13, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e12 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{_, WCon{y13, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e13 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{_, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e14 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{_, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e15 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{_, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e16 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{_, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e17 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{_, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e18 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{_, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e19 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{_, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e20 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{_, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e21 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{_, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e22 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{_, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e23 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{_, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e24 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{_, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e25 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{_, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e26 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{_, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e27 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{_, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e28 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{_, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e29 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{_, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e30 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{_, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %e31 : {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{_, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  {==}

# the bytes of a word, put back together as read32 does, give the word
def recomp.id(+w: Word(32n)) -> {recomp(U32{w}) == U32{w} : U32}:
  match w:
    case WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, WCon{+b6, WCon{+b7, WCon{+b8, WCon{+b9, WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WCon{+b16, WCon{+b17, WCon{+b18, WCon{+b19, WCon{+b20, WCon{+b21, WCon{+b22, WCon{+b23, WCon{+b24, WCon{+b25, WCon{+b26, WCon{+b27, WCon{+b28, WCon{+b29, WCon{+b30, WCon{+b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Equal.trans(U32, recomp(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), U32{WCon{g0(b0), WCon{g0(b1), WCon{g0(b2), WCon{g0(b3), WCon{g0(b4), WCon{g0(b5), WCon{g0(b6), WCon{g0(b7), WCon{g1(b8), WCon{g1(b9), WCon{g1(b10), WCon{g1(b11), WCon{g1(b12), WCon{g1(b13), WCon{g1(b14), WCon{g1(b15), WCon{g2(b16), WCon{g2(b17), WCon{g2(b18), WCon{g2(b19), WCon{g2(b20), WCon{g2(b21), WCon{g2(b22), WCon{g2(b23), WCon{g3(b24), WCon{g3(b25), WCon{g3(b26), WCon{g3(b27), WCon{g3(b28), WCon{g3(b29), WCon{g3(b30), WCon{g3(b31), WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, {==},
        word32.cong(g0(b0), b0, g0(b1), b1, g0(b2), b2, g0(b3), b3, g0(b4), b4, g0(b5), b5, g0(b6), b6, g0(b7), b7, g1(b8), b8, g1(b9), b9, g1(b10), b10, g1(b11), b11, g1(b12), b12, g1(b13), b13, g1(b14), b14, g1(b15), b15, g2(b16), b16, g2(b17), b17, g2(b18), b18, g2(b19), b19, g2(b20), b20, g2(b21), b21, g2(b22), b22, g2(b23), b23, g3(b24), b24, g3(b25), b25, g3(b26), b26, g3(b27), b27, g3(b28), b28, g3(b29), b29, g3(b30), b30, g3(b31), b31,
          g0.id(b0), g0.id(b1), g0.id(b2), g0.id(b3), g0.id(b4), g0.id(b5), g0.id(b6), g0.id(b7), g1.id(b8), g1.id(b9), g1.id(b10), g1.id(b11), g1.id(b12), g1.id(b13), g1.id(b14), g1.id(b15), g2.id(b16), g2.id(b17), g2.id(b18), g2.id(b19), g2.id(b20), g2.id(b21), g2.id(b22), g2.id(b23), g3.id(b24), g3.id(b25), g3.id(b26), g3.id(b27), g3.id(b28), g3.id(b29), g3.id(b30), g3.id(b31)))

# Equal words
# -----------

# a word compares equal to itself
def W.cmp.refl(+n: Nat, +w: Word(n)) -> {Cmp.is_eq(Word.cmp(n, w, w)) == True{} : Bool}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(p, t, t))), Cmp.is_eq(Word.cmp(p, t, t)), True{},
            fin.ff(Word.cmp(p, t, t)), W.cmp.refl(p, t))
        case WCon{True{}, +t}:
          Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(True{}, True{}, Word.cmp(p, t, t))), Cmp.is_eq(Word.cmp(p, t, t)), True{},
            fin.tt(Word.cmp(p, t, t)), W.cmp.refl(p, t))

def U32.is_eq.refl(+a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  match a:
    case U32{+w}:
      W.cmp.refl(32n, w)

# the comparison of two different low bits is not EQ
def fin.ft(c: Cmp) -> {Cmp.is_eq(Word.cmp.fin(False{}, True{}, c)) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def fin.tf(c: Cmp) -> {Cmp.is_eq(Word.cmp.fin(True{}, False{}, c)) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def eq.ff(+c: Cmp, e: {Cmp.is_eq(Word.cmp.fin(False{}, False{}, c)) == True{} : Bool}) -> {Cmp.is_eq(c) == True{} : Bool}:
  Equal.trans(Bool, Cmp.is_eq(c), Cmp.is_eq(Word.cmp.fin(False{}, False{}, c)), True{},
    Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(False{}, False{}, c)), Cmp.is_eq(c), fin.ff(c)), e)

def eq.tt(+c: Cmp, e: {Cmp.is_eq(Word.cmp.fin(True{}, True{}, c)) == True{} : Bool}) -> {Cmp.is_eq(c) == True{} : Bool}:
  Equal.trans(Bool, Cmp.is_eq(c), Cmp.is_eq(Word.cmp.fin(True{}, True{}, c)), True{},
    Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(True{}, True{}, c)), Cmp.is_eq(c), fin.tt(c)), e)

# words that compare equal are equal
def W.eq(+n: Nat, +a: Word(n), +b: Word(n), e: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, at, bt, W.eq(p, at, bt, eq.ff(Word.cmp(p, at, bt), e)))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, at, bt, W.eq(p, at, bt, eq.tt(Word.cmp(p, at, bt), e)))
        case WCon{False{}, +at} WCon{True{}, +bt}:
          Empty.absurd({WCon{False{}, at} == WCon{True{}, bt} : Word(1n+p)},
            N.true_ne_false(Equal.trans(Bool, True{}, Cmp.is_eq(Word.cmp.fin(False{}, True{}, Word.cmp(p, at, bt))), False{},
              Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(False{}, True{}, Word.cmp(p, at, bt))), True{}, e), fin.ft(Word.cmp(p, at, bt)))))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          Empty.absurd({WCon{True{}, at} == WCon{False{}, bt} : Word(1n+p)},
            N.true_ne_false(Equal.trans(Bool, True{}, Cmp.is_eq(Word.cmp.fin(True{}, False{}, Word.cmp(p, at, bt))), False{},
              Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(True{}, False{}, Word.cmp(p, at, bt))), True{}, e), fin.tf(Word.cmp(p, at, bt)))))

def U32.eq(+a: U32, +b: U32, e: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      Equal.cong(Word(32n), U32, z => U32{z}, x, y, W.eq(32n, x, y, e))

# a sum, less one of its terms, is the other
def W.add_sub.go(+n: Nat, +x: Word(n), +y: Word(n), +c: Bool) ->
  {Word.adc(n, Word.adc(n, x, y, False{}, c), y, True{}, Bool.not(c)) == x : Word(n)}:
  match n:
    case 0n:
      match x:
        case WNil{}:
          {==}
    case 1n+p:
      match x y c:
        case WCon{False{}, +xt} WCon{False{}, +yt} False{}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.adc(p, Word.adc(p, xt, yt, False{}, False{}), yt, True{}, True{}), xt, W.add_sub.go(p, xt, yt, False{}))
        case WCon{False{}, +xt} WCon{False{}, +yt} True{}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.adc(p, Word.adc(p, xt, yt, False{}, False{}), yt, True{}, True{}), xt, W.add_sub.go(p, xt, yt, False{}))
        case WCon{False{}, +xt} WCon{True{}, +yt} False{}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.adc(p, Word.adc(p, xt, yt, False{}, False{}), yt, True{}, True{}), xt, W.add_sub.go(p, xt, yt, False{}))
        case WCon{False{}, +xt} WCon{True{}, +yt} True{}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.adc(p, Word.adc(p, xt, yt, False{}, True{}), yt, True{}, False{}), xt, W.add_sub.go(p, xt, yt, True{}))
        case WCon{True{}, +xt} WCon{False{}, +yt} False{}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, Word.adc(p, Word.adc(p, xt, yt, False{}, False{}), yt, True{}, True{}), xt, W.add_sub.go(p, xt, yt, False{}))
        case WCon{True{}, +xt} WCon{False{}, +yt} True{}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, Word.adc(p, Word.adc(p, xt, yt, False{}, True{}), yt, True{}, False{}), xt, W.add_sub.go(p, xt, yt, True{}))
        case WCon{True{}, +xt} WCon{True{}, +yt} False{}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, Word.adc(p, Word.adc(p, xt, yt, False{}, True{}), yt, True{}, False{}), xt, W.add_sub.go(p, xt, yt, True{}))
        case WCon{True{}, +xt} WCon{True{}, +yt} True{}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, Word.adc(p, Word.adc(p, xt, yt, False{}, True{}), yt, True{}, False{}), xt, W.add_sub.go(p, xt, yt, True{}))

# (x + y) - y = x
def U32.add_sub(+x: U32, +y: U32) -> {U32.sub(U32.add(x, y), y) == x : U32}:
  match x y:
    case U32{+xw} U32{+yw}:
      Equal.cong(Word(32n), U32, z => U32{z}, Word.adc(32n, Word.adc(32n, xw, yw, False{}, False{}), yw, True{}, True{}), xw,
        W.add_sub.go(32n, xw, yw, False{}))

# a + x = a + y gives x = y
def U32.add_cancel(+a: U32, +x: U32, +y: U32, e: {U32.add(a, x) == U32.add(a, y) : U32}) -> {x == y : U32}:
  +ex = Equal.trans(U32, U32.add(x, a), U32.add(a, x), U32.add(a, y), U32.add_comm(x, a), e)
  +exy = Equal.trans(U32, U32.add(x, a), U32.add(a, y), U32.add(y, a), ex, U32.add_comm(a, y))
  Equal.trans(U32, x, U32.sub(U32.add(x, a), a), y,
    Equal.sym(U32, U32.sub(U32.add(x, a), a), x, U32.add_sub(x, a)),
    Equal.trans(U32, U32.sub(U32.add(x, a), a), U32.sub(U32.add(y, a), a), y,
      Equal.cong(U32, U32, z => U32.sub(z, a), U32.add(x, a), U32.add(y, a), exy), U32.add_sub(y, a)))

# a + 0 = a
def U32.add_zero(+a: U32) -> {U32.add(a, 0) == a : U32}:
  match a:
    case U32{+w}:
      Equal.cong(Word(32n), U32, z => U32{z}, Word.adc(32n, w, Word.zero(32n), False{}, False{}), w, PH.H.z0(32n, w))

def ne.if(b: Bool, +x: U32, +y: U32, e: {U32.is_eq(x, y) == b : Bool}, k: {x == y : U32} -> Empty) -> {U32.is_eq(x, y) == False{} : Bool}:
  match b:
    case False{}:
      e
    case True{}:
      Empty.absurd({U32.is_eq(x, y) == False{} : Bool}, k(U32.eq(x, y, e)))

# words that differ do not compare equal
def U32.ne(+x: U32, +y: U32, k: {x == y : U32} -> Empty) -> {U32.is_eq(x, y) == False{} : Bool}:
  ne.if(U32.is_eq(x, y), x, y, {==}, k)

def ne.lit(+i: U32, +j: U32, d: {U32.is_eq(i, j) == False{} : Bool}, e: {i == j : U32}) -> Empty:
  N.true_ne_false(Equal.trans(Bool, True{}, U32.is_eq(i, i), False{},
    Equal.sym(Bool, U32.is_eq(i, i), True{}, U32.is_eq.refl(i)),
    (%Equal.sym(U32, i, j, e) : {U32.is_eq(i, _) == False{} : Bool}; d)))

# a + i and a + j differ when i and j do
def add.ne(+a: U32, +i: U32, +j: U32, d: {U32.is_eq(i, j) == False{} : Bool}) -> {U32.is_eq(U32.add(a, i), U32.add(a, j)) == False{} : Bool}:
  U32.ne(U32.add(a, i), U32.add(a, j), e => ne.lit(i, j, d, U32.add_cancel(a, i, j, e)))

# Bytes at U32 addresses
# ----------------------

def R8(m: C.Wasm.Bytes, a: U32) -> U32:
  match a:
    case U32{w}:
      B.get(32n, w, m)

def read8.eq(+m: C.Wasm.Bytes, +a: U32) -> {C.Wasm.read8(m, a) == C.Wasm.Peek{R8(m, a), m} : C.Wasm.Peek}:
  match a:
    case U32{+w}:
      peek.eq(32n, w, m)

def R8.same(+m: C.Wasm.Bytes, +a: U32, +b: U32) -> {R8(C.Wasm.write8(m, a, b), a) == b : U32}:
  match a:
    case U32{+w}:
      get.set.same(32n, w, m, b)

# a write of a byte keeps the bytes at the other addresses
def R8.other(+m: C.Wasm.Bytes, +a: U32, +x: U32, +b: U32, ne: {U32.is_eq(x, a) == False{} : Bool}) ->
  {R8(C.Wasm.write8(m, a, b), x) == R8(m, x) : U32}:
  match a x:
    case U32{+w} U32{+w2}:
      get.set.other(32n, w, w2, m, b, ne)

# the four bytes from a, put together as read32 does
def V4(+x0: U32, +x1: U32, +x2: U32, +x3: U32) -> U32:
  U32.or(U32.or(U32.or(x0, U32.shln(x1, 8n)), U32.shln(x2, 16n)), U32.shln(x3, 24n))

def V32(+m: C.Wasm.Bytes, +a: U32) -> U32:
  V4(R8(m, a), R8(m, U32.add(a, 1)), R8(m, U32.add(a, 2)), R8(m, U32.add(a, 3)))

# read32 gives V32 and the bytes as they were
def read32.eq(+m: C.Wasm.Bytes, +a: U32) -> {C.Wasm.read32(m, a) == C.Wasm.Peek{V32(m, a), m} : C.Wasm.Peek}:
  +r0 = R8(m, a)
  +v1 = U32.or(r0, U32.shln(R8(m, U32.add(a, 1)), 8n))
  +v2 = U32.or(v1, U32.shln(R8(m, U32.add(a, 2)), 16n))
  %Equal.sym(C.Wasm.Peek, C.Wasm.read8(m, a), C.Wasm.Peek{r0, m}, read8.eq(m, a)) :
    {C.Wasm.read32.b0(_, a) == C.Wasm.Peek{V32(m, a), m} : C.Wasm.Peek}
  %Equal.sym(C.Wasm.Peek, C.Wasm.read8(m, U32.add(a, 1)), C.Wasm.Peek{R8(m, U32.add(a, 1)), m}, read8.eq(m, U32.add(a, 1))) :
    {C.Wasm.read32.b1(r0, _, a) == C.Wasm.Peek{V32(m, a), m} : C.Wasm.Peek}
  %Equal.sym(C.Wasm.Peek, C.Wasm.read8(m, U32.add(a, 2)), C.Wasm.Peek{R8(m, U32.add(a, 2)), m}, read8.eq(m, U32.add(a, 2))) :
    {C.Wasm.read32.b2(v1, _, a) == C.Wasm.Peek{V32(m, a), m} : C.Wasm.Peek}
  %Equal.sym(C.Wasm.Peek, C.Wasm.read8(m, U32.add(a, 3)), C.Wasm.Peek{R8(m, U32.add(a, 3)), m}, read8.eq(m, U32.add(a, 3))) :
    {C.Wasm.read32.b3(v2, _) == C.Wasm.Peek{V32(m, a), m} : C.Wasm.Peek}
  {==}

def V4.cong(-x0: U32, -x1: U32, -x2: U32, -x3: U32, -y0: U32, -y1: U32, -y2: U32, -y3: U32,
  e0: {x0 == y0 : U32}, e1: {x1 == y1 : U32}, e2: {x2 == y2 : U32}, e3: {x3 == y3 : U32}) ->
  {V4(x0, x1, x2, x3) == V4(y0, y1, y2, y3) : U32}:
  %e0 : {V4(x0, x1, x2, x3) == V4(_, y1, y2, y3) : U32}
  %e1 : {V4(x0, x1, x2, x3) == V4(x0, _, y2, y3) : U32}
  %e2 : {V4(x0, x1, x2, x3) == V4(x0, x1, _, y3) : U32}
  %e3 : {V4(x0, x1, x2, x3) == V4(x0, x1, x2, _) : U32}
  {==}

# a is not a + i, for i not 0
def ne.self(+a: U32, +i: U32, d: {U32.is_eq(0, i) == False{} : Bool}) -> {U32.is_eq(a, U32.add(a, i)) == False{} : Bool}:
  %U32.add_zero(a) : {U32.is_eq(_, U32.add(a, i)) == False{} : Bool}
  add.ne(a, 0, i, d)

# x differs from a word and from the next three addresses after it
def Out4(+x: U32, +a: U32) -> Data:
  P2(P2({U32.is_eq(x, a) == False{} : Bool}, {U32.is_eq(x, U32.add(a, 1)) == False{} : Bool}),
     P2({U32.is_eq(x, U32.add(a, 2)) == False{} : Bool}, {U32.is_eq(x, U32.add(a, 3)) == False{} : Bool}))

# recomp on U32
def recomp.u32(+v: U32) -> {recomp(v) == v : U32}:
  match v:
    case U32{+w}:
      recomp.id(w)

# the word v, written at a, read back from a
def V32.same(+m: C.Wasm.Bytes, +a: U32, +v: U32) -> {V32(C.Wasm.write32(m, a, v), a) == v : U32}:
  +A1 = U32.add(a, 1)
  +A2 = U32.add(a, 2)
  +A3 = U32.add(a, 3)
  +B0 = U32.and(v, 255)
  +B1 = U32.and(U32.shrn(v, 8n), 255)
  +B2 = U32.and(U32.shrn(v, 16n), 255)
  +B3 = U32.shrn(v, 24n)
  +m1 = C.Wasm.write8(m, a, B0)
  +m2 = C.Wasm.write8(m1, A1, B1)
  +m3 = C.Wasm.write8(m2, A2, B2)
  +m4 = C.Wasm.write8(m3, A3, B3)
  +r0 = Equal.trans(U32, R8(m4, a), R8(m3, a), B0, R8.other(m3, A3, a, B3, ne.self(a, 3, {==})),
    Equal.trans(U32, R8(m3, a), R8(m2, a), B0, R8.other(m2, A2, a, B2, ne.self(a, 2, {==})),
      Equal.trans(U32, R8(m2, a), R8(m1, a), B0, R8.other(m1, A1, a, B1, ne.self(a, 1, {==})), R8.same(m, a, B0))))
  +r1 = Equal.trans(U32, R8(m4, A1), R8(m3, A1), B1, R8.other(m3, A3, A1, B3, add.ne(a, 1, 3, {==})),
    Equal.trans(U32, R8(m3, A1), R8(m2, A1), B1, R8.other(m2, A2, A1, B2, add.ne(a, 1, 2, {==})), R8.same(m1, A1, B1)))
  +r2 = Equal.trans(U32, R8(m4, A2), R8(m3, A2), B2, R8.other(m3, A3, A2, B3, add.ne(a, 2, 3, {==})), R8.same(m2, A2, B2))
  +r3 = R8.same(m3, A3, B3)
  Equal.trans(U32, V32(m4, a), V4(B0, B1, B2, B3), v,
    V4.cong(R8(m4, a), R8(m4, A1), R8(m4, A2), R8(m4, A3), B0, B1, B2, B3, r0, r1, r2, r3),
    recomp.u32(v))

# a write of a word keeps the bytes outside it
def R8.out32(+m: C.Wasm.Bytes, +a: U32, +v: U32, +x: U32, +o: Out4(x, a)) ->
  {R8(C.Wasm.write32(m, a, v), x) == R8(m, x) : U32}:
  (+o01, +o23) = o
  (+n0, +n1) = o01
  (+n2, +n3) = o23
  +A1 = U32.add(a, 1)
  +A2 = U32.add(a, 2)
  +A3 = U32.add(a, 3)
  +m1 = C.Wasm.write8(m, a, U32.and(v, 255))
  +m2 = C.Wasm.write8(m1, A1, U32.and(U32.shrn(v, 8n), 255))
  +m3 = C.Wasm.write8(m2, A2, U32.and(U32.shrn(v, 16n), 255))
  Equal.trans(U32, R8(C.Wasm.write8(m3, A3, U32.shrn(v, 24n)), x), R8(m3, x), R8(m, x), R8.other(m3, A3, x, U32.shrn(v, 24n), n3),
    Equal.trans(U32, R8(m3, x), R8(m2, x), R8(m, x), R8.other(m2, A2, x, U32.and(U32.shrn(v, 16n), 255), n2),
      Equal.trans(U32, R8(m2, x), R8(m1, x), R8(m, x), R8.other(m1, A1, x, U32.and(U32.shrn(v, 8n), 255), n1),
        R8.other(m, a, x, U32.and(v, 255), n0))))

# the four bytes of b are outside the word at a
def Disj4(+b: U32, +a: U32) -> Data:
  P2(P2(Out4(b, a), Out4(U32.add(b, 1), a)), P2(Out4(U32.add(b, 2), a), Out4(U32.add(b, 3), a)))

# a write of a word keeps the words outside it
def V32.out32(+m: C.Wasm.Bytes, +a: U32, +v: U32, +b: U32, +d: Disj4(b, a)) ->
  {V32(C.Wasm.write32(m, a, v), b) == V32(m, b) : U32}:
  (+d01, +d23) = d
  (+o0, +o1) = d01
  (+o2, +o3) = d23
  +m4 = C.Wasm.write32(m, a, v)
  V4.cong(R8(m4, b), R8(m4, U32.add(b, 1)), R8(m4, U32.add(b, 2)), R8(m4, U32.add(b, 3)),
    R8(m, b), R8(m, U32.add(b, 1)), R8(m, U32.add(b, 2)), R8(m, U32.add(b, 3)),
    R8.out32(m, a, v, b, o0), R8.out32(m, a, v, U32.add(b, 1), o1), R8.out32(m, a, v, U32.add(b, 2), o2), R8.out32(m, a, v, U32.add(b, 3), o3))

# the four bytes of b differ from x
def In4(+b: U32, +x: U32) -> Data:
  P2(P2({U32.is_eq(b, x) == False{} : Bool}, {U32.is_eq(U32.add(b, 1), x) == False{} : Bool}),
     P2({U32.is_eq(U32.add(b, 2), x) == False{} : Bool}, {U32.is_eq(U32.add(b, 3), x) == False{} : Bool}))

# a write of a byte keeps the words that do not hold it
def V32.out8(+m: C.Wasm.Bytes, +x: U32, +y: U32, +b: U32, +d: In4(b, x)) ->
  {V32(C.Wasm.write8(m, x, y), b) == V32(m, b) : U32}:
  (+d01, +d23) = d
  (+n0, +n1) = d01
  (+n2, +n3) = d23
  +m1 = C.Wasm.write8(m, x, y)
  V4.cong(R8(m1, b), R8(m1, U32.add(b, 1)), R8(m1, U32.add(b, 2)), R8(m1, U32.add(b, 3)),
    R8(m, b), R8(m, U32.add(b, 1)), R8(m, U32.add(b, 2)), R8(m, U32.add(b, 3)),
    R8.other(m, x, b, y, n0), R8.other(m, x, U32.add(b, 1), y, n1), R8.other(m, x, U32.add(b, 2), y, n2), R8.other(m, x, U32.add(b, 3), y, n3))
