# compiler: the frame of the model's memory writes
# ================================================
#
# A write of a byte or a word keeps every byte, word and cell of the memory
# that lies elsewhere, and so every view of proof_sim_inv.bend that does not
# hold it (RB.keep, RC.keep, from a pointwise fact). Two U32s whose numbers
# differ do not compare equal (ne.nat); the numbers of the addresses are
# exact below W = 2^32. Cir's cells, a tree like the bytes, give the cell
# that a set puts (cells.same) and keep every other (cells.other).

import Base
import ./impl.bend as C
import ./proof_need.bend as N
import ./proof_instrs.bend as I
import ./proof_halt.bend as PH
import ./proof_valid.bend as V
import ./proof_sim_step.bend as S
import ./proof_sim_mem.bend as Y
import ./proof_sim_nat.bend as Z
import ./proof_sim_inv.bend as Q

# The cells of Cir
# ----------------

# the cells that are all zeros
def cz(+n: Nat, +w: Word(n)) -> {C.Cir.Cells.get.at(n, w, C.Cir.Cells.none{}) == C.Cir.Cell.zero() : C.Cir.Cell}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          {==}
        case WCon{True{}, t}:
          {==}

# a set puts its cell
def cs.at(+n: Nat, +w: Word(n), +m: C.Cir.Cells, +c: C.Cir.Cell) ->
  {C.Cir.Cells.get.at(n, w, C.Cir.Cells.set.at(n, w, m, c)) == c : C.Cir.Cell}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          match m:
            case C.Cir.Cells.node{+lo, +hi}:
              cs.at(p, t, lo, c)
            case C.Cir.Cells.none{}:
              cs.at(p, t, C.Cir.Cells.none{}, c)
            case C.Cir.Cells.one{+x}:
              cs.at(p, t, C.Cir.Cells.none{}, c)
        case WCon{True{}, +t}:
          match m:
            case C.Cir.Cells.node{+lo, +hi}:
              cs.at(p, t, hi, c)
            case C.Cir.Cells.none{}:
              cs.at(p, t, C.Cir.Cells.none{}, c)
            case C.Cir.Cells.one{+x}:
              cs.at(p, t, C.Cir.Cells.none{}, c)

# a set keeps every other cell
def co.at(+n: Nat, +w: Word(n), +w2: Word(n), +m: C.Cir.Cells, +c: C.Cir.Cell,
  ne: {Cmp.is_eq(Word.cmp(n, w2, w)) == False{} : Bool}) ->
  {C.Cir.Cells.get.at(n, w2, C.Cir.Cells.set.at(n, w, m, c)) == C.Cir.Cells.get.at(n, w2, m) : C.Cir.Cell}:
  match n:
    case 0n:
      match w w2:
        case WNil{} WNil{}:
          Empty.absurd({C.Cir.Cells.get.at(0n, WNil{}, C.Cir.Cells.set.at(0n, WNil{}, m, c)) == C.Cir.Cells.get.at(0n, WNil{}, m) : C.Cir.Cell},
            N.true_ne_false(ne))
    case 1n+p:
      match w w2:
        case WCon{False{}, +t} WCon{False{}, +t2}:
          match m:
            case C.Cir.Cells.node{+lo, +hi}:
              co.at(p, t, t2, lo, c, Y.ne.ff(Word.cmp(p, t2, t), ne))
            case C.Cir.Cells.none{}:
              Equal.trans(C.Cir.Cell, C.Cir.Cells.get.at(p, t2, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, c)),
                C.Cir.Cells.get.at(p, t2, C.Cir.Cells.none{}), C.Cir.Cell.zero(),
                co.at(p, t, t2, C.Cir.Cells.none{}, c, Y.ne.ff(Word.cmp(p, t2, t), ne)), cz(p, t2))
            case C.Cir.Cells.one{+x}:
              Equal.trans(C.Cir.Cell, C.Cir.Cells.get.at(p, t2, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, c)),
                C.Cir.Cells.get.at(p, t2, C.Cir.Cells.none{}), C.Cir.Cell.zero(),
                co.at(p, t, t2, C.Cir.Cells.none{}, c, Y.ne.ff(Word.cmp(p, t2, t), ne)), cz(p, t2))
        case WCon{True{}, +t} WCon{True{}, +t2}:
          match m:
            case C.Cir.Cells.node{+lo, +hi}:
              co.at(p, t, t2, hi, c, Y.ne.tt(Word.cmp(p, t2, t), ne))
            case C.Cir.Cells.none{}:
              Equal.trans(C.Cir.Cell, C.Cir.Cells.get.at(p, t2, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, c)),
                C.Cir.Cells.get.at(p, t2, C.Cir.Cells.none{}), C.Cir.Cell.zero(),
                co.at(p, t, t2, C.Cir.Cells.none{}, c, Y.ne.tt(Word.cmp(p, t2, t), ne)), cz(p, t2))
            case C.Cir.Cells.one{+x}:
              Equal.trans(C.Cir.Cell, C.Cir.Cells.get.at(p, t2, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, c)),
                C.Cir.Cells.get.at(p, t2, C.Cir.Cells.none{}), C.Cir.Cell.zero(),
                co.at(p, t, t2, C.Cir.Cells.none{}, c, Y.ne.tt(Word.cmp(p, t2, t), ne)), cz(p, t2))
        case WCon{False{}, +t} WCon{True{}, +t2}:
          match m:
            case C.Cir.Cells.node{+lo, +hi}:
              {==}
            case C.Cir.Cells.none{}:
              cz(p, t2)
            case C.Cir.Cells.one{+x}:
              cz(p, t2)
        case WCon{True{}, +t} WCon{False{}, +t2}:
          match m:
            case C.Cir.Cells.node{+lo, +hi}:
              {==}
            case C.Cir.Cells.none{}:
              cz(p, t2)
            case C.Cir.Cells.one{+x}:
              cz(p, t2)

# the cell i, once set
def cells.same(+m: C.Cir.Cells, +i: U32, +c: C.Cir.Cell) -> {C.Cir.Cells.get(C.Cir.Cells.set(m, i, c), i) == c : C.Cir.Cell}:
  match i:
    case U32{+w}:
      cs.at(32n, w, m, c)

# another cell j, once i is set
def cells.other(+m: C.Cir.Cells, +i: U32, +j: U32, +c: C.Cir.Cell, ne: {U32.is_eq(j, i) == False{} : Bool}) ->
  {C.Cir.Cells.get(C.Cir.Cells.set(m, i, c), j) == C.Cir.Cells.get(m, j) : C.Cir.Cell}:
  match i j:
    case U32{+w} U32{+w2}:
      co.at(32n, w, w2, m, c, ne)

# Numbers that differ
# -------------------

# x < y gives x != y
def lt.ne(+x: Nat, +y: Nat, h: N.Le(1n+x, y), e: {x == y : Nat}) -> Empty:
  N.not_succ_le(y, N.le_rw_l(1n+x, 1n+y, y, Equal.cong(Nat, Nat, z => 1n+z, x, y, e), h))

# x < y or y < x
def Ne(+x: Nat, +y: Nat) -> Data:
  Either<&2, &2, N.Le(1n+x, y), N.Le(1n+y, x)>

def ne.either(+x: Nat, +y: Nat, h: Ne(x, y), e: {x == y : Nat}) -> Empty:
  match h:
    case Inl{l}:
      lt.ne(x, y, l, e)
    case Inr{r}:
      lt.ne(y, x, r, Equal.sym(Nat, x, y, e))

# U32s whose numbers differ do not compare equal
def ne.nat(+x: U32, +y: U32, h: Ne(U32.to_nat(x), U32.to_nat(y))) -> {U32.is_eq(x, y) == False{} : Bool}:
  Y.U32.ne(x, y, e => ne.either(U32.to_nat(x), U32.to_nat(y), h, Equal.cong(U32, Nat, z => U32.to_nat(z), x, y, e)))

# Addresses
# ---------

# x is outside the w addresses from a: before them, or after
def Out(+x: Nat, +a: Nat, +w: Nat) -> Data:
  Either<&2, &2, N.Le(1n+x, a), N.Le(Nat.add(w, a), x)>

# the four bytes from b, and the four from a, do not overlap
def Sep(+b: Nat, +a: Nat) -> Data:
  Either<&2, &2, N.Le(4n+b, a), N.Le(4n+a, b)>

# a <= b gives a + x <= W when b + x <= W
def lit.le(+a: Nat, +b: Nat, +X: Nat, +W: Nat, h: N.Le(a, b), r: N.Le(Nat.add(b, X), W)) -> N.Le(Nat.add(a, X), W):
  N.le_trans(Nat.add(a, X), Nat.add(b, X), W, Z.le.add_r(a, b, X, h), r)

# the number of a + j is j + A, when it is below W
def add.nat(+a: U32, +j: U32, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  h: N.Le(1n+Nat.add(U32.to_nat(j), U32.to_nat(a)), W)) ->
  {U32.to_nat(U32.add(a, j)) == Nat.add(U32.to_nat(j), U32.to_nat(a)) : Nat}:
  +A = U32.to_nat(a)
  +J = U32.to_nat(j)
  +h2 = N.le_rw_l(1n+Nat.add(J, A), 1n+Nat.add(A, J), W,
    Equal.cong(Nat, Nat, z => 1n+z, Nat.add(J, A), Nat.add(A, J), Z.add.comm(J, A)), h)
  Equal.trans(Nat, U32.to_nat(U32.add(a, j)), Nat.add(A, J), Nat.add(J, A), Z.u32.add_ex(a, j, W, hW, h2), Z.add.comm(A, J))

# c + 1 is U32.inc(c)
def inc.add1(+c: U32) -> {U32.add(c, 1) == U32.inc(c) : U32}:
  Equal.trans(U32, U32.add(c, 1), U32.inc(U32.add(c, 0)), U32.inc(c), V.add.inc(c, 0),
    Equal.cong(U32, U32, z => U32.inc(z), U32.add(c, 0), c, Y.U32.add_zero(c)))

# the number of c + 1 is one more, below W
def inc.nat(+c: U32, +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, h: N.Le(2n+U32.to_nat(c), W)) ->
  {U32.to_nat(U32.inc(c)) == 1n+U32.to_nat(c) : Nat}:
  +C = U32.to_nat(c)
  Equal.trans(Nat, U32.to_nat(U32.inc(c)), U32.to_nat(U32.add(c, 1)), 1n+C,
    Equal.cong(U32, Nat, z => U32.to_nat(z), U32.inc(c), U32.add(c, 1), Equal.sym(U32, U32.add(c, 1), U32.inc(c), inc.add1(c))),
    add.nat(c, 1, W, hW, h))

# x is not a + j, for j below w, when x is outside the w addresses from a
def out.ne.go(+X: Nat, +A: Nat, +J: Nat, +w: Nat, +T: Nat, e: {T == Nat.add(J, A) : Nat}, hj: N.Le(1n+J, w), o: Out(X, A, w)) -> Ne(X, T):
  match o:
    case Inl{l}:
      Inl{N.le_rw_r(1n+X, Nat.add(J, A), T, Equal.sym(Nat, T, Nat.add(J, A), e), N.le_trans(1n+X, A, Nat.add(J, A), l, N.le_add_l(J, A)))}
    case Inr{r}:
      Inr{N.le_rw_l(1n+Nat.add(J, A), 1n+T, X, Equal.cong(Nat, Nat, z => 1n+z, Nat.add(J, A), T, Equal.sym(Nat, T, Nat.add(J, A), e)),
        N.le_trans(1n+Nat.add(J, A), Nat.add(w, A), X, Z.le.add_r(1n+J, w, A, hj), r))}

def out.ne(+x: U32, +a: U32, +j: U32, +w: Nat, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  hA: N.Le(1n+Nat.add(U32.to_nat(j), U32.to_nat(a)), W), hj: N.Le(1n+U32.to_nat(j), w),
  o: Out(U32.to_nat(x), U32.to_nat(a), w)) -> {U32.is_eq(x, U32.add(a, j)) == False{} : Bool}:
  ne.nat(x, U32.add(a, j), out.ne.go(U32.to_nat(x), U32.to_nat(a), U32.to_nat(j), w, U32.to_nat(U32.add(a, j)),
    add.nat(a, j, W, hW, hA), hj, o))

def out.ne0.go(+X: Nat, +A: Nat, +w: Nat, hw: N.Le(1n, w), o: Out(X, A, w)) -> Ne(X, A):
  match o:
    case Inl{l}:
      Inl{l}
    case Inr{r}:
      Inr{N.le_trans(1n+A, Nat.add(w, A), X, Z.le.add_r(1n, w, A, hw), r)}

def out.ne0(+x: U32, +a: U32, +w: Nat, hw: N.Le(1n, w), o: Out(U32.to_nat(x), U32.to_nat(a), w)) -> {U32.is_eq(x, a) == False{} : Bool}:
  ne.nat(x, a, out.ne0.go(U32.to_nat(x), U32.to_nat(a), w, hw, o))

# x is none of the four bytes from a
def out4(+x: U32, +a: U32, +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hA: N.Le(4n+U32.to_nat(a), W),
  +o: Out(U32.to_nat(x), U32.to_nat(a), 4n)) -> Y.Out4(x, a):
  +A = U32.to_nat(a)
  +h3 = N.weaken(3n+A, W, hA)
  +h2 = N.weaken(2n+A, W, h3)
  ((out.ne0(x, a, 4n, Unit{}, o), out.ne(x, a, 1, 4n, W, hW, h2, Unit{}, o)),
   (out.ne(x, a, 2, 4n, W, hW, h3, Unit{}, o), out.ne(x, a, 3, 4n, W, hW, hA, Unit{}, o)))

# the byte j of the word at b is outside the word at a
def sep.out(+B: Nat, +A: Nat, +J: Nat, +T: Nat, e: {T == Nat.add(J, B) : Nat}, hj: N.Le(1n+J, 4n), s: Sep(B, A)) -> Out(T, A, 4n):
  match s:
    case Inl{l}:
      Inl{N.le_rw_l(1n+Nat.add(J, B), 1n+T, A, Equal.cong(Nat, Nat, z => 1n+z, Nat.add(J, B), T, Equal.sym(Nat, T, Nat.add(J, B), e)),
        N.le_trans(1n+Nat.add(J, B), 4n+B, A, Z.le.add_r(1n+J, 4n, B, hj), l))}
    case Inr{r}:
      Inr{N.le_rw_r(4n+A, Nat.add(J, B), T, Equal.sym(Nat, T, Nat.add(J, B), e), N.le_trans(4n+A, B, Nat.add(J, B), r, N.le_add_l(J, B)))}

def sep.out0(+B: Nat, +A: Nat, s: Sep(B, A)) -> Out(B, A, 4n):
  match s:
    case Inl{l}:
      Inl{N.le_trans(1n+B, 4n+B, A, Z.le.add_r(1n, 4n, B, Unit{}), l)}
    case Inr{r}:
      Inr{r}

# the words at b and a do not overlap
def disj4(+b: U32, +a: U32, +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hB: N.Le(4n+U32.to_nat(b), W), +hA: N.Le(4n+U32.to_nat(a), W),
  +s: Sep(U32.to_nat(b), U32.to_nat(a))) -> Y.Disj4(b, a):
  +B = U32.to_nat(b)
  +A = U32.to_nat(a)
  +h3 = N.weaken(3n+B, W, hB)
  +h2 = N.weaken(2n+B, W, h3)
  ((out4(b, a, W, hW, hA, sep.out0(B, A, s)),
    out4(U32.add(b, 1), a, W, hW, hA, sep.out(B, A, 1n, U32.to_nat(U32.add(b, 1)), add.nat(b, 1, W, hW, h2), Unit{}, s))),
   (out4(U32.add(b, 2), a, W, hW, hA, sep.out(B, A, 2n, U32.to_nat(U32.add(b, 2)), add.nat(b, 2, W, hW, h3), Unit{}, s)),
    out4(U32.add(b, 3), a, W, hW, hA, sep.out(B, A, 3n, U32.to_nat(U32.add(b, 3)), add.nat(b, 3, W, hW, hB), Unit{}, s))))

# byte j of the word at b is not x, when x is outside that word
def in.ne.go(+X: Nat, +B: Nat, +J: Nat, +T: Nat, e: {T == Nat.add(J, B) : Nat}, hj: N.Le(1n+J, 4n), o: Out(X, B, 4n)) -> Ne(T, X):
  match o:
    case Inl{l}:
      Inr{N.le_rw_r(1n+X, Nat.add(J, B), T, Equal.sym(Nat, T, Nat.add(J, B), e), N.le_trans(1n+X, B, Nat.add(J, B), l, N.le_add_l(J, B)))}
    case Inr{r}:
      Inl{N.le_rw_l(1n+Nat.add(J, B), 1n+T, X, Equal.cong(Nat, Nat, z => 1n+z, Nat.add(J, B), T, Equal.sym(Nat, T, Nat.add(J, B), e)),
        N.le_trans(1n+Nat.add(J, B), 4n+B, X, Z.le.add_r(1n+J, 4n, B, hj), r))}

def in.ne0.go(+X: Nat, +B: Nat, o: Out(X, B, 4n)) -> Ne(B, X):
  match o:
    case Inl{l}:
      Inr{l}
    case Inr{r}:
      Inl{N.le_trans(1n+B, 4n+B, X, Z.le.add_r(1n, 4n, B, Unit{}), r)}

def in4(+b: U32, +x: U32, +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hB: N.Le(4n+U32.to_nat(b), W),
  +o: Out(U32.to_nat(x), U32.to_nat(b), 4n)) -> Y.In4(b, x):
  +B = U32.to_nat(b)
  +X = U32.to_nat(x)
  +h3 = N.weaken(3n+B, W, hB)
  +h2 = N.weaken(2n+B, W, h3)
  ((ne.nat(b, x, in.ne0.go(X, B, o)),
    ne.nat(U32.add(b, 1), x, in.ne.go(X, B, 1n, U32.to_nat(U32.add(b, 1)), add.nat(b, 1, W, hW, h2), Unit{}, o))),
   (ne.nat(U32.add(b, 2), x, in.ne.go(X, B, 2n, U32.to_nat(U32.add(b, 2)), add.nat(b, 2, W, hW, h3), Unit{}, o)),
    ne.nat(U32.add(b, 3), x, in.ne.go(X, B, 3n, U32.to_nat(U32.add(b, 3)), add.nat(b, 3, W, hW, hB), Unit{}, o))))

# Cells in the memory
# -------------------

# 20 × c, the first byte of the cell c, for c <= P
def at.nat(+c: U32, +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, hc: N.Le(U32.to_nat(c), P)) ->
  {U32.to_nat(C.Cir.at(c)) == PH.H.t20(U32.to_nat(c)) : Nat}:
  match c:
    case U32{+w}:
      PH.H.tex_w(32n, w, P, hP, hc)

# a cell below P, and a word after it, are below W = 2^4 + 20P
def cell.room(+C: Nat, +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, h: N.Le(1n+C, P)) -> N.Le(36n+PH.H.t20(C), W):
  +t1 = PH.H.t20_mono(1n+C, P, h)
  +t2 = N.add_mono(16n, 16n, 20n+PH.H.t20(C), PH.H.t20(P), N.le_refl(16n), t1)
  +t3 = N.le_rw_r(36n+PH.H.t20(C), Nat.add(PH.H.W(4n), PH.H.t20(P)), PH.H.W(32n), hP, t2)
  N.le_rw_r(36n+PH.H.t20(C), PH.H.W(32n), W, Equal.sym(Nat, W, PH.H.W(32n), hW), t3)

# the offset of field j
def O(j: Nat) -> Nat:
  U32.to_nat(U32.shln(U32.from_nat(j), 2n))

# the first byte of field j of the cell c: O(j) + 20c
def fld.nat(+c: U32, +j: Nat, +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hc: N.Le(1n+U32.to_nat(c), P), hj: N.Le(4n+O(j), 20n)) ->
  {U32.to_nat(Q.at.f(c, j)) == Nat.add(O(j), PH.H.t20(U32.to_nat(c))) : Nat}:
  +X = PH.H.t20(U32.to_nat(c))
  +ea = at.nat(c, P, hP, N.weaken(U32.to_nat(c), P, hc))
  +room = cell.room(U32.to_nat(c), P, hP, W, hW, hc)
  +h1 = lit.le(1n+O(j), 36n, X, W, N.le_trans(1n+O(j), 4n+O(j), 36n, Z.le.add_r(1n, 4n, O(j), Unit{}), N.le_trans(4n+O(j), 20n, 36n, hj, Unit{})), room)
  +h2 = N.le_rw_l(1n+Nat.add(O(j), X), 1n+Nat.add(O(j), U32.to_nat(C.Cir.at(c))), W,
    Equal.cong(Nat, Nat, z => 1n+Nat.add(O(j), z), X, U32.to_nat(C.Cir.at(c)), Equal.sym(Nat, U32.to_nat(C.Cir.at(c)), X, ea)), h1)
  Equal.trans(Nat, U32.to_nat(Q.at.f(c, j)), Nat.add(O(j), U32.to_nat(C.Cir.at(c))), Nat.add(O(j), X),
    add.nat(C.Cir.at(c), U32.shln(U32.from_nat(j), 2n), W, hW, h2),
    Equal.cong(Nat, Nat, z => Nat.add(O(j), z), U32.to_nat(C.Cir.at(c)), X, ea))

# field j of a cell, and a word after it, are below W
def fld.room(+c: U32, +j: Nat, +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hc: N.Le(1n+U32.to_nat(c), P), +hj: N.Le(4n+O(j), 20n)) ->
  N.Le(4n+U32.to_nat(Q.at.f(c, j)), W):
  +X = PH.H.t20(U32.to_nat(c))
  +e = fld.nat(c, j, P, hP, W, hW, hc, hj)
  N.le_rw_l(4n+Nat.add(O(j), X), 4n+U32.to_nat(Q.at.f(c, j)), W,
    Equal.cong(Nat, Nat, z => 4n+z, Nat.add(O(j), X), U32.to_nat(Q.at.f(c, j)), Equal.sym(Nat, U32.to_nat(Q.at.f(c, j)), Nat.add(O(j), X), e)),
    lit.le(4n+O(j), 36n, X, W, N.le_trans(4n+O(j), 20n, 36n, hj, Unit{}), cell.room(U32.to_nat(c), P, hP, W, hW, hc)))

# a cell's field and a word outside the cell do not overlap
def fsep(+X: Nat, +Oj: Nat, +T: Nat, e: {T == Nat.add(Oj, X) : Nat}, hO: N.Le(4n+Oj, 20n), +A: Nat,
  s: Either<&2, &2, N.Le(20n+X, A), N.Le(4n+A, X)>) -> Sep(T, A):
  match s:
    case Inl{l}:
      Inl{N.le_rw_l(4n+Nat.add(Oj, X), 4n+T, A, Equal.cong(Nat, Nat, z => 4n+z, Nat.add(Oj, X), T, Equal.sym(Nat, T, Nat.add(Oj, X), e)),
        N.le_trans(4n+Nat.add(Oj, X), 20n+X, A, Z.le.add_r(4n+Oj, 20n, X, hO), l))}
    case Inr{r}:
      Inr{N.le_rw_r(4n+A, Nat.add(Oj, X), T, Equal.sym(Nat, T, Nat.add(Oj, X), e), N.le_trans(4n+A, X, Nat.add(Oj, X), r, N.le_add_l(Oj, X)))}

# a cell's field and a byte outside the cell do not overlap
def fout(+X: Nat, +Oj: Nat, +T: Nat, e: {T == Nat.add(Oj, X) : Nat}, hO: N.Le(4n+Oj, 20n), +A: Nat,
  s: Either<&2, &2, N.Le(20n+X, A), N.Le(1n+A, X)>) -> Out(A, T, 4n):
  match s:
    case Inl{l}:
      Inr{N.le_rw_l(4n+Nat.add(Oj, X), Nat.add(4n, T), A, Equal.cong(Nat, Nat, z => 4n+z, Nat.add(Oj, X), T, Equal.sym(Nat, T, Nat.add(Oj, X), e)),
        N.le_trans(4n+Nat.add(Oj, X), 20n+X, A, Z.le.add_r(4n+Oj, 20n, X, hO), l))}
    case Inr{r}:
      Inl{N.le_rw_r(1n+A, Nat.add(Oj, X), T, Equal.sym(Nat, T, Nat.add(Oj, X), e), N.le_trans(1n+A, X, Nat.add(Oj, X), r, N.le_add_l(Oj, X)))}

# two fields of a cell do not overlap
def fpair(+X: Nat, +Oj: Nat, +Ok: Nat, +Tj: Nat, +Tk: Nat, ej: {Tj == Nat.add(Oj, X) : Nat}, ek: {Tk == Nat.add(Ok, X) : Nat},
  d: Sep(Oj, Ok)) -> Sep(Tj, Tk):
  match d:
    case Inl{l}:
      Inl{N.le_rw_r(4n+Tj, Nat.add(Ok, X), Tk, Equal.sym(Nat, Tk, Nat.add(Ok, X), ek),
        N.le_rw_l(4n+Nat.add(Oj, X), 4n+Tj, Nat.add(Ok, X), Equal.cong(Nat, Nat, z => 4n+z, Nat.add(Oj, X), Tj, Equal.sym(Nat, Tj, Nat.add(Oj, X), ej)),
          Z.le.add_r(4n+Oj, Ok, X, l)))}
    case Inr{r}:
      Inr{N.le_rw_r(4n+Tk, Nat.add(Oj, X), Tj, Equal.sym(Nat, Tj, Nat.add(Oj, X), ej),
        N.le_rw_l(4n+Nat.add(Ok, X), 4n+Tk, Nat.add(Oj, X), Equal.cong(Nat, Nat, z => 4n+z, Nat.add(Ok, X), Tk, Equal.sym(Nat, Tk, Nat.add(Ok, X), ek)),
          Z.le.add_r(4n+Ok, Oj, X, r)))}

def cell.cong5(-x0: U32, -x1: U32, -x2: U32, -x3: U32, -x4: U32, -y0: U32, -y1: U32, -y2: U32, -y3: U32, -y4: U32,
  e0: {x0 == y0 : U32}, e1: {x1 == y1 : U32}, e2: {x2 == y2 : U32}, e3: {x3 == y3 : U32}, e4: {x4 == y4 : U32}) ->
  {C.Cir.Cell{x0, x1, x2, x3, x4} == C.Cir.Cell{y0, y1, y2, y3, y4} : C.Cir.Cell}:
  %e0 : {C.Cir.Cell{x0, x1, x2, x3, x4} == C.Cir.Cell{_, y1, y2, y3, y4} : C.Cir.Cell}
  %e1 : {C.Cir.Cell{x0, x1, x2, x3, x4} == C.Cir.Cell{x0, _, y2, y3, y4} : C.Cir.Cell}
  %e2 : {C.Cir.Cell{x0, x1, x2, x3, x4} == C.Cir.Cell{x0, x1, _, y3, y4} : C.Cir.Cell}
  %e3 : {C.Cir.Cell{x0, x1, x2, x3, x4} == C.Cir.Cell{x0, x1, x2, _, y4} : C.Cir.Cell}
  %e4 : {C.Cir.Cell{x0, x1, x2, x3, x4} == C.Cir.Cell{x0, x1, x2, x3, _} : C.Cir.Cell}
  {==}

# field j of the cell c, after a write of a word outside the cell
def fld.w32(+m: C.Wasm.Bytes, +a: U32, +v: U32, +c: U32, +j: Nat, +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hc: N.Le(1n+U32.to_nat(c), P), +hA: N.Le(4n+U32.to_nat(a), W), +hj: N.Le(4n+O(j), 20n),
  s: Either<&2, &2, N.Le(20n+PH.H.t20(U32.to_nat(c)), U32.to_nat(a)), N.Le(4n+U32.to_nat(a), PH.H.t20(U32.to_nat(c)))>) ->
  {Y.V32(C.Wasm.write32(m, a, v), Q.at.f(c, j)) == Y.V32(m, Q.at.f(c, j)) : U32}:
  +f = Q.at.f(c, j)
  Y.V32.out32(m, a, v, f, disj4(f, a, W, hW, fld.room(c, j, P, hP, W, hW, hc, hj), hA,
    fsep(PH.H.t20(U32.to_nat(c)), O(j), U32.to_nat(f), fld.nat(c, j, P, hP, W, hW, hc, hj), hj, U32.to_nat(a), s)))

# a write of a word outside a cell keeps it
def rcell.w32(+m: C.Wasm.Bytes, +a: U32, +v: U32, +c: U32, +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hc: N.Le(1n+U32.to_nat(c), P), +hA: N.Le(4n+U32.to_nat(a), W),
  +s: Either<&2, &2, N.Le(20n+PH.H.t20(U32.to_nat(c)), U32.to_nat(a)), N.Le(4n+U32.to_nat(a), PH.H.t20(U32.to_nat(c)))>) ->
  {Q.RCell(C.Wasm.write32(m, a, v), c) == Q.RCell(m, c) : C.Cir.Cell}:
  +m2 = C.Wasm.write32(m, a, v)
  cell.cong5(Y.V32(m2, Q.at.f(c, 0n)), Y.V32(m2, Q.at.f(c, 1n)), Y.V32(m2, Q.at.f(c, 2n)), Y.V32(m2, Q.at.f(c, 3n)), Y.V32(m2, Q.at.f(c, 4n)),
    Y.V32(m, Q.at.f(c, 0n)), Y.V32(m, Q.at.f(c, 1n)), Y.V32(m, Q.at.f(c, 2n)), Y.V32(m, Q.at.f(c, 3n)), Y.V32(m, Q.at.f(c, 4n)),
    fld.w32(m, a, v, c, 0n, P, hP, W, hW, hc, hA, Unit{}, s), fld.w32(m, a, v, c, 1n, P, hP, W, hW, hc, hA, Unit{}, s),
    fld.w32(m, a, v, c, 2n, P, hP, W, hW, hc, hA, Unit{}, s), fld.w32(m, a, v, c, 3n, P, hP, W, hW, hc, hA, Unit{}, s),
    fld.w32(m, a, v, c, 4n, P, hP, W, hW, hc, hA, Unit{}, s))

# field j of the cell c, after a write of a byte outside the cell
def fld.w8(+m: C.Wasm.Bytes, +x: U32, +y: U32, +c: U32, +j: Nat, +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hc: N.Le(1n+U32.to_nat(c), P), +hj: N.Le(4n+O(j), 20n),
  s: Either<&2, &2, N.Le(20n+PH.H.t20(U32.to_nat(c)), U32.to_nat(x)), N.Le(1n+U32.to_nat(x), PH.H.t20(U32.to_nat(c)))>) ->
  {Y.V32(C.Wasm.write8(m, x, y), Q.at.f(c, j)) == Y.V32(m, Q.at.f(c, j)) : U32}:
  +f = Q.at.f(c, j)
  Y.V32.out8(m, x, y, f, in4(f, x, W, hW, fld.room(c, j, P, hP, W, hW, hc, hj),
    fout(PH.H.t20(U32.to_nat(c)), O(j), U32.to_nat(f), fld.nat(c, j, P, hP, W, hW, hc, hj), hj, U32.to_nat(x), s)))

# a write of a byte outside a cell keeps it
def rcell.w8(+m: C.Wasm.Bytes, +x: U32, +y: U32, +c: U32, +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hc: N.Le(1n+U32.to_nat(c), P),
  +s: Either<&2, &2, N.Le(20n+PH.H.t20(U32.to_nat(c)), U32.to_nat(x)), N.Le(1n+U32.to_nat(x), PH.H.t20(U32.to_nat(c)))>) ->
  {Q.RCell(C.Wasm.write8(m, x, y), c) == Q.RCell(m, c) : C.Cir.Cell}:
  +m2 = C.Wasm.write8(m, x, y)
  cell.cong5(Y.V32(m2, Q.at.f(c, 0n)), Y.V32(m2, Q.at.f(c, 1n)), Y.V32(m2, Q.at.f(c, 2n)), Y.V32(m2, Q.at.f(c, 3n)), Y.V32(m2, Q.at.f(c, 4n)),
    Y.V32(m, Q.at.f(c, 0n)), Y.V32(m, Q.at.f(c, 1n)), Y.V32(m, Q.at.f(c, 2n)), Y.V32(m, Q.at.f(c, 3n)), Y.V32(m, Q.at.f(c, 4n)),
    fld.w8(m, x, y, c, 0n, P, hP, W, hW, hc, Unit{}, s), fld.w8(m, x, y, c, 1n, P, hP, W, hW, hc, Unit{}, s),
    fld.w8(m, x, y, c, 2n, P, hP, W, hW, hc, Unit{}, s), fld.w8(m, x, y, c, 3n, P, hP, W, hW, hc, Unit{}, s),
    fld.w8(m, x, y, c, 4n, P, hP, W, hW, hc, Unit{}, s))

# field j of the cell i, after a write of field k of it
def fld.other(+m: C.Wasm.Bytes, +i: U32, +j: Nat, +k: Nat, +x: U32, +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hc: N.Le(1n+U32.to_nat(i), P), +hj: N.Le(4n+O(j), 20n), +hk: N.Le(4n+O(k), 20n),
  d: Sep(O(j), O(k))) ->
  {Y.V32(C.Wasm.write32(m, Q.at.f(i, k), x), Q.at.f(i, j)) == Y.V32(m, Q.at.f(i, j)) : U32}:
  +fj = Q.at.f(i, j)
  +fk = Q.at.f(i, k)
  Y.V32.out32(m, fk, x, fj, disj4(fj, fk, W, hW, fld.room(i, j, P, hP, W, hW, hc, hj), fld.room(i, k, P, hP, W, hW, hc, hk),
    fpair(PH.H.t20(U32.to_nat(i)), O(j), O(k), U32.to_nat(fj), U32.to_nat(fk), fld.nat(i, j, P, hP, W, hW, hc, hj), fld.nat(i, k, P, hP, W, hW, hc, hk), d)))

# a write of field k of the cell i sets that field of it
def rcell.set(+m: C.Wasm.Bytes, +i: U32, k: Nat, +x: U32, +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hc: N.Le(1n+U32.to_nat(i), P), hk: {Nat.is_le(k, 4n) == True{} : Bool}) ->
  {Q.RCell(C.Wasm.write32(m, Q.at.f(i, k), x), i) == C.Cir.Cell.set(k, Q.RCell(m, i), x) : C.Cir.Cell}:
  match k:
    case 0n:
      +m2 = C.Wasm.write32(m, Q.at.f(i, 0n), x)
      cell.cong5(Y.V32(m2, Q.at.f(i, 0n)), Y.V32(m2, Q.at.f(i, 1n)), Y.V32(m2, Q.at.f(i, 2n)), Y.V32(m2, Q.at.f(i, 3n)), Y.V32(m2, Q.at.f(i, 4n)),
        x, Y.V32(m, Q.at.f(i, 1n)), Y.V32(m, Q.at.f(i, 2n)), Y.V32(m, Q.at.f(i, 3n)), Y.V32(m, Q.at.f(i, 4n)),
        Y.V32.same(m, Q.at.f(i, 0n), x), fld.other(m, i, 1n, 0n, x, P, hP, W, hW, hc, Unit{}, Unit{}, Inr{Unit{}}),
        fld.other(m, i, 2n, 0n, x, P, hP, W, hW, hc, Unit{}, Unit{}, Inr{Unit{}}), fld.other(m, i, 3n, 0n, x, P, hP, W, hW, hc, Unit{}, Unit{}, Inr{Unit{}}),
        fld.other(m, i, 4n, 0n, x, P, hP, W, hW, hc, Unit{}, Unit{}, Inr{Unit{}}))
    case 1n:
      +m2 = C.Wasm.write32(m, Q.at.f(i, 1n), x)
      cell.cong5(Y.V32(m2, Q.at.f(i, 0n)), Y.V32(m2, Q.at.f(i, 1n)), Y.V32(m2, Q.at.f(i, 2n)), Y.V32(m2, Q.at.f(i, 3n)), Y.V32(m2, Q.at.f(i, 4n)),
        Y.V32(m, Q.at.f(i, 0n)), x, Y.V32(m, Q.at.f(i, 2n)), Y.V32(m, Q.at.f(i, 3n)), Y.V32(m, Q.at.f(i, 4n)),
        fld.other(m, i, 0n, 1n, x, P, hP, W, hW, hc, Unit{}, Unit{}, Inl{Unit{}}), Y.V32.same(m, Q.at.f(i, 1n), x),
        fld.other(m, i, 2n, 1n, x, P, hP, W, hW, hc, Unit{}, Unit{}, Inr{Unit{}}), fld.other(m, i, 3n, 1n, x, P, hP, W, hW, hc, Unit{}, Unit{}, Inr{Unit{}}),
        fld.other(m, i, 4n, 1n, x, P, hP, W, hW, hc, Unit{}, Unit{}, Inr{Unit{}}))
    case 2n:
      +m2 = C.Wasm.write32(m, Q.at.f(i, 2n), x)
      cell.cong5(Y.V32(m2, Q.at.f(i, 0n)), Y.V32(m2, Q.at.f(i, 1n)), Y.V32(m2, Q.at.f(i, 2n)), Y.V32(m2, Q.at.f(i, 3n)), Y.V32(m2, Q.at.f(i, 4n)),
        Y.V32(m, Q.at.f(i, 0n)), Y.V32(m, Q.at.f(i, 1n)), x, Y.V32(m, Q.at.f(i, 3n)), Y.V32(m, Q.at.f(i, 4n)),
        fld.other(m, i, 0n, 2n, x, P, hP, W, hW, hc, Unit{}, Unit{}, Inl{Unit{}}), fld.other(m, i, 1n, 2n, x, P, hP, W, hW, hc, Unit{}, Unit{}, Inl{Unit{}}),
        Y.V32.same(m, Q.at.f(i, 2n), x), fld.other(m, i, 3n, 2n, x, P, hP, W, hW, hc, Unit{}, Unit{}, Inr{Unit{}}),
        fld.other(m, i, 4n, 2n, x, P, hP, W, hW, hc, Unit{}, Unit{}, Inr{Unit{}}))
    case 3n:
      +m2 = C.Wasm.write32(m, Q.at.f(i, 3n), x)
      cell.cong5(Y.V32(m2, Q.at.f(i, 0n)), Y.V32(m2, Q.at.f(i, 1n)), Y.V32(m2, Q.at.f(i, 2n)), Y.V32(m2, Q.at.f(i, 3n)), Y.V32(m2, Q.at.f(i, 4n)),
        Y.V32(m, Q.at.f(i, 0n)), Y.V32(m, Q.at.f(i, 1n)), Y.V32(m, Q.at.f(i, 2n)), x, Y.V32(m, Q.at.f(i, 4n)),
        fld.other(m, i, 0n, 3n, x, P, hP, W, hW, hc, Unit{}, Unit{}, Inl{Unit{}}), fld.other(m, i, 1n, 3n, x, P, hP, W, hW, hc, Unit{}, Unit{}, Inl{Unit{}}),
        fld.other(m, i, 2n, 3n, x, P, hP, W, hW, hc, Unit{}, Unit{}, Inl{Unit{}}), Y.V32.same(m, Q.at.f(i, 3n), x),
        fld.other(m, i, 4n, 3n, x, P, hP, W, hW, hc, Unit{}, Unit{}, Inr{Unit{}}))
    case 4n:
      +m2 = C.Wasm.write32(m, Q.at.f(i, 4n), x)
      cell.cong5(Y.V32(m2, Q.at.f(i, 0n)), Y.V32(m2, Q.at.f(i, 1n)), Y.V32(m2, Q.at.f(i, 2n)), Y.V32(m2, Q.at.f(i, 3n)), Y.V32(m2, Q.at.f(i, 4n)),
        Y.V32(m, Q.at.f(i, 0n)), Y.V32(m, Q.at.f(i, 1n)), Y.V32(m, Q.at.f(i, 2n)), Y.V32(m, Q.at.f(i, 3n)), x,
        fld.other(m, i, 0n, 4n, x, P, hP, W, hW, hc, Unit{}, Unit{}, Inl{Unit{}}), fld.other(m, i, 1n, 4n, x, P, hP, W, hW, hc, Unit{}, Unit{}, Inl{Unit{}}),
        fld.other(m, i, 2n, 4n, x, P, hP, W, hW, hc, Unit{}, Unit{}, Inl{Unit{}}), fld.other(m, i, 3n, 4n, x, P, hP, W, hW, hc, Unit{}, Unit{}, Inl{Unit{}}),
        Y.V32.same(m, Q.at.f(i, 4n), x))
    case 5n+k5:
      Empty.absurd({Q.RCell(C.Wasm.write32(m, Q.at.f(i, 5n+k5), x), i) == C.Cir.Cell.set(5n+k5, Q.RCell(m, i), x) : C.Cir.Cell}, N.false_ne_true(hk))

# Views
# -----

def cons.cong(-A: Data, -h1: A, -h2: A, -t1: List<&2, A>, -t2: List<&2, A>, eh: {h1 == h2 : A}, et: {t1 == t2 : List<&2, A>}) ->
  {Con{h1, t1} == Con{h2, t2} : List<&2, A>}:
  %eh : {Con{h1, t1} == Con{_, t2} : List<&2, A>}
  %et : {Con{h1, t1} == Con{h1, _} : List<&2, A>}
  {==}

# the address x, of the number Xn, is outside the w bytes from a, when the q
# bytes from x are
def rb.out(+q: Nat, +X: Nat, +Xn: Nat, ex: {X == Xn : Nat}, +A: Nat, +w: Nat,
  s: Either<&2, &2, N.Le(1n+Nat.add(q, Xn), A), N.Le(Nat.add(w, A), Xn)>) -> Out(X, A, w):
  match s:
    case Inl{l}:
      Inl{N.le_rw_l(1n+Xn, 1n+X, A, Equal.cong(Nat, Nat, z => 1n+z, Xn, X, Equal.sym(Nat, X, Xn, ex)),
        N.le_trans(1n+Xn, 1n+Nat.add(q, Xn), A, N.le_add_l(q, Xn), l))}
    case Inr{r}:
      Inr{N.le_rw_r(Nat.add(w, A), Xn, X, Equal.sym(Nat, X, Xn, ex), r)}

# the same, from the next address
def rb.next(+p: Nat, +Xn: Nat, +A: Nat, +w: Nat,
  s: Either<&2, &2, N.Le(1n+Nat.add(p, Xn), A), N.Le(Nat.add(w, A), Xn)>) ->
  Either<&2, &2, N.Le(Nat.add(p, 1n+Xn), A), N.Le(Nat.add(w, A), 1n+Xn)>:
  match s:
    case Inl{l}:
      Inl{N.le_rw_l(1n+Nat.add(p, Xn), Nat.add(p, 1n+Xn), A, Equal.sym(Nat, Nat.add(p, 1n+Xn), 1n+Nat.add(p, Xn), N.add_succ_r(p, Xn)), l)}
    case Inr{r}:
      Inr{N.le_succ(Nat.add(w, A), Xn, r)}

# the number of x + 1, from that of x
def inc.eq(+x: U32, +Xn: Nat, +ex: {U32.to_nat(x) == Xn : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, h: N.Le(2n+Xn, W)) ->
  {U32.to_nat(U32.inc(x)) == 1n+Xn : Nat}:
  Equal.trans(Nat, U32.to_nat(U32.inc(x)), 1n+U32.to_nat(x), 1n+Xn,
    inc.nat(x, W, hW, N.le_rw_l(2n+Xn, 2n+U32.to_nat(x), W, Equal.cong(Nat, Nat, z => 2n+z, Xn, U32.to_nat(x), Equal.sym(Nat, U32.to_nat(x), Xn, ex)), h)),
    Equal.cong(Nat, Nat, z => 1n+z, U32.to_nat(x), Xn, ex))

# a write of a word outside the q bytes from x keeps them
def RB.w32(q: Nat, +m: C.Wasm.Bytes, +a: U32, +v: U32, +x: U32, +Xn: Nat, +ex: {U32.to_nat(x) == Xn : Nat},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hA: N.Le(4n+U32.to_nat(a), W), +hx: N.Le(1n+Nat.add(q, Xn), W),
  +s: Either<&2, &2, N.Le(Nat.add(q, Xn), U32.to_nat(a)), N.Le(4n+U32.to_nat(a), Xn)>) ->
  {Q.RB(q, C.Wasm.write32(m, a, v), x) == Q.RB(q, m, x) : List<&2, U32>}:
  match q:
    case 0n:
      {==}
    case 1n+(+p):
      +m2 = C.Wasm.write32(m, a, v)
      +A = U32.to_nat(a)
      +h2 = N.le_trans(2n+Xn, 2n+Nat.add(p, Xn), W, N.le_add_l(p, Xn), hx)
      +ex2 = inc.eq(x, Xn, ex, W, hW, h2)
      +hx2 = N.le_rw_l(2n+Nat.add(p, Xn), 1n+Nat.add(p, 1n+Xn), W,
        Equal.cong(Nat, Nat, z => 1n+z, 1n+Nat.add(p, Xn), Nat.add(p, 1n+Xn), Equal.sym(Nat, Nat.add(p, 1n+Xn), 1n+Nat.add(p, Xn), N.add_succ_r(p, Xn))), hx)
      cons.cong(U32, Y.R8(m2, x), Y.R8(m, x), Q.RB(p, m2, U32.inc(x)), Q.RB(p, m, U32.inc(x)),
        Y.R8.out32(m, a, v, x, out4(x, a, W, hW, hA, rb.out(p, U32.to_nat(x), Xn, ex, A, 4n, s))),
        RB.w32(p, m, a, v, U32.inc(x), 1n+Xn, ex2, W, hW, hA, hx2, rb.next(p, Xn, A, 4n, s)))

# a write of a byte outside the q bytes from x keeps them
def RB.w8(q: Nat, +m: C.Wasm.Bytes, +a: U32, +b: U32, +x: U32, +Xn: Nat, +ex: {U32.to_nat(x) == Xn : Nat},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hx: N.Le(1n+Nat.add(q, Xn), W),
  +s: Either<&2, &2, N.Le(Nat.add(q, Xn), U32.to_nat(a)), N.Le(1n+U32.to_nat(a), Xn)>) ->
  {Q.RB(q, C.Wasm.write8(m, a, b), x) == Q.RB(q, m, x) : List<&2, U32>}:
  match q:
    case 0n:
      {==}
    case 1n+(+p):
      +m2 = C.Wasm.write8(m, a, b)
      +A = U32.to_nat(a)
      +h2 = N.le_trans(2n+Xn, 2n+Nat.add(p, Xn), W, N.le_add_l(p, Xn), hx)
      +ex2 = inc.eq(x, Xn, ex, W, hW, h2)
      +hx2 = N.le_rw_l(2n+Nat.add(p, Xn), 1n+Nat.add(p, 1n+Xn), W,
        Equal.cong(Nat, Nat, z => 1n+z, 1n+Nat.add(p, Xn), Nat.add(p, 1n+Xn), Equal.sym(Nat, Nat.add(p, 1n+Xn), 1n+Nat.add(p, Xn), N.add_succ_r(p, Xn))), hx)
      cons.cong(U32, Y.R8(m2, x), Y.R8(m, x), Q.RB(p, m2, U32.inc(x)), Q.RB(p, m, U32.inc(x)),
        Y.R8.other(m, a, x, b, out.ne0(x, a, 1n, Unit{}, rb.out(p, U32.to_nat(x), Xn, ex, A, 1n, s))),
        RB.w8(p, m, a, b, U32.inc(x), 1n+Xn, ex2, W, hW, hx2, rb.next(p, Xn, A, 1n, s)))

# the cell c, of the number Cn, is outside the w bytes from a, when the q
# cells from c are
def rc.out(+p: Nat, +X: Nat, +Cn: Nat, ex: {X == Cn : Nat}, +A: Nat, +w: Nat,
  s: Either<&2, &2, N.Le(PH.H.t20(1n+Nat.add(p, Cn)), A), N.Le(Nat.add(w, A), PH.H.t20(Cn))>) ->
  Either<&2, &2, N.Le(20n+PH.H.t20(X), A), N.Le(Nat.add(w, A), PH.H.t20(X))>:
  match s:
    case Inl{l}:
      Inl{N.le_rw_l(20n+PH.H.t20(Cn), 20n+PH.H.t20(X), A, Equal.cong(Nat, Nat, z => 20n+PH.H.t20(z), Cn, X, Equal.sym(Nat, X, Cn, ex)),
        N.le_trans(20n+PH.H.t20(Cn), 20n+PH.H.t20(Nat.add(p, Cn)), A,
          N.add_mono(20n, 20n, PH.H.t20(Cn), PH.H.t20(Nat.add(p, Cn)), N.le_refl(20n), PH.H.t20_mono(Cn, Nat.add(p, Cn), N.le_add_l(p, Cn))), l))}
    case Inr{r}:
      Inr{N.le_rw_r(Nat.add(w, A), PH.H.t20(Cn), PH.H.t20(X), Equal.cong(Nat, Nat, z => PH.H.t20(z), Cn, X, Equal.sym(Nat, X, Cn, ex)), r)}

def rc.next(+p: Nat, +Cn: Nat, +A: Nat, +w: Nat,
  s: Either<&2, &2, N.Le(PH.H.t20(1n+Nat.add(p, Cn)), A), N.Le(Nat.add(w, A), PH.H.t20(Cn))>) ->
  Either<&2, &2, N.Le(PH.H.t20(Nat.add(p, 1n+Cn)), A), N.Le(Nat.add(w, A), PH.H.t20(1n+Cn))>:
  match s:
    case Inl{l}:
      Inl{N.le_rw_l(PH.H.t20(1n+Nat.add(p, Cn)), PH.H.t20(Nat.add(p, 1n+Cn)), A,
        Equal.cong(Nat, Nat, z => PH.H.t20(z), 1n+Nat.add(p, Cn), Nat.add(p, 1n+Cn), Equal.sym(Nat, Nat.add(p, 1n+Cn), 1n+Nat.add(p, Cn), N.add_succ_r(p, Cn))), l)}
    case Inr{r}:
      Inr{N.le_trans(Nat.add(w, A), PH.H.t20(Cn), 20n+PH.H.t20(Cn), r, N.le_add_l(20n, PH.H.t20(Cn)))}

def rc.inc(+c: U32, +Cn: Nat, +ec: {U32.to_nat(c) == Cn : Nat}, +p: Nat, +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hcq: N.Le(1n+Nat.add(p, Cn), P)) -> {U32.to_nat(U32.inc(c)) == 1n+Cn : Nat}:
  +hc = N.le_trans(1n+Cn, 1n+Nat.add(p, Cn), P, N.le_add_l(p, Cn), hcq)
  inc.eq(c, Cn, ec, W, hW, N.le_trans(2n+Cn, 36n+PH.H.t20(Cn), W,
    N.add_mono(2n, 36n, Cn, PH.H.t20(Cn), Unit{}, PH.H.le_t20(Cn)), cell.room(Cn, P, hP, W, hW, hc)))

def rc.hc(+c: U32, +Cn: Nat, +ec: {U32.to_nat(c) == Cn : Nat}, +p: Nat, +P: Nat, hcq: N.Le(1n+Nat.add(p, Cn), P)) -> N.Le(1n+U32.to_nat(c), P):
  N.le_rw_l(1n+Cn, 1n+U32.to_nat(c), P, Equal.cong(Nat, Nat, z => 1n+z, Cn, U32.to_nat(c), Equal.sym(Nat, U32.to_nat(c), Cn, ec)),
    N.le_trans(1n+Cn, 1n+Nat.add(p, Cn), P, N.le_add_l(p, Cn), hcq))

def rc.hcq(+p: Nat, +Cn: Nat, +P: Nat, hcq: N.Le(1n+Nat.add(p, Cn), P)) -> N.Le(Nat.add(p, 1n+Cn), P):
  N.le_rw_l(1n+Nat.add(p, Cn), Nat.add(p, 1n+Cn), P, Equal.sym(Nat, Nat.add(p, 1n+Cn), 1n+Nat.add(p, Cn), N.add_succ_r(p, Cn)), hcq)

# a write of a word outside the q cells from c keeps them
def RC.w32(q: Nat, +m: C.Wasm.Bytes, +a: U32, +v: U32, +c: U32, +Cn: Nat, +ec: {U32.to_nat(c) == Cn : Nat},
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hA: N.Le(4n+U32.to_nat(a), W), +hcq: N.Le(Nat.add(q, Cn), P),
  +s: Either<&2, &2, N.Le(PH.H.t20(Nat.add(q, Cn)), U32.to_nat(a)), N.Le(4n+U32.to_nat(a), PH.H.t20(Cn))>) ->
  {Q.RC(q, C.Wasm.write32(m, a, v), c) == Q.RC(q, m, c) : List<&2, C.Cir.Cell>}:
  match q:
    case 0n:
      {==}
    case 1n+(+p):
      +m2 = C.Wasm.write32(m, a, v)
      +A = U32.to_nat(a)
      cons.cong(C.Cir.Cell, Q.RCell(m2, c), Q.RCell(m, c), Q.RC(p, m2, U32.inc(c)), Q.RC(p, m, U32.inc(c)),
        rcell.w32(m, a, v, c, P, hP, W, hW, rc.hc(c, Cn, ec, p, P, hcq), hA, rc.out(p, U32.to_nat(c), Cn, ec, A, 4n, s)),
        RC.w32(p, m, a, v, U32.inc(c), 1n+Cn, rc.inc(c, Cn, ec, p, P, hP, W, hW, hcq), P, hP, W, hW, hA, rc.hcq(p, Cn, P, hcq),
          rc.next(p, Cn, A, 4n, s)))

# a write of a byte outside the q cells from c keeps them
def RC.w8(q: Nat, +m: C.Wasm.Bytes, +x: U32, +b: U32, +c: U32, +Cn: Nat, +ec: {U32.to_nat(c) == Cn : Nat},
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hcq: N.Le(Nat.add(q, Cn), P),
  +s: Either<&2, &2, N.Le(PH.H.t20(Nat.add(q, Cn)), U32.to_nat(x)), N.Le(1n+U32.to_nat(x), PH.H.t20(Cn))>) ->
  {Q.RC(q, C.Wasm.write8(m, x, b), c) == Q.RC(q, m, c) : List<&2, C.Cir.Cell>}:
  match q:
    case 0n:
      {==}
    case 1n+(+p):
      +m2 = C.Wasm.write8(m, x, b)
      +X = U32.to_nat(x)
      cons.cong(C.Cir.Cell, Q.RCell(m2, c), Q.RCell(m, c), Q.RC(p, m2, U32.inc(c)), Q.RC(p, m, U32.inc(c)),
        rcell.w8(m, x, b, c, P, hP, W, hW, rc.hc(c, Cn, ec, p, P, hcq), rc.out(p, U32.to_nat(c), Cn, ec, X, 1n, s)),
        RC.w8(p, m, x, b, U32.inc(c), 1n+Cn, rc.inc(c, Cn, ec, p, P, hP, W, hW, hcq), P, hP, W, hW, rc.hcq(p, Cn, P, hcq),
          rc.next(p, Cn, X, 1n, s)))

# Steps of stores
# ---------------

# a store of a word inside the memory
def store.step(+o: U32, +x: U32, +v: U32, +k: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +stk: List<&2, U32>,
  +loc: List<&2, U32>, +pg: U32, +lm: U32, +m: C.Wasm.Bytes, hin: {C.Wasm.inside(pg, x, o, 4) == True{} : Bool}) ->
  {PH.H.steps(1n, Q.Cfg(Con{C.Wasm.Instr.store{o}, k}, ls, Con{v, Con{x, stk}}, loc, C.Wasm.Memory{pg, lm, m})) ==
    Q.Cfg(k, ls, stk, loc, C.Wasm.Memory{pg, lm, C.Wasm.write32(m, U32.add(x, o), v)}) : C.Wasm.Step}:
  %Equal.sym(Bool, C.Wasm.inside(pg, x, o, 4), True{}, hin) :
    {C.Wasm.step.stored(_, U32.is_eq(4, 4), U32.add(x, o), v, k, ls, 1n, stk, loc, C.Wasm.Memory{pg, lm, m}) ==
      Q.Cfg(k, ls, stk, loc, C.Wasm.Memory{pg, lm, C.Wasm.write32(m, U32.add(x, o), v)}) : C.Wasm.Step}
  {==}

# a store of a byte inside the memory
def store8.step(+o: U32, +x: U32, +v: U32, +k: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +stk: List<&2, U32>,
  +loc: List<&2, U32>, +pg: U32, +lm: U32, +m: C.Wasm.Bytes, hin: {C.Wasm.inside(pg, x, o, 1) == True{} : Bool}) ->
  {PH.H.steps(1n, Q.Cfg(Con{C.Wasm.Instr.store8{o}, k}, ls, Con{v, Con{x, stk}}, loc, C.Wasm.Memory{pg, lm, m})) ==
    Q.Cfg(k, ls, stk, loc, C.Wasm.Memory{pg, lm, C.Wasm.write8(m, U32.add(x, o), U32.and(v, 255))}) : C.Wasm.Step}:
  %Equal.sym(Bool, C.Wasm.inside(pg, x, o, 1), True{}, hin) :
    {C.Wasm.step.stored(_, U32.is_eq(1, 4), U32.add(x, o), v, k, ls, 1n, stk, loc, C.Wasm.Memory{pg, lm, m}) ==
      Q.Cfg(k, ls, stk, loc, C.Wasm.Memory{pg, lm, C.Wasm.write8(m, U32.add(x, o), U32.and(v, 255))}) : C.Wasm.Step}
  {==}

# Bytes that fit
# --------------

# 16 <= W
def w16(+P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat}) -> N.Le(16n, W):
  N.le_rw_r(16n, PH.H.W(32n), W, Equal.sym(Nat, W, PH.H.W(32n), hW),
    N.le_rw_r(16n, Nat.add(PH.H.W(4n), PH.H.t20(P)), PH.H.W(32n), hP, N.le_add_r(16n, PH.H.t20(P))))

# a < b is false for b <= a
def nle.lt(a: Nat, b: Nat, e: {Nat.is_le(a, b) == False{} : Bool}) -> N.Le(1n+b, a):
  match a b:
    case 0n 0n:
      Empty.absurd(N.Le(1n, 0n), N.true_ne_false(e))
    case 0n 1n+q:
      Empty.absurd(N.Le(2n+q, 0n), N.true_ne_false(e))
    case 1n+p 0n:
      N.le_zero(p)
    case 1n+p 1n+q:
      nle.lt(p, q, e)

# w >= 1 bytes from x fit in the memory of p pages, when they end within it
def fits.ok(+p: U32, +x: U32, +w: U32, +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hw: N.Le(1n, U32.to_nat(w)),
  +h: N.Le(Nat.add(U32.to_nat(x), U32.to_nat(w)), Q.PB(p)), +hb: N.Le(1n+Q.PB(p), W)) -> {C.Wasm.fits(p, x, w) == True{} : Bool}:
  +X = U32.to_nat(x)
  +h1 = N.le_rw_l(Nat.add(X, U32.to_nat(w)), Nat.add(Nat.add(X, U32.to_nat(0)), U32.to_nat(w)), Q.PB(p),
    Equal.cong(Nat, Nat, z => Nat.add(z, U32.to_nat(w)), X, Nat.add(X, U32.to_nat(0)), Equal.sym(Nat, Nat.add(X, 0n), X, N.add_zero(X))), h)
  +e1 = Z.inside.ok(p, x, 0, w, W, hW, hw, h1, hb)
  +t1 = {(%Equal.sym(Bool, U32.is_lt(x, x), False{}, Z.nlt.of(x, x, N.le_refl(X))) :
      {Bool.and(Bool.not(_), C.Wasm.fits(p, x, w)) == C.Wasm.fits(p, x, w) : Bool}; {==}) :
    {Bool.and(Bool.not(U32.is_lt(x, x)), C.Wasm.fits(p, x, w)) == C.Wasm.fits(p, x, w) : Bool}}
  +t2 = Equal.cong(U32, Bool, z => Bool.and(Bool.not(U32.is_lt(z, x)), C.Wasm.fits(p, z, w)), U32.add(x, 0), x, Y.U32.add_zero(x))
  Equal.trans(Bool, C.Wasm.fits(p, x, w), Bool.and(Bool.not(U32.is_lt(x, x)), C.Wasm.fits(p, x, w)), True{},
    Equal.sym(Bool, Bool.and(Bool.not(U32.is_lt(x, x)), C.Wasm.fits(p, x, w)), C.Wasm.fits(p, x, w), t1),
    Equal.trans(Bool, Bool.and(Bool.not(U32.is_lt(x, x)), C.Wasm.fits(p, x, w)),
      Bool.and(Bool.not(U32.is_lt(U32.add(x, 0), x)), C.Wasm.fits(p, U32.add(x, 0), w)), True{},
      Equal.sym(Bool, Bool.and(Bool.not(U32.is_lt(U32.add(x, 0), x)), C.Wasm.fits(p, U32.add(x, 0), w)),
        Bool.and(Bool.not(U32.is_lt(x, x)), C.Wasm.fits(p, x, w)), t2), e1))

def fits0.go(+p: U32, +x: U32, c1: {U32.is_lt(x, x) == False{} : Bool}, c2: {U32.is_zero(x) == False{} : Bool},
  c3: {U32.is_lt(U32.shrn(U32.sub(x, 1), 16n), p) == True{} : Bool}) -> {C.Wasm.fits.end(U32.is_lt(x, x), p, x) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_lt(x, x), False{}, c1) : {C.Wasm.fits.end(_, p, x) == True{} : Bool}
  %Equal.sym(Bool, U32.is_zero(x), False{}, c2) : {Bool.or(_, U32.is_lt(U32.shrn(U32.sub(x, 1), 16n), p)) == True{} : Bool}
  %Equal.sym(Bool, U32.is_lt(U32.shrn(U32.sub(x, 1), 16n), p), True{}, c3) : {Bool.or(False{}, _) == True{} : Bool}
  {==}

# no bytes from x fit in the memory of p pages, when x is not 0 and is
# within it
def fits0(+p: U32, +x: U32, +h1: N.Le(1n, U32.to_nat(x)), +h: N.Le(U32.to_nat(x), Q.PB(p))) -> {C.Wasm.fits(p, x, 0) == True{} : Bool}:
  +X = U32.to_nat(x)
  +d = U32.sub(x, 1)
  +sh = U32.shrn(d, 16n)
  +ed = Z.dec.nat(x, h1)
  +h4 = N.le_trans(1n+N.D(16n, U32.to_nat(sh)), 1n+U32.to_nat(d), Q.PB(p), V.shrn.le(16n, d),
    N.le_rw_l(X, 1n+U32.to_nat(d), Q.PB(p), Equal.sym(Nat, 1n+U32.to_nat(d), X, ed), h))
  +c3 = Z.lt.to(sh, p, V.dlt(16n, U32.to_nat(sh), U32.to_nat(p), h4))
  +t2 = Equal.cong(U32, Bool, z => C.Wasm.fits.end(U32.is_lt(z, x), p, z), U32.add(x, 0), x, Y.U32.add_zero(x))
  Equal.trans(Bool, C.Wasm.fits(p, x, 0), C.Wasm.fits.end(U32.is_lt(x, x), p, x), True{},
    t2, fits0.go(p, x, Z.nlt.of(x, x, N.le_refl(X)), Z.nz.to(x, h1), c3))

# Reading the output
# ------------------

# the host's read of q bytes is the view RB
def rb.read(q: Nat, +m: C.Wasm.Bytes, +x: U32) -> {C.Wasm.read.bytes(q, m, x) == Q.RB(q, m, x) : List<&2, U32>}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(C.Wasm.Peek, C.Wasm.read8(m, x), C.Wasm.Peek{Y.R8(m, x), m}, Y.read8.eq(m, x)) :
        {C.Wasm.read.bytes.of(_, m2 => C.Wasm.read.bytes(p, m2, U32.inc(x))) == Q.RB(1n+p, m, x) : List<&2, U32>}
      cons.cong(U32, Y.R8(m, x), Y.R8(m, x), C.Wasm.read.bytes(p, m, U32.inc(x)), Q.RB(p, m, U32.inc(x)), {==}, rb.read(p, m, U32.inc(x)))

# the host reads the output from the address at byte 0 and the length at
# byte 4
def out.ok(+pg: U32, +lm: U32, +m2: C.Wasm.Bytes, +A0: U32, +on: U32,
  f8: {C.Wasm.fits(pg, 0, 8) == True{} : Bool}, v0: {Y.V32(m2, 0) == A0 : U32}, v4: {Y.V32(m2, 4) == on : U32},
  fo: {C.Wasm.fits(pg, A0, on) == True{} : Bool}) ->
  {C.Wasm.run.output(C.Wasm.Memory{pg, lm, m2}) == C.Wasm.Outcome.result{C.Wasm.read.bytes(U32.to_nat(on), m2, A0)} : C.Wasm.Outcome}:
  +R = {C.Wasm.Outcome.result{C.Wasm.read.bytes(U32.to_nat(on), m2, A0)} : C.Wasm.Outcome}
  %Equal.sym(Bool, C.Wasm.fits(pg, 0, 8), True{}, f8) : {C.Wasm.run.output.at(_, pg, m2) == R : C.Wasm.Outcome}
  %Equal.sym(C.Wasm.Peek, C.Wasm.read32(m2, 0), C.Wasm.Peek{Y.V32(m2, 0), m2}, Y.read32.eq(m2, 0)) :
    {C.Wasm.run.output.a(pg, _) == R : C.Wasm.Outcome}
  %Equal.sym(U32, Y.V32(m2, 0), A0, v0) : {C.Wasm.run.output.n(pg, _, C.Wasm.read32(m2, 4)) == R : C.Wasm.Outcome}
  %Equal.sym(C.Wasm.Peek, C.Wasm.read32(m2, 4), C.Wasm.Peek{Y.V32(m2, 4), m2}, Y.read32.eq(m2, 4)) :
    {C.Wasm.run.output.n(pg, A0, _) == R : C.Wasm.Outcome}
  %Equal.sym(U32, Y.V32(m2, 4), on, v4) : {C.Wasm.run.output.if(C.Wasm.fits(pg, A0, _), m2, A0, _) == R : C.Wasm.Outcome}
  %Equal.sym(Bool, C.Wasm.fits(pg, A0, on), True{}, fo) : {C.Wasm.run.output.if(_, m2, A0, on) == R : C.Wasm.Outcome}
  {==}

def is.con(l: List<&2, U32>) -> Data:
  match l:
    case Nil{}:
      Empty
    case Con{_, _}:
      Unit

def revgo.ne(t: List<&2, U32>, -h: U32, -acc: List<&2, U32>, e: {List.reverse.go(&2, U32, t, Con{h, acc}) == Nil{} : List<&2, U32>}) -> Empty:
  match t:
    case Nil{}:
      %e : is.con(_)
      Unit{}
    case Con{h2, t2}:
      revgo.ne(t2, h2, Con{h, acc}, e)

# a list whose reverse is empty is empty
def rev.nil(ou: List<&2, U32>, e: {Nil{} == List.reverse(&2, U32, ou) : List<&2, U32>}) -> {ou == Nil{} : List<&2, U32>}:
  match ou:
    case Nil{}:
      {==}
    case Con{h, t}:
      Empty.absurd({Con{h, t} == Nil{} : List<&2, U32>}, revgo.ne(t, h, Nil{}, Equal.sym(List<&2, U32>, Nil{}, List.reverse(&2, U32, Con{h, t}), e)))

# Bounds of the run
# -----------------

# the input starts at byte 20 or later, so the memory has 20 bytes or more
def b.a20(-P: Nat, -G: Nat, +a: U32, -nx: U32, -fi: U32, +im: U32, -pg: U32, -lm: U32, -inp: List<&2, U32>, -on: U32,
  +hB: Q.Bounds(P, G, a, nx, fi, im, pg, lm, inp, on)) -> N.Le(20n, U32.to_nat(a)):
  +K = U32.to_nat(im)
  N.le_rw_r(20n, PH.H.t20(1n+K), U32.to_nat(a), Equal.sym(Nat, U32.to_nat(a), PH.H.t20(1n+K), Q.b.a(P, G, a, nx, fi, im, pg, lm, inp, on, hB)),
    N.le_add_r(20n, PH.H.t20(K)))

def b.pb20(-P: Nat, -G: Nat, +a: U32, -nx: U32, -fi: U32, +im: U32, +pg: U32, -lm: U32, +inp: List<&2, U32>, -on: U32,
  +hB: Q.Bounds(P, G, a, nx, fi, im, pg, lm, inp, on)) -> N.Le(20n, Q.PB(pg)):
  +A = U32.to_nat(a)
  N.le_trans(20n, A, Q.PB(pg), b.a20(P, G, a, nx, fi, im, pg, lm, inp, on, hB),
    N.le_trans(A, Nat.add(A, List.length(&2, U32, inp)), Q.PB(pg), N.le_add_r(A, List.length(&2, U32, inp)),
      Q.b.epb(P, G, a, nx, fi, im, pg, lm, inp, on, hB)))

# the cells end at byte 20 or later
def inv.x20(+P: Nat, +G: Nat, +a: U32, +n: U32, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32, +m: C.Wasm.Bytes, +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m)) ->
  N.Le(20n, PH.H.t20(U32.to_nat(nx))):
  +hB = Q.inv.bounds(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)
  +A = U32.to_nat(a)
  +FI = U32.to_nat(fi)
  N.le_trans(20n, PH.H.t20(FI), PH.H.t20(U32.to_nat(nx)),
    N.le_trans(20n, A, PH.H.t20(FI), b.a20(P, G, a, nx, fi, im, pg, lm, inp, on, hB),
      N.le_trans(A, Nat.add(A, List.length(&2, U32, inp)), PH.H.t20(FI), N.le_add_r(A, List.length(&2, U32, inp)),
        Q.b.efi(P, G, a, nx, fi, im, pg, lm, inp, on, hB))),
    PH.H.t20_mono(FI, U32.to_nat(nx), Q.inv.fle(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)))

# 20 × next is below W
def b.xw(-G: Nat, -a: U32, +nx: U32, -fi: U32, -im: U32, -pg: U32, -lm: U32, -inp: List<&2, U32>, -on: U32,
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hB: Q.Bounds(P, G, a, nx, fi, im, pg, lm, inp, on)) -> N.Le(1n+PH.H.t20(U32.to_nat(nx)), W):
  N.le_rw_r(1n+PH.H.t20(U32.to_nat(nx)), PH.H.W(32n), W, Equal.sym(Nat, W, PH.H.W(32n), hW),
    PH.H.t20_bound(32n, U32.to_nat(nx), P, hP, Q.b.nx(P, G, a, nx, fi, im, pg, lm, inp, on, hB)))

# the words at 0 and 4 do not overlap
def d04() -> Y.Disj4(0, 4):
  (((({==}, {==}), ({==}, {==})), (({==}, {==}), ({==}, {==}))), ((({==}, {==}), ({==}, {==})), (({==}, {==}), ({==}, {==}))))

# A store into a view
# -------------------

# Nat numbers that are not equal: one is below the other
def nat.ne(+x: Nat, +y: Nat, k: {x == y : Nat} -> Empty) -> Ne(x, y):
  match x y:
    case 0n 0n:
      Empty.absurd(Ne(0n, 0n), k({==}))
    case 0n 1n+q:
      Inl{N.le_zero(q)}
    case 1n+p 0n:
      Inr{N.le_zero(p)}
    case 1n+p 1n+q:
      nat.ne(p, q, e => k(Equal.cong(Nat, Nat, z => 1n+z, p, q, e)))

# U32s that do not compare equal have different numbers
def ne.of(+c: U32, +i: U32, e: {U32.is_eq(c, i) == False{} : Bool}) -> Ne(U32.to_nat(c), U32.to_nat(i)):
  nat.ne(U32.to_nat(c), U32.to_nat(i), h => Y.ne.lit(c, i, e,
    Equal.trans(U32, c, U32.from_nat(U32.to_nat(c)), i, Equal.sym(U32, U32.from_nat(U32.to_nat(c)), c, Z.from.to(c)),
      Equal.trans(U32, U32.from_nat(U32.to_nat(c)), U32.from_nat(U32.to_nat(i)), i,
        Equal.cong(Nat, U32, z => U32.from_nat(z), U32.to_nat(c), U32.to_nat(i), h), Z.from.to(i)))))

# two different cells: a field of one is outside the other
def cell.sep(+C: Nat, +I: Nat, +Ok: Nat, hk: N.Le(4n+Ok, 20n), d: Ne(C, I)) ->
  Either<&2, &2, N.Le(20n+PH.H.t20(C), Nat.add(Ok, PH.H.t20(I))), N.Le(4n+Nat.add(Ok, PH.H.t20(I)), PH.H.t20(C))>:
  match d:
    case Inl{l}:
      Inl{N.le_trans(20n+PH.H.t20(C), PH.H.t20(I), Nat.add(Ok, PH.H.t20(I)), PH.H.t20_mono(1n+C, I, l), N.le_add_l(Ok, PH.H.t20(I)))}
    case Inr{r}:
      Inr{N.le_trans(4n+Nat.add(Ok, PH.H.t20(I)), 20n+PH.H.t20(I), PH.H.t20(C), Z.le.add_r(4n+Ok, 20n, PH.H.t20(I), hk), PH.H.t20_mono(1n+I, C, r))}

# the separation of a cell from a word, at the word's number
def rw.sep(+C: Nat, +T: Nat, +T2: Nat, e: {T == T2 : Nat},
  s: Either<&2, &2, N.Le(20n+PH.H.t20(C), T2), N.Le(4n+T2, PH.H.t20(C))>) ->
  Either<&2, &2, N.Le(20n+PH.H.t20(C), T), N.Le(4n+T, PH.H.t20(C))>:
  match s:
    case Inl{l}:
      Inl{N.le_rw_r(20n+PH.H.t20(C), T2, T, Equal.sym(Nat, T, T2, e), l)}
    case Inr{r}:
      Inr{N.le_rw_l(4n+T2, 4n+T, PH.H.t20(C), Equal.cong(Nat, Nat, z => 4n+z, T2, T, Equal.sym(Nat, T, T2, e)), r)}

# the cell c of a view, after a store into field k of the cell i
def rc.st.head(b: Bool, +m: C.Wasm.Bytes, +cl: C.Cir.Cells, +c: U32, +i: U32, +k: Nat, +x: U32,
  +hk: {Nat.is_le(k, 4n) == True{} : Bool}, +hk4: N.Le(4n+O(k), 20n),
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hc: N.Le(1n+U32.to_nat(c), P), +hi: N.Le(1n+U32.to_nat(i), P), +eb: {U32.is_eq(c, i) == b : Bool},
  +oldh: {Q.RCell(m, c) == C.Cir.Cells.get(cl, c) : C.Cir.Cell}) ->
  {Q.RCell(C.Wasm.write32(m, Q.at.f(i, k), x), c) == C.Cir.Cells.get(C.Cir.Cells.set(cl, i, C.Cir.Cell.set(k, C.Cir.Cells.get(cl, i), x)), c) : C.Cir.Cell}:
  match b:
    case True{}:
      +m2 = C.Wasm.write32(m, Q.at.f(i, k), x)
      +cv = C.Cir.Cell.set(k, C.Cir.Cells.get(cl, i), x)
      +cl2 = C.Cir.Cells.set(cl, i, cv)
      +eci = Y.U32.eq(c, i, eb)
      +oldi = {(%eci : {Q.RCell(m, _) == C.Cir.Cells.get(cl, _) : C.Cir.Cell}; oldh) : {Q.RCell(m, i) == C.Cir.Cells.get(cl, i) : C.Cir.Cell}}
      %Equal.sym(U32, c, i, eci) : {Q.RCell(m2, _) == C.Cir.Cells.get(cl2, _) : C.Cir.Cell}
      Equal.trans(C.Cir.Cell, Q.RCell(m2, i), C.Cir.Cell.set(k, Q.RCell(m, i), x), C.Cir.Cells.get(cl2, i),
        rcell.set(m, i, k, x, P, hP, W, hW, hi, hk),
        Equal.trans(C.Cir.Cell, C.Cir.Cell.set(k, Q.RCell(m, i), x), cv, C.Cir.Cells.get(cl2, i),
          Equal.cong(C.Cir.Cell, C.Cir.Cell, z => C.Cir.Cell.set(k, z, x), Q.RCell(m, i), C.Cir.Cells.get(cl, i), oldi),
          Equal.sym(C.Cir.Cell, C.Cir.Cells.get(cl2, i), cv, cells.same(cl, i, cv))))
    case False{}:
      +m2 = C.Wasm.write32(m, Q.at.f(i, k), x)
      +cv = C.Cir.Cell.set(k, C.Cir.Cells.get(cl, i), x)
      +cl2 = C.Cir.Cells.set(cl, i, cv)
      +I = U32.to_nat(i)
      +Aw = Q.at.f(i, k)
      +ea = fld.nat(i, k, P, hP, W, hW, hi, hk4)
      +s0 = cell.sep(U32.to_nat(c), I, O(k), hk4, ne.of(c, i, eb))
      +s = rw.sep(U32.to_nat(c), U32.to_nat(Aw), Nat.add(O(k), PH.H.t20(I)), ea, s0)
      Equal.trans(C.Cir.Cell, Q.RCell(m2, c), Q.RCell(m, c), C.Cir.Cells.get(cl2, c),
        rcell.w32(m, Aw, x, c, P, hP, W, hW, hc, fld.room(i, k, P, hP, W, hW, hi, hk4), s),
        Equal.trans(C.Cir.Cell, Q.RCell(m, c), C.Cir.Cells.get(cl, c), C.Cir.Cells.get(cl2, c), oldh,
          Equal.sym(C.Cir.Cell, C.Cir.Cells.get(cl2, c), C.Cir.Cells.get(cl, c), cells.other(cl, i, c, cv, eb))))

# a store into field k of the cell i: the q cells from c read as Cir's cells
# after its set
def RC.st(q: Nat, +m: C.Wasm.Bytes, +cl: C.Cir.Cells, +c: U32, +Cn: Nat, +ec: {U32.to_nat(c) == Cn : Nat},
  +i: U32, +k: Nat, +x: U32, +hk: {Nat.is_le(k, 4n) == True{} : Bool}, +hk4: N.Le(4n+O(k), 20n),
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hcq: N.Le(Nat.add(q, Cn), P), +hi: N.Le(1n+U32.to_nat(i), P),
  +old: {Q.RC(q, m, c) == Q.GC(q, cl, c) : List<&2, C.Cir.Cell>}) ->
  {Q.RC(q, C.Wasm.write32(m, Q.at.f(i, k), x), c) == Q.GC(q, C.Cir.Cells.set(cl, i, C.Cir.Cell.set(k, C.Cir.Cells.get(cl, i), x)), c) : List<&2, C.Cir.Cell>}:
  match q:
    case 0n:
      {==}
    case 1n+(+p):
      +m2 = C.Wasm.write32(m, Q.at.f(i, k), x)
      +cl2 = C.Cir.Cells.set(cl, i, C.Cir.Cell.set(k, C.Cir.Cells.get(cl, i), x))
      +oldh = Equal.cong(List<&2, C.Cir.Cell>, C.Cir.Cell, l => Q.hd.cell(l), Q.RC(1n+p, m, c), Q.GC(1n+p, cl, c), old)
      +oldt = Equal.cong(List<&2, C.Cir.Cell>, List<&2, C.Cir.Cell>, l => Q.tl.cell(l), Q.RC(1n+p, m, c), Q.GC(1n+p, cl, c), old)
      cons.cong(C.Cir.Cell, Q.RCell(m2, c), C.Cir.Cells.get(cl2, c), Q.RC(p, m2, U32.inc(c)), Q.GC(p, cl2, U32.inc(c)),
        rc.st.head(U32.is_eq(c, i), m, cl, c, i, k, x, hk, hk4, P, hP, W, hW, rc.hc(c, Cn, ec, p, P, hcq), hi, {==}, oldh),
        RC.st(p, m, cl, U32.inc(c), 1n+Cn, rc.inc(c, Cn, ec, p, P, hP, W, hW, hcq), i, k, x, hk, hk4, P, hP, W, hW,
          rc.hcq(p, Cn, P, hcq), hi, oldt))

# the output ends below W
def outw.go(ON: Nat, +X: Nat, +PBn: Nat, +W: Nat, hof: Q.OF(ON, X, PBn), hb: N.Le(1n+PBn, W), hxw: N.Le(1n+PH.H.t20(X), W)) ->
  N.Le(1n+Nat.add(ON, PH.H.t20(X)), W):
  match ON:
    case 0n:
      hxw
    case 1n+(+q):
      N.le_trans(1n+Nat.add(1n+q, PH.H.t20(X)), 1n+PBn, W,
        N.le_rw_l(Nat.add(PH.H.t20(X), 1n+q), Nat.add(1n+q, PH.H.t20(X)), PBn, Z.add.comm(PH.H.t20(X), 1n+q), hof), hb)

def b.outw(+P: Nat, +G: Nat, +a: U32, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32, +inp: List<&2, U32>, +on: U32,
  +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hG: {N.D(16n, G) == W : Nat},
  +hB: Q.Bounds(P, G, a, nx, fi, im, pg, lm, inp, on)) -> N.Le(1n+Nat.add(U32.to_nat(on), PH.H.t20(U32.to_nat(nx))), W):
  outw.go(U32.to_nat(on), U32.to_nat(nx), Q.PB(pg), W, Q.b.of(P, G, a, nx, fi, im, pg, lm, inp, on, hB),
    Q.pb.lt(P, G, a, nx, fi, im, pg, lm, inp, on, hB, W, hG), b.xw(G, a, nx, fi, im, pg, lm, inp, on, P, hP, W, hW, hB))

# the input ends below W
def b.inw(+P: Nat, +G: Nat, +a: U32, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32, +inp: List<&2, U32>, +on: U32,
  +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +hB: Q.Bounds(P, G, a, nx, fi, im, pg, lm, inp, on)) -> N.Le(1n+Nat.add(List.length(&2, U32, inp), U32.to_nat(a)), W):
  +A = U32.to_nat(a)
  +L = List.length(&2, U32, inp)
  N.le_trans(1n+Nat.add(L, A), 1n+PH.H.t20(P), W,
    N.le_rw_l(Nat.add(A, L), Nat.add(L, A), PH.H.t20(P), Z.add.comm(A, L), Q.b.e20(P, G, a, nx, fi, im, pg, lm, inp, on, hB)),
    N.le_rw_r(1n+PH.H.t20(P), PH.H.W(32n), W, Equal.sym(Nat, W, PH.H.W(32n), hW),
      N.le_rw_r(1n+PH.H.t20(P), Nat.add(PH.H.W(4n), PH.H.t20(P)), PH.H.W(32n), hP, N.le_add_l(15n, PH.H.t20(P)))))

# The relation after a store
# --------------------------

# fields 0 to 4 end within their cell
def ok4(k: Nat, hk: {Nat.is_le(k, 4n) == True{} : Bool}) -> N.Le(4n+O(k), 20n):
  match k:
    case 0n:
      Unit{}
    case 1n:
      Unit{}
    case 2n:
      Unit{}
    case 3n:
      Unit{}
    case 4n:
      Unit{}
    case 5n+k5:
      Empty.absurd(N.Le(4n+O(5n+k5), 20n), N.false_ne_true(hk))

# a word in the cell i ends by the next cell
def fend(+I: Nat, +Ok: Nat, hk4: N.Le(4n+Ok, 20n)) -> N.Le(4n+Nat.add(Ok, PH.H.t20(I)), PH.H.t20(1n+I)):
  Z.le.add_r(4n+Ok, 20n, PH.H.t20(I), hk4)

# the relation, from its parts that a store changes
def inv.store.go(+P: Nat, +G: Nat, +a: U32, +n: U32, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32, +m: C.Wasm.Bytes, +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +hG: {N.D(16n, G) == W : Nat},
  +i: U32, +k: Nat, +x: U32, +hk: {Nat.is_le(k, 4n) == True{} : Bool}, +hi: N.Le(1n+U32.to_nat(i), P),
  +s_in: Either<&2, &2, N.Le(Nat.add(List.length(&2, U32, inp), U32.to_nat(a)), U32.to_nat(Q.at.f(i, k))), N.Le(4n+U32.to_nat(Q.at.f(i, k)), U32.to_nat(a))>,
  +s_out: N.Le(4n+U32.to_nat(Q.at.f(i, k)), PH.H.t20(U32.to_nat(nx)))) ->
  Q.Inv(P, G, a, n, C.Cir.Cells.set(cl, i, C.Cir.Cell.set(k, C.Cir.Cells.get(cl, i), x)), nx, fi, im, pg, lm, inp, ou, on,
    C.Wasm.write32(m, Q.at.f(i, k), x)):
  +hB = Q.inv.bounds(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)
  +hk4 = ok4(k, hk)
  +Aw = Q.at.f(i, k)
  +hA = fld.room(i, k, P, hP, W, hW, hi, hk4)
  +K = U32.to_nat(im)
  +NX = U32.to_nat(nx)
  +FI = U32.to_nat(fi)
  +L = List.length(&2, U32, inp)
  +fle = Q.inv.fle(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)
  +hcb = N.le_rw_l(1n+K, Nat.add(K, 1n), P, Equal.sym(Nat, Nat.add(K, 1n), 1n+K, I.add.one(K)), Q.b.k(P, G, a, nx, fi, im, pg, lm, inp, on, hB))
  +hcm = N.le_rw_l(NX, Nat.add(Nat.sub(NX, FI), FI), P, Equal.sym(Nat, Nat.add(Nat.sub(NX, FI), FI), NX, Z.sub.add(NX, FI, fle)),
    Q.b.nx(P, G, a, nx, fi, im, pg, lm, inp, on, hB))
  +book = RC.st(K, m, cl, 1, 1n, {==}, i, k, x, hk, hk4, P, hP, W, hW, hcb, hi, Q.inv.book(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI))
  +mach = RC.st(Nat.sub(NX, FI), m, cl, fi, FI, {==}, i, k, x, hk, hk4, P, hP, W, hW, hcm, hi, Q.inv.mach(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI))
  +m2 = C.Wasm.write32(m, Aw, x)
  +inp2 = Equal.trans(List<&2, U32>, Q.RB(L, m2, a), Q.RB(L, m, a), inp,
    RB.w32(L, m, Aw, x, a, U32.to_nat(a), {==}, W, hW, hA, b.inw(P, G, a, nx, fi, im, pg, lm, inp, on, hP, W, hW, hB), s_in),
    Q.inv.inp(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI))
  +X = PH.H.t20(NX)
  +ex = at.nat(nx, P, hP, Q.b.nx(P, G, a, nx, fi, im, pg, lm, inp, on, hB))
  +out2 = Equal.trans(List<&2, U32>, Q.RB(U32.to_nat(on), m2, C.Cir.at(nx)), Q.RB(U32.to_nat(on), m, C.Cir.at(nx)), List.reverse(&2, U32, ou),
    RB.w32(U32.to_nat(on), m, Aw, x, C.Cir.at(nx), X, ex, W, hW, hA, b.outw(P, G, a, nx, fi, im, pg, lm, inp, on, hP, W, hW, hG, hB), Inr{s_out}),
    Q.inv.out(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI))
  (((Q.inv.ea(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI), Q.q.size(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)), (book, inp2)),
   ((fle, mach), (out2, hB)))

# a store into a cell of the book's, or of the machine's own: the relation holds
def inv.store.if(b1: Bool, +P: Nat, +G: Nat, +a: U32, +n: U32, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32, +m: C.Wasm.Bytes, +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +hG: {N.D(16n, G) == W : Nat},
  +i: U32, +k: Nat, +x: U32, +hk: {Nat.is_le(k, 4n) == True{} : Bool},
  +e1: {Bool.and(Bool.not(U32.is_zero(i)), U32.is_le(i, im)) == b1 : Bool},
  +hc: {Bool.or(b1, Bool.and(U32.is_le(fi, i), U32.is_lt(i, nx))) == True{} : Bool}) ->
  Q.Inv(P, G, a, n, C.Cir.Cells.set(cl, i, C.Cir.Cell.set(k, C.Cir.Cells.get(cl, i), x)), nx, fi, im, pg, lm, inp, ou, on,
    C.Wasm.write32(m, Q.at.f(i, k), x)):
  match b1:
    case True{}:
      +hB = Q.inv.bounds(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)
      +hk4 = ok4(k, hk)
      +I = U32.to_nat(i)
      +K = U32.to_nat(im)
      +A = U32.to_nat(a)
      +L = List.length(&2, U32, inp)
      +T = U32.to_nat(Q.at.f(i, k))
      +IK = Z.le.of(i, im, I.and.r(Bool.not(U32.is_zero(i)), U32.is_le(i, im), e1))
      +hi = N.le_trans(1n+I, 1n+K, P, IK, Q.b.k(P, G, a, nx, fi, im, pg, lm, inp, on, hB))
      +ea = fld.nat(i, k, P, hP, W, hW, hi, hk4)
      +h1 = N.le_rw_l(4n+Nat.add(O(k), PH.H.t20(I)), 4n+T, PH.H.t20(1n+K),
        Equal.cong(Nat, Nat, z => 4n+z, Nat.add(O(k), PH.H.t20(I)), T, Equal.sym(Nat, T, Nat.add(O(k), PH.H.t20(I)), ea)),
        N.le_trans(4n+Nat.add(O(k), PH.H.t20(I)), PH.H.t20(1n+I), PH.H.t20(1n+K), fend(I, O(k), hk4), PH.H.t20_mono(1n+I, 1n+K, IK)))
      +h2 = N.le_rw_r(4n+T, PH.H.t20(1n+K), A, Equal.sym(Nat, A, PH.H.t20(1n+K), Q.b.a(P, G, a, nx, fi, im, pg, lm, inp, on, hB)), h1)
      +h3 = N.le_trans(4n+T, A, PH.H.t20(U32.to_nat(nx)), h2,
        N.le_trans(A, Nat.add(A, L), PH.H.t20(U32.to_nat(nx)), N.le_add_r(A, L),
          N.le_trans(Nat.add(A, L), PH.H.t20(U32.to_nat(fi)), PH.H.t20(U32.to_nat(nx)), Q.b.efi(P, G, a, nx, fi, im, pg, lm, inp, on, hB),
            PH.H.t20_mono(U32.to_nat(fi), U32.to_nat(nx), Q.inv.fle(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)))))
      inv.store.go(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI, W, hW, hP, hG, i, k, x, hk, hi, Inr{h2}, h3)
    case False{}:
      +hB = Q.inv.bounds(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)
      +hk4 = ok4(k, hk)
      +I = U32.to_nat(i)
      +A = U32.to_nat(a)
      +L = List.length(&2, U32, inp)
      +T = U32.to_nat(Q.at.f(i, k))
      +hfi = Z.le.of(fi, i, I.and.l(U32.is_le(fi, i), U32.is_lt(i, nx), hc))
      +hnx = Z.lt.of(i, nx, I.and.r(U32.is_le(fi, i), U32.is_lt(i, nx), hc))
      +hi = N.le_trans(1n+I, U32.to_nat(nx), P, hnx, Q.b.nx(P, G, a, nx, fi, im, pg, lm, inp, on, hB))
      +ea = fld.nat(i, k, P, hP, W, hW, hi, hk4)
      +s_in = N.le_rw_r(Nat.add(L, A), Nat.add(O(k), PH.H.t20(I)), T, Equal.sym(Nat, T, Nat.add(O(k), PH.H.t20(I)), ea),
        N.le_trans(Nat.add(L, A), PH.H.t20(I), Nat.add(O(k), PH.H.t20(I)),
          N.le_trans(Nat.add(L, A), PH.H.t20(U32.to_nat(fi)), PH.H.t20(I),
            N.le_rw_l(Nat.add(A, L), Nat.add(L, A), PH.H.t20(U32.to_nat(fi)), Z.add.comm(A, L), Q.b.efi(P, G, a, nx, fi, im, pg, lm, inp, on, hB)),
            PH.H.t20_mono(U32.to_nat(fi), I, hfi)),
          N.le_add_l(O(k), PH.H.t20(I))))
      +s_out = N.le_rw_l(4n+Nat.add(O(k), PH.H.t20(I)), 4n+T, PH.H.t20(U32.to_nat(nx)),
        Equal.cong(Nat, Nat, z => 4n+z, Nat.add(O(k), PH.H.t20(I)), T, Equal.sym(Nat, T, Nat.add(O(k), PH.H.t20(I)), ea)),
        N.le_trans(4n+Nat.add(O(k), PH.H.t20(I)), PH.H.t20(1n+I), PH.H.t20(U32.to_nat(nx)), fend(I, O(k), hk4), PH.H.t20_mono(1n+I, U32.to_nat(nx), hnx)))
      inv.store.go(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI, W, hW, hP, hG, i, k, x, hk, hi, Inl{s_in}, s_out)

# a store into a cell that the machine may use: the relation holds
def inv.store(+P: Nat, +G: Nat, +a: U32, +n: U32, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32, +m: C.Wasm.Bytes, +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +hG: {N.D(16n, G) == W : Nat},
  +i: U32, +k: Nat, +x: U32, +hk: {Nat.is_le(k, 4n) == True{} : Bool}, +hc: {C.Cir.is_cell(i, im, fi, nx) == True{} : Bool}) ->
  Q.Inv(P, G, a, n, C.Cir.Cells.set(cl, i, C.Cir.Cell.set(k, C.Cir.Cells.get(cl, i), x)), nx, fi, im, pg, lm, inp, ou, on,
    C.Wasm.write32(m, Q.at.f(i, k), x)):
  inv.store.if(Bool.and(Bool.not(U32.is_zero(i)), U32.is_le(i, im)), P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI,
    W, hW, hP, hG, i, k, x, hk, {==}, hc)
