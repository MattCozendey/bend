# compiler: the host's run of the module
# ======================================
#
# Wasm.run of the module of a Cir program, step by step as the host does it
# (instantiation, alloc, the input's write, run, the status and the output),
# against Cir.result: the module decodes to itself and is valid, so the
# instance has the memory of the minimum with the book's cells (inst);
# alloc gives what Cir.alloc.pages says (af.call); run's start reaches the
# program's block with next = Cir.first (pr.go), where the relation holds
# (IN.inv0); the program's code does what Cir.exec says (T.sim.stmt), and
# run's status gives what Cir.ended says.

import Base
import ./impl.bend as C
import ./proof_need.bend as N
import ./proof_halt.bend as PH
import ./proof_module.bend as M
import ./proof_valid.bend as V
import ./proof_img.bend as G
import ./proof_sim_step.bend as S
import ./proof_sim_mem.bend as Y
import ./proof_sim_nat.bend as Z
import ./proof_sim_inv.bend as Q
import ./proof_sim_frame.bend as F
import ./proof_sim_alloc.bend as A
import ./proof_sim_div.bend as DV
import ./proof_sim_stmt.bend as T
import ./proof_sim_af.bend as AF
import ./proof_sim_pro.bend as PR
import ./proof_sim_init.bend as IN

# Numbers
# -------

# a U32 is below 2^32
def u32.bnd(+x: U32, +W: Nat, +hW: {W == PH.H.W(32n) : Nat}) -> N.Le(1n+U32.to_nat(x), W):
  match x:
    case U32{+w}:
      N.le_rw_r(1n+Word.to_nat(32n, w), PH.H.W(32n), W, Equal.sym(Nat, W, PH.H.W(32n), hW), PH.H.bound(32n, w))

# 2^n, as H.W and as D
def hw.d(+n: Nat) -> {PH.H.W(n) == N.D(n, PH.H.bn(True{})) : Nat}:
  {==}

# 2^32 is W
def d32.w(+W: Nat, +hW: {W == PH.H.W(32n) : Nat}) -> {N.D(32n, 1n) == W : Nat}:
  Equal.trans(Nat, N.D(32n, 1n), N.D(32n, PH.H.bn(True{})), W, Equal.cong(Nat, Nat, z => N.D(32n, z), 1n, PH.H.bn(True{}), {==}),
    Equal.trans(Nat, N.D(32n, PH.H.bn(True{})), PH.H.W(32n), W, Equal.sym(Nat, PH.H.W(32n), N.D(32n, PH.H.bn(True{})), hw.d(32n)),
      Equal.sym(Nat, W, PH.H.W(32n), hW)))

# 1 + (2^32 - 1) = 2^32
def max.nat(+W: Nat, +hW: {W == PH.H.W(32n) : Nat}) -> {1n+U32.to_nat(4294967295) == W : Nat}:
  Equal.trans(Nat, 1n+U32.to_nat(4294967295), N.D(32n, 1n), W, M.val_MAX(), d32.w(W, hW))

# a < b is false: b <= a
def nlt.rel(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), e: {Cmp.is_lt(c) == False{} : Bool}) -> N.Le(y, x):
  match c:
    case LT{}:
      Empty.absurd(N.Le(y, x), N.true_ne_false(e))
    case EQ{}:
      (%Equal.sym(Nat, x, y, r) : N.Le(y, _); N.le_refl(y))
    case GT{}:
      N.weaken(y, x, r)

def nlt.to(+a: U32, +b: U32, e: {U32.is_lt(a, b) == False{} : Bool}) -> N.Le(U32.to_nat(b), U32.to_nat(a)):
  nlt.rel(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), e)

# a > b is false: a <= b
def ngt.rel(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), e: {Cmp.is_gt(c) == False{} : Bool}) -> N.Le(x, y):
  match c:
    case LT{}:
      N.weaken(x, y, r)
    case EQ{}:
      (%r : N.Le(x, _); N.le_refl(x))
    case GT{}:
      Empty.absurd(N.Le(x, y), N.true_ne_false(e))

def ngt.to(+a: U32, +b: U32, e: {U32.is_gt(a, b) == False{} : Bool}) -> N.Le(U32.to_nat(a), U32.to_nat(b)):
  ngt.rel(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), e)

# a <= b: a <= b as numbers
def le.to(+a: U32, +b: U32, e: {U32.is_le(a, b) == True{} : Bool}) -> N.Le(U32.to_nat(a), U32.to_nat(b)):
  Z.rel.le(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), e)

# a = b is false, a <= b: a < b
def ne.rel(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), e: {Cmp.is_eq(c) == False{} : Bool}, h: N.Le(x, y)) -> N.Le(1n+x, y):
  match c:
    case LT{}:
      r
    case EQ{}:
      Empty.absurd(N.Le(1n+x, y), N.true_ne_false(e))
    case GT{}:
      Empty.absurd(N.Le(1n+x, y), N.not_succ_le(y, N.le_trans(1n+y, x, y, r, h)))

# n + 1, when n is not 2^32 - 1 = T
def inc.go(+n: U32, +T: Nat, +eT: {U32.to_nat(4294967295) == T : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +eW: {1n+T == W : Nat}, e: {U32.is_eq(n, 4294967295) == False{} : Bool}) ->
  {U32.to_nat(U32.inc(n)) == 1n+U32.to_nat(n) : Nat}:
  +X = U32.to_nat(n)
  +hn = N.le_rw_r(1n+X, W, 1n+T, Equal.sym(Nat, 1n+T, W, eW), u32.bnd(n, W, hW))
  r = {(%eT : N.Rel(U32.cmp(n, 4294967295), X, _); N.U32.rel(n, 4294967295)) :
    N.Rel(U32.cmp(n, 4294967295), X, T)}
  +lt = ne.rel(U32.cmp(n, 4294967295), X, T, r, e, hn)
  F.inc.eq(n, X, {==}, W, hW, N.le_rw_r(2n+X, 1n+T, W, eW, lt))

def inc.ne1(+n: U32, +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, e: {U32.is_eq(n, 4294967295) == False{} : Bool}) ->
  {U32.to_nat(U32.inc(n)) == 1n+U32.to_nat(n) : Nat}:
  inc.go(n, U32.to_nat(4294967295), {==}, W, hW, max.nat(W, hW), e)

# a sum that does not wrap is exact
def nw.go(c: Bool, +V: Nat, +A0: Nat, +B0: Nat, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  e: {Nat.add(V, N.D(32n, PH.H.bn(c))) == Nat.add(A0, B0) : Nat}, h: N.Le(A0, V), hB: N.Le(1n+B0, W)) -> {V == Nat.add(A0, B0) : Nat}:
  match c:
    case False{}:
      Equal.trans(Nat, V, Nat.add(V, 0n), Nat.add(A0, B0), Equal.sym(Nat, Nat.add(V, 0n), V, N.add_zero(V)),
        (%Equal.sym(Nat, N.D(32n, 0n), 0n, {==}) : {Nat.add(V, _) == Nat.add(A0, B0) : Nat}; e))
    case True{}:
      +e2 = Equal.trans(Nat, Nat.add(V, W), Nat.add(V, N.D(32n, PH.H.bn(True{}))), Nat.add(A0, B0),
        Equal.cong(Nat, Nat, z => Nat.add(V, z), W, N.D(32n, PH.H.bn(True{})), Equal.trans(Nat, W, PH.H.W(32n), N.D(32n, PH.H.bn(True{})), hW, hw.d(32n))), e)
      +l1 = N.le_rw_r(Nat.add(A0, W), Nat.add(V, W), Nat.add(A0, B0), e2, N.add_mono(A0, V, W, W, h, N.le_refl(W)))
      +l2 = PH.H.le_sub_add(A0, W, Nat.add(A0, B0), l1)
      +l3 = {(%Equal.trans(Nat, Nat.sub(Nat.add(A0, B0), A0), Nat.sub(Nat.add(B0, A0), A0), B0,
          Equal.cong(Nat, Nat, z => Nat.sub(z, A0), Nat.add(A0, B0), Nat.add(B0, A0), Z.add.comm(A0, B0)), DV.add.sub.r(B0, A0)) : N.Le(W, _); l2) : N.Le(W, B0)}
      Empty.absurd({V == Nat.add(A0, B0) : Nat}, N.not_succ_le(B0, N.le_trans(1n+B0, W, B0, hB, l3)))

def nowrap(+x: U32, +y: U32, +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, e: {U32.is_lt(U32.add(x, y), x) == False{} : Bool}) ->
  {U32.to_nat(U32.add(x, y)) == Nat.add(U32.to_nat(x), U32.to_nat(y)) : Nat}:
  match x y:
    case U32{+xw} U32{+yw}:
      +V = Word.to_nat(32n, Word.add(32n, xw, yw))
      nw.go(PH.H.cout(32n, xw, yw, False{}), V, Word.to_nat(32n, xw), Word.to_nat(32n, yw), W, hW, PH.H.adc(32n, xw, yw, False{}),
        nlt.to(U32{Word.add(32n, xw, yw)}, U32{xw}, e), u32.bnd(U32{yw}, W, hW))

# The lengths
# -----------

def enc.from(-X: Data, xs: List<&2, X>) -> {C.Wasm.encode.len(X, xs) == U32.from_nat(List.length(&2, X, xs)) : U32}:
  match xs:
    case Nil{}:
      {==}
    case Con{_, rest}:
      Equal.cong(U32, U32, z => U32.inc(z), C.Wasm.encode.len(X, rest), U32.from_nat(List.length(&2, X, rest)), enc.from(X, rest))

def L32.T(xs: List<&2, U32>, +n: U32, +v: U32) -> Data:
  S.P2({v == Z.incn(List.length(&2, U32, xs), n) : U32}, {U32.to_nat(v) == Nat.add(List.length(&2, U32, xs), U32.to_nat(n)) : Nat})

def L32.fin(+x: U32, +rest: List<&2, U32>, +n: U32, +v: U32, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  eb: {U32.is_eq(n, 4294967295) == False{} : Bool}, pr: L32.T(rest, U32.inc(n), v)) -> L32.T(Con{x, rest}, n, v):
  (+e1, +e2) = pr
  +q = List.length(&2, U32, rest)
  (e1, Equal.trans(Nat, U32.to_nat(v), Nat.add(q, U32.to_nat(U32.inc(n))), 1n+Nat.add(q, U32.to_nat(n)), e2,
    Equal.trans(Nat, Nat.add(q, U32.to_nat(U32.inc(n))), Nat.add(q, 1n+U32.to_nat(n)), 1n+Nat.add(q, U32.to_nat(n)),
      Equal.cong(Nat, Nat, z => Nat.add(q, z), U32.to_nat(U32.inc(n)), 1n+U32.to_nat(n), inc.ne1(n, W, hW, eb)),
      N.add_succ_r(q, U32.to_nat(n)))))

def L32.if(b: Bool, +x: U32, +n: U32, +rest: List<&2, U32>, +v: U32, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  eb: {U32.is_eq(n, 4294967295) == b : Bool},
  e: {C.Wasm.length32.if(b, u => C.Wasm.length32.go(rest, U32.inc(n))) == Some{v} : Maybe<&2, U32>},
  ih: {C.Wasm.length32.go(rest, U32.inc(n)) == Some{v} : Maybe<&2, U32>} -> L32.T(rest, U32.inc(n), v)) -> L32.T(Con{x, rest}, n, v):
  match b:
    case True{}:
      Empty.absurd(L32.T(Con{x, rest}, n, v), Q.none.some(v, e))
    case False{}:
      L32.fin(x, rest, n, v, W, hW, eb, ih(e))

# the length that length32 counts from n
def L32.go(xs: List<&2, U32>, +n: U32, +v: U32, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  e: {C.Wasm.length32.go(xs, n) == Some{v} : Maybe<&2, U32>}) -> L32.T(xs, n, v):
  match xs:
    case Nil{}:
      +ev = Equal.sym(U32, n, v, Q.some.inj(n, v, e))
      (ev, Equal.cong(U32, Nat, z => U32.to_nat(z), v, n, ev))
    case Con{+x, +rest}:
      L32.if(U32.is_eq(n, 4294967295), x, n, rest, v, W, hW, {==}, e, y => L32.go(rest, U32.inc(n), v, W, hW, y))
