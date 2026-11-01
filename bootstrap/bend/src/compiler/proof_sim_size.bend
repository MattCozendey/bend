# compiler: the size of the machine's code
# ========================================
#
# The bytes of the code section of Cir.module(Mach.code(), ...) are fewer
# than 2^32 - 1, the premise of M.module.round: each instruction encodes to
# at most 7 bytes, and a block to 3 more than its body (ib.len); the code of
# each node of a Cir program has at most 2^8 such bytes (cb.stmt); and
# Mach.code has at most 2^16 nodes (by evaluation).

import Base
import ./impl.bend as C
import ./proof_need.bend as N
import ./proof_halt.bend as PH
import ./proof_module.bend as M
import ./proof_sim_nat.bend as Z

# the units of code of an expression and of a statement: about one for each
# node, in the order that the code chains them (see cb.expr and cb.stmt)
def NE(e: C.Cir.Expr) -> Nat:
  match e:
    case C.Cir.Expr.const{_}:
      1n
    case C.Cir.Expr.get{_}:
      1n
    case C.Cir.Expr.op{_, a, b}:
      Nat.add(NE(a), Nat.add(NE(b), 1n))
    case C.Cir.Expr.eqz{a}:
      Nat.add(NE(a), 1n)
    case C.Cir.Expr.field{_, c}:
      Nat.add(NE(c), 1n)
    case C.Cir.Expr.byte{i}:
      Nat.add(NE(i), 1n)
    case C.Cir.Expr.size{}:
      1n

def NS(s: C.Cir.Stmt) -> Nat:
  match s:
    case C.Cir.Stmt.nop{}:
      0n
    case C.Cir.Stmt.set{_, e}:
      Nat.add(NE(e), 1n)
    case C.Cir.Stmt.store{_, c, v}:
      Nat.add(NE(c), Nat.add(1n, Nat.add(NE(v), 1n)))
    case C.Cir.Stmt.alloc{_}:
      1n
    case C.Cir.Stmt.emit{v}:
      Nat.add(1n, Nat.add(NE(v), 1n))
    case C.Cir.Stmt.seq{a, b}:
      Nat.add(NS(a), NS(b))
    case C.Cir.Stmt.if{c, t, e}:
      Nat.add(Nat.add(Nat.add(Nat.add(NE(c), Nat.add(1n, NS(t))), 1n), NS(e)), 1n)
    case C.Cir.Stmt.while{c, body}:
      Nat.add(Nat.add(Nat.add(NE(c), Nat.add(1n, NS(body))), 1n), 1n)
    case C.Cir.Stmt.halt{_}:
      1n

# a bound on the bytes of the instructions xs: 7 for each, 3 more than its
# body for a block or loop, 12 more than 5 per label for a br_table
def ib.tab(ls: List<&2, U32>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case Con{_, r}:
      5n+ib.tab(r)

def ib(xs: List<&2, C.Wasm.Instr>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, rest}:
      match x:
        case C.Wasm.Instr.block{body}:
          3n+Nat.add(ib(body), ib(rest))
        case C.Wasm.Instr.loop{body}:
          3n+Nat.add(ib(body), ib(rest))
        case C.Wasm.Instr.br_table{ls, _}:
          12n+Nat.add(ib.tab(ls), ib(rest))
        case _:
          7n+ib(rest)

# Bytes of instructions
# ----------------------

def len.u(+v: U32) -> N.Le(List.length(&2, U32, C.Wasm.encode.uleb(v)), 5n):
  M.ulen(5n, v)

def len.s(+v: U32) -> N.Le(List.length(&2, U32, C.Wasm.encode.sleb(v)), 5n):
  N.toLe(List.length(&2, U32, C.Wasm.encode.sleb(v)), 5n, PH.H.len_go(5n, v))

# an opcode, an immediate of at most 6 bytes, then R
def with.len(+op: U32, +imm: List<&2, U32>, +R: List<&2, U32>, +X: Nat, h: N.Le(List.length(&2, U32, imm), 6n),
  ih: N.Le(List.length(&2, U32, R), X)) -> N.Le(List.length(&2, U32, C.Wasm.encode.with(op, imm, R)), 7n+X):
  N.le_rw_l(Nat.add(List.length(&2, U32, imm), List.length(&2, U32, R)), List.length(&2, U32, List.append(&2, U32, imm, R)), 6n+X,
    Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, imm, R)), Nat.add(List.length(&2, U32, imm), List.length(&2, U32, R)), M.len.app(imm, R)),
    N.add_mono(List.length(&2, U32, imm), 6n, List.length(&2, U32, R), X, h, ih))

# the labels of a br_table
def labels.len(ls: List<&2, U32>, +acc: List<&2, U32>, +X: Nat, ih: N.Le(List.length(&2, U32, acc), X)) ->
  N.Le(List.length(&2, U32, C.Wasm.encode.labels(ls, acc)), Nat.add(ib.tab(ls), X)):
  match ls:
    case Nil{}:
      ih
    case Con{+l, +r}:
      N.le_rw_l(Nat.add(List.length(&2, U32, C.Wasm.encode.uleb(l)), List.length(&2, U32, C.Wasm.encode.labels(r, acc))),
        List.length(&2, U32, List.append(&2, U32, C.Wasm.encode.uleb(l), C.Wasm.encode.labels(r, acc))), 5n+Nat.add(ib.tab(r), X),
        Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, C.Wasm.encode.uleb(l), C.Wasm.encode.labels(r, acc))),
          Nat.add(List.length(&2, U32, C.Wasm.encode.uleb(l)), List.length(&2, U32, C.Wasm.encode.labels(r, acc))), M.len.app(C.Wasm.encode.uleb(l), C.Wasm.encode.labels(r, acc))),
        N.add_mono(List.length(&2, U32, C.Wasm.encode.uleb(l)), 5n, List.length(&2, U32, C.Wasm.encode.labels(r, acc)), Nat.add(ib.tab(r), X), len.u(l),
          labels.len(r, acc, X, ih)))

# a + (k + x) = k + (a + x)
def shk(+a: Nat, +k: Nat, +x: Nat) -> {Nat.add(a, Nat.add(k, x)) == Nat.add(k, Nat.add(a, x)) : Nat}:
  PH.H.add_k(a, k, x)

# the bytes of a block of the body b, then R: 3 more than the body's bound
def blk.len(+body: List<&2, C.Wasm.Instr>, +R: List<&2, U32>, +X: Nat, ih: N.Le(List.length(&2, U32, R), X),
  hb: N.Le(List.length(&2, U32, C.Wasm.encode.instrs(body, Con{11, R})), Nat.add(ib(body), 1n+List.length(&2, U32, R)))) ->
  N.Le(2n+List.length(&2, U32, C.Wasm.encode.instrs(body, Con{11, R})), 3n+Nat.add(ib(body), X)):
  N.le_trans(2n+List.length(&2, U32, C.Wasm.encode.instrs(body, Con{11, R})), 2n+Nat.add(ib(body), 1n+List.length(&2, U32, R)),
    3n+Nat.add(ib(body), X), hb,
    N.le_rw_l(3n+Nat.add(ib(body), List.length(&2, U32, R)), 2n+Nat.add(ib(body), 1n+List.length(&2, U32, R)), 3n+Nat.add(ib(body), X),
      Equal.sym(Nat, 2n+Nat.add(ib(body), 1n+List.length(&2, U32, R)), 3n+Nat.add(ib(body), List.length(&2, U32, R)),
        Equal.cong(Nat, Nat, z => 2n+z, Nat.add(ib(body), 1n+List.length(&2, U32, R)), 1n+Nat.add(ib(body), List.length(&2, U32, R)), N.add_succ_r(ib(body), List.length(&2, U32, R)))),
      N.add_mono(ib(body), ib(body), List.length(&2, U32, R), X, N.le_refl(ib(body)), ih)))

# reassociate the bound of a block
def blk.as(+Y: Nat, +a: Nat, +b: Nat, +c: Nat, h: N.Le(Y, 3n+Nat.add(a, Nat.add(b, c)))) -> N.Le(Y, 3n+Nat.add(Nat.add(a, b), c)):
  N.le_rw_r(Y, 3n+Nat.add(a, Nat.add(b, c)), 3n+Nat.add(Nat.add(a, b), c),
    Equal.cong(Nat, Nat, z => 3n+z, Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, b), c), Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), Z.add.assoc(a, b, c))), h)

def tab.as(+Y: Nat, +a: Nat, +b: Nat, +c: Nat, h: N.Le(Y, 12n+Nat.add(a, Nat.add(b, c)))) -> N.Le(Y, 12n+Nat.add(Nat.add(a, b), c)):
  N.le_rw_r(Y, 12n+Nat.add(a, Nat.add(b, c)), 12n+Nat.add(Nat.add(a, b), c),
    Equal.cong(Nat, Nat, z => 12n+z, Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, b), c), Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), Z.add.assoc(a, b, c))), h)

# the bytes of the instructions xs, then acc: at most ib(xs) + |acc|
def ib.len(xs: List<&2, C.Wasm.Instr>, +acc: List<&2, U32>) ->
  N.Le(List.length(&2, U32, C.Wasm.encode.instrs(xs, acc)), Nat.add(ib(xs), List.length(&2, U32, acc))):
  match xs:
    case Nil{}:
      N.le_refl(List.length(&2, U32, acc))
    case Con{x, +rest}:
      match x:
        case C.Wasm.Instr.const{+n}:
          with.len(65, C.Wasm.encode.sleb(n), C.Wasm.encode.instrs(rest, acc), Nat.add(ib(rest), List.length(&2, U32, acc)),
            N.le_trans(List.length(&2, U32, C.Wasm.encode.sleb(n)), 5n, 6n, len.s(n), Unit{}), ib.len(rest, acc))
        case C.Wasm.Instr.local_get{+i}:
          with.len(32, C.Wasm.encode.uleb(i), C.Wasm.encode.instrs(rest, acc), Nat.add(ib(rest), List.length(&2, U32, acc)),
            N.le_trans(List.length(&2, U32, C.Wasm.encode.uleb(i)), 5n, 6n, len.u(i), Unit{}), ib.len(rest, acc))
        case C.Wasm.Instr.local_set{+i}:
          with.len(33, C.Wasm.encode.uleb(i), C.Wasm.encode.instrs(rest, acc), Nat.add(ib(rest), List.length(&2, U32, acc)),
            N.le_trans(List.length(&2, U32, C.Wasm.encode.uleb(i)), 5n, 6n, len.u(i), Unit{}), ib.len(rest, acc))
        case C.Wasm.Instr.local_tee{+i}:
          with.len(34, C.Wasm.encode.uleb(i), C.Wasm.encode.instrs(rest, acc), Nat.add(ib(rest), List.length(&2, U32, acc)),
            N.le_trans(List.length(&2, U32, C.Wasm.encode.uleb(i)), 5n, 6n, len.u(i), Unit{}), ib.len(rest, acc))
        case C.Wasm.Instr.op{o}:
          +X = Nat.add(ib(rest), List.length(&2, U32, acc))
          N.le_trans(1n+List.length(&2, U32, C.Wasm.encode.instrs(rest, acc)), 1n+X, 7n+X, ib.len(rest, acc), Z.le.add_r(1n, 7n, X, Unit{}))
        case C.Wasm.Instr.eqz{}:
          +X = Nat.add(ib(rest), List.length(&2, U32, acc))
          N.le_trans(1n+List.length(&2, U32, C.Wasm.encode.instrs(rest, acc)), 1n+X, 7n+X, ib.len(rest, acc), Z.le.add_r(1n, 7n, X, Unit{}))
        case C.Wasm.Instr.load{+o}:
          with.len(40, Con{2, C.Wasm.encode.uleb(o)}, C.Wasm.encode.instrs(rest, acc), Nat.add(ib(rest), List.length(&2, U32, acc)), len.u(o), ib.len(rest, acc))
        case C.Wasm.Instr.load8_u{+o}:
          with.len(45, Con{0, C.Wasm.encode.uleb(o)}, C.Wasm.encode.instrs(rest, acc), Nat.add(ib(rest), List.length(&2, U32, acc)), len.u(o), ib.len(rest, acc))
        case C.Wasm.Instr.store{+o}:
          with.len(54, Con{2, C.Wasm.encode.uleb(o)}, C.Wasm.encode.instrs(rest, acc), Nat.add(ib(rest), List.length(&2, U32, acc)), len.u(o), ib.len(rest, acc))
        case C.Wasm.Instr.store8{+o}:
          with.len(58, Con{0, C.Wasm.encode.uleb(o)}, C.Wasm.encode.instrs(rest, acc), Nat.add(ib(rest), List.length(&2, U32, acc)), len.u(o), ib.len(rest, acc))
        case C.Wasm.Instr.memory_size{}:
          +X = Nat.add(ib(rest), List.length(&2, U32, acc))
          N.le_trans(2n+List.length(&2, U32, C.Wasm.encode.instrs(rest, acc)), 2n+X, 7n+X, ib.len(rest, acc), Z.le.add_r(2n, 7n, X, Unit{}))
        case C.Wasm.Instr.memory_grow{}:
          +X = Nat.add(ib(rest), List.length(&2, U32, acc))
          N.le_trans(2n+List.length(&2, U32, C.Wasm.encode.instrs(rest, acc)), 2n+X, 7n+X, ib.len(rest, acc), Z.le.add_r(2n, 7n, X, Unit{}))
        case C.Wasm.Instr.block{+body}:
          +R = C.Wasm.encode.instrs(rest, acc)
          blk.as(2n+List.length(&2, U32, C.Wasm.encode.instrs(body, Con{11, R})), ib(body), ib(rest), List.length(&2, U32, acc),
            blk.len(body, R, Nat.add(ib(rest), List.length(&2, U32, acc)), ib.len(rest, acc), ib.len(body, Con{11, R})))
        case C.Wasm.Instr.loop{+body}:
          +R = C.Wasm.encode.instrs(rest, acc)
          blk.as(2n+List.length(&2, U32, C.Wasm.encode.instrs(body, Con{11, R})), ib(body), ib(rest), List.length(&2, U32, acc),
            blk.len(body, R, Nat.add(ib(rest), List.length(&2, U32, acc)), ib.len(rest, acc), ib.len(body, Con{11, R})))
        case C.Wasm.Instr.br{+l}:
          with.len(12, C.Wasm.encode.uleb(l), C.Wasm.encode.instrs(rest, acc), Nat.add(ib(rest), List.length(&2, U32, acc)),
            N.le_trans(List.length(&2, U32, C.Wasm.encode.uleb(l)), 5n, 6n, len.u(l), Unit{}), ib.len(rest, acc))
        case C.Wasm.Instr.br_if{+l}:
          with.len(13, C.Wasm.encode.uleb(l), C.Wasm.encode.instrs(rest, acc), Nat.add(ib(rest), List.length(&2, U32, acc)),
            N.le_trans(List.length(&2, U32, C.Wasm.encode.uleb(l)), 5n, 6n, len.u(l), Unit{}), ib.len(rest, acc))
        case C.Wasm.Instr.br_table{+ls, +l}:
          +R = C.Wasm.encode.instrs(rest, acc)
          +X = Nat.add(ib(rest), List.length(&2, U32, acc))
          +T0 = List.append(&2, U32, C.Wasm.encode.uleb(l), R)
          +hT0 = N.le_rw_l(Nat.add(List.length(&2, U32, C.Wasm.encode.uleb(l)), List.length(&2, U32, R)), List.length(&2, U32, T0), 5n+X,
            Equal.sym(Nat, List.length(&2, U32, T0), Nat.add(List.length(&2, U32, C.Wasm.encode.uleb(l)), List.length(&2, U32, R)), M.len.app(C.Wasm.encode.uleb(l), R)),
            N.add_mono(List.length(&2, U32, C.Wasm.encode.uleb(l)), 5n, List.length(&2, U32, R), X, len.u(l), ib.len(rest, acc)))
          +hall = with.len(14, C.Wasm.encode.uleb(C.Wasm.encode.len(U32, ls)), C.Wasm.encode.labels(ls, T0), Nat.add(ib.tab(ls), 5n+X),
            N.le_trans(List.length(&2, U32, C.Wasm.encode.uleb(C.Wasm.encode.len(U32, ls))), 5n, 6n, len.u(C.Wasm.encode.len(U32, ls)), Unit{}),
            labels.len(ls, T0, 5n+X, hT0))
          +Y = List.length(&2, U32, C.Wasm.encode.with(14, C.Wasm.encode.uleb(C.Wasm.encode.len(U32, ls)), C.Wasm.encode.labels(ls, T0)))
          tab.as(Y, ib.tab(ls), ib(rest), List.length(&2, U32, acc),
            N.le_rw_r(Y, 7n+Nat.add(5n, Nat.add(ib.tab(ls), X)), 12n+Nat.add(ib.tab(ls), X), {==},
              N.le_rw_r(Y, 7n+Nat.add(ib.tab(ls), 5n+X), 7n+Nat.add(5n, Nat.add(ib.tab(ls), X)),
                Equal.cong(Nat, Nat, z => 7n+z, Nat.add(ib.tab(ls), 5n+X), Nat.add(5n, Nat.add(ib.tab(ls), X)), shk(ib.tab(ls), 5n, X)), hall)))

# Bytes of the code of a program
# -------------------------------

# 512 n: the bound on the instruction bytes of n units of code
def L(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      512n+L(p)

def L.add(+a: Nat, +b: Nat) -> {L(Nat.add(a, b)) == Nat.add(L(a), L(b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 512n+z, L(Nat.add(p, b)), Nat.add(L(p), L(b)), L.add(p, b))

def L.mono(+a: Nat, +b: Nat, h: N.Le(a, b)) -> N.Le(L(a), L(b)):
  match a:
    case 0n:
      N.le_zero(L(b))
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(N.Le(512n+L(p), 0n), h)
        case 1n+q:
          L.mono(p, q, h)

# 2 × (512 x) = 512 (2 x)
def L.double(+x: Nat) -> {L(Nat.double(x)) == Nat.double(L(x)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, 1024n+L(Nat.double(p)), 1024n+Nat.double(L(p)), Nat.double(512n+L(p)),
        Equal.cong(Nat, Nat, z => 1024n+z, L(Nat.double(p)), Nat.double(L(p)), L.double(p)), {==})

def L.D(+k: Nat, +x: Nat) -> {L(N.D(k, x)) == N.D(k, L(x)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+q:
      Equal.trans(Nat, L(Nat.double(N.D(q, x))), Nat.double(L(N.D(q, x))), Nat.double(N.D(q, L(x))),
        L.double(N.D(q, x)),
        Equal.cong(Nat, Nat, z => Nat.double(z), L(N.D(q, x)), N.D(q, L(x)), L.D(q, x)))

# the bytes X, then Z: at most the bytes of n units more than Z
def B(X: Nat, n: Nat, Z: Nat) -> Data:
  N.Le(X, Nat.add(L(n), Z))

# Y, at most c more than Z, for c <= 512: one unit
def B.one(+c: Nat, +Y: Nat, +Z: Nat, h: N.Le(Y, Nat.add(c, Z)), hc: N.Le(c, 512n)) -> B(Y, 1n, Z):
  N.le_trans(Y, Nat.add(c, Z), Nat.add(512n, Z), h, Z.le.add_r(c, 512n, Z, hc))

# X before Y, Y before Z
def B.chain(+X: Nat, +Y: Nat, +a: Nat, +b: Nat, +Zv: Nat, h1: B(X, a, Y), h2: B(Y, b, Zv)) -> B(X, Nat.add(a, b), Zv):
  N.le_trans(X, Nat.add(L(a), Y), Nat.add(L(Nat.add(a, b)), Zv), h1,
    N.le_rw_r(Nat.add(L(a), Y), Nat.add(L(a), Nat.add(L(b), Zv)), Nat.add(L(Nat.add(a, b)), Zv),
      Equal.trans(Nat, Nat.add(L(a), Nat.add(L(b), Zv)), Nat.add(Nat.add(L(a), L(b)), Zv), Nat.add(L(Nat.add(a, b)), Zv),
        Equal.sym(Nat, Nat.add(Nat.add(L(a), L(b)), Zv), Nat.add(L(a), Nat.add(L(b), Zv)), Z.add.assoc(L(a), L(b), Zv)),
        Equal.cong(Nat, Nat, z => Nat.add(z, Zv), Nat.add(L(a), L(b)), L(Nat.add(a, b)), Equal.sym(Nat, L(Nat.add(a, b)), Nat.add(L(a), L(b)), L.add(a, b)))),
      N.add_mono(L(a), L(a), Y, Nat.add(L(b), Zv), N.le_refl(L(a)), h2)))

# a block of the body P, then Z: P is at most c, c <= 509, more than a units
def B.blk(+P: Nat, +a: Nat, +Zv: Nat, +c: Nat, h: B(P, a, c), hc: N.Le(c, 509n)) -> B(3n+Nat.add(P, Zv), Nat.add(a, 1n), Zv):
  +La = L(a)
  N.le_trans(3n+Nat.add(P, Zv), 3n+Nat.add(Nat.add(La, c), Zv), Nat.add(L(Nat.add(a, 1n)), Zv),
    Z.le.add_r(P, Nat.add(La, c), Zv, h),
    N.le_rw_l(Nat.add(La, Nat.add(3n+c, Zv)), 3n+Nat.add(Nat.add(La, c), Zv), Nat.add(L(Nat.add(a, 1n)), Zv),
      Equal.trans(Nat, Nat.add(La, Nat.add(3n, Nat.add(c, Zv))), Nat.add(3n, Nat.add(La, Nat.add(c, Zv))), 3n+Nat.add(Nat.add(La, c), Zv),
        shk(La, 3n, Nat.add(c, Zv)),
        Equal.cong(Nat, Nat, z => 3n+z, Nat.add(La, Nat.add(c, Zv)), Nat.add(Nat.add(La, c), Zv),
          Equal.sym(Nat, Nat.add(Nat.add(La, c), Zv), Nat.add(La, Nat.add(c, Zv)), Z.add.assoc(La, c, Zv)))),
      N.le_rw_r(Nat.add(La, Nat.add(3n+c, Zv)), Nat.add(La, Nat.add(512n, Zv)), Nat.add(L(Nat.add(a, 1n)), Zv),
        Equal.trans(Nat, Nat.add(La, Nat.add(512n, Zv)), Nat.add(Nat.add(La, L(1n)), Zv), Nat.add(L(Nat.add(a, 1n)), Zv),
          Equal.sym(Nat, Nat.add(Nat.add(La, L(1n)), Zv), Nat.add(La, Nat.add(L(1n), Zv)), Z.add.assoc(La, L(1n), Zv)),
          Equal.cong(Nat, Nat, z => Nat.add(z, Zv), Nat.add(La, L(1n)), L(Nat.add(a, 1n)), Equal.sym(Nat, L(Nat.add(a, 1n)), Nat.add(La, L(1n)), L.add(a, 1n)))),
        N.add_mono(La, La, Nat.add(3n+c, Zv), Nat.add(512n, Zv), N.le_refl(La), Z.le.add_r(3n+c, 512n, Zv, hc)))))

def B.refl(+Y: Nat) -> B(Y, 0n, Y):
  N.le_refl(Y)

# the code of an expression, then acc
def cb.expr(e: C.Cir.Expr, +acc: List<&2, C.Wasm.Instr>) -> B(ib(C.Cir.code.expr(e, acc)), NE(e), ib(acc)):
  match e:
    case C.Cir.Expr.const{+n}:
      B.one(7n, 7n+ib(acc), ib(acc), N.le_refl(7n+ib(acc)), Unit{})
    case C.Cir.Expr.get{+r}:
      B.one(7n, 7n+ib(acc), ib(acc), N.le_refl(7n+ib(acc)), Unit{})
    case C.Cir.Expr.op{+o, +a, +b}:
      +Ab = C.Cir.code.expr(b, Con{C.Cir.i.op(o), acc})
      B.chain(ib(C.Cir.code.expr(a, Ab)), ib(Ab), NE(a), Nat.add(NE(b), 1n), ib(acc), cb.expr(a, Ab),
        B.chain(ib(Ab), 7n+ib(acc), NE(b), 1n, ib(acc), cb.expr(b, Con{C.Cir.i.op(o), acc}),
          B.one(7n, 7n+ib(acc), ib(acc), N.le_refl(7n+ib(acc)), Unit{})))
    case C.Cir.Expr.eqz{+a}:
      B.chain(ib(C.Cir.code.expr(a, Con{C.Wasm.Instr.eqz{}, acc})), 7n+ib(acc), NE(a), 1n, ib(acc), cb.expr(a, Con{C.Wasm.Instr.eqz{}, acc}),
        B.one(7n, 7n+ib(acc), ib(acc), N.le_refl(7n+ib(acc)), Unit{}))
    case C.Cir.Expr.field{+k, +c}:
      +Ac = C.Cir.code.at(Con{C.Wasm.Instr.load{U32.shln(U32.from_nat(k), 2n)}, acc})
      B.chain(ib(C.Cir.code.expr(c, Ac)), 56n+ib(acc), NE(c), 1n, ib(acc), cb.expr(c, Ac),
        B.one(56n, 56n+ib(acc), ib(acc), N.le_refl(56n+ib(acc)), Unit{}))
    case C.Cir.Expr.byte{+i}:
      +Ab = {Con{C.Cir.i.get(0), Con{C.Cir.i.op(C.Wasm.Op.add{}), Con{C.Wasm.Instr.load8_u{0},
        Con{C.Cir.i.const(255), Con{C.Cir.i.op(C.Wasm.Op.and{}), acc}}}}} : List<&2, C.Wasm.Instr>}
      B.chain(ib(C.Cir.code.expr(i, Ab)), 35n+ib(acc), NE(i), 1n, ib(acc), cb.expr(i, Ab),
        B.one(35n, 35n+ib(acc), ib(acc), N.le_refl(35n+ib(acc)), Unit{}))
    case C.Cir.Expr.size{}:
      B.one(7n, 7n+ib(acc), ib(acc), N.le_refl(7n+ib(acc)), Unit{})

# the bytes of a halt's result and branch
def cb.res(b: Bool, +q: U32) -> N.Le(ib(List.append(&2, C.Wasm.Instr, C.Cir.code.result(b), [C.Wasm.Instr.br{q}])), 98n):
  match b:
    case True{}:
      Unit{}
    case False{}:
      Unit{}

# the code of a statement at d levels inside run's block, then acc
def cb.stmt(s: C.Cir.Stmt, +d: Nat, +acc: List<&2, C.Wasm.Instr>) -> B(ib(C.Cir.code.stmt(s, d, acc)), NS(s), ib(acc)):
  match s:
    case C.Cir.Stmt.nop{}:
      B.refl(ib(acc))
    case C.Cir.Stmt.set{+r, +e}:
      +Ae = {Con{C.Cir.i.set(C.Cir.l.reg(r)), acc} : List<&2, C.Wasm.Instr>}
      B.chain(ib(C.Cir.code.expr(e, Ae)), 7n+ib(acc), NE(e), 1n, ib(acc), cb.expr(e, Ae),
        B.one(7n, 7n+ib(acc), ib(acc), N.le_refl(7n+ib(acc)), Unit{}))
    case C.Cir.Stmt.store{+k, +c, +v}:
      +Av = {Con{C.Wasm.Instr.store{U32.shln(U32.from_nat(k), 2n)}, acc} : List<&2, C.Wasm.Instr>}
      +Ev = C.Cir.code.expr(v, Av)
      +Ac = C.Cir.code.at(Ev)
      B.chain(ib(C.Cir.code.expr(c, Ac)), ib(Ac), NE(c), Nat.add(1n, Nat.add(NE(v), 1n)), ib(acc), cb.expr(c, Ac),
        B.chain(ib(Ac), ib(Ev), 1n, Nat.add(NE(v), 1n), ib(acc), B.one(49n, ib(Ac), ib(Ev), N.le_refl(49n+ib(Ev)), Unit{}),
          B.chain(ib(Ev), 7n+ib(acc), NE(v), 1n, ib(acc), cb.expr(v, Av),
            B.one(7n, 7n+ib(acc), ib(acc), N.le_refl(7n+ib(acc)), Unit{}))))
    case C.Cir.Stmt.alloc{+r}:
      B.one(477n, ib(C.Cir.code.alloc(C.Cir.l.reg(r), d, acc)), ib(acc), N.le_refl(477n+ib(acc)), Unit{})
    case C.Cir.Stmt.emit{+v}:
      +Av = {Con{C.Wasm.Instr.store8{0}, Con{C.Cir.i.get(C.Cir.l.outn()), Con{C.Cir.i.const(1), Con{C.Cir.i.op(C.Wasm.Op.add{}),
        Con{C.Cir.i.set(C.Cir.l.outn()), acc}}}}} : List<&2, C.Wasm.Instr>}
      +Ev = C.Cir.code.expr(v, Av)
      B.chain(ib(C.Cir.code.emit(v, d, acc)), ib(Ev), 1n, Nat.add(NE(v), 1n), ib(acc),
        B.one(316n, ib(C.Cir.code.emit(v, d, acc)), ib(Ev), N.le_refl(316n+ib(Ev)), Unit{}),
        B.chain(ib(Ev), 35n+ib(acc), NE(v), 1n, ib(acc), cb.expr(v, Av),
          B.one(35n, 35n+ib(acc), ib(acc), N.le_refl(35n+ib(acc)), Unit{})))
    case C.Cir.Stmt.seq{+a, +b}:
      +Sb = C.Cir.code.stmt(b, d, acc)
      B.chain(ib(C.Cir.code.stmt(a, d, Sb)), ib(Sb), NS(a), NS(b), ib(acc), cb.stmt(a, d, Sb), cb.stmt(b, d, acc))
    case C.Cir.Stmt.if{+c, +t, +e}:
      +St = C.Cir.code.stmt(t, 2n+d, [C.Wasm.Instr.br{1}])
      +Ae = {Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{0}, St}} : List<&2, C.Wasm.Instr>}
      +B1 = C.Cir.code.expr(c, Ae)
      +Se = C.Cir.code.stmt(e, 1n+d, [])
      +n1 = Nat.add(NE(c), Nat.add(1n, NS(t)))
      +h1 = B.chain(ib(B1), ib(Ae), NE(c), Nat.add(1n, NS(t)), 7n, cb.expr(c, Ae),
        B.chain(ib(Ae), ib(St), 1n, NS(t), 7n, B.one(14n, ib(Ae), ib(St), N.le_refl(14n+ib(St)), Unit{}),
          cb.stmt(t, 2n+d, [C.Wasm.Instr.br{1}])))
      +h2 = B.blk(ib(B1), n1, ib(Se), 7n, h1, Unit{})
      +h3 = B.chain(3n+Nat.add(ib(B1), ib(Se)), ib(Se), Nat.add(n1, 1n), NS(e), 0n, h2, cb.stmt(e, 1n+d, []))
      B.blk(3n+Nat.add(ib(B1), ib(Se)), Nat.add(Nat.add(n1, 1n), NS(e)), ib(acc), 0n, h3, Unit{})
    case C.Cir.Stmt.while{+c, +body}:
      +Sb = C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])
      +Ae = {Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, Sb}} : List<&2, C.Wasm.Instr>}
      +B1 = C.Cir.code.expr(c, Ae)
      +n1 = Nat.add(NE(c), Nat.add(1n, NS(body)))
      +h1 = B.chain(ib(B1), ib(Ae), NE(c), Nat.add(1n, NS(body)), 7n, cb.expr(c, Ae),
        B.chain(ib(Ae), ib(Sb), 1n, NS(body), 7n, B.one(14n, ib(Ae), ib(Sb), N.le_refl(14n+ib(Sb)), Unit{}),
          cb.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])))
      +h2 = B.blk(ib(B1), n1, 0n, 7n, h1, Unit{})
      B.blk(3n+Nat.add(ib(B1), 0n), Nat.add(n1, 1n), ib(acc), 0n, h2, Unit{})
    case C.Cir.Stmt.halt{+v}:
      +R = ib(List.append(&2, C.Wasm.Instr, C.Cir.code.result(U32.is_zero(v)), [C.Wasm.Instr.br{U32.from_nat(1n+d)}]))
      B.one(115n, 17n+Nat.add(R, ib(acc)), ib(acc), Z.le.add_r(R, 98n, ib(acc), cb.res(U32.is_zero(v), U32.from_nat(1n+d))), Unit{})

def mach.nodes() -> N.Le(NS(C.Mach.code()), N.D(16n, 1n)):
  Unit{}
