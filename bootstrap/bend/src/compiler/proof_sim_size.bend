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

# the nodes of an expression and of a statement
def NE(e: C.Cir.Expr) -> Nat:
  match e:
    case C.Cir.Expr.const{_}:
      1n
    case C.Cir.Expr.get{_}:
      1n
    case C.Cir.Expr.op{_, a, b}:
      1n+Nat.add(NE(a), NE(b))
    case C.Cir.Expr.eqz{a}:
      1n+NE(a)
    case C.Cir.Expr.field{_, c}:
      1n+NE(c)
    case C.Cir.Expr.byte{i}:
      1n+NE(i)
    case C.Cir.Expr.size{}:
      1n

def NS(s: C.Cir.Stmt) -> Nat:
  match s:
    case C.Cir.Stmt.nop{}:
      1n
    case C.Cir.Stmt.set{_, e}:
      1n+NE(e)
    case C.Cir.Stmt.store{_, c, v}:
      1n+Nat.add(NE(c), NE(v))
    case C.Cir.Stmt.alloc{_}:
      1n
    case C.Cir.Stmt.emit{v}:
      1n+NE(v)
    case C.Cir.Stmt.seq{a, b}:
      1n+Nat.add(NS(a), NS(b))
    case C.Cir.Stmt.if{c, t, e}:
      1n+Nat.add(NE(c), Nat.add(NS(t), NS(e)))
    case C.Cir.Stmt.while{c, body}:
      1n+Nat.add(NE(c), NS(body))
    case C.Cir.Stmt.halt{_}:
      1n

# a bound on the bytes of the instructions xs: 7 for each, 3 more than its
# body for a block or loop, 11 more than 5 per label for a br_table
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
          11n+Nat.add(ib.tab(ls), ib(rest))
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
    N.le_rw_l(2n+Nat.add(ib(body), 1n+List.length(&2, U32, R)), 3n+Nat.add(ib(body), List.length(&2, U32, R)), 3n+Nat.add(ib(body), X),
      Equal.cong(Nat, Nat, z => 2n+z, Nat.add(ib(body), 1n+List.length(&2, U32, R)), 1n+Nat.add(ib(body), List.length(&2, U32, R)), N.add_succ_r(ib(body), List.length(&2, U32, R))),
      N.add_mono(ib(body), ib(body), List.length(&2, U32, R), X, N.le_refl(ib(body)), ih)))

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
          blk.len(body, R, Nat.add(ib(rest), List.length(&2, U32, acc)), ib.len(rest, acc), ib.len(body, Con{11, R}))
        case C.Wasm.Instr.loop{+body}:
          +R = C.Wasm.encode.instrs(rest, acc)
          blk.len(body, R, Nat.add(ib(rest), List.length(&2, U32, acc)), ib.len(rest, acc), ib.len(body, Con{11, R}))
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
          N.le_rw_r(7n+Nat.add(ib.tab(ls), 5n+X), 7n+Nat.add(5n, Nat.add(ib.tab(ls), X)), 11n+Nat.add(ib.tab(ls), X), {==},
            N.le_rw_r(7n+Nat.add(ib.tab(ls), 5n+X), 7n+Nat.add(ib.tab(ls), 5n+X), 7n+Nat.add(5n, Nat.add(ib.tab(ls), X)),
              Equal.cong(Nat, Nat, z => 7n+z, Nat.add(ib.tab(ls), 5n+X), Nat.add(5n, Nat.add(ib.tab(ls), X)), shk(ib.tab(ls), 5n, X)), hall))

def mach.nodes() -> N.Le(NS(C.Mach.code()), N.D(16n, 1n)):
  Unit{}
