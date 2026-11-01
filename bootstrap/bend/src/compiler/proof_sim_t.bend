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

def probe1(+rr: U32, +d: Nat, +acc: List<&2, C.Wasm.Instr>) -> {ib(C.Cir.code.alloc(rr, d, acc)) == ib(acc) : Nat}:
  ?TODO

def probe2(+v: C.Cir.Expr, +d: Nat, +acc: List<&2, C.Wasm.Instr>) -> {ib(C.Cir.code.emit(v, d, acc)) == ib(acc) : Nat}:
  ?TODO

def probe3(+prog: C.Cir.Stmt, +regs: Nat, +k: U32) -> {ib(M.body(C.Cir.run(prog, regs, k))) == ib(C.Cir.code.stmt(prog, 0n, [])) : Nat}:
  ?TODO

def probe4(+k: U32) -> {ib(M.body(C.Cir.alloc(k))) == 0n : Nat}:
  {==}

def probe5(+s: U32, +d: Nat, +acc: List<&2, C.Wasm.Instr>) -> {ib(Con{C.Cir.code.halt(s, d), acc}) == ib(acc) : Nat}:
  ?TODO

def probe6(+d: Nat) -> {ib(C.Cir.code.at([])) == ib([]) : Nat}:
  ?TODO
