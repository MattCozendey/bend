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

def mach.nodes() -> N.Le(NS(C.Mach.code()), N.D(16n, 1n)):
  Unit{}
