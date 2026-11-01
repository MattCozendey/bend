import Base
import ./impl.bend as C

def sel.e(x: C.Cir.Stmt) -> C.Cir.Stmt:
  match x:
    case C.Cir.Stmt.if{_, _, e}:
      e
    case _:
      C.Cir.Stmt.nop{}

def sel.a(x: C.Cir.Stmt) -> C.Cir.Stmt:
  match x:
    case C.Cir.Stmt.seq{a, _}:
      a
    case _:
      C.Cir.Stmt.nop{}

def sel.b(x: C.Cir.Stmt) -> C.Cir.Stmt:
  match x:
    case C.Cir.Stmt.seq{_, b}:
      b
    case _:
      C.Cir.Stmt.nop{}

def X.chain(i: Nat) -> C.Cir.Stmt:
  match i:
    case 0n:
      sel.a(sel.b(sel.b(sel.b(sel.e(C.M.ret())))))
    case 1n+j:
      sel.e(X.chain(j))

def t1() -> {X.chain(0n) == sel.a(sel.b(sel.b(sel.b(sel.e(C.M.ret()))))) : C.Cir.Stmt}:
  {==}

def t2() -> {C.Cir.Stmt.seq{X.chain(0n), C.Cir.Stmt.nop{}} == sel.b(sel.b(sel.b(sel.e(C.M.ret())))) : C.Cir.Stmt}:
  {==}
