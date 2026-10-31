import Base
import ./impl.bend as C

def c0() -> C.Cir.Cell:
  C.Cir.Cell{1, 2, 3, 4, 5}

def p1() -> C.Cir.Stmt:
  C.Cir.Stmt.halt{0}

def p2() -> C.Cir.Stmt:
  C.Cir.Stmt.seq{C.Cir.Stmt.set{0n, C.Cir.Expr.const{7}},
    C.Cir.Stmt.seq{C.Cir.Stmt.alloc{1n},
      C.Cir.Stmt.seq{C.Cir.Stmt.store{2n, C.Cir.Expr.get{1n}, C.Cir.Expr.field{4n, C.Cir.Expr.get{1n}}},
        C.Cir.Stmt.emit{C.Cir.Expr.op{C.Wasm.Op.add{}, C.Cir.Expr.get{0n}, C.Cir.Expr.byte{C.Cir.Expr.size{}}}}}}}

def p3() -> C.Cir.Stmt:
  C.Cir.Stmt.while{C.Cir.Expr.get{2n},
    C.Cir.Stmt.if{C.Cir.Expr.eqz{C.Cir.Expr.get{0n}}, C.Cir.Stmt.halt{2}, C.Cir.Stmt.set{2n, C.Cir.Expr.const{0}}}}

def p4() -> C.Cir.Stmt:
  C.Cir.Stmt.set{3n, C.Cir.Expr.const{0}}

def main() -> List<Bool>:
  [C.Wasm.valid.module(C.Cir.module(p1(), 3n, [c0(), c0()])),
   C.Wasm.valid.module(C.Cir.module(p2(), 3n, [c0(), c0()])),
   C.Wasm.valid.module(C.Cir.module(p3(), 3n, [c0(), c0()])),
   C.Wasm.valid.module(C.Cir.module(p4(), 3n, [c0(), c0()]))]
