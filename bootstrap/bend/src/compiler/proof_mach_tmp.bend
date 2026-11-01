import Base
import ./impl.bend as C

def t1(+f: Nat, +st: C.Cir.State) -> {C.Cir.exec(f, C.Cir.Stmt.nop{}, st) == C.Cir.Out.next{st} : C.Cir.Out}:
  {==}
