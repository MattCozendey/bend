import Base
import ./impl.bend as C
import ./proof_mach.bend as PM
import ./proof_copy_cx.bend as X

def T.cnt() -> {PM.Cnt(2n, X.A.m(), 400, 2n, 400, [400], Nil{}) == True{} : Bool}:
  {==}
