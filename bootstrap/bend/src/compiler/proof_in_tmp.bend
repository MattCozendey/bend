import Base
import ./impl.bend as C
import ./proof_need.bend as N
import ./proof_halt.bend as PH

def t1() -> {N.D(32n, 1n) == PH.H.W(32n) : Nat}:
  {==}
