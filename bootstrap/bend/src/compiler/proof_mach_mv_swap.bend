# compiler: layer B, the swap moves
# =================================

import Base
import ./impl.bend as C
import ./proof_need.bend as N
import ./proof_mach_defs.bend as D
import ./proof_mach_exec.bend as X

def sw.dummy() -> {1n == 1n : Nat}:
  {==}
