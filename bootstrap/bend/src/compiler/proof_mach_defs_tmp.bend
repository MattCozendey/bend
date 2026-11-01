import Base
import ./proof_mach_defs.bend as PM

def tst2(+h: @c: U32 -> {U32.is_eq(c, c) == True{} : Bool}) -> PM.P2({U32.is_eq(1, 1) == True{} : Bool}, {U32.is_eq(2, 2) == True{} : Bool}):
  (h(1), h(2))
