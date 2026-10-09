# perf (perf-no-import): a PERF.bend that does not import ./main.bend
# names no main function, so the run refuses it.
import Base

def zero() -> Nat:
  0n
