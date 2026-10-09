# perf (main-imports-perf): main.bend imports PERF.bend. main never
# names PERF.bend, so the run refuses it.
import Base

def zero() -> Nat:
  0n
