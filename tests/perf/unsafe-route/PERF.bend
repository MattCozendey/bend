# perf (unsafe-route): a route that relies on @unsafe code proves
# nothing, so a run refuses it.
import Base
import ./main.bend as M

@unsafe
def dbl_fast(xs: List<&2, Nat>) -> List<&2, Nat>:
  M.dbl(xs)

law dbl.fast:
  for +xs: List<&2, Nat>
  {M.dbl(xs) == dbl_fast(xs) : List<&2, Nat>}

def dbl.fast(xs):
  {==}
