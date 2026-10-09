# perf (via-halts): the route reaches dbl through main's via, which calls
# dbl on the same input. Code a route reaches keeps its own calls, so via
# runs the dbl main wrote and the run halts.
import Base
import ./main.bend as M

def dbl_fast(xs: List<&2, Nat>) -> List<&2, Nat>:
  M.via(xs)

law dbl.fast:
  for +xs: List<&2, Nat>
  {M.dbl(xs) == dbl_fast(xs) : List<&2, Nat>}

def dbl.fast(xs):
  {==}
