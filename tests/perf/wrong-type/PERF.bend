# perf (wrong-type): the route's parameter is +, dbl's is not: a route
# has exactly its function's type.
import Base
import ./main.bend as M

def dbl_fast(+xs: List<&2, Nat>) -> List<&2, Nat>:
  M.dbl(xs)

law dbl.fast:
  for +xs: List<&2, Nat>
  {M.dbl(xs) == dbl_fast(xs) : List<&2, Nat>}

def dbl.fast(xs):
  {==}
