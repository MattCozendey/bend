# perf (producer-type): the route takes +xs where via takes xs: each of a
# producer route's parameters has the type and mode of the slot it fills.
import Base
import ./main.bend as M

def dbl_via(+xs: List<&2, Nat>) -> List<&2, Nat>:
  M.dbl(M.dbl(xs))

law dbl.via:
  for +xs: List<&2, Nat>
  {M.dbl(M.via(xs)) == dbl_via(xs) : List<&2, Nat>}

def dbl.via(xs):
  {==}
