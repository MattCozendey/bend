# perf (two-routes): two routes for dbl. A function takes one route;
# several shapes go in that route's match.
import Base
import ./main.bend as M

def dbl_a(xs: List<&2, Nat>) -> List<&2, Nat>:
  M.dbl(xs)

def dbl_b(xs: List<&2, Nat>) -> List<&2, Nat>:
  M.dbl(xs)

law dbl.a:
  for +xs: List<&2, Nat>
  {M.dbl(xs) == dbl_a(xs) : List<&2, Nat>}

def dbl.a(xs):
  {==}

law dbl.b:
  for +xs: List<&2, Nat>
  {M.dbl(xs) == dbl_b(xs) : List<&2, Nat>}

def dbl.b(xs):
  {==}
