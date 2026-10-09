# perf (producer-route): main calls show on via's list; a producer rule
# switches that call, with via's list, to a route that never builds it.
import Base
import ./main.bend as M

def show_via(xs: List<&2, Nat>) -> IO(Unit):
  IO.print(Nat.show(List.length(&2, Nat, M.dbl(M.dbl(xs)))))

law show.via:
  for +xs: List<&2, Nat>
  {M.show(M.via(xs)) == show_via(xs) : IO(Unit)}

def show.via(xs):
  {==}
