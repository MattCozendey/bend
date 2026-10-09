# perf (io-extra-print): an IO route that prints one more line is not
# equal to show: its proof fails.
import Base
import ./main.bend as M

def show_fast(xs: List<&2, Nat>) -> IO(Unit):
  IO.bind(Unit, Unit, IO.print("extra"), _ => M.show(xs))

law show.fast:
  for +xs: List<&2, Nat>
  {M.show(xs) == show_fast(xs) : IO(Unit)}

def show.fast(xs):
  {==}
