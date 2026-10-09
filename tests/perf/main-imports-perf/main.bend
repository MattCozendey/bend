import Base
import ./PERF.bend as P

def dbl(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case +h <> t:
      h <> h <> dbl(t)

# calls dbl on its own input
def via(xs: List<&2, Nat>) -> List<&2, Nat>:
  dbl(xs)

def show(xs: List<&2, Nat>) -> IO(Unit):
  IO.print(Nat.show(List.length(&2, Nat, dbl(xs))))

def main() -> IO(Unit):
  show(via([1n, 2n]))

#|SOME PROOFS FAIL
#|Error: main.bend must not import PERF.bend
