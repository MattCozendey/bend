import Base

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
#|Error:
#|- expected : IO.print(Nat.show.fin(List.length(&2, Nat, dbl(xs)), "", Nat.show.put(Nat.divmod.go(List.length(&2, Nat, dbl(xs)), 9n, 0n, 0n))))
#|- observed : R => k => IO.print("extra", R, x => IO.print(Nat.show.fin(List.length(&2, Nat, dbl(xs)), "", Nat.show.put(Nat.divmod.go(List.length(&2, Nat, dbl(xs)), 9n, 0n, 0n))), R, k))
#|Context:
#|- xs : List<&2, Nat>
#|Location: show.fast
#|13 | def show.fast(xs):
#|14>|   {==}
#|   |   ^^^^
#|15 |
