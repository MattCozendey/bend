# the first byte, after a rewrite that runs as code: Rwt evaluates its proof
import Base

def two() -> {Nat.add(1n, 1n) == 2n : Nat}:
  {==}

def first(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, _}:
      [{x : U32}]

def main(i: List<&2, U32>) -> List<&2, U32>:
  %two() : List<&2, U32>
  first(i)
