# erased and Data parameters, and a list used twice
import Base

def keep(-n: Nat, +x: U32, y: U32) -> U32:
  U32.and(U32.add(x, U32.add(x, y)), 255)

def twice(+xs: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, xs, xs)

def go(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, rest}:
      Con{keep(5n, x, 1), go(rest)}

def main(+i: List<&2, U32>) -> List<&2, U32>:
  twice(go(i))
