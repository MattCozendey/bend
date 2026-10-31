# each byte plus 3: a def applied to 2 of its 3 arguments
import Base

def add3(a: U32, b: U32, c: U32) -> U32:
  U32.and(U32.add(a, U32.add(b, c)), 255)

def apply(~f: U32 -> U32, xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      Con{f(x), apply(~f, rest)}

def main(i: List<&2, U32>) -> List<&2, U32>:
  apply(~add3(1, 2), i)
