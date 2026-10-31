# each byte plus 1: U32 arithmetic, bit by bit
import Base

def incs(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      Con{U32.and(U32.add(x, 1), 255), incs(rest)}

def main(i: List<&2, U32>) -> List<&2, U32>:
  incs(i)
