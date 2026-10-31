# each byte plus 3: a closure that holds the 3
import Base

def adds(~f: U32 -> U32, xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      Con{f(x), adds(~f, rest)}

def adder(n: U32) -> U32 -> U32:
  x => U32.and(U32.add(x, n), 255)

def main(i: List<&2, U32>) -> List<&2, U32>:
  adds(~adder(3), i)
