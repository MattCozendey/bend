# the number of bytes, in decimal, by a recursion that is not a tail call: its
# frames grow with the input
import Base

def bytes(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, rest}:
      Con{c, bytes(rest)}

def len(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{_, rest}:
      1n+len(rest)

def main(i: List<&2, U32>) -> List<&2, U32>:
  bytes(Nat.show(len(i)))
