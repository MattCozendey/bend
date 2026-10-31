# the number of bytes, in decimal: Nat.show divides a unary Nat by 10, and binds
# its rest at quantity 2 at each step
import Base

def bytes(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, rest}:
      Con{c, bytes(rest)}

def main(i: List<&2, U32>) -> List<&2, U32>:
  bytes(Nat.show(List.length(&2, U32, i)))
