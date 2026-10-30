import Base

def sum(xs: List<Nat>, acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      sum(t, (acc + U32.from_nat(h) : U32))

def main(xs: List<Nat>) -> Nat:
  U32.to_nat(sum(xs, 0))
