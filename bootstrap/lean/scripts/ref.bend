import Base

def main() -> (U32 & U32 & U32 & U32 & U32 & U32 & U32 & U32 & U32 & U32 & Cmp & Nat):
  (U32.inc(7), U32.not(7), U32.and(12, 10), U32.or(12, 10), U32.xor(12, 10),
   U32.shl(7), U32.shr(7), U32.mul(6, 7), U32.add(1, 2), U32.sub(9, 4),
   U32.cmp(3, 5), U32.to_nat(U32.from_nat(9n)))
