import Base

# 2^n, the slow way: two calls on n - 1
def pow2(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n++p:
      Nat.add(pow2(p), pow2(p))

# n itself, through a call
def same(n: Nat) -> Nat:
  n

def main() -> IO(Unit):
  IO.print(Nat.show(pow2(16n)))

#|65536
#?ALL PROOFS CHECK
#?Use --verdict for mathematical validity.
#?PERF routes:
#?- pow2 -> PERF.pow2_same (top call)
