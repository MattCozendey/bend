# perf (pow2-every-call): the route calls pow2 once, on the predecessor its
# match took apart, so the loop pow2 -> route -> pow2 shrinks n each trip:
# pow2's own two calls switch to the route too, and 2^n takes n steps.
import Base
import ./main.bend as M

def pow2_fast(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n+p:
      +h = M.pow2(p)
      Nat.add(h, h)

law pow2.fast:
  for +n: Nat
  {M.pow2(n) == pow2_fast(n) : Nat}

def pow2.fast(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}
