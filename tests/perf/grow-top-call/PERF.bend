# perf (grow-top-call): the route calls pow2 on same(n), which is n but
# not a part of n as the compiler reads it, so pow2's own calls keep to
# pow2: the route takes the top call only.
import Base
import ./main.bend as M

def pow2_same(n: Nat) -> Nat:
  M.pow2(M.same(n))

law pow2.same:
  for +n: Nat
  {M.pow2(n) == pow2_same(n) : Nat}

def pow2.same(n):
  {==}
