import Base
import ./impl.bend as C
import ./proof_sim_step.bend as S

def mk(+a: Nat) -> S.EX(j => {j == a : Nat}):
  (a, {==})

def use2(+a: Nat) -> S.EX(j => {j == a : Nat}):
  (+j, e) = mk(a)
  (j, e)
