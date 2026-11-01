import Base
import ./impl.bend as C
import ./proof_need.bend as N

def t1(+x: U32, +o: U32, +w: U32, +Sm: Nat, eE: {U32.to_nat(U32.add(U32.add(x, o), w)) == Sm : Nat}, h: N.Le(1n, Sm)) -> N.Le(1n, U32.to_nat(U32.add(U32.add(x, o), w))):
  N.le_rw_r(1n, Sm, U32.to_nat(U32.add(U32.add(x, o), w)), Equal.sym(Nat, U32.to_nat(U32.add(U32.add(x, o), w)), Sm, eE), h)
