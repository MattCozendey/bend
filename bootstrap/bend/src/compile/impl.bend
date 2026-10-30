import Base
import ./spec.bend as Spec
import ../source/impl.bend as Source
import ../source/proof.bend as Proof

# Compile
# =======
#
# The compiler: it passes the source through, as the interpreter's compile
# does. The laws of spec.bend then hold at the same fuel.

def Spec.compile(src):
  src

def Spec.fuel_out(src, input, n):
  n

def Spec.fuel_src(src, input, n):
  n

# Proofs
# ======

def Obs.is_eq_self(a: Source.Obs) -> {Source.Obs.is_eq(a, a) == True{} : Bool}:
  match a:
    case Source.Obs.lab{k}:
      Proof.Name.is_eq_self(k)
    case Source.Obs.rfl{}:
      {==}
    case Source.Obs.tup{a1, a2}:
      %Equal.sym(Bool, Source.Obs.is_eq(a1, a1), True{}, Obs.is_eq_self(a1)) :
        {Bool.and(_, Source.Obs.is_eq(a2, a2)) == True{} : Bool}
      Obs.is_eq_self(a2)
    case Source.Obs.tup0{a2}:
      Obs.is_eq_self(a2)

def Obs.is_kept_self(a: Maybe<&2, Source.Obs>) -> {Source.Obs.is_kept(a, a) == True{} : Bool}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      Obs.is_eq_self(x)

def Spec.keeps_results(src, input, n):
  Obs.is_kept_self(Source.run(n, src, input))

def Spec.adds_no_results(src, input, n):
  Obs.is_kept_self(Source.run(n, src, input))
