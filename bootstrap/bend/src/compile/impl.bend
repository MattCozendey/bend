import Base
import ./spec.bend as Spec
import ../source/impl.bend as Source

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

law Nat.cmp_self:
  for a: Nat
  {Nat.cmp(a, a) == EQ{} : Cmp}

def Nat.cmp_self(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.cmp_self(p)

law Nat.is_eq_self:
  for a: Nat
  {Nat.is_eq(a, a) == True{} : Bool}

def Nat.is_eq_self(a):
  %Equal.sym(Cmp, Nat.cmp(a, a), EQ{}, Nat.cmp_self(a)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

law Name.is_eq_self:
  for a: List<&2, Nat>
  {Source.Name.is_eq(a, a) == True{} : Bool}

def Name.is_eq_self(a):
  match a:
    case Nil{}:
      {==}
    case Con{x, xs}:
      %Equal.sym(Bool, Nat.is_eq(x, x), True{}, Nat.is_eq_self(x)) :
        {Bool.and(_, Source.Name.is_eq(xs, xs)) == True{} : Bool}
      Name.is_eq_self(xs)

law Obs.is_eq_self:
  for a: Source.Obs
  {Source.Obs.is_eq(a, a) == True{} : Bool}

def Obs.is_eq_self(a):
  match a:
    case Source.Obs.lab{k}:
      Name.is_eq_self(k)
    case Source.Obs.rfl{}:
      {==}
    case Source.Obs.tup{a1, a2}:
      %Equal.sym(Bool, Source.Obs.is_eq(a1, a1), True{}, Obs.is_eq_self(a1)) :
        {Bool.and(_, Source.Obs.is_eq(a2, a2)) == True{} : Bool}
      Obs.is_eq_self(a2)
    case Source.Obs.tup0{a2}:
      Obs.is_eq_self(a2)

law Obs.is_kept_self:
  for a: Maybe<&2, Source.Obs>
  {Source.Obs.is_kept(a, a) == True{} : Bool}

def Obs.is_kept_self(a):
  match a:
    case None{}:
      {==}
    case Some{x}:
      Obs.is_eq_self(x)

def Spec.keeps_results(src, input, n):
  Obs.is_kept_self(Source.run(n, src, input))

def Spec.adds_no_results(src, input, n):
  Obs.is_kept_self(Source.run(n, src, input))
