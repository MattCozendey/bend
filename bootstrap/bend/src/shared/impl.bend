import Base

# Shared
# ======
#
# Small helpers of the proofs of more than one module.

def Bool.disc(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def Bool.no(h: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, h) : Bool.disc(_)
  Unit{}

# anything, from False == True
def Bool.absurd(-A: Type, h: {False{} == True{} : Bool}) -> A:
  Empty.absurd(A, Bool.no(h))

def Maybe.no_none(-A: Data, -a: A, e: {None{} == Some{a} : Maybe<&2, A>}) -> Empty:
  Bool.no(Equal.cong(Maybe<&2, A>, Bool, m => Maybe.is_some(&2, A, m), None{}, Some{a}, e))
