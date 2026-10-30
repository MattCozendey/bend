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

# Cases
# =====

def Maybe.elim(-A: Data, m: Maybe<&2, A>, -P: Maybe<&2, A> -> Type, s: @x:A -> P(Some{x}),
  n: P(None{})) -> P(m):
  match m:
    case Some{x}:
      s(x)
    case None{}:
      n

def Bool.elim(c: Bool, -P: Bool -> Type, t: P(True{}), f: P(False{})) -> P(c):
  match c:
    case True{}:
      t
    case False{}:
      f

# Order
# =====

def Nat.is_le_zero(b: Nat) -> {Nat.is_le(0n, b) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+q:
      {==}

def Nat.is_le_refl(a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.is_le_refl(p)

def Nat.is_le_succ(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Bool.absurd({Nat.is_le(1n+p, 1n+0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      Nat.is_le_succ(p, q, h)

def Nat.is_le_trans(a: Nat, b: Nat, c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool},
  h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      Nat.is_le_zero(c)
    case 1n+p 0n _:
      Bool.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, h1)
    case 1n+p 1n+q 0n:
      Bool.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, h2)
    case 1n+p 1n+q 1n+r:
      Nat.is_le_trans(p, q, r, h1, h2)

def Nat.is_le_pred(a: Nat, b: Nat, h: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case _ 0n:
      Bool.absurd({Nat.is_le(a, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      Nat.is_le_pred(p, q, h)

def Nat.is_le_add(a: Nat, d: Nat) -> {Nat.is_le(a, Nat.add(a, d)) == True{} : Bool}:
  match a:
    case 0n:
      Nat.is_le_zero(d)
    case 1n+p:
      Nat.is_le_add(p, d)

def Nat.dec(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def Nat.is_le_dec(a: Nat) -> {Nat.is_le(a, 1n+Nat.dec(a)) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.is_le_refl(p)

# a below b, so at most b less one
def Nat.is_le_below(a: Nat, b: Nat, h: {Nat.is_le(1n+a, b) == True{} : Bool}) ->
  {Nat.is_le(a, Nat.dec(b)) == True{} : Bool}:
  match b:
    case 0n:
      Bool.absurd({Nat.is_le(a, 0n) == True{} : Bool}, h)
    case 1n+q:
      h
