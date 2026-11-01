import Base

def F(n: Nat) -> Nat:
  n

def t1(-h: @j:Nat -> {F(j) == Nat.add(j, 0n) : Nat}) -> {Nat.add(F(1n), F(2n)) == Nat.add(Nat.add(1n, 0n), Nat.add(2n, 0n)) : Nat}:
  %h(1n) : {Nat.add(_, F(2n)) == Nat.add(Nat.add(1n, 0n), Nat.add(2n, 0n)) : Nat}
  %h(2n) : {Nat.add(Nat.add(1n, 0n), _) == Nat.add(Nat.add(1n, 0n), Nat.add(2n, 0n)) : Nat}
  {==}

def G(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Unit

def t2(-h: @j:Nat -> {F(j) == Nat.add(j, 0n) : Nat}, x: G(Nat.add(1n, 0n)), y: G(Nat.add(2n, 0n))) -> Pair(G(F(1n)), G(F(2n))):
  %h(1n) : Pair(G(_), G(F(2n)))
  %h(2n) : Pair(G(Nat.add(1n, 0n)), G(_))
  (x, y)
