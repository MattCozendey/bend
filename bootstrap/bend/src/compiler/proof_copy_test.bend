import Base

def use(f: @n: Nat -> Sigma<&2, &2, Nat, k => {k == k : Nat}> -> {n == n : Nat}) -> {0n == 0n : Nat}:
  f(0n, (0n, {==}))

def rec2(-k: Nat) -> {0n == 0n : Nat}:
  use(n => q => Sigma.go(n, q))

def Sigma.go(n: Nat, q: Sigma<&2, &2, Nat, k => {k == k : Nat}>) -> {n == n : Nat}:
  (w, u) = q
  {==}
