import Base

# Word
# ====
#
# Defs about words for the proofs of the run time (step 5): Word.of_nat, which
# is U32.from_nat at each width, and Fits, whether an i32 holds a number.

# the number x as a word of n bits, modulo 2^n
def Word.of_nat(+n: Nat, x: Nat) -> Word(n):
  match x:
    case 0n:
      Word.zero(n)
    case 1n+p:
      Word.inc(n, Word.of_nat(n, p))

# an i32 holds x: U32.from_nat keeps it
def Fits(x: Nat) -> Type:
  {U32.to_nat(U32.from_nat(x)) == x : Nat}
