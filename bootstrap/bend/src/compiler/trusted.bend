# compiler: the program that the interpreter runs (PLAN, STEPS #3)
# ================================================================
#
# main is our own compiler: it takes the bytes of a book, as the Lean writer
# writes them, and gives the bytes of its WASM module. The laws of spec.bend
# and their proofs (proof.bend) are in this file's book, so that a book that
# --verdict accepts for this file holds them.

import Base
import ./impl.bend as C
import ./proof.bend as P

def main(+p: List<&2, U32>) -> List<&2, U32>:
  C.Compiler.compile(p)
