import Base
import ../wasm/impl.bend as Wasm
import ./impl.bend as Imp

# Imp laws
# ========
#
# The translation keeps the meaning of a program: its module gives each output
# that the program gives, and no other. proof.bend proves them.

# for a program, the pages, an input and a fuel n of the program: a fuel of its
# module
law fuel_out:
  for p: Imp.Prog
  for pages: Nat
  for input: Maybe<&2, List<&2, Nat>>
  for n: Nat
  Nat

# The module gives each output that the program gives.
law compile_keeps:
  for p: Imp.Prog
  for pages: Nat
  for input: Maybe<&2, List<&2, Nat>>
  for n: Nat
  for w: List<&2, Nat>
  for h: {Imp.Imp.run(pages, n, p, input) == Some{w} : Maybe<&2, List<&2, Nat>>}
  {Wasm.Wasm.run(pages, fuel_out(p, pages, input, n), Imp.Imp.compile(p), input) == Some{w} :
    Maybe<&2, List<&2, Nat>>}

# The module gives no other output: the program gives each output that the
# module gives in n steps, with fuel n.
law compile_adds_none:
  for p: Imp.Prog
  for pages: Nat
  for input: Maybe<&2, List<&2, Nat>>
  for n: Nat
  for w: List<&2, Nat>
  for h: {Wasm.Wasm.run(pages, n, Imp.Imp.compile(p), input) == Some{w} : Maybe<&2, List<&2, Nat>>}
  {Imp.Imp.run(pages, n, p, input) == Some{w} : Maybe<&2, List<&2, Nat>>}
