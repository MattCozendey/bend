# compiler: the laws of step 1
# ============================
#
# PLAN, STEPS #1, as C1 states them (approved). They hold for every program,
# not only for the ones that the kernel accepts (INVARIANTS #1): Wasm.run is
# the Bend copy of WASM's meaning (STEPS #5), Program.gives what a program
# gives by the Bend copy of Eval (INVARIANTS #2 and #3), and Program.need the
# memory that INVARIANTS #4 grants it.

import Base
import ./impl.bend as C

# LAW (INVARIANTS #1), no wrong result: a result that the compiled program
# gives is the one that Eval gives
law no_wrong_result:
  for +f: Nat
  for +p: List<&2, U32>
  for +i: List<&2, U32>
  for +m: U32
  for +o: List<&2, U32>
  for e: {C.Wasm.run(f, C.Compiler.compile(p), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome}
  exs n: Nat
  {C.Program.gives(p, i, n) == Some{o} : Maybe<&2, List<&2, U32>>}

# LAW (INVARIANTS #1), no other failure: when Eval gives a result, the compiled
# program gives it, or runs out of memory
law no_other_failure:
  for +p: List<&2, U32>
  for +i: List<&2, U32>
  for +n: Nat
  for +o: List<&2, U32>
  for +m: U32
  for e: {C.Program.gives(p, i, n) == Some{o} : Maybe<&2, List<&2, U32>>}
  exs f: Nat
  {C.Wasm.run(f, C.Compiler.compile(p), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome} |
    {C.Wasm.run(f, C.Compiler.compile(p), i, m) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}

# LAW (INVARIANTS #1 and #4), enough memory: with the memory that
# Program.need asks, the compiled program gives the result that Eval gives
law enough_memory:
  for +p: List<&2, U32>
  for +i: List<&2, U32>
  for +n: Nat
  for +o: List<&2, U32>
  for +m: U32
  for e: {C.Program.gives(p, i, n) == Some{o} : Maybe<&2, List<&2, U32>>}
  for big: {Nat.is_le(C.Program.need(p, i, n), C.Program.memory(m)) == True{} : Bool}
  exs f: Nat
  {C.Wasm.run(f, C.Compiler.compile(p), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome}
