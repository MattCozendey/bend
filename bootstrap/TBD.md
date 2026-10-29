# NOTE: BEND DOESN'T RUN ON WINDOWS USE WSL. NEVER RUN THE FULL SUITE IT KILLS MY COMPUTER AND FREEZES IT

# TBD

Open items for the verified compiler in this folder. The plan they hang
off: a Lean compiler, proven against `Eval` in `bend2/bendtt.lean`, whose
contract (`Claim.compile_correct`, `Claim.compile_total`) is written first
and changes only by review. Its first version is the verified interpreter:
`compile` passes the book through, and the machine steps terms as `Eval`
does. The environment machine comes next. Each item below waits on a
decision.

## Passes beyond the spec

`Eval` fixes what a program means; these change how it runs, in ways the
spec does not describe.

1. Labels and case trees as integer switches. `Eval` matches labels by
   name; numbering them is a representation choice.
2. Native 32-bit words. Replace base's bit-level U32 (`Word(32n)` and the
   defs over it) with Lean's `UInt32`. Needs a proof that each of base's
   elaborated word defs (`Word.add`, ...) equals its `BitVec` operation,
   which ties the compiler to how `base.bend` elaborates.
3. Effects. No spec exists: BendTT keeps every effect opaque, and the C
   and JS in `bend2/effs/` are the de facto semantics. Needs a spec per
   effect, a Lean driver (its pure conversions proven, Lean's IO trusted,
   the OS assumed), and a single-threaded scheduler for `IO.spawn` and
   `Chan.*`, which is fair because pure code between effects halts.

## Optional

4. Erase dead parts (types, q=0 arguments and lets, annotations). Not
   needed for correctness: `Eval` never runs them, so the machine can
   carry them as inert syntax. Only a speed and memory gain. If done,
   `Rwt` needs its own argument: its proof is evaluated at run time.

## Tests

5. Tests for what the proofs do not cover: reading the `.bendtt` file,
   printing the result, and the elaborator (`safe.ts`). Run the tests in
   the subset through `bend -o` and the compiler, and compare each file's
   `#|` lines. A mismatch is a glue or elaborator bug, or a comp.ts bug.
