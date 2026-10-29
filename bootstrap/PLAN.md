# NOTE: BEND DOESN'T RUN ON WINDOWS USE WSL. NEVER RUN THE FULL SUITE IT KILLS MY COMPUTER AND FREEZES IT

# PLAN

A compiler for Bend that can be trusted: written in Lean and proven against
`Eval`, the run-time semantics in `bend2/bendtt.lean`, so a compiled
program computes what `Eval` says its source computes. Slow is fine. It
trusts Lean (its kernel and compiler) and `bendtt.lean`, and assumes that
`bend -o` (bend.ts and safe.ts) gives the `.bendtt` text that means the
`.bend` file. The `.bendtt` text is the program the proofs speak of.

It covers pure code over datatypes, U32 included at its bit-level meaning.
F32 and effects are out: BendTT keeps them opaque, so `Eval` gives them no
meaning to preserve.

## The trusted compiler

0. Done (a69359d5). A Lake project in this folder, on Lean v4.34.0 as
   `--verdict` uses. `Bootstrap/Kernel.lean` is `bend2/bendtt.lean` minus
   its Main section, regenerated on every build so this project can
   declare its own `main`. The build fails unless that section
   (`Kernel.cut` in `lakefile.lean`) appears once, unchanged. `Main.lean`
   is a placeholder that runs the kernel's check.
1. The contract, `Spec.lean`, written before any compiler code:
   - `Claim.compile_correct`: if `compile` accepts a checked book, running
     its code on the machine gives what `Eval` gives main.
   - `Claim.compile_total`: every checked book whose main is `Pure`
     compiles, so the first claim is not vacuous.
   - `observe` compares only a result's live parts: dead fields may differ
     in text.
   - `Pure`: main's live code reaches no opaque def, since `Eval` would run
     its placeholder body. Kept simple, as a narrower one would make
     `compile_total` hollow.
   - Fuel lives inside `Machine.run`. The CLI passes a huge number, and
     running out is an error, never a wrong answer.
2. The verified interpreter. `compile` passes the book through, and the
   machine is a `step` function on terms. Prove `step t = some u → Eval bk
   t u` and `(∃ u, Eval bk t u) → step t ≠ none`, then close both claims
   with the kernel's `halts`, `progress` and `sr`. The CLI parses with
   `Book.parse`, checks with `Book.check`, runs and prints.

This completes the trusted compiler. Its `compile` passes the book through,
so it is a trusted interpreter: everything below is speed or new meaning.

## Speed

These change how a program runs, not what it means: the claims stay as
they are. Each is optional, since slow is fine, and each that is done needs
its own proof that it preserves the claims, composed into them. Each waits
on a decision.

1. The environment machine: closures instead of substitution. Actual
   compilation starts here.
2. Labels and case trees as integer switches. `Eval` matches labels by
   name; numbering them is a representation choice.
3. Native 32-bit words. Replace base's bit-level U32 (`Word(32n)` and the
   defs over it) with Lean's `UInt32`. The meaning stays base's: the proof
   shows each of base's elaborated word defs (`Word.add`, ...) equals its
   `BitVec` operation, which ties the compiler to how `base.bend`
   elaborates.
4. Erase dead parts (types, q=0 arguments and lets, annotations). `Eval`
   never runs them, so the machine can carry them as inert syntax; erasing
   them saves time and memory. `Rwt` needs its own argument: its proof is
   evaluated at run time.

## Beyond the spec

These need a meaning `Eval` does not give, so the claims grow: the meaning
is written and reviewed before any compiler work. Each waits on a decision.

1. Effects. No spec exists: BendTT keeps every effect opaque, and the C
   and JS in `bend2/effs/` are the de facto semantics. Needs a spec per
   effect, a Lean driver (its pure conversions proven, Lean's IO trusted,
   the OS assumed), and a single-threaded scheduler for `IO.spawn` and
   `Chan.*`, which is fair because pure code between effects halts.
2. F32. Its ops are base laws with no body, so the kernel knows only their
   types. Needs a spec, as software floating point over `Word(32n)`:
   in Lean, outside `--verdict`, or as bodies in `base.bend`, which
   `--verdict` then backs and comp.ts's native floats must match.

## Guards

How the compiler stays correct as it grows.

1. The contract is frozen: `Spec.lean` changes only by review. The build
   pins its hash, so an edit fails until the pin is updated by hand.
2. No escape hatches: the build fails on `sorry`, `axiom`, `native_decide`,
   `partial`, `unsafe`, `implemented_by` or `extern` in this folder's
   sources, and `#print axioms` on both claims must list only `propext`,
   `Classical.choice` and `Quot.sound`. `Kernel.lean` is exempt: its
   parser is `partial`, trusted as `--verdict` trusts it.
3. What runs is what is proven: the CLI calls the `compile` and
   `Machine.run` the claims name, and the glue around them stays tiny.
4. The spec is tracked: Step 0 imports the kernel in place, so a change to
   `Eval` rechecks every proof.
5. No vacuity: a proven `compile_total` needs no tests. `Pure` is reviewed
   as part of the contract.

## Tests

TBD. Tests for what the proofs do not cover: reading the `.bendtt` file,
printing the result, and the elaborator (`safe.ts`). Run the subset's
tests through `bend -o` and the compiler a few at a time, never the full
suite, and compare each file's `#|` lines. A mismatch is a glue or
elaborator bug, or a comp.ts bug.
