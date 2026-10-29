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
1. The contract: `Bootstrap/Spec.lean`. Status: reviewed and pinned.
   - It holds definitions and claims only. Write it before compiler code.
   - Claim `correct`: when `compile` accepts def k of a checked book, def k
     is `Pure` and has one result. `run` gives that result or no result,
     at all fuel. It never gives a wrong result.
   - Claim `total`: `compile` accepts each `Pure` def of a checked book. So
     `correct` is not empty.
   - Claim `bytes`: bytes go in and out without change.
   - Claim `cli`: a result from the CLI is the result of the def it runs.
   - `Answer`: a value that `Eval` reaches shows the result. Each value
     that `Eval` reaches shows the same result.
   - `observe`: the plain data in a value. It is the same as the kernel's
     `Data`: it drops only dead (q=0) fields.
   - `Pure`: the kernel's checker accepts the type as Data, and no opaque
     def is reachable. It can be false by mistake, never true by mistake.
   - Input: a list of bytes. Each byte is a Nat in unary (`Zero`, `Succ`).
     A Nat has one form only, so its type fixes its meaning.
   - The CLI adds def `bootstrap.run` = `main(input)`. The kernel checks
     the full book.
   - A compiler written in Bend fits as one pure function:
     `compile(src) -> out`.
   - The build pins the hash of `Spec.lean` (`Spec.pin` in
     `lakefile.lean`).
2. The verified interpreter. `compile` gives the book as it is. The
   machine is a `step` function on terms.
   - Prove `step t = some u → Eval bk t u`, and
     `(∃ u, Eval bk t u) → step t ≠ none`.
   - Then prove the 4 claims with the kernel's `halts`, `progress`, `sr`
     and `confluent`.
   - The CLI parses with the kernel's `Book.parse`, then calls one
     function. Claim `cli` is about that function.
   - Freeze the lines that state the claims for this compiler and this
     function.

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
   pins its hash, so an edit fails until the pin is updated by hand. The
   pin does not stop a person who edits both. It makes each change show
   in review.
2. No escape hatches:
   - A Lean check walks each def that the CLI function uses. It fails on
     an `opaque`, `partial`, `extern` or `implemented_by` def in
     `bootstrap/` or the kernel copy.
   - Lean's own library is exempt. We trust it.
   - `#print axioms` on each proof shows only `propext`,
     `Classical.choice` and `Quot.sound`.
   - A text scan for `sorry` and the rest is an extra.
3. What runs is what is proven: claim `cli` is about the function that
   main calls. Outside the proofs: Lean's IO, the kernel's parser (as
   `--verdict`), and printing a result that is not bytes.
4. The spec is tracked: Step 0 imports the kernel in place, so a change to
   `Eval` rechecks every proof.
5. No vacuity: a proven `compile_total` needs no tests. `Pure` is reviewed
   as part of the contract.

## Tests

TBD. Tests for what the proofs do not cover: reading files, the kernel's
parser, printing a result that is not bytes, and the elaborator
(`safe.ts`). Run the subset's
tests through `bend -o` and the compiler a few at a time, never the full
suite, and compare each file's `#|` lines. A mismatch is a glue or
elaborator bug, or a comp.ts bug.
