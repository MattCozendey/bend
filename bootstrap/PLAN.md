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

0. Done (a69359d5). A Lake project in `lean/`, on Lean v4.34.0 as
   `--verdict` uses. `src/Kernel.lean` is `bend2/bendtt.lean` minus its
   Main section, regenerated on every build so this project can declare
   its own `main`. The build fails unless that section (`Kernel.cut` in
   `lakefile.lean`) appears once, unchanged.
1. The contract: `src/Contract/Spec.lean`. Status: reviewed and pinned.
   - It holds definitions and claims only. Write it before compiler code.
   - Claim `correct`: when `compile` accepts def k of a checked book, def k
     is `Pure` and has one result. `run` gives that result or no result,
     at all fuel. It never gives a wrong result.
   - Claim `total`: `compile` accepts each `Pure` def of a checked book. So
     `correct` is not empty.
   - Claim `bytes`: bytes go in and out without change.
   - Claim `cli`: a result from the CLI is the result of the def it runs.
   - Claim `laws`: each law that a proof shows about a def holds about the
     value that `Eval` reaches. So a law proven in Bend holds about the
     result that the CLI shows.
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
   - The build pins the hash of `Contract/Spec.lean` (`Pins` in
     `lakefile.lean`).
2. The verified interpreter. Status: done.
   - `compile` gives the book as it is. The machine is a `step` function
     on terms.
   - `Step.lean`: each `step` is an `Eval` step, and `step` gives none only
     when no `Eval` step exists.
   - `Run.lean`: claims `correct` and `total`. `Bytes.lean`: claim `bytes`.
     `Laws.lean`: claim `laws`. `Cli.lean`: claim `cli`.
   - `Contract/Proof.lean` states the 5 claims for the interpreter and the
     CLI function, and calls the guards. The build pins it.
   - `Main.lean` is the glue: it reads files, calls `Interp.cli`, and
     writes the result. The build pins it.

This completes the trusted compiler. Its `compile` passes the book through,
so it is a trusted interpreter: everything below is speed or new meaning.

## Speed

These change how a program runs, not what it means: the claims stay as
they are. Each is optional, since slow is fine, and each that is done needs
its own proof that it preserves the claims, composed into them. Each waits
on a decision.

Now: a U32 sum over 256 input bytes takes 0.33 s, and over 4096 bytes
3.3 s (most of it reads the input: an echo of 4096 bytes takes 2 s).

1. One-pass step. Status: done. `scanWith` finds the next step and the
   values in one walk. `scanWith_eq` proves that with no jump it gives what
   `step` gives. Before it, 16 bytes took 18 s, and the time grew as the
   cube of the input size.
2. The environment machine. Status: done. `Machine/Impl.lean` keeps values
   in environments and its place in a stack of frames, so no step walks the
   full term. `Machine/Spec.lean` proves that each step keeps the decoded
   term or makes `Eval` steps on it, and that the machine stops. The
   proven stepper then ends the run. Before it, 256 bytes took 146 s.
3. Labels and case trees as integer switches. `Eval` matches labels by
   name; numbering them is a representation choice.
4. Word jumps. A call of base's word code goes to its result in one step,
   for each width. The proof shows that `Eval` reaches the same result.
   - A jump runs only when the book's defs equal `Word/Ref.lean`, a
     generated copy of base's code. Else it does not run, and the result
     stays correct.
   - Status: done for each family: add, sub, not, and, or, xor, inc,
     to_nat, cmp, shl, shr, mul. One file of proofs per family in `Word/`,
     `Word/Shared.lean` for what they share, and `Word/Impl.lean` for the
     jumps.
   - `T.from_nat` also jumps, for each one-word type `T` (U32 now, U64
     later) whose code equals templates in `T` and its width. Before it,
     4096 bytes took 71 s.

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

1. Reviewed files are frozen: `Contract/Spec.lean`, `Contract/Proof.lean`,
   `Guard.lean` and `Main.lean` change only by review. The build pins their hashes, so an
   edit fails until its pin is updated by hand. A pin does not stop a
   person who edits both. It makes each change show in review.
2. No escape hatches:
   - `#guard_runs` walks each def that the CLI function uses. It fails on
     an `opaque`, `partial`, `extern` or `implemented_by` def in this
     project or the kernel copy.
   - Lean's own library is exempt. We trust it.
   - `#guard_axioms`: each proof uses only `propext`, `Classical.choice`
     and `Quot.sound`.
   - An extra: the build scans the code for `sorry` and the rest.
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
