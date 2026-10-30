# NOTE: THE EXISTING `bend` COMMAND DOESN'T RUN ON WINDOWS: USE WSL FOR IT. THIS IS ITS LIMIT, NOT OURS. NEVER RUN THE FULL TEST SUITE: IT FREEZES MY COMPUTER. DON'T RUN THE LINTER. THEIR RULES DON'T APPLY TO THIS NEW BEND

# PLAN

The goal: a compiler for Bend, written in Bend, that you can trust.

The Lean part (this folder) is the starting point: a trusted interpreter
for Bend. It is written in Lean and proven against `Eval`, the run-time
semantics in `bend2/bendtt.lean`: it computes what `Eval` says a program
computes. Slow is fine.

The two parts join like this:
1. The compiler in Bend is one pure function, `compile(src) -> out`: bytes
   in, bytes out. Its laws are proven in Bend.
2. The interpreter runs it on `src`. Claim 7 carries each law for all
   `src` about `compile(src)` to the bytes that the interpreter writes.

## Assumptions

We trust these, with no proof:
1. The checker is right. The Bend kernel (`bendtt.lean`), `bend -o`
   (`bend.ts` and `safe.ts`), which gives the kernel its input, and Lean
   (its kernel, its compiler and its IO) are correct. So a `--verdict`
   result is true. The proofs speak of the `.bendtt` text that `bend -o`
   gives.
2. Bend is sound, as `bendtt.lean` proves.
3. The claims state what we need. A person reviews `Contract/Spec.lean`;
   the build proves its claims.
4. The existing compiler is not trusted. `comp.ts`, its output and the
   effect code in `bend2/effs/` decide nothing about our compiler. Our
   compiler grows on its own. It can take ideas from them, nothing more.
   We use the `bend` command for one job: `bend -o`, which makes the
   `.bendtt` text (assumption 1).

## Scope: correct, and incomplete on purpose

Each result that the interpreter gives is the result that `Eval` gives.
It covers pure code over datatypes, U32 at its bit-level meaning included.

It refuses each def that reaches an opaque def. It follows each name in
each part of a def, the dead parts included. `bend -o` makes a def opaque
when the def has no body: F32 ops, effects, handles, natives, foreign
fills. For an opaque def, the kernel has only a model: a placeholder of
the right type. So `Eval` gives no real result to preserve.

**Bootstrapping does not need opaque defs.** The compiler in Bend uses no
F32, no effect and no handle.

The scope only grows. When a def gets a body, it is no longer opaque, and
the interpreter runs it. A refusal then becomes a result, and no earlier
result changes. "Beyond the spec" says how F32 and effects can get a
meaning.

## The trusted interpreter

0. The project. Status: done (a69359d5).
   - A Lake project in `lean/`, on Lean v4.34.0, as `--verdict` uses.
   - `src/Kernel.lean` is `bend2/bendtt.lean` minus its Main section, so
     this project can declare its own `main`.
   - The copy is committed, because Lake reads module headers before it
     runs a target. `lake run regen` writes it.
   - Each build fails unless the copy is exactly that text, and unless that
     section (`Kernel.cut` in `lakefile.lean`) occurs once, unchanged.
1. The contract: `src/Contract/Spec.lean`. Status: reviewed and pinned.
   - It holds definitions and claims only. It came before the interpreter
     code. It has the exact text of each claim.
   - Claim 1, `correct`: when `compile` accepts def k of a checked book, k
     is `Pure` and has one result. Some fuel makes `run` give it. At all
     fuel, `run` gives it or no result, never a wrong result.
   - Claim 2, `total`: `compile` accepts each `Pure` def of a checked book.
     So claim 1 is not empty.
   - Claim 3, `bytes`: bytes go in and out without change.
   - Claim 4, `cli`: when the CLI gives a result, at any fuel, the kernel
     accepted the book (as for `--verdict`) and the book with the input,
     the def is `Pure`, and the result is its result. For each `Pure` def
     of such books, some fuel gives a result.
   - Claim 5, `laws`: each law about a def, or about its body, holds about
     each value that `Eval` reaches from the def.
   - Claim 6, `shut`: `Eval` from a `Pure` def meets no opaque def.
   - Claim 7, `input`: when the CLI gives a result for an input, each law
     of the book for all inputs of `main` holds at that input, about a
     value that shows the result. A law can have more `for` binders after
     the input: it holds for each closed value of them. It can name `main`,
     or `f` when `main` is `λx. f(x)`: `bend -o` puts a path before the
     names of an imported file, so a law there cannot name `main`.
   - `Answer`: a value that `Eval` reaches shows the result. Each value
     that `Eval` reaches shows the same result.
   - `observe`: the plain data in a value. It is the kernel's `Data`: it
     drops only dead (q=0) fields.
   - `Pure`: the kernel's checker accepts the type as Data, and a shut set
     of defs that are not opaque holds the def. It can be false by
     mistake, never true by mistake.
   - Input: a list of bytes. Each byte is a Nat in unary (`Zero`, `Succ`).
     A Nat has one form only, so its type fixes its meaning.
   - Output: a result that is a List of Nat below 256 goes out as bytes.
     The result type must be Data, for example `List<&2, Nat>`.
     `List<Nat>` is short for `List<&1, Nat>`, a Type, so the CLI refuses
     a def that gives it.
   - With an input, the CLI adds two defs: `bootstrap.input : A = input`,
     where `A` is the input type of `main`, and `bootstrap.run` =
     `main(bootstrap.input)`. The kernel checks the book with those defs,
     so it checks the input once.
   - The build pins the hash of `Contract/Spec.lean` (`Pins` in
     `lakefile.lean`).
2. The verified interpreter. Status: done.
   - `compile` gives the book as it is. The environment machine runs it,
     and the proven `step` ends the run (Speed, items 1 and 2).
   - `Step.lean`: each `step` is an `Eval` step, and `step` gives none only
     when no `Eval` step exists.
   - The proofs: `Run.lean` (claims 1, 2), `Bytes.lean` (3), `Cli.lean`
     (4), `Laws.lean` (5, 7), `Shut.lean` (6).
   - `Contract/Proof.lean` states the 7 claims for the interpreter and the
     CLI function, and calls the guards. The build pins it.
   - `Main.lean` is the glue: it reads files, calls `Interp.cli`, and
     writes the result. The build pins it.

This completes the Lean part. Its `compile` passes the book through, so
it is an interpreter. Each item below adds speed or a new meaning.

## The compiler in Bend

Status: the contract is written, reviewed and pinned. The first compiler
passes the source through and proves it (Parts, below). Its contract came
first, as `Contract/Spec.lean` came before the interpreter. A law that
holds is not always the law we need. These three requirements decide what the
contract holds:
1. A preservation law: the output means what the source means, for each
   `src`. A law that is too weak lets a wrong compiler pass, for example
   "the output is well-formed".
2. A totality law: `compile` accepts what it should accept. Without it,
   law 1 holds for a compiler that refuses everything. This is why the
   interpreter has claim 2 beside claim 1.
3. The meaning of the source and of the target, written in Bend. A person
   reviews them. No claim of `Contract/Spec.lean` ties them to the kernel's
   `Eval`; laws in Bend tie the source meaning to a copy of its rules. If
   `Eval` does not run the target, the chain of trust ends at that meaning.

Review each law as `.bendtt` text, not as `.bend` text: the proofs speak of
the `.bendtt` text (assumption 1). Claim 7 carries each law for all inputs
to the bytes that the interpreter writes.

Tests do not replace a law: a test samples, and a law covers all inputs.
A test finds a law that is too weak or empty, and an assumption that fails.

Decisions:
1. The source is `.bendtt` text, as `bend -o` gives it. Assumption 1
   already trusts `bend -o`. The source meaning is the kernel's parser and
   `Eval`, written in Bend. `Eval` has no typing premise, so the laws hold
   for each program, typed or not, and the compiler needs no type checker.
   A program's own laws hold only when the kernel checks it (`--verdict`).
   A frontend for `.bend` can come later: the laws hold for each `.bendtt`
   text that it gives.
2. The target is `.bendtt` now. The first compiler passes the source
   through, as the interpreter did, to test the chain: the source meaning,
   claim 7 and the harness. The next target is WASM (see The WASM target).
   Its meaning takes the memory size as a parameter: with a fixed size, the
   law is false for large programs; if out of memory counts as no result,
   the law is empty.
3. The interpreter's limits (`Pure`) bind only what it runs: the compiler,
   which is bytes to bytes, and the output of the `.bendtt` target. The
   source meaning can grow past `Eval`, for example to effects.
4. A law is `for src: List<&2, Nat>`, more `for` binders (for example the
   fuel), then an equality. Claim 7 carries it. Bend's `exs` is Base's
   `Exists` datatype, not a binder, so claim 7 does not carry it. A law says
   "some fuel" with a fuel function that the compiler gives: a proof of
   `exs` computes that fuel anyway.
5. The contract is a module's `spec.bend`: its laws, and the defs that
   only they use. It is pinned as `Contract/Spec.lean` is. `main` is
   `λsrc. compile(src)`, so the laws name `compile` (claim 7).

Parts, in `bootstrap/bend/`:
1. `main.bend`: `main` is `λsrc. compile(src)`.
2. `src/compile/spec.bend`: the contract. `compile`, and the fuel functions
   `fuel_out` and `fuel_src`. `keeps_results`: the output gives each result
   that the source gives (as claim 2). `adds_no_results`: it gives no other
   result (as claim 1).
3. `src/compile/impl.bend`: the compiler. It passes the source through, so
   the laws hold at the same fuel.
4. `src/source/impl.bend`: the source meaning: the kernel's parser, and
   `step` and `stepUntil` as `Step.lean` has them.
5. `src/source/spec.bend`: the kernel's run-time relations (`Data`, `Walk`,
   `Value`, `Eval`), copied rule by rule, and the laws of `Step.lean`.
   `src/source/proof.bend` proves them, so `step` and the run follow `Eval`
   by proof. The copy differs only in form: equalities in place of
   indices, `X.when(c)` for a premise `(c = true → X)`, `Values` as a def,
   and `Walk` without the book, which no rule of it reads.

The build pins parts 1, 2, 4 and 5, and what they copy and reach (see
Guards, item 1). The proofs tie `step`, `walk`, `is_value`, `is_data` and
the run to the copy of the rules. All else is review-only. No proof finds an
error in it:
- part 4: the parser, `run`, `observe`, the entry, `Obs.is_eq`,
  `Obs.is_kept`, and the helpers that the rules call (`Term.sub`,
  `Term.shift`, `Sub`, `Env.sub`, `Term.spine`, `Term.unspine`,
  `Term.takes`, `Term.node`, `Book.get`, `Quan`, `Term.qmin`, `Name`).
  `step` calls the same helpers, so an error in one is on both sides.
- part 5: the copy of the rules.
- the Base defs that parts 4 and 5 reach. The laws fix some of them, for
  example `Nat.is_eq` through the hit and miss rules, but not all.

The compiler's book holds all the proofs, so each run of the CLI has the
kernel check them.

## The WASM target

The goal is speed: the compiler in Bend writes WASM, which an engine runs
near native speed. It compiles all of pure Bend, with no subset, so that no
workaround hides in a scope.

Decisions:
1. The meaning comes first, as for the other parts: `src/wasm/impl.bend`,
   a small part of WebAssembly 2.0, copied from its spec. A person reviews
   it against the spec. Its header lists the part.
2. A module is one function, of type `[] -> [i32]`. The compiled code keeps
   its own stack in linear memory, not on the engine's call stack, so only
   the memory size bounds a run, and the meaning has that size as a
   parameter. Its blocks and loops have the empty type.
3. The module imports its memory (`env.memory`), so the host chooses its
   size. The input's length goes at 0 and its bytes at 4, or 0xffffffff
   goes at 0 for no input; `main` returns an address whose length and
   bytes are the output. `Wasm.fits` says which sizes and inputs the host
   can run.
4. The laws speak of the module's syntax (`Module`, `Code`).
   `Wasm.encode` writes its bytes. It stays review-only: an engine checks
   the bytes, and refuses an invalid module.
5. The meaning has no validation. An engine refuses an invalid module, so
   such a module gives no result where the meaning may give one: never a
   wrong one.
6. Two engines run each module: bun's (JavaScriptCore) and node's (V8),
   with the same glue, `harness/wasm.ts`. It names the kind of each failure:
   a trap, an invalid module, a link error, or an input or output that does
   not fit.
7. The meaning and the glue add to what you trust (assumption 1 trusts the
   engines): they are pinned, as are the Base defs that the meaning reaches.

Status: the meaning, the encoder and the glue are done, and tested (see
Tests). The contract, `src/compile_wasm/spec.bend`, is reviewed and
pinned; its header states what it promises and its excuses. It is a new
module, so the compiler in `src/compile/` stays until the new one replaces
it.

The compiler is a chain of proven steps, each a module with its laws, each
reviewed before the next starts:
1. Imp: a small structured language (i32 locals, memory, `if`, loops,
   `break`), with a meaning and a proven translation to the WASM meaning.
   All later run-time code is Imp, so no later proof reads WASM. Status:
   done (`src/imp/`).
2. The front: the parse with a fuel that the text's length gives
   (`Front.fuel`), as `Source.run` parses with the fuel of the run.
   `parse_above` proves that each fuel from `Front.fuel` on parses each
   text that some fuel parses, to the same defs. Status: done
   (`src/front/`).
3. The machine: an environment machine on the parsed book, with no
   substitution, after the Lean machine (`Machine/`). It is exact for
   untyped books too, where the Lean machine hands the run to `stepUntil`:
   a dead term is a closure, and the machine reads its form when a case
   tree asks for it. Its result is the source's run on the parsed book:
   its fuel for a run of the source sums the weights of the run's terms,
   and the source needs one step more than the machine. Status: done
   (`src/machine/`).
4. The layout: the machine's values, environments and frames as bytes in
   the memory, with a number for each def and each label. A full memory
   gives `Out.oom`. It does what step 3 does.
5. The run time in Imp: the machine's loop, the loader (the book into the
   memory, by stores, as the WASM part has no data segments), the input
   (its `Nat`s 0 to 255 shared) and the output (`Out.of`). It computes what
   step 4 computes.
6. The assembly: `compile(src)` is the WASM of the loader and the run time.
   The laws of steps 1 to 5 give the contract's laws. `main.bend` becomes
   `λsrc. Wasm.encode(compile(src))`, and `src/compile/` goes.

So the first compiler interprets the book; it is likely no faster than the
Lean interpreter. Then, each optional and proven against the step below it:
7. Case trees as code: each def as its own Imp code.
8. U32 and Word as i32 operations, as the interpreter's jumps.
9. A compact `Nat`.
10. Garbage collection.
11. The compiler compiled by itself, so that compiling is fast too.

## Speed

Each item changes how a program runs, not what it means: the claims stay
as they are. Each item is optional, because slow is fine. Each done item
has its own proof that it keeps the claims, composed into them.

Now: a U32 sum over 256 input bytes takes 0.3 s, and over 4096 bytes
3 s. Most of that time reads and checks the input: an echo of 4096 bytes
takes 2 s.

1. The environment machine. Status: done. `Machine/Impl.lean` keeps values
   in environments and its place in a stack of frames, so no step walks the
   full term. `Machine/Spec.lean` proves that each step keeps the decoded
   term or makes `Eval` steps on it, and that it stops where `Eval` ends.
   Before it, 256 bytes took 146 s.
2. A linear end of a run. Status: done. When the machine stops, `runSteps`
   (`Run.lean`) ends the run with `stepUntil`, which tests `isValue` before
   each `step`. So a large data result costs time linear in its size.
   Without that test, the echo took 30 s, because `step` checks again that
   a part is a value.
3. Labels and case trees as integer switches. Status: waits on a decision.
   `Eval` matches labels by name. Numbers for labels are a choice of
   representation.
4. Word jumps. Status: done. A call of base's word code goes to its result
   in one step, for each width. The proof shows that `Eval` reaches the
   same result.
   - A family jumps only when the book's defs for it equal
     `Word/Ref.lean`, a generated copy of base's code (`scripts/GenRef.lean`
     makes it from `scripts/ref.bend`). Else it does not jump, and the
     result stays correct.
   - The families: add (it also takes sub), not, and, or, xor, inc,
     to_nat, cmp, shl, shr, mul. Each family (`Family`) has a list of defs
     (its code), its jump, and a proof that the jump is sound when the book
     has the code (`HasRefs`). `Word/` has one file of proofs per group of
     families, `Word/Shared.lean` for what they share, and `Word/Impl.lean`
     for the jumps.
   - `T.from_nat` also jumps, for each one-word type `T` (U32 now, U64
     later) whose defs equal the templates of `Word/Nat.lean`, when
     `Word.inc` also equals its copy. Before it, 4096 bytes took 71 s.

## Beyond the spec

These need a meaning that `Eval` does not give, so the claims grow. Write
and review the meaning before any code for it. Each waits on a decision.

1. Effects. No spec exists: BendTT keeps each effect opaque. The C and JS
   in `bend2/effs/` are not a spec for us (assumption 4). They can give
   ideas only. Needs:
   - our own spec per effect;
   - a Lean driver: its pure conversions proven, Lean's IO trusted, the OS
     assumed;
   - a single-threaded scheduler for effects that run at the same time,
     such as `IO.spawn` and `Chan.*`. It is fair, because pure code
     between effects halts.

   An option: write each effect as data, a request and the code that runs
   after the answer. Data is pure, so `Eval` gives it a meaning, and a
   proof in Bend can use it. Only the code that does the real IO stays
   outside the proofs.
2. F32. Its ops are base laws with no body, so the kernel knows only their
   types. Needs a spec, as software floating point over `Word(32n)`, in one
   of two places:
   - In Lean, outside `--verdict`. Then the claims grow.
   - As bodies in `base.bend`. Then `--verdict` checks them, and the claims
     do not change: the ops are no longer opaque, so `Eval` gives their
     meaning.

   The bodies give the meaning only. A compiler can still emit native float
   ops, with a proof that each op gives what its body gives. That proof
   assumes that the hardware follows IEEE 754 strictly: no fast-math, no
   FMA contraction, no flush-to-zero. Check the bodies against IEEE 754
   test vectors.

## Guards

How the interpreter stays correct as it grows.

1. Reviewed texts are frozen: each text that `Pins` (`lakefile.lean`) names
   changes only by review, for example `Contract/Spec.lean` and the
   contract of the compiler in Bend. The build pins their hashes, so an edit
   fails the build until its pin is updated by hand. The harness runs the
   same check (`lake run pinned`) before its cases, so an edit also stops
   the tests. A pin does not stop a person who edits both. It makes each
   change show in review.
2. No escape hatches:
   - `#guard_runs` walks each def that `Interp.cli` or `Bytes.ofObs` uses.
     It fails on an `unsafe`, `opaque`, `extern` or `implemented_by` def in
     this project or the kernel copy. Lean makes a `partial` def opaque, so
     it fails on that too. Lean's own library is exempt: we trust it.
   - `#guard_axioms`: each proof uses only `propext`, `Classical.choice`
     and `Quot.sound`.
   - An extra: the build scans the code for the words of `Scan.words`
     (`lakefile.lean`), for example `sorry`.
3. What runs is what is proven: claims 3 and 4 are about the functions that
   `main` calls. Outside the proofs: Lean's IO, reading the arguments and
   the files, the kernel's parser (as for `--verdict`), and `render`, which
   prints a result that is not bytes.
4. The spec is tracked: the kernel copy must equal `bend2/bendtt.lean`
   minus its Main section, so a change to `Eval` rechecks every proof. The
   build check is our own code, so also check the copy by hand. This diff
   must show only the `main` section:

       diff bend2/bendtt.lean <(tail -n +4 bootstrap/lean/src/Kernel.lean)

   The meaning in Bend copies parts of `bendtt.lean` by hand. Their pins
   (item 1) fail when one changes, until a person checks the copy again.
5. No vacuity: claim 2 makes claim 1 not empty, with no test. `Pure` is
   reviewed as part of the contract. A test must still show that real books
   pass the kernel's check (see Tests).

## Tests

Status: the harness is done, with 4 cases for the interpreter
(`interp.json`), 1 for the compiler in Bend (`compile.json`), 26 for the
WASM meaning (`wasm.json`) and 25 for the engines (`wasm_engines.json`).

The tests cover what the proofs do not:
- reading files, the kernel's parser, and `render`;
- the elaborator (`safe.ts`);
- that the kernel accepts the book with the input, for a usual
  `main : List<Nat> -> D`;
- that the compiler in Bend reaches no opaque def. `bend -o` also makes each
  template `~` parameter opaque (`bend2/safe.ts`).

One harness serves both parts: `bootstrap/harness/harness.ts`. It does not
know which implementation it tests. A command-line parameter names it:

    bun bootstrap/harness/harness.ts --run '<command>' [--make '<command>']
      [--check '<command>'] bootstrap/harness/cases/interp.json

- `--run` is the implementation, for example the bootstrap program, with
  `{program}` (a `.bendtt` file) and `{input}`. It writes the output bytes
  to stdout and exits non-zero to refuse. The compiler in Bend runs on the
  interpreter, so its command is the same, with the `.bendtt` file of the
  compiler as the program. Later, a command can run it with no interpreter.
- `--make` turns a `.bend` program into `.bendtt`. By default it runs this
  repo's Bend (`bend2/main.ts`), because the pins cover its `base.bend` and
  `bendtt.lean`. Another `--make` must run a Bend with the same files. This
  is the only step that needs Bend, so it is the only step that needs WSL
  on Windows, for example `--make 'wsl -e bash -lc "bun <repo>/bend2/main.ts
  {source} -o {out}"'`. It makes a program where it is, so that its imports
  resolve. A case whose program is not a `.bend` file skips it.
- `--check` runs before the cases, in `bootstrap/lean`. By default it is
  `lake run pinned` (Guards, items 1 and 4). When it fails, the harness
  runs no case.
- A case has an `expect`: the output bytes, the output text, or a refusal
  that names a text. Without `expect`, two `--run` must give the same
  outcome. The existing compiler's run cannot be a `--run` as it is: it
  takes `.bend` source, takes no byte input, and prints surface syntax. For
  a comparison, run `bend file.bend` by hand. Its differences are advice
  only (assumption 4): `Eval` decides.
- Cases are data in `bootstrap/harness/cases/`, one list for each part. The
  `#|` lines of the existing tests are not cases, because they come from
  the existing JS and C runs.
- Run a few cases at a time. Never run the full suite.
- The WASM meaning has two case lists. `harness/gen_wasm.ts` makes both
  from `i32.wast` of the official testsuite (the script names its commit)
  and from tests written by hand. `wasm.json` runs the modules of
  `cases/wasm.bend` by the meaning (kind b, against the testsuite), in 60 s.
  `wasm_engines.json` runs the same modules, as `Wasm.encode` writes them,
  on bun and node (kind b, against the engines). Give it one `--run` for
  each engine, with `<bootstrap>` the path of the interpreter and `<repo>`
  the path of this repo (the command runs in another folder):

      --run 'sh -c "<bootstrap> {program} {input} > {input}.wasm &&
        tail -c +3 {input} > {input}.data &&
        bun <repo>/bootstrap/harness/wasm.ts {input}.wasm {input}.data 1"'
