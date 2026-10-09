# Inpiling

Inpiling lets a user give a function a second, faster route for inputs of a
particular shape, prove it equivalent, and have the compiler take it, without
main.bend knowing it exists.

    main.bend    the program as written: the general, readable code
    LAWS.bend    what the program must satisfy
    PROOF.bend   the proofs of LAWS.bend
    PERF.bend    the shape-specific routes, their guards, and the proofs
                 that each route agrees with main.bend where its guard holds

The meaning lives in main.bend; the speed lives in PERF.bend. Deleting
PERF.bend changes how fast the program runs, never what it prints.

## Working rules

- On Windows, everything runs in WSL: builds, tests, benches, any command.
  This is non-negotiable.
- Never run the full gates (`gates/_run.ts`, `gates/test.ts`,
  `gates/perf.ts`, `gates/safe.ts`, `gates/ping.ts`); they may be too much
  for the machine. Run single tests or demos, and ask before running any
  gate.

## Principles

- main.bend is unaware: it never imports PERF.bend, names its functions, or
  carries annotations. Everything perf-specific is in PERF.bend.
- Every route is proven: a route is taken only where a checked law says it
  gives the same result as the general code.
- The general code is always compiled. A route is an addition, never a
  replacement.
- The choice of route is the compiler's, not the call site's.
- Proofs are compile-time only and erased; they never run.

## Scope

The value keeps its type; for a given shape, a different algorithm runs.
A different representation of the data (tree vs array kept across calls)
is out of scope for both phases. A route may still convert internally,
compute, and return.

## Phase 1: proof of concept, plain runtime guard

### What the user writes (PERF.bend only)

Syntax is illustrative; the final form follows Bend's law syntax.

    import ./main.bend as M

    # the guard: pure, inspects x and hands it back (Bend is affine)
    def small(x: Bar) -> Bar & Bool:
      ...

    # the route for that shape
    def foo_small(x: Bar) -> T:
      ...

    # the guard returns x unchanged
    law small.same:
      for +x: Bar
      {fst(small(x)) == x : Bar}

    # where the guard says True, the route agrees with main.bend
    law foo.small:
      for +x: Bar
      {snd(small(x)) == True : Bool} -> {M.foo(x) == foo_small(x) : T}

### What the compiler does

1. Load: if PERF.bend sits next to main.bend, load and check it with the
   book. It must import ./main.bend. A flag (`--no-perf`) skips it.
2. Recognize: every PERF law of the shape
   `guard(x) == True -> {M.f(x) == g(x) : T}`, with its `same` law, is a
   rule. A PERF law that names a main.bend def in that position but has
   another shape is an error.
3. Rewrite the checked book, before emitting:
   - `M.foo`'s original body becomes `M.foo.gen`.
   - `M.foo` becomes the dispatcher:

         def M.foo(x):
           (x, ok) = small(x)
           match ok:
             case True{}:  foo_small(x)
             case False{}: M.foo.gen(x)

   - Several rules for one function chain in file order; the first guard
     that says True wins, and `M.foo.gen` is the last arm.
   - Calls to main.bend defs from inside PERF.bend go to their `.gen`.
   - Recursive calls inside main.bend go through the dispatcher, so a
     route applies at every level of a recursion.
4. Emit as usual. The dispatcher is plain Bend: a guard call, a tag
   compare on the Bool, and a tail jump (`WL_JMP`) into the chosen route.
   C, Metal, CUDA and JS get it with no emitter or runtime change.

### The halting rule

Each piece is checked to halt on its own, but the rewrite builds a program
the checker never saw. Without the `.gen` rule, `foo_small(x) = M.foo(x)` is
provably equal to `M.foo(x)`, and the dispatched program loops forever.
With it, a route never re-enters a dispatcher, and the original termination
argument of main.bend still holds: dispatch only adds routes that halt.

### IO

- A function returning `IO(A)` takes rules like any other; the law reads
  `{M.foo(x) == foo_small(x) : IO(A)}`. IO is a continuation-passing value
  whose primitives are opaque to the checker, so the proof should only go
  through when both sides perform the same effects in the same order.
  A route can speed up the pure work between effects; it cannot reorder,
  batch or merge effects.
- Guards are pure: `Bar -> Bar & Bool`, never `IO`.

### Where the changes go

- `bend2/main.ts`: the PERF.bend loader, the flag, rule recognition, the
  book rewrite.
- No change to `bend2/bend.ts`, the checker, the emitters or the runtimes.

### The gate

- Each test with a PERF.bend runs with and without it, and both runs must
  print the same `#|` lines.
- The perf bench times both and reports the difference.
- During development, check this on the single tests and demos involved, in
  WSL; running the gates themselves needs asking first (see Working rules).

### Deliverables

- The loader, flag, recognizer and rewrite in `main.ts`.
- A demo with main.bend, PERF.bend and a pure route.
- A demo with an `IO` route.
- Negative tests:
  - a law of the wrong shape is rejected;
  - a route that calls `M.foo` on the same input still halts (the `.gen`
    rule);
  - an IO route with different effects fails to check.

### Can the plain guard stay fast?

Yes, when the guard is cheap. Per call, dispatch costs:

- the guard's own work;
- one compare;
- one jump.

The branch is cheap on CPU. Whether the guard is cheap is up to its author:
a guard should look at a bounded part of the input (the first constructors,
a stored size), not walk all of it. Things to measure in phase 1:

- Guard round trip: the guard takes x apart and hands it back. Check
  whether the emitted code reuses the nodes or rebuilds them; rebuilding
  would put an allocation on every call.
- Recursion: every recursive call pays the guard. With a bounded guard
  that is a constant factor per call; measure it against the route's gain.
- GPU: threads in one group that take different routes run both one after
  the other. A guard that splits a group unevenly costs more on device
  than on CPU.

## Phase 2: dropping the check

One asymmetry makes this safe:

- Skipping the check toward the general route (`M.foo.gen`) is always
  correct. The compiler may do it whenever a cost heuristic says the check
  is not worth it at a site.
- Skipping the check toward a specialized route requires knowing the guard
  says True there. Never a guess.

Three ways to know, complementary:

1. Compile-time guard evaluation. At call sites in main.bend, run the guard
   on what is statically known: constants, constructors built at the site,
   the `case` branch the call sits in. Guards are pure and checked to halt,
   so evaluating one at compile time always finishes. Needs a partial
   evaluator: the largest compiler addition of the three.
2. Producer laws. The user proves in PERF.bend that a main.bend function's
   output always passes a guard, e.g.
   `{snd(small(M.make(a))) == True : Bool}`. Wherever `foo` is fed
   `M.make`'s output, the compiler drops the check and calls the route.
   Covers results evaluation cannot see, such as `make(a)` with `a` from
   input. Reuses phase 1's law recognition.
3. Routes call `.gen`. Already true from phase 1's halting rule: inside
   PERF.bend there is no check to drop.

1 and 2 combine best as one mechanism: an evaluator that uses producer
laws as known facts when it reaches a call it cannot compute. 3 applies to
PERF.bend's own code only.

The remainder keeps the runtime check: shapes that depend on input with no
law about them. No static fact decides those.

Suggested order:

1. producer laws;
2. the general-route heuristic;
3. compile-time evaluation, then its merge with producer laws.

## Open questions

- Law syntax: the exact form of the guard hypothesis and the `same` law in
  Bend's law syntax, and the quantity modes on `x` (`+x`).
- Arity: phase 1 handles single-argument functions, or guards over all the
  arguments.
- Recognition: by shape alone, or by shape plus a naming convention.
- IO equality: confirm in WSL that the checker rejects an IO equality whose
  effects differ.
- The repo gate: `gates/repo.ts` keeps an allow list of files; this file
  and PERF.bend files would need entries there.
