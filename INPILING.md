# Inpiling

Inpiling lets a user give a function a second, faster route for inputs of a
particular shape, prove it equivalent, and have the compiler take it, without
main.bend knowing it exists.

    main.bend    the program as written: the general, readable code
    LAWS.bend    what the program must satisfy
    PROOF.bend   the proofs of LAWS.bend
    PERF.bend    the routes, and the proofs that each route agrees with
                 the main.bend function it stands in for

The meaning lives in main.bend; the speed lives in PERF.bend. Deleting
PERF.bend changes how fast the program runs, never what it prints.

## Working rules

- On Windows, everything runs in WSL: builds, tests, benches, any command.
  This is non-negotiable.
- Never run the full gates (`gates/_run.ts`, `gates/test.ts`,
  `gates/perf.ts`, `gates/safe.ts`, `gates/ping.ts`); they may be too much
  for the machine. Run single tests or demos, and ask before running any
  gate.
- Run `--verdict` conservatively: it builds and runs the Lean kernel and
  is very expensive. Use `--check-only` day to day; run `--verdict` only
  when a change needs the kernel's answer, one file at a time.

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

## Phase 1: proof of concept (built)

Status: built and checked in WSL. The design changed from the first draft:
the user writes the dispatch inside PERF.bend (the one place an `if` is
allowed), and the compiler generates nothing. A rule is one total
equivalence; the compiler only switches calls.

### What the user writes (PERF.bend only)

    import Base
    import ./main.bend as M

    # the route: any code, usually a match on the input's shape; it may
    # fall back on M.foo, the function main.bend wrote
    def foo_fast(x: Bar) -> T:
      ...

    # the rule: the route equals foo on every input
    law foo.fast:
      for +x: Bar
      {M.foo(x) == foo_fast(x) : T}

    def foo.fast(x):
      ...   # the proof

A rule is any PERF def or law whose type is
`{f(x0, .., xn) == g(x0, .., xn) : T}`, quantified over all of f's
parameters in order, where:

- f is a def outside PERF.bend and Base;
- g is a PERF def with exactly f's type (parameter modes included).

One function takes at most one route; several shapes go in one route's
match. Rules may have any number of parameters, and may be proven with
other rules (`report.fast` in the demo uses `rev.fast`).

### What the compiler does

1. Load (`perf_load`): when the file is a main.bend with a PERF.bend
   beside it, load PERF.bend into the same book under the namespace
   `PERF` and check everything together. PERF.bend must import
   ./main.bend; main.bend must not import PERF.bend. `--no-perf` skips it.
2. Recognize (`perf_rules`): collect the rules.
   - A rule whose route has another type than f is an error.
   - A rule that relies on an @unsafe or foreign def is refused.
   - Other lemmas, even ones that look alike (`rev_go_app` in the demo),
     are not rules. `--check-only` lists the routes it found, so a near
     miss is visible:

         ALL PROOFS CHECK
         PERF routes:
         - rev -> PERF.rev_fast (every call)
         - report -> PERF.report_fast (every call)

   Each route says whether it takes every call of f or the top call only
   (see the halting rule).

3. Switch (`perf_inpile`), for runs and builds only, never for
   `--check-only`, `--verdict` or `-o x.bendtt`, which see the program as
   checked. Every reference to a rule's f, in every def outside PERF.bend
   and Base that the routes do not reach, becomes a reference to its g;
   so does an f's reference to itself when its rule passes the deep check
   (below). The decision is `perf_plan`, which the route listing reads
   too.
   Both the checked body (`e`, which the emitters compile) and the value
   (`v`, which the interpreter runs) are switched.
4. Emit as usual. C, Metal, CUDA and JS get the switched book with no
   emitter or runtime change.

### The halting rule

The checker proves each def halts, but the switch builds a call graph it
never saw. The rule: code the routes reach keeps its own calls.

- A route that falls back on `M.foo` runs the foo main.bend wrote.
- A route that reaches foo through other main.bend code (route -> M.via
  -> M.foo) does not loop either: M.via is reached by the route, so its
  call stays on the original foo.
- Main code outside that set calls routes; a route only ever runs
  original, checked code, so every call into a route returns.

So when a route falls back on M.foo, foo's own recursive calls would stay
on foo, and the route would apply only at the top call. Switching them
blindly is not safe: a route equal to foo may call foo on a larger input
(sum(xs) as sum(xs ++ [0])), and the switched program would never stop.

The deep check (`perf_deep`) switches foo's self-calls too when the loop
foo -> route -> foo provably shrinks:

- in the route's reach, only the route names foo, and no other rule's f
  is there;
- every call `M.foo(a0, .., an)` in the route passes, in each live column
  j, the route's own parameter j or a part of it (a field of a match on
  it), the way Bend's descent check reads columns; erased columns may pass
  anything.

foo's self-calls shrink its arguments (the checker proved it), and the
route never grows them, so each trip around the loop shrinks them and the
trips end. A route that fails the check is still a route, for the top
call; the listing says `(top call)`. A route that never reaches foo takes
every call with no check needed. Bend lets a def call only defs declared
before it and itself, so foo's self-calls are the only ones in its body
that can lead back to foo.

### IO

- A function returning `IO(A)` takes rules like any other. IO is a
  continuation-passing value whose primitives are opaque to the checker,
  so an equality between two IO programs holds only when both perform the
  same effects with the same arguments in the same order. Confirmed: a
  route that adds one `IO.print` fails its proof.
- A route can speed up the pure work between effects; it cannot reorder,
  batch or merge effects.
- IO functions in main.bend also benefit from pure rules with no IO rule
  at all: their calls of a ruled pure function are switched.

### Where the changes went

- `bend2/bend.ts` (three small edits, in `book_load`, `parse_reso` and
  `name_show`): an import of a file already loaded as the
  root aliases the namespace that file lives in, so PERF.bend's `M.foo`
  resolves to main.bend's root `foo`; error messages keep root names bare.
- `bend2/main.ts`: the loader, `--no-perf`, rule recognition, the plan
  (with the deep check), the switch, the route listing.
- No change to the checker's rules, the emitters or the runtimes.

### The demo: demos/perf_reverse

- main.bend: `rev` written the plain way (quadratic), and `report`, an IO
  function that prints the head of `rev(xs)`. main reverses a range of the
  length given on the command line (default 20000) and reports it.
- PERF.bend: `rev_fast` (accumulator, linear) and `report_fast`, with the
  proofs: `app_nil`, `app_assoc`, `rev_go_app`, then the rules `rev.fast`
  and `report.fast`.
- Results (WSL, C build, three runs each; both print 0):

      length     plain (--no-perf)   inpiled
      20000      1.42 - 1.50 s       < 0.01 s
      40000      6.00 - 6.06 s       < 0.01 s
      1000000    -                   0.03 s
      4000000    -                   0.10 s

  The default run (`bend main.bend`, 20000): 7.49 s plain, 0.19 s
  inpiled. The JS build takes the route too.
- The length comes from the command line on purpose: with a constant
  input, the compiler folds the whole linear program at compile time,
  which hides the runtime comparison.

### Every-call routing: pow2

`tests/perf/pow2-every-call`: main.bend's `pow2(1+p)` adds `pow2(p)` to
itself with two calls, so it takes 2^n steps; the route matches n and
calls `M.pow2(p)` once. The route passes the deep check, so pow2's own
calls switch too and every level takes the route: n steps. The same
program with the exponent from the command line (WSL, C build):

      n     plain (--no-perf)   inpiled
      20    0.00 s              0.00 s
      24    0.05 s              0.00 s
      26    0.24 s              0.00 s

Without the deep check the route would take the top call only and save
one call of 2^n.

### Another representation: demos/perf_tree_array

A route may hand the data to a very different structure and back, as long
as the result is proven equal.

- Bend's `Array` is logically a binary tree (`ALeaf`/`ANode`) and a
  contiguous buffer at run time: the compiler turns `Array.get`, `set`,
  `swap`, `size` and `new` into direct buffer access (`OPERATIONS` in
  comp.ts). Their Bend definitions are the specification proofs read.
- Measured first (WSL, C, answers checked against Python): reads by index
  are where contiguity pays. k scattered reads cost 15.4 s on a 262144
  element List for k = 10000, and 0.05 s on an Array for k = 100M. A sum
  over 4M elements, 100 passes: List 4.9 s, Array read by index 0.11 s,
  but an Array walked like a tree (matching `ALeaf`/`ANode` and handing it
  back) 8.0 s, slower than the List.
- main.bend keeps a sequence as a perfect binary `Tree` and reads it the
  way a perfect tree is read: wrap the index to the size, descend by
  comparing with the half size. `lookups` sums k reads.
- PERF.bend's route checks the tree is perfect, turns it into an `Array`
  once (`to_arr`, node for node), and reads with `Array.get`; any other
  tree keeps `M.lookups`. The guard is for the run time: an `ANode` whose
  halves differ in size stops the program, which the checker cannot see
  (the Bend definition allows it).
- The proofs need no U32 arithmetic lemma: `Array.get` reads its tree with
  the same `shr`, `sub`, `is_lt` and `and` that `tree_get` uses on the
  Tree, so each lemma (`size_arr`, `go_arr`, `get_arr`, `lookups_arr_eq`,
  `pick_eq`) is a plain induction where both sides compute the same.
- Results (WSL, C build; same answers both ways):

      depth  reads   plain (--no-perf)   inpiled
      18     1M      0.11 s              0.01 s
      18     10M     1.08 s              0.02 s
      22     1M      0.58 s              0.17 s
      22     10M     4.53 s              0.20 s

  At depth 22 the conversion (4M leaves) is most of the inpiled time.

### Tests: tests/perf

One directory per case (lowercase, digits and hyphens: the repo gate's
allow line for `tests/<ns>/<dir>/<Name>.bend`), each a main.bend, its
PERF.bend, and the `#|` lines its run must print at the end of main.bend;
a case may add `#?` lines, what `--check-only` must print (the route
listing, with each route's kind).
The test gate reads only the `.bend` files directly in `tests/<ns>/`, so
it skips these directories; they run by hand, and the gates stay as they
are.

    rev-route           a pure rule and an IO rule proven with it
    via-halts           a route reaching dbl through main's via: halts,
                        top call
    pow2-every-call     a route calling pow2 on n's predecessor: every call
    grow-top-call       a route calling pow2 on same(n), not a part of n:
                        top call
    tree-array          a perfect tree read through an Array, a lopsided
                        one through main's lookups: same sums
    io-extra-print      an IO route with one more print: its proof fails
    unsafe-route        a route relying on @unsafe code: refused
    wrong-type          a route whose parameter mode differs: refused
    two-routes          two routes for one function: refused
    main-imports-perf   main.bend imports PERF.bend: refused
    perf-no-import      PERF.bend does not import ./main.bend: refused

A passing case prints its `#|` lines with and without PERF.bend; a failing
case (its `#|` lines start with `SOME PROOFS FAIL` or `Error:`) prints
them with it. In WSL, from the repo root:

    for d in tests/perf/*/; do
      tidy() { tr -d '\r' | sed 's/[ \t]*$//'; }
      want=$(grep '^#|' "${d}main.bend" | sed 's/^#|//' | tidy)
      got=$(bun bend2/main.ts "${d}main.bend" 2>&1 | tidy)
      case "$want" in
        "SOME PROOFS FAIL"*|Error:*) bare=$want ;;
        *) bare=$(bun bend2/main.ts "${d}main.bend" --no-perf 2>&1 | tidy) ;;
      esac
      ask=$(grep '^#?' "${d}main.bend" | sed 's/^#?//' | tidy)
      [ -z "$ask" ] || seen=$(bun bend2/main.ts "${d}main.bend" --check-only 2>&1 | tidy)
      [ "$got" = "$want" ] && [ "$bare" = "$want" ] \
        && { [ -z "$ask" ] || [ "$seen" = "$ask" ]; } \
        && echo "PASS $d" || echo "FAIL $d"
    done

### Not done yet

- `--verdict` on the demo (it builds the Lean kernel CLI; see Working
  rules).
- Templates: a def with ~ parameters cannot be a rule's f or g yet (phase
  3).

## Phase 2: fewer checks, more routes

The guard now lives in the user's route, so the compiler cannot drop it by
looking inside. The phase 2 ideas carry over as more specific rules:

- The general route is always correct: the compiler may keep a call on f
  wherever it judges the route not worth it.
- Producer rules: a rule over a call pattern, e.g.
  `{M.foo(M.make(a)) == foo_small(M.make(a)) : T}`, switches only calls of
  foo on make's output, straight to the shape's algorithm with no guard.
  It covers results whose shape the code decides, even when `a` comes from
  input, and reuses phase 1's recognition with a pattern in place of plain
  variables.
- Compile-time evaluation: the compiler already folds whole programs on
  constant input (seen in the demo); a route on constant input folds with
  it.
- Self-call routing: built (the deep check, in phase 1 above).

The remainder keeps the route's own check: shapes that depend on input
with no rule about them.

## Phase 3: templates

A def with ~ parameters is a template: each call with concrete ~
arguments mints a checked instance (`def_inst`), and main's code calls
the instances, not the template. Erased parameters (`-A: Type`) are plain
parameters and need none of this.

- Rules: let a rule's law take ~ clauses, with f and g templates of the
  same type.
- Switch: for each instance of f that main's code calls (`book.tmps`
  lists them), mint and check g's instance at the same ~ arguments, and
  switch the call to it.
- Unknown: whether a checked book keeps each instance's ~ argument terms;
  if not, `bend.ts` keeps them.

Small (tens of lines). Waits for a real program with a higher-order
function of its own that wants a route.

## Open questions

- Test layout for PERF pairs, and the with/without-PERF comparison in the
  gate.
- The repo gate: `gates/repo.ts` keeps an allow list of files; this file,
  the demo and PERF.bend files would need entries there.
- The deep check reads parts of a parameter through matches only; a
  route that takes its input apart some other way (a let of a pair, a
  helper) gets the top call. Widen it if a real route needs it.
