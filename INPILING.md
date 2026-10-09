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

A rule is a PERF `law` (an equality a `def` states in its own type is a
lemma, never a rule) whose type is
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
   - Only laws are rules: a proof lemma of a rule's shape (`rev_go_app`
     in the demo, a producer rule's shape) is never switched on, which
     would put main on code written only to prove something.
     `--check-only` lists the routes it found, so a near miss is visible:

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
  (with the deep check), producer rules, the switch, the route listing.
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

### Producer rules

A producer rule switches a call by its shape: f called on what a
producer p returns.

    law lookups.built:
      for k: Nat
      for +i: U32
      for +d: Nat
      for +lo: U32
      for acc: U32
      {M.lookups(k, i, M.build(d, lo), acc) == lookups_built(k, i, d, lo, acc) : U32}

- The left side is a call of a def outside PERF.bend and Base whose
  arguments are rule variables or calls of defs outside PERF.bend on rule
  variables, at least one such call. A variable may fill several slots on
  the left when they have one mode and type (`sort(d, s, gen(d, i))`).
  The right side is a PERF def applied to the rule variables, each once,
  in any order. Each of its parameters has the type and mode of the slot
  its variable fills on the left; else the rule is an error.
- `perf_match` switches, in the same main code as a plain rule (outside
  the code the routes reach), every call whose producers sit in their
  slots and whose repeated variables meet the same term (terms are pure:
  the same term, the same value; a different spelling of one value keeps
  the call); the first producer rule in file order wins, and a call that
  matches none falls to f's plain rule, if any. The halting argument does
  not change: a route only runs original, checked code.
- The listing shows it: `- lookups(_, _, build(..), _) ->
  PERF.lookups_built (producer)`.

In perf_tree_array, main reads `build(d, 0)`'s tree, so the producer
route builds the Array directly (`build_arr`, proven equal to
`to_arr(build(..))` by one induction): no Tree, no conversion, no guard
(build's trees are perfect). The compiled C holds no `build`. Times
(WSL, C; same answers):

      depth  reads   plain     convert route   producer route
      22     1M      0.58 s    0.20 s          0.08 s
      22     10M     4.53 s    0.20 s          0.14 s
      24     1M      1.04 s    0.77 s          0.36 s

### Data from a file: demos/perf_file_lookup

The routes above mostly meet data the program built itself. Here the data
is read: main.bend reads numbers from a file, one per line, pairs them
level by level into a balanced Tree (the natural bottom-up build) and
sums k scattered reads, as perf_tree_array does. The tree is perfect
exactly when the file holds 2^n numbers, so the route's guard decides
from the data at run time. PERF.bend is perf_tree_array's route and
proofs, unchanged.

Two files of random numbers below 2^31: 2^20 lines (perfect) and
1,000,000 lines (lopsided). Every answer below matches a Python model of
main's own tree and reads. WSL, C, CPU; about 0.5 s of each run is
reading and parsing the 12 MB file:

      file        reads   plain     inpiled
      2^20        1M      1.08 s    0.51 s
      2^20        10M     4.14 s    0.49 s
      2^20        50M     17.84 s   0.58 s
      1,000,000   1M      0.79 s    0.76 s
      1,000,000   10M     4.02 s    4.12 s
      1,000,000   50M     18.11 s   15.61 s

The perfect file takes the Array, about 30x the plain run at 50M reads;
the lopsided one keeps main's lookups either way, as the guard says.
There is no test case for it: a test is .bend files only, and the
tree-array case already takes both of the guard's answers.

### An existing demo: pure_par_sort

`demos/pure_par_sort` is the repo's own bitonic sort, untouched: main
sorts `gen(16, 0)`'s tree of 2^16 numbers and checks it ascends. gen
always builds one block of consecutive numbers, descending, so its
PERF.bend holds one producer rule:

    law sort.gen:
      for +d: Nat
      for +s: Bool
      for +i: Nat
      {M.sort(d, s, M.gen(d, i)) == sorted(d, s, i) : M.Tree(d)}

`sorted` is the block ascending (`asc`, one pass, no compare) when s is
up, and gen's tree itself when down. The proof follows the bitonic sort
on such blocks with no arithmetic on the leaves' values beyond `<` on
block numbers:

- `LT` and four facts: k < j keeps 2k < 2j, 2k + 1 < 2j, 2k < 2j + 1,
  and n < n + 1;
- three mix lemmas: a mix of two blocks that do not overlap keeps one
  block whole, the lesser up and the greater down;
- two flow lemmas: a sorted block, either way, flows into the block
  sorted by s;
- sort_gen: the halves sort to an ascending upper block and a descending
  lower one, which flow merges.

The compiled C holds no `sort`, `flow` or `mix`. WSL, C, CPU: plain
0.12 - 0.14 s and 14 MB, inpiled under 0.01 s and 3 MB; both print
`sorted`, and the demo's own PROOF.bend still checks.

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
    tree-array          build's tree takes the producer route, a lopsided
                        one the plain route's fallback: same sums
    producer-route      show on via's list switched to a route that never
                        builds it (an IO producer rule)
    producer-type       a producer route whose parameter mode differs from
                        its slot's: refused
    sort-gen            pure_par_sort at depth 6: a producer rule naming
                        d twice, sort(d, s, gen(d, i))
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
- Producer rules: built (above). A rule over a call pattern switches only
  calls of f on a producer's output, straight to the shape's algorithm
  with no guard, even when the producer's inputs come from input.
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

## TODO

- Report to the maintainers, as a GitHub issue: the runtime can drift
  from the checked program. An `ANode` whose two halves differ in size
  checks (Bend's `Array` definition allows it) but stops the compiled
  program (`bend: runtime fail-stop`); found building
  `ANode{ALeaf{0}, a}` in a benchmark, and the reason
  perf_tree_array's route checks the tree is perfect. The Array
  intrinsics (`Array.get`, `set`, `swap`, `size`, `new`) are trusted to
  match their Bend definitions the same way.

## Open questions

- Test layout for PERF pairs, and the with/without-PERF comparison in the
  gate.
- The repo gate: `gates/repo.ts` keeps an allow list of files; this file,
  the demo and PERF.bend files would need entries there.
- The deep check reads parts of a parameter through matches only; a
  route that takes its input apart some other way (a let of a pair, a
  helper) gets the top call. Widen it if a real route needs it.
