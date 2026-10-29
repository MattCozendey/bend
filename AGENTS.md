# AGENTS

Bend is a dependently typed, affine language that checks in one linear
bidirectional pass and runs massively parallel on CPU threads and GPUs.
bend2/bend.ts is the language (parser, theory, checker) and is human-written:
do not edit it. bend2/comp.ts is the one compiler: the C runtime (host and
device from one source), the C emitter and the JS emitter; base.bend is the
prelude; main.ts is the CLI. Every test is a Bend file that ends in the `#|`
lines its run must print, and the gates run on the mini cluster.

    bend2/bend.ts       the language: parser, theory, checker
    bend2/comp.ts       the compiler and the runtimes (C, Metal, CUDA, JS)
    bend2/main.ts       the CLI; imported, the .bend loader for bun and node
    bend2/safe.ts       --verdict and -o <out>.bendtt: the elaborator from a
                        checked book to BendTT text
    bend2/bendtt.lean   BendTT: the kernel, its claims (no checked def has type
                        Empty, live code halts) and their proofs; --verdict
                        builds its CLI once, with Lean v4.34.0
    bend2/base.bend     the base library
    bend2/effs/         IO effect sources per backend; related effects may share
    bend2/pack/         package.json, tsconfig.json, bun.lock
    bend2/docs/         the papers' Typst sources, the film, gen_pins.ts (the
                        record pins on this Mac), gen_charts.ts (the landing
                        page's and the film's numbers), gen_gifs.ts (the images)
    bench/runtime/      one dir per bench: main.bend and its twins (C, TS, Lean)
    bench/checker/      one dir per bench: main.bend and its rivals
    bench/*/_pin_/      the pins, one file per hardware: apple_m4 the gate's,
                        apple_m4_max the record
    tests/<ns>/         the tests by namespace, with their foreign .c/.js
    gates/test.ts       every test, one shard per live mini, PASS: n / n
    gates/perf.ts       the benches on 48 minis against the pins (--pin writes
                        the medians of three runs)
    gates/repo.ts       the allow list of files and the permanent ttok caps
                        (bend.ts 48k, comp.ts 66k, main.ts 16k, bendtt.lean
                        64k, README 4k, GUIDE 8k); only Taelin changes them
    gates/ping.ts       the installer, the compiled bend, its daily version
                        check and a release, on a localhost hub
    gates/safe.ts       bend2's verdict against BendTT's, per file, on the
                        minis: `tests` or `hub` (a BendHub store, $SAFE_HUB)
    gates/_run.ts       the four gates with --gate
    demos/              one dir per demo
    guide/              GUIDE.md
    paper/              BendTT.pdf, BendRT.pdf
    media/              the film and the charts
    .github/            ISSUE_TEMPLATE/bug.yml, the bug report form, and
                        config.yml, which points questions at Discord
    ../bend-lang.com    the site repo (bendlang/bend-lang.com), a sibling
                        checkout: the sites, install.sh, the hub, release.ts
                        (the executables per platform) and the droplet ops;
                        gates/ping.ts and gen_charts.ts read it there (or at
                        $SITE_REPO)

# AGENT NOTE: THIS IS A WINDOWS FORK FROM AN INDEPENDENT MANTAINER. WE ARE EXPLICTLY EXEMPT FROM THE TOKEN CAPS (THOUGH IT'S PREFERABLE IF WE REMAIN UNDER IT) AND LIMITS ON WHAT FILES TO TOUCH(WE CAN INDEED TOUCH BEND.TS). DON'T RUN THE GATES THEY TAKE FOREVER AND FREEZE MY MACHINE. IF NEED TO RUN TESTS PICK SMALL REPRESENTATIVE SAMPLE.

# The Windows fork

feature/cuda-and-windows is main plus one commit, Windows support. On Linux
and macOS the fork runs main's code, byte for byte; Windows differs only to
make up for what Windows lacks. A new main means rebuilding that one commit
on it, from a fresh branch off main, not merging; the branch keeps its name.

- Kept as they are: .gitattributes (LF: the emitter's macros continue lines
  with a backslash), .github/workflows/upstream-sync.yml, the note above, and
  the README and WONTFIX changes.
- The token caps do not apply to the fork; gates/repo.ts raises comp.ts's
  only so the repo gate passes.
- Every Windows change sits behind a gate, main's lines untouched beside it:
  - C (comp.ts's runtime, effs/*.c): `#ifdef _WIN32` ... `#else` main's
    lines `#endif`. An alias may stand for main's text where it expands to
    it off Windows (sock_close is close there).
  - The CUDA twin: BEND_TWIN, which a Windows CUDA build defines and passes
    to NVRTC with its device program (gpu_make); DEVICE splits host from
    device.
  - TS and JS (main.ts, bend.ts, comp.ts's JS runtime, effs/*.js, gates/):
    a `process.platform === "win32"` arm (Bend.WIN, lib.LOCAL) whose other
    side is main's expression; Bend.path_slash is the identity off Windows.
    A function Windows reworks whole gets a Windows twin (cli_build_win) and
    main's stays as it is.
- What Windows may change: what stands in for something Windows lacks, as
  the OS's services (memory, threads, sockets, waits, processes, windows,
  audio) and Win64's ABI. The twin is one: WDDM gives no concurrent managed
  access, so the corpus has a twin in VRAM that a turn copies, and its heap
  split (the host's pages from the bottom, the lanes' from the top) exists
  only to make those copies small. A change that would speed up main too
  belongs upstream, not here.
- WSL2 is Linux: it runs main's code, which refuses the GPU there (no
  concurrent managed access) and runs ! on the cores.
- Main's tests are never edited. On Windows the test gate skips WIN_SKIP
  (gates/test.ts) and runs the _win tests, Windows' versions of those;
  elsewhere a _win test never runs.
- The proof: `bun gates/win.ts [dirs]` (a few minutes) emits every program
  with main's compiler and the fork's, preprocesses each Linux and macOS
  lane's C (the CPU's, CUDA's host and device, Metal's host and device) and
  must PASS with 0 mismatched. It prints the JS hunks: each must be a win32
  arm or a function only Windows calls.
- Speed: Windows stays at least as fast as the fork's previous Windows
  build: the runtime benches on the cores and on the twin, and the slash
  boss demo's frame (SLASH_PROBE). The machine is in use while it measures:
  interleave old and new, run each several times, compare medians.