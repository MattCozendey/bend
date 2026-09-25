A `!` runs on the GPU under WSL2: a CUDA device without concurrent managed access gets a twin of the corpus

## Summary

WONTFIX tells Windows users to use WSL, and a user there expects `!` to use
the GPU. Today it does not build (`cannot find -lcuda`), or, with
`LIBRARY_PATH` set, it runs on the cores without a message. This PR makes
the WONTFIX advice true.

## Why it is safe, and why it is needed

### 1. Linux: nothing changes for existing users

On native Linux, the CPU build is byte-identical to main's, and a CUDA
device with managed access takes main's path and main's device program.

- The CPU build's assembly (`clang -O3 -S`) is byte-identical to main's for
  the 16 runtime benches and 3 tests.
- The CUDA host build contains the twin code behind `if (gpu_twin)`. On a
  device with managed access those branches never run.
- Without a twin, the CUDA device program's cubin is identical to main's for
  queens, mandelbrot, symreg, tree-bitonic, raytrace, kmeans and array_fork
  (NVRTC 13.3, sm_89).

### 2. Metal: no Metal code changed

No Metal code changed; every shared change compiles out or expands to
main's text on Metal. Please confirm on the minis (test and perf gates).

- `WL_GO(F, K)` expands to `WL_JMP(F)` and `WL_AGAIN(F, K)` to `continue`,
  as before.
- The parking code is under `#if BEND_PARK`, which only the twin's NVRTC
  build sets.
- `gpu_twin` is `#define`d as `false` outside CUDA, so `POOL_ALT` is
  `SIGSTKSZ` and `gpu_sync` does nothing.
- The new header words `H_PARKED` and `H_BUDGET` (`LINE + 1`, `LINE + 2`)
  are read and written only by the twin and parking code.

### 3. WSL: `!` now builds and runs on the GPU

- The build links `libcuda` against the toolkit's stub, which comes after
  the other `-L` paths; its soname is `libcuda.so.1`, so at run time the
  loader loads the driver's library.
- A device without concurrent managed access (WSL2's, under WDDM) gets a
  twin: a copy of the corpus in VRAM, synced in lazy 2 MB chunks.
- 38 of 38 `!` tests pass on WSL2 (RTX 4050, CUDA 13.3), with
  `--gpu off` and `--gpu 512MB`.

### 4. Why parking is needed, despite the comment on #1012

- **A different problem.** #1012 was about a `!` with no parallelism on
  Metal. Here the program is parallel, and Windows' display driver (WDDM,
  which every WSL2 GPU uses) stops any launch after about 2 s. The
  maintainer's fixes do apply, but they give up the GPU:
  - "Use the CPU" would move every long-running `!` on WSL to the cores, so
    WSL users would still not have the GPU for real work (point 5).
  - "Fail cleanly" is in this PR (the watchdog message), but by itself it
    would stop the program instead of finishing it.
  - Parking is the only one of the three that lets a long, parallel `!`
    finish on the GPU under a 2 s limit.
- **No cost for others.** Parking is compiled only for a twin
  (`-DBEND_PARK`). Metal and Linux with managed access run main's device
  program.
- **Simpler than #1012:** no new task tag, no call-graph pass, no fuel
  constant and no build knob. The budget is time, read from `%globaltimer`.
- **Tested on a GPU:** 96 forced resume rounds matched the cores, and 15 s
  of real GPU work caused no driver reset (RTX 4050 Laptop, under WDDM, the
  driver model WSL2 uses).
- **Agreed in advance:** the two-phase plan was agreed with @nicolas-abril
  on Discord.

### 5. WONTFIX sends Windows users to WSL

WONTFIX says "Use WSL", and a user there expects `!` to use the GPU. Today
it does not build, or it runs on the cores without a message. This PR
makes the WONTFIX advice true.

## The commits

1. A `!` program links libcuda against the toolkit's stub where the
   driver's is off the linker's path.
2. A `!` runs on a CUDA device without concurrent managed access: the corpus
   gets a twin.
3. A twin's GPU lanes park at a budget, so no launch meets the display
   driver's watchdog.
4. A twin's frame fills on the device, and a chunk the host only reads stays
   clean.
5. The twin's Windows side, under `_WIN32`: a shared section,
   `VirtualProtect` and a whole read of the `.gpu`.

## Review notes

- **The SIGSEGV handler calls CUDA.** It is safe here because only a host
  touch of a stale chunk causes that fault, on the thread that touched it.
- **CUDA now has two memory models.** The twin runs only when the device
  reports no concurrent managed access; everything else is main's.
- **The twin duplicates the HIP lane's design (#891).** It follows the same
  design on the CUDA driver API; a shared twin layer is possible if HIP
  merges.
- **Parking depends on `gpu_twin`, not on the watchdog attribute.** A Linux
  desktop that shows X on the GPU does not get it yet.
- **A pure spin cannot park.** One sequential loop compiled as a native spin
  (`spin_N`) must still end within 2 s; the README states this. For that
  case, "warn or use the CPU" (#942) is the right fix.

## Request

Please run the gates (test and perf) on the minis for Metal, and on a
native Linux CUDA machine if one is available. These were not tested here.

## Evidence

| Check | Result |
|---|---|
| Linux CPU assembly against main (`clang 22 -O3 -S`) | 19 of 19 byte-identical |
| `!` tests on WSL2 (RTX 4050), `--gpu off` and `--gpu 512MB` | 38 of 38 |
| `_WIN32` groups removed: commit 5's emitted C against commit 4's | 274 of 274 identical |
| `queens` size 18 on the GPU (about 15 s of GPU work; WDDM) | Same answer as the cores, no driver reset |
| Forced parking (0.2 ms budget), 96 resume rounds (WDDM) | Same results as the cores |

Not tested: Metal, native Linux CUDA, the perf gate.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
