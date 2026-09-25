A `!` runs on the GPU under WSL2: a CUDA device without concurrent managed access gets a twin of the corpus

## Summary

WONTFIX tells Windows users to use WSL, and a user there expects `!` to use
the GPU. Today it does not build (`cannot find -lcuda`), or, with
`LIBRARY_PATH` set, it runs on the cores without a message. This PR makes
the WONTFIX advice true.

## Terms

- **Concurrent managed access:** a CUDA device attribute
  (`CU_DEVICE_ATTRIBUTE_CONCURRENT_MANAGED_ACCESS`). With it, the host and
  the device can use one managed allocation at the same time; the CUDA lane
  on main needs it for its corpus. A GPU under WSL2 reports 0, so main's
  probe refuses it.
- **Twin:** this PR's answer for such a device. The corpus stays in host
  memory, and a second copy of it (the twin) lives in VRAM. A `!` turn
  copies what it can touch to the twin before it runs, and back after.
- **Watchdog:** Windows' display driver model (WDDM), which every WSL2 GPU
  runs under, stops any single GPU launch after about 2 s (the TDR).
- **Parking:** a lane that has used its time budget saves its state and
  stops; the next launch resumes it. So no launch reaches the watchdog,
  however long the whole `!` runs.

## Why it is safe, and why it is needed

### 1. Linux: nothing changes for existing users

On native Linux, the CPU build is byte-identical to main's, and a CUDA
device with managed access takes main's path and main's device program.

- The CPU build's assembly (`clang -O3 -S`) is byte-identical to main's for
  the 16 runtime benches and 3 tests.
- The CUDA host build contains the twin code behind `if (gpu_twin)`. On a
  device with managed access those branches never run.
- Without a twin, NVRTC (NVIDIA's runtime compiler, which builds the device
  program at `--gpu-build`) gets main's options, and the program's text
  differs from main's only where it compiles out or expands to main's
  macros (point 2).

### 2. Metal: no Metal code changed

No Metal code changed; every shared change compiles out or expands to
main's text on Metal. Please confirm on the minis (test and perf gates).

- The emitter's jumps now pass the number of registers they fill, which a
  parking lane saves: `WL_GO(F, K)` expands to `WL_JMP(F)` and
  `WL_AGAIN(F, K)` to `continue`, as before.
- The parking code is under `#if BEND_PARK`, which only the twin's NVRTC
  build sets.
- `gpu_twin` is `#define`d as `false` outside CUDA, so `POOL_ALT` (the
  signal stack's size, larger for a twin) is `SIGSTKSZ`, and `gpu_sync`
  (a twin's copies around a turn) does nothing.
- The new header words `H_PARKED` and `H_BUDGET` (`LINE + 1`, `LINE + 2`)
  are read and written only by the twin and parking code.

### 3. WSL: `!` now builds and runs on the GPU

- The build links `libcuda` against the toolkit's stub, which comes after
  the other `-L` paths; its soname is `libcuda.so.1`, so at run time the
  loader loads the driver's library.
- A device without concurrent managed access gets a twin. The heap is
  synced lazily, in 2 MB chunks: after a turn, the host downloads a chunk
  only when it touches it (a page fault), and the next turn uploads only
  the chunks the host wrote. So data that stays on the device is not
  copied back and forth.
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
- **Tested on a GPU:** on WSL2, `queens` at size 18 ran about 14 s on the
  GPU with no driver reset. With the budget forced down to 0.2 ms, so that
  lanes parked every few thousand steps, 96 rounds of parking and resuming
  gave the same results as the cores (RTX 4050 Laptop, under WDDM).

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
- **One kind of loop cannot park.** The compiler emits some pure sequential
  loops as a plain C loop (`spin_N`, from `emit_native`), which has no point
  where a lane can stop and save its state. One such loop in a `!` must
  still end within 2 s, and the README states this. For that case, a
  warning or a CPU fallback (#942) is the right fix.

## Request

Please run the gates (test and perf) on the minis for Metal, and on a
native Linux CUDA machine if one is available. These were not tested here.

## Evidence

| Check | Result |
|---|---|
| Linux CPU assembly against main (`clang 22 -O3 -S`) | 19 of 19 byte-identical |
| `!` tests on WSL2 (RTX 4050), `--gpu off` and `--gpu 512MB`, after commits 2 and 3 | 38 of 38 |
| `queens` size 18 on WSL2 (about 14 s of GPU work) | Same answer as the cores, no driver reset |
| A tree of 2^24 leaves kept on the device across four `!` turns, WSL2 | About 0.3 s |
| Parking with the budget forced to 0.2 ms, 96 resume rounds (WDDM) | Same results as the cores |

Not tested: Metal, native Linux CUDA, the perf gate.

🤖 Generated with [Claude Code](https://claude.com/claude-code)