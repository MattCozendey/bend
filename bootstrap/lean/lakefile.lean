import Lake
open Lake DSL

-- Both libraries are also built to native code (precompileModules), with the
-- clang of the Lean toolchain, and `lake lean` runs a script's #eval with it:
-- the same definitions, about 20 times faster than in Lean's interpreter (the
-- reader on its own book: 56 s with `lake env lean`, 2.9 s with `lake lean`).
package bootstrap

-- the kernel, bend2/bendtt.lean, read in place and unchanged
lean_lib Kernel where
  srcDir := "../../bend2"
  roots := #[`bendtt]
  precompileModules := true

-- the paths of the library's files: a new file changes them, so the root
-- builds again, and its guard sees the file
target paths : Unit := Job.sync do
  let fs ← System.FilePath.walkDir (__dir__ / "src" / "Bootstrap")
  setTrace (.ofHash (Hash.ofString ("\n".intercalate ((fs.map toString).qsort (· < ·)).toList)))

-- its root, src/Bootstrap.lean, imports each module and ends with the guard
@[default_target]
lean_lib Bootstrap where
  srcDir := "src"
  roots := #[`Bootstrap]
  needs := #[paths]
  precompileModules := true
