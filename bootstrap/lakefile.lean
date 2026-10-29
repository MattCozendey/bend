import Lake
open Lake DSL System

-- Bootstrap
-- =========
--
-- The verified compiler. Its proofs read the kernel itself: Kernel.lean is
-- bend2/bendtt.lean minus its Main section, regenerated on every build, so
-- a module that imports it can declare its own main. Nothing else differs.

package bootstrap

-- the kernel's Main section, exactly as bendtt.lean has it: the only text
-- the copy leaves out. If it changes there, the build fails until this is
-- updated by hand, after checking the change touches nothing but main.
def Kernel.cut : Array String := (r#"-- Main
-- ====

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let s ← IO.FS.readFile path
    match Book.parse s >>= Book.check with
    | .ok _ =>
      IO.println "ALL PROOFS CHECK"
      pure 0
    | .error e =>
      IO.println ("SOME PROOFS FAIL\n" ++ e)
      pure 1
  | _ =>
    IO.println "usage: bendtt <file.bendtt>"
    pure 2
"#.splitOn "\n").toArray

-- bendtt.lean's text, its Main section cut out; fails unless that section
-- appears in it exactly once, unchanged
def Kernel.strip (text : String) : Except String String := do
  let ls := (text.splitOn "\n").toArray
  let n := Kernel.cut.size
  let cut_at (i : Nat) := (List.range n).all fun k =>
    ls[i + k]? == some Kernel.cut[k]! || ls[i + k]? == some (Kernel.cut[k]! ++ "\r")
  let [i] := (List.range ls.size).filter cut_at
    | throw "expected the Main section once, unchanged (see Kernel.cut)"
  let head := "-- GENERATED from bend2/bendtt.lean by bootstrap/lakefile.lean,\n"
    ++ "-- with its Main section cut out. Do not edit.\n\n"
  return head ++ "\n".intercalate (ls.extract 0 i ++ ls.extract (i + n) ls.size).toList

target kernel pkg : FilePath := do
  let out := pkg.dir / "Bootstrap" / "Kernel.lean"
  let src ← inputTextFile (pkg.dir / ".." / "bend2" / "bendtt.lean")
  src.mapM fun src => do
    match Kernel.strip (← IO.FS.readFile src) with
    | .error e => error s!"{src}: {e}"
    | .ok text =>
      let old ← if ← out.pathExists then IO.FS.readFile out else pure ""
      if old != text then
        IO.FS.createDirAll (pkg.dir / "Bootstrap")
        IO.FS.writeFile out text
      return out

-- the hash of Bootstrap/Spec.lean, the contract, after a review. A change
-- to the contract fails the build until this is updated by hand, so each
-- change shows in review as a change to this line.
def Spec.pin : UInt64 := 14227108132861646865

-- the contract's text, line endings made LF, so a checkout's CRLF keeps
-- its hash
def Spec.hash (text : String) : UInt64 :=
  Hashable.hash (text.replace "\r\n" "\n")

target spec pkg : Unit := do
  let src ← inputTextFile (pkg.dir / "Bootstrap" / "Spec.lean")
  src.mapM fun src => do
    let h := Spec.hash (← IO.FS.readFile src)
    unless h == Spec.pin do
      error s!"{src} changed. Review it, then set Spec.pin in lakefile.lean to {h}"

@[default_target]
lean_lib Bootstrap where
  globs := #[.submodules `Bootstrap]
  needs := #[`@/kernel, `@/spec]

@[default_target]
lean_exe bootstrap where
  root := `Main
  needs := #[`@/kernel]
