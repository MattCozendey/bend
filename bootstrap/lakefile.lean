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

-- Pins
-- ====

-- each reviewed file, and the hash of its text after the review. A change
-- to a file fails the build until its pin is updated by hand, so each
-- change shows in review as a change to its line here.
-- - Spec.lean: the contract.
-- - Final.lean: the claims, stated for what the CLI runs, and the guards.
-- - Guard.lean: the guards' code.
-- - Main.lean: the glue that no proof covers.
def Pins : List (String × UInt64) := [
  ("Bootstrap/Spec.lean", 14227108132861646865),
  ("Bootstrap/Final.lean", 4680035673247075582),
  ("Bootstrap/Guard.lean", 9896677752811532416),
  ("Main.lean", 1594596338706852610)]

-- a file's text, line endings made LF, so a checkout's CRLF keeps its hash
def Pin.hash (text : String) : UInt64 :=
  Hashable.hash (text.replace "\r\n" "\n")

target pins pkg : Unit := Job.async do
  let mut bad := #[]
  for (path, pin) in Pins do
    let h := Pin.hash (← IO.FS.readFile (pkg.dir / path))
    unless h == pin do
      bad := bad.push s!"{path} changed. Review it, then set its pin in lakefile.lean to {h}"
  unless bad.isEmpty do
    error ("\n".intercalate bad.toList)

-- Scan
-- ====

-- the words that let code run past a proof. The scan reads the code of
-- Main.lean and Bootstrap/*.lean, but not the kernel copy and not comments.
-- It is an extra: Final.lean's guards are the main check.
def Scan.words : List String :=
  ["sorry", "admit", "native_decide", "implemented_by", "@[extern", "axiom ",
   "partial def", "unsafe def", "opaque "]

-- the words in the code part of a line (before "--")
def Scan.line (l : String) : List String :=
  let code := (l.splitOn "--").headD ""
  Scan.words.filter fun w => (code.splitOn w).length > 1

target scan pkg : Unit := Job.async do
  let mut files := #[pkg.dir / "Main.lean"]
  for e in ← (pkg.dir / "Bootstrap").readDir do
    if e.fileName.endsWith ".lean" && e.fileName != "Kernel.lean" then
      files := files.push e.path
  let mut bad := #[]
  for f in files do
    for l in (← IO.FS.readFile f).splitOn "\n" do
      for w in Scan.line l do
        bad := bad.push s!"{f}: {w}: {l}"
  unless bad.isEmpty do
    error ("\n".intercalate bad.toList)

@[default_target]
lean_lib Bootstrap where
  globs := #[.submodules `Bootstrap]
  needs := #[`@/kernel, `@/pins, `@/scan]

@[default_target]
lean_exe bootstrap where
  root := `Main
  needs := #[`@/kernel, `@/pins, `@/scan]
