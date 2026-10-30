import Lake
open Lake DSL System

-- Bootstrap
-- =========
--
-- The verified compiler. Its proofs read the kernel itself: src/Kernel.lean
-- is bend2/bendtt.lean minus its Main section, so a module that imports it
-- can declare its own main. Nothing else differs. The copy is committed so
-- that Lake can read its header before any target runs; every build checks
-- that it is exactly that text, and `lake run regen` writes it.

package bootstrap where
  srcDir := "src"

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

-- a file's text, line endings made LF, so a checkout's CRLF changes nothing
def LF (text : String) : String :=
  text.replace "\r\n" "\n"

-- bendtt.lean's text, its Main section cut out; fails unless that section
-- appears in it exactly once, unchanged
def Kernel.strip (text : String) : Except String String := do
  let ls := ((LF text).splitOn "\n").toArray
  let n := Kernel.cut.size
  let cut_at (i : Nat) := (List.range n).all fun k => ls[i + k]? == some Kernel.cut[k]!
  let [i] := (List.range ls.size).filter cut_at
    | throw "expected the Main section once, unchanged (see Kernel.cut)"
  let head := "-- A COPY of bend2/bendtt.lean with its Main section cut out. The build\n"
    ++ "-- fails unless this is exactly that. Do not edit: `lake run regen` writes it.\n\n"
  return head ++ "\n".intercalate (ls.extract 0 i ++ ls.extract (i + n) ls.size).toList

-- the text that src/Kernel.lean must have, from bend2/bendtt.lean
def Kernel.want (dir : FilePath) : IO (Except String String) :=
  return Kernel.strip (← IO.FS.readFile (dir / ".." / ".." / "bend2" / "bendtt.lean"))

target kernel pkg : Unit := Job.async do
  match ← Kernel.want pkg.dir with
  | .error e => error s!"bend2/bendtt.lean: {e}"
  | .ok want =>
    let file := pkg.dir / "src" / "Kernel.lean"
    unless ← file.pathExists do
      error "src/Kernel.lean is missing. Run `lake run regen`."
    unless LF (← IO.FS.readFile file) == want do
      error ("src/Kernel.lean is not bend2/bendtt.lean minus its Main section. "
        ++ "Run `lake run regen`, review the diff, and commit.")

script regen (_args) do
  let dir := (← getWorkspace).root.dir
  match ← Kernel.want dir with
  | .error e => IO.eprintln s!"bend2/bendtt.lean: {e}"; return 1
  | .ok want => IO.FS.writeFile (dir / "src" / "Kernel.lean") want; return 0

-- Pins
-- ====

-- each reviewed file, and the hash of its text after the review. A change
-- to a file fails the build until its pin is updated by hand, so each
-- change shows in review as a change to its line here.
-- - Contract/Spec.lean: the contract.
-- - Contract/Proof.lean: the claims, stated for what the CLI runs, and the
--   guards.
-- - Guard.lean: the guards' code.
-- - Main.lean: the glue that no proof covers.
def Pins : List (String × UInt64) := [
  ("src/Contract/Spec.lean", 1941511504593986303),
  ("src/Contract/Proof.lean", 13366616450239201674),
  ("src/Guard.lean", 15051376749205065931),
  ("src/Main.lean", 10677801529969707441)]

def Pin.hash (text : String) : UInt64 :=
  Hashable.hash (LF text)

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
-- each file in src, but not the kernel copy and not comments. It is an
-- extra: the guards of Contract/Proof.lean are the main check.
def Scan.words : List String :=
  ["sorry", "admit", "native_decide", "implemented_by", "@[extern", "axiom ",
   "partial def", "unsafe def", "opaque "]

-- the words in the code part of a line (before "--")
def Scan.line (l : String) : List String :=
  let code := (l.splitOn "--").headD ""
  Scan.words.filter fun w => (code.splitOn w).length > 1

target scan pkg : Unit := Job.async do
  let files := (← (pkg.dir / "src").walkDir).filter fun f =>
    f.extension == some "lean" && f != pkg.dir / "src" / "Kernel.lean"
  let mut bad := #[]
  for f in files do
    for l in (← IO.FS.readFile f).splitOn "\n" do
      for w in Scan.line l do
        bad := bad.push s!"{f}: {w}: {l}"
  unless bad.isEmpty do
    error ("\n".intercalate bad.toList)

@[default_target]
lean_lib Bootstrap where
  roots := #[`Kernel, `Guard, `Step, `Run, `Bytes, `Laws, `Shut, `Cli, `Contract, `Machine, `Word]
  globs := #[.one `Kernel, .one `Guard, .one `Step, .one `Run, .one `Bytes, .one `Laws, .one `Shut,
    .one `Cli,
    .submodules `Contract, .submodules `Machine, .submodules `Word]
  needs := #[`@/kernel, `@/pins, `@/scan]

@[default_target]
lean_exe bootstrap where
  root := `Main
  needs := #[`@/kernel, `@/pins, `@/scan]
