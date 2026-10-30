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

-- why src/Kernel.lean is not that text, or none
def Kernel.check (dir : FilePath) : IO (Option String) := do
  match ← Kernel.want dir with
  | .error e => return some s!"bend2/bendtt.lean: {e}"
  | .ok want =>
    let file := dir / "src" / "Kernel.lean"
    unless ← file.pathExists do
      return some "src/Kernel.lean is missing. Run `lake run regen`."
    unless LF (← IO.FS.readFile file) == want do
      return some ("src/Kernel.lean is not bend2/bendtt.lean minus its Main section. "
        ++ "Run `lake run regen`, review the diff, and commit.")
    return none

target kernel pkg : Unit := Job.async do
  match ← Kernel.check pkg.dir with
  | some e => error e
  | none => pure ()

script regen (_args) do
  let dir := (← getWorkspace).root.dir
  match ← Kernel.want dir with
  | .error e => IO.eprintln s!"bend2/bendtt.lean: {e}"; return 1
  | .ok want => IO.FS.writeFile (dir / "src" / "Kernel.lean") want; return 0

-- Pins
-- ====

-- the part of a file that a pin covers: from its first line up to the next
-- line that ends it (not included), or to the end of the file
inductive Pin.Part where
  -- the whole file
  | all
  -- from the line a up to the line b
  | span (a b : String)
  -- a def: from the line that starts with h up to an empty line
  | block (h : String)

-- each reviewed text, and the hash of its text after the review. A change
-- to a text fails the build until its pin is updated by hand, so each
-- change shows in review as a change to its line here.
-- - Contract/Spec.lean: the contract.
-- - Contract/Proof.lean: the claims, stated for what the CLI runs, and the
--   guards.
-- - Guard.lean: the guards' code.
-- - Main.lean: the glue that no proof covers.
-- - ../bend/main.bend: main, which must be λsrc. compile(src), as claim 7
--   names the call of a law only through main.
-- - ../bend/src/compile/spec.bend: the contract of the compiler in Bend.
-- - ../bend/src/source/impl.bend: the meaning of its source.
-- - ../bend/src/source/spec.bend: the kernel's relations, copied, that its
--   laws tie that meaning to.
-- - ../bend/runner.bend and ../bend/src/runner/impl.bend: the runner in Bend,
--   which runs a program by that meaning.
-- - ../../bend2/bendtt.lean: the parts of the kernel that impl.bend and
--   spec.bend copy: Types up to Ctx (the terms, substitution and the book),
--   the Parser, and Evaluation (the run-time relations). When one changes,
--   check the copy again.
-- - ../../bend2/base.bend: each Base def that the meaning or the runner
--   reaches: in the .bendtt of ../bend/main.bend and ../bend/runner.bend,
--   from the defs of source/impl.bend, source/spec.bend and runner/impl.bend,
--   and from the types of the laws. A pinned def that starts to call another
--   Base def changes, so its review adds that def here.
def Pins : List (String × Pin.Part × UInt64) := [
  ("src/Contract/Spec.lean", .all, 1941511504593986303),
  ("src/Contract/Proof.lean", .all, 13366616450239201674),
  ("src/Guard.lean", .all, 15051376749205065931),
  ("src/Main.lean", .all, 10677801529969707441),
  ("../bend/main.bend", .all, 12787539127806695791),
  ("../bend/src/compile/spec.bend", .all, 16295624150471894959),
  ("../bend/src/source/impl.bend", .all, 16563396131937143125),
  ("../bend/src/source/spec.bend", .all, 5629837982964475826),
  ("../bend/runner.bend", .all, 1850732974300312482),
  ("../bend/src/runner/impl.bend", .all, 12737539636974758867),
  ("../../bend2/bendtt.lean", .span "-- Types" "-- Ctx", 14875125228840285785),
  ("../../bend2/bendtt.lean", .span "-- Parser" "-- Evaluator", 15025253426444512988),
  ("../../bend2/bendtt.lean", .span "-- Evaluation" "-- Claims", 4021871860510412546),
  ("../../bend2/base.bend", .block "type Empty ", 13328514820168334527),
  ("../../bend2/base.bend", .block "type Unit ", 11655013887032649838),
  ("../../bend2/base.bend", .block "type Bool ", 10837456009245346379),
  ("../../bend2/base.bend", .block "type Cmp ", 1356910975501632879),
  ("../../bend2/base.bend", .block "type Either<", 15328778016285137708),
  ("../../bend2/base.bend", .block "type Sigma<", 9217934299523109552),
  ("../../bend2/base.bend", .block "type Nat ", 2600738686466065594),
  ("../../bend2/base.bend", .block "type Maybe<", 17874651699370011728),
  ("../../bend2/base.bend", .block "type List<", 17002992440093265846),
  ("../../bend2/base.bend", .block "type Word.Nil ", 3326355874253803456),
  ("../../bend2/base.bend", .block "type Word.Con<", 13608246266612647673),
  ("../../bend2/base.bend", .block "def Word(", 6078558829838616308),
  ("../../bend2/base.bend", .block "type U32 ", 17049118783817157415),
  ("../../bend2/base.bend", .block "type Char ", 11568173190120668437),
  ("../../bend2/base.bend", .block "type String ", 1425772917372064238),
  ("../../bend2/base.bend", .block "def Pair(", 16586760494593832162),
  ("../../bend2/base.bend", .block "def Or(", 10185388648639581221),
  ("../../bend2/base.bend", .block "def Bool.not(", 11689238119106776062),
  ("../../bend2/base.bend", .block "def Bool.and(", 13836908075683677256),
  ("../../bend2/base.bend", .block "def Bool.or(", 18017131119575026037),
  ("../../bend2/base.bend", .block "def Cmp.is_lt(", 7913983619305019013),
  ("../../bend2/base.bend", .block "def Cmp.is_eq(", 2439583826802733364),
  ("../../bend2/base.bend", .block "def Cmp.is_le(", 7659969790581787967),
  ("../../bend2/base.bend", .block "def Nat.double(", 13782423285035845449),
  ("../../bend2/base.bend", .block "def Nat.add(", 4659165431988668479),
  ("../../bend2/base.bend", .block "def Nat.sub(", 7425936745064968018),
  ("../../bend2/base.bend", .block "def Nat.cmp(", 9808790773107524040),
  ("../../bend2/base.bend", .block "def Nat.is_lt(", 15841316101325720444),
  ("../../bend2/base.bend", .block "def Nat.is_eq(", 1051263939805551333),
  ("../../bend2/base.bend", .block "def Nat.is_le(", 12695900786442840810),
  ("../../bend2/base.bend", .block "def List.append(", 15630691666062795272),
  ("../../bend2/base.bend", .block "def List.reverse.go(", 3740530639075124172),
  ("../../bend2/base.bend", .block "def List.reverse(", 5721769233288835689),
  ("../../bend2/base.bend", .block "def Word.to_nat(", 723743634680710343),
  ("../../bend2/base.bend", .block "def U32.to_nat(", 15123021057519108580),
  ("../../bend2/base.bend", .block "def Pair.fst(", 10900200023254262526),
  ("../../bend2/base.bend", .block "def Pair.snd(", 1246976093224629073),
  ("../../bend2/base.bend", .block "def Nat.mul(", 1813486149535455628),
  ("../../bend2/base.bend", .block "def Nat.divmod.go(", 6487796413967987314),
  ("../../bend2/base.bend", .block "def Nat.divmod(", 12078178798127432727),
  ("../../bend2/base.bend", .block "def Nat.div(", 84019639989369007),
  ("../../bend2/base.bend", .block "def Nat.mod(", 1601870151355992951),
  ("../../bend2/base.bend", .block "def List.length(", 18432464484018013776),
  ("../../bend2/base.bend", .block "def List.take(", 8769491522669272524),
  ("../../bend2/base.bend", .block "def List.drop(", 17352358031024133288)]

-- the index of the first line, from i on, that p holds for
def Pin.find (ls : Array String) (i : Nat) (p : String → Bool) : Option Nat :=
  (List.range ls.size).find? fun k => i ≤ k && p ls[k]!

-- the line that begins part, and the line that ends it
def Pin.Part.bounds : Pin.Part → (String → Bool) × (String → Bool)
  | .all => ((fun _ => true), (fun _ => false))
  | .span a b => ((· == a), (· == b))
  | .block h => ((·.startsWith h), (· == ""))

-- part in a message, after its file's path
def Pin.Part.label : Pin.Part → String
  | .all => ""
  | .span a _ => s!" from '{a}'"
  | .block h => s!" at '{h}'"

-- the text that part covers in a file's text
def Pin.Part.text (text : String) (part : Pin.Part) : Except String String := do
  let ls := ((LF text).splitOn "\n").toArray
  let (starts, stops) := part.bounds
  let some i := Pin.find ls 0 starts
    | throw s!"no line{part.label}"
  let j := (Pin.find ls (i + 1) stops).getD ls.size
  return "\n".intercalate (ls.extract i j).toList

-- each pin whose text is not the pinned one, and why
def Pins.check (dir : FilePath) : IO (Array String) := do
  let mut bad := #[]
  for (path, part, pin) in Pins do
    match Pin.Part.text (← IO.FS.readFile (dir / path)) part with
    | .error e => bad := bad.push s!"{path}: {e}"
    | .ok text =>
      let h := Hashable.hash text
      unless h == pin do
        bad := bad.push
          s!"{path}{part.label} changed. Review it, then set its pin in lakefile.lean to {h}"
  return bad

target pins pkg : Unit := Job.async do
  let bad ← Pins.check pkg.dir
  unless bad.isEmpty do
    error ("\n".intercalate bad.toList)

-- the guards of the reviewed texts, outside a build: the kernel copy and the
-- pins. The harness runs it before its cases (`lake run pinned`).
script pinned (_args) do
  let dir := (← getWorkspace).root.dir
  let mut bad ← Pins.check dir
  if let some e := (← Kernel.check dir) then
    bad := bad.push e
  for b in bad do
    IO.eprintln b
  return if bad.isEmpty then 0 else 1

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
