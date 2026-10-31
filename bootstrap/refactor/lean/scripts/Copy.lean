import Bootstrap

-- Copy
-- ====
--
-- Writes a Lean copy of the defs that the kernel's parser reads from a .bendtt
-- file, for the laws about our Bend code (src/Bootstrap/Code.lean):
--
--   bend <file.bend> -o <file.bendtt>
--   BOOK=<file.bendtt> NAME=<name> SOURCE=<file.bend> OUTPUT=<file.lean> \
--     lake env lean scripts/Copy.lean
--
-- The Lean file defines a def «NAME.k» per def k, and NAME : List Def. Like
-- scripts/Run.lean, it takes its input from files, as Lean runs a script's
-- #eval with no stdin.

open Quan Term

def env (k : String) : IO String := do
  let some v ← IO.getEnv k | throw (IO.userError s!"{k} is not set")
  pure v

-- the Lean def that copies d: one atomic name, so that it opens no namespace in
-- which a Bend name such as List hides Lean's
def copyDef (name : String) (d : Def) : String :=
  s!"def «{name}.{d.k}» : Def :=\n  ⟨{repr d.k},\n    {(repr d.T).pretty 100 4},\n" ++
  s!"    {(repr d.v).pretty 100 4},\n    {d.o}⟩\n\n"

def copyBook : IO Unit := do
  let name ← env "NAME"
  match Book.parse (← IO.FS.readFile (← env "BOOK")) with
  | .error msg => throw (IO.userError msg)
  | .ok bk =>
    IO.FS.writeFile (← env "OUTPUT") <|
      s!"import bendtt\n\n-- Made by scripts/Copy.lean from the `bend -o` output of {← env "SOURCE"}.\n" ++
      s!"-- Do not edit it.\n\nopen Quan Term\n\n" ++ String.join (bk.defs.map (copyDef name)) ++
      s!"def {name} : List Def :=\n  [" ++ ",\n   ".intercalate (bk.defs.map fun d => s!"«{name}.{d.k}»") ++ "]\n"
    IO.println s!"{bk.defs.length} defs"

#eval copyBook
