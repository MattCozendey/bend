import Bootstrap

-- Run
-- ===
--
-- Runs the program of a .bendtt file on the bytes of a file with interp
-- (src/Bootstrap/Program.lean), and writes the bytes it gives to a file. It
-- is a script and not an executable: the kernel's own main has the name that
-- an executable needs. Lean runs a script's #eval with no stdin and keeps its
-- stdout, so the bytes go through files.
--
--   lake build
--   BOOK=prog.bendtt INPUT=in OUTPUT=out [FUEL=n] lake env lean scripts/Run.lean
--
-- On a result, it writes OUTPUT, prints the number of steps and exits with
-- 0. Else it prints the error, and why there is no result, and exits with 1.

open Quan Term

-- why a run of the program on i has no result
def noResult (bk : Book) (fuel : Nat) (i : List UInt8) : String :=
  let (v, n) := steps bk fuel (start i) 0
  if (step bk v).isSome then s!"no result within {fuel} steps"
  else if value bk v then s!"no result: after {n} steps, the value is not a list of bytes"
  else s!"no result: stuck after {n} steps"

def env (k : String) : IO String := do
  let some v ← IO.getEnv k | throw (IO.userError s!"{k} is not set")
  pure v

def runBook : IO Unit := do
  let fuel := ((← IO.getEnv "FUEL").bind String.toNat?).getD 100000000
  match Book.parse (← IO.FS.readFile (← env "BOOK")) with
  | .error e => throw (IO.userError e)
  | .ok bk =>
    let i := (← IO.FS.readBinFile (← env "INPUT")).toList
    match interp bk fuel i with
    | some (r, n) =>
      IO.FS.writeBinFile (← env "OUTPUT") ⟨r.toArray⟩
      IO.println s!"{n} steps"
    | none => throw (IO.userError (noResult bk fuel i))

#eval runBook
