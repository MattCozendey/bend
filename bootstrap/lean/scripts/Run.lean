import Bootstrap.Program
import Bootstrap.Script

-- Run
-- ===
--
-- Runs the program of a .bendtt file on the bytes of a file with interp
-- (src/Bootstrap/Program.lean), and writes the bytes it gives to a file.
--
--   BOOK=prog.bendtt INPUT=in OUTPUT=out [FUEL=n] lake lean scripts/Run.lean
--
-- FUEL is defaultFuel when it is not set. On a result, it writes OUTPUT, prints
-- the number of steps and exits with 0. Else it prints the error, and why there
-- is no result, and exits with 1.

open Quan Term

def defaultFuel : Nat := 100000000

-- why the end (v, n) of a run with this fuel gives no result
def noResult (bk : Book) (fuel : Nat) : Term × Nat → String
  | (v, n) =>
    if (step bk v).isSome then s!"no result within {fuel} steps"
    else if value bk v then s!"no result: after {n} steps, the value is not a list of bytes"
    else s!"no result: stuck after {n} steps"

def runBook : IO Unit := do
  let fuel := ((← IO.getEnv "FUEL").bind String.toNat?).getD defaultFuel
  let bk ← Script.book
  let i := (← IO.FS.readBinFile (← Script.env "INPUT")).toList
  let e := steps bk fuel (start i) 0
  have _ : result bk e = interp bk fuel i := rfl
  match result bk e with
  | some (r, n) =>
    IO.FS.writeBinFile (← Script.env "OUTPUT") ⟨r.toArray⟩
    IO.println s!"{n} steps"
  | none => throw (IO.userError (noResult bk fuel e))

#eval runBook
