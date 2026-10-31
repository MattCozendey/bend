import bendtt

-- Script
-- ======
--
-- What the scripts in scripts/ share. They are scripts and not executables:
-- the kernel's own main has the name that an executable needs. Lean runs a
-- script's #eval with no stdin and keeps its stdout, so a script takes its
-- input from files, and environment variables name them.

namespace Script

-- the value of the environment variable k, which must be set
def env (k : String) : IO String := do
  let some v ← IO.getEnv k | throw (IO.userError s!"{k} is not set")
  pure v

-- the book of the .bendtt file that BOOK names
def book : IO Book := do
  match Book.parse (← IO.FS.readFile (← env "BOOK")) with
  | .error msg => throw (IO.userError msg)
  | .ok bk => pure bk

end Script
