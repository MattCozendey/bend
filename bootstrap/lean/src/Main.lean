import Contract.Proof

-- Main
-- ====
--
-- bootstrap <file.bendtt> [input-file]: run def main of the book.
-- - With an input file, main takes the bytes of the file.
-- - A result that is a list of bytes goes to stdout as those bytes.
-- - An other result goes to stdout as text. No proof covers this text.
-- This file is glue: it reads files, calls Interp.cli, and writes the
-- result. Change it only after a review. The build pins its hash.

open Contract

-- render o: o as text. A Nat shows as its number.
def render (o : Obs) : String :=
  match Bytes.ofNat o with
  | some n => toString n
  | none =>
    match o with
    | .lab k => if k == "()" then k else "." ++ k
    | .rfl => "{==}"
    | .tup a b => "(" ++ render a ++ ", " ++ render b ++ ")"
    | .tup0 b => "(-, " ++ render b ++ ")"

def main (args : List String) : IO UInt32 := do
  let (path, inp) ← match args with
    | [p] => pure (p, none)
    | [p, i] => pure (p, some i)
    | _ => throw (IO.userError "usage: bootstrap <file.bendtt> [input-file]")
  let bk ← match Book.parse (← IO.FS.readFile path) with
    | .ok bk => pure bk
    | .error e => throw (IO.userError e)
  let input ← match inp with
    | none => pure none
    | some i => pure (some (← IO.FS.readBinFile i).toList)
  match Interp.cli bk input with
  | .error e =>
    IO.eprintln e
    pure 1
  | .ok o =>
    match Bytes.ofObs o with
    | some bs =>
      (← IO.getStdout).write (ByteArray.mk bs.toArray)
      pure 0
    | none =>
      IO.println (render o)
      pure 0
