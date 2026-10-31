import Bootstrap.Book
import Bootstrap.Script

-- Write
-- =====
--
-- Writes the bytes of the book of a .bendtt file, as the Lean writer of
-- src/Bootstrap/Book.lean writes them (INVARIANTS #5): the input of the
-- compiler of step 1.
--
--   BOOK=prog.bendtt OUTPUT=prog.book lake lean scripts/Write.lean

def writeBook : IO Unit := do
  let bs := write (← Script.book)
  IO.FS.writeBinFile (← Script.env "OUTPUT") ⟨bs.toArray⟩
  IO.println s!"{bs.length} bytes"

#eval writeBook
