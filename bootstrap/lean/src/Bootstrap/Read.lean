import Bootstrap.Read.Go
import Bootstrap.Read.Write

-- Read
-- ====
--
-- INVARIANTS #5: the Bend reader (bootstrap/bend/src/book) gives back
-- each book from the bytes that the Lean writer writes for it. The proof goes
-- through a Lean model of the reader's stack machine, over the terms of its
-- stack items: the model reads back the writer's bytes, and the Bend code does
-- what the model does (src/Bootstrap/Read/).

open Quan Term

-- in a book that holds the reader, the reader gives back exactly the book
-- whose bytes the Lean writer wrote
theorem read_write : Contains B reader →
    Runs B (App Q1 (Ref "Book.read") (bytes (write bk))) (Form.some (Form.defs bk.defs)) := by
  intro h
  have hk := h «reader.Book.read» (by simp [reader])
  have ev : Eval B (spine (Ref "Book.read") [(Q1, bytes (write bk))])
      (App Q1 (App Q1 (Ref "Book.read.go") (bytes (write bk))) (Form.some (list []))) := by
    refine Eval.walk hk (.cons (fun _ => value_bytes) .nil) ?_
    simp [«reader.Book.read», walk, bindsAt, Quan.live, Term.sub, Env.sub, Term.spine, Form.some, list, ctor, takes]
  exact .step ev (go_run h _ [] nofun run_write)
