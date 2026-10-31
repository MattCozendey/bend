import Bootstrap.EvalSteps.Step

-- EvalSteps
-- =========
--
-- INVARIANTS #2: Eval.steps, the Bend copy of Eval
-- (bootstrap/refactor/bend/src/book), gives what the kernel's Eval gives,
-- after the same number of steps, in both directions. The proof goes through
-- step (Bootstrap/Interp.lean), which the copy follows case for case
-- (src/Bootstrap/EvalSteps/).

open Quan Term

-- in a book that holds the copy of Eval, the copy says that t reaches u after
-- n steps exactly when the kernel's Eval says so
theorem copy_steps : Contains B evalCopy →
    (Runs B (App Q1 (App Q1 (App Q1 (Ref "Eval.steps") (Form.nat n)) (Form.defs bk.defs)) (Form.term t))
      (Form.some (Form.term u)) ↔ Steps bk n t u) := sorry
