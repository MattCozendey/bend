import Bootstrap.Machine.App

-- Machine.Move
-- ============
--
-- A move that is no step keeps the term, and a move that is a step is one step
-- of Eval. Each keeps what the state knows true.

open Quan Term

namespace Machine

theorem move_admin (hs : s.Ok bk) (h : move bk s = .admin s') : s'.Ok bk ∧ s'.term = s.term :=
  sorry

theorem move_step (hs : s.Ok bk) (h : move bk s = .step s') : s'.Ok bk ∧ Eval bk s.term s'.term :=
  sorry

end Machine
