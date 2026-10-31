import Bootstrap.EvalSteps.Call

-- EvalSteps.Step
-- ==============
--
-- The step of the Eval copy, and its runs of exactly n steps, give what step
-- (Bootstrap/Interp.lean) gives.

open Quan Term

namespace EvalCopy

-- exactly n steps of step
def iterate (bk : Book) : Nat → Term → Option Term
  | 0, t => some t
  | n + 1, t => (step bk t).bind (iterate bk n)

theorem step_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Eval.step") [(Q2, Form.defs bk.defs), (Q2, Form.term t)])
      (Form.maybe Form.term (step bk t)) := sorry

theorem steps_copy (h : Contains B evalCopy) :
    Runs B (App Q1 (App Q1 (App Q1 (Ref "Eval.steps") (Form.nat n)) (Form.defs bk.defs)) (Form.term t))
      (Form.maybe Form.term (iterate bk n t)) := sorry

end EvalCopy
