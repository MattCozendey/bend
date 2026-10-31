import Bootstrap.EvalSteps.Name
import Bootstrap.EvalSteps.Subst

-- EvalSteps.Walk
-- ==============
--
-- The defs of the Eval copy on spines, and its walk of a case tree.

open Quan Term

namespace EvalCopy

theorem head_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Term.head") [(Q1, Form.term t)]) (Form.term (unspine t []).1) := sorry

theorem args_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Term.args") [(Q1, Form.term t), (Q1, Form.args xs)])
      (Form.args (unspine t xs).2) := sorry

theorem spine_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Term.spine") [(Q1, Form.args xs), (Q1, Form.term t)])
      (Form.term (Term.spine t xs)) := sorry

theorem walk_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Eval.walk") [(Q2, Form.term t), (Q2, Form.env e), (Q2, Form.args xs)])
      (Form.maybe (Form.maybe Form.term) (walk bk t e xs)) := sorry

end EvalCopy
