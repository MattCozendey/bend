import Bootstrap.EvalSteps.Walk

-- EvalSteps.Call
-- ==============
--
-- The defs of the Eval copy on calls: the walk of a call, Value and the
-- arguments of a call (as_args), a call's step, and a redex.

open Quan Term

namespace EvalCopy

theorem callWalk_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Eval.callWalk") [(Q1, Form.defs bk.defs), (Q2, Form.term t)])
      (Form.maybe (Form.maybe Form.term) (callWalk bk t)) := sorry

theorem vals_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Eval.vals") [(Q2, Form.defs bk.defs), (Q2, Form.term t), (Q1, Form.bool a)])
      (Form.bool (if a then args bk t else value bk t)) := sorry

theorem call_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Eval.call") [(Q2, Form.defs bk.defs), (Q2, Form.term t)])
      (Form.maybe Form.term (call bk t)) := sorry

theorem redex_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Eval.redex")
        [(Q1, Form.defs bk.defs), (Q2, Form.quan q), (Q2, Form.term f), (Q2, Form.term x)])
      (Form.maybe Form.term (redex bk q f x)) := sorry

end EvalCopy
