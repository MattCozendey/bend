import Bootstrap.Code
import Bootstrap.Copy.Eval

-- EvalSteps.Bool
-- ==============
--
-- The defs of the Eval copy on Bools, quantities and the forms of terms give
-- what their Lean counterparts give.

open Quan Term

namespace EvalCopy

theorem not_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Bool.not") [(Q1, Form.bool a)]) (Form.bool !a) := sorry

theorem and_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Bool.and") [(Q1, Form.bool a), (Q1, Form.bool b)]) (Form.bool (a && b)) :=
  sorry

theorem or_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Bool.or") [(Q1, Form.bool a), (Q1, Form.bool b)]) (Form.bool (a || b)) :=
  sorry

theorem live_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Quan.live") [(Q1, Form.quan q)]) (Form.bool q.live) := sorry

theorem lives_as_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Quan.lives_as") [(Q1, Form.quan p), (Q1, Form.quan q)])
      (Form.bool (p.live == q.live)) := sorry

theorem fld_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Quan.fld") [(Q1, Form.quan r), (Q1, Form.quan q)])
      (Form.quan (Quan.fld r q)) := sorry

theorem is_data_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Term.is_data") [(Q1, Form.term t)]) (Form.bool (data t)) := sorry

theorem fits_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Quan.fits") [(Q1, Form.quan q), (Q1, Form.term v)])
      (Form.bool (q != Q2 || data v)) := sorry

theorem binds_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Quan.binds") [(Q2, Form.quan p), (Q1, Form.quan q), (Q1, Form.term x)])
      (Form.bool (bindsAt p q x)) := sorry

theorem is_former_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Term.is_former") [(Q1, Form.term t)]) (Form.bool (t.former != 0)) := sorry

theorem takes_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Term.takes") [(Q1, Form.term t)]) (Form.bool (Term.takes t)) := sorry

theorem waits_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Eval.waits") [(Q1, Form.maybe (Form.maybe Form.term) r)])
      (Form.bool (r == some none)) := sorry

end EvalCopy
