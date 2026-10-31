import Bootstrap.EvalSteps.Bool

-- EvalSteps.Name
-- ==============
--
-- The defs of the Eval copy on names: equality, the lookup of a def, and the
-- meet of two quantity labels.

open Quan Term

namespace EvalCopy

-- the form of a name, its UTF-8 bytes, says which name it is
theorem name_inj : Form.name a = Form.name b → a = b := sorry

theorem name_is_eq_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Name.is_eq") [(Q1, Form.name a), (Q1, Form.name b)]) (Form.bool (a == b)) :=
  sorry

theorem get_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Book.get") [(Q1, Form.defs ds), (Q2, Form.name k)])
      (Form.maybe Form.defn (ds.find? (·.k == k))) := sorry

theorem meet_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Eval.meet") [(Q1, Form.term a), (Q1, Form.term b)])
      (Form.maybe Form.term (meet a b)) := sorry

end EvalCopy
