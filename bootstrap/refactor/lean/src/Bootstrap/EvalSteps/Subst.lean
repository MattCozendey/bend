import Bootstrap.EvalSteps.Bool

-- EvalSteps.Subst
-- ===============
--
-- The defs of the Eval copy on variables: the term of a variable, a shift, and
-- a substitution, as the kernel's Term.subk computes it.

open Quan Term

namespace EvalCopy

-- the renaming that moves each variable from c on up by d
def shifts (d c : Nat) (i : Nat) : Nat := if i < c then i else i + d

theorem env_sub_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Env.sub") [(Q1, Form.env e), (Q1, Form.nat i)]) (Form.term (Env.sub e i)) :=
  sorry

theorem shift_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Term.shift") [(Q1, Form.term t), (Q2, Form.nat d), (Q2, Form.nat c)])
      (Form.term (ren (shifts d c) t)) := sorry

theorem subst_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Term.subst") [(Q1, Form.term t), (Q2, Form.env e), (Q2, Form.nat d)])
      (Form.term (Term.subk (Env.sub e) d t)) := sorry

theorem inst_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Term.inst") [(Q1, Form.term f), (Q1, Form.term v)])
      (Form.term (Term.inst f v)) := sorry

end EvalCopy
