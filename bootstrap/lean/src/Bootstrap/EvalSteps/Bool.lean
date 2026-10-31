import Bootstrap.Code
import Bootstrap.Copy.Eval

-- EvalSteps.Bool
-- ==============
--
-- The defs of the Eval copy on Bools, quantities and the forms of terms give
-- what their Lean counterparts give.

open Quan Term

namespace EvalCopy

-- a call on values steps to the leaf of its def's case tree, then runs on
private theorem call (hk : Book.get B k = some d) (vs : Values B xs)
    (w : walk B d.v [] xs = some (some u)) (r : Runs B u v) : Runs B (spine (Ref k) xs) v :=
  .step (Eval.walk hk vs w) r

theorem not_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Bool.not") [(Q1, Form.bool a)]) (Form.bool !a) := by
  have hk : Book.get B "Bool.not" = some «evalCopy.Bool.not» :=
    h «evalCopy.Bool.not» (by simp [evalCopy])
  refine call hk (.cons (fun _ => value_bool) .nil) ?_ (.refl value_bool)
  cases a <;> simp [«evalCopy.Bool.not», walk, Form.bool, ctor, Quan.live, takes, Quan.fld,
    Term.sub, spine]

theorem and_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Bool.and") [(Q1, Form.bool a), (Q1, Form.bool b)]) (Form.bool (a && b)) :=
  by
  have hk : Book.get B "Bool.and" = some «evalCopy.Bool.and» :=
    h «evalCopy.Bool.and» (by simp [evalCopy])
  refine call hk (.cons (fun _ => value_bool) (.cons (fun _ => value_bool) .nil)) ?_
    (.refl value_bool)
  cases a <;> simp [«evalCopy.Bool.and», walk, Form.bool, ctor, bindsAt, Quan.live, takes,
    Quan.fld, Term.sub, Env.sub, spine, data]

theorem or_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Bool.or") [(Q1, Form.bool a), (Q1, Form.bool b)]) (Form.bool (a || b)) :=
  by
  have hk : Book.get B "Bool.or" = some «evalCopy.Bool.or» :=
    h «evalCopy.Bool.or» (by simp [evalCopy])
  refine call hk (.cons (fun _ => value_bool) (.cons (fun _ => value_bool) .nil)) ?_
    (.refl value_bool)
  cases a <;> simp [«evalCopy.Bool.or», walk, Form.bool, ctor, bindsAt, Quan.live, takes,
    Quan.fld, Term.sub, Env.sub, spine, data]

theorem live_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Quan.live") [(Q1, Form.quan q)]) (Form.bool q.live) := by
  have hk : Book.get B "Quan.live" = some «evalCopy.Quan.live» :=
    h «evalCopy.Quan.live» (by simp [evalCopy])
  refine call hk (.cons (fun _ => value_quan) .nil) ?_ (.refl value_bool)
  cases q <;> simp [«evalCopy.Quan.live», walk, Form.bool, Form.quan, ctor, Quan.live, takes,
    Quan.fld, Term.sub, spine]

theorem lives_as_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Quan.lives_as") [(Q1, Form.quan p), (Q1, Form.quan q)])
      (Form.bool (p.live == q.live)) := by
  have hk : Book.get B "Quan.lives_as" = some «evalCopy.Quan.lives_as» :=
    h «evalCopy.Quan.lives_as» (by simp [evalCopy])
  refine call hk (.cons (fun _ => value_quan) (.cons (fun _ => value_quan) .nil)) ?_
    (.refl value_bool)
  cases p <;> cases q <;> simp [«evalCopy.Quan.lives_as», walk, Form.bool, Form.quan, ctor,
    bindsAt, Quan.live, takes, Quan.fld, Term.sub, spine, data]

theorem fld_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Quan.fld") [(Q1, Form.quan r), (Q1, Form.quan q)])
      (Form.quan (Quan.fld r q)) := by
  have hk : Book.get B "Quan.fld" = some «evalCopy.Quan.fld» :=
    h «evalCopy.Quan.fld» (by simp [evalCopy])
  refine call hk (.cons (fun _ => value_quan) (.cons (fun _ => value_quan) .nil)) ?_
    (.refl value_quan)
  cases r <;> cases q <;> simp [«evalCopy.Quan.fld», walk, Form.quan, ctor,
    bindsAt, Quan.live, takes, Quan.fld, Term.sub, Env.sub, spine, data]

-- an argument runs first, after a function that is a value
private theorem runs_arg (vf : Value B f) (rx : Runs B x x') (r : Runs B (App Q1 f x') v) :
    Runs B (App Q1 f x) v :=
  have ⟨_, s, _⟩ := rx; .steps (Steps.app_x vf rfl s) r

-- the function of an application runs first
private theorem runs_fun (rf : Runs B f f') (r : Runs B (App q f' x) v) : Runs B (App q f x) v :=
  have ⟨_, s, _⟩ := rf; .steps (Steps.app_f s) r

-- Bool.not runs on an argument that runs to a Bool
private theorem not_runs (h : Contains B evalCopy) (rx : Runs B x (Form.bool a)) :
    Runs B (App Q1 (Ref "Bool.not") x) (Form.bool !a) :=
  runs_arg (.call (xs := []) (h «evalCopy.Bool.not» (by simp [evalCopy])) .nil
    (walk_iff.1 (by simp [walk, «evalCopy.Bool.not», takes]))) rx (not_copy h)

-- Quan.live runs on an argument that runs to a quantity
private theorem live_runs (h : Contains B evalCopy) (rx : Runs B x (Form.quan q)) :
    Runs B (App Q1 (Ref "Quan.live") x) (Form.bool q.live) :=
  runs_arg (.call (xs := []) (h «evalCopy.Quan.live» (by simp [evalCopy])) .nil
    (walk_iff.1 (by simp [walk, «evalCopy.Quan.live», takes]))) rx (live_copy h)

-- Bool.and runs on arguments that run to Bools
private theorem and_runs (h : Contains B evalCopy) (rx : Runs B x (Form.bool a))
    (ry : Runs B y (Form.bool b)) :
    Runs B (App Q1 (App Q1 (Ref "Bool.and") x) y) (Form.bool (a && b)) := by
  have hk : Book.get B "Bool.and" = some «evalCopy.Bool.and» :=
    h «evalCopy.Bool.and» (by simp [evalCopy])
  have v1 : Value B (App Q1 (Ref "Bool.and") (Form.bool a)) :=
    .call (xs := [(Q1, _)]) hk (.cons (fun _ => value_bool) .nil) (walk_iff.1 (by
      cases a <;> simp [walk, «evalCopy.Bool.and», takes, Form.bool, ctor, Quan.live, Quan.fld]))
  exact runs_fun (runs_arg (.call (xs := []) hk .nil
    (walk_iff.1 (by simp [walk, «evalCopy.Bool.and», takes]))) rx (.refl v1))
    (runs_arg v1 ry (and_copy h))

-- Bool.or runs on arguments that run to Bools
private theorem or_runs (h : Contains B evalCopy) (rx : Runs B x (Form.bool a))
    (ry : Runs B y (Form.bool b)) :
    Runs B (App Q1 (App Q1 (Ref "Bool.or") x) y) (Form.bool (a || b)) := by
  have hk : Book.get B "Bool.or" = some «evalCopy.Bool.or» :=
    h «evalCopy.Bool.or» (by simp [evalCopy])
  have v1 : Value B (App Q1 (Ref "Bool.or") (Form.bool a)) :=
    .call (xs := [(Q1, _)]) hk (.cons (fun _ => value_bool) .nil) (walk_iff.1 (by
      cases a <;> simp [walk, «evalCopy.Bool.or», takes, Form.bool, ctor, Quan.live, Quan.fld]))
  exact runs_fun (runs_arg (.call (xs := []) hk .nil
    (walk_iff.1 (by simp [walk, «evalCopy.Bool.or», takes]))) rx (.refl v1))
    (runs_arg v1 ry (or_copy h))

theorem is_data_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Term.is_data") [(Q1, Form.term t)]) (Form.bool (data t)) := by
  have hk : Book.get B "Term.is_data" = some «evalCopy.Term.is_data» :=
    h «evalCopy.Term.is_data» (by simp [evalCopy])
  induction t
  case Tup q a b iha ihb =>
    refine call hk (.cons (fun _ => value_term) .nil) ?_ (and_runs h (or_runs h
      (not_runs h (live_runs h (.refl value_quan))) iha) ihb)
    simp [«evalCopy.Term.is_data», walk, Form.term, ctor, Quan.live, takes, Quan.fld,
      Term.sub, Env.sub, spine, bindsAt, data_iff.2 data_quan, data_iff.2 data_term]
  all_goals
    refine call hk (.cons (fun _ => value_term) .nil) ?_ (.refl value_bool)
    simp [«evalCopy.Term.is_data», walk, Form.term, Form.bool, ctor, Quan.live, takes, Quan.fld,
      Term.sub, spine, bindsAt, data]

theorem fits_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Quan.fits") [(Q1, Form.quan q), (Q1, Form.term v)])
      (Form.bool (q != Q2 || data v)) := by
  have hk : Book.get B "Quan.fits" = some «evalCopy.Quan.fits» :=
    h «evalCopy.Quan.fits» (by simp [evalCopy])
  have vs : Values B [(Q1, Form.quan q), (Q1, Form.term v)] :=
    .cons (fun _ => value_quan) (.cons (fun _ => value_term) .nil)
  cases q
  case Q2 =>
    refine call hk vs (u := App Q1 (Ref "Term.is_data") (Form.term v)) ?_ ?_
    · simp [«evalCopy.Quan.fits», walk, Form.quan, ctor, Quan.live, takes, Quan.fld,
        Term.sub, Env.sub, spine, bindsAt]
    · simpa [spine] using is_data_copy h
  all_goals
    refine call hk vs ?_ (.refl value_bool)
    simp [«evalCopy.Quan.fits», walk, Form.quan, Form.bool, ctor, Quan.live, takes, Quan.fld,
      Term.sub, spine, bindsAt, data]

theorem binds_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Quan.binds") [(Q2, Form.quan p), (Q1, Form.quan q), (Q1, Form.term x)])
      (Form.bool (bindsAt p q x)) := by
  have hk : Book.get B "Quan.binds" = some «evalCopy.Quan.binds» :=
    h «evalCopy.Quan.binds» (by simp [evalCopy])
  refine call hk (.cons (fun _ => value_quan) (.cons (fun _ => value_quan)
    (.cons (fun _ => value_term) .nil))) ?_ (and_runs h (lives_as_copy h) (fits_copy h))
  simp [«evalCopy.Quan.binds», walk, Quan.live, takes, Term.sub, Env.sub, spine, bindsAt,
    data_iff.2 data_quan]

theorem is_former_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Term.is_former") [(Q1, Form.term t)]) (Form.bool (t.former != 0)) := by
  have hk : Book.get B "Term.is_former" = some «evalCopy.Term.is_former» :=
    h «evalCopy.Term.is_former» (by simp [evalCopy])
  refine call hk (.cons (fun _ => value_term) .nil) ?_ (.refl value_bool)
  cases t <;> simp [«evalCopy.Term.is_former», walk, Form.term, Form.bool, ctor, Quan.live,
    takes, Quan.fld, Term.sub, spine, bindsAt, data, former]

theorem takes_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Term.takes") [(Q1, Form.term t)]) (Form.bool (Term.takes t)) := by
  have hk : Book.get B "Term.takes" = some «evalCopy.Term.takes» :=
    h «evalCopy.Term.takes» (by simp [evalCopy])
  refine call hk (.cons (fun _ => value_term) .nil) ?_ (.refl value_bool)
  cases t <;> simp [«evalCopy.Term.takes», walk, Form.term, Form.bool, ctor, Quan.live,
    takes, Quan.fld, Term.sub, spine, bindsAt, data]

theorem waits_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Eval.waits") [(Q1, Form.maybe (Form.maybe Form.term) r)])
      (Form.bool (r == some none)) := by
  have hk : Book.get B "Eval.waits" = some «evalCopy.Eval.waits» :=
    h «evalCopy.Eval.waits» (by simp [evalCopy])
  refine call hk (.cons (fun _ => value_maybe (fun _ => value_maybe (fun _ => value_term))) .nil)
    ?_ (.refl value_bool)
  rcases r with _ | _ | t <;> simp [«evalCopy.Eval.waits», walk, Form.maybe, Form.some,
    Form.bool, ctor, Quan.live, takes, Quan.fld, Term.sub, spine, bindsAt, data]

end EvalCopy
