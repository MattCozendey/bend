import Bootstrap.Code

-- Kit
-- ===
--
-- Runs of calls, as EvalSteps' private helpers make them: a call on values
-- steps to the leaf of its walk; the arguments of a call run first, in
-- order; a pair runs field by field; a term runs to at most one value.

open Quan Term

namespace Kit

-- a call whose arguments are values steps to the leaf of its walk
theorem call (hk : Book.get B k = some d) (vs : Values B xs)
    (w : walk B d.v [] xs = some (some u)) (r : Runs B u v) : Runs B (spine (Ref k) xs) v :=
  .step (Eval.walk hk vs w) r

-- a call that needs more arguments is a value
theorem part (hk : Book.get B k = some d) (vs : Values B xs)
    (w : walk B d.v [] xs = some none) : Value B (spine (Ref k) xs) :=
  .call hk vs (walk_iff.1 w)

-- the argument of a value runs first
theorem run_x (vf : Value B f) (l : q.live = true) (rx : Runs B x x')
    (r : Runs B (App q f x') v) : Runs B (App q f x) v := by
  obtain ⟨_, s, -⟩ := rx
  exact .steps (Steps.app_x vf l s) r

-- the function of an application runs first
theorem run_f (rf : Runs B f f') (r : Runs B (App q f' x) v) : Runs B (App q f x) v := by
  obtain ⟨_, s, -⟩ := rf
  exact .steps (Steps.app_f s) r

-- a pair at quantity 1 runs field by field
theorem run_tup (ra : Runs B a a') (rb : Runs B b b') : Runs B (Tup Q1 a b) (Tup Q1 a' b') := by
  obtain ⟨n, s, va⟩ := ra
  obtain ⟨m, t, vb⟩ := rb
  have s' : Steps B n (Tup Q1 a b) (Tup Q1 a' b) := by
    clear t; induction s with
    | refl => exact .refl
    | step e _ ih => exact .step (.tup_a rfl e) (ih va)
  have t' : Steps B m (Tup Q1 a' b) (Tup Q1 a' b') := by
    clear s s'; induction t with
    | refl => exact .refl
    | step e _ ih => exact .step (.tup_b (fun _ => va) e) (ih vb)
  exact ⟨_, s'.trans t', .tup (fun _ => va) vb⟩

-- a term runs to at most one value
theorem runs_det (r : Runs B t v) (r' : Runs B t v') : v = v' := by
  obtain ⟨_, s, hv⟩ := r
  obtain ⟨_, s', hv'⟩ := r'
  exact (steps_det s hv s' hv').2

theorem runs_eq (r : Runs B e v) (h : v = v') : Runs B e v' := h ▸ r

-- each argument term runs to its value, at a live quantity
-- (a dead argument stays as it is)
inductive RunsArgs (B : Book) : List Arg → List Arg → Prop
  | nil : RunsArgs B [] []
  | cons : q.live = true → Runs B e x → RunsArgs B es xs → RunsArgs B ((q, e) :: es) ((q, x) :: xs)
  | dead : q.live = false → RunsArgs B es xs → RunsArgs B ((q, x) :: es) ((q, x) :: xs)

theorem RunsArgs.values : RunsArgs B es xs → Values B xs
  | .nil => .nil
  | .cons _ ⟨_, _, v⟩ rs => .cons (fun _ => v) rs.values
  | .dead l rs => .cons (fun h => by simp [l] at h) rs.values

theorem RunsArgs.take : RunsArgs B es xs → ∀ m, Values B (xs.take m)
  | .nil, _ => by simp; exact .nil
  | .cons _ ⟨_, _, v⟩ rs, 0 => by simp; exact .nil
  | .cons _ ⟨_, _, v⟩ rs, m + 1 => by simp; exact .cons (fun _ => v) (rs.take m)
  | .dead _ rs, 0 => by simp; exact .nil
  | .dead l rs, m + 1 => by simp; exact .cons (fun h => by simp [l] at h) (rs.take m)

-- the arguments of a spine run in order, after its head
theorem runs_spine (rs : RunsArgs B es xs) (hf : Steps B n f f')
    (hp : ∀ m < xs.length, Value B (spine f' (xs.take m))) (r : Runs B (spine f' xs) v) :
    Runs B (spine f es) v := by
  induction rs generalizing n f f' with
  | nil => exact .steps hf r
  | cons l rx _ ih =>
    obtain ⟨_, sx, _⟩ := rx
    have vf : Value B f' := hp 0 (by simp)
    exact ih (hf.app_f.trans (sx.app_x vf l)) (fun m hm => hp (m + 1) (by simp; omega)) r
  | dead _ _ ih => exact ih hf.app_f (fun m hm => hp (m + 1) (by simp; omega)) r

-- the arguments of a call run to values first, and its prefixes are values
theorem runs_args (hk : Book.get B k = some d) (rs : RunsArgs B es xs)
    (hp : ∀ m < xs.length, walk B d.v [] (xs.take m) = some none)
    (r : Runs B (spine (Ref k) xs) v) : Runs B (spine (Ref k) es) v :=
  runs_spine rs .refl (fun m hm => .call hk (rs.take m) (walk_iff.1 (hp m hm))) r

-- a call whose arguments run to values steps to the leaf of its walk
theorem runs_call (hk : Book.get B k = some d) (rs : RunsArgs B es xs)
    (hp : ∀ m < xs.length, walk B d.v [] (xs.take m) = some none)
    (w : walk B d.v [] xs = some (some u)) (r : Runs B u v) : Runs B (spine (Ref k) es) v :=
  runs_spine rs .refl (fun m hm => .call hk (rs.take m) (walk_iff.1 (hp m hm)))
    (.step (Eval.walk hk rs.values w) r)

-- a value as an argument runs to itself
theorem RunsArgs.v (l : q.live = true) (v : Value B x) (rs : RunsArgs B es xs) :
    RunsArgs B ((q, x) :: es) ((q, x) :: xs) := .cons l (.refl v) rs

theorem RunsArgs.d (l : q.live = false) (rs : RunsArgs B es xs) :
    RunsArgs B ((q, x) :: es) ((q, x) :: xs) := .dead l rs

theorem RunsArgs.r (l : q.live = true) (r : Runs B e x) (rs : RunsArgs B es xs) :
    RunsArgs B ((q, e) :: es) ((q, x) :: xs) := .cons l r rs

end Kit
