import bendtt

-- Eval
-- ====
--
-- Facts about the kernel's Eval (bend2/bendtt.lean), which INVARIANTS #2
-- and #4 rely on: "the result" and "the number of steps" of a run.

open Quan Term

-- a walk has at most one outcome
theorem walk_det (w : Walk bk t e xs o) (w' : Walk bk t e xs o') : o = o' := by
  induction w generalizing o' <;> cases w' <;> first
    | rfl
    | (apply_assumption; assumption)
    | exact nomatch ‹node _ = false›.symm.trans (node_takes ‹_›)
    | simp_all [node, takes]

-- a walk with one more argument either needed more arguments before it, or
-- applies its result before it to that argument
theorem walk_snoc (w : Walk bk t e zs o) : zs = xs ++ [(q, x)] →
    Walk bk t e xs none ∨ ∃ r, Walk bk t e xs (some r) ∧ o = some (App q r x) := by
  induction w generalizing xs <;> intro h
  case app hn _ ih => exact (ih (congrArg _ h)).imp (.app hn) fun ⟨r, w, e⟩ => ⟨r, .app hn w, e⟩
  case need => cases xs <;> cases h
  case done hn => subst h; exact .inr ⟨_, .done hn, by rw [spine_snoc]⟩
  case lam hl hd _ ih =>
    cases xs with
    | nil => exact .inl (.need rfl)
    | cons _ xs =>
      simp only [List.cons_append, List.cons.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact (ih rfl).imp (.lam hl hd) fun ⟨r, w, e⟩ => ⟨r, .lam hl hd w, e⟩
  case prj hl _ ih =>
    cases xs with
    | nil => exact .inl (.need rfl)
    | cons _ xs =>
      simp only [List.cons_append, List.cons.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact (ih (xs := _ :: _ :: xs) rfl).imp (.prj hl) fun ⟨r, w, e⟩ => ⟨r, .prj hl w, e⟩
  case hit hl _ ih =>
    cases xs with
    | nil => exact .inl (.need rfl)
    | cons _ xs =>
      simp only [List.cons_append, List.cons.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact (ih rfl).imp (.hit hl) fun ⟨r, w, e⟩ => ⟨r, .hit hl w, e⟩
  case miss hl hj _ ih =>
    cases xs with
    | nil => exact .inl (.need rfl)
    | cons _ xs =>
      simp only [List.cons_append, List.cons.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact (ih (xs := _ :: xs) rfl).imp (.miss hl hj) fun ⟨r, w, e⟩ => ⟨r, .miss hl hj w, e⟩

-- a call whose arguments are values steps only to its walk's result
theorem call_det (hk : Book.get bk k = some d) (vs : Values bk xs)
    (w : Walk bk d.v [] xs (some r)) (h : Eval bk (spine (Ref k) xs) u) : u = r := by
  generalize e : spine (Ref k) xs = s at h
  induction h generalizing xs r
  case call hk' _ w' =>
    cases (spine_head rfl).symm.trans (spine_head e); cases hk.symm.trans hk'
    exact Option.some.inj (walk_det w' w)
  case app_f hf ih =>
    rcases xs.eq_nil_or_concat with rfl | ⟨ys, ⟨q, x⟩, rfl⟩; cases e
    simp only [List.concat_eq_append, spine_snoc] at e vs w; cases e
    have vs := (values_snoc.1 vs).1
    rcases walk_snoc w rfl with w | ⟨r, w, e⟩
    · exact (eval_value hf (.call hk vs w)).elim
    · rw [ih vs w rfl, Option.some.inj e]
  case app_x hl hx _ =>
    rcases xs.eq_nil_or_concat with rfl | ⟨ys, ⟨q, x⟩, rfl⟩; cases e
    simp only [List.concat_eq_append, spine_snoc] at e vs; cases e
    exact (eval_value hx ((values_snoc.1 vs).2 hl)).elim
  all_goals have := spine_head e.symm; simp [unspine] at this

-- Eval is deterministic: a term has at most one next step
theorem eval_det (h : Eval bk t u) (h' : Eval bk t u') : u = u' := by
  have h0 := h
  generalize e : t = s at h'
  induction h generalizing u' s
  case call hk vs w => subst e; exact (call_det hk vs w h').symm
  all_goals
    cases h' <;> first
      | exact call_det ‹_› ‹_› ‹_› (e ▸ h0)
      | (cases e <;> first
          | rfl
          | (exfalso; solve_by_elim [eval_value, Value.lam, Value.prj, Value.mat, Value.lab,
              Value.rfl, rfl])
          | (congr 1 <;> (apply_assumption <;> first | rfl | assumption)); done)
