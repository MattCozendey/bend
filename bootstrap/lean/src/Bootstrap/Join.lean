import Bootstrap.Code

-- Join
-- ====
--
-- Step 3 of the plan: what the Bend laws that --verdict accepts say about
-- runs. --verdict is Book.check on the kernel's parse of the `bend -o` text.
-- The kernel's adequate (bend2/bendtt.lean) turns a checked proof of a == b
-- into a conversion of a and b, and conv_runs turns that into a run.

open Quan Term

-- Data with no dead part: labels, Rfl, and pairs of it at a live quantity
inductive Plain : Term → Prop
  | lab : Plain (Lab k)
  | rfl : Plain Rfl
  | tup : q.live = true → Plain a → Plain b → Plain (Tup q a b)

-- a pair reduces only to a pair at its quantity, field by field
private theorem pars_tup : Pars B (Tup q x y) c →
    ∃ x' y', c = Tup q x' y' ∧ Pars B x x' ∧ Pars B y y' := by
  intro h
  generalize e : Tup q x y = t at h
  induction h generalizing x y with
  | refl => subst e; exact ⟨_, _, rfl, .refl, .refl⟩
  | step s _ ih =>
    subst e; cases s with
    | tup s1 s2 =>
      obtain ⟨x', y', rfl, p1, p2⟩ := ih rfl
      exact ⟨x', y', rfl, .step s1 p1, .step s2 p2⟩

-- a plain term reduces only to itself
private theorem plain_fix (hb : Plain b) : Pars B b c → c = b := by
  induction hb generalizing c with
  | lab => exact lab_fix
  | rfl => exact pars_fix fun _ s => by cases s; rfl
  | tup _ _ _ iha ihb =>
    intro h
    obtain ⟨x', y', rfl, p1, p2⟩ := pars_tup h
    rw [iha p1, ihb p2]

-- a Data term that reduces to a plain term is that term
private theorem data_pars (hb : Plain b) : Data v → Pars B v b → v = b := by
  induction hb generalizing v with
  | lab =>
    intro hv h; cases hv with
    | lab => exact (lab_fix h).symm
    | rfl => cases (pars_fix (fun _ s => by cases s; rfl) h)
    | tup => obtain ⟨_, _, e, _⟩ := pars_tup h; cases e
  | rfl =>
    intro hv h; cases hv with
    | lab => cases lab_fix h
    | rfl => rfl
    | tup => obtain ⟨_, _, e, _⟩ := pars_tup h; cases e
  | tup hq _ _ iha ihb =>
    intro hv h; cases hv with
    | lab => cases lab_fix h
    | rfl => cases (pars_fix (fun _ s => by cases s; rfl) h)
    | tup da db =>
      obtain ⟨_, _, e, p1, p2⟩ := pars_tup h
      cases e
      rw [iha (da hq) p1, ihb db p2]

-- a closed typed term whose evaluation is accessible runs to a value it reduces to
private theorem runs_acc (wt : Book.WellTyped B) (lv : Book.Live B) :
    Acc (fun u t => Eval B t u) t → Typed B [] t A → ∃ v, Runs B t v ∧ Pars B t v := by
  intro hacc
  induction hacc with
  | intro t _ ih =>
    intro ht
    rcases progress B t A wt lv ht with hv | ⟨u, e⟩
    · exact ⟨t, Runs.refl hv, .refl⟩
    · have pu := eval_pars lv.1 e
      obtain ⟨v, r, p⟩ := ih u e (pars_sr wt ht pu)
      exact ⟨v, Runs.step e r, pars_trans pu p⟩

-- in a book that --verdict accepts, a closed, live term a of a Data type,
-- that converts to the plain b, runs to b
theorem conv_runs : Book.check B = .ok () → Term.Closed a → Term.Live B a →
    Typed B [] a A → Typed B [] A T2 → Plain b → Conv B a b → Runs B a b := by
  intro hc hcl hl ht hT hb hv
  obtain ⟨wt, lv⟩ := book_check B hc
  obtain ⟨v, r, pv⟩ := runs_acc wt lv (halts B a lv hcl hl) ht
  obtain ⟨c, pa, pb⟩ := hv
  cases plain_fix hb pb
  obtain ⟨d, p1, p2⟩ := confluent B a v _ pv pa
  cases plain_fix hb p2
  obtain ⟨n, s, vv⟩ := r
  have dv := canon_data wt vv (pars_sr wt ht pv) hT
  rw [← data_pars hb dv p1]
  exact ⟨n, s, vv⟩

-- a run's steps are reductions
private theorem steps_pars (cl : Book.Closed B) : Steps B n a b → Pars B a b := by
  intro s
  induction s with
  | refl => exact .refl
  | step e _ ih => exact pars_trans (eval_pars cl e) ih

-- in a book that --verdict accepts, a run of a to b proves a == b
theorem runs_rfl : Book.check B = .ok () → Runs B a b → Typed B Γ Rfl (Eql a b T) := by
  rintro hc ⟨_, s, _⟩
  exact .rfl ⟨b, steps_pars (book_check B hc).2.1 s, .refl⟩
