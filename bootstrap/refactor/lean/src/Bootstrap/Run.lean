import Bootstrap.Interp

-- Run
-- ===
--
-- Runs of step: Steps (Bootstrap/Eval.lean), computed.

open Quan Term

-- at most fuel more steps of t, after n: the term reached, and the steps in all
def steps (bk : Book) : Nat → Term → Nat → Term × Nat
  | 0, t, n => (t, n)
  | fuel + 1, t, n =>
    match step bk t with
    | some u => steps bk fuel u (n + 1)
    | none => (t, n)

-- a run from any count takes steps of Eval, no more than its fuel
theorem steps_sound_from : steps bk fuel t m = (u, n) → ∃ k, n = m + k ∧ Steps bk k t u ∧ k ≤ fuel := by
  induction fuel generalizing t m with
  | zero =>
    intro h
    simp only [steps, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨0, rfl, .refl, Nat.le_refl 0⟩
  | succ fuel ih =>
    intro h
    simp only [steps] at h
    split at h
    · obtain ⟨k, rfl, s, hk⟩ := ih h
      exact ⟨k + 1, by omega, .step (step_iff.1 ‹_›) s, by omega⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨0, rfl, .refl, Nat.zero_le _⟩

-- a run takes steps of Eval, no more than its fuel
theorem steps_sound : steps bk fuel t 0 = (u, n) → Steps bk n t u ∧ n ≤ fuel := by
  intro h
  obtain ⟨k, rfl, s, hk⟩ := steps_sound_from h
  rw [Nat.zero_add]
  exact ⟨s, hk⟩

-- a run from any count reaches each value that Eval reaches within its fuel
theorem steps_complete_from : Steps bk n t v → Value bk v → n ≤ fuel →
    steps bk fuel t m = (v, m + n) := by
  intro s hv
  induction s generalizing fuel m with
  | refl =>
    intro _
    cases fuel with
    | zero => rfl
    | succ fuel => simp only [steps, step_value hv, Nat.add_zero]
  | step e _ ih =>
    intro hn
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [steps, step_iff.2 e]
      rw [ih hv (by omega)]
      congr 1
      omega

-- a run reaches each value that Eval reaches within its fuel, after as many steps
theorem steps_complete : Steps bk n t v → Value bk v → n ≤ fuel → steps bk fuel t 0 = (v, n) := by
  intro s hv hn
  have h := steps_complete_from (m := 0) s hv hn
  rwa [Nat.zero_add] at h
