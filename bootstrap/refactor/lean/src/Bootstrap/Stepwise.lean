import Bootstrap.Interp

-- Stepwise
-- ========
--
-- Runs of step, one step at a time: Steps (Bootstrap/Eval.lean), computed.
-- Each step starts again from the top of the term. The machine
-- (Bootstrap/Machine.lean) is fast, and hands over to this when it stops.

open Quan Term

-- at most fuel more steps of t, after n: the term reached, and the steps in all
def stepwise (bk : Book) : Nat → Term → Nat → Term × Nat
  | 0, t, n => (t, n)
  | fuel + 1, t, n =>
    match step bk t with
    | some u => stepwise bk fuel u (n + 1)
    | none => (t, n)

-- a run from any count takes steps of Eval, no more than its fuel
theorem stepwise_sound : stepwise bk fuel t m = (u, n) → ∃ k, n = m + k ∧ Steps bk k t u ∧ k ≤ fuel := by
  induction fuel generalizing t m with
  | zero =>
    intro h
    simp only [stepwise, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨0, rfl, .refl, Nat.le_refl 0⟩
  | succ fuel ih =>
    intro h
    simp only [stepwise] at h
    split at h
    · obtain ⟨k, rfl, s, hk⟩ := ih h
      exact ⟨k + 1, by omega, .step (step_iff.1 ‹_›) s, by omega⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨0, rfl, .refl, Nat.zero_le _⟩

-- a run from any count reaches each value that Eval reaches within its fuel
theorem stepwise_complete : Steps bk n t v → Value bk v → n ≤ fuel →
    stepwise bk fuel t m = (v, m + n) := by
  intro s hv
  induction s generalizing fuel m with
  | refl =>
    intro _
    cases fuel with
    | zero => rfl
    | succ fuel => simp only [stepwise, step_value hv, Nat.add_zero]
  | step e _ ih =>
    intro hn
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [stepwise, step_iff.2 e]
      rw [ih hv (by omega)]
      congr 1
      omega
