import Bootstrap.Machine.Loop

-- Run
-- ===
--
-- Runs of Eval: Steps (Bootstrap/Eval.lean), computed by the machine
-- (Bootstrap/Machine.lean).

open Quan Term

-- at most fuel more steps of t, after n: the term reached, and the steps in all
def steps (bk : Book) (fuel : Nat) (t : Term) (n : Nat) : Term × Nat :=
  Machine.run bk Machine.gas fuel (Machine.init t) n

-- a run from any count takes steps of Eval, no more than its fuel
theorem steps_sound_from : steps bk fuel t m = (u, n) → ∃ k, n = m + k ∧ Steps bk k t u ∧ k ≤ fuel := by
  intro h
  have := Machine.run_sound Machine.init_ok h
  rwa [Machine.init_term] at this

-- a run takes steps of Eval, no more than its fuel
theorem steps_sound : steps bk fuel t 0 = (u, n) → Steps bk n t u ∧ n ≤ fuel := by
  intro h
  obtain ⟨k, rfl, s, hk⟩ := steps_sound_from h
  rw [Nat.zero_add]
  exact ⟨s, hk⟩

-- a run from any count reaches each value that Eval reaches within its fuel
theorem steps_complete_from : Steps bk n t v → Value bk v → n ≤ fuel →
    steps bk fuel t m = (v, m + n) := by
  intro s hv hn
  exact Machine.run_complete Machine.init_ok (by rwa [Machine.init_term]) hv hn

-- a run reaches each value that Eval reaches within its fuel, after as many steps
theorem steps_complete : Steps bk n t v → Value bk v → n ≤ fuel → steps bk fuel t 0 = (v, n) := by
  intro s hv hn
  have h := steps_complete_from (m := 0) s hv hn
  rwa [Nat.zero_add] at h
