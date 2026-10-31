import Bootstrap.Machine.Move

-- Machine.Loop
-- ============
--
-- A run of the machine takes steps of Eval, and reaches each value that Eval
-- reaches, after as many steps.

open Quan Term

namespace Machine

theorem init_ok : (init t).Ok bk :=
  ⟨fun _ h => by simp at h, fun _ h => by simp [init] at h⟩

theorem init_term : (init t).term = t := by
  simp [init, State.term, plugs, Focus.term, close]

-- a run takes steps of Eval, no more than its fuel
theorem run_sound (hs : s.Ok bk) :
    run bk g fuel s m = (u, n) → ∃ k, n = m + k ∧ Steps bk k s.term u ∧ k ≤ fuel := by
  induction g generalizing fuel s m with
  | zero => intro h; exact stepwise_sound h
  | succ g ih =>
    intro h
    simp only [run] at h
    split at h
    · rename_i s' hm
      obtain ⟨hs', he⟩ := move_admin hs hm
      rw [← he]; exact ih hs' h
    · rename_i s' hm
      obtain ⟨hs', he⟩ := move_step hs hm
      split at h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨0, rfl, .refl, Nat.le_refl _⟩
      · rename_i fuel
        obtain ⟨k, rfl, hk, hle⟩ := ih hs' h
        exact ⟨k + 1, by omega, .step he hk, by omega⟩
    · exact stepwise_sound h

-- a run reaches each value that Eval reaches within its fuel, after as many steps
theorem run_complete (hs : s.Ok bk) : Steps bk n s.term v → Value bk v → n ≤ fuel →
    run bk g fuel s m = (v, m + n) := by
  intro hst hv hn
  induction g generalizing fuel s m n with
  | zero => exact stepwise_complete hst hv hn
  | succ g ih =>
    simp only [run]
    split
    · rename_i s' hm
      obtain ⟨hs', he⟩ := move_admin hs hm
      exact ih hs' (he ▸ hst) hn
    · rename_i s' hm
      obtain ⟨hs', he⟩ := move_step hs hm
      cases hst with
      | refl => exact (eval_value he hv).elim
      | step h1 hr =>
        rename_i n' w
        have hw := eval_det h1 he
        subst hw
        cases fuel with
        | zero => omega
        | succ fuel =>
          simp only
          rw [ih hs' hr (by omega)]
          congr 1; omega
    · exact stepwise_complete hst hv hn

end Machine
