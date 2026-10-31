import Bootstrap.Run
import Bootstrap.Bytes

-- Program
-- =======
--
-- What a program gives on a list of bytes (INVARIANTS #3), and the
-- interpreter of STEPS #2, which computes it.

open Quan Term

-- the start of a program's run: main, applied once at quantity 1 to the
-- input's bytes
def start (i : List UInt8) : Term := App Q1 (Ref "main") (bytes i)

-- INVARIANTS #3: the run from the start reaches, after exactly n steps, a
-- value v that is the list of bytes r
def Gives (bk : Book) (i r : List UInt8) (n : Nat) : Prop :=
  ∃ v, Steps bk n (start i) v ∧ Value bk v ∧ unbytes v = some r

-- a program gives at most one result, after one number of steps
theorem gives_det : Gives bk i r n → Gives bk i r' n' → r = r' ∧ n = n' := by
  rintro ⟨v, hs, hv, hu⟩ ⟨v', hs', hv', hu'⟩
  obtain ⟨rfl, rfl⟩ := steps_det hs hv hs' hv'
  exact ⟨Option.some.inj (hu.symm.trans hu'), rfl⟩

def interp (bk : Book) (fuel : Nat) (i : List UInt8) : Option (List UInt8 × Nat) :=
  let (v, n) := steps bk fuel (start i) 0
  if value bk v then (unbytes v).map (·, n) else none

-- the interpreter: no extra result, no missing result, the same number of steps
theorem interp_iff : interp bk fuel i = some (r, n) ↔ Gives bk i r n ∧ n ≤ fuel := by
  unfold interp
  generalize hrun : steps bk fuel (start i) 0 = p
  obtain ⟨v, m⟩ := p
  obtain ⟨hs, hm⟩ := steps_sound hrun
  constructor
  · intro h
    by_cases hv : value bk v = true
    · simp only [hv, ite_true, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨r', hu, rfl, rfl⟩ := h
      exact ⟨⟨v, hs, (value_iff).1 hv, hu⟩, hm⟩
    · simp [hv] at h
  · rintro ⟨⟨v', hs', hv', hu'⟩, hn⟩
    rw [steps_complete hs' hv' hn] at hrun
    cases hrun
    simp [(value_iff).2 hv', hu']
