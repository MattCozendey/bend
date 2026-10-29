import Contract.Spec

-- Bytes
-- =====
--
-- The proof of claim 3 (bytes): bytes go in and out without change.

open Quan Term Contract

namespace Interp

theorem nat_in (n : Nat) : ∃ o, observe (Bytes.nat n) = some o ∧ Bytes.ofNat o = some n := by
  induction n with
  | zero => exact ⟨_, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨o, ho, hn⟩ := ih
    exact ⟨.tup (.lab "Succ") (.tup o (.lab "()")), by simp [Bytes.nat, observe, ho, Quan.live],
      by simp [Bytes.ofNat, hn]⟩

theorem nat_out (h : Bytes.ofNat o = some n) : observe (Bytes.nat n) = some o := by
  fun_induction Bytes.ofNat o generalizing n with
  | case1 => cases h; rfl
  | case2 o ih =>
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.1 h
    simp [Bytes.nat, observe, ih hm, Quan.live]
  | case3 => simp at h

theorem bytes_in (bs : List UInt8) :
    ∃ o, observe (Bytes.term bs) = some o ∧ Bytes.ofObs o = some bs := by
  induction bs with
  | nil => exact ⟨_, rfl, rfl⟩
  | cons b bs ih =>
    obtain ⟨o, ho, hb⟩ := ih
    obtain ⟨on, hon, hn⟩ := nat_in b.toNat
    refine ⟨.tup (.lab "Con") (.tup on (.tup o (.lab "()"))),
      by simp [Bytes.term, observe, ho, hon, Quan.live], ?_⟩
    have lt : b.toNat < 256 := UInt8.toNat_lt b
    simp [Bytes.ofObs, hn, hb, lt]

theorem bytes_out (h : Bytes.ofObs o = some bs) : observe (Bytes.term bs) = some o := by
  fun_induction Bytes.ofObs o generalizing bs with
  | case1 => cases h; rfl
  | case2 hd tl ih =>
    cases hn : Bytes.ofNat hd with
    | none => simp [hn] at h
    | some n =>
      by_cases lt : n < 256
      · cases hbs : Bytes.ofObs tl with
        | none => simp [hn, hbs] at h
        | some bs' =>
          simp [hn, lt, hbs] at h
          subst h
          have hb : (n.toUInt8).toNat = n := by simp [Nat.mod_eq_of_lt lt]
          simp [Bytes.term, observe, ih hbs, hb, nat_out hn, Quan.live]
      · simp [hn, lt] at h
  | case3 => simp at h

theorem claim_bytes : Claim.bytes := by
  refine ⟨fun bs => ?_, fun o bs h => bytes_out h⟩
  obtain ⟨o, ho, hb⟩ := bytes_in bs
  simp [ho, hb]

end Interp
