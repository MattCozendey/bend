import Bootstrap.Code
import Bootstrap.Copy.Reader

-- Read.Nat
-- ========
--
-- Base's U32.to_nat, which the reader calls on each tag, gives the cell's value.

open Quan Term

-- the field of a Succ takes its steps
theorem Steps.succ (h : Steps B n x x') :
    Steps B n (ctor "Succ" [x]) (ctor "Succ" [x']) := by
  induction h with
  | refl => exact .refl
  | step e _ ih => exact .step (.tup_b (fun _ => .lab) (.tup_a rfl e)) ih

-- Nat.double doubles a nat
theorem double_nat (h : Contains B reader) :
    Runs B (App Q1 (Ref "Nat.double") (Form.nat m)) (Form.nat (2 * m)) := by
  have hk := h «reader.Nat.double» (by simp [reader])
  induction m with
  | zero =>
    refine .step (Eval.walk (xs := [(Q1, _)]) hk (.cons (fun _ => value_nat) .nil) ?_)
      (.refl value_nat)
    simp [walk, «reader.Nat.double», Form.nat, ctor, takes, Quan.live, Quan.fld, sub, spine]
  | succ m ih =>
    refine .step (Eval.walk (xs := [(Q1, _)])
      (u := ctor "Succ" [ctor "Succ" [App Q1 (Ref "Nat.double") (Form.nat m)]])
      hk (.cons (fun _ => value_nat) .nil) ?_) ?_
    · simp [walk, «reader.Nat.double», Form.nat, ctor, takes, Quan.live, Quan.fld, sub, spine,
        bindsAt, Env.sub]
    · obtain ⟨n, s, _⟩ := ih
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega]
      exact ⟨n, s.succ.succ, value_nat⟩

-- Nat.double alone is a value
theorem value_double (h : Contains B reader) : Value B (Ref "Nat.double") :=
  .call (xs := []) (h «reader.Nat.double» (by simp [reader])) .nil
    (walk_iff.1 (by simp [walk, «reader.Nat.double», takes]))

-- Word.to_nat reads a Word(n) as its value modulo 2 ^ n
theorem word_nat (h : Contains B reader) :
    Runs B (App Q1 (App Q1 (Ref "Word.to_nat") (Form.nat n)) (bits n v))
      (Form.nat (v % 2 ^ n)) := by
  have hk := h «reader.Word.to_nat» (by simp [reader])
  have vs : Values B [(Q1, Form.nat n), (Q1, bits n v)] :=
    .cons (fun _ => value_nat) (.cons (fun _ => value_bits) .nil)
  induction n generalizing v with
  | zero =>
    rw [Nat.pow_zero, Nat.mod_one]
    refine .step (Eval.walk (xs := [(Q1, _), (Q1, _)]) (u := Form.nat 0) hk vs ?_)
      (.refl value_nat)
    simp [walk, «reader.Word.to_nat», Form.nat, bits, ctor, takes, Quan.live, Quan.fld, sub,
      spine, bindsAt]
  | succ n ih =>
    have e : v % 2 ^ (n + 1) = v % 2 + 2 * (v / 2 % 2 ^ n) := by
      rw [Nat.pow_succ', Nat.mod_mul]
    obtain ⟨k, s, -⟩ := double_nat (m := v / 2 % 2 ^ n) h
    obtain ⟨j, t, -⟩ :=
      ih (v := v / 2) (.cons (fun _ => value_nat) (.cons (fun _ => value_bits) .nil))
    have r := Runs.steps (Steps.app_x (value_double h) rfl t) ⟨k, s, value_nat⟩
    rcases Nat.mod_two_eq_zero_or_one v with hv | hv
    · refine .step (Eval.walk (xs := [(Q1, _), (Q1, _)])
        (u := App Q1 (Ref "Nat.double")
          (App Q1 (App Q1 (Ref "Word.to_nat") (Form.nat n)) (bits n (v / 2))))
        hk vs ?_) ?_
      · simp [walk, «reader.Word.to_nat», Form.nat, bits, ctor, takes, Quan.live, Quan.fld, sub,
          spine, bindsAt, Env.sub, data_iff.2 data_nat, hv]
      · rw [e, hv, Nat.zero_add]; exact r
    · refine .step (Eval.walk (xs := [(Q1, _), (Q1, _)])
        (u := ctor "Succ" [App Q1 (Ref "Nat.double")
          (App Q1 (App Q1 (Ref "Word.to_nat") (Form.nat n)) (bits n (v / 2)))])
        hk vs ?_) ?_
      · simp [walk, «reader.Word.to_nat», Form.nat, bits, ctor, takes, Quan.live, Quan.fld, sub,
          spine, bindsAt, Env.sub, data_iff.2 data_nat, hv]
      · obtain ⟨i, u, -⟩ := r
        rw [e, hv, Nat.add_comm]
        exact ⟨i, u.succ, value_nat⟩

theorem to_nat_cell : Contains B reader →
    Runs B (App Q1 (Ref "U32.to_nat") (cell b)) (Form.nat b.toNat) := by
  intro h
  have hk := h «reader.U32.to_nat» (by simp [reader])
  have hb : b.toNat % 2 ^ 32 = b.toNat := Nat.mod_eq_of_lt (by have := b.toNat_lt; omega)
  refine .step (Eval.walk (xs := [(Q1, _)])
    (u := App Q1 (App Q1 (Ref "Word.to_nat") (Form.nat 32)) (bits 32 b.toNat))
    hk (.cons (fun _ => value_cell) .nil) ?_) ?_
  · simp [walk, «reader.U32.to_nat», cell, ctor, takes, Quan.live, Quan.fld, sub, spine, bindsAt,
      Env.sub, Form.nat]
  · have r := word_nat h (n := 32) (v := b.toNat)
    rwa [hb] at r
