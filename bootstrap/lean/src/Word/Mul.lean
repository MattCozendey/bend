import Word.Add
import Word.Shift

-- Word.Mul
-- ========
--
-- Base's mul code: Word.mul.go, with Word.add and Word.shl. For each bit of
-- a, from the lowest, it adds b to the sum when the bit is 1, then shifts b
-- left.

open Quan Term Contract

namespace Interp.Word

def mulGoBits : List Bool → List Bool → List Bool → List Bool
  | [], _, acc => acc
  | false :: as, b, acc => mulGoBits as (shlBits b) acc
  | true :: as, b, acc => mulGoBits as (shlBits b) (adcBits false acc b false)

-- goCall n m a b acc: a call of Word.mul.go. n is the width, m the count of
-- bits left in a, and acc the sum.
def goCall (n m a b acc : Term) : Term :=
  App Q1 (App Q2 (App Q1 (App Q1 (App Q2 (Ref "Word.mul.go") n) m) a) b) acc

def mulCode : List (String × Term) :=
  ("Word.mul.go", R.Word.mul.go) :: ("Word.add", R.Word.add) :: (groupCode ++ shlCode)

theorem mulCode_parts (H : HasRefs bk mulCode) :
    HasRef bk "Word.add" R.Word.add ∧ HasRefs bk groupCode ∧ HasRefs bk shlCode := by
  obtain ⟨-, ha, H⟩ := H
  exact ⟨ha, H.of_append⟩

-- Rounds
-- ======

theorem go_round0 (H : HasRefs bk mulCode) (k : Nat) (bs cs : List Bool) :
    step bk (goCall (Bytes.nat k) (Bytes.nat 0) (wordT []) (wordT bs) (wordT cs)) =
      some (wordT cs) := by
  obtain ⟨⟨_, hg, hgv⟩, -⟩ := H
  word_simp [hg, hgv, R.Word.mul.go, goCall, wordT, Bytes.nat]

theorem go_round_f (H : HasRefs bk mulCode) (k j : Nat) (as bs cs : List Bool) :
    step bk (goCall (Bytes.nat k) (boxT "Succ" (Bytes.nat j)) (cellT (bitT false) (wordT as))
        (wordT bs) (wordT cs)) =
      some (goCall (Bytes.nat k) (Bytes.nat j) (wordT as) (callT "Word.shl" [Bytes.nat k, wordT bs])
        (wordT cs)) := by
  obtain ⟨⟨_, hg, hgv⟩, -⟩ := H
  word_simp [hg, hgv, R.Word.mul.go, goCall]

theorem go_round_t (H : HasRefs bk mulCode) (k j : Nat) (as bs cs : List Bool) :
    step bk (goCall (Bytes.nat k) (boxT "Succ" (Bytes.nat j)) (cellT (bitT true) (wordT as))
        (wordT bs) (wordT cs)) =
      some (goCall (Bytes.nat k) (Bytes.nat j) (wordT as) (callT "Word.shl" [Bytes.nat k, wordT bs])
        (callT "Word.add" [Bytes.nat k, wordT cs, wordT bs])) := by
  obtain ⟨⟨_, hg, hgv⟩, -⟩ := H
  word_simp [hg, hgv, R.Word.mul.go, goCall]

-- Word.mul.go on three arguments (go3) or four (go4) waits for more
theorem go3_isValue (H : HasRefs bk mulCode) (k : Nat) : ∀ as : List Bool,
    isValue bk (App Q1 (App Q1 (App Q2 (Ref "Word.mul.go") (Bytes.nat k))
      (Bytes.nat as.length)) (wordT as)) = true
  | [] => by
    obtain ⟨⟨_, hg, hgv⟩, -⟩ := H
    word_simp [hg, hgv, R.Word.mul.go, wordT, Bytes.nat]
  | b :: as => by
    obtain ⟨⟨_, hg, hgv⟩, -⟩ := H
    cases b <;> word_simp [hg, hgv, R.Word.mul.go, wordT, Bytes.nat]

theorem go4_isValue (H : HasRefs bk mulCode) (k : Nat) (bs : List Bool) : ∀ as : List Bool,
    isValue bk (App Q2 (App Q1 (App Q1 (App Q2 (Ref "Word.mul.go") (Bytes.nat k))
      (Bytes.nat as.length)) (wordT as)) (wordT bs)) = true
  | [] => by
    obtain ⟨⟨_, hg, hgv⟩, -⟩ := H
    word_simp [hg, hgv, R.Word.mul.go, wordT, Bytes.nat]
  | b :: as => by
    obtain ⟨⟨_, hg, hgv⟩, -⟩ := H
    cases b <;> word_simp [hg, hgv, R.Word.mul.go, wordT, Bytes.nat]

-- Eval steps in the b and acc arguments of a call of Word.mul.go
theorem evals_go_b (H : HasRefs bk mulCode) (h : Evals bk x x') :
    Evals bk (goCall (Bytes.nat k) (Bytes.nat as.length) (wordT as) x acc)
      (goCall (Bytes.nat k) (Bytes.nat as.length) (wordT as) x' acc) :=
  evals_map (fun y => goCall (Bytes.nat k) (Bytes.nat as.length) (wordT as) y acc)
    (fun e => .app_f (.app_x (isValue_iff.1 (go3_isValue H k as)) rfl e)) h

theorem evals_go_acc (H : HasRefs bk mulCode) (h : Evals bk x x') :
    Evals bk (goCall (Bytes.nat k) (Bytes.nat as.length) (wordT as) (wordT bs) x)
      (goCall (Bytes.nat k) (Bytes.nat as.length) (wordT as) (wordT bs) x') :=
  evals_map (fun y => goCall (Bytes.nat k) (Bytes.nat as.length) (wordT as) (wordT bs) y)
    (fun e => .app_x (isValue_iff.1 (go4_isValue H k bs as)) rfl e) h

theorem go_evals (H : HasRefs bk mulCode) : ∀ (as bs cs : List Bool), cs.length = bs.length →
    Evals bk (goCall (Bytes.nat bs.length) (Bytes.nat as.length) (wordT as) (wordT bs) (wordT cs))
      (wordT (mulGoBits as bs cs))
  | [], bs, cs, _ => .step (step_sound (go_round0 H bs.length bs cs)) .refl
  | false :: as, bs, cs, h => by
    have ⟨_, _, HS⟩ := mulCode_parts H
    have r := Evals.step (step_sound (go_round_f H bs.length as.length as bs cs)) .refl
    have s := evals_go_b (k := bs.length) (as := as) (acc := wordT cs) H (shl_evals HS bs)
    have l : (shlBits bs).length = bs.length := shlBits_length
    have ih := go_evals H as (shlBits bs) cs (h.trans l.symm)
    rw [l] at ih
    exact evals_trans r (evals_trans s ih)
  | true :: as, bs, cs, h => by
    have ⟨ha, HA, HS⟩ := mulCode_parts H
    have r := Evals.step (step_sound (go_round_t H bs.length as.length as bs cs)) .refl
    have s := evals_go_b (k := bs.length) (as := as)
      (acc := callT "Word.add" [Bytes.nat bs.length, wordT cs, wordT bs]) H (shl_evals HS bs)
    have a := add_evals HA ha cs bs h
    rw [h] at a
    have t := evals_go_acc (k := bs.length) (as := as) (bs := shlBits bs) H a
    have l : (shlBits bs).length = bs.length := shlBits_length
    have la : (adcBits false cs bs false).length = (shlBits bs).length := by
      rw [adcBits_length cs bs false false h, h, l]
    have ih := go_evals H as (shlBits bs) (adcBits false cs bs false) la
    rw [l] at ih
    exact evals_trans r (evals_trans s (evals_trans t ih))

end Interp.Word
