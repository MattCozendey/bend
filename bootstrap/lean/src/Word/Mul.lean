import Word.Add
import Word.Shift

-- Word.Mul
-- ========
--
-- Base's mul code: Word.mul.go. For each bit of a, from the lowest, it
-- shifts b left, and on a 1 bit it first adds b to the sum. A call on
-- words reaches the word that mulGoBits gives, for each width.

open Quan Term Contract

namespace Interp.Word

def mulGoBits : List Bool → List Bool → List Bool → List Bool
  | [], _, acc => acc
  | false :: as, b, acc => mulGoBits as (shlBits b) acc
  | true :: as, b, acc => mulGoBits as (shlBits b) (adcBits false acc b false)

-- a call of Word.mul.go: width n, count m, word a, word b, sum acc
def goCall (n m a b acc : Term) : Term :=
  App Q1 (App Q2 (App Q1 (App Q1 (App Q2 (Ref "Word.mul.go") n) m) a) b) acc

structure HasMul (bk : Book) : Prop where
  go : HasRef bk "Word.mul.go" R.Word.mul.go
  add : HasRef bk "Word.add" R.Word.add
  adds : HasAdd bk
  shl : HasShl bk

def hasMul (bk : Book) : Bool :=
  hasRef bk "Word.mul.go" R.Word.mul.go && hasRef bk "Word.add" R.Word.add && hasAdd bk && hasShl bk

theorem hasMul_sound (h : hasMul bk = true) : HasMul bk := by
  simp only [hasMul, Bool.and_eq_true] at h
  exact ⟨hasRef_sound h.1.1.1, hasRef_sound h.1.1.2, hasAdd_sound h.1.2, hasShl_sound h.2⟩

-- Rounds
-- ======

theorem go_round0 (H : HasMul bk) (k : Nat) (bs cs : List Bool) :
    step bk (goCall (Bytes.nat k) (Bytes.nat 0) (wordT []) (wordT bs) (wordT cs)) =
      some (wordT cs) := by
  obtain ⟨_, hg, hgv⟩ := H.go
  word_simp [hg, hgv, R.Word.mul.go, goCall, wordT, Bytes.nat]

theorem go_round_f (H : HasMul bk) (k j : Nat) (as bs cs : List Bool) :
    step bk (goCall (Bytes.nat k) (succT (Bytes.nat j)) (cellT (bitT false) (wordT as))
        (wordT bs) (wordT cs)) =
      some (goCall (Bytes.nat k) (Bytes.nat j) (wordT as) (callT "Word.shl" [Bytes.nat k, wordT bs])
        (wordT cs)) := by
  obtain ⟨_, hg, hgv⟩ := H.go
  word_simp [hg, hgv, R.Word.mul.go, goCall]

theorem go_round_t (H : HasMul bk) (k j : Nat) (as bs cs : List Bool) :
    step bk (goCall (Bytes.nat k) (succT (Bytes.nat j)) (cellT (bitT true) (wordT as))
        (wordT bs) (wordT cs)) =
      some (goCall (Bytes.nat k) (Bytes.nat j) (wordT as) (callT "Word.shl" [Bytes.nat k, wordT bs])
        (callT "Word.add" [Bytes.nat k, wordT cs, wordT bs])) := by
  obtain ⟨_, hg, hgv⟩ := H.go
  word_simp [hg, hgv, R.Word.mul.go, goCall]

-- Word.mul.go on a width, a count and a word of that count waits for more
theorem go3_isValue (H : HasMul bk) (k : Nat) : ∀ as : List Bool,
    isValue bk (App Q1 (App Q1 (App Q2 (Ref "Word.mul.go") (Bytes.nat k))
      (Bytes.nat as.length)) (wordT as)) = true
  | [] => by
    obtain ⟨_, hg, hgv⟩ := H.go
    word_simp [hg, hgv, R.Word.mul.go, wordT, Bytes.nat]
  | b :: as => by
    obtain ⟨_, hg, hgv⟩ := H.go
    cases b <;> word_simp [hg, hgv, R.Word.mul.go, wordT, Bytes.nat]

theorem go4_isValue (H : HasMul bk) (k : Nat) (bs : List Bool) : ∀ as : List Bool,
    isValue bk (App Q2 (App Q1 (App Q1 (App Q2 (Ref "Word.mul.go") (Bytes.nat k))
      (Bytes.nat as.length)) (wordT as)) (wordT bs)) = true
  | [] => by
    obtain ⟨_, hg, hgv⟩ := H.go
    word_simp [hg, hgv, R.Word.mul.go, wordT, Bytes.nat]
  | b :: as => by
    obtain ⟨_, hg, hgv⟩ := H.go
    cases b <;> word_simp [hg, hgv, R.Word.mul.go, wordT, Bytes.nat]

-- Eval steps in the b and acc arguments of a call of Word.mul.go
theorem evals_go_b (H : HasMul bk) (h : Evals bk x x') :
    Evals bk (goCall (Bytes.nat k) (Bytes.nat as.length) (wordT as) x acc)
      (goCall (Bytes.nat k) (Bytes.nat as.length) (wordT as) x' acc) :=
  evals_map (fun y => goCall (Bytes.nat k) (Bytes.nat as.length) (wordT as) y acc)
    (fun e => .app_f (.app_x (isValue_iff.1 (go3_isValue H k as)) rfl e)) h

theorem evals_go_acc (H : HasMul bk) (h : Evals bk x x') :
    Evals bk (goCall (Bytes.nat k) (Bytes.nat as.length) (wordT as) (wordT bs) x)
      (goCall (Bytes.nat k) (Bytes.nat as.length) (wordT as) (wordT bs) x') :=
  evals_map (fun y => goCall (Bytes.nat k) (Bytes.nat as.length) (wordT as) (wordT bs) y)
    (fun e => .app_x (isValue_iff.1 (go4_isValue H k bs as)) rfl e) h

-- a call of Word.mul.go on words reaches the word that mulGoBits gives
theorem go_evals (H : HasMul bk) : ∀ (as bs cs : List Bool), cs.length = bs.length →
    Evals bk (goCall (Bytes.nat bs.length) (Bytes.nat as.length) (wordT as) (wordT bs) (wordT cs))
      (wordT (mulGoBits as bs cs))
  | [], bs, cs, _ => .step (step_sound (go_round0 H bs.length bs cs)) .refl
  | false :: as, bs, cs, h => by
    have r := Evals.step (step_sound (go_round_f H bs.length as.length as bs cs)) .refl
    have s := evals_go_b (k := bs.length) (as := as) (acc := wordT cs) H (shl_evals H.shl bs)
    have l : (shlBits bs).length = bs.length := shlBits_length
    have ih := go_evals H as (shlBits bs) cs (h.trans l.symm)
    rw [l] at ih
    exact evals_trans r (evals_trans s ih)
  | true :: as, bs, cs, h => by
    have r := Evals.step (step_sound (go_round_t H bs.length as.length as bs cs)) .refl
    have s := evals_go_b (k := bs.length) (as := as)
      (acc := callT "Word.add" [Bytes.nat bs.length, wordT cs, wordT bs]) H (shl_evals H.shl bs)
    have a := add_evals H.adds H.add cs bs h
    rw [h] at a
    have t := evals_go_acc (k := bs.length) (as := as) (bs := shlBits bs) H a
    have l : (shlBits bs).length = bs.length := shlBits_length
    have la : (adcBits false cs bs false).length = (shlBits bs).length := by
      rw [adcBits_length cs bs false false h, h, l]
    have ih := go_evals H as (shlBits bs) (adcBits false cs bs false) la
    rw [l] at ih
    exact evals_trans r (evals_trans s (evals_trans t ih))

end Interp.Word
