import Bootstrap.Word

-- WordNat
-- =======
--
-- Base's inc code (Word.inc) and its code from a word to a Nat
-- (Word.to_nat, with Nat.double).

open Quan Term Spec

namespace Interp

-- Inc
-- ===

def incBits : List Bool → List Bool
  | [] => []
  | false :: bs => true :: bs
  | true :: bs => false :: incBits bs

def incOk (bk : Book) : Bool := hasRef bk "Word.inc" R.Word.inc

theorem inc_round0 (H : HasRef bk "Word.inc" R.Word.inc) :
    Evals bk (callT "Word.inc" [Bytes.nat 0, wordT []]) (wordT []) := by
  obtain ⟨_, hi, hiv⟩ := H
  apply stepUntil_sound (stop := fun _ => false) (n := 50)
  word_simp [hi, hiv, R.Word.inc, wordT, Bytes.nat]

-- a 0 bit becomes 1, and the rest stays
theorem inc_round_f (H : HasRef bk "Word.inc" R.Word.inc) (j : Nat) (t : List Bool) :
    Evals bk (callT "Word.inc" [succT (Bytes.nat j), cellT (bitT false) (wordT t)])
      (cellT (bitT true) (wordT t)) := by
  obtain ⟨_, hi, hiv⟩ := H
  apply stepUntil_sound (stop := fun _ => false) (n := 100)
  word_simp [hi, hiv, R.Word.inc]

-- a 1 bit becomes 0, and the rest carries
theorem inc_round_t (H : HasRef bk "Word.inc" R.Word.inc) (j : Nat) (t : List Bool) :
    Evals bk (callT "Word.inc" [succT (Bytes.nat j), cellT (bitT true) (wordT t)])
      (cellT (bitT false) (callT "Word.inc" [Bytes.nat j, wordT t])) := by
  obtain ⟨_, hi, hiv⟩ := H
  apply stepUntil_sound (stop := cellEnd "Word.inc") (n := 100)
  word_simp [hi, hiv, R.Word.inc]

theorem inc_evals (H : HasRef bk "Word.inc" R.Word.inc) : ∀ bs : List Bool,
    Evals bk (callT "Word.inc" [Bytes.nat bs.length, wordT bs]) (wordT (incBits bs))
  | [] => inc_round0 H
  | false :: bs => inc_round_f H bs.length bs
  | true :: bs => evals_trans (inc_round_t H bs.length bs) (evals_rest (inc_evals H bs))

-- To Nat
-- ======

def toNatBits : List Bool → Nat
  | [] => 0
  | false :: bs => 2 * toNatBits bs
  | true :: bs => 2 * toNatBits bs + 1

structure ToNatRefs (bk : Book) : Prop where
  word : HasRef bk "Word.to_nat" R.Word.to_nat
  double : HasRef bk "Nat.double" R.Nat.double

def toNatOk (bk : Book) : Bool :=
  hasRef bk "Word.to_nat" R.Word.to_nat && hasRef bk "Nat.double" R.Nat.double

theorem toNatOk_ok (h : toNatOk bk = true) : ToNatRefs bk := by
  simp only [toNatOk, Bool.and_eq_true] at h
  exact ⟨hasRef_ok h.1, hasRef_ok h.2⟩

-- a Succ whose pred is a call of def k
def succEnd (k : String) : Term → Bool
  | Tup _ (Lab "Succ") (Tup _ x (Lab "()")) => headIs k x
  | _ => false

-- a Succ of a Succ whose pred is a call of def k
def succ2End (k : String) : Term → Bool
  | Tup _ (Lab "Succ") (Tup _ x (Lab "()")) => succEnd k x
  | _ => false

-- Eval steps in the pred of a Succ
theorem evals_succ (h : Evals bk x x') : Evals bk (succT x) (succT x') :=
  evals_map succT (fun e => .tup_b (fun _ => .lab) (.tup_a rfl e)) h

theorem double_value (H : ToNatRefs bk) : isValue bk (Ref "Nat.double") = true := by
  obtain ⟨_, hd, hdv⟩ := H.double
  word_simp [hd, hdv, R.Nat.double]

theorem double_round (H : ToNatRefs bk) (v : Nat) :
    Evals bk (callT "Nat.double" [succT (Bytes.nat v)])
      (succT (succT (callT "Nat.double" [Bytes.nat v]))) := by
  obtain ⟨_, hd, hdv⟩ := H.double
  apply stepUntil_sound (stop := succ2End "Nat.double") (n := 50)
  word_simp [succ2End, succEnd, hd, hdv, R.Nat.double]

theorem double_round0 (H : ToNatRefs bk) :
    Evals bk (callT "Nat.double" [Bytes.nat 0]) (Bytes.nat 0) := by
  obtain ⟨_, hd, hdv⟩ := H.double
  apply stepUntil_sound (stop := fun _ => false) (n := 50)
  word_simp [hd, hdv, R.Nat.double, Bytes.nat]

theorem double_evals (H : ToNatRefs bk) : ∀ v : Nat,
    Evals bk (callT "Nat.double" [Bytes.nat v]) (Bytes.nat (2 * v))
  | 0 => double_round0 H
  | v + 1 => by
    have e : Bytes.nat (2 * (v + 1)) = succT (succT (Bytes.nat (2 * v))) := by
      rw [show 2 * (v + 1) = 2 * v + 1 + 1 by omega]; rfl
    rw [e]
    exact evals_trans (double_round H v) (evals_succ (evals_succ (double_evals H v)))

theorem toNat_round0 (H : ToNatRefs bk) :
    Evals bk (callT "Word.to_nat" [Bytes.nat 0, wordT []]) (Bytes.nat 0) := by
  obtain ⟨_, hw, hwv⟩ := H.word
  apply stepUntil_sound (stop := fun _ => false) (n := 50)
  word_simp [hw, hwv, R.Word.to_nat, wordT, Bytes.nat]

theorem toNat_round_f (H : ToNatRefs bk) (j : Nat) (t : List Bool) :
    Evals bk (callT "Word.to_nat" [succT (Bytes.nat j), cellT (bitT false) (wordT t)])
      (callT "Nat.double" [callT "Word.to_nat" [Bytes.nat j, wordT t]]) := by
  obtain ⟨_, hw, hwv⟩ := H.word
  apply stepUntil_sound (stop := headIs "Nat.double") (n := 100)
  word_simp [hw, hwv, R.Word.to_nat]

theorem toNat_round_t (H : ToNatRefs bk) (j : Nat) (t : List Bool) :
    Evals bk (callT "Word.to_nat" [succT (Bytes.nat j), cellT (bitT true) (wordT t)])
      (succT (callT "Nat.double" [callT "Word.to_nat" [Bytes.nat j, wordT t]])) := by
  obtain ⟨_, hw, hwv⟩ := H.word
  apply stepUntil_sound (stop := succEnd "Nat.double") (n := 100)
  word_simp [succEnd, hw, hwv, R.Word.to_nat]

theorem toNat_evals (H : ToNatRefs bk) : ∀ bs : List Bool,
    Evals bk (callT "Word.to_nat" [Bytes.nat bs.length, wordT bs]) (Bytes.nat (toNatBits bs))
  | [] => toNat_round0 H
  | false :: bs =>
    evals_trans (toNat_round_f H bs.length bs)
      (evals_trans (evals_arg (double_value H) rfl (toNat_evals H bs)) (double_evals H _))
  | true :: bs =>
    evals_trans (toNat_round_t H bs.length bs)
      (evals_succ (evals_trans (evals_arg (double_value H) rfl (toNat_evals H bs))
        (double_evals H _)))

end Interp
