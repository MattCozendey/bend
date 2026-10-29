import Bootstrap.Word

-- WordCmp
-- =======
--
-- Base's compare code: Word.cmp, with Word.cmp.fin and Bool.cmp. A call
-- compares the rests first, then this bit decides only when the rests are
-- equal.

open Quan Term Spec

namespace Interp

def boolCmp : Bool → Bool → Ordering
  | false, true => .lt
  | true, false => .gt
  | _, _ => .eq

def finOrd (a b : Bool) : Ordering → Ordering
  | .lt => .lt
  | .eq => boolCmp a b
  | .gt => .gt

def cmpBits : List Bool → List Bool → Ordering
  | a :: as, b :: bs => finOrd a b (cmpBits as bs)
  | _, _ => .eq

structure CmpRefs (bk : Book) : Prop where
  cmp : HasRef bk "Word.cmp" R.Word.cmp
  fin : HasRef bk "Word.cmp.fin" R.Word.cmp.fin
  bool : HasRef bk "Bool.cmp" R.Bool.cmp

def cmpOk (bk : Book) : Bool :=
  hasRef bk "Word.cmp" R.Word.cmp && hasRef bk "Word.cmp.fin" R.Word.cmp.fin &&
  hasRef bk "Bool.cmp" R.Bool.cmp

theorem cmpOk_ok (h : cmpOk bk = true) : CmpRefs bk := by
  simp only [cmpOk, Bool.and_eq_true] at h
  exact ⟨hasRef_ok h.1.1, hasRef_ok h.1.2, hasRef_ok h.2⟩

theorem cmp_round (H : CmpRefs bk) (j : Nat) (as bs : List Bool) (a b : Bool) :
    Evals bk (callT "Word.cmp" [succT (Bytes.nat j), cellT (bitT a) (wordT as),
        cellT (bitT b) (wordT bs)])
      (callT "Word.cmp.fin" [bitT a, bitT b, callT "Word.cmp" [Bytes.nat j, wordT as, wordT bs]]) := by
  obtain ⟨_, hc, hcv⟩ := H.cmp
  apply stepUntil_sound (stop := headIs "Word.cmp.fin") (n := 100)
  cases a <;> cases b <;> word_simp [hc, hcv, R.Word.cmp]

theorem cmp_round0 (H : CmpRefs bk) :
    Evals bk (callT "Word.cmp" [Bytes.nat 0, wordT [], wordT []]) (cmpT .eq) := by
  obtain ⟨_, hc, hcv⟩ := H.cmp
  apply stepUntil_sound (stop := fun _ => false) (n := 50)
  word_simp [hc, hcv, R.Word.cmp, wordT, Bytes.nat, cmpT]

-- Word.cmp.fin on two bits waits for the order of the rests
theorem fin_value (H : CmpRefs bk) (a b : Bool) :
    isValue bk (App Q1 (App Q1 (Ref "Word.cmp.fin") (bitT a)) (bitT b)) = true := by
  obtain ⟨_, hf, hfv⟩ := H.fin
  cases a <;> cases b <;> word_simp [hf, hfv, R.Word.cmp.fin]

theorem fin_evals (H : CmpRefs bk) (a b : Bool) (o : Ordering) :
    Evals bk (callT "Word.cmp.fin" [bitT a, bitT b, cmpT o]) (cmpT (finOrd a b o)) := by
  obtain ⟨_, hf, hfv⟩ := H.fin
  obtain ⟨_, hb, hbv⟩ := H.bool
  apply stepUntil_sound (stop := fun _ => false) (n := 50)
  cases a <;> cases b <;> cases o <;> word_simp [hf, hfv, hb, hbv, R.Word.cmp.fin, R.Bool.cmp,
    cmpT, finOrd, boolCmp]

theorem cmp_evals (H : CmpRefs bk) : ∀ (as bs : List Bool), as.length = bs.length →
    Evals bk (callT "Word.cmp" [Bytes.nat as.length, wordT as, wordT bs]) (cmpT (cmpBits as bs))
  | [], [], _ => cmp_round0 H
  | a :: as, b :: bs, h =>
    evals_trans (cmp_round H as.length as bs a b)
      (evals_trans (evals_arg (fin_value H a b) rfl (cmp_evals H as bs (by simpa using h)))
        (fin_evals H a b _))
  | [], _ :: _, h | _ :: _, [], h => by simp at h

end Interp
