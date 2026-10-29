import Word.Shared

-- Word.Shift
-- ==========
--
-- Base's shift code: Word.shl (with Word.shl.put) and Word.shr (with
-- Word.shr.pad). A word is lowest bit first, so shl puts a 0 bit first,
-- and shr drops the first bit and puts a 0 bit last.

open Quan Term Contract

namespace Interp.Word

-- putBits c bs: c, then bs without its last bit
def putBits (c : Bool) : List Bool → List Bool
  | [] => []
  | b :: bs => c :: putBits b bs

def shlBits : List Bool → List Bool
  | [] => []
  | b :: bs => false :: putBits b bs

-- padBits bs: bs, then a 0 bit
def padBits : List Bool → List Bool
  | [] => [false]
  | b :: bs => b :: padBits bs

def shrBits : List Bool → List Bool
  | [] => []
  | _ :: bs => padBits bs

theorem putBits_length : (putBits c bs).length = bs.length := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih => simp [putBits, ih]

theorem shlBits_length : (shlBits bs).length = bs.length := by
  cases bs <;> simp [shlBits, putBits_length]

-- Shl
-- ===

structure HasShl (bk : Book) : Prop where
  shl : HasRef bk "Word.shl" R.Word.shl
  put : HasRef bk "Word.shl.put" R.Word.shl.put

def hasShl (bk : Book) : Bool :=
  hasRef bk "Word.shl" R.Word.shl && hasRef bk "Word.shl.put" R.Word.shl.put

theorem hasShl_sound (h : hasShl bk = true) : HasShl bk := by
  simp only [hasShl, Bool.and_eq_true] at h
  exact ⟨hasRef_sound h.1, hasRef_sound h.2⟩

theorem put_round (H : HasShl bk) (j : Nat) (t : List Bool) (c b : Bool) :
    Evals bk (callT "Word.shl.put" [succT (Bytes.nat j), bitT c, cellT (bitT b) (wordT t)])
      (cellT (bitT c) (callT "Word.shl.put" [Bytes.nat j, bitT b, wordT t])) := by
  obtain ⟨_, hp, hpv⟩ := H.put
  apply stepUntil_sound (stop := cellEnd "Word.shl.put") (n := 100)
  cases c <;> cases b <;> word_simp [hp, hpv, R.Word.shl.put]

theorem put_round0 (H : HasShl bk) (c : Bool) :
    Evals bk (callT "Word.shl.put" [Bytes.nat 0, bitT c, wordT []]) (wordT []) := by
  obtain ⟨_, hp, hpv⟩ := H.put
  apply stepUntil_sound (stop := fun _ => false) (n := 50)
  cases c <;> word_simp [hp, hpv, R.Word.shl.put, wordT, Bytes.nat]

theorem put_evals (H : HasShl bk) : ∀ (c : Bool) (bs : List Bool),
    Evals bk (callT "Word.shl.put" [Bytes.nat bs.length, bitT c, wordT bs]) (wordT (putBits c bs))
  | c, [] => put_round0 H c
  | c, b :: bs => evals_trans (put_round H bs.length bs c b) (evals_rest (put_evals H b bs))

theorem shl_round (H : HasShl bk) (j : Nat) (t : List Bool) (b : Bool) :
    Evals bk (callT "Word.shl" [succT (Bytes.nat j), cellT (bitT b) (wordT t)])
      (cellT (bitT false) (callT "Word.shl.put" [Bytes.nat j, bitT b, wordT t])) := by
  obtain ⟨_, hs, hsv⟩ := H.shl
  apply stepUntil_sound (stop := cellEnd "Word.shl.put") (n := 100)
  cases b <;> word_simp [hs, hsv, R.Word.shl]

theorem shl_round0 (H : HasShl bk) :
    Evals bk (callT "Word.shl" [Bytes.nat 0, wordT []]) (wordT []) := by
  obtain ⟨_, hs, hsv⟩ := H.shl
  apply stepUntil_sound (stop := fun _ => false) (n := 50)
  word_simp [hs, hsv, R.Word.shl, wordT, Bytes.nat]

theorem shl_evals (H : HasShl bk) : ∀ bs : List Bool,
    Evals bk (callT "Word.shl" [Bytes.nat bs.length, wordT bs]) (wordT (shlBits bs))
  | [] => shl_round0 H
  | b :: bs => evals_trans (shl_round H bs.length bs b) (evals_rest (put_evals H b bs))

-- Shr
-- ===

structure HasShr (bk : Book) : Prop where
  shr : HasRef bk "Word.shr" R.Word.shr
  pad : HasRef bk "Word.shr.pad" R.Word.shr.pad

def hasShr (bk : Book) : Bool :=
  hasRef bk "Word.shr" R.Word.shr && hasRef bk "Word.shr.pad" R.Word.shr.pad

theorem hasShr_sound (h : hasShr bk = true) : HasShr bk := by
  simp only [hasShr, Bool.and_eq_true] at h
  exact ⟨hasRef_sound h.1, hasRef_sound h.2⟩

theorem pad_round (H : HasShr bk) (j : Nat) (t : List Bool) (b : Bool) :
    Evals bk (callT "Word.shr.pad" [succT (Bytes.nat j), cellT (bitT b) (wordT t)])
      (cellT (bitT b) (callT "Word.shr.pad" [Bytes.nat j, wordT t])) := by
  obtain ⟨_, hp, hpv⟩ := H.pad
  apply stepUntil_sound (stop := cellEnd "Word.shr.pad") (n := 100)
  cases b <;> word_simp [hp, hpv, R.Word.shr.pad]

theorem pad_round0 (H : HasShr bk) :
    Evals bk (callT "Word.shr.pad" [Bytes.nat 0, wordT []]) (wordT [false]) := by
  obtain ⟨_, hp, hpv⟩ := H.pad
  apply stepUntil_sound (stop := fun _ => false) (n := 50)
  word_simp [hp, hpv, R.Word.shr.pad, wordT, Bytes.nat]

theorem pad_evals (H : HasShr bk) : ∀ bs : List Bool,
    Evals bk (callT "Word.shr.pad" [Bytes.nat bs.length, wordT bs]) (wordT (padBits bs))
  | [] => pad_round0 H
  | b :: bs => evals_trans (pad_round H bs.length bs b) (evals_rest (pad_evals H bs))

theorem shr_round (H : HasShr bk) (j : Nat) (t : List Bool) (b : Bool) :
    Evals bk (callT "Word.shr" [succT (Bytes.nat j), cellT (bitT b) (wordT t)])
      (callT "Word.shr.pad" [Bytes.nat j, wordT t]) := by
  obtain ⟨_, hs, hsv⟩ := H.shr
  apply stepUntil_sound (stop := headIs "Word.shr.pad") (n := 100)
  cases b <;> word_simp [hs, hsv, R.Word.shr]

theorem shr_round0 (H : HasShr bk) :
    Evals bk (callT "Word.shr" [Bytes.nat 0, wordT []]) (wordT []) := by
  obtain ⟨_, hs, hsv⟩ := H.shr
  apply stepUntil_sound (stop := fun _ => false) (n := 50)
  word_simp [hs, hsv, R.Word.shr, wordT, Bytes.nat]

theorem shr_evals (H : HasShr bk) : ∀ bs : List Bool,
    Evals bk (callT "Word.shr" [Bytes.nat bs.length, wordT bs]) (wordT (shrBits bs))
  | [] => shr_round0 H
  | b :: bs => evals_trans (shr_round H bs.length bs b) (pad_evals H bs)

end Interp.Word
