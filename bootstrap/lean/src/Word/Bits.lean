import Word.Shared

-- Word.Bits
-- =========
--
-- Base's bitwise code: Word.not, Word.and, Word.or and Word.xor. Each
-- applies its Bool def to each bit.

open Quan Term Contract

namespace Interp.Word

-- Not
-- ===

structure HasNot (bk : Book) : Prop where
  word : HasRef bk "Word.not" R.Word.not
  bool : HasRef bk "Bool.not" R.Bool.not

def hasNot (bk : Book) : Bool :=
  hasRef bk "Word.not" R.Word.not && hasRef bk "Bool.not" R.Bool.not

theorem hasNot_sound (h : hasNot bk = true) : HasNot bk := by
  simp only [hasNot, Bool.and_eq_true] at h
  exact ⟨hasRef_sound h.1, hasRef_sound h.2⟩

theorem not_round (H : HasNot bk) (j : Nat) (t : List Bool) (b : Bool) :
    Evals bk (callT "Word.not" [succT (Bytes.nat j), cellT (bitT b) (wordT t)])
      (cellT (bitT !b) (callT "Word.not" [Bytes.nat j, wordT t])) := by
  obtain ⟨_, hw, hwv⟩ := H.word
  obtain ⟨_, hb, hbv⟩ := H.bool
  apply stepUntil_sound (stop := cellEnd "Word.not") (n := 100)
  cases b <;> word_simp [hw, hwv, hb, hbv, R.Word.not, R.Bool.not]

theorem not_round0 (H : HasNot bk) :
    Evals bk (callT "Word.not" [Bytes.nat 0, wordT []]) (wordT []) := by
  obtain ⟨_, hw, hwv⟩ := H.word
  apply stepUntil_sound (stop := fun _ => false) (n := 50)
  word_simp [hw, hwv, R.Word.not, wordT, Bytes.nat]

theorem not_evals (H : HasNot bk) : ∀ bs : List Bool,
    Evals bk (callT "Word.not" [Bytes.nat bs.length, wordT bs]) (wordT (bs.map (!·)))
  | [] => not_round0 H
  | b :: bs => evals_trans (not_round H bs.length bs b) (evals_rest (not_evals H bs))

-- And, or, xor
-- ============

inductive BitOp where
  | and | or | xor
  deriving DecidableEq

def BitOp.word : BitOp → String
  | .and => "Word.and" | .or => "Word.or" | .xor => "Word.xor"

def BitOp.bool : BitOp → String
  | .and => "Bool.and" | .or => "Bool.or" | .xor => "Bool.xor"

def BitOp.wordRef : BitOp → Term
  | .and => R.Word.and | .or => R.Word.or | .xor => R.Word.xor

def BitOp.boolRef : BitOp → Term
  | .and => R.Bool.and | .or => R.Bool.or | .xor => R.Bool.xor

def BitOp.op : BitOp → Bool → Bool → Bool
  | .and => (· && ·) | .or => (· || ·) | .xor => (· ^^ ·)

-- Bool.xor calls Bool.not; Bool.and and Bool.or call nothing
structure HasBit (bk : Book) (o : BitOp) : Prop where
  word : HasRef bk o.word o.wordRef
  bool : HasRef bk o.bool o.boolRef
  not : o = .xor → HasRef bk "Bool.not" R.Bool.not

def hasBit (bk : Book) (o : BitOp) : Bool :=
  hasRef bk o.word o.wordRef && hasRef bk o.bool o.boolRef &&
  (o != .xor || hasRef bk "Bool.not" R.Bool.not)

theorem hasBit_sound (h : hasBit bk o = true) : HasBit bk o := by
  simp only [hasBit, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  exact ⟨hasRef_sound h.1.1, hasRef_sound h.1.2, fun e => by simp_all [hasRef_sound]⟩

theorem bit_round (H : HasBit bk o) (j : Nat) (as bs : List Bool) (a b : Bool) :
    Evals bk (callT o.word [succT (Bytes.nat j), cellT (bitT a) (wordT as),
        cellT (bitT b) (wordT bs)])
      (cellT (bitT (o.op a b)) (callT o.word [Bytes.nat j, wordT as, wordT bs])) := by
  apply stepUntil_sound (stop := cellEnd o.word) (n := 100)
  cases o <;> obtain ⟨_, hw, hwv⟩ := H.word <;> obtain ⟨_, hb, hbv⟩ := H.bool <;>
    simp only [BitOp.word, BitOp.bool, BitOp.wordRef, BitOp.boolRef, BitOp.op] at hw hwv hb hbv ⊢
  · cases a <;> cases b <;> word_simp [hw, hwv, hb, hbv, R.Word.and, R.Bool.and]
  · cases a <;> cases b <;> word_simp [hw, hwv, hb, hbv, R.Word.or, R.Bool.or]
  · obtain ⟨_, hn, hnv⟩ := H.not rfl
    cases a <;> cases b <;> word_simp [hw, hwv, hb, hbv, hn, hnv, R.Word.xor, R.Bool.xor,
      R.Bool.not]

theorem bit_round0 (H : HasBit bk o) :
    Evals bk (callT o.word [Bytes.nat 0, wordT [], wordT []]) (wordT []) := by
  apply stepUntil_sound (stop := fun _ => false) (n := 50)
  cases o <;> obtain ⟨_, hw, hwv⟩ := H.word <;>
    simp only [BitOp.word, BitOp.wordRef] at hw hwv ⊢
  · word_simp [hw, hwv, R.Word.and, wordT, Bytes.nat]
  · word_simp [hw, hwv, R.Word.or, wordT, Bytes.nat]
  · word_simp [hw, hwv, R.Word.xor, wordT, Bytes.nat]

theorem bit_evals (H : HasBit bk o) : ∀ (as bs : List Bool), as.length = bs.length →
    Evals bk (callT o.word [Bytes.nat as.length, wordT as, wordT bs])
      (wordT (List.zipWith o.op as bs))
  | [], [], _ => bit_round0 H
  | a :: as, b :: bs, h =>
    evals_trans (bit_round H as.length as bs a b)
      (evals_rest (bit_evals H as bs (by simpa using h)))
  | [], _ :: _, h | _ :: _, [], h => by simp at h

end Interp.Word
