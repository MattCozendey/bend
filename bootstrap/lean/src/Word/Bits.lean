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

def notCode : List (String × Term) := [("Word.not", R.Word.not), ("Bool.not", R.Bool.not)]

theorem not_round (H : HasRefs bk notCode) (j : Nat) (t : List Bool) (b : Bool) :
    Evals bk (callT "Word.not" [boxT "Succ" (Bytes.nat j), cellT (bitT b) (wordT t)])
      (cellT (bitT !b) (callT "Word.not" [Bytes.nat j, wordT t])) := by
  obtain ⟨⟨_, hw, hwv⟩, ⟨_, hb, hbv⟩, -⟩ := H
  apply stepUntil_sound (stop := cellEnd "Word.not") (n := 100)
  cases b <;> word_simp [hw, hwv, hb, hbv, R.Word.not, R.Bool.not]

theorem not_round0 (H : HasRefs bk notCode) :
    Evals bk (callT "Word.not" [Bytes.nat 0, wordT []]) (wordT []) := by
  obtain ⟨⟨_, hw, hwv⟩, -⟩ := H
  apply stepUntil_sound (stop := fun _ => false) (n := 50)
  word_simp [hw, hwv, R.Word.not, wordT, Bytes.nat]

theorem not_evals (H : HasRefs bk notCode) : ∀ bs : List Bool,
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

def BitOp.op : BitOp → Bool → Bool → Bool
  | .and => (· && ·) | .or => (· || ·) | .xor => (· ^^ ·)

-- Bool.xor calls Bool.not; Bool.and and Bool.or call nothing
def BitOp.code : BitOp → List (String × Term)
  | .and => [("Word.and", R.Word.and), ("Bool.and", R.Bool.and)]
  | .or => [("Word.or", R.Word.or), ("Bool.or", R.Bool.or)]
  | .xor => [("Word.xor", R.Word.xor), ("Bool.xor", R.Bool.xor), ("Bool.not", R.Bool.not)]

theorem bit_round {o : BitOp} (H : HasRefs bk o.code) (j : Nat) (as bs : List Bool)
    (a b : Bool) :
    Evals bk (callT o.word [boxT "Succ" (Bytes.nat j), cellT (bitT a) (wordT as),
        cellT (bitT b) (wordT bs)])
      (cellT (bitT (o.op a b)) (callT o.word [Bytes.nat j, wordT as, wordT bs])) := by
  apply stepUntil_sound (stop := cellEnd o.word) (n := 100)
  cases o <;> obtain ⟨⟨_, hw, hwv⟩, ⟨_, hb, hbv⟩, H⟩ := H <;> simp only [BitOp.word, BitOp.op]
  · cases a <;> cases b <;> word_simp [hw, hwv, hb, hbv, R.Word.and, R.Bool.and]
  · cases a <;> cases b <;> word_simp [hw, hwv, hb, hbv, R.Word.or, R.Bool.or]
  · obtain ⟨⟨_, hn, hnv⟩, -⟩ := H
    cases a <;> cases b <;> word_simp [hw, hwv, hb, hbv, hn, hnv, R.Word.xor, R.Bool.xor,
      R.Bool.not]

theorem bit_round0 {o : BitOp} (H : HasRefs bk o.code) :
    Evals bk (callT o.word [Bytes.nat 0, wordT [], wordT []]) (wordT []) := by
  apply stepUntil_sound (stop := fun _ => false) (n := 50)
  cases o <;> obtain ⟨⟨_, hw, hwv⟩, -⟩ := H <;> simp only [BitOp.word]
  · word_simp [hw, hwv, R.Word.and, wordT, Bytes.nat]
  · word_simp [hw, hwv, R.Word.or, wordT, Bytes.nat]
  · word_simp [hw, hwv, R.Word.xor, wordT, Bytes.nat]

theorem bit_evals {o : BitOp} (H : HasRefs bk o.code) :
    ∀ (as bs : List Bool), as.length = bs.length →
    Evals bk (callT o.word [Bytes.nat as.length, wordT as, wordT bs])
      (wordT (List.zipWith o.op as bs))
  | [], [], _ => bit_round0 H
  | a :: as, b :: bs, h =>
    evals_trans (bit_round H as.length as bs a b)
      (evals_rest (bit_evals H as bs (by simpa using h)))
  | [], _ :: _, h | _ :: _, [], h => by simp at h

end Interp.Word
