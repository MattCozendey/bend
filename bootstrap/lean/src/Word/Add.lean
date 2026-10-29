import Word.Shared

-- Word.Add
-- ========
--
-- Base's add code: Word.adc. Bend puts Word.adc and Word.adc.con in one
-- def, Word.adc.group, and a tag argument picks the member. A call of
-- Word.add or Word.sub steps to a groupCall, which jumps.

open Quan Term Contract

namespace Interp.Word

-- groupCall n a b f c: the call of Word.adc on n, a, b, f and the carry c
def groupCall (n a b f c : Term) : Term :=
  App Q1 (App Q1 (App Q1 (App Q1 (App Q1 (App Q1 (Ref "Word.adc.group") n) a) b) f)
    (labT "Word.adc")) c

-- fullAdd a b c: Bool.full_add, the sum bit and the carry of a + b + c
def fullAdd (a b c : Bool) : Bool × Bool :=
  if a then (!(b ^^ c), b || c) else (b ^^ c, b && c)

-- adcBits f as bs c: the bits of Word.adc. f true flips each bit of bs.
-- Word.sub gives f = c = true, so the result is as - bs.
def adcBits (f : Bool) : List Bool → List Bool → Bool → List Bool
  | a :: as, b :: bs, c =>
    let sk := fullAdd a (if f then !b else b) c
    sk.1 :: adcBits f as bs sk.2
  | _, _, _ => []

theorem adcBits_length : ∀ (as bs : List Bool) (f c : Bool), as.length = bs.length →
    (adcBits f as bs c).length = as.length
  | [], [], _, _, _ => rfl
  | _ :: as, _ :: bs, f, _, h => by
    simp only [adcBits, List.length_cons]
    rw [adcBits_length as bs f _ (by simpa using h)]
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => by simp at h

def groupCode : List (String × Term) :=
  [("Word.adc.group", R.Word.adc.group), ("Bool.full_add", R.Bool.full_add),
    ("Bool.xor", R.Bool.xor), ("Bool.and", R.Bool.and), ("Bool.or", R.Bool.or),
    ("Bool.not", R.Bool.not)]

theorem group_round (H : HasRefs bk groupCode) (j : Nat) (as bs : List Bool) (f a b c : Bool) :
    Evals bk (groupCall (boxT "Succ" (Bytes.nat j)) (cellT (bitT a) (wordT as))
        (cellT (bitT b) (wordT bs)) (bitT f) (bitT c))
      (cellT (bitT (fullAdd a (if f then !b else b) c).1)
        (groupCall (Bytes.nat j) (wordT as) (wordT bs) (bitT f)
          (bitT (fullAdd a (if f then !b else b) c).2))) := by
  obtain ⟨⟨_, hg, hgv⟩, ⟨_, hf, hfv⟩, ⟨_, hx, hxv⟩, ⟨_, ha, hav⟩, ⟨_, ho, hov⟩, ⟨_, ht, htv⟩,
    -⟩ := H
  apply stepUntil_sound (stop := cellEnd "Word.adc.group") (n := 200)
  cases f <;> cases a <;> cases b <;> cases c <;>
    word_simp [hg, hgv, hf, hfv, hx, hxv, ha, hav, ho, hov, ht, htv, R.Word.adc.group,
      R.Bool.full_add, R.Bool.xor, R.Bool.and, R.Bool.or, R.Bool.not, groupCall, fullAdd]

theorem group_round0 (H : HasRefs bk groupCode) (f c : Bool) :
    Evals bk (groupCall (Bytes.nat 0) (wordT []) (wordT []) (bitT f) (bitT c)) (wordT []) := by
  obtain ⟨⟨_, hg, hgv⟩, -⟩ := H
  apply stepUntil_sound (stop := fun _ => false) (n := 50)
  cases f <;> cases c <;> word_simp [hg, hgv, R.Word.adc.group, groupCall, wordT, Bytes.nat]

theorem group_evals (H : HasRefs bk groupCode) : ∀ (as bs : List Bool) (f c : Bool),
    as.length = bs.length →
    Evals bk (groupCall (Bytes.nat as.length) (wordT as) (wordT bs) (bitT f) (bitT c))
      (wordT (adcBits f as bs c))
  | [], [], f, c, _ => group_round0 H f c
  | a :: as, b :: bs, f, c, h =>
    evals_trans (group_round H as.length as bs f a b c)
      (evals_rest (group_evals H as bs f _ (by simpa using h)))
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => by simp at h

theorem add_group (ha : HasRef bk "Word.add" R.Word.add) (k : Nat) (as bs : List Bool) :
    Evals bk (callT "Word.add" [Bytes.nat k, wordT as, wordT bs])
      (groupCall (Bytes.nat k) (wordT as) (wordT bs) (bitT false) (bitT false)) := by
  obtain ⟨_, h, hv⟩ := ha
  apply stepUntil_sound (stop := headIs "Word.adc.group") (n := 10)
  word_simp [h, hv, R.Word.add, groupCall]

theorem add_evals (H : HasRefs bk groupCode) (ha : HasRef bk "Word.add" R.Word.add)
    (as bs : List Bool) (len : as.length = bs.length) :
    Evals bk (callT "Word.add" [Bytes.nat as.length, wordT as, wordT bs])
      (wordT (adcBits false as bs false)) :=
  evals_trans (add_group ha _ as bs) (group_evals H as bs false false len)

end Interp.Word
