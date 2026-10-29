import Bootstrap.Word

-- WordAdd
-- =======
--
-- Base's add code: Word.adc.group, the code of Word.add and Word.sub. A
-- call on two words of n bits reaches the word that adcBits gives, for each
-- n (group_evals). A call of Word.add reaches the same (add_evals).

open Quan Term Spec

namespace Interp

def groupCall (n a b f c : Term) : Term :=
  App Q1 (App Q1 (App Q1 (App Q1 (App Q1 (App Q1 (Ref "Word.adc.group") n) a) b) f)
    (Tup Q1 (Lab "Word.adc") (Lab "()"))) c

-- the bits that Word.adc computes. f true subtracts: it flips each bit of
-- the second word.
def fullAdd (a b c : Bool) : Bool × Bool :=
  if a then (!(b ^^ c), b || c) else (b ^^ c, b && c)

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

-- AddRefs bk: the book has base's add code
structure AddRefs (bk : Book) : Prop where
  group : HasRef bk "Word.adc.group" R.Word.adc.group
  fullAdd : HasRef bk "Bool.full_add" R.Bool.full_add
  xor : HasRef bk "Bool.xor" R.Bool.xor
  and : HasRef bk "Bool.and" R.Bool.and
  or : HasRef bk "Bool.or" R.Bool.or
  not : HasRef bk "Bool.not" R.Bool.not

def addOk (bk : Book) : Bool :=
  hasRef bk "Word.adc.group" R.Word.adc.group && hasRef bk "Bool.full_add" R.Bool.full_add &&
  hasRef bk "Bool.xor" R.Bool.xor && hasRef bk "Bool.and" R.Bool.and &&
  hasRef bk "Bool.or" R.Bool.or && hasRef bk "Bool.not" R.Bool.not

theorem addOk_ok (h : addOk bk = true) : AddRefs bk := by
  simp only [addOk, Bool.and_eq_true] at h
  exact ⟨hasRef_ok h.1.1.1.1.1, hasRef_ok h.1.1.1.1.2, hasRef_ok h.1.1.1.2, hasRef_ok h.1.1.2,
    hasRef_ok h.1.2, hasRef_ok h.2⟩

-- one round: a call on two word cells gives a cell of the result, with the
-- call on the rests as its rest
theorem add_round (H : AddRefs bk) (j : Nat) (as bs : List Bool) (f a b c : Bool) :
    Evals bk (groupCall (succT (Bytes.nat j)) (cellT (bitT a) (wordT as))
        (cellT (bitT b) (wordT bs)) (bitT f) (bitT c))
      (cellT (bitT (fullAdd a (if f then !b else b) c).1)
        (groupCall (Bytes.nat j) (wordT as) (wordT bs) (bitT f)
          (bitT (fullAdd a (if f then !b else b) c).2))) := by
  obtain ⟨_, hg, hgv⟩ := H.group
  obtain ⟨_, hf, hfv⟩ := H.fullAdd
  obtain ⟨_, hx, hxv⟩ := H.xor
  obtain ⟨_, ha, hav⟩ := H.and
  obtain ⟨_, ho, hov⟩ := H.or
  obtain ⟨_, ht, htv⟩ := H.not
  apply stepUntil_sound (stop := cellEnd "Word.adc.group") (n := 200)
  cases f <;> cases a <;> cases b <;> cases c <;>
    word_simp [hg, hgv, hf, hfv, hx, hxv, ha, hav, ho, hov, ht, htv, R.Word.adc.group,
      R.Bool.full_add, R.Bool.xor, R.Bool.and, R.Bool.or, R.Bool.not, groupCall, fullAdd]

-- the last round: a call on two empty words gives the empty word
theorem add_round0 (H : AddRefs bk) (f c : Bool) :
    Evals bk (groupCall (Bytes.nat 0) (wordT []) (wordT []) (bitT f) (bitT c)) (wordT []) := by
  obtain ⟨_, hg, hgv⟩ := H.group
  apply stepUntil_sound (stop := fun _ => false) (n := 50)
  cases f <;> cases c <;> word_simp [hg, hgv, R.Word.adc.group, groupCall, wordT, Bytes.nat]

theorem group_evals (H : AddRefs bk) : ∀ (as bs : List Bool) (f c : Bool),
    as.length = bs.length →
    Evals bk (groupCall (Bytes.nat as.length) (wordT as) (wordT bs) (bitT f) (bitT c))
      (wordT (adcBits f as bs c))
  | [], [], f, c, _ => add_round0 H f c
  | a :: as, b :: bs, f, c, h =>
    evals_trans (add_round H as.length as bs f a b c)
      (evals_rest (group_evals H as bs f _ (by simpa using h)))
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => by simp at h

-- a call of Word.add goes to the call of the group
theorem add_group (ha : HasRef bk "Word.add" R.Word.add) (k : Nat) (as bs : List Bool) :
    Evals bk (callT "Word.add" [Bytes.nat k, wordT as, wordT bs])
      (groupCall (Bytes.nat k) (wordT as) (wordT bs) (bitT false) (bitT false)) := by
  obtain ⟨_, h, hv⟩ := ha
  apply stepUntil_sound (stop := headIs "Word.adc.group") (n := 10)
  word_simp [h, hv, R.Word.add, groupCall]

theorem add_evals (H : AddRefs bk) (ha : HasRef bk "Word.add" R.Word.add)
    (as bs : List Bool) (len : as.length = bs.length) :
    Evals bk (callT "Word.add" [Bytes.nat as.length, wordT as, wordT bs])
      (wordT (adcBits false as bs false)) :=
  evals_trans (add_group ha _ as bs) (group_evals H as bs false false len)

end Interp
