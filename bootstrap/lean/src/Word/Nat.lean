import Word.Shared

-- Word.Nat
-- ========
--
-- Base's inc code (Word.inc), its code from a word to a Nat (Word.to_nat,
-- with Nat.double), and from a Nat to a one-word type (T.from_nat).

open Quan Term Contract

namespace Interp.Word

-- Inc
-- ===

def incBits : List Bool → List Bool
  | [] => []
  | false :: bs => true :: bs
  | true :: bs => false :: incBits bs

def hasInc (bk : Book) : Bool := hasRef bk "Word.inc" R.Word.inc

theorem inc_round0 (H : HasRef bk "Word.inc" R.Word.inc) :
    Evals bk (callT "Word.inc" [Bytes.nat 0, wordT []]) (wordT []) := by
  obtain ⟨_, hi, hiv⟩ := H
  apply stepUntil_sound (stop := fun _ => false) (n := 50)
  word_simp [hi, hiv, R.Word.inc, wordT, Bytes.nat]

theorem inc_round_f (H : HasRef bk "Word.inc" R.Word.inc) (j : Nat) (t : List Bool) :
    Evals bk (callT "Word.inc" [succT (Bytes.nat j), cellT (bitT false) (wordT t)])
      (cellT (bitT true) (wordT t)) := by
  obtain ⟨_, hi, hiv⟩ := H
  apply stepUntil_sound (stop := fun _ => false) (n := 100)
  word_simp [hi, hiv, R.Word.inc]

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

structure HasToNat (bk : Book) : Prop where
  word : HasRef bk "Word.to_nat" R.Word.to_nat
  double : HasRef bk "Nat.double" R.Nat.double

def hasToNat (bk : Book) : Bool :=
  hasRef bk "Word.to_nat" R.Word.to_nat && hasRef bk "Nat.double" R.Nat.double

theorem hasToNat_sound (h : hasToNat bk = true) : HasToNat bk := by
  simp only [hasToNat, Bool.and_eq_true] at h
  exact ⟨hasRef_sound h.1, hasRef_sound h.2⟩

-- a Succ whose pred is a call of def k
def succEnd (k : String) : Term → Bool
  | Tup _ (Lab "Succ") (Tup _ x (Lab "()")) => headIs k x
  | _ => false

-- a Succ of a Succ whose pred is a call of def k
def succ2End (k : String) : Term → Bool
  | Tup _ (Lab "Succ") (Tup _ x (Lab "()")) => succEnd k x
  | _ => false

theorem double_isValue (H : HasToNat bk) : isValue bk (Ref "Nat.double") = true := by
  obtain ⟨_, hd, hdv⟩ := H.double
  word_simp [hd, hdv, R.Nat.double]

theorem double_round (H : HasToNat bk) (v : Nat) :
    Evals bk (callT "Nat.double" [succT (Bytes.nat v)])
      (succT (succT (callT "Nat.double" [Bytes.nat v]))) := by
  obtain ⟨_, hd, hdv⟩ := H.double
  apply stepUntil_sound (stop := succ2End "Nat.double") (n := 50)
  word_simp [succ2End, succEnd, hd, hdv, R.Nat.double]

theorem double_round0 (H : HasToNat bk) :
    Evals bk (callT "Nat.double" [Bytes.nat 0]) (Bytes.nat 0) := by
  obtain ⟨_, hd, hdv⟩ := H.double
  apply stepUntil_sound (stop := fun _ => false) (n := 50)
  word_simp [hd, hdv, R.Nat.double, Bytes.nat]

theorem double_evals (H : HasToNat bk) : ∀ v : Nat,
    Evals bk (callT "Nat.double" [Bytes.nat v]) (Bytes.nat (2 * v))
  | 0 => double_round0 H
  | v + 1 => by
    have e : Bytes.nat (2 * (v + 1)) = succT (succT (Bytes.nat (2 * v))) := by
      rw [show 2 * (v + 1) = 2 * v + 1 + 1 by omega]; rfl
    rw [e]
    exact evals_trans (double_round H v) (evals_box "Succ" (evals_box "Succ" (double_evals H v)))

theorem toNat_round0 (H : HasToNat bk) :
    Evals bk (callT "Word.to_nat" [Bytes.nat 0, wordT []]) (Bytes.nat 0) := by
  obtain ⟨_, hw, hwv⟩ := H.word
  apply stepUntil_sound (stop := fun _ => false) (n := 50)
  word_simp [hw, hwv, R.Word.to_nat, wordT, Bytes.nat]

theorem toNat_round_f (H : HasToNat bk) (j : Nat) (t : List Bool) :
    Evals bk (callT "Word.to_nat" [succT (Bytes.nat j), cellT (bitT false) (wordT t)])
      (callT "Nat.double" [callT "Word.to_nat" [Bytes.nat j, wordT t]]) := by
  obtain ⟨_, hw, hwv⟩ := H.word
  apply stepUntil_sound (stop := headIs "Nat.double") (n := 100)
  word_simp [hw, hwv, R.Word.to_nat]

theorem toNat_round_t (H : HasToNat bk) (j : Nat) (t : List Bool) :
    Evals bk (callT "Word.to_nat" [succT (Bytes.nat j), cellT (bitT true) (wordT t)])
      (succT (callT "Nat.double" [callT "Word.to_nat" [Bytes.nat j, wordT t]])) := by
  obtain ⟨_, hw, hwv⟩ := H.word
  apply stepUntil_sound (stop := succEnd "Nat.double") (n := 100)
  word_simp [succEnd, hw, hwv, R.Word.to_nat]

theorem toNat_evals (H : HasToNat bk) : ∀ bs : List Bool,
    Evals bk (callT "Word.to_nat" [Bytes.nat bs.length, wordT bs]) (Bytes.nat (toNatBits bs))
  | [] => toNat_round0 H
  | false :: bs =>
    evals_trans (toNat_round_f H bs.length bs)
      (evals_trans (evals_arg (double_isValue H) rfl (toNat_evals H bs)) (double_evals H _))
  | true :: bs =>
    evals_trans (toNat_round_t H bs.length bs)
      (evals_box "Succ" (evals_trans (evals_arg (double_isValue H) rfl (toNat_evals H bs))
        (double_evals H _)))

-- From Nat
-- ========
--
-- Base's from_nat for a one-word type T of width w (for U32, T = "U32" and
-- w = 32). T.lit0 is T{0}. T.inc applies Word.inc to T's word. T.from_nat n
-- applies T.inc n times to T.lit0. The refs are templates in T and w, so
-- these proofs hold for each such type.

def lit0Ref (T : String) (w : Nat) : Term := boxT T (wordT (List.replicate w false))

def incRef (T : String) (w : Nat) : Term :=
  Prj (Mat T (Prj (Lam Q1 (Mat "()" (boxT T (callT "Word.inc" [Bytes.nat w, Var 0])) Efq))) Efq)

def fromNatRef (T : String) : Term :=
  Prj (Mat "Zero" (Mat "()" (Ref (T ++ ".lit0")) Efq)
    (Mat "Succ" (Prj (Lam Q1 (Mat "()"
      (callT (T ++ ".inc") [callT (T ++ ".from_nat") [Var 0]]) Efq))) Efq))

theorem incBits_length : ∀ bs : List Bool, (incBits bs).length = bs.length
  | [] => rfl
  | false :: _ => rfl
  | true :: bs => by simp [incBits, incBits_length bs]

def incN : Nat → List Bool → List Bool
  | 0, bs => bs
  | n + 1, bs => incN n (incBits bs)

theorem incN_succ : incN (n + 1) bs = incBits (incN n bs) := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih => exact ih (bs := incBits bs)

theorem incN_length : (incN n bs).length = bs.length := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih => simp only [incN, ih, incBits_length]

-- fromNatBits w n: the word of T.from_nat n at width w, that is n mod 2^w
def fromNatBits (w n : Nat) : List Bool := incN n (List.replicate w false)

structure HasFromNat (bk : Book) (T : String) (w : Nat) : Prop where
  fromNat : HasRef bk (T ++ ".from_nat") (fromNatRef T)
  inc : HasRef bk (T ++ ".inc") (incRef T w)
  lit0 : HasRef bk (T ++ ".lit0") (lit0Ref T w)
  word : HasRef bk "Word.inc" R.Word.inc

def hasFromNat (bk : Book) (T : String) (w : Nat) : Bool :=
  hasRef bk (T ++ ".from_nat") (fromNatRef T) && hasRef bk (T ++ ".inc") (incRef T w) &&
  hasRef bk (T ++ ".lit0") (lit0Ref T w) && hasInc bk

-- fromNatTypes bk: each (T, w) for which hasFromNat holds, where T.from_nat
-- is a def of bk and w is the width of T.lit0's word
def fromNatTypes (bk : Book) : List (String × Nat) :=
  let found := bk.defs.filterMap fun d => do
    let T := (← d.k.dropSuffix? ".from_nat").toString
    let l ← bk.get (T ++ ".lit0")
    match l.v with
    | Tup Q1 (Lab _) (Tup Q1 x (Lab "()")) => (decWord x).map fun bs => (T, bs.length)
    | _ => none
  found.filter fun (T, w) => hasFromNat bk T w

theorem fromNatTypes_sound (h : (T, w) ∈ fromNatTypes bk) : HasFromNat bk T w := by
  have ok := (List.mem_filter.1 h).2
  simp only [hasFromNat, Bool.and_eq_true] at ok
  exact ⟨hasRef_sound ok.1.1.1, hasRef_sound ok.1.1.2, hasRef_sound ok.1.2, hasRef_sound ok.2⟩

theorem sub_nat : ∀ n : Nat, Term.sub s (Bytes.nat n) = Bytes.nat n
  | 0 => rfl
  | n + 1 => by simp [Bytes.nat, Term.sub, sub_nat n]

theorem sub_word : ∀ bs : List Bool, Term.sub s (wordT bs) = wordT bs
  | [] => rfl
  | b :: bs => by cases b <;> simp [wordT, cellT, bitT, Term.sub, sub_word bs]

theorem fromNat_round0 (H : HasFromNat bk T w) :
    Evals bk (callT (T ++ ".from_nat") [Bytes.nat 0]) (lit0Ref T w) := by
  obtain ⟨_, hf, hfv⟩ := H.fromNat
  obtain ⟨_, hl, hlv⟩ := H.lit0
  apply stepUntil_sound (stop := fun _ => false) (n := 50)
  word_simp [hf, hfv, hl, hlv, fromNatRef, lit0Ref, Bytes.nat, sub_word]

-- an App whose argument is an App
def callEnd : Term → Bool
  | App _ _ (App _ _ _) => true
  | _ => false

theorem fromNat_round (H : HasFromNat bk T w) (n : Nat) :
    Evals bk (callT (T ++ ".from_nat") [succT (Bytes.nat n)])
      (callT (T ++ ".inc") [callT (T ++ ".from_nat") [Bytes.nat n]]) := by
  obtain ⟨_, hf, hfv⟩ := H.fromNat
  apply stepUntil_sound (stop := callEnd) (n := 10)
  word_simp [callEnd, hf, hfv, fromNatRef]

theorem boxInc_isValue (H : HasFromNat bk T w) : isValue bk (Ref (T ++ ".inc")) = true := by
  obtain ⟨_, hi, hiv⟩ := H.inc
  word_simp [hi, hiv, incRef]

-- a boxT whose field is a call of Word.inc
def boxEnd : Term → Bool
  | Tup _ (Lab _) (Tup _ x (Lab "()")) => headIs "Word.inc" x
  | _ => false

theorem boxInc_round (H : HasFromNat bk T w) (bs : List Bool) :
    Evals bk (callT (T ++ ".inc") [boxT T (wordT bs)])
      (boxT T (callT "Word.inc" [Bytes.nat w, wordT bs])) := by
  obtain ⟨_, hi, hiv⟩ := H.inc
  apply stepUntil_sound (stop := boxEnd) (n := 20)
  word_simp [boxEnd, hi, hiv, incRef, sub_nat]

theorem boxInc_evals (H : HasFromNat bk T w) (bs : List Bool) (len : bs.length = w) :
    Evals bk (callT (T ++ ".inc") [boxT T (wordT bs)]) (boxT T (wordT (incBits bs))) := by
  have e := inc_evals H.word bs
  rw [len] at e
  exact evals_trans (boxInc_round H bs) (evals_box T e)

theorem fromNat_evals (H : HasFromNat bk T w) : ∀ n : Nat,
    Evals bk (callT (T ++ ".from_nat") [Bytes.nat n]) (boxT T (wordT (fromNatBits w n)))
  | 0 => fromNat_round0 H
  | n + 1 => by
    have l : (fromNatBits w n).length = w := by simp [fromNatBits, incN_length]
    rw [show fromNatBits w (n + 1) = incBits (fromNatBits w n) from incN_succ]
    exact evals_trans (fromNat_round H n)
      (evals_trans (evals_arg (boxInc_isValue H) rfl (fromNat_evals H n)) (boxInc_evals H _ l))

end Interp.Word
