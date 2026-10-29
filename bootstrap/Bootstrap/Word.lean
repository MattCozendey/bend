import Bootstrap.WordRef

-- Word
-- ====
--
-- The word jump. A call of base's Word.adc.group (the code of Word.add and
-- Word.sub) on values goes in one step to its result, which adcBits, a bit
-- recursion in Lean, computes. group_evals proves that Eval reaches the
-- same result, for each width. The jump runs only when the book's defs
-- equal the terms in WordRef.

open Quan Term Spec

namespace Interp

-- Terms
-- =====

-- a Bool, a word (lowest bit first) and a call of the group, as terms
def bitT (b : Bool) : Term := Tup Q1 (Lab (if b then "True" else "False")) (Lab "()")

def wordT : List Bool → Term
  | [] => Tup Q1 (Lab "WNil") (Lab "()")
  | b :: bs => Tup Q1 (Lab "WCon") (Tup Q1 (bitT b) (Tup Q1 (wordT bs) (Lab "()")))

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

-- Refs bk: the book has base's word add code, as WordRef gives it
structure Refs (bk : Book) : Prop where
  group : ∃ d, bk.get "Word.adc.group" = some d ∧ d.v = refGroup
  fullAdd : ∃ d, bk.get "Bool.full_add" = some d ∧ d.v = refFullAdd
  xor : ∃ d, bk.get "Bool.xor" = some d ∧ d.v = refXor
  and : ∃ d, bk.get "Bool.and" = some d ∧ d.v = refAnd
  or : ∃ d, bk.get "Bool.or" = some d ∧ d.v = refOr
  not : ∃ d, bk.get "Bool.not" = some d ∧ d.v = refNot

-- the body of def k is r
def hasRef (bk : Book) (k : String) (r : Term) : Bool := (bk.get k).map (·.v) == some r

theorem hasRef_ok (h : hasRef bk k r = true) : ∃ d, bk.get k = some d ∧ d.v = r := by
  simp only [hasRef, beq_iff_eq, Option.map_eq_some_iff] at h; exact h

def refsMatch (bk : Book) : Bool :=
  hasRef bk "Word.adc.group" refGroup && hasRef bk "Bool.full_add" refFullAdd &&
  hasRef bk "Bool.xor" refXor && hasRef bk "Bool.and" refAnd &&
  hasRef bk "Bool.or" refOr && hasRef bk "Bool.not" refNot

theorem refsMatch_ok (h : refsMatch bk = true) : Refs bk := by
  simp only [refsMatch, Bool.and_eq_true] at h
  exact ⟨hasRef_ok h.1.1.1.1.1, hasRef_ok h.1.1.1.1.2, hasRef_ok h.1.1.1.2, hasRef_ok h.1.1.2,
    hasRef_ok h.1.2, hasRef_ok h.2⟩

-- Values
-- ======

theorem value_step (v : isValue bk t = true) : step bk t = none := by
  cases h : step bk t with
  | none => rfl
  | some u => exact (eval_value (step_sound h) (isValue_iff.1 v)).elim

theorem bit_value : isValue bk (bitT b) = true ∧ isData (bitT b) = true := by
  cases b <;> simp [bitT, isValue, isData, Quan.live]

theorem word_value : isValue bk (wordT bs) = true ∧ isData (wordT bs) = true := by
  induction bs with
  | nil => simp [wordT, isValue, isData]
  | cons b bs ih =>
    have := bit_value (bk := bk) (b := b)
    simp_all [wordT, isValue, isData, Quan.live]

theorem nat_value : isValue bk (Bytes.nat n) = true ∧ isData (Bytes.nat n) = true := by
  induction n with
  | zero => simp [Bytes.nat, isValue, isData]
  | succ n ih => simp_all [Bytes.nat, isValue, isData, Quan.live]

-- Rounds
-- ======

-- stepUntil bk stop n t: the first term from t, in at most n steps, where
-- stop holds
def stepUntil (bk : Book) (stop : Term → Bool) : Nat → Term → Option Term
  | 0, _ => none
  | n + 1, t =>
    if stop t then some t else
    match step bk t with
    | some u => stepUntil bk stop n u
    | none => none

theorem stepUntil_sound : stepUntil bk stop n t = some u → Evals bk t u := by
  induction n generalizing t with
  | zero => simp [stepUntil]
  | succ n ih =>
    simp only [stepUntil]; split
    · simp only [Option.some.injEq]; rintro rfl; exact .refl
    · split
      · rename_i u' h; exact fun e => .step (step_sound h) (ih e)
      · simp

-- the end of a round: a word cell whose tail is the next group call
def roundEnd : Term → Bool
  | Tup _ (Lab "WCon") (Tup _ _ (Tup _ (App _ (App _ (App _ (App _ (App _ (App _
      (Ref "Word.adc.group") _) _) _) _) _) _) (Lab "()"))) => true
  | _ => false

-- the end of the last round: the empty word
def wnilEnd : Term → Bool
  | Tup _ (Lab "WNil") (Lab "()") => true
  | _ => false

-- one round: a call on two word cells gives a cell of the result, with the
-- call on the tails as its tail
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem round (R : Refs bk) (vn : isValue bk n = true) (dn : isData n = true)
    (va : isValue bk as = true) (da : isData as = true)
    (vb : isValue bk bs = true) (db : isData bs = true) (f a b c : Bool) :
    Evals bk (groupCall (Tup Q1 (Lab "Succ") (Tup Q1 n (Lab "()")))
        (Tup Q1 (Lab "WCon") (Tup Q1 (bitT a) (Tup Q1 as (Lab "()"))))
        (Tup Q1 (Lab "WCon") (Tup Q1 (bitT b) (Tup Q1 bs (Lab "()")))) (bitT f) (bitT c))
      (Tup Q1 (Lab "WCon") (Tup Q1 (bitT (fullAdd a (if f then !b else b) c).1)
        (Tup Q1 (groupCall n as bs (bitT f) (bitT (fullAdd a (if f then !b else b) c).2))
          (Lab "()")))) := by
  obtain ⟨dg, hg, hgv⟩ := R.group
  obtain ⟨df, hf, hfv⟩ := R.fullAdd
  obtain ⟨dx, hx, hxv⟩ := R.xor
  obtain ⟨da', ha, hav⟩ := R.and
  obtain ⟨do', ho, hov⟩ := R.or
  obtain ⟨dt, ht, htv⟩ := R.not
  have sn := value_step vn
  have sa := value_step va
  have sb := value_step vb
  apply stepUntil_sound (stop := roundEnd) (n := 200)
  cases f <;> cases a <;> cases b <;> cases c <;>
    simp (config := { maxSteps := 50000000 }) [stepUntil, roundEnd, step, call, fires, isArgs,
      isValue, stops, unspine, walk, redex, isData, hg, hgv, hf, hfv, hx, hxv, ha, hav, ho, hov,
      ht, htv, vn, dn, va, da, vb, db, sn, sa, sb, refGroup, refFullAdd, refXor, refAnd, refOr,
      refNot, groupCall, bitT, fullAdd, Quan.live, Quan.fld, takes, spine, Term.sub, Env.sub]

-- the last round: a call on two empty words gives the empty word
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem round0 (R : Refs bk) (f c : Bool) :
    Evals bk (groupCall (Tup Q1 (Lab "Zero") (Lab "()")) (wordT []) (wordT []) (bitT f) (bitT c))
      (wordT []) := by
  obtain ⟨dg, hg, hgv⟩ := R.group
  apply stepUntil_sound (stop := wnilEnd) (n := 50)
  cases f <;> cases c <;>
    simp (config := { maxSteps := 50000000 }) [stepUntil, wnilEnd, step, call, fires, isArgs,
      isValue, unspine, walk, isData, hg, hgv, refGroup, groupCall, wordT, bitT, Quan.live,
      Quan.fld, takes, spine, Term.sub, Env.sub]

-- Eval steps inside a word cell's tail
theorem evals_tail (h : Evals bk x x') :
    Evals bk (Tup Q1 (Lab "WCon") (Tup Q1 (bitT s) (Tup Q1 x (Lab "()"))))
      (Tup Q1 (Lab "WCon") (Tup Q1 (bitT s) (Tup Q1 x' (Lab "()")))) := by
  have vs := isValue_iff.1 (bit_value (bk := bk) (b := s)).1
  refine evals_map (fun y => Tup Q1 (Lab "WCon") (Tup Q1 (bitT s) (Tup Q1 y (Lab "()"))))
    (fun e => .tup_b (fun _ => .lab) (.tup_b (fun _ => vs) (.tup_a rfl e))) h

-- a group call on two words of n bits reaches the word that adcBits gives
theorem group_evals (R : Refs bk) : ∀ (as bs : List Bool) (f c : Bool), as.length = bs.length →
    Evals bk (groupCall (Bytes.nat as.length) (wordT as) (wordT bs) (bitT f) (bitT c))
      (wordT (adcBits f as bs c))
  | [], [], f, c, _ => round0 R f c
  | a :: as, b :: bs, f, c, h => by
    have vn := nat_value (bk := bk) (n := as.length)
    have va := word_value (bk := bk) (bs := as)
    have vb := word_value (bk := bk) (bs := bs)
    have r := round R vn.1 vn.2 va.1 va.2 vb.1 vb.2 f a b c
    exact evals_trans r (evals_tail (group_evals R as bs f _ (by simpa using h)))
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h

-- Jump
-- ====

def decBit : Term → Option Bool
  | Tup Q1 (Lab "True") (Lab "()") => some true
  | Tup Q1 (Lab "False") (Lab "()") => some false
  | _ => none

def decWord : Term → Option (List Bool)
  | Tup Q1 (Lab "WNil") (Lab "()") => some []
  | Tup Q1 (Lab "WCon") (Tup Q1 h (Tup Q1 t (Lab "()"))) => do
    let b ← decBit h
    let bs ← decWord t
    pure (b :: bs)
  | _ => none

def decNat : Term → Option Nat
  | Tup Q1 (Lab "Zero") (Lab "()") => some 0
  | Tup Q1 (Lab "Succ") (Tup Q1 n (Lab "()")) => (decNat n).map (· + 1)
  | _ => none

theorem decBit_ok (h : decBit t = some b) : t = bitT b := by
  unfold decBit at h
  split at h <;> simp_all [bitT]

theorem decWord_ok (h : decWord t = some bs) : t = wordT bs := by
  fun_induction decWord t generalizing bs with
  | case1 => cases h; rfl
  | case2 hd tl ih =>
    cases hb : decBit hd with
    | none => simp [hb] at h
    | some b =>
      cases ht : decWord tl with
      | none => simp [hb, ht] at h
      | some bs' =>
        simp [hb, ht] at h; subst h
        simp [wordT, decBit_ok hb, ih ht]
  | case3 => simp at h

theorem decNat_ok (h : decNat t = some n) : t = Bytes.nat n := by
  fun_induction decNat t generalizing n with
  | case1 => cases h; rfl
  | case2 m ih =>
    obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.1 h
    simp [Bytes.nat, ih hk]
  | case3 => simp at h

-- wordJump ok t: when ok and t is a group call on a width, two words of
-- that width and two Bools, the word that the call reaches
def wordJump (ok : Bool) : Term → Option Term
  | App Q1 (App Q1 (App Q1 (App Q1 (App Q1 (App Q1 (Ref "Word.adc.group") n) a) b) f)
      (Tup Q1 (Lab "Word.adc") (Lab "()"))) c =>
    if ok then do
      let m ← decNat n
      let as ← decWord a
      let bs ← decWord b
      let fb ← decBit f
      let cb ← decBit c
      if as.length = m ∧ bs.length = m then some (wordT (adcBits fb as bs cb)) else none
    else none
  | _ => none

theorem wordJump_sound (hr : ok = true → Refs bk) : wordJump ok t = some u → Plus bk t u := by
  intro h
  unfold wordJump at h
  split at h
  · rename_i n a b f c
    split at h
    · rename_i hok
      cases hm : decNat n with
      | none => simp [hm] at h
      | some m =>
      cases has : decWord a with
      | none => simp [hm, has] at h
      | some as =>
      cases hbs : decWord b with
      | none => simp [hm, has, hbs] at h
      | some bs =>
      cases hfb : decBit f with
      | none => simp [hm, has, hbs, hfb] at h
      | some fb =>
      cases hcb : decBit c with
      | none => simp [hm, has, hbs, hfb, hcb] at h
      | some cb =>
      simp only [hm, has, hbs, hfb, hcb, bind, Option.bind] at h
      split at h
      · rename_i len
        cases h
        rw [decNat_ok hm, decWord_ok has, decWord_ok hbs, decBit_ok hfb, decBit_ok hcb, ← len.1]
        refine plus_of (group_evals (hr hok) as bs fb cb (len.1.trans len.2.symm)) ?_
        cases adcBits fb as bs cb <;> simp [wordT]
      · simp at h
    · simp at h
  · simp at h

end Interp
