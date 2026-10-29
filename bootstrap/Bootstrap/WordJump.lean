import Bootstrap.WordBits
import Bootstrap.WordCmp
import Bootstrap.WordNat
import Bootstrap.WordMul

-- WordJump
-- ========
--
-- The word jump: a call of base's word code on values goes in one step to
-- the result that the proofs of that code give. A family of word defs
-- jumps only when the book's defs for it equal WordRef (WordOk, made once
-- per run). wordJump_sound proves that each jump is one or more Eval steps.

open Quan Term Spec

namespace Interp

-- Shapes
-- ======

-- jump1 k f t: when t is a call of def k on a width and a word of that
-- width, f of the word's bits
def jump1 (k : String) (f : List Bool → Term) : Term → Option Term
  | App Q1 (App Q1 (Ref j) n) w =>
    if j = k then do
      let m ← decNat n
      let bs ← decWord w
      if bs.length = m then some (f bs) else none
    else none
  | _ => none

-- jump2 k f t: when t is a call of def k on a width and two words of that
-- width, f of the words' bits
def jump2 (k : String) (f : List Bool → List Bool → Term) : Term → Option Term
  | App Q1 (App Q1 (App Q1 (Ref j) n) a) b =>
    if j = k then do
      let m ← decNat n
      let as ← decWord a
      let bs ← decWord b
      if as.length = m ∧ bs.length = m then some (f as bs) else none
    else none
  | _ => none

-- groupJump t: when t is a call of Word.adc.group on a width, two words of
-- that width and two Bools, the word that adcBits gives
def groupJump : Term → Option Term
  | App Q1 (App Q1 (App Q1 (App Q1 (App Q1 (App Q1 (Ref "Word.adc.group") n) a) b) f)
      (Tup Q1 (Lab "Word.adc") (Lab "()"))) c => do
    let m ← decNat n
    let as ← decWord a
    let bs ← decWord b
    let fb ← decBit f
    let cb ← decBit c
    if as.length = m ∧ bs.length = m then some (wordT (adcBits fb as bs cb)) else none
  | _ => none

-- mulJump t: when t is a call of Word.mul.go on words, the word that
-- mulGoBits gives
def mulJump : Term → Option Term
  | App Q1 (App Q2 (App Q1 (App Q1 (App Q2 (Ref "Word.mul.go") n) m) a) b) acc => do
    let k ← decNat n
    let j ← decNat m
    let as ← decWord a
    let bs ← decWord b
    let cs ← decWord acc
    if as.length = j ∧ bs.length = k ∧ cs.length = k then some (wordT (mulGoBits as bs cs))
    else none
  | _ => none

theorem jump1_spec (h : jump1 k f t = some u) :
    ∃ bs, t = callT k [Bytes.nat bs.length, wordT bs] ∧ u = f bs := by
  unfold jump1 at h
  split at h
  · rename_i j n w
    split at h
    · rename_i hj
      cases hm : decNat n with
      | none => simp [hm] at h
      | some m =>
      cases hw : decWord w with
      | none => simp [hm, hw] at h
      | some bs =>
      simp only [hm, hw, bind, Option.bind] at h
      split at h
      · rename_i len
        cases h
        exact ⟨bs, by rw [decNat_ok hm, decWord_ok hw, ← len, hj]; rfl, rfl⟩
      · simp at h
    · simp at h
  · simp at h

theorem jump2_spec (h : jump2 k f t = some u) :
    ∃ as bs, as.length = bs.length ∧ t = callT k [Bytes.nat as.length, wordT as, wordT bs] ∧
      u = f as bs := by
  unfold jump2 at h
  split at h
  · rename_i j n a b
    split at h
    · rename_i hj
      cases hm : decNat n with
      | none => simp [hm] at h
      | some m =>
      cases ha : decWord a with
      | none => simp [hm, ha] at h
      | some as =>
      cases hb : decWord b with
      | none => simp [hm, ha, hb] at h
      | some bs =>
      simp only [hm, ha, hb, bind, Option.bind] at h
      split at h
      · rename_i len
        cases h
        refine ⟨as, bs, len.1.trans len.2.symm, ?_, rfl⟩
        rw [decNat_ok hm, decWord_ok ha, decWord_ok hb, ← len.1, hj]; rfl
      · simp at h
    · simp at h
  · simp at h

theorem groupJump_spec (h : groupJump t = some u) :
    ∃ as bs f c, as.length = bs.length ∧
      t = groupCall (Bytes.nat as.length) (wordT as) (wordT bs) (bitT f) (bitT c) ∧
      u = wordT (adcBits f as bs c) := by
  unfold groupJump at h
  split at h
  · rename_i n a b f c
    cases hm : decNat n with
    | none => simp [hm] at h
    | some m =>
    cases ha : decWord a with
    | none => simp [hm, ha] at h
    | some as =>
    cases hb : decWord b with
    | none => simp [hm, ha, hb] at h
    | some bs =>
    cases hf : decBit f with
    | none => simp [hm, ha, hb, hf] at h
    | some fb =>
    cases hc : decBit c with
    | none => simp [hm, ha, hb, hf, hc] at h
    | some cb =>
    simp only [hm, ha, hb, hf, hc, bind, Option.bind] at h
    split at h
    · rename_i len
      cases h
      refine ⟨as, bs, fb, cb, len.1.trans len.2.symm, ?_, rfl⟩
      rw [decNat_ok hm, decWord_ok ha, decWord_ok hb, decBit_ok hf, decBit_ok hc, ← len.1]; rfl
    · simp at h
  · simp at h

theorem mulJump_spec (h : mulJump t = some u) :
    ∃ as bs cs, cs.length = bs.length ∧
      t = goCall (Bytes.nat bs.length) (Bytes.nat as.length) (wordT as) (wordT bs) (wordT cs) ∧
      u = wordT (mulGoBits as bs cs) := by
  unfold mulJump at h
  split at h
  · rename_i n m a b acc
    cases hn : decNat n with
    | none => simp [hn] at h
    | some k =>
    cases hm : decNat m with
    | none => simp [hn, hm] at h
    | some j =>
    cases ha : decWord a with
    | none => simp [hn, hm, ha] at h
    | some as =>
    cases hb : decWord b with
    | none => simp [hn, hm, ha, hb] at h
    | some bs =>
    cases hc : decWord acc with
    | none => simp [hn, hm, ha, hb, hc] at h
    | some cs =>
    simp only [hn, hm, ha, hb, hc, bind, Option.bind] at h
    split at h
    · rename_i len
      cases h
      refine ⟨as, bs, cs, len.2.2.trans len.2.1.symm, ?_, rfl⟩
      rw [decNat_ok hn, decNat_ok hm, decWord_ok ha, decWord_ok hb, decWord_ok hc, ← len.1,
        ← len.2.1]; rfl
    · simp at h
  · simp at h

-- Jump
-- ====

structure WordOk where
  add : Bool
  not : Bool
  and : Bool
  or : Bool
  xor : Bool
  inc : Bool
  toNat : Bool
  cmp : Bool
  shl : Bool
  shr : Bool
  mul : Bool

def wordOk (bk : Book) : WordOk :=
  ⟨addOk bk, notOk bk, bitOk bk .and, bitOk bk .or, bitOk bk .xor, incOk bk, toNatOk bk,
    cmpOk bk, shlOk bk, shrOk bk, mulOk bk⟩

def bitJump (o : BitOp) : Term → Option Term :=
  jump2 o.word fun as bs => wordT (List.zipWith o.op as bs)

-- wordJump ok t: the first jump of a family that ok allows
def wordJump (ok : WordOk) (t : Term) : Option Term :=
  [ (ok.add, groupJump),
    (ok.not, jump1 "Word.not" fun bs => wordT (bs.map (!·))),
    (ok.and, bitJump .and),
    (ok.or, bitJump .or),
    (ok.xor, bitJump .xor),
    (ok.inc, jump1 "Word.inc" fun bs => wordT (incBits bs)),
    (ok.toNat, jump1 "Word.to_nat" fun bs => Bytes.nat (toNatBits bs)),
    (ok.cmp, jump2 "Word.cmp" fun as bs => cmpT (cmpBits as bs)),
    (ok.shl, jump1 "Word.shl" fun bs => wordT (shlBits bs)),
    (ok.shr, jump1 "Word.shr" fun bs => wordT (shrBits bs)),
    (ok.mul, mulJump) ].findSome? fun (on, j) => if on then j t else none

theorem bitJump_sound (H : BitRefs bk o) (h : bitJump o t = some u) : Plus bk t u := by
  obtain ⟨as, bs, len, rfl, rfl⟩ := jump2_spec h
  exact plus_tup (bit_evals H as bs len) word_tup

theorem wordJump_sound : wordJump (wordOk bk) t = some u → Plus bk t u := by
  intro h
  obtain ⟨⟨on, j⟩, mem, hj⟩ := List.exists_of_findSome?_eq_some h
  cases hon : on
  · simp [hon] at hj
  simp only [hon, ite_true] at hj
  simp only [wordOk, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
  rcases mem with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ |
    ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ <;> rw [hon] at e
  · obtain ⟨as, bs, f, c, len, rfl, rfl⟩ := groupJump_spec hj
    exact plus_tup (group_evals (addOk_ok e.symm) as bs f c len) word_tup
  · obtain ⟨bs, rfl, rfl⟩ := jump1_spec hj
    exact plus_tup (not_evals (notOk_ok e.symm) bs) word_tup
  · exact bitJump_sound (bitOk_ok e.symm) hj
  · exact bitJump_sound (bitOk_ok e.symm) hj
  · exact bitJump_sound (bitOk_ok e.symm) hj
  · obtain ⟨bs, rfl, rfl⟩ := jump1_spec hj
    exact plus_tup (inc_evals (hasRef_ok e.symm) bs) word_tup
  · obtain ⟨bs, rfl, rfl⟩ := jump1_spec hj
    exact plus_tup (toNat_evals (toNatOk_ok e.symm) bs) nat_tup
  · obtain ⟨as, bs, len, rfl, rfl⟩ := jump2_spec hj
    exact plus_tup (cmp_evals (cmpOk_ok e.symm) as bs len) ⟨_, _, _, rfl⟩
  · obtain ⟨bs, rfl, rfl⟩ := jump1_spec hj
    exact plus_tup (shl_evals (shlOk_ok e.symm) bs) word_tup
  · obtain ⟨bs, rfl, rfl⟩ := jump1_spec hj
    exact plus_tup (shr_evals (shrOk_ok e.symm) bs) word_tup
  · obtain ⟨as, bs, cs, len, rfl, rfl⟩ := mulJump_spec hj
    exact plus_tup (go_evals (mulOk_ok e.symm) as bs cs len) word_tup

end Interp
