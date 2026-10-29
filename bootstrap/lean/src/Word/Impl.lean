import Word.Bits
import Word.Cmp
import Word.Nat
import Word.Mul

-- Word.Impl
-- =========
--
-- The word jump: a call of base's word code on values goes in one step to
-- the result that the proofs of that code give. A family of word defs
-- jumps only when the book's defs for it equal Word.Ref, and T.from_nat
-- only when T's defs equal the templates of Word.Nat (Found, made once per
-- run). jump_sound proves that each jump is one or more Eval steps.

open Quan Term Contract

namespace Interp.Word

-- Shapes
-- ======

-- jump1 k f: for a call of def k on a width and a word of that width, f of
-- the word's bits
def jump1 (k : String) (f : List Bool → Term) : Jump where
  takes := (· == k)
  go
    | App Q1 (App Q1 (Ref j) n) w =>
      if j = k then do
        let m ← decNat n
        let bs ← decWord w
        if bs.length = m then some (f bs) else none
      else none
    | _ => none

-- jump2 k f: for a call of def k on a width and two words of that width, f
-- of the words' bits
def jump2 (k : String) (f : List Bool → List Bool → Term) : Jump where
  takes := (· == k)
  go
    | App Q1 (App Q1 (App Q1 (Ref j) n) a) b =>
      if j = k then do
        let m ← decNat n
        let as ← decWord a
        let bs ← decWord b
        if as.length = m ∧ bs.length = m then some (f as bs) else none
      else none
    | _ => none

-- groupJump: for a call of Word.adc.group on a width, two words of that
-- width and two Bools, the word that adcBits gives
def groupJump : Jump where
  takes := (· == "Word.adc.group")
  go
    | App Q1 (App Q1 (App Q1 (App Q1 (App Q1 (App Q1 (Ref "Word.adc.group") n) a) b) f)
        (Tup Q1 (Lab "Word.adc") (Lab "()"))) c => do
      let m ← decNat n
      let as ← decWord a
      let bs ← decWord b
      let fb ← decBit f
      let cb ← decBit c
      if as.length = m ∧ bs.length = m then some (wordT (adcBits fb as bs cb)) else none
    | _ => none

-- mulJump: for a call of Word.mul.go on words, the word that mulGoBits
-- gives
def mulJump : Jump where
  takes := (· == "Word.mul.go")
  go
    | App Q1 (App Q2 (App Q1 (App Q1 (App Q2 (Ref "Word.mul.go") n) m) a) b) acc => do
      let k ← decNat n
      let j ← decNat m
      let as ← decWord a
      let bs ← decWord b
      let cs ← decWord acc
      if as.length = j ∧ bs.length = k ∧ cs.length = k then some (wordT (mulGoBits as bs cs))
      else none
    | _ => none

-- fromNatJump ts: for a call of T.from_nat on a Nat, for a type T of width
-- w in ts, the T whose word is that Nat's bits
def fromNatJump (ts : List (String × Nat)) : Jump :=
  let names := ts.map (·.1 ++ ".from_nat")
  ⟨names.contains, fun
    | App Q1 (Ref k) n => do
      let (T, w) ← ts.find? fun (T, _) => k == T ++ ".from_nat"
      let m ← decNat n
      some (boxT T (wordT (fromNatBits w m)))
    | _ => none⟩

theorem jump1_inv (h : (jump1 k f).go t = some u) :
    ∃ bs, t = callT k [Bytes.nat bs.length, wordT bs] ∧ u = f bs := by
  unfold jump1 at h
  dsimp only at h
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
        exact ⟨bs, by rw [decNat_sound hm, decWord_sound hw, ← len, hj]; rfl, rfl⟩
      · simp at h
    · simp at h
  · simp at h

theorem jump2_inv (h : (jump2 k f).go t = some u) :
    ∃ as bs, as.length = bs.length ∧ t = callT k [Bytes.nat as.length, wordT as, wordT bs] ∧
      u = f as bs := by
  unfold jump2 at h
  dsimp only at h
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
        rw [decNat_sound hm, decWord_sound ha, decWord_sound hb, ← len.1, hj]; rfl
      · simp at h
    · simp at h
  · simp at h

theorem groupJump_inv (h : groupJump.go t = some u) :
    ∃ as bs f c, as.length = bs.length ∧
      t = groupCall (Bytes.nat as.length) (wordT as) (wordT bs) (bitT f) (bitT c) ∧
      u = wordT (adcBits f as bs c) := by
  unfold groupJump at h
  dsimp only at h
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
      rw [decNat_sound hm, decWord_sound ha, decWord_sound hb, decBit_sound hf, decBit_sound hc,
        ← len.1]; rfl
    · simp at h
  · simp at h

theorem mulJump_inv (h : mulJump.go t = some u) :
    ∃ as bs cs, cs.length = bs.length ∧
      t = goCall (Bytes.nat bs.length) (Bytes.nat as.length) (wordT as) (wordT bs) (wordT cs) ∧
      u = wordT (mulGoBits as bs cs) := by
  unfold mulJump at h
  dsimp only at h
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
      rw [decNat_sound hn, decNat_sound hm, decWord_sound ha, decWord_sound hb, decWord_sound hc,
        ← len.1, ← len.2.1]; rfl
    · simp at h
  · simp at h

theorem fromNatJump_inv (h : (fromNatJump ts).go t = some u) :
    ∃ T w n, (T, w) ∈ ts ∧ t = callT (T ++ ".from_nat") [Bytes.nat n] ∧
      u = boxT T (wordT (fromNatBits w n)) := by
  unfold fromNatJump at h
  dsimp only at h
  split at h
  · rename_i k n
    cases hf : ts.find? (fun (T, _) => k == T ++ ".from_nat") with
    | none => simp [hf] at h
    | some p =>
    obtain ⟨T, w⟩ := p
    cases hm : decNat n with
    | none => simp [hf, hm] at h
    | some m =>
    simp only [hf, hm, bind, Option.bind, Option.some.injEq] at h
    have hk := List.find?_some hf
    simp only [beq_iff_eq] at hk
    exact ⟨T, w, m, List.mem_of_find?_eq_some hf, by rw [decNat_sound hm, hk]; rfl, h.symm⟩
  · simp at h

-- Jump
-- ====

structure Found where
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
  fromNat : List (String × Nat)

def found (bk : Book) : Found :=
  ⟨hasAdd bk, hasNot bk, hasBit bk .and, hasBit bk .or, hasBit bk .xor, hasInc bk, hasToNat bk,
    hasCmp bk, hasShl bk, hasShr bk, hasMul bk, fromNatTypes bk⟩

def bitJump (o : BitOp) : Jump :=
  jump2 o.word fun as bs => wordT (List.zipWith o.op as bs)

-- the jump of each family, and whether found has it
def families (found : Found) : List (Bool × Jump) :=
  [ (found.add, groupJump),
    (found.not, jump1 "Word.not" fun bs => wordT (bs.map (!·))),
    (found.and, bitJump .and),
    (found.or, bitJump .or),
    (found.xor, bitJump .xor),
    (found.inc, jump1 "Word.inc" fun bs => wordT (incBits bs)),
    (found.toNat, jump1 "Word.to_nat" fun bs => Bytes.nat (toNatBits bs)),
    (found.cmp, jump2 "Word.cmp" fun as bs => cmpT (cmpBits as bs)),
    (found.shl, jump1 "Word.shl" fun bs => wordT (shlBits bs)),
    (found.shr, jump1 "Word.shr" fun bs => wordT (shrBits bs)),
    (found.mul, mulJump),
    (!found.fromNat.isEmpty, fromNatJump found.fromNat) ]

-- jump found: the first jump of a family that found has. It takes what
-- those jumps take.
def jump (found : Found) : Jump :=
  let js := families found
  ⟨fun k => js.any fun (on, j) => on && j.takes k,
    fun t => js.findSome? fun (on, j) => if on then j.go t else none⟩

theorem bitJump_sound (H : HasBit bk o) (h : (bitJump o).go t = some u) : Plus bk t u := by
  obtain ⟨as, bs, len, rfl, rfl⟩ := jump2_inv h
  exact plus_tup (bit_evals H as bs len) word_tup

theorem jump_sound : Jump.Sound bk (jump (found bk)) := by
  intro t u h
  obtain ⟨⟨on, j⟩, mem, hj⟩ := List.exists_of_findSome?_eq_some h
  cases hon : on
  · simp [hon] at hj
  simp only [hon, ite_true] at hj
  simp only [families, found, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
  rcases mem with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ |
    ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ <;> rw [hon] at e
  · obtain ⟨as, bs, f, c, len, rfl, rfl⟩ := groupJump_inv hj
    exact plus_tup (group_evals (hasAdd_sound e.symm) as bs f c len) word_tup
  · obtain ⟨bs, rfl, rfl⟩ := jump1_inv hj
    exact plus_tup (not_evals (hasNot_sound e.symm) bs) word_tup
  · exact bitJump_sound (hasBit_sound e.symm) hj
  · exact bitJump_sound (hasBit_sound e.symm) hj
  · exact bitJump_sound (hasBit_sound e.symm) hj
  · obtain ⟨bs, rfl, rfl⟩ := jump1_inv hj
    exact plus_tup (inc_evals (hasRef_sound e.symm) bs) word_tup
  · obtain ⟨bs, rfl, rfl⟩ := jump1_inv hj
    exact plus_tup (toNat_evals (hasToNat_sound e.symm) bs) nat_tup
  · obtain ⟨as, bs, len, rfl, rfl⟩ := jump2_inv hj
    exact plus_tup (cmp_evals (hasCmp_sound e.symm) as bs len) ⟨_, _, _, rfl⟩
  · obtain ⟨bs, rfl, rfl⟩ := jump1_inv hj
    exact plus_tup (shl_evals (hasShl_sound e.symm) bs) word_tup
  · obtain ⟨bs, rfl, rfl⟩ := jump1_inv hj
    exact plus_tup (shr_evals (hasShr_sound e.symm) bs) word_tup
  · obtain ⟨as, bs, cs, len, rfl, rfl⟩ := mulJump_inv hj
    exact plus_tup (go_evals (hasMul_sound e.symm) as bs cs len) word_tup
  · obtain ⟨T, w, n, mem, rfl, rfl⟩ := fromNatJump_inv hj
    exact plus_tup (fromNat_evals (fromNatTypes_sound mem) n) ⟨_, _, _, rfl⟩

end Interp.Word
