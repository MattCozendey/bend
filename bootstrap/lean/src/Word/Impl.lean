import Word.Bits
import Word.Cmp
import Word.Nat
import Word.Mul

-- Word.Impl
-- =========
--
-- The word jump: a call of base's word code on values goes in one step to
-- the result that the proofs of that code give.

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

-- groupJump: for a groupCall on a width, two words of that width and two
-- bits, the word that adcBits gives
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

-- mulJump: for a goCall on a width, a count, a word of that count and two
-- words of that width, the word that mulGoBits gives
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

-- fromNatJump ts: for a call of T.from_nat on a Nat, with (T, w) in ts, the
-- T that fromNatBits gives
def fromNatJump (ts : List (String × Nat)) : Jump where
  takes := (ts.map (·.1 ++ ".from_nat")).contains
  go
    | App Q1 (Ref k) n => do
      let (T, w) ← ts.find? fun (T, _) => k == T ++ ".from_nat"
      let m ← decNat n
      some (boxT T (wordT (fromNatBits w m)))
    | _ => none

theorem jump1_sound (ev : ∀ bs, Evals bk (callT k [Bytes.nat bs.length, wordT bs]) (f bs))
    (tup : ∀ bs, ∃ q a b, f bs = Tup q a b) : Jump.Sound bk (jump1 k f) := by
  intro t u h
  unfold jump1 at h
  dsimp only at h
  split at h
  · bind_simp at h
    obtain ⟨rfl, _, hm, bs, hw, rfl, rfl⟩ := h
    rw [decNat_sound hm, decWord_sound hw]
    exact plus_tup (ev bs) (tup bs)
  · simp at h

theorem jump2_sound (ev : ∀ as bs, as.length = bs.length →
      Evals bk (callT k [Bytes.nat as.length, wordT as, wordT bs]) (f as bs))
    (tup : ∀ as bs, ∃ q a b, f as bs = Tup q a b) : Jump.Sound bk (jump2 k f) := by
  intro t u h
  unfold jump2 at h
  dsimp only at h
  split at h
  · bind_simp at h
    obtain ⟨rfl, _, hm, as, ha, bs, hb, ⟨rfl, len⟩, rfl⟩ := h
    rw [decNat_sound hm, decWord_sound ha, decWord_sound hb]
    exact plus_tup (ev as bs len.symm) (tup as bs)
  · simp at h

theorem groupJump_sound (H : HasRefs bk groupCode) : Jump.Sound bk groupJump := by
  intro t u h
  unfold groupJump at h
  dsimp only at h
  split at h
  · bind_simp at h
    obtain ⟨_, hm, as, ha, bs, hb, f, hf, c, hc, ⟨rfl, len⟩, rfl⟩ := h
    rw [decNat_sound hm, decWord_sound ha, decWord_sound hb, decBit_sound hf, decBit_sound hc]
    exact plus_tup (group_evals H as bs f c len.symm) word_tup
  · simp at h

theorem mulJump_sound (H : HasRefs bk mulCode) : Jump.Sound bk mulJump := by
  intro t u h
  unfold mulJump at h
  dsimp only at h
  split at h
  · bind_simp at h
    obtain ⟨_, hn, _, hm, as, ha, bs, hb, cs, hc, ⟨rfl, rfl, len⟩, rfl⟩ := h
    rw [decNat_sound hn, decNat_sound hm, decWord_sound ha, decWord_sound hb, decWord_sound hc]
    exact plus_tup (go_evals H as bs cs len) word_tup
  · simp at h

theorem fromNatJump_sound : Jump.Sound bk (fromNatJump (fromNatTypes bk)) := by
  intro t u h
  unfold fromNatJump at h
  dsimp only at h
  split at h
  · bind_simp at h
    obtain ⟨⟨T, w⟩, hf, m, hm, rfl⟩ := h
    have hk := List.find?_some hf
    simp only [beq_iff_eq] at hk
    rw [decNat_sound hm, hk]
    exact plus_tup (fromNat_evals (fromNatTypes_sound (List.mem_of_find?_eq_some hf)) m)
      ⟨_, _, _, rfl⟩
  · simp at h

-- Jump
-- ====

-- Family bk: a jump, the code that it needs, and the proof that the jump is
-- sound when bk has that code
structure Family (bk : Book) where
  code : List (String × Term)
  jump : Jump
  sound : HasRefs bk code → Jump.Sound bk jump

def bitFamily (o : BitOp) : Family bk :=
  ⟨o.code, jump2 o.word fun as bs => wordT (List.zipWith o.op as bs),
    fun H => jump2_sound (bit_evals H) fun _ _ => word_tup⟩

-- the families of base's word code. The T.from_nat family needs no code:
-- fromNatTypes makes its checks.
def families (bk : Book) : List (Family bk) :=
  [ ⟨groupCode, groupJump, groupJump_sound⟩,
    ⟨notCode, jump1 "Word.not" fun bs => wordT (bs.map (!·)),
      fun H => jump1_sound (not_evals H) fun _ => word_tup⟩,
    bitFamily .and,
    bitFamily .or,
    bitFamily .xor,
    ⟨incCode, jump1 "Word.inc" fun bs => wordT (incBits bs),
      fun H => jump1_sound (inc_evals H) fun _ => word_tup⟩,
    ⟨toNatCode, jump1 "Word.to_nat" fun bs => Bytes.nat (toNatBits bs),
      fun H => jump1_sound (toNat_evals H) fun _ => nat_tup⟩,
    ⟨cmpCode, jump2 "Word.cmp" fun as bs => cmpT (cmpBits as bs),
      fun H => jump2_sound (cmp_evals H) fun _ _ => ⟨_, _, _, rfl⟩⟩,
    ⟨shlCode, jump1 "Word.shl" fun bs => wordT (shlBits bs),
      fun H => jump1_sound (shl_evals H) fun _ => word_tup⟩,
    ⟨shrCode, jump1 "Word.shr" fun bs => wordT (shrBits bs),
      fun H => jump1_sound (shr_evals H) fun _ => word_tup⟩,
    ⟨mulCode, mulJump, mulJump_sound⟩,
    ⟨[], fromNatJump (fromNatTypes bk), fun _ => fromNatJump_sound⟩ ]

-- jump bk: the first result of the jumps whose code bk has. It takes each
-- def that one of these jumps takes. The let makes the checks once, when
-- jump bk is made, and not at each call.
def jump (bk : Book) : Jump :=
  let fs := (families bk).filter fun f => hasRefs bk f.code
  ⟨fun k => fs.any (·.jump.takes k), fun t => fs.findSome? (·.jump.go t)⟩

theorem jump_sound : Jump.Sound bk (jump bk) := by
  intro t u h
  obtain ⟨f, mem, hf⟩ := List.exists_of_findSome?_eq_some h
  exact f.sound (hasRefs_sound (List.mem_filter.1 mem).2) t u hf

end Interp.Word
