import Bootstrap.Code

-- Ops.Kit
-- =======
--
-- Exact counts of the steps of Eval, for the proofs of Bootstrap/Ops.lean: a
-- call steps once to the leaf of its walk; the arguments of a call and the
-- fields of a pair take their steps in order, one after the other.

open Quan Term

set_option linter.unusedSimpArgs false

namespace Ops

-- the book holds a def named k, whose term is v
def Has (bk : Book) (k : String) (v : Term) : Prop := ∃ d, Book.get bk k = some d ∧ d.v = v

-- Has, computed: the def's term is compared, as a Term
def has (bk : Book) (k : String) (v : Term) : Bool :=
  match Book.get bk k with
  | some d => d.v == v
  | none => false

theorem has_sound (h : has bk k v = true) : Has bk k v := by
  unfold has at h
  split at h
  next d hk => exact ⟨d, hk, beq_iff_eq.1 h⟩
  next => cases h

-- a call whose arguments are values steps to the leaf of its walk
theorem step_call (h : Has bk k b) (vs : Values bk xs) (w : walk bk b [] xs = some (some u))
    (s : Steps bk n u r) : Steps bk (n + 1) (spine (Ref k) xs) r := by
  obtain ⟨d, hk, rfl⟩ := h
  exact .step (Eval.walk hk vs w) s

-- a call that needs more arguments is a value
theorem part (h : Has bk k b) (vs : Values bk xs) (w : walk bk b [] xs = some none) :
    Value bk (spine (Ref k) xs) := by
  obtain ⟨d, hk, rfl⟩ := h
  exact .call hk vs (walk_iff.1 w)

-- the live argument of a function that is a value takes its steps first
theorem arg (vf : Value bk f) (l : q.live = true) (sx : Steps bk n x x')
    (s : Steps bk m (App q f x') r) : Steps bk (n + m) (App q f x) r :=
  (Steps.app_x vf l sx).trans s

-- the function of an application takes its steps first
theorem fn (sf : Steps bk n f f') (s : Steps bk m (App q f' x) r) :
    Steps bk (n + m) (App q f x) r :=
  sf.app_f.trans s

-- an annotation steps to its term
theorem ann (s : Steps bk n x r) : Steps bk (n + 1) (Ann x T) r := .step .ann s

theorem tup_a (h : Steps bk n a a') : Steps bk n (Tup Q1 a b) (Tup Q1 a' b) := by
  induction h with
  | refl => exact .refl
  | step e _ ih => exact .step (.tup_a rfl e) ih

theorem tup_b (va : Value bk a) (h : Steps bk n b b') : Steps bk n (Tup Q1 a b) (Tup Q1 a b') := by
  induction h with
  | refl => exact .refl
  | step e _ ih => exact .step (.tup_b (fun _ => va) e) ih

-- a pair at quantity 1 takes the steps of its first field, then of its second
theorem tup (sa : Steps bk n a a') (va : Value bk a') (sb : Steps bk m b b') :
    Steps bk (n + m) (Tup Q1 a b) (Tup Q1 a' b') :=
  (tup_a sa).trans (tup_b va sb)

-- a constructor of one field takes the steps of its field
theorem ctor1 (s : Steps bk n a a') : Steps bk n (ctor k [a]) (ctor k [a']) :=
  tup_b .lab (tup_a s)

-- a constructor of two fields takes the steps of each field, in order
theorem ctor2 (sa : Steps bk n a a') (va : Value bk a') (sb : Steps bk m b b') :
    Steps bk (n + m) (ctor k [a, b]) (ctor k [a', b']) :=
  tup_b .lab (tup sa va (tup_a sb))

-- a constructor of two fields, the first a value
theorem ctor2v (va : Value bk a) (sb : Steps bk m b b') :
    Steps bk m (ctor k [a, b]) (ctor k [a, b']) :=
  tup_b .lab (tup_b va (tup_a sb))

theorem steps_eq (s : Steps bk n t r) (hn : n = n') (hr : r = r') : Steps bk n' t r' := hn ▸ hr ▸ s

-- Forms
-- -----

-- the form of a bit
abbrev bit (v : Nat) : Term := ctor (if v % 2 = 1 then "True" else "False") []

-- a U32, as `bend -o` writes it
def u32 (v : Nat) : Term := ctor "U32" [bits 32 v]

theorem value_bit : Value bk (bit v) := value_ctor nofun

theorem value_u32 : Value bk (u32 v) := value_ctor (by simpa using value_bits)

theorem data_bits' : data (bits n v) = true := data_iff.2 data_bits

theorem data_nat' : data (Form.nat n) = true := data_iff.2 data_nat

theorem data_u32 : data (u32 v) = true := data_iff.2 (data_ctor (by simpa using data_bits))

-- a word of n + 1 bits, by its lowest bit and the rest
theorem bits_succ : bits (n + 1) v = ctor "WCon" [bit v, bits n (v / 2)] := rfl

-- a word of n + 1 bits whose value is b + 2 x, for a bit b
theorem bits_cons (hb : b < 2) : bits (n + 1) (b + 2 * x) = ctor "WCon" [bit b, bits n x] := by
  have h1 : (b + 2 * x) % 2 = b % 2 := by omega
  have h2 : (b + 2 * x) / 2 = x := by omega
  rw [bits_succ]; simp only [bit, h1, h2]

-- a word of n + 1 bits whose lowest bit is v's
theorem bits_mod2 : bits (n + 1) (v % 2 + 2 * x) = ctor "WCon" [bit v, bits n x] := by
  rw [bits_cons (Nat.mod_lt _ (by omega))]; simp only [bit, Nat.mod_mod]

-- a word is the form of its value modulo 2 ^ n
theorem bits_mod : bits n (v % 2 ^ n) = bits n v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    have h1 : v % 2 ^ (n + 1) % 2 = v % 2 := by
      rw [Nat.pow_succ', Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right 2 _)]
    have h2 : v % 2 ^ (n + 1) / 2 = v / 2 % 2 ^ n := by
      rw [Nat.pow_succ', Nat.mod_mul_right_div_self]
    rw [bits_succ, bits_succ]; simp only [bit, h1, h2, ih]

-- a substitution leaves a nat, a word, a U32 as they are
theorem sub_nat : Term.sub s (Form.nat n) = Form.nat n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Form.nat, ctor, Term.sub, ih]

theorem sub_bits : Term.sub s (bits n v) = bits n v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [bits, ctor, Term.sub, ih]

theorem sub_u32 : Term.sub s (u32 v) = u32 v := by simp [u32, ctor, Term.sub, sub_bits]

-- the form of a nat of n + 1
theorem nat_succ : Form.nat (n + 1) = ctor "Succ" [Form.nat n] := rfl

-- Arguments
-- ---------

-- the labels of a cell (Bootstrap/Bytes.lean), taken from the cells: compiled
-- code compares two strings by pointer first, so a cell's labels, and those of
-- the words built here, compare at once
def labU32 : String := match cell 1 with | Tup _ (Lab k) _ => k | _ => "U32"
def labUnit : String := match cell 1 with | Tup _ _ (Tup _ _ (Lab k)) => k | _ => "()"
def labWCon : String := match cell 1 with | Tup _ _ (Tup _ (Tup _ (Lab k) _) _) => k | _ => "WCon"
def labTrue : String :=
  match cell 1 with | Tup _ _ (Tup _ (Tup _ _ (Tup _ (Tup _ (Lab k) _) _)) _) => k | _ => "True"
def labFalse : String :=
  match cell 0 with | Tup _ _ (Tup _ (Tup _ _ (Tup _ (Tup _ (Lab k) _) _)) _) => k | _ => "False"
def labWNil : String := match bits 0 0 with | Tup _ (Lab k) _ => k | _ => "WNil"

theorem labU32_eq : labU32 = "U32" := rfl
theorem labUnit_eq : labUnit = "()" := rfl
theorem labWCon_eq : labWCon = "WCon" := rfl
theorem labTrue_eq : labTrue = "True" := rfl
theorem labFalse_eq : labFalse = "False" := rfl
theorem labWNil_eq : labWNil = "WNil" := rfl

-- the value of a word of n bits, lowest bit first: acc, plus p times the
-- value of the word w
def decW : Nat → @& Term → Nat → Nat → Option Nat
  | 0, Tup Q1 (Lab k) (Lab u), acc, _ => if k = labWNil ∧ u = labUnit then some acc else none
  | n + 1, Tup Q1 (Lab k) (Tup Q1 (Tup Q1 (Lab b) (Lab u1)) (Tup Q1 w (Lab u2))), acc, p =>
    if k = labWCon ∧ u1 = labUnit ∧ u2 = labUnit then
      if b = labTrue then decW n w (acc + p) (2 * p)
      else if b = labFalse then decW n w acc (2 * p)
      else none
    else none
  | _, _, _, _ => none

theorem decW_eq (h : decW n w acc p = some v) : ∃ x, w = bits n x ∧ x < 2 ^ n ∧ v = acc + p * x := by
  fun_induction decW n w acc p generalizing v
  all_goals try simp only [labWNil_eq, labUnit_eq, labWCon_eq, labTrue_eq, labFalse_eq] at *
  all_goals try (cases h; done)
  · rename_i k u acc _ hk
    obtain ⟨rfl, rfl⟩ := hk; cases h; exact ⟨0, rfl, by simp, by simp⟩
  · rename_i n k u1 w u2 acc p hk ih
    obtain ⟨rfl, rfl, rfl⟩ := hk
    obtain ⟨x, rfl, hx, rfl⟩ := ih h
    refine ⟨1 + 2 * x, ?_, by rw [Nat.pow_succ]; omega, ?_⟩
    · rw [bits_cons (by omega)]; simp [ctor]
    · rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm p 2]; omega
  · rename_i n k u1 w u2 acc p hk _ ih
    obtain ⟨rfl, rfl, rfl⟩ := hk
    obtain ⟨x, rfl, hx, rfl⟩ := ih h
    refine ⟨0 + 2 * x, ?_, by rw [Nat.pow_succ]; omega, ?_⟩
    · rw [bits_cons (by omega)]; simp [ctor]
    · rw [Nat.zero_add, ← Nat.mul_assoc, Nat.mul_comm p 2]

-- the value of a U32 term
def decU32 : @& Term → Option Nat
  | Tup Q1 (Lab k) (Tup Q1 w (Lab u)) => if k = labU32 ∧ u = labUnit then decW 32 w 0 1 else none
  | _ => none

theorem decU32_eq (h : decU32 t = some v) : t = u32 v ∧ v < 2 ^ 32 := by
  unfold decU32 at h
  split at h
  next k w u =>
    split at h
    next hk =>
      simp only [labU32_eq, labUnit_eq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      obtain ⟨x, rfl, hx, rfl⟩ := decW_eq h
      simp only [Nat.zero_add, Nat.one_mul]
      exact ⟨rfl, hx⟩
    next => cases h
  next => cases h

-- the value of a nat term, plus a
def decNat : @& Term → Nat → Option Nat
  | Tup Q1 (Lab "Zero") (Lab "()"), a => some a
  | Tup Q1 (Lab "Succ") (Tup Q1 t (Lab "()")), a => decNat t (a + 1)
  | _, _ => none

theorem decNat_eq (h : decNat t a = some m) : t = Form.nat (m - a) ∧ a ≤ m := by
  fun_induction decNat t a generalizing m
  next a => cases h; simp [Form.nat, ctor]
  next t a ih =>
    obtain ⟨e, l⟩ := ih h
    refine ⟨?_, by omega⟩
    rw [e, show m - a = (m - (a + 1)) + 1 by omega]
    rfl
  next => cases h

-- Results
-- -------

-- the parts of a word, made once
def wnilT : Term := Tup Q1 (Lab labWNil) (Lab labUnit)
def wconL : Term := Lab labWCon
def unitL : Term := Lab labUnit
def u32L : Term := Lab labU32
def trueB : Term := Tup Q1 (Lab labTrue) (Lab labUnit)
def falseB : Term := Tup Q1 (Lab labFalse) (Lab labUnit)

-- the words of n zero bits, n ≤ 32, made once
def zeroW : Array Term := Array.ofFn (n := 33) fun i => bits i.val 0

-- bits n v, with its parts shared, and its top zero bits too
def mkBits : Nat → Nat → Term
  | 0, _ => wnilT
  | n + 1, v =>
    if v = 0 then zeroW.getD (n + 1) (bits (n + 1) 0)
    else Tup Q1 wconL (Tup Q1 (if v % 2 = 1 then trueB else falseB) (Tup Q1 (mkBits n (v / 2)) unitL))

theorem mkBits_eq : mkBits n v = bits n v := by
  induction n generalizing v with
  | zero => simp [mkBits, wnilT, labWNil_eq, labUnit_eq, bits, ctor]
  | succ n ih =>
    unfold mkBits
    split
    next h =>
      subst h
      unfold Array.getD
      split
      next hn => simp [zeroW]
      next => rfl
    next =>
      rw [ih, bits_succ]
      split <;> simp_all [ctor, wconL, unitL, trueB, falseB, labWCon_eq, labUnit_eq, labTrue_eq, labFalse_eq]

-- a U32, with the 256 cells shared
def mkU32 (v : Nat) : Term :=
  if v < 256 then cell v.toUInt8 else Tup Q1 u32L (Tup Q1 (mkBits 32 v) unitL)

theorem mkU32_eq : mkU32 v = u32 v := by
  unfold mkU32
  split
  next h =>
    have : v.toUInt8.toNat = v := by simp [Nat.toUInt8, UInt8.toNat_ofNat]; omega
    simp [cell, u32, this]
  next => simp [mkBits_eq, u32, ctor, u32L, unitL, labU32_eq, labUnit_eq]

end Ops
