import Bootstrap.Ops.Kit
import Bootstrap.Ops.Defs

-- Ops.Cmp
-- =======
--
-- The steps of Bool.cmp, Word.cmp.fin, Word.cmp, U32.cmp, of the Cmp.is_*
-- tests, and of U32.is_eq, is_ne, is_lt, is_le, is_gt, is_ge, is_zero.

open Quan Term

set_option linter.unusedSimpArgs false

set_option maxRecDepth 4000

namespace Ops

-- the form of a Cmp
def cmpK : Ordering → String
  | .lt => "LT"
  | .eq => "EQ"
  | .gt => "GT"

def cmpT (o : Ordering) : Term := ctor (cmpK o) []

theorem value_cmpT : Value bk (cmpT o) := value_ctor nofun

-- Word.cmp.fin ab bb t: t, or the comparison of the bits when t is EQ
def finV (o : Ordering) (v w : Nat) : Ordering :=
  match o with
  | .lt => .lt
  | .eq => compare (v % 2) (w % 2)
  | .gt => .gt

-- Word.cmp n a b, from the top bit down
def cmpV : Nat → Nat → Nat → Ordering
  | 0, _, _ => .eq
  | n + 1, v, w => finV (cmpV n (v / 2) (w / 2)) v w

def cmpC : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | n + 1, v, w => cmpC n (v / 2) (w / 2) + (if cmpV n (v / 2) (w / 2) = .eq then 3 else 2)

theorem bool_cmp_steps (h : Has bk "Bool.cmp" «opsDefs.Bool.cmp».v) :
    Steps bk 1 (App Q1 (App Q1 (Ref "Bool.cmp") (bit v)) (bit w)) (cmpT (compare (v % 2) (w % 2))) := by
  rcases Nat.mod_two_eq_zero_or_one v with hv | hv <;>
  rcases Nat.mod_two_eq_zero_or_one w with hw | hw <;>
  exact step_call (xs := [(Q1, _), (Q1, _)]) h (.cons (fun _ => value_bit) (.cons (fun _ => value_bit) .nil))
    (by simp [walk, «opsDefs.Bool.cmp», hv, hw, ctor, cmpT, cmpK, takes, Quan.live, Quan.fld, Term.sub,
      spine, compare, compareOfLessAndEq]) .refl

theorem value_fin (h : Has bk "Word.cmp.fin" «opsDefs.Word.cmp.fin».v) :
    Value bk (App Q1 (App Q1 (Ref "Word.cmp.fin") (bit v)) (bit w)) :=
  part (xs := [(Q1, _), (Q1, _)]) h (.cons (fun _ => value_bit) (.cons (fun _ => value_bit) .nil))
    (by simp [walk, «opsDefs.Word.cmp.fin», takes, bindsAt, Quan.live])

theorem fin_steps (h : Has bk "Word.cmp.fin" «opsDefs.Word.cmp.fin».v)
    (hb : Has bk "Bool.cmp" «opsDefs.Bool.cmp».v) :
    Steps bk (if o = .eq then 2 else 1) (App Q1 (App Q1 (App Q1 (Ref "Word.cmp.fin") (bit v)) (bit w)) (cmpT o))
      (cmpT (finV o v w)) := by
  have vs : Values bk [(Q1, bit v), (Q1, bit w), (Q1, cmpT o)] :=
    .cons (fun _ => value_bit) (.cons (fun _ => value_bit) (.cons (fun _ => value_cmpT) .nil))
  cases o
  · exact step_call (xs := [(Q1, _), (Q1, _), (Q1, _)]) h vs
      (by simp [walk, «opsDefs.Word.cmp.fin», cmpT, cmpK, finV, ctor, takes, bindsAt, data, Quan.live,
        Quan.fld, Term.sub, spine]) .refl
  · exact step_call (xs := [(Q1, _), (Q1, _), (Q1, _)]) h vs
      (u := App Q1 (App Q1 (Ref "Bool.cmp") (bit v)) (bit w))
      (by simp [walk, «opsDefs.Word.cmp.fin», cmpT, cmpK, ctor, takes, bindsAt, data, Quan.live,
        Quan.fld, Term.sub, spine, Env.sub]) (bool_cmp_steps hb)
  · exact step_call (xs := [(Q1, _), (Q1, _), (Q1, _)]) h vs
      (by simp [walk, «opsDefs.Word.cmp.fin», cmpT, cmpK, finV, ctor, takes, bindsAt, data, Quan.live,
        Quan.fld, Term.sub, spine]) .refl

-- the defs that Word.cmp reaches
structure WordCmpDefs (bk : Book) : Prop where
  word : Has bk "Word.cmp" «opsDefs.Word.cmp».v
  fin : Has bk "Word.cmp.fin" «opsDefs.Word.cmp.fin».v
  bool : Has bk "Bool.cmp" «opsDefs.Bool.cmp».v

theorem word_cmp_steps (h : WordCmpDefs bk) :
    Steps bk (cmpC n v w) (App Q1 (App Q1 (App Q1 (Ref "Word.cmp") (Form.nat n)) (bits n v)) (bits n w))
      (cmpT (cmpV n v w)) := by
  have vs : ∀ n v w, Values bk [(Q1, Form.nat n), (Q1, bits n v), (Q1, bits n w)] := fun _ _ _ =>
    .cons (fun _ => value_nat) (.cons (fun _ => value_bits) (.cons (fun _ => value_bits) .nil))
  induction n generalizing v w with
  | zero =>
    exact step_call (xs := [(Q1, _), (Q1, _), (Q1, _)]) h.word (vs _ _ _)
      (by simp [walk, «opsDefs.Word.cmp», Form.nat, bits, ctor, cmpT, cmpK, cmpV, takes, Quan.live,
        Quan.fld, Term.sub, spine, bindsAt]) .refl
  | succ n ih =>
    refine steps_eq (step_call (xs := [(Q1, _), (Q1, _), (Q1, _)]) h.word (vs _ _ _)
      (u := App Q1 (App Q1 (App Q1 (Ref "Word.cmp.fin") (bit v)) (bit w))
        (App Q1 (App Q1 (App Q1 (Ref "Word.cmp") (Form.nat n)) (bits n (v / 2))) (bits n (w / 2))))
      (by simp [walk, «opsDefs.Word.cmp», nat_succ, bits_succ, ctor, takes, Quan.live, Quan.fld,
        Term.sub, spine, bindsAt, Env.sub, sub_nat, sub_bits, data_nat', data_bits'])
      (arg (value_fin h.fin) rfl ih (fin_steps h.fin h.bool))) ?_ rfl
    simp only [cmpC]
    split <;> simp_all <;> omega

-- the defs that U32.cmp reaches
structure CmpDefs (bk : Book) : Prop where
  u32 : Has bk "U32.cmp" «opsDefs.U32.cmp».v
  word : WordCmpDefs bk

theorem u32_cmp_steps (h : CmpDefs bk) :
    Steps bk (cmpC 32 v w + 1) (App Q1 (App Q1 (Ref "U32.cmp") (u32 v)) (u32 w)) (cmpT (cmpV 32 v w)) :=
  step_call (xs := [(Q1, _), (Q1, _)]) h.u32 (.cons (fun _ => value_u32) (.cons (fun _ => value_u32) .nil))
    (u := App Q1 (App Q1 (App Q1 (Ref "Word.cmp") (Form.nat 32)) (bits 32 v)) (bits 32 w))
    (by simp [walk, «opsDefs.U32.cmp», u32, ctor, takes, bindsAt, Quan.live, Quan.fld, Term.sub,
      spine, Env.sub, sub_nat, Term.unspine])
    (word_cmp_steps h.word)

-- each Cmp test steps once to its Bool
theorem is_steps {f : Ordering → Term} (h : Has bk c t)
    (w : ∀ o, walk bk t [] [(Q1, cmpT o)] = some (some (f o))) :
    Steps bk 1 (App Q1 (Ref c) (cmpT o)) (f o) :=
  step_call (xs := [(Q1, _)]) h (.cons (fun _ => value_cmpT) .nil) (w o) .refl

theorem is_eq_steps (h : Has bk "Cmp.is_eq" «opsDefs.Cmp.is_eq».v) :
    Steps bk 1 (App Q1 (Ref "Cmp.is_eq") (cmpT o)) (Form.bool (o == .eq)) :=
  is_steps (f := fun o => Form.bool (o == .eq)) h fun o => by
    cases o <;> simp [walk, «opsDefs.Cmp.is_eq», cmpT, cmpK, ctor, Form.bool, takes, bindsAt, Quan.live,
      Quan.fld, Term.sub, spine, data]

theorem is_lt_steps (h : Has bk "Cmp.is_lt" «opsDefs.Cmp.is_lt».v) :
    Steps bk 1 (App Q1 (Ref "Cmp.is_lt") (cmpT o)) (Form.bool (o == .lt)) :=
  is_steps (f := fun o => Form.bool (o == .lt)) h fun o => by
    cases o <;> simp [walk, «opsDefs.Cmp.is_lt», cmpT, cmpK, ctor, Form.bool, takes, bindsAt, Quan.live,
      Quan.fld, Term.sub, spine, data]

theorem is_le_steps (h : Has bk "Cmp.is_le" «opsDefs.Cmp.is_le».v) :
    Steps bk 1 (App Q1 (Ref "Cmp.is_le") (cmpT o)) (Form.bool (o != .gt)) :=
  is_steps (f := fun o => Form.bool (o != .gt)) h fun o => by
    cases o <;> simp [walk, «opsDefs.Cmp.is_le», cmpT, cmpK, ctor, Form.bool, takes, bindsAt, Quan.live,
      Quan.fld, Term.sub, spine, data]

theorem is_gt_steps (h : Has bk "Cmp.is_gt" «opsDefs.Cmp.is_gt».v) :
    Steps bk 1 (App Q1 (Ref "Cmp.is_gt") (cmpT o)) (Form.bool (o == .gt)) :=
  is_steps (f := fun o => Form.bool (o == .gt)) h fun o => by
    cases o <;> simp [walk, «opsDefs.Cmp.is_gt», cmpT, cmpK, ctor, Form.bool, takes, bindsAt, Quan.live,
      Quan.fld, Term.sub, spine, data]

theorem is_ge_steps (h : Has bk "Cmp.is_ge" «opsDefs.Cmp.is_ge».v) :
    Steps bk 1 (App Q1 (Ref "Cmp.is_ge") (cmpT o)) (Form.bool (o != .lt)) :=
  is_steps (f := fun o => Form.bool (o != .lt)) h fun o => by
    cases o <;> simp [walk, «opsDefs.Cmp.is_ge», cmpT, cmpK, ctor, Form.bool, takes, bindsAt, Quan.live,
      Quan.fld, Term.sub, spine, data]

-- a def whose case tree takes an argument is a value
theorem value_ref (h : Has bk c t) (ht : takes t = true) : Value bk (Ref c) :=
  part (xs := []) h .nil (walk_need ht)

-- a U32 test: c applied to the U32.cmp of a and b
abbrev u32Is (c : String) : Term :=
  Lam Q1 (Lam Q1 (App Q1 (Ref c) (App Q1 (App Q1 (Ref "U32.cmp") (Var 1)) (Var 0))))

theorem u32_is_steps {f : Ordering → Term} (h : Has bk k (u32Is c)) (vc : Value bk (Ref c))
    (hs : ∀ o, Steps bk 1 (App Q1 (Ref c) (cmpT o)) (f o)) (hp : CmpDefs bk) :
    Steps bk (cmpC 32 v w + 3) (App Q1 (App Q1 (Ref k) (u32 v)) (u32 w)) (f (cmpV 32 v w)) :=
  steps_eq (step_call (xs := [(Q1, _), (Q1, _)]) h (.cons (fun _ => value_u32) (.cons (fun _ => value_u32) .nil))
    (u := App Q1 (Ref c) (App Q1 (App Q1 (Ref "U32.cmp") (u32 v)) (u32 w)))
    (by simp [walk, takes, bindsAt, Quan.live, Term.sub, spine, Env.sub, data_u32])
    (arg vc rfl (u32_cmp_steps hp) (hs _))) (by omega) rfl

theorem not_steps (h : Has bk "Bool.not" «opsDefs.Bool.not».v) :
    Steps bk 1 (App Q1 (Ref "Bool.not") (Form.bool b)) (Form.bool !b) := by
  cases b <;>
  exact step_call (xs := [(Q1, _)]) h (.cons (fun _ => value_bool) .nil)
    (by simp [walk, «opsDefs.Bool.not», Form.bool, ctor, takes, bindsAt, Quan.live, Quan.fld, Term.sub,
      spine]) .refl

-- the U32 test of is_ne
abbrev u32IsNe : Term :=
  Lam Q1 (Lam Q1 (App Q1 (Ref "Bool.not") (App Q1 (Ref "Cmp.is_eq")
    (App Q1 (App Q1 (Ref "U32.cmp") (Var 1)) (Var 0)))))

theorem u32_is_ne_steps (h : Has bk "U32.is_ne" u32IsNe) (hc : Has bk "Cmp.is_eq" «opsDefs.Cmp.is_eq».v)
    (hn : Has bk "Bool.not" «opsDefs.Bool.not».v) (hp : CmpDefs bk) :
    Steps bk (cmpC 32 v w + 4) (App Q1 (App Q1 (Ref "U32.is_ne") (u32 v)) (u32 w))
      (Form.bool (cmpV 32 v w != .eq)) :=
  steps_eq (step_call (xs := [(Q1, _), (Q1, _)]) h (.cons (fun _ => value_u32) (.cons (fun _ => value_u32) .nil))
    (u := App Q1 (Ref "Bool.not") (App Q1 (Ref "Cmp.is_eq") (App Q1 (App Q1 (Ref "U32.cmp") (u32 v)) (u32 w))))
    (by simp [walk, takes, bindsAt, Quan.live, Term.sub, spine, Env.sub, data_u32])
    (arg (value_ref hn rfl) rfl (arg (value_ref hc rfl) rfl (u32_cmp_steps hp) (is_eq_steps hc))
      (not_steps (b := cmpV 32 v w == .eq) hn))) (by omega) rfl

-- a def whose term is the U32 v steps once to it
theorem lit_steps (h : Has bk k (u32 v)) : Steps bk 1 (Ref k) (u32 v) := by
  refine step_call (xs := []) h .nil ?_ .refl
  rw [walk_done rfl]
  simp [spine, sub_u32]

theorem lit0_eq : «opsDefs.U32.lit0».v = u32 0 := rfl

theorem u32_is_zero_steps (h : Has bk "U32.is_zero" «opsDefs.U32.is_zero».v)
    (he : Has bk "U32.is_eq" (u32Is "Cmp.is_eq")) (hc : Has bk "Cmp.is_eq" «opsDefs.Cmp.is_eq».v)
    (hl : Has bk "U32.lit0" «opsDefs.U32.lit0».v) (hp : CmpDefs bk) :
    Steps bk (cmpC 32 v 0 + 5) (App Q1 (Ref "U32.is_zero") (u32 v)) (Form.bool (cmpV 32 v 0 == .eq)) := by
  rw [lit0_eq] at hl
  have vf : Value bk (App Q1 (Ref "U32.is_eq") (u32 v)) :=
    part (xs := [(Q1, _)]) he (.cons (fun _ => value_u32) .nil)
      (by simp [walk, takes, bindsAt, Quan.live, data_u32])
  exact steps_eq (step_call (xs := [(Q1, _)]) h (.cons (fun _ => value_u32) .nil)
    (u := App Q1 (App Q1 (Ref "U32.is_eq") (u32 v)) (Ref "U32.lit0"))
    (by simp [walk, «opsDefs.U32.is_zero», takes, bindsAt, Quan.live, Term.sub, spine, Env.sub, data_u32])
    (arg vf rfl (lit_steps hl) (u32_is_steps he (value_ref hc rfl) (fun _ => is_eq_steps hc) hp)))
    (by omega) rfl

-- Values
-- ------

theorem compare_two (ha : a < 2) (hb : b < 2) :
    compare (a + 2 * A) (b + 2 * B) = finV (compare A B) a b := by
  unfold finV
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  cases h : compare A B
  · rw [Nat.compare_eq_lt] at h ⊢; omega
  · rw [Nat.compare_eq_eq] at h; subst h
    cases h' : compare a b
    · rw [Nat.compare_eq_lt] at h' ⊢; omega
    · rw [Nat.compare_eq_eq] at h' ⊢; omega
    · rw [Nat.compare_eq_gt] at h' ⊢; omega
  · rw [Nat.compare_eq_gt] at h ⊢; omega

-- Word.cmp compares the values of the words
theorem cmpV_eq : cmpV n v w = compare (v % 2 ^ n) (w % 2 ^ n) := by
  induction n generalizing v w with
  | zero => simp [cmpV, Nat.mod_one]
  | succ n ih =>
    rw [cmpV, ih, Nat.pow_succ', Nat.mod_mul, Nat.mod_mul,
      compare_two (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))]
    simp [finV, Nat.mod_mod]

theorem xor_eq_zero (h : a ^^^ b = 0) : a = b :=
  Nat.eq_of_testBit_eq fun i => by
    have := congrArg (Nat.testBit · i) h
    simp only [Nat.testBit_xor, Nat.zero_testBit] at this
    cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

-- the steps of Word.cmp: 1, then 2 per bit, and 1 more per bit above the
-- top bit where the words differ
def cmpE (n v w : Nat) : Nat := if v = w then n else n - Nat.log2 (v ^^^ w)

theorem cmpC_eq (hv : v < 2 ^ n) (hw : w < 2 ^ n) : cmpC n v w = 1 + 2 * n + cmpE n v w := by
  induction n generalizing v w with
  | zero => simp [cmpC, cmpE]
  | succ n ih =>
    have hv2 : v / 2 < 2 ^ n := by rw [Nat.pow_succ] at hv; omega
    have hw2 : w / 2 < 2 ^ n := by rw [Nat.pow_succ] at hw; omega
    rw [cmpC, ih hv2 hw2, cmpV_eq, Nat.mod_eq_of_lt hv2, Nat.mod_eq_of_lt hw2]
    have hx : (v ^^^ w) / 2 = v / 2 ^^^ w / 2 := Nat.xor_div_two
    by_cases h2 : v / 2 = w / 2
    · have hc : compare (v / 2) (w / 2) = .eq := Nat.compare_eq_eq.2 h2
      rw [ite_eq_left hc]
      unfold cmpE
      rw [ite_eq_left h2]
      split
      · omega
      · rename_i hne
        have h1 : v ^^^ w = 1 := by
          have : (v ^^^ w) / 2 = 0 := by rw [hx, h2, Nat.xor_self]
          have : v ^^^ w ≠ 0 := fun e => hne (xor_eq_zero e)
          omega
        rw [h1]; simp [Nat.log2_def]; omega
    · have hc : compare (v / 2) (w / 2) ≠ .eq := fun e => h2 (Nat.compare_eq_eq.1 e)
      rw [ite_eq_right hc]
      have hne : v ≠ w := fun e => h2 (by rw [e])
      have hx0 : v / 2 ^^^ w / 2 ≠ 0 := fun e => h2 (xor_eq_zero e)
      have hl : Nat.log2 (v ^^^ w) = Nat.log2 (v / 2 ^^^ w / 2) + 1 := by
        rw [Nat.log2_def, ite_eq_left (by omega), hx]
      unfold cmpE
      rw [ite_eq_right h2, ite_eq_right hne, hl]
      omega

-- U32.cmp's steps and value, at once
def cmpFast (v w : Nat) : Nat × Ordering :=
  (65 + (if v = w then 32 else 32 - Nat.log2 (v ^^^ w)), compare v w)

theorem cmpFast_eq (hv : v < 2 ^ 32) (hw : w < 2 ^ 32) : cmpFast v w = (cmpC 32 v w, cmpV 32 v w) := by
  rw [cmpC_eq hv hw, cmpV_eq, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hw]
  rfl

end Ops
