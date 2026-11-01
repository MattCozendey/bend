import Bootstrap.Ops.Kit
import Bootstrap.Ops.Defs

-- Ops.Logic
-- =========
--
-- The steps of Bool.and, Word.and, U32.and, of Bool.or, Word.or, U32.or, and
-- of Word.inc, U32.inc.

open Quan Term

set_option linter.unusedSimpArgs false

set_option maxRecDepth 4000

namespace Ops

-- And, or
-- -------

-- the bit of Bool.and and of Bool.or
def andB (v w : Nat) : Nat := v % 2 * (w % 2)
def orB (v w : Nat) : Nat := if v % 2 = 1 then 1 else w % 2

theorem andB_lt : andB v w < 2 := by
  unfold andB; rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h] <;> omega

theorem orB_lt : orB v w < 2 := by unfold orB; split <;> omega

-- Word.and and Word.or, bit by bit
def andV : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n + 1, v, w => andB v w + 2 * andV n (v / 2) (w / 2)

def orV : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n + 1, v, w => orB v w + 2 * orV n (v / 2) (w / 2)

theorem bool_and_steps (h : Has bk "Bool.and" «opsDefs.Bool.and».v) :
    Steps bk 1 (App Q1 (App Q1 (Ref "Bool.and") (bit v)) (bit w)) (bit (andB v w)) := by
  rcases Nat.mod_two_eq_zero_or_one v with hv | hv <;>
  exact step_call (xs := [(Q1, _), (Q1, _)]) h (.cons (fun _ => value_bit) (.cons (fun _ => value_bit) .nil))
    (by simp [walk, «opsDefs.Bool.and», andB, hv, ctor, takes, bindsAt, Quan.live, Quan.fld, Term.sub,
      spine, Env.sub]) .refl

theorem bool_or_steps (h : Has bk "Bool.or" «opsDefs.Bool.or».v) :
    Steps bk 1 (App Q1 (App Q1 (Ref "Bool.or") (bit v)) (bit w)) (bit (orB v w)) := by
  rcases Nat.mod_two_eq_zero_or_one v with hv | hv <;>
  exact step_call (xs := [(Q1, _), (Q1, _)]) h (.cons (fun _ => value_bit) (.cons (fun _ => value_bit) .nil))
    (by simp [walk, «opsDefs.Bool.or», orB, hv, ctor, takes, bindsAt, Quan.live, Quan.fld, Term.sub,
      spine, Env.sub]) .refl

-- Word.and and Word.or have the same case tree, with Bool.and or Bool.or for the bits
theorem word_bits_steps {fV : Nat → Nat → Nat → Nat} {fB : Nat → Nat → Nat} {W B : String} {body : Term}
    (h : Has bk W body)
    (w0 : ∀ v w, walk bk body [] [(Q1, Form.nat 0), (Q1, bits 0 v), (Q1, bits 0 w)] =
      some (some (ctor "WNil" [])))
    (w1 : ∀ n v w, walk bk body [] [(Q1, Form.nat (n + 1)), (Q1, bits (n + 1) v), (Q1, bits (n + 1) w)] =
      some (some (ctor "WCon" [App Q1 (App Q1 (Ref B) (bit v)) (bit w),
        App Q1 (App Q1 (App Q1 (Ref W) (Form.nat n)) (bits n (v / 2))) (bits n (w / 2))])))
    (hb : ∀ v w, Steps bk 1 (App Q1 (App Q1 (Ref B) (bit v)) (bit w)) (bit (fB v w)))
    (hlt : ∀ v w, fB v w < 2)
    (e0 : ∀ v w, fV 0 v w = 0) (e1 : ∀ n v w, fV (n + 1) v w = fB v w + 2 * fV n (v / 2) (w / 2)) :
    Steps bk (2 * n + 1) (App Q1 (App Q1 (App Q1 (Ref W) (Form.nat n)) (bits n v)) (bits n w))
      (bits n (fV n v w)) := by
  have vs : ∀ n v w, Values bk [(Q1, Form.nat n), (Q1, bits n v), (Q1, bits n w)] := fun _ _ _ =>
    .cons (fun _ => value_nat) (.cons (fun _ => value_bits) (.cons (fun _ => value_bits) .nil))
  induction n generalizing v w with
  | zero => exact step_call (xs := [(Q1, _), (Q1, _), (Q1, _)]) h (vs _ _ _) (w0 v w) (by rw [e0]; exact .refl)
  | succ n ih =>
    exact steps_eq (step_call (xs := [(Q1, _), (Q1, _), (Q1, _)]) h (vs _ _ _) (w1 n v w)
      (ctor2 (hb v w) value_bit ih)) (by omega) (by rw [e1, bits_cons (hlt v w)])

theorem word_and_steps (h : Has bk "Word.and" «opsDefs.Word.and».v)
    (hb : Has bk "Bool.and" «opsDefs.Bool.and».v) :
    Steps bk (2 * n + 1) (App Q1 (App Q1 (App Q1 (Ref "Word.and") (Form.nat n)) (bits n v)) (bits n w))
      (bits n (andV n v w)) :=
  word_bits_steps (B := "Bool.and") h
    (fun _ _ => by simp [walk, «opsDefs.Word.and», Form.nat, bits, ctor, takes, Quan.live, Quan.fld,
      Term.sub, spine, bindsAt])
    (fun _ _ _ => by simp [walk, «opsDefs.Word.and», nat_succ, bits_succ, ctor, takes, Quan.live,
      Quan.fld, Term.sub, spine, bindsAt, Env.sub, sub_nat, sub_bits])
    (fun _ _ => bool_and_steps hb) (fun _ _ => andB_lt) (fun _ _ => rfl) (fun _ _ _ => rfl)

theorem word_or_steps (h : Has bk "Word.or" «opsDefs.Word.or».v)
    (hb : Has bk "Bool.or" «opsDefs.Bool.or».v) :
    Steps bk (2 * n + 1) (App Q1 (App Q1 (App Q1 (Ref "Word.or") (Form.nat n)) (bits n v)) (bits n w))
      (bits n (orV n v w)) :=
  word_bits_steps (B := "Bool.or") h
    (fun _ _ => by simp [walk, «opsDefs.Word.or», Form.nat, bits, ctor, takes, Quan.live, Quan.fld,
      Term.sub, spine, bindsAt])
    (fun _ _ _ => by simp [walk, «opsDefs.Word.or», nat_succ, bits_succ, ctor, takes, Quan.live,
      Quan.fld, Term.sub, spine, bindsAt, Env.sub, sub_nat, sub_bits])
    (fun _ _ => bool_or_steps hb) (fun _ _ => orB_lt) (fun _ _ => rfl) (fun _ _ _ => rfl)

-- the defs that U32.and reaches
structure AndDefs (bk : Book) : Prop where
  u32 : Has bk "U32.and" «opsDefs.U32.and».v
  word : Has bk "Word.and" «opsDefs.Word.and».v
  bool : Has bk "Bool.and" «opsDefs.Bool.and».v

-- the defs that U32.or reaches
structure OrDefs (bk : Book) : Prop where
  u32 : Has bk "U32.or" «opsDefs.U32.or».v
  word : Has bk "Word.or" «opsDefs.Word.or».v
  bool : Has bk "Bool.or" «opsDefs.Bool.or».v

theorem u32_and_steps (h : AndDefs bk) :
    Steps bk 66 (App Q1 (App Q1 (Ref "U32.and") (u32 v)) (u32 w)) (u32 (andV 32 v w)) :=
  step_call (xs := [(Q1, _), (Q1, _)]) h.u32 (.cons (fun _ => value_u32) (.cons (fun _ => value_u32) .nil))
    (u := ctor "U32" [App Q1 (App Q1 (App Q1 (Ref "Word.and") (Form.nat 32)) (bits 32 v)) (bits 32 w)])
    (by simp [walk, «opsDefs.U32.and», u32, ctor, takes, bindsAt, Quan.live, Quan.fld, Term.sub,
      spine, Env.sub, sub_nat, sub_bits])
    (ctor1 (word_and_steps (n := 32) h.word h.bool))

theorem u32_or_steps (h : OrDefs bk) :
    Steps bk 66 (App Q1 (App Q1 (Ref "U32.or") (u32 v)) (u32 w)) (u32 (orV 32 v w)) :=
  step_call (xs := [(Q1, _), (Q1, _)]) h.u32 (.cons (fun _ => value_u32) (.cons (fun _ => value_u32) .nil))
    (u := ctor "U32" [App Q1 (App Q1 (App Q1 (Ref "Word.or") (Form.nat 32)) (bits 32 v)) (bits 32 w)])
    (by simp [walk, «opsDefs.U32.or», u32, ctor, takes, bindsAt, Quan.live, Quan.fld, Term.sub,
      spine, Env.sub, sub_nat, sub_bits])
    (ctor1 (word_or_steps (n := 32) h.word h.bool))

theorem andV_eq : andV n v w = (v &&& w) % 2 ^ n := by
  induction n generalizing v w with
  | zero => simp [andV, Nat.mod_one]
  | succ n ih =>
    rw [andV, ih, ← Nat.and_div_two, Nat.pow_succ', Nat.mod_mul]
    congr 1
    have h := Nat.and_mod_two_eq_one (a := v) (b := w)
    have hx := Nat.mod_two_eq_zero_or_one (v &&& w)
    unfold andB
    rcases Nat.mod_two_eq_zero_or_one v with hv | hv <;>
    rcases Nat.mod_two_eq_zero_or_one w with hw | hw <;>
    rw [hv, hw] at h ⊢ <;> omega

theorem orV_eq : orV n v w = (v ||| w) % 2 ^ n := by
  induction n generalizing v w with
  | zero => simp [orV, Nat.mod_one]
  | succ n ih =>
    rw [orV, ih, ← Nat.or_div_two, Nat.pow_succ', Nat.mod_mul]
    congr 1
    have h := Nat.or_mod_two_eq_one (a := v) (b := w)
    have hx := Nat.mod_two_eq_zero_or_one (v ||| w)
    unfold orB
    rcases Nat.mod_two_eq_zero_or_one v with hv | hv <;>
    rcases Nat.mod_two_eq_zero_or_one w with hw | hw <;>
    rw [hv, hw] at h ⊢ <;> split <;> omega

-- Inc
-- ---

-- Word.inc n w: w + 1, and its steps
def incV : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, v => if v % 2 = 0 then 1 + 2 * (v / 2) else 0 + 2 * incV n (v / 2)

def incC : Nat → Nat → Nat
  | 0, _ => 1
  | n + 1, v => if v % 2 = 0 then 1 else incC n (v / 2) + 1

theorem word_inc_steps (h : Has bk "Word.inc" «opsDefs.Word.inc».v) :
    Steps bk (incC n v) (App Q1 (App Q1 (Ref "Word.inc") (Form.nat n)) (bits n v)) (bits n (incV n v)) := by
  have vs : ∀ n v, Values bk [(Q1, Form.nat n), (Q1, bits n v)] := fun _ _ =>
    .cons (fun _ => value_nat) (.cons (fun _ => value_bits) .nil)
  induction n generalizing v with
  | zero =>
    exact step_call (xs := [(Q1, _), (Q1, _)]) h (vs _ _)
      (by simp [walk, «opsDefs.Word.inc», Form.nat, bits, ctor, takes, Quan.live, Quan.fld,
        Term.sub, spine, bindsAt]) .refl
  | succ n ih =>
    rcases Nat.mod_two_eq_zero_or_one v with hv | hv
    · refine steps_eq (step_call (xs := [(Q1, _), (Q1, _)]) h (vs _ _)
        (u := ctor "WCon" [bit 1, bits n (v / 2)])
        (by simp [walk, «opsDefs.Word.inc», nat_succ, bits_succ, ctor, takes, Quan.live, Quan.fld,
          Term.sub, spine, bindsAt, Env.sub, sub_nat, sub_bits, hv]) .refl) (by simp [incC, hv]) ?_
      rw [incV, ite_eq_left hv, bits_cons (by omega)]
    · refine steps_eq (step_call (xs := [(Q1, _), (Q1, _)]) h (vs _ _)
        (u := ctor "WCon" [bit 0, App Q1 (App Q1 (Ref "Word.inc") (Form.nat n)) (bits n (v / 2))])
        (by simp [walk, «opsDefs.Word.inc», nat_succ, bits_succ, ctor, takes, Quan.live, Quan.fld,
          Term.sub, spine, bindsAt, Env.sub, sub_nat, sub_bits, hv]) (ctor2v value_bit ih))
        (by simp [incC, hv]) ?_
      rw [incV, ite_eq_right (by omega), bits_cons (by omega)]

-- the defs that U32.inc reaches
structure IncDefs (bk : Book) : Prop where
  u32 : Has bk "U32.inc" «opsDefs.U32.inc».v
  word : Has bk "Word.inc" «opsDefs.Word.inc».v

theorem u32_inc_steps (h : IncDefs bk) :
    Steps bk (incC 32 v + 1) (App Q1 (Ref "U32.inc") (u32 v)) (u32 (incV 32 v)) :=
  step_call (xs := [(Q1, _)]) h.u32 (.cons (fun _ => value_u32) .nil)
    (u := ctor "U32" [App Q1 (App Q1 (Ref "Word.inc") (Form.nat 32)) (bits 32 v)])
    (by simp [walk, «opsDefs.U32.inc», u32, ctor, takes, bindsAt, Quan.live, Quan.fld, Term.sub,
      spine, Env.sub, sub_nat, sub_bits])
    (ctor1 (word_inc_steps h.word))

theorem incV_mod : incV n v % 2 ^ n = (v + 1) % 2 ^ n := by
  induction n generalizing v with
  | zero => simp [Nat.mod_one]
  | succ n ih =>
    rw [incV]
    split
    next hv => rw [show 1 + 2 * (v / 2) = v + 1 by omega]
    next hv =>
      rw [Nat.zero_add, Nat.pow_succ', Nat.mul_mod_mul_left, ih,
        show v + 1 = 2 * (v / 2 + 1) by omega, Nat.mul_mod_mul_left]

-- the U32 of incV 32 v is the U32 of v + 1
theorem u32_incV : u32 (incV 32 v) = u32 ((v + 1) % 2 ^ 32) := by
  rw [u32, ← bits_mod, incV_mod, u32]

-- incC n v sees only the low n bits of v
theorem incC_mod : incC n (v % 2 ^ n) = incC n v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    have h1 : v % 2 ^ (n + 1) % 2 = v % 2 := by
      rw [Nat.pow_succ', Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right 2 _)]
    have h2 : v % 2 ^ (n + 1) / 2 = v / 2 % 2 ^ n := by
      rw [Nat.pow_succ', Nat.mod_mul_right_div_self]
    simp only [incC, h1, h2, ih]

end Ops
