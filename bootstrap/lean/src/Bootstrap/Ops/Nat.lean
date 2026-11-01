import Bootstrap.Ops.Shift
import Bootstrap.Ops.Logic
import Bootstrap.Ops.Cmp

-- Ops.Nat
-- =======
--
-- The steps of Nat.double, Word.to_nat, U32.to_nat, and of U32.from_nat.

open Quan Term

set_option linter.unusedSimpArgs false

set_option maxRecDepth 4000

namespace Ops

theorem double_steps (h : Has bk "Nat.double" «opsDefs.Nat.double».v) :
    Steps bk (m + 1) (App Q1 (Ref "Nat.double") (Form.nat m)) (Form.nat (2 * m)) := by
  induction m with
  | zero =>
    exact step_call (xs := [(Q1, _)]) h (.cons (fun _ => value_nat) .nil)
      (by simp [walk, «opsDefs.Nat.double», Form.nat, ctor, takes, Quan.live, Quan.fld, Term.sub, spine]) .refl
  | succ m ih =>
    exact steps_eq (step_call (xs := [(Q1, _)]) h (.cons (fun _ => value_nat) .nil)
      (u := ctor "Succ" [ctor "Succ" [App Q1 (Ref "Nat.double") (Form.nat m)]])
      (by simp [walk, «opsDefs.Nat.double», nat_succ, ctor, takes, Quan.live, Quan.fld, Term.sub, spine,
        bindsAt, Env.sub, sub_nat])
      (ctor1 (ctor1 ih))) rfl (by rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega]; rfl)

-- the steps of Word.to_nat n w
def tnC : Nat → Nat → Nat
  | 0, _ => 1
  | n + 1, v => tnC n (v / 2) + (v / 2 % 2 ^ n + 1) + 1

theorem value_double (h : Has bk "Nat.double" «opsDefs.Nat.double».v) : Value bk (Ref "Nat.double") :=
  value_ref h rfl

theorem word_to_nat_steps (h : Has bk "Word.to_nat" «opsDefs.Word.to_nat».v)
    (hd : Has bk "Nat.double" «opsDefs.Nat.double».v) :
    Steps bk (tnC n v) (App Q1 (App Q1 (Ref "Word.to_nat") (Form.nat n)) (bits n v)) (Form.nat (padV n v)) := by
  have vs : ∀ n v, Values bk [(Q1, Form.nat n), (Q1, bits n v)] := fun _ _ =>
    .cons (fun _ => value_nat) (.cons (fun _ => value_bits) .nil)
  induction n generalizing v with
  | zero =>
    exact step_call (xs := [(Q1, _), (Q1, _)]) h (vs _ _)
      (by simp [walk, «opsDefs.Word.to_nat», Form.nat, bits, padV, ctor, takes, Quan.live, Quan.fld,
        Term.sub, spine, bindsAt]) .refl
  | succ n ih =>
    have r := arg (value_double hd) rfl (ih (v := v / 2)) (double_steps hd)
    rw [padV_eq] at r
    rcases Nat.mod_two_eq_zero_or_one v with hv | hv
    · refine steps_eq (step_call (xs := [(Q1, _), (Q1, _)]) h (vs _ _)
        (u := App Q1 (Ref "Nat.double") (App Q1 (App Q1 (Ref "Word.to_nat") (Form.nat n)) (bits n (v / 2))))
        (by simp [walk, «opsDefs.Word.to_nat», nat_succ, bits_succ, ctor, takes, Quan.live, Quan.fld,
          Term.sub, spine, bindsAt, Env.sub, sub_nat, sub_bits, hv, data_nat']) r) (by simp [tnC]) ?_
      rw [padV, ← padV_eq, hv, Nat.zero_add]
    · refine steps_eq (step_call (xs := [(Q1, _), (Q1, _)]) h (vs _ _)
        (u := ctor "Succ" [App Q1 (Ref "Nat.double")
          (App Q1 (App Q1 (Ref "Word.to_nat") (Form.nat n)) (bits n (v / 2)))])
        (by simp [walk, «opsDefs.Word.to_nat», nat_succ, bits_succ, ctor, takes, Quan.live, Quan.fld,
          Term.sub, spine, bindsAt, Env.sub, sub_nat, sub_bits, hv, data_nat']) (ctor1 r)) (by simp [tnC]) ?_
      rw [padV, ← padV_eq, hv, Nat.add_comm, nat_succ]

-- the defs that U32.to_nat reaches
structure ToNatDefs (bk : Book) : Prop where
  u32 : Has bk "U32.to_nat" «opsDefs.U32.to_nat».v
  word : Has bk "Word.to_nat" «opsDefs.Word.to_nat».v
  double : Has bk "Nat.double" «opsDefs.Nat.double».v

theorem u32_to_nat_steps (h : ToNatDefs bk) :
    Steps bk (tnC 32 v + 1) (App Q1 (Ref "U32.to_nat") (u32 v)) (Form.nat (padV 32 v)) :=
  step_call (xs := [(Q1, _)]) h.u32 (.cons (fun _ => value_u32) .nil)
    (u := App Q1 (App Q1 (Ref "Word.to_nat") (Form.nat 32)) (bits 32 v))
    (by simp [walk, «opsDefs.U32.to_nat», u32, ctor, takes, bindsAt, Quan.live, Quan.fld, Term.sub,
      spine, Env.sub, sub_nat, Term.unspine])
    (word_to_nat_steps h.word h.double)

-- the steps of U32.to_nat, in one pass: 2 + v / 2 per bit of v, as v < 2 ^ n
def tnF : Nat → Nat → Nat → Nat
  | 0, _, acc => acc + 1
  | n + 1, v, acc => tnF n (v / 2) (acc + v / 2 + 2)

theorem tnF_eq (hv : v < 2 ^ n) : tnF n v acc = acc + tnC n v := by
  induction n generalizing v acc with
  | zero => simp [tnF, tnC]
  | succ n ih =>
    have h2 : v / 2 < 2 ^ n := by rw [Nat.pow_succ] at hv; omega
    rw [tnF, ih h2, tnC, Nat.mod_eq_of_lt h2]
    omega

-- the form of the nat m + k, from the form of m: a loop, for a large k
def succL : Term := Lab "Succ"

def natUp : Nat → Term → Term
  | 0, t => t
  | k + 1, t => natUp k (Tup Q1 succL (Tup Q1 t unitL))

theorem natUp_eq : natUp k (Form.nat m) = Form.nat (m + k) := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
    rw [natUp, show Tup Q1 succL (Tup Q1 (Form.nat m) unitL) = Form.nat (m + 1) by
      simp [succL, unitL, labUnit_eq, Form.nat, ctor], ih, Nat.add_right_comm, Nat.add_assoc]

-- From nat
-- ---------

-- U32.from_nat m: its U32, and its steps
def fnV : Nat → Nat
  | 0 => 0
  | m + 1 => incV 32 (fnV m)

def fnC : Nat → Nat
  | 0 => 2
  | m + 1 => fnC m + (incC 32 (fnV m) + 1) + 1

-- the defs that U32.from_nat reaches
structure FromNatDefs (bk : Book) : Prop where
  from_nat : Has bk "U32.from_nat" «opsDefs.U32.from_nat».v
  lit0 : Has bk "U32.lit0" «opsDefs.U32.lit0».v
  inc : IncDefs bk

theorem u32_from_nat_steps (h : FromNatDefs bk) :
    Steps bk (fnC m) (App Q1 (Ref "U32.from_nat") (Form.nat m)) (u32 (fnV m)) := by
  induction m with
  | zero =>
    have hl := h.lit0
    rw [lit0_eq] at hl
    exact step_call (xs := [(Q1, _)]) h.from_nat (.cons (fun _ => value_nat) .nil)
      (u := Ref "U32.lit0")
      (by simp [walk, «opsDefs.U32.from_nat», Form.nat, ctor, takes, Quan.live, Quan.fld, Term.sub,
        spine, node]) (lit_steps hl)
  | succ m ih =>
    exact step_call (xs := [(Q1, _)]) h.from_nat (.cons (fun _ => value_nat) .nil)
      (u := App Q1 (Ref "U32.inc") (App Q1 (Ref "U32.from_nat") (Form.nat m)))
      (by simp [walk, «opsDefs.U32.from_nat», nat_succ, ctor, takes, Quan.live, Quan.fld, Term.sub,
        spine, bindsAt, Env.sub, sub_nat])
      (arg (value_ref h.inc.u32 rfl) rfl ih (u32_inc_steps h.inc))

theorem fnV_mod : fnV m % 2 ^ 32 = m % 2 ^ 32 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [fnV, incV_mod, Nat.add_mod, ih, ← Nat.add_mod]

theorem u32_fnV : u32 (fnV m) = u32 (m % 2 ^ 32) := by rw [u32, ← bits_mod, fnV_mod, u32]

-- the steps of U32.from_nat, in a loop, for a large m
def fnF : Nat → Nat → Nat
  | 0, acc => acc + 2
  | m + 1, acc => fnF m (acc + incC 32 (m % 4294967296) + 2)

theorem fnF_eq : fnF m acc = acc + fnC m := by
  induction m generalizing acc with
  | zero => rfl
  | succ m ih =>
    rw [fnF, ih, fnC, ← incC_mod (v := fnV m), fnV_mod]
    simp only [show (2 : Nat) ^ 32 = 4294967296 from rfl]
    omega

end Ops
