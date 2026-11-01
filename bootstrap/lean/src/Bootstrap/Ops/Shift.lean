import Bootstrap.Ops.Kit
import Bootstrap.Ops.Defs

-- Ops.Shift
-- =========
--
-- The steps of Word.shr.pad, Word.shr, U32.shr, U32.shrn, and of
-- Word.shl.put, Word.shl, U32.shl, U32.shln: each lemma gives the exact
-- number of steps and the value, as functions that follow the def.

open Quan Term

set_option linter.unusedSimpArgs false

set_option maxRecDepth 4000

namespace Ops

-- Right
-- -----

-- Word.shr.pad n w: w, with a False bit on top
def padV : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, v => v % 2 + 2 * padV n (v / 2)

-- Word.shr n w: w without its lowest bit
def shrV : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, v => padV n (v / 2)

def shrC : Nat → Nat
  | 0 => 1
  | n + 1 => n + 2

-- U32.shrn a m: a shifted right m times
def shrnV : Nat → Nat → Nat
  | 0, v => v
  | m + 1, v => shrV 32 (shrnV m v)

theorem pad_steps (h : Has bk "Word.shr.pad" «opsDefs.Word.shr.pad».v) :
    Steps bk (n + 1) (App Q1 (App Q1 (Ref "Word.shr.pad") (Form.nat n)) (bits n v))
      (bits (n + 1) (padV n v)) := by
  induction n generalizing v with
  | zero =>
    refine step_call (xs := [(Q1, _), (Q1, _)]) h (.cons (fun _ => value_nat) (.cons (fun _ => value_bits) .nil))
      (by simp [walk, «opsDefs.Word.shr.pad», Form.nat, bits, padV, ctor, takes, bindsAt, Quan.live,
        Quan.fld, Term.sub, spine, Env.sub]) .refl
  | succ n ih =>
    refine step_call (xs := [(Q1, _), (Q1, _)]) h (.cons (fun _ => value_nat) (.cons (fun _ => value_bits) .nil))
      (u := ctor "WCon" [bit v, App Q1 (App Q1 (Ref "Word.shr.pad") (Form.nat n)) (bits n (v / 2))])
      (by simp [walk, «opsDefs.Word.shr.pad», nat_succ, bits_succ, ctor, takes, bindsAt, Quan.live,
        Quan.fld, Term.sub, spine, Env.sub, sub_nat, sub_bits])
      (steps_eq (ctor2v value_bit ih) rfl (by rw [padV, bits_mod2]))

theorem word_shr_steps (h : Has bk "Word.shr" «opsDefs.Word.shr».v)
    (hp : Has bk "Word.shr.pad" «opsDefs.Word.shr.pad».v) :
    Steps bk (shrC n) (App Q1 (App Q1 (Ref "Word.shr") (Form.nat n)) (bits n v)) (bits n (shrV n v)) := by
  cases n with
  | zero =>
    exact step_call (xs := [(Q1, _), (Q1, _)]) h (.cons (fun _ => value_nat) (.cons (fun _ => value_bits) .nil))
      (by simp [walk, «opsDefs.Word.shr», Form.nat, bits, ctor, takes, bindsAt, Quan.live,
        Quan.fld, Term.sub, spine, Env.sub]) .refl
  | succ n =>
    exact steps_eq (step_call (xs := [(Q1, _), (Q1, _)]) h
      (.cons (fun _ => value_nat) (.cons (fun _ => value_bits) .nil))
      (u := App Q1 (App Q1 (Ref "Word.shr.pad") (Form.nat n)) (bits n (v / 2)))
      (by simp [walk, «opsDefs.Word.shr», nat_succ, bits_succ, ctor, takes, bindsAt, Quan.live,
        Quan.fld, Term.sub, spine, Env.sub, sub_nat, sub_bits])
      (pad_steps hp)) (by simp [shrC]) rfl

-- the defs that U32.shr reaches
structure ShrDefs (bk : Book) : Prop where
  u32 : Has bk "U32.shr" «opsDefs.U32.shr».v
  word : Has bk "Word.shr" «opsDefs.Word.shr».v
  pad : Has bk "Word.shr.pad" «opsDefs.Word.shr.pad».v

theorem u32_shr_steps (h : ShrDefs bk) :
    Steps bk 34 (App Q1 (Ref "U32.shr") (u32 v)) (u32 (shrV 32 v)) :=
  step_call (xs := [(Q1, _)]) h.u32 (.cons (fun _ => value_u32) .nil)
    (u := ctor "U32" [App Q1 (App Q1 (Ref "Word.shr") (Form.nat 32)) (bits 32 v)])
    (by simp [walk, «opsDefs.U32.shr», u32, ctor, takes, bindsAt, Quan.live, Quan.fld, Term.sub,
      spine, Env.sub, sub_nat, sub_bits])
    (ctor1 (word_shr_steps (n := 32) h.word h.pad))

theorem value_ref_shr (h : ShrDefs bk) : Value bk (Ref "U32.shr") :=
  part (xs := []) h.u32 .nil (by simp [walk, «opsDefs.U32.shr», takes])

-- the defs that U32.shrn reaches
structure ShrnDefs (bk : Book) : Prop where
  shrn : Has bk "U32.shrn" «opsDefs.U32.shrn».v
  shr : ShrDefs bk

theorem u32_shrn_steps (h : ShrnDefs bk) :
    Steps bk (1 + 35 * m) (App Q1 (App Q1 (Ref "U32.shrn") (u32 v)) (Form.nat m)) (u32 (shrnV m v)) := by
  induction m with
  | zero =>
    exact step_call (xs := [(Q1, _), (Q1, _)]) h.shrn (.cons (fun _ => value_u32) (.cons (fun _ => value_nat) .nil))
      (by simp [walk, «opsDefs.U32.shrn», Form.nat, ctor, takes, bindsAt, Quan.live, data_u32,
        Quan.fld, Term.sub, spine, Env.sub, shrnV]) .refl
  | succ m ih =>
    exact steps_eq (step_call (xs := [(Q1, _), (Q1, _)]) h.shrn
      (.cons (fun _ => value_u32) (.cons (fun _ => value_nat) .nil))
      (u := App Q1 (Ref "U32.shr") (App Q1 (App Q1 (Ref "U32.shrn") (u32 v)) (Form.nat m)))
      (by simp [walk, «opsDefs.U32.shrn», nat_succ, ctor, takes, bindsAt, Quan.live, data_u32,
        Quan.fld, Term.sub, spine, Env.sub, sub_nat])
      (arg (value_ref_shr h.shr) rfl ih (u32_shr_steps h.shr))) (by omega) (by simp [shrnV])

-- Left
-- ----

-- Word.shl.put n c w: the bit c, then w without its top bit
def putV : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n + 1, c, v => c % 2 + 2 * putV n v (v / 2)

-- Word.shl n w: a False bit, then w without its top bit
def shlV : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, v => 2 * putV n v (v / 2)

-- U32.shln a m: a shifted left m times
def shlnV : Nat → Nat → Nat
  | 0, v => v
  | m + 1, v => shlV 32 (shlnV m v)

theorem put_steps (h : Has bk "Word.shl.put" «opsDefs.Word.shl.put».v) :
    Steps bk (n + 1) (App Q1 (App Q1 (App Q1 (Ref "Word.shl.put") (Form.nat n)) (bit c)) (bits n v))
      (bits n (putV n c v)) := by
  induction n generalizing c v with
  | zero =>
    refine step_call (xs := [(Q1, _), (Q1, _), (Q1, _)]) h
      (.cons (fun _ => value_nat) (.cons (fun _ => value_bit) (.cons (fun _ => value_bits) .nil)))
      (by simp [walk, «opsDefs.Word.shl.put», Form.nat, bits, putV, ctor, takes, bindsAt, Quan.live,
        Quan.fld, Term.sub, spine, Env.sub]) .refl
  | succ n ih =>
    refine step_call (xs := [(Q1, _), (Q1, _), (Q1, _)]) h
      (.cons (fun _ => value_nat) (.cons (fun _ => value_bit) (.cons (fun _ => value_bits) .nil)))
      (u := ctor "WCon" [bit c, App Q1 (App Q1 (App Q1 (Ref "Word.shl.put") (Form.nat n)) (bit v))
        (bits n (v / 2))])
      (by simp [walk, «opsDefs.Word.shl.put», nat_succ, bits_succ, ctor, takes, bindsAt, Quan.live,
        Quan.fld, Term.sub, spine, Env.sub, sub_nat, sub_bits])
      (steps_eq (ctor2v value_bit ih) rfl (by rw [putV, bits_mod2]))

theorem word_shl_steps (h : Has bk "Word.shl" «opsDefs.Word.shl».v)
    (hp : Has bk "Word.shl.put" «opsDefs.Word.shl.put».v) :
    Steps bk (shrC n) (App Q1 (App Q1 (Ref "Word.shl") (Form.nat n)) (bits n v)) (bits n (shlV n v)) := by
  cases n with
  | zero =>
    exact step_call (xs := [(Q1, _), (Q1, _)]) h (.cons (fun _ => value_nat) (.cons (fun _ => value_bits) .nil))
      (by simp [walk, «opsDefs.Word.shl», Form.nat, bits, ctor, takes, bindsAt, Quan.live,
        Quan.fld, Term.sub, spine, Env.sub]) .refl
  | succ n =>
    exact steps_eq (step_call (xs := [(Q1, _), (Q1, _)]) h
      (.cons (fun _ => value_nat) (.cons (fun _ => value_bits) .nil))
      (u := ctor "WCon" [bit 0, App Q1 (App Q1 (App Q1 (Ref "Word.shl.put") (Form.nat n)) (bit v))
        (bits n (v / 2))])
      (by simp [walk, «opsDefs.Word.shl», nat_succ, bits_succ, ctor, takes, bindsAt, Quan.live,
        Quan.fld, Term.sub, spine, Env.sub, sub_nat, sub_bits])
      (ctor2v value_bit (put_steps hp))) (by simp [shrC])
      (by rw [shlV, ← bits_mod2 (v := 0)]; simp)

-- the defs that U32.shl reaches
structure ShlDefs (bk : Book) : Prop where
  u32 : Has bk "U32.shl" «opsDefs.U32.shl».v
  word : Has bk "Word.shl" «opsDefs.Word.shl».v
  put : Has bk "Word.shl.put" «opsDefs.Word.shl.put».v

theorem u32_shl_steps (h : ShlDefs bk) :
    Steps bk 34 (App Q1 (Ref "U32.shl") (u32 v)) (u32 (shlV 32 v)) :=
  step_call (xs := [(Q1, _)]) h.u32 (.cons (fun _ => value_u32) .nil)
    (u := ctor "U32" [App Q1 (App Q1 (Ref "Word.shl") (Form.nat 32)) (bits 32 v)])
    (by simp [walk, «opsDefs.U32.shl», u32, ctor, takes, bindsAt, Quan.live, Quan.fld, Term.sub,
      spine, Env.sub, sub_nat, sub_bits])
    (ctor1 (word_shl_steps (n := 32) h.word h.put))

theorem value_ref_shl (h : ShlDefs bk) : Value bk (Ref "U32.shl") :=
  part (xs := []) h.u32 .nil (by simp [walk, «opsDefs.U32.shl», takes])

-- the defs that U32.shln reaches
structure ShlnDefs (bk : Book) : Prop where
  shln : Has bk "U32.shln" «opsDefs.U32.shln».v
  shl : ShlDefs bk

theorem u32_shln_steps (h : ShlnDefs bk) :
    Steps bk (1 + 35 * m) (App Q1 (App Q1 (Ref "U32.shln") (u32 v)) (Form.nat m)) (u32 (shlnV m v)) := by
  induction m with
  | zero =>
    exact step_call (xs := [(Q1, _), (Q1, _)]) h.shln (.cons (fun _ => value_u32) (.cons (fun _ => value_nat) .nil))
      (by simp [walk, «opsDefs.U32.shln», Form.nat, ctor, takes, bindsAt, Quan.live, data_u32,
        Quan.fld, Term.sub, spine, Env.sub, shlnV]) .refl
  | succ m ih =>
    exact steps_eq (step_call (xs := [(Q1, _), (Q1, _)]) h.shln
      (.cons (fun _ => value_u32) (.cons (fun _ => value_nat) .nil))
      (u := App Q1 (Ref "U32.shl") (App Q1 (App Q1 (Ref "U32.shln") (u32 v)) (Form.nat m)))
      (by simp [walk, «opsDefs.U32.shln», nat_succ, ctor, takes, bindsAt, Quan.live, data_u32,
        Quan.fld, Term.sub, spine, Env.sub, sub_nat])
      (arg (value_ref_shl h.shl) rfl ih (u32_shl_steps h.shl))) (by omega) (by simp [shlnV])

-- Values
-- ------

theorem two32 : (2 : Nat) ^ 32 = 4294967296 := rfl

theorem padV_eq : padV n v = v % 2 ^ n := by
  induction n generalizing v with
  | zero => simp [padV, Nat.mod_one]
  | succ n ih => rw [padV, ih, Nat.pow_succ', Nat.mod_mul]

theorem shrV_32 (hv : v < 2 ^ 32) : shrV 32 v = v / 2 := by
  rw [shrV, padV_eq]
  rw [two32] at hv
  exact Nat.mod_eq_of_lt (by rw [show (2 : Nat) ^ 31 = 2147483648 from rfl]; omega)

theorem shrnV_eq (hv : v < 2 ^ 32) : shrnV m v = v >>> m := by
  rw [Nat.shiftRight_eq_div_pow]
  induction m with
  | zero => simp [shrnV]
  | succ m ih =>
    rw [shrnV, ih, shrV_32 (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hv), Nat.div_div_eq_div_mul,
      Nat.pow_succ]

theorem putV_eq : putV n c v = (c % 2 + 2 * v) % 2 ^ n := by
  induction n generalizing c v with
  | zero => simp [putV, Nat.mod_one]
  | succ n ih =>
    rw [putV, ih, show v % 2 + 2 * (v / 2) = v by omega, Nat.pow_succ', Nat.mod_mul,
      show (c % 2 + 2 * v) % 2 = c % 2 by omega, show (c % 2 + 2 * v) / 2 = v by omega]

theorem shlV_eq : shlV n v = 2 * v % 2 ^ n := by
  cases n with
  | zero => simp [shlV, Nat.mod_one]
  | succ n =>
    rw [shlV, putV_eq, show v % 2 + 2 * (v / 2) = v by omega, Nat.pow_succ', Nat.mul_mod_mul_left]

theorem shlnV_eq (hv : v < 2 ^ 32) : shlnV m v = v * 2 ^ m % 2 ^ 32 := by
  induction m with
  | zero => simp [shlnV, Nat.mod_eq_of_lt hv]
  | succ m ih =>
    rw [shlnV, ih, shlV_eq, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    congr 1
    rw [Nat.pow_succ', Nat.mul_left_comm]

-- U32.shln's value, computed: no power beyond 2 ^ 32
theorem shln_fast (hv : v < 2 ^ 32) :
    shlnV m v = if m < 32 then (v <<< m) % 4294967296 else 0 := by
  rw [shlnV_eq hv]
  split
  next => rw [Nat.shiftLeft_eq, two32]
  next h =>
    rw [show m = 32 + (m - 32) by omega, Nat.pow_add, ← Nat.mul_assoc, Nat.mul_comm v,
      Nat.mul_assoc, Nat.mul_mod_right]

end Ops
