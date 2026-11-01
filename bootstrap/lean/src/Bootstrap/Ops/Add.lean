import Bootstrap.Ops.Cmp

-- Ops.Add
-- =======
--
-- The steps of Bool.xor, Bool.full_add, Word.adc.group (Base's Word.adc and
-- Word.adc.con, in one def), Word.add, Word.sub, U32.add, U32.sub.

open Quan Term

set_option linter.unusedSimpArgs false

set_option maxRecDepth 4000

namespace Ops

-- Bits
-- ----

theorem bool_bit : Form.bool b = bit (if b then 1 else 0) := by cases b <;> rfl

theorem xor_steps (h : Has bk "Bool.xor" «opsDefs.Bool.xor».v) (hn : Has bk "Bool.not" «opsDefs.Bool.not».v) :
    Steps bk (if y then 2 else 1) (App Q1 (App Q1 (Ref "Bool.xor") (Form.bool y)) (Form.bool z))
      (Form.bool (y ^^ z)) := by
  have vs : Values bk [(Q1, Form.bool y), (Q1, Form.bool z)] :=
    .cons (fun _ => value_bool) (.cons (fun _ => value_bool) .nil)
  cases y
  · exact step_call (xs := [(Q1, _), (Q1, _)]) h vs
      (by simp [walk, «opsDefs.Bool.xor», Form.bool, ctor, takes, bindsAt, Quan.live, Quan.fld, Term.sub,
        spine, Env.sub]) .refl
  · exact step_call (xs := [(Q1, _), (Q1, _)]) h vs (u := App Q1 (Ref "Bool.not") (Form.bool z))
      (by simp [walk, «opsDefs.Bool.xor», Form.bool, ctor, takes, bindsAt, Quan.live, Quan.fld, Term.sub,
        spine, Env.sub]) (by simpa using not_steps (b := z) hn)

theorem and_steps (h : Has bk "Bool.and" «opsDefs.Bool.and».v) :
    Steps bk 1 (App Q1 (App Q1 (Ref "Bool.and") (Form.bool y)) (Form.bool z)) (Form.bool (y && z)) := by
  cases y <;>
  exact step_call (xs := [(Q1, _), (Q1, _)]) h (.cons (fun _ => value_bool) (.cons (fun _ => value_bool) .nil))
    (by simp [walk, «opsDefs.Bool.and», Form.bool, ctor, takes, bindsAt, Quan.live, Quan.fld, Term.sub,
      spine, Env.sub]) .refl

theorem or_steps (h : Has bk "Bool.or" «opsDefs.Bool.or».v) :
    Steps bk 1 (App Q1 (App Q1 (Ref "Bool.or") (Form.bool y)) (Form.bool z)) (Form.bool (y || z)) := by
  cases y <;>
  exact step_call (xs := [(Q1, _), (Q1, _)]) h (.cons (fun _ => value_bool) (.cons (fun _ => value_bool) .nil))
    (by simp [walk, «opsDefs.Bool.or», Form.bool, ctor, takes, bindsAt, Quan.live, Quan.fld, Term.sub,
      spine, Env.sub]) .refl

-- the sum and the carry of Bool.full_add x y z
def sB (x y z : Bool) : Bool := if x then !(y ^^ z) else y ^^ z
def kB (x y z : Bool) : Bool := if x then y || z else y && z

-- the defs that Bool.full_add reaches
structure FullAddDefs (bk : Book) : Prop where
  fa : Has bk "Bool.full_add" «opsDefs.Bool.full_add».v
  xor : Has bk "Bool.xor" «opsDefs.Bool.xor».v
  not : Has bk "Bool.not" «opsDefs.Bool.not».v
  and : Has bk "Bool.and" «opsDefs.Bool.and».v
  or : Has bk "Bool.or" «opsDefs.Bool.or».v

def faC (x y : Bool) : Nat := 3 + (if x then 1 else 0) + (if y then 1 else 0)

-- Bool.full_add, with a second argument that runs first
theorem full_add_steps (h : FullAddDefs bk) (hy : Steps bk m Y (Form.bool y)) :
    Steps bk (m + faC x y) (App Q2 (App Q2 (App Q1 (Ref "Bool.full_add") (Form.bool x)) Y) (Form.bool z))
      (ctor "Tuple" [Form.bool (sB x y z), Form.bool (kB x y z)]) := by
  have v1 : Value bk (App Q1 (Ref "Bool.full_add") (Form.bool x)) :=
    part (xs := [(Q1, _)]) h.fa (.cons (fun _ => value_bool) .nil)
      (by cases x <;> simp [walk, «opsDefs.Bool.full_add», Form.bool, ctor, takes, Quan.live, Quan.fld])
  have vs : Values bk [(Q1, Form.bool x), (Q2, Form.bool y), (Q2, Form.bool z)] :=
    .cons (fun _ => value_bool) (.cons (fun _ => value_bool) (.cons (fun _ => value_bool) .nil))
  have hc : Steps bk (faC x y)
      (App Q2 (App Q2 (App Q1 (Ref "Bool.full_add") (Form.bool x)) (Form.bool y)) (Form.bool z))
      (ctor "Tuple" [Form.bool (sB x y z), Form.bool (kB x y z)]) := by
    cases x
    · refine steps_eq (step_call (xs := [(Q1, _), (Q2, _), (Q2, _)]) h.fa vs
        (u := ctor "Tuple" [App Q1 (App Q1 (Ref "Bool.xor") (Form.bool y)) (Form.bool z),
          App Q1 (App Q1 (Ref "Bool.and") (Form.bool y)) (Form.bool z)])
        (by simp [walk, «opsDefs.Bool.full_add», Form.bool, ctor, takes, bindsAt, Quan.live, Quan.fld,
          Term.sub, spine, Env.sub, data])
        (ctor2 (xor_steps h.xor h.not) value_bool (and_steps h.and))) ?_ rfl
      cases y <;> simp [faC]
    · refine steps_eq (step_call (xs := [(Q1, _), (Q2, _), (Q2, _)]) h.fa vs
        (u := ctor "Tuple" [App Q1 (Ref "Bool.not") (App Q1 (App Q1 (Ref "Bool.xor") (Form.bool y)) (Form.bool z)),
          App Q1 (App Q1 (Ref "Bool.or") (Form.bool y)) (Form.bool z)])
        (by simp [walk, «opsDefs.Bool.full_add», Form.bool, ctor, takes, bindsAt, Quan.live, Quan.fld,
          Term.sub, spine, Env.sub, data])
        (ctor2 (arg (value_ref h.not rfl) rfl (xor_steps h.xor h.not) (not_steps h.not)) value_bool
          (or_steps h.or))) ?_ rfl
      cases y <;> simp [faC]
  exact steps_eq (fn (arg v1 rfl hy .refl) hc) (by omega) rfl

-- Word.adc
-- --------

-- the tags of Word.adc.group
def adcT : Term := ctor "Word.adc" []
def conT : Term := ctor "Word.adc.con" [ctor "Word.adc" []]

theorem value_conT : Value bk conT :=
  value_ctor fun f hf => by simp at hf; subst hf; exact value_ctor nofun

theorem value_pair : Value bk (ctor "Tuple" [Form.bool s, Form.bool k]) :=
  value_ctor fun f hf => by simp at hf; rcases hf with rfl | rfl <;> exact value_bool

-- Word.adc n a b f c: a + b + c, with b's bits flipped when f
def adcV : Nat → Nat → Nat → Bool → Bool → Nat
  | 0, _, _, _, _ => 0
  | n + 1, a, b, f, c =>
    (if sB (a % 2 = 1) ((b % 2 = 1) ^^ f) c then 1 else 0) +
      2 * adcV n (a / 2) (b / 2) f (kB (a % 2 = 1) ((b % 2 = 1) ^^ f) c)

def adcC : Nat → Nat → Nat → Bool → Bool → Nat
  | 0, _, _, _, _ => 1
  | n + 1, a, b, f, c =>
    adcC n (a / 2) (b / 2) f (kB (a % 2 = 1) ((b % 2 = 1) ^^ f) c) +
      (4 + (if f then 1 else 0) + faC (a % 2 = 1) ((b % 2 = 1) ^^ f))

-- the defs that Word.adc.group reaches
structure AdcDefs (bk : Book) : Prop where
  group : Has bk "Word.adc.group" «opsDefs.Word.adc.group».v
  fa : FullAddDefs bk

-- a call of Word.adc.group, on its six arguments
abbrev grp (n : Nat) (a b : Term) (f : Bool) (tag c : Term) : Term :=
  App Q1 (App Q1 (App Q1 (App Q1 (App Q1 (App Q1 (Ref "Word.adc.group") (Form.nat n)) a) b) (Form.bool f)) tag) c

theorem adc_steps (h : AdcDefs bk) :
    Steps bk (adcC n a b f c) (grp n (bits n a) (bits n b) f adcT (Form.bool c)) (bits n (adcV n a b f c)) := by
  induction n generalizing a b c with
  | zero =>
    exact step_call (xs := [(Q1, _), (Q1, _), (Q1, _), (Q1, _), (Q1, _), (Q1, _)]) h.group
      (.cons (fun _ => value_nat) (.cons (fun _ => value_bits) (.cons (fun _ => value_bits)
        (.cons (fun _ => value_bool) (.cons (fun _ => value_ctor nofun) (.cons (fun _ => value_bool) .nil))))))
      (by simp [walk, «opsDefs.Word.adc.group», adcT, Form.nat, bits, ctor, takes, Quan.live, Quan.fld,
        Term.sub, spine, bindsAt, Env.sub, Term.unspine, node]) .refl
  | succ n ih =>
    -- the call on Word.adc.con's tag: the bit of the sum, then Word.adc on the carry
    have vcon : Value bk (App Q1 (App Q1 (App Q1 (App Q1 (App Q1 (Ref "Word.adc.group") (Form.nat n))
        (bits n (a / 2))) (bits n (b / 2))) (Form.bool f)) conT) :=
      part (xs := [(Q1, _), (Q1, _), (Q1, _), (Q1, _), (Q1, _)]) h.group
        (.cons (fun _ => value_nat) (.cons (fun _ => value_bits) (.cons (fun _ => value_bits)
          (.cons (fun _ => value_bool) (.cons (fun _ => value_conT) .nil)))))
        (by simp [walk, «opsDefs.Word.adc.group», conT, ctor, takes, Quan.live, Quan.fld, bindsAt,
          Env.sub, Term.unspine, node])
    have con : ∀ s k, Steps bk (adcC n (a / 2) (b / 2) f k + 2)
        (grp n (bits n (a / 2)) (bits n (b / 2)) f conT (ctor "Tuple" [Form.bool s, Form.bool k]))
        (ctor "WCon" [Form.bool s, bits n (adcV n (a / 2) (b / 2) f k)]) := fun s k =>
      step_call (xs := [(Q1, _), (Q1, _), (Q1, _), (Q1, _), (Q1, _), (Q1, _)]) h.group
        (.cons (fun _ => value_nat) (.cons (fun _ => value_bits) (.cons (fun _ => value_bits)
          (.cons (fun _ => value_bool) (.cons (fun _ => value_conT)
            (.cons (fun _ => value_pair) .nil))))))
        (u := ctor "WCon" [Form.bool s, Ann (grp n (bits n (a / 2)) (bits n (b / 2)) f adcT (Form.bool k))
          (App Q1 (Ref "Word") (Form.nat n))])
        (by simp [walk, «opsDefs.Word.adc.group», conT, adcT, ctor, takes, Quan.live, Quan.fld, bindsAt,
          Env.sub, Term.unspine, node, Term.sub, spine, sub_nat, sub_bits, Form.bool])
        (ctor2v value_bool (ann ih))
    have vs : Values bk [(Q1, Form.nat (n + 1)), (Q1, bits (n + 1) a), (Q1, bits (n + 1) b),
        (Q1, Form.bool f), (Q1, adcT), (Q1, Form.bool c)] :=
      .cons (fun _ => value_nat) (.cons (fun _ => value_bits) (.cons (fun _ => value_bits)
        (.cons (fun _ => value_bool) (.cons (fun _ => value_ctor nofun) (.cons (fun _ => value_bool) .nil)))))
    have hres : ctor "WCon" [Form.bool (sB (a % 2 = 1) ((b % 2 = 1) ^^ f) c),
        bits n (adcV n (a / 2) (b / 2) f (kB (a % 2 = 1) ((b % 2 = 1) ^^ f) c))] =
        bits (n + 1) (adcV (n + 1) a b f c) := by
      rw [adcV, bits_cons (by split <;> omega), ← bool_bit]
    rw [← hres]
    cases f <;> simp only [Bool.xor_false, Bool.xor_true]
    · -- Word.adc on f = False: the full add of the bits as they are
      refine steps_eq (step_call (xs := [(Q1, _), (Q1, _), (Q1, _), (Q1, _), (Q1, _), (Q1, _)]) h.group vs
        (u := Ann (grp n (bits n (a / 2)) (bits n (b / 2)) false conT
          (App Q2 (App Q2 (App Q1 (Ref "Bool.full_add") (Form.bool (a % 2 = 1))) (Form.bool (b % 2 = 1)))
            (Form.bool c))) (App Q1 (Ref "Word") (Form.nat (n + 1))))
        (by simp [walk, «opsDefs.Word.adc.group», adcT, conT, nat_succ, bits_succ, ctor, takes, Quan.live,
          Quan.fld, bindsAt, Env.sub, Term.unspine, node, Term.sub, spine, sub_nat, sub_bits, Form.bool,
          data_nat', data_bits', data])
        (ann (arg vcon rfl (full_add_steps (m := 0) (z := c) h.fa .refl) (con _ _)))) ?_ rfl
      simp only [adcC]; split <;> simp_all <;> omega
    · -- Word.adc on f = True: the full add with b's bit flipped by Bool.not
      refine steps_eq (step_call (xs := [(Q1, _), (Q1, _), (Q1, _), (Q1, _), (Q1, _), (Q1, _)]) h.group vs
        (u := Ann (grp n (bits n (a / 2)) (bits n (b / 2)) true conT
          (App Q2 (App Q2 (App Q1 (Ref "Bool.full_add") (Form.bool (a % 2 = 1)))
            (App Q1 (Ref "Bool.not") (Form.bool (b % 2 = 1)))) (Form.bool c)))
          (App Q1 (Ref "Word") (Form.nat (n + 1))))
        (by simp [walk, «opsDefs.Word.adc.group», adcT, conT, nat_succ, bits_succ, ctor, takes, Quan.live,
          Quan.fld, bindsAt, Env.sub, Term.unspine, node, Term.sub, spine, sub_nat, sub_bits, Form.bool,
          data_nat', data_bits', data])
        (ann (arg vcon rfl (full_add_steps (z := c) h.fa (not_steps h.fa.not)) (con _ _)))) ?_ rfl
      simp only [adcC]; split <;> simp_all <;> omega

-- the value and the steps of Word.adc, in one pass
def adcCV : Nat → Nat → Nat → Bool → Bool → Nat × Nat
  | 0, _, _, _, _ => (0, 1)
  | n + 1, a, b, f, c =>
    let x := a % 2 = 1
    let y := (b % 2 = 1) ^^ f
    let r := adcCV n (a / 2) (b / 2) f (kB x y c)
    ((if sB x y c then 1 else 0) + 2 * r.1, r.2 + (4 + (if f then 1 else 0) + faC x y))

theorem adcCV_eq : adcCV n a b f c = (adcV n a b f c, adcC n a b f c) := by
  induction n generalizing a b c with
  | zero => rfl
  | succ n ih => simp only [adcCV, ih, adcV, adcC]

-- Word.add and Word.sub: Word.adc, under an annotation
abbrev wordAdc (f : Bool) : Term :=
  Lam Q1 (Lam Q1 (Lam Q1 (Ann (App Q1 (App Q1 (App Q1 (App Q1 (App Q1 (App Q1 (Ref "Word.adc.group")
    (Var 2)) (Var 1)) (Var 0)) (Form.bool f)) adcT) (Form.bool f)) (App Q1 (Ref "Word") (Var 2)))))

theorem word_add_eq : «opsDefs.Word.add».v = wordAdc false := rfl
theorem word_sub_eq : «opsDefs.Word.sub».v = wordAdc true := rfl

theorem word_adc_steps (h : Has bk W (wordAdc f)) (ha : AdcDefs bk) :
    Steps bk (adcC n a b f f + 2) (App Q1 (App Q1 (App Q1 (Ref W) (Form.nat n)) (bits n a)) (bits n b))
      (bits n (adcV n a b f f)) :=
  step_call (xs := [(Q1, _), (Q1, _), (Q1, _)]) h
    (.cons (fun _ => value_nat) (.cons (fun _ => value_bits) (.cons (fun _ => value_bits) .nil)))
    (u := Ann (grp n (bits n a) (bits n b) f adcT (Form.bool f)) (App Q1 (Ref "Word") (Form.nat n)))
    (by simp [walk, takes, Quan.live, bindsAt, Env.sub, Term.sub, spine, adcT, ctor, Form.bool, sub_nat])
    (ann (adc_steps ha))

-- U32.add and U32.sub: the U32 of Word.add or Word.sub
abbrev u32Adc (W : String) : Term :=
  Prj (Mat "U32" (Prj (Lam Q1 (Mat "()" (Prj (Mat "U32" (Prj (Lam Q1 (Mat "()" (Tup Q1 (Lab "U32")
    (Tup Q1 (App Q1 (App Q1 (App Q1 (Ref W) (Form.nat 32)) (Var 1)) (Var 0)) (Lab "()"))) Efq))) Efq))
    Efq))) Efq)

theorem u32_add_eq : «opsDefs.U32.add».v = u32Adc "Word.add" := rfl
theorem u32_sub_eq : «opsDefs.U32.sub».v = u32Adc "Word.sub" := rfl

theorem u32_adc_steps (h : Has bk k (u32Adc W)) (hw : Has bk W (wordAdc f)) (ha : AdcDefs bk) :
    Steps bk (adcC 32 v w f f + 3) (App Q1 (App Q1 (Ref k) (u32 v)) (u32 w)) (u32 (adcV 32 v w f f)) :=
  step_call (xs := [(Q1, _), (Q1, _)]) h (.cons (fun _ => value_u32) (.cons (fun _ => value_u32) .nil))
    (u := ctor "U32" [App Q1 (App Q1 (App Q1 (Ref W) (Form.nat 32)) (bits 32 v)) (bits 32 w)])
    (by simp [walk, u32, ctor, takes, bindsAt, Quan.live, Quan.fld, Term.sub, spine, Env.sub, sub_nat,
      sub_bits])
    (ctor1 (word_adc_steps hw ha))

end Ops
