import Bootstrap.EvalSteps.Bool

-- EvalSteps.Subst
-- ===============
--
-- The defs of the Eval copy on variables: the term of a variable, a shift, and
-- a substitution, as the kernel's Term.subk computes it.

open Quan Term

namespace EvalCopy

-- the renaming that moves each variable from c on up by d
def shifts (d c : Nat) (i : Nat) : Nat := if i < c then i else i + d

-- a call steps to its leaf, then runs on
private theorem call (hk : Book.get B k = some d) (vs : Values B xs)
    (w : walk B d.v [] xs = some (some u)) (r : Runs B u v) : Runs B (spine (Ref k) xs) v :=
  .step (Eval.walk hk vs w) r

theorem env_sub_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Env.sub") [(Q1, Form.env e), (Q1, Form.nat i)]) (Form.term (Env.sub e i)) := by
  have hk : Book.get B "Env.sub" = some «evalCopy.Env.sub» := h «evalCopy.Env.sub» (by simp [evalCopy])
  have vs : Values B [(Q1, Form.env e), (Q1, Form.nat i)] :=
    .cons (fun _ => value_env) (.cons (fun _ => value_nat) .nil)
  induction e generalizing i with
  | nil =>
    exact call hk vs (by
      simp [«evalCopy.Env.sub», Form.env, list, walk, Form.term, ctor, takes, Quan.live, Quan.fld,
        sub, spine, bindsAt, Env.sub, data_iff.2 data_nat] <;> rfl) (.refl value_term)
  | cons x e ih =>
    cases i with
    | zero =>
      exact call hk vs (by
        simp [«evalCopy.Env.sub», Form.env, list, walk, Form.nat, ctor, takes, Quan.live, Quan.fld,
          sub, spine, bindsAt, Env.sub, data_iff.2 data_term] <;> rfl) (.refl value_term)
    | succ i =>
      refine call hk vs (by
        simp [«evalCopy.Env.sub», Form.env, list, walk, Form.nat, ctor, takes, Quan.live, Quan.fld,
          sub, spine, bindsAt, Env.sub, data_iff.2 data_nat, data_iff.2 data_term] <;> rfl) ?_
      simpa [spine, Form.env, Env.sub] using
        ih (i := i) (.cons (fun _ => value_env) (.cons (fun _ => value_nat) .nil))

-- the first field of a pair takes its steps
private theorem Steps.tup_a (h : Steps B n a a') : Steps B n (Tup Q1 a b) (Tup Q1 a' b) := by
  induction h with
  | refl => exact .refl
  | step e _ ih => exact .step (.tup_a rfl e) ih

-- the second field of a pair takes its steps, after a first field that is a value
private theorem Steps.tup_b (va : Value B a) (h : Steps B n b b') :
    Steps B n (Tup Q1 a b) (Tup Q1 a b') := by
  induction h with
  | refl => exact .refl
  | step e _ ih => exact .step (.tup_b (fun _ => va) e) ih

-- a pair at quantity 1 runs its two fields
private theorem runs_tup (ha : Runs B a a') (hb : Runs B b b') :
    Runs B (Tup Q1 a b) (Tup Q1 a' b') :=
  have ⟨_, sa, va⟩ := ha
  have ⟨_, sb, vb⟩ := hb
  ⟨_, (Steps.tup_a sa).trans (Steps.tup_b va sb), .tup (fun _ => va) vb⟩

-- a live argument runs, after a function that is a value
private theorem runs_app_x (vf : Value B f) (hx : Runs B x x') (r : Runs B (App q f x') v)
    (l : q.live = true := by rfl) : Runs B (App q f x) v :=
  have ⟨_, s, _⟩ := hx
  .steps (Steps.app_x vf l s) r

-- a def that takes an argument is a value alone
private theorem value_ref (hk : Book.get B k = some d) (w : walk B d.v [] [] = some none) :
    Value B (Ref k) :=
  .call (xs := []) hk .nil (walk_iff.1 w)

-- Nat.add adds
private theorem add_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Nat.add") [(Q1, Form.nat a), (Q1, Form.nat b)]) (Form.nat (a + b)) := by
  have hk : Book.get B "Nat.add" = some «evalCopy.Nat.add» := h «evalCopy.Nat.add» (by simp [evalCopy])
  induction a with
  | zero =>
    refine call hk (.cons (fun _ => value_nat) (.cons (fun _ => value_nat) .nil)) (by
      simp [walk, «evalCopy.Nat.add», Form.nat, ctor, takes, Quan.live, Quan.fld, sub, spine,
        bindsAt, Env.sub] <;> rfl) ?_
    simpa using Runs.refl value_nat
  | succ a ih =>
    refine call hk (.cons (fun _ => value_nat) (.cons (fun _ => value_nat) .nil)) (by
      simp [walk, «evalCopy.Nat.add», Form.nat, ctor, takes, Quan.live, Quan.fld, sub, spine,
        bindsAt, Env.sub] <;> rfl) ?_
    rw [Nat.add_right_comm]
    exact runs_tup (.refl .lab) (runs_tup ih (.refl .lab))

-- Nat.cmp compares two nats
private theorem cmp_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Nat.cmp") [(Q1, Form.nat a), (Q1, Form.nat b)])
      (ctor (if a < b then "LT" else if a = b then "EQ" else "GT") []) := by
  have hk : Book.get B "Nat.cmp" = some «evalCopy.Nat.cmp» := h «evalCopy.Nat.cmp» (by simp [evalCopy])
  have vs : Values B [(Q1, Form.nat a), (Q1, Form.nat b)] :=
    .cons (fun _ => value_nat) (.cons (fun _ => value_nat) .nil)
  induction a generalizing b with
  | zero =>
    cases b
    · exact call hk vs (by
        simp [«evalCopy.Nat.cmp», walk, Form.nat, ctor, takes, Quan.live, Quan.fld, sub,
          spine] <;> rfl) (.refl (value_ctor (fs := []) nofun))
    · exact call hk vs (by
        simp [«evalCopy.Nat.cmp», walk, Form.nat, ctor, takes, Quan.live, Quan.fld, sub, spine,
          bindsAt, data_iff.2 data_nat] <;> rfl) (.refl (value_ctor (fs := []) nofun))
  | succ a ih =>
    cases b
    · exact call hk vs (by
        simp [«evalCopy.Nat.cmp», walk, Form.nat, ctor, takes, Quan.live, Quan.fld, sub, spine,
          bindsAt, data_iff.2 data_nat] <;> rfl) (.refl (value_ctor (fs := []) nofun))
    · refine call hk vs (by
        simp [«evalCopy.Nat.cmp», walk, Form.nat, ctor, takes, Quan.live, Quan.fld, sub, spine,
          bindsAt, Env.sub, data_iff.2 data_nat] <;> rfl) ?_
      simpa [spine] using ih (b := _) (.cons (fun _ => value_nat) (.cons (fun _ => value_nat) .nil))

-- Nat.is_lt tells whether a < b
private theorem is_lt_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Nat.is_lt") [(Q1, Form.nat a), (Q1, Form.nat b)])
      (Form.bool (decide (a < b))) := by
  have hk : Book.get B "Nat.is_lt" = some «evalCopy.Nat.is_lt» :=
    h «evalCopy.Nat.is_lt» (by simp [evalCopy])
  have hc : Book.get B "Cmp.is_lt" = some «evalCopy.Cmp.is_lt» :=
    h «evalCopy.Cmp.is_lt» (by simp [evalCopy])
  refine call hk (.cons (fun _ => value_nat) (.cons (fun _ => value_nat) .nil)) (by
    simp [«evalCopy.Nat.is_lt», walk, takes, Quan.live, sub, spine, bindsAt, Env.sub,
      data_iff.2 data_nat] <;> rfl) ?_
  have hr := cmp_copy h (a := a) (b := b)
  have vc := value_ref hc (by simp [«evalCopy.Cmp.is_lt», walk, takes] <;> rfl)
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · simp only [hab, ↓reduceIte] at hr
    refine runs_app_x vc hr (call (xs := [(Q1, _)]) hc
      (.cons (fun _ => value_ctor (fs := []) nofun) .nil) (by
        simp [«evalCopy.Cmp.is_lt», walk, ctor, takes, Quan.live, Quan.fld, sub, spine] <;> rfl) ?_)
    simp only [hab, decide_true]; exact .refl (value_bool (b := true))
  · subst hab; simp only [Nat.lt_irrefl, ↓reduceIte] at hr
    refine runs_app_x vc hr (call (xs := [(Q1, _)]) hc
      (.cons (fun _ => value_ctor (fs := []) nofun) .nil) (by
        simp [«evalCopy.Cmp.is_lt», walk, ctor, takes, Quan.live, Quan.fld, sub, spine,
          bindsAt] <;> rfl) ?_)
    simp only [Nat.lt_irrefl, decide_false]; exact .refl (value_bool (b := false))
  · simp only [show ¬ a < b by omega, show a ≠ b by omega, ↓reduceIte] at hr
    refine runs_app_x vc hr (call (xs := [(Q1, _)]) hc
      (.cons (fun _ => value_ctor (fs := []) nofun) .nil) (by
        simp [«evalCopy.Cmp.is_lt», walk, ctor, takes, Quan.live, Quan.fld, sub, spine,
          bindsAt] <;> rfl) ?_)
    simp only [show ¬ a < b by omega, decide_false]; exact .refl (value_bool (b := false))

-- Term.shift.at gives the shifted variable
private theorem shift_at_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Term.shift.at")
        [(Q1, Form.bool (decide (i < c))), (Q1, Form.nat i), (Q1, Form.nat d)])
      (Form.nat (shifts d c i)) := by
  have hk : Book.get B "Term.shift.at" = some «evalCopy.Term.shift.at» :=
    h «evalCopy.Term.shift.at» (by simp [evalCopy])
  have vs : Values B [(Q1, Form.bool (decide (i < c))), (Q1, Form.nat i), (Q1, Form.nat d)] :=
    .cons (fun _ => value_bool) (.cons (fun _ => value_nat) (.cons (fun _ => value_nat) .nil))
  by_cases hic : i < c
  · refine call hk vs (by
      simp [«evalCopy.Term.shift.at», hic, walk, Form.bool, ctor, takes, Quan.live, Quan.fld, sub,
        spine, bindsAt, Env.sub, data_iff.2 data_nat] <;> rfl) ?_
    simpa [shifts, hic] using Runs.refl (value_nat (n := i))
  · refine call hk vs (by
      simp [«evalCopy.Term.shift.at», hic, walk, Form.bool, ctor, takes, Quan.live, Quan.fld, sub,
        spine, bindsAt, Env.sub, data_iff.2 data_nat] <;> rfl) ?_
    simpa [shifts, hic, spine] using add_copy h (a := i) (b := d)

-- shifting under one more binder lifts the renaming
private theorem shifts_succ : shifts d (c + 1) = Ren.up (shifts d c) := by
  funext i; cases i <;> simp [shifts, Ren.up] <;> split <;> omega

-- a Succ, as the copy writes it, is the form of the next nat
private theorem nat_succ : Tup Q1 (Lab "Succ") (Tup Q1 (Form.nat n) (Lab "()")) = Form.nat (n + 1) :=
  rfl

theorem shift_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Term.shift") [(Q1, Form.term t), (Q2, Form.nat d), (Q2, Form.nat c)])
      (Form.term (ren (shifts d c) t)) := by
  have hk : Book.get B "Term.shift" = some «evalCopy.Term.shift» :=
    h «evalCopy.Term.shift» (by simp [evalCopy])
  induction t generalizing c
  case Var i =>
    have vs : Values B [(Q1, Form.term (Var i)), (Q2, Form.nat d), (Q2, Form.nat c)] :=
      .cons (fun _ => value_term) (.cons (fun _ => value_nat) (.cons (fun _ => value_nat) .nil))
    refine call hk vs (by
      simp [«evalCopy.Term.shift», walk, Form.term, ctor, takes, Quan.live, Quan.fld, sub, spine,
        bindsAt, Env.sub, data_iff.2 data_nat] <;> rfl) ?_
    simp only [ren, Form.term, ctor, List.foldr]
    refine runs_tup (.refl .lab) (runs_tup ?_ (.refl .lab))
    have vsa := value_ref (h «evalCopy.Term.shift.at» (by simp [evalCopy]))
      (by simp [«evalCopy.Term.shift.at», walk, takes] <;> rfl)
    obtain ⟨_, s, _⟩ := is_lt_copy h (a := i) (b := c)
    exact .steps (Steps.app_f (Steps.app_f (Steps.app_x vsa rfl s))) (shift_at_copy h)
  all_goals
    refine call hk
      (.cons (fun _ => value_term) (.cons (fun _ => value_nat) (.cons (fun _ => value_nat) .nil)))
      (by
        simp [«evalCopy.Term.shift», walk, Form.term, ctor, takes, Quan.live, Quan.fld, sub, spine,
          bindsAt, Env.sub, data_iff.2 data_nat, data_iff.2 data_term] <;> rfl) ?_
    simp only [ren, Form.term, ctor, List.foldr, ← shifts_succ, nat_succ]
    repeat' (first
      | (apply Runs.refl
         first
           | exact value_quan
           | exact .lab
           | exact value_bytes
           | exact value_list (by simpa [Form.name] using fun _ _ => value_bytes))
      | apply_assumption
      | apply runs_tup)

-- Nat.sub subtracts, down to zero
private theorem nat_sub_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Nat.sub") [(Q1, Form.nat a), (Q1, Form.nat b)]) (Form.nat (a - b)) := by
  have hk : Book.get B "Nat.sub" = some «evalCopy.Nat.sub» := h «evalCopy.Nat.sub» (by simp [evalCopy])
  have vs : Values B [(Q1, Form.nat a), (Q1, Form.nat b)] :=
    .cons (fun _ => value_nat) (.cons (fun _ => value_nat) .nil)
  induction a generalizing b with
  | zero =>
    rw [Nat.zero_sub]
    exact call hk vs (by
      simp [«evalCopy.Nat.sub», walk, Form.nat, ctor, takes, Quan.live, Quan.fld, sub, spine,
        bindsAt, data_iff.2 data_nat] <;> rfl) (.refl (value_nat (n := 0)))
  | succ a ih =>
    cases b
    · exact call hk vs (by
        simp [«evalCopy.Nat.sub», walk, Form.nat, ctor, takes, Quan.live, Quan.fld, sub, spine,
          bindsAt, Env.sub, data_iff.2 data_nat] <;> rfl) (.refl (value_nat (n := a + 1)))
    · refine call hk vs (by
        simp [«evalCopy.Nat.sub», walk, Form.nat, ctor, takes, Quan.live, Quan.fld, sub, spine,
          bindsAt, Env.sub, data_iff.2 data_nat] <;> rfl) ?_
      simpa [spine] using ih (b := _) (.cons (fun _ => value_nat) (.cons (fun _ => value_nat) .nil))

-- a call that needs more arguments is a value
private theorem value_part (hk : Book.get B k = some d) (vs : Values B xs)
    (w : walk B d.v [] xs = some none) : Value B (spine (Ref k) xs) :=
  .call hk vs (walk_iff.1 w)

-- Env.sub on an env alone is a value
private theorem value_env_sub (h : Contains B evalCopy) :
    Value B (App Q1 (Ref "Env.sub") (Form.env e)) := by
  have hk : Book.get B "Env.sub" = some «evalCopy.Env.sub» := h «evalCopy.Env.sub» (by simp [evalCopy])
  cases e <;>
    exact value_part (xs := [(Q1, _)]) hk (.cons (fun _ => value_env) .nil)
      (by simp [«evalCopy.Env.sub», Form.env, list, walk, ctor, takes, Quan.live, Quan.fld, bindsAt])

-- Term.lift.at keeps the variable below the depth, else takes the value
private theorem lift_at_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Term.lift.at")
        [(Q1, Form.bool (decide (i < d))), (Q1, Form.nat i), (Q1, Form.term v)])
      (Form.term (if i < d then Var i else v)) := by
  have hk : Book.get B "Term.lift.at" = some «evalCopy.Term.lift.at» :=
    h «evalCopy.Term.lift.at» (by simp [evalCopy])
  have vs : Values B [(Q1, Form.bool (decide (i < d))), (Q1, Form.nat i), (Q1, Form.term v)] :=
    .cons (fun _ => value_bool) (.cons (fun _ => value_nat) (.cons (fun _ => value_term) .nil))
  by_cases hid : i < d
  · refine call hk vs (by
      simp [«evalCopy.Term.lift.at», hid, walk, Form.bool, ctor, takes, Quan.live, Quan.fld, sub,
        spine, bindsAt, Env.sub, data_iff.2 data_nat, data_iff.2 data_term] <;> rfl) ?_
    simp only [hid, ↓reduceIte]; exact .refl (value_term (t := Var i))
  · refine call hk vs (by
      simp [«evalCopy.Term.lift.at», hid, walk, Form.bool, ctor, takes, Quan.live, Quan.fld, sub,
        spine, bindsAt, Env.sub, data_iff.2 data_nat, data_iff.2 data_term] <;> rfl) ?_
    simp only [hid, ↓reduceIte]; exact .refl value_term

-- shifting from 0 adds d to each variable
private theorem shifts_zero : shifts d 0 = (· + d) := by
  funext i; simp [shifts]

-- Term.lift gives the variable i under d binders
private theorem lift_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Term.lift") [(Q2, Form.env e), (Q2, Form.nat d), (Q2, Form.nat i)])
      (Form.term (Subst.lift (Env.sub e) d i)) := by
  have hk : Book.get B "Term.lift" = some «evalCopy.Term.lift» :=
    h «evalCopy.Term.lift» (by simp [evalCopy])
  have vs : Values B [(Q2, Form.env e), (Q2, Form.nat d), (Q2, Form.nat i)] :=
    .cons (fun _ => value_env) (.cons (fun _ => value_nat) (.cons (fun _ => value_nat) .nil))
  cases d with
  | zero =>
    refine call hk vs (by
      simp [«evalCopy.Term.lift», walk, Form.nat, ctor, takes, Quan.live, Quan.fld, sub, spine,
        bindsAt, Env.sub, data_iff.2 data_nat, data_iff.2 data_env] <;> rfl) ?_
    simpa [Subst.lift, spine] using env_sub_copy h (e := e) (i := i)
  | succ p =>
    refine call hk vs (by
      simp [«evalCopy.Term.lift», walk, Form.nat, ctor, takes, Quan.live, Quan.fld, sub, spine,
        bindsAt, Env.sub, data_iff.2 data_nat, data_iff.2 data_env] <;> rfl) ?_
    have hla : Book.get B "Term.lift.at" = some «evalCopy.Term.lift.at» :=
      h «evalCopy.Term.lift.at» (by simp [evalCopy])
    have vla := value_ref hla (by simp [«evalCopy.Term.lift.at», walk, takes] <;> rfl)
    have vsh := value_ref (h «evalCopy.Term.shift» (by simp [evalCopy]))
      (by simp [«evalCopy.Term.shift», walk, takes] <;> rfl)
    obtain ⟨_, s1, _⟩ := is_lt_copy h (a := i) (b := p + 1)
    obtain ⟨_, s2, _⟩ := nat_sub_copy h (a := i) (b := p + 1)
    obtain ⟨_, s3, _⟩ := env_sub_copy h (e := e) (i := i - (p + 1))
    obtain ⟨_, s4, _⟩ := shift_copy h (t := Env.sub e (i - (p + 1))) (d := p + 1) (c := 0)
    have vpart : Value B (spine (Ref "Term.lift.at")
        [(Q1, Form.bool (decide (i < p + 1))), (Q1, Form.nat i)]) := by
      by_cases hid : i < p + 1
      · exact value_part hla (.cons (fun _ => value_bool) (.cons (fun _ => value_nat) .nil))
          (by simp [«evalCopy.Term.lift.at», hid, walk, Form.bool, ctor, takes, Quan.live, Quan.fld,
            bindsAt])
      · exact value_part hla (.cons (fun _ => value_bool) (.cons (fun _ => value_nat) .nil))
          (by simp [«evalCopy.Term.lift.at», hid, walk, Form.bool, ctor, takes, Quan.live, Quan.fld,
            bindsAt])
    have r := lift_at_copy h (i := i) (d := p + 1)
      (v := ren (shifts (p + 1) 0) (Env.sub e (i - (p + 1))))
    have sx := (Steps.app_f (Steps.app_f (Steps.app_x vsh rfl
      ((Steps.app_x (value_env_sub h) rfl s2).trans s3)))).trans s4
    refine .steps (Steps.app_f (Steps.app_f (Steps.app_x vla rfl s1)))
      (.steps (Steps.app_x vpart rfl sx) ?_)
    have e : Subst.lift (Env.sub e) (p + 1) i =
        if i < p + 1 then Var i else ren (shifts (p + 1) 0) (Env.sub e (i - (p + 1))) := by
      simp [Subst.lift, shifts_zero]
    rw [e]; exact r

theorem subst_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Term.subst") [(Q1, Form.term t), (Q2, Form.env e), (Q2, Form.nat d)])
      (Form.term (Term.subk (Env.sub e) d t)) := by
  have hk : Book.get B "Term.subst" = some «evalCopy.Term.subst» :=
    h «evalCopy.Term.subst» (by simp [evalCopy])
  induction t generalizing d
  case Var i =>
    refine call hk
      (.cons (fun _ => value_term) (.cons (fun _ => value_env) (.cons (fun _ => value_nat) .nil)))
      (by
        simp [«evalCopy.Term.subst», walk, Form.term, ctor, takes, Quan.live, Quan.fld, sub, spine,
          bindsAt, Env.sub, data_iff.2 data_nat, data_iff.2 data_env] <;> rfl) ?_
    simpa [subk, spine] using lift_copy h (e := e) (d := d) (i := i)
  all_goals
    refine call hk
      (.cons (fun _ => value_term) (.cons (fun _ => value_env) (.cons (fun _ => value_nat) .nil)))
      (by
        simp [«evalCopy.Term.subst», walk, Form.term, ctor, takes, Quan.live, Quan.fld, sub, spine,
          bindsAt, Env.sub, data_iff.2 data_nat, data_iff.2 data_term, data_iff.2 data_env] <;> rfl) ?_
    simp only [subk, Form.term, ctor, List.foldr, nat_succ]
    repeat' (first
      | (apply Runs.refl
         first
           | exact value_quan
           | exact .lab
           | exact value_bytes
           | exact value_list (by simpa [Form.name] using fun _ _ => value_bytes))
      | apply_assumption
      | apply runs_tup)

-- Subst.one v is the env [v]
private theorem one_env : Subst.one v = Env.sub [v] := by
  funext i; cases i <;> rfl

theorem inst_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Term.inst") [(Q1, Form.term f), (Q1, Form.term v)])
      (Form.term (Term.inst f v)) := by
  have hk : Book.get B "Term.inst" = some «evalCopy.Term.inst» :=
    h «evalCopy.Term.inst» (by simp [evalCopy])
  refine call hk (.cons (fun _ => value_term) (.cons (fun _ => value_term) .nil)) (by
    simp [«evalCopy.Term.inst», walk, takes, Quan.live, sub, spine, bindsAt, Env.sub,
      data_iff.2 data_term] <;> rfl) ?_
  have e : Term.inst f v = Term.subk (Env.sub [v]) 0 f := by
    rw [subk_sub, Term.inst, one_env]; congr 1
  rw [e]; exact subst_copy h (e := [v]) (d := 0)

end EvalCopy
