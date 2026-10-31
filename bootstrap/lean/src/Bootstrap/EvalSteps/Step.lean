import Bootstrap.EvalSteps.Call

-- EvalSteps.Step
-- ==============
--
-- The step of the Eval copy, and its runs of exactly n steps, give what step
-- (Bootstrap/Interp.lean) gives.

open Quan Term

namespace EvalCopy

-- exactly n steps of step
def iterate (bk : Book) : Nat → Term → Option Term
  | 0, t => some t
  | n + 1, t => (step bk t).bind (iterate bk n)

-- each argument term runs to its value, at a live quantity
private inductive RunsArgs (B : Book) : List Arg → List Arg → Prop
  | nil : RunsArgs B [] []
  | cons : q.live = true → Runs B e x → RunsArgs B es xs → RunsArgs B ((q, e) :: es) ((q, x) :: xs)

-- the values of RunsArgs are values
private theorem RunsArgs.values : RunsArgs B es xs → Values B xs
  | .nil => .nil
  | .cons _ ⟨_, _, v⟩ rs => .cons (fun _ => v) rs.values

-- each prefix of the values of RunsArgs is a list of values
private theorem RunsArgs.take : RunsArgs B es xs → ∀ m, Values B (xs.take m)
  | .nil, _ => by simp; exact .nil
  | .cons _ ⟨_, _, v⟩ rs, 0 => by simp; exact .nil
  | .cons _ ⟨_, _, v⟩ rs, m + 1 => by simp; exact .cons (fun _ => v) (rs.take m)

-- the arguments of a spine run in order, after its head
private theorem runs_spine (rs : RunsArgs B es xs) (hf : Steps B n f f')
    (hp : ∀ m < xs.length, Value B (spine f' (xs.take m))) (r : Runs B (spine f' xs) v) :
    Runs B (spine f es) v := by
  induction rs generalizing n f f' with
  | nil => exact .steps hf r
  | cons l rx _ ih =>
    obtain ⟨_, sx, _⟩ := rx
    have vf : Value B f' := hp 0 (by simp)
    exact ih (hf.app_f.trans (sx.app_x vf l)) (fun m hm => hp (m + 1) (by simp; omega)) r

-- the arguments of a call run to values, and its prefixes are values
private theorem runs_args (hk : Book.get B k = some d) (rs : RunsArgs B es xs)
    (hp : ∀ m < xs.length, walk B d.v [] (xs.take m) = some none)
    (r : Runs B (spine (Ref k) xs) v) : Runs B (spine (Ref k) es) v :=
  runs_spine rs .refl (fun m hm => .call hk (rs.take m) (walk_iff.1 (hp m hm))) r

-- a call whose arguments run to values steps to the leaf of its walk
private theorem runs_call (hk : Book.get B k = some d) (rs : RunsArgs B es xs)
    (hp : ∀ m < xs.length, walk B d.v [] (xs.take m) = some none)
    (w : walk B d.v [] xs = some (some u)) (r : Runs B u v) : Runs B (spine (Ref k) es) v :=
  runs_args hk rs hp (.step (Eval.walk hk rs.values w) r)

-- a value as an argument at quantity 1 runs to itself
private theorem RunsArgs.v1 (v : Value B x) (rs : RunsArgs B es xs) :
    RunsArgs B ((Q1, x) :: es) ((Q1, x) :: xs) := .cons rfl (.refl v) rs

-- a value as an argument at quantity 2 runs to itself
private theorem RunsArgs.v2 (v : Value B x) (rs : RunsArgs B es xs) :
    RunsArgs B ((Q2, x) :: es) ((Q2, x) :: xs) := .cons rfl (.refl v) rs

-- an argument at quantity 1 runs to its value
private theorem RunsArgs.r1 (r : Runs B e x) (rs : RunsArgs B es xs) :
    RunsArgs B ((Q1, e) :: es) ((Q1, x) :: xs) := .cons rfl r rs

-- the form of a term is Data
private theorem dterm : data (Form.term t) = true := data_iff.2 data_term

-- the form of a list of defs is Data
private theorem ddefs : data (Form.defs ds) = true := data_iff.2 data_defs

-- the form of a quantity is Data
private theorem dquan : data (Form.quan q) = true := data_iff.2 data_quan

-- the form of a list of names is Data
private theorem dnames : data (list (List.map Form.name ks)) = true :=
  data_iff.2 (data_list (by simpa [Form.name] using fun _ _ => data_bytes))

-- the form of a nat is Data
private theorem dnat : data (Form.nat n) = true := data_iff.2 data_nat

-- the form of a name is Data
private theorem dname : data (Form.name k) = true := data_iff.2 data_bytes

-- quantity 0 is dead
private theorem live0 : Q0.live = false := rfl

-- quantity 1 is live
private theorem live1 : Q1.live = true := rfl

-- quantity 2 is live
private theorem live2 : Q2.live = true := rfl

-- a run that reaches the form of o reaches the form of o', when o = o'
private theorem runs_eq (r : Runs B e (Form.maybe Form.term o)) (ho : o = o') :
    Runs B e (Form.maybe Form.term o') := ho ▸ r

-- the first field of a live pair takes its steps
private theorem steps_tup_a (l : q.live = true) (h : Steps B n a a') :
    Steps B n (Tup q a b) (Tup q a' b) := by
  induction h with
  | refl => exact .refl
  | step e _ ih => exact .step (.tup_a l e) ih

-- the second field of a pair takes its steps, after a first field that is a value
private theorem steps_tup_b (va : q.live = true → Value B a) (h : Steps B n b b') :
    Steps B n (Tup q a b) (Tup q a b') := by
  induction h with
  | refl => exact .refl
  | step e _ ih => exact .step (.tup_b va e) ih

-- the Some of a term runs as that term runs
private theorem runs_some (r : Runs B x x') : Runs B (Form.some x) (Form.some x') := by
  obtain ⟨_, s, v⟩ := r
  exact ⟨_, steps_tup_b (fun _ => .lab) (steps_tup_a rfl s), value_ctor (by simp [v])⟩

-- Eval.vals, not as arguments, gives value
private theorem vals_false {bk : Book} (h : Contains B evalCopy) :
    Runs B (spine (Ref "Eval.vals") [(Q2, Form.defs bk.defs), (Q2, Form.term t), (Q1, Form.bool false)])
      (Form.bool (value bk t)) := by simpa using vals_copy (a := false) h

-- a call of Eval.step steps to the leaf of its walk
private theorem step_call {bk : Book} (h : Contains B evalCopy)
    (w : walk B «evalCopy.Eval.step».v [] [(Q2, Form.defs bk.defs), (Q2, Form.term t)] = some (some u))
    (r : Runs B u v) : Runs B (spine (Ref "Eval.step") [(Q2, Form.defs bk.defs), (Q2, Form.term t)]) v := by
  refine runs_call (h «evalCopy.Eval.step» (by simp [evalCopy])) (.v2 value_defs (.v2 value_term .nil)) ?_ w r
  intro m hm; simp at hm
  rcases m with _ | _ | m <;> first | omega | simp [«evalCopy.Eval.step», walk, takes, bindsAt, Quan.live, ddefs]

-- Eval.step.unlet gives f with v put in, when fits
private theorem unlet_run (h : Contains B evalCopy)
    (rs : RunsArgs B es [(Q1, Form.bool b), (Q1, Form.term f), (Q1, Form.term v)]) :
    Runs B (spine (Ref "Eval.step.unlet") es) (Form.maybe Form.term (if b then some (inst f v) else none)) := by
  have hk := h «evalCopy.Eval.step.unlet» (by simp [evalCopy])
  cases b
  · refine runs_call hk rs ?_ ?_ (.refl (value_maybe fun _ => value_term))
    · intro m hm; simp at hm
      rcases m with _ | _ | _ | m <;> first | omega | simp [«evalCopy.Eval.step.unlet», walk, Form.bool, ctor, takes, bindsAt, Quan.live, Quan.fld]
    · simp [«evalCopy.Eval.step.unlet», walk, Form.bool, Form.maybe, ctor, takes, bindsAt, Quan.live, Quan.fld, Term.sub, Term.spine]
  · refine runs_call hk rs (u := Form.some (spine (Ref "Term.inst") [(Q1, Form.term f), (Q1, Form.term v)])) ?_ ?_
      (runs_some (inst_copy h))
    · intro m hm; simp at hm
      rcases m with _ | _ | _ | m <;> first | omega | simp [«evalCopy.Eval.step.unlet», walk, Form.bool, ctor, takes, bindsAt, Quan.live, Quan.fld]
    · simp [«evalCopy.Eval.step.unlet», walk, Form.bool, Form.some, ctor, takes, bindsAt, Quan.live, Quan.fld, Term.sub, Env.sub, Term.spine]

-- Eval.step.tup_b puts the step of b back in the pair
private theorem tup_b_run (h : Contains B evalCopy)
    (rs : RunsArgs B es [(Q1, Form.quan q), (Q1, Form.term a), (Q1, Form.maybe Form.term sb)]) :
    Runs B (spine (Ref "Eval.step.tup_b") es) (Form.maybe Form.term (sb.map (Tup q a ·))) := by
  have hk := h «evalCopy.Eval.step.tup_b» (by simp [evalCopy])
  refine runs_call hk rs ?_ ?_ (.refl (value_maybe fun _ => value_term))
  all_goals cases sb
  all_goals first
    | (intro m hm; simp at hm; rcases m with _ | _ | _ | m <;> first | omega | simp [«evalCopy.Eval.step.tup_b», walk, Form.maybe, Form.some, ctor, takes, bindsAt, Quan.live])
    | simp [«evalCopy.Eval.step.tup_b», walk, Form.maybe, Form.some, Form.term, ctor, takes, bindsAt, Quan.live, Quan.fld, Term.sub, Env.sub, Term.spine]

-- Eval.step.cast gives f, when e is Rfl
private theorem cast_run (h : Contains B evalCopy)
    (rs : RunsArgs B es [(Q1, Form.term e), (Q1, Form.term f)]) :
    Runs B (spine (Ref "Eval.step.cast") es) (Form.maybe Form.term (if e = Rfl then some f else none)) := by
  have hk := h «evalCopy.Eval.step.cast» (by simp [evalCopy])
  refine runs_call hk rs ?_ ?_ (.refl (value_maybe fun _ => value_term))
  all_goals cases e
  all_goals first
    | (intro m hm; simp at hm; rcases m with _ | _ | m <;> first | omega | simp [«evalCopy.Eval.step.cast», walk, Form.term, ctor, takes, bindsAt, Quan.live, Quan.fld])
    | simp [«evalCopy.Eval.step.cast», walk, Form.maybe, Form.some, Form.term, ctor, takes, bindsAt, Quan.live, Quan.fld, Term.sub, Env.sub, Term.spine]

theorem step_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Eval.step") [(Q2, Form.defs bk.defs), (Q2, Form.term t)])
      (Form.maybe Form.term (step bk t)) := by
  induction t
  case Ann x T =>
    refine step_call h ?_ (.refl (value_maybe fun _ => value_term))
    simp [«evalCopy.Eval.step», step, walk, Form.term, Form.maybe, Form.some, ctor, takes, bindsAt, Quan.live, Quan.fld, ddefs, dterm, Term.sub, Env.sub, Term.spine]
  case Ref k =>
    refine step_call h (u := spine (Ref "Eval.call") [(Q2, Form.defs bk.defs), (Q2, Form.term (Ref k))]) ?_ (call_copy h)
    simp [«evalCopy.Eval.step», walk, Form.term, ctor, takes, bindsAt, Quan.live, Quan.fld, ddefs, dname, Term.sub, Env.sub, Term.spine]
  case App q f x ihf ihx =>
    have ha := h «evalCopy.Eval.step.app» (by simp [evalCopy])
    refine step_call h (u := spine (Ref "Eval.step.app") [(Q1, Form.quan q), (Q1, Form.term f), (Q1, Form.term x),
      (Q1, spine (Ref "Eval.step") [(Q2, Form.defs bk.defs), (Q2, Form.term f)]),
      (Q1, spine (Ref "Eval.vals") [(Q2, Form.defs bk.defs), (Q2, Form.term f), (Q1, Form.bool false)]),
      (Q1, spine (Ref "Quan.live") [(Q1, Form.quan q)]),
      (Q1, spine (Ref "Eval.step") [(Q2, Form.defs bk.defs), (Q2, Form.term x)]),
      (Q1, spine (Ref "Eval.vals") [(Q2, Form.defs bk.defs), (Q2, Form.term x), (Q1, Form.bool false)]),
      (Q1, spine (Ref "Eval.redex") [(Q1, Form.defs bk.defs), (Q2, Form.quan q), (Q2, Form.term f), (Q2, Form.term x)])])
      (by simp [«evalCopy.Eval.step», walk, Form.bool, Form.term, ctor, takes, bindsAt, Quan.live, Quan.fld, dquan, dterm, ddefs, Term.sub, Env.sub, Term.spine])
      (runs_call ha (.v1 value_quan (.v1 value_term (.v1 value_term
        (.r1 ihf (.r1 (vals_false h) (.r1 (live_copy h) (.r1 ihx
          (.r1 (vals_false h) (.r1 (redex_copy h) .nil))))))))) ?_ ?_
        (.refl (value_maybe fun _ => value_term)))
    all_goals cases q <;> cases hsf : step bk f <;> cases hvf : value bk f <;> cases hsx : step bk x <;> cases hvx : value bk x
    all_goals first
      | (intro m hm; simp at hm; rcases m with _ | _ | _ | _ | _ | _ | _ | _ | _ | m <;> first | omega | simp [«evalCopy.Eval.step.app», walk, Form.maybe, Form.some, Form.bool, ctor, takes, bindsAt, Quan.live, Quan.fld, dquan, dterm])
      | simp [«evalCopy.Eval.step.app», step, part, hsf, hvf, hsx, hvx, walk, Form.maybe, Form.some, Form.bool, Form.term, ctor, takes, bindsAt, Quan.live, Quan.fld, dquan, dterm, Term.sub, Env.sub, Term.spine]
  case Min a b iha ihb =>
    have ha := h «evalCopy.Eval.step.min» (by simp [evalCopy])
    refine step_call h (u := spine (Ref "Eval.step.min") [(Q1, Form.term a), (Q1, Form.term b),
      (Q1, spine (Ref "Eval.step") [(Q2, Form.defs bk.defs), (Q2, Form.term a)]),
      (Q1, spine (Ref "Eval.vals") [(Q2, Form.defs bk.defs), (Q2, Form.term a), (Q1, Form.bool false)]),
      (Q1, spine (Ref "Eval.step") [(Q2, Form.defs bk.defs), (Q2, Form.term b)]),
      (Q1, spine (Ref "Eval.vals") [(Q2, Form.defs bk.defs), (Q2, Form.term b), (Q1, Form.bool false)]),
      (Q1, spine (Ref "Eval.meet") [(Q1, Form.term a), (Q1, Form.term b)])])
      (by simp [«evalCopy.Eval.step», walk, Form.bool, Form.term, ctor, takes, bindsAt, Quan.live, Quan.fld, dterm, ddefs, Term.sub, Env.sub, Term.spine])
      (runs_call ha (.v1 value_term (.v1 value_term
        (.r1 iha (.r1 (vals_false h) (.r1 ihb (.r1 (vals_false h) (.r1 (meet_copy h) .nil))))))) ?_ ?_
        (.refl (value_maybe fun _ => value_term)))
    all_goals cases hsa : step bk a <;> cases hva : value bk a <;> cases hsb : step bk b <;> cases hvb : value bk b
    all_goals first
      | (intro m hm; simp at hm; rcases m with _ | _ | _ | _ | _ | _ | _ | _ | _ | m <;> first | omega | simp [«evalCopy.Eval.step.min», walk, Form.maybe, Form.some, Form.bool, ctor, takes, bindsAt, Quan.live, Quan.fld, dterm])
      | simp [«evalCopy.Eval.step.min», step, part, hsa, hva, hsb, hvb, walk, Form.maybe, Form.some, Form.bool, Form.term, ctor, takes, bindsAt, Quan.live, Quan.fld, dterm, Term.sub, Env.sub, Term.spine]
  case Let q v f ihv _ =>
    have hl := h «evalCopy.Eval.step.let» (by simp [evalCopy])
    refine step_call h (u := spine (Ref "Eval.step.let") [(Q1, Form.quan q), (Q1, Form.term v), (Q1, Form.term f),
      (Q1, spine (Ref "Quan.live") [(Q1, Form.quan q)]),
      (Q1, spine (Ref "Eval.step") [(Q2, Form.defs bk.defs), (Q2, Form.term v)]),
      (Q1, spine (Ref "Eval.vals") [(Q2, Form.defs bk.defs), (Q2, Form.term v), (Q1, Form.bool false)]),
      (Q1, spine (Ref "Quan.fits") [(Q1, Form.quan q), (Q1, Form.term v)])])
      (by simp [«evalCopy.Eval.step», walk, Form.bool, Form.term, ctor, takes, bindsAt, live2, Quan.fld, dquan, dterm, ddefs, Term.sub, Env.sub, Term.spine]) ?_
    have rs := RunsArgs.v1 (value_quan (q := q)) (.v1 (value_term (t := v)) (.v1 (value_term (t := f))
      (.r1 (live_copy (q := q) h) (.r1 ihv (.r1 (vals_false (bk := bk) (t := v) h) (.r1 (fits_copy (q := q) (v := v) h) .nil))))))
    cases hq : q.live <;> cases hs : step bk v <;> cases hv : value bk v
    all_goals first
      | (refine runs_call hl rs ?_ ?_ (.refl (value_maybe fun _ => value_term))
         · (intro m hm; simp at hm; rcases m with _ | _ | _ | _ | _ | _ | _ | _ | _ | m <;> first | omega | simp [«evalCopy.Eval.step.let», hq, hs, hv, walk, Form.maybe, Form.some, Form.bool, ctor, takes, bindsAt, live1, live2, Quan.fld, dquan, dterm])
         · simp [«evalCopy.Eval.step.let», step, part, hq, hs, hv, walk, Form.maybe, Form.some, Form.bool, Form.term, ctor, takes, bindsAt, live1, live2, Quan.fld, dquan, dterm, Term.sub, Env.sub, Term.spine])
      | (refine runs_call hl rs (u := spine (Ref "Eval.step.unlet") [(Q1, Form.bool (q != Q2 || data v)), (Q1, Form.term f), (Q1, Form.term v)]) ?_ ?_ (runs_eq (unlet_run h (.v1 value_bool (.v1 value_term (.v1 value_term .nil)))) ?_)
         · (intro m hm; simp at hm; rcases m with _ | _ | _ | _ | _ | _ | _ | _ | _ | m <;> first | omega | simp [«evalCopy.Eval.step.let», hq, hs, hv, walk, Form.maybe, Form.some, Form.bool, ctor, takes, bindsAt, live1, live2, Quan.fld, dquan, dterm])
         · simp [«evalCopy.Eval.step.let», hq, hs, hv, walk, Form.maybe, Form.some, Form.bool, ctor, takes, bindsAt, live1, live2, Quan.fld, dquan, dterm, Term.sub, Env.sub, Term.spine]
         · cases q <;> simp [Quan.live] at hq <;> simp [step, part, hs, hv, Quan.live])
  case Tup q a b iha ihb =>
    have hl := h «evalCopy.Eval.step.tup» (by simp [evalCopy])
    refine step_call h (u := spine (Ref "Eval.step.tup") [(Q1, Form.quan q), (Q1, Form.term a), (Q1, Form.term b),
      (Q1, spine (Ref "Quan.live") [(Q1, Form.quan q)]),
      (Q1, spine (Ref "Eval.step") [(Q2, Form.defs bk.defs), (Q2, Form.term a)]),
      (Q1, spine (Ref "Eval.vals") [(Q2, Form.defs bk.defs), (Q2, Form.term a), (Q1, Form.bool false)]),
      (Q1, spine (Ref "Eval.step") [(Q2, Form.defs bk.defs), (Q2, Form.term b)])])
      (by simp [«evalCopy.Eval.step», walk, Form.bool, Form.term, ctor, takes, bindsAt, live2, Quan.fld, dquan, dterm, ddefs, Term.sub, Env.sub, Term.spine]) ?_
    have rs := RunsArgs.v1 (value_quan (q := q)) (.v1 (value_term (t := a)) (.v1 (value_term (t := b))
      (.r1 (live_copy (q := q) h) (.r1 iha (.r1 (vals_false (bk := bk) (t := a) h) (.r1 ihb .nil))))))
    cases hq : q.live <;> cases hs : step bk a <;> cases hv : value bk a
    all_goals first
      | (refine runs_call hl rs ?_ ?_ (.refl (value_maybe fun _ => value_term))
         · (intro m hm; simp at hm; rcases m with _ | _ | _ | _ | _ | _ | _ | _ | _ | m <;> first | omega | simp [«evalCopy.Eval.step.tup», hq, hs, hv, walk, Form.maybe, Form.some, Form.bool, ctor, takes, bindsAt, live1, live2, Quan.fld, dquan, dterm])
         · simp [«evalCopy.Eval.step.tup», step, part, hq, hs, hv, walk, Form.maybe, Form.some, Form.bool, Form.term, ctor, takes, bindsAt, live1, live2, Quan.fld, dquan, dterm, Term.sub, Env.sub, Term.spine])
      | (refine runs_call hl rs (u := spine (Ref "Eval.step.tup_b") [(Q1, Form.quan q), (Q1, Form.term a), (Q1, Form.maybe Form.term (step bk b))]) ?_ ?_ (runs_eq (tup_b_run h (.v1 value_quan (.v1 value_term (.v1 (value_maybe fun _ => value_term) .nil)))) ?_)
         · (intro m hm; simp at hm; rcases m with _ | _ | _ | _ | _ | _ | _ | _ | _ | m <;> first | omega | simp [«evalCopy.Eval.step.tup», hq, hs, hv, walk, Form.maybe, Form.some, Form.bool, ctor, takes, bindsAt, live1, live2, Quan.fld, dquan, dterm])
         · simp [«evalCopy.Eval.step.tup», hq, hs, hv, walk, Form.maybe, Form.some, Form.bool, ctor, takes, bindsAt, live1, live2, Quan.fld, dquan, dterm, Term.sub, Env.sub, Term.spine]
         · simp [step, part, hq, hs, hv])
  case Rwt e P f ihe _ _ =>
    have hl := h «evalCopy.Eval.step.rwt» (by simp [evalCopy])
    refine step_call h (u := spine (Ref "Eval.step.rwt") [(Q1, Form.term e), (Q1, Form.term P), (Q1, Form.term f),
      (Q1, spine (Ref "Eval.step") [(Q2, Form.defs bk.defs), (Q2, Form.term e)]),
      (Q1, spine (Ref "Eval.vals") [(Q2, Form.defs bk.defs), (Q2, Form.term e), (Q1, Form.bool false)])])
      (by simp [«evalCopy.Eval.step», walk, Form.bool, Form.term, ctor, takes, bindsAt, live2, Quan.fld, dterm, ddefs, Term.sub, Env.sub, Term.spine]) ?_
    have rs := RunsArgs.v1 (value_term (t := e)) (.v1 (value_term (t := P)) (.v1 (value_term (t := f))
      (.r1 ihe (.r1 (vals_false (bk := bk) (t := e) h) .nil))))
    cases hs : step bk e <;> cases hv : value bk e
    all_goals first
      | (refine runs_call hl rs ?_ ?_ (.refl (value_maybe fun _ => value_term))
         · (intro m hm; simp at hm; rcases m with _ | _ | _ | _ | _ | _ | _ | _ | _ | m <;> first | omega | simp [«evalCopy.Eval.step.rwt», hs, hv, walk, Form.maybe, Form.some, Form.bool, ctor, takes, bindsAt, live1, live2, Quan.fld, dterm])
         · simp [«evalCopy.Eval.step.rwt», step, part, hs, hv, walk, Form.maybe, Form.some, Form.bool, Form.term, ctor, takes, bindsAt, live1, live2, Quan.fld, dterm, Term.sub, Env.sub, Term.spine])
      | (refine runs_call hl rs (u := spine (Ref "Eval.step.cast") [(Q1, Form.term e), (Q1, Form.term f)]) ?_ ?_ (runs_eq (cast_run h (.v1 value_term (.v1 value_term .nil))) ?_)
         · (intro m hm; simp at hm; rcases m with _ | _ | _ | _ | _ | _ | _ | _ | _ | m <;> first | omega | simp [«evalCopy.Eval.step.rwt», hs, hv, walk, Form.maybe, Form.bool, ctor, takes, bindsAt, live1, live2, Quan.fld, dterm])
         · simp [«evalCopy.Eval.step.rwt», hs, hv, walk, Form.maybe, Form.bool, ctor, takes, bindsAt, live1, live2, Quan.fld, dterm, Term.sub, Env.sub, Term.spine]
         · simp [step, part, hs, hv])
  all_goals
    refine step_call h ?_ (.refl (value_maybe fun _ => value_term))
    simp [«evalCopy.Eval.step», step, walk, Form.maybe, Form.term, ctor, takes, bindsAt, live1, live2, Quan.fld, dquan, dterm, ddefs, Term.sub, Term.spine, dnat, dname, dnames, data]

-- Eval.run gives the state after n more steps
private theorem run_copy {bk : Book} (h : Contains B evalCopy) : ∀ n r,
    Runs B (spine (Ref "Eval.run") [(Q1, Form.nat n), (Q2, Form.defs bk.defs), (Q1, Form.maybe Form.term r)])
      (Form.maybe Form.term (r.bind (iterate bk n))) := by
  have hk := h «evalCopy.Eval.run» (by simp [evalCopy])
  intro n
  induction n with
  | zero =>
    intro r
    refine runs_call hk (.v1 value_nat (.v2 value_defs (.v1 (value_maybe fun _ => value_term) .nil))) ?_ ?_
      (.refl (value_maybe fun _ => value_term))
    all_goals cases r
    all_goals first
      | (intro m hm; simp at hm; rcases m with _ | _ | _ | m <;> first | omega | simp [«evalCopy.Eval.run», walk, Form.maybe, Form.some, Form.nat, ctor, takes, bindsAt, live1, live2, Quan.fld, ddefs])
      | simp [«evalCopy.Eval.run», iterate, walk, Form.maybe, Form.some, Form.nat, ctor, takes, bindsAt, live1, live2, Quan.fld, ddefs, Term.sub, Env.sub, Term.spine]
  | succ n ih =>
    intro r
    cases r with
    | none =>
      refine runs_call hk (.v1 value_nat (.v2 value_defs (.v1 (value_maybe fun _ => value_term) .nil))) ?_ ?_
        (.refl (value_maybe fun _ => value_term))
      · (intro m hm; simp at hm; rcases m with _ | _ | _ | m <;> first | omega | simp [«evalCopy.Eval.run», walk, Form.maybe, Form.nat, ctor, takes, bindsAt, live1, live2, Quan.fld, ddefs, dnat])
      · simp [«evalCopy.Eval.run», walk, Form.maybe, Form.nat, ctor, takes, bindsAt, live1, live2, Quan.fld, ddefs, dnat, Term.sub, Term.spine]
    | some t =>
      refine runs_call hk (.v1 value_nat (.v2 value_defs (.v1 (value_maybe fun _ => value_term) .nil)))
        (u := spine (Ref "Eval.run") [(Q1, Form.nat n), (Q2, Form.defs bk.defs),
          (Q1, spine (Ref "Eval.step") [(Q2, Form.defs bk.defs), (Q2, Form.term t)])]) ?_ ?_
        (runs_args hk (.v1 value_nat (.v2 value_defs (.r1 (step_copy h) .nil))) ?_ (ih (step bk t)))
      · (intro m hm; simp at hm; rcases m with _ | _ | _ | m <;> first | omega | simp [«evalCopy.Eval.run», walk, Form.maybe, Form.some, Form.nat, ctor, takes, bindsAt, live1, live2, Quan.fld, ddefs, dnat])
      · simp [«evalCopy.Eval.run», walk, Form.maybe, Form.some, Form.nat, ctor, takes, bindsAt, live1, live2, Quan.fld, dterm, ddefs, dnat, Term.sub, Env.sub, Term.spine]
      · cases n <;> (intro m hm; simp at hm; rcases m with _ | _ | _ | m <;> first | omega | simp [«evalCopy.Eval.run», walk, Form.maybe, Form.some, Form.nat, ctor, takes, bindsAt, live1, live2, Quan.fld, ddefs, dnat])

theorem steps_copy (h : Contains B evalCopy) :
    Runs B (App Q1 (App Q1 (App Q1 (Ref "Eval.steps") (Form.nat n)) (Form.defs bk.defs)) (Form.term t))
      (Form.maybe Form.term (iterate bk n t)) := by
  have hk := h «evalCopy.Eval.steps» (by simp [evalCopy])
  show Runs B (spine (Ref "Eval.steps") [(Q1, Form.nat n), (Q1, Form.defs bk.defs), (Q1, Form.term t)]) _
  refine runs_call hk (.v1 value_nat (.v1 value_defs (.v1 value_term .nil)))
    (u := spine (Ref "Eval.run") [(Q1, Form.nat n), (Q2, Form.defs bk.defs), (Q1, Form.maybe Form.term (some t))])
    ?_ ?_ (run_copy h n (some t))
  · (intro m hm; simp at hm; rcases m with _ | _ | _ | m <;> first | omega | simp [«evalCopy.Eval.steps», walk, takes, bindsAt, live1])
  · simp [«evalCopy.Eval.steps», walk, Form.maybe, Form.some, ctor, takes, bindsAt, live1, dterm, ddefs, dnat, Term.sub, Env.sub, Term.spine]

end EvalCopy
