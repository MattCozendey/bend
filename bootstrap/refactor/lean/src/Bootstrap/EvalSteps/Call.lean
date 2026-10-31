import Bootstrap.EvalSteps.Walk

-- EvalSteps.Call
-- ==============
--
-- The defs of the Eval copy on calls: the walk of a call, Value and the
-- arguments of a call (as_args), a call's step, and a redex.

open Quan Term

namespace EvalCopy

-- a live argument runs first, after a function that is a value
private theorem run_x (vf : Value B f) (l : q.live = true) (hx : Runs B x x')
    (r : Runs B (App q f x') v) : Runs B (App q f x) v :=
  have ⟨_, s, _⟩ := hx; .steps (s.app_x vf l) r

-- the function of an application runs first
private theorem run_f (hf : Runs B f f') (r : Runs B (App q f' x) v) : Runs B (App q f x) v :=
  have ⟨_, s, _⟩ := hf; .steps s.app_f r

-- the form of a term is Data
private theorem data_term' : data (Form.term t) = true := data_iff.2 data_term

-- the form of a list of defs is Data
private theorem data_defs' : data (Form.defs ds) = true := data_iff.2 data_defs

-- the form of a def is a value
private theorem value_defn : Value B (Form.defn d) :=
  value_ctor (by simpa [Form.name] using ⟨value_bytes, value_term, value_term, value_bool⟩)

-- the form of a term is a pair of its tag and its fields
private theorem term_tag (t : Term) : ∃ c r, Form.term t = Tup Q1 (Lab c) r ∧
    (c = "Term.Tup" → ∃ q a b, t = Tup q a b) ∧ (c = "Term.App" → ∃ q f x, t = App q f x) ∧
    (c = "Term.Ref" → ∃ k, t = Ref k) := by
  cases t <;> exact ⟨_, _, rfl, by simp, by simp, by simp⟩

theorem callWalk_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Eval.callWalk") [(Q1, Form.defs bk.defs), (Q2, Form.term t)])
      (Form.maybe (Form.maybe Form.term) (callWalk bk t)) := by
  have hk : Book.get B "Eval.callWalk" = some «evalCopy.Eval.callWalk» :=
    h «evalCopy.Eval.callWalk» (by simp [evalCopy])
  have hh : Book.get B "Eval.callWalk.head" = some «evalCopy.Eval.callWalk.head» :=
    h «evalCopy.Eval.callWalk.head» (by simp [evalCopy])
  have hd : Book.get B "Eval.callWalk.def" = some «evalCopy.Eval.callWalk.def» :=
    h «evalCopy.Eval.callWalk.def» (by simp [evalCopy])
  have vh : Value B (App Q1 (Ref "Eval.callWalk.head") (Form.defs bk.defs)) :=
    .call (xs := [(Q1, _)]) hh (.cons (fun _ => value_defs) .nil) (walk_iff.1 (by
      simp [«evalCopy.Eval.callWalk.head», walk, bindsAt, Quan.live, takes]))
  rcases e : unspine t [] with ⟨g, xs⟩
  have rh := head_copy (t := t) h
  have ra := args_copy (t := t) (xs := []) h
  rw [e] at rh ra
  refine .step (Eval.walk hk (.cons (fun _ => value_defs) (.cons (fun _ => value_term) .nil)) (by
    simp [«evalCopy.Eval.callWalk», walk, bindsAt, Quan.live, takes, data_term', Term.sub, Env.sub,
      Term.spine] <;> rfl)) ?_
  obtain ⟨c, r, eg, -, -, hr⟩ := term_tag g
  by_cases hc : c = "Term.Ref"
  · obtain ⟨k, rfl⟩ := hr hc
    have vg : Value B
        (App Q1 (App Q1 (Ref "Eval.callWalk.head") (Form.defs bk.defs)) (Form.term (Ref k))) :=
      .call (xs := [(Q1, _), (Q1,
        _)]) hh (.cons (fun _ => value_defs) (.cons (fun _ => value_term) .nil))
        (walk_iff.1 (by simp [«evalCopy.Eval.callWalk.head», walk, bindsAt, Quan.live, Quan.fld,
          takes, Form.term, ctor]))
    refine run_f (run_x vh rfl rh (.refl vg)) (run_x vg rfl ra ?_)
    refine .step (Eval.walk hh (xs := [(Q1, _), (Q1, _), (Q1, _)])
      (.cons (fun _ => value_defs) (.cons (fun _ => value_term)
        (.cons (fun _ => value_args_form) .nil))) (by
      simp [«evalCopy.Eval.callWalk.head», walk, bindsAt, Quan.live, Quan.fld, takes, Form.term,
        ctor, Term.sub, Env.sub,
        Term.spine] <;> rfl)) ?_
    have vd : Value B (Ref "Eval.callWalk.def") :=
      .call (xs := []) hd .nil (walk_iff.1 (by simp [«evalCopy.Eval.callWalk.def», walk, takes]))
    have rg := get_copy (ds := bk.defs) (k := k) h
    rw [← get_find] at rg
    have vm : ∀ o : Option Def,
      Value B (App Q1 (Ref "Eval.callWalk.def") (Form.maybe Form.defn o)) := by
      intro o
      refine .call (xs := [(Q1, _)]) hd (.cons (fun _ => value_maybe fun _ => value_defn) .nil)
        (walk_iff.1 ?_)
      cases o <;> simp [«evalCopy.Eval.callWalk.def», walk, bindsAt, Quan.live, Quan.fld, takes,
        Form.maybe, Form.some, Form.defn, Form.bool, ctor]
    refine run_f (run_x vd rfl rg (.refl (vm _))) ?_
    cases hg : bk.get k with
    | none =>
      have hn : callWalk bk t = none := by simp [callWalk, e, hg]
      rw [hn]
      refine .step (Eval.walk hd (xs := [(Q1, _), (Q1, _)])
        (.cons (fun _ => value_maybe fun _ => value_defn)
          (.cons (fun _ => value_args_form) .nil)) (by
        simp [«evalCopy.Eval.callWalk.def», walk, bindsAt, Quan.live, Quan.fld, takes, Form.maybe,
          ctor,
          Term.sub,
            Term.spine] <;> rfl)) (.refl (value_maybe (fun _ => value_maybe fun _ => value_term)))
    | some d =>
      have hn : callWalk bk t = walk bk d.v [] xs := by simp [callWalk, e, hg]
      rw [hn]
      refine .step (Eval.walk hd (xs := [(Q1, _), (Q1, _)])
        (.cons (fun _ => value_maybe fun _ => value_defn)
          (.cons (fun _ => value_args_form) .nil)) (by
        simp [«evalCopy.Eval.callWalk.def», walk, bindsAt, Quan.live, Quan.fld, takes, Form.maybe,
          Form.some, Form.defn, Form.bool, ctor, Term.sub, Env.sub, Term.spine] <;> rfl))
        (walk_copy (bk := bk) (t := d.v) (e := []) (xs := xs) h)
  · have ng : ∀ k, g ≠ Ref k := by rintro k rfl; simp [Form.term, ctor] at eg; exact hc eg.1.symm
    have vg : Value B
        (App Q1 (App Q1 (Ref "Eval.callWalk.head") (Form.defs bk.defs)) (Form.term g)) :=
      .call (xs := [(Q1, _), (Q1,
        _)]) hh (.cons (fun _ => value_defs) (.cons (fun _ => value_term) .nil))
        (walk_iff.1 (by rw [eg]; simp [«evalCopy.Eval.callWalk.head», walk, bindsAt, Quan.live,
          Quan.fld, takes, hc]))
    refine run_f (run_x vh rfl rh (.refl vg)) (run_x vg rfl ra ?_)
    have hn : callWalk bk t = none := by
      simp only [callWalk, e]; split <;> simp_all
    rw [hn]
    refine .step (Eval.walk hh (xs := [(Q1, _), (Q1, _), (Q1, _)])
      (.cons (fun _ => value_defs) (.cons (fun _ => value_term)
        (.cons (fun _ => value_args_form) .nil))) (by
      rw [eg]; simp [«evalCopy.Eval.callWalk.head», walk, bindsAt, Quan.live, Quan.fld, takes, hc,
        Term.sub,
        Term.spine] <;> rfl)) (.refl (value_maybe (fun _ => value_maybe fun _ => value_term)))

-- an argument runs, then the call of one argument
private theorem run1 (v0 : Value B f) (hx : Runs B x x') (r : Runs B (App Q1 f x') v) :
    Runs B (App Q1 f x) v := run_x v0 rfl hx r

-- two arguments run in turn, then the call
private theorem run2 (v0 : Value B f) (hx : Runs B x x') (v1 : Value B (App Q1 f x'))
    (hy : Runs B y y') (r : Runs B (App Q1 (App Q1 f x') y') v) :
    Runs B (App Q1 (App Q1 f x) y) v :=
  run_f (run_x v0 rfl hx (.refl v1)) (run_x v1 rfl hy r)

-- three arguments run in turn, then the call
private theorem run3 (v0 : Value B f) (hx : Runs B x x') (v1 : Value B (App Q1 f x'))
    (hy : Runs B y y') (v2 : Value B (App Q1 (App Q1 f x') y')) (hz : Runs B z z')
    (r : Runs B (App Q1 (App Q1 (App Q1 f x') y') z') v) :
    Runs B (App Q1 (App Q1 (App Q1 f x) y) z) v :=
  run_f (run2 v0 hx v1 hy (.refl v2)) (run_x v2 rfl hz r)

-- a def of the copy alone is a value, when its case tree takes an argument
private theorem vref (h : Contains B evalCopy) (hd : d ∈ evalCopy) (w : takes d.v = true) :
    Value B (Ref d.k) :=
  .call (xs := []) (h d hd) .nil (walk_iff.1 (walk_need w))

-- a def of the copy on one value is a value, when its walk needs more
private theorem vapp1 (h : Contains B evalCopy) (hd : d ∈ evalCopy) (vx : Value B x)
    (w : walk B d.v [] [(Q1, x)] = some none) : Value B (App Q1 (Ref d.k) x) :=
  .call (xs := [(Q1, _)]) (h d hd) (.cons (fun _ => vx) .nil) (walk_iff.1 w)

-- a def of the copy on two values is a value, when its walk needs more
private theorem vapp2 (h : Contains B evalCopy) (hd : d ∈ evalCopy) (vx : Value B x)
    (vy : Value B y)
    (w : walk B d.v [] [(Q1, x), (Q1, y)] = some none) : Value B (App Q1 (App Q1 (Ref d.k) x) y) :=
  .call (xs := [(Q1, _), (Q1, _)]) (h d hd) (.cons (fun _ => vx) (.cons (fun _ => vy) .nil))
    (walk_iff.1 w)

-- the and of two runs, by Bool.and
private theorem and_run (h : Contains B evalCopy) (hx : Runs B x (Form.bool a))
    (hy : Runs B y (Form.bool b)) :
    Runs B (App Q1 (App Q1 (Ref "Bool.and") x) y) (Form.bool (a && b)) :=
  run2 (vref (d := «evalCopy.Bool.and») h (by simp [evalCopy]) rfl) hx
    (vapp1 (d := «evalCopy.Bool.and») h (by simp [evalCopy]) value_bool (by
      cases a <;> simp [«evalCopy.Bool.and», walk, Form.bool, ctor, Quan.live, Quan.fld, takes]))
    hy (and_copy h)

-- the or of two runs, by Bool.or
private theorem or_run (h : Contains B evalCopy) (hx : Runs B x (Form.bool a))
    (hy : Runs B y (Form.bool b)) :
    Runs B (App Q1 (App Q1 (Ref "Bool.or") x) y) (Form.bool (a || b)) :=
  run2 (vref (d := «evalCopy.Bool.or») h (by simp [evalCopy]) rfl) hx
    (vapp1 (d := «evalCopy.Bool.or») h (by simp [evalCopy]) value_bool (by
      cases a <;> simp [«evalCopy.Bool.or», walk, Form.bool, ctor, Quan.live, Quan.fld, takes]))
    hy (or_copy h)

-- the or of a dead quantity and a run, by Bool.or, Bool.not and Quan.live
private theorem dead_or_run (h : Contains B evalCopy) (hy : Runs B y (Form.bool b)) :
    Runs B (App Q1 (App Q1 (Ref "Bool.or")
      (App Q1 (Ref "Bool.not") (App Q1 (Ref "Quan.live") (Form.quan q)))) y)
      (Form.bool (!q.live || b)) :=
  or_run h (run1 (vref (d := «evalCopy.Bool.not») h (by simp [evalCopy]) rfl) (live_copy h)
    (not_copy h)) hy

-- the form of a name is Data
private theorem data_name' : data (Form.name k) = true := data_iff.2 data_bytes

-- the form of a quantity is Data
private theorem data_quan' : data (Form.quan q) = true := data_iff.2 data_quan

-- the copy of value and args on a term that is no pair, application or reference
private theorem vals_other (h : Contains B evalCopy) (h1 : ∀ q x y, t ≠ Tup q x y)
    (h2 : ∀ q f x, t ≠ App q f x) (h3 : ∀ k, t ≠ Ref k) :
    Runs B (spine (Ref "Eval.vals") [(Q2, Form.defs bk.defs), (Q2, Form.term t), (Q1, Form.bool a)])
      (Form.bool (if a then args bk t else value bk t)) := by
  have hk : Book.get B "Eval.vals" = some «evalCopy.Eval.vals» :=
    h «evalCopy.Eval.vals» (by simp [evalCopy])
  have e : args bk t = false ∧ value bk t = (t.former != 0) := by
    cases t <;> simp_all [args, value]
  obtain ⟨c, r, eg, ht, ha, hr⟩ := term_tag t
  have c1 : c ≠ "Term.Tup" := fun hc => by obtain ⟨_, _, _, e⟩ := ht hc; exact h1 _ _ _ e
  have c2 : c ≠ "Term.App" := fun hc => by obtain ⟨_, _, _, e⟩ := ha hc; exact h2 _ _ _ e
  have c3 : c ≠ "Term.Ref" := fun hc => by obtain ⟨_, e⟩ := hr hc; exact h3 _ e
  have dr : data r = true := by
    have := data_term' (t := t); rw [eg] at this; simpa [data, Quan.live] using this
  have ho := h «evalCopy.Eval.vals.other» (by simp [evalCopy])
  refine .step (Eval.walk hk (xs := [(Q2, _), (Q2, _), (Q1, _)])
    (.cons (fun _ => value_defs) (.cons (fun _ => value_term) (.cons (fun _ => value_bool) .nil)))
    (by rw [eg]; simp [«evalCopy.Eval.vals», c1, c2, c3, dr, walk, bindsAt, Quan.live, Quan.fld,
      takes, data, data_defs', Form.bool, ctor, Term.sub, Env.sub, Term.spine] <;> rfl)) ?_
  have rf := is_former_copy (t := t) h
  rw [eg] at rf
  refine run2 (vref (d := «evalCopy.Eval.vals.other») h (by simp [evalCopy]) rfl) (.refl value_bool)
    (vapp1 (d := «evalCopy.Eval.vals.other») h (by simp [evalCopy]) value_bool (by
      cases a <;> simp [«evalCopy.Eval.vals.other», walk, Quan.live, Quan.fld, takes])) rf ?_
  cases a
  · simp only [Bool.false_eq_true, ↓reduceIte, e]
    exact .step (Eval.walk ho (xs := [(Q1, _), (Q1, _)])
      (.cons (fun _ => .tup (fun _ => .lab) .lab) (.cons (fun _ => value_bool) .nil))
      (by simp [«evalCopy.Eval.vals.other», walk, bindsAt, Quan.live, Quan.fld, takes, data,
        Form.bool, ctor, Term.sub, Env.sub, Term.spine] <;> rfl)) (.refl value_bool)
  · simp only [↓reduceIte, e]
    exact .step (Eval.walk ho (xs := [(Q1, _), (Q1, _)])
      (.cons (fun _ => .tup (fun _ => .lab) .lab) (.cons (fun _ => value_bool) .nil))
      (by simp [«evalCopy.Eval.vals.other», walk, bindsAt, Quan.live, Quan.fld, takes, data,
        Form.bool, ctor, Term.sub, Term.spine] <;> rfl)) (.refl (value_bool (b := false)))

theorem vals_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Eval.vals") [(Q2, Form.defs bk.defs), (Q2, Form.term t), (Q1, Form.bool a)])
      (Form.bool (if a then args bk t else value bk t)) := by
  have hk : Book.get B "Eval.vals" = some «evalCopy.Eval.vals» :=
    h «evalCopy.Eval.vals» (by simp [evalCopy])
  induction t generalizing a with
  | Tup q x y ihx ihy =>
    cases a
    · refine .step (Eval.walk hk (xs := [(Q2, _), (Q2, _), (Q1, _)])
        (.cons (fun _ => value_defs) (.cons (fun _ => value_term)
          (.cons (fun _ => value_bool) .nil)))
        (by simp [«evalCopy.Eval.vals», walk, bindsAt, Quan.live, Quan.fld, takes, data_term',
          data_defs', data_quan', Form.term, Form.bool, ctor, Term.sub, Env.sub,
            Term.spine] <;> rfl)) ?_
      simp only [Bool.false_eq_true, ↓reduceIte, value]
      exact and_run h (dead_or_run h (ihx (a := false))) (ihy (a := false))
    · refine .step (Eval.walk hk (xs := [(Q2, _), (Q2, _), (Q1, _)])
        (.cons (fun _ => value_defs) (.cons (fun _ => value_term)
          (.cons (fun _ => value_bool) .nil)))
        (by simp [«evalCopy.Eval.vals», walk, bindsAt, Quan.live, Quan.fld, takes, data_term',
          data_defs', data_quan', Form.term, Form.bool, ctor, Term.sub, Term.spine] <;> rfl)) ?_
      simp only [↓reduceIte, args]
      exact .refl (value_bool (b := false))
  | App q f x ihf ihx =>
    have ha := h «evalCopy.Eval.vals.app» (by simp [evalCopy])
    have rf := ihf (a := true)
    have rx := ihx (a := false)
    simp only [↓reduceIte, Bool.false_eq_true] at rf rx
    refine .step (Eval.walk hk (xs := [(Q2, _), (Q2, _), (Q1, _)])
      (.cons (fun _ => value_defs) (.cons (fun _ => value_term) (.cons (fun _ => value_bool) .nil)))
      (by simp [«evalCopy.Eval.vals», walk, bindsAt, Quan.live, Quan.fld, takes, data, data_term',
        data_defs', data_quan', Form.term, Form.bool, ctor, Term.sub, Env.sub,
        Term.spine] <;> rfl)) ?_
    refine run3 (vref (d := «evalCopy.Eval.vals.app») h (by simp [evalCopy]) rfl) (.refl value_bool)
      (vapp1 (d := «evalCopy.Eval.vals.app») h (by simp [evalCopy]) value_bool (by
        cases a <;> simp [«evalCopy.Eval.vals.app», walk, Quan.live, Quan.fld, takes]))
      (and_run h rf (dead_or_run h rx))
      (vapp2 (d := «evalCopy.Eval.vals.app») h (by simp [evalCopy]) value_bool value_bool (by
        cases a <;> simp [«evalCopy.Eval.vals.app», walk, bindsAt, Quan.live, Quan.fld, takes,
          data, Form.bool, ctor]))
      (callWalk_copy (t := App q f x) h) ?_
    cases a
    · simp only [Bool.false_eq_true, ↓reduceIte, value]
      refine .step (Eval.walk ha (xs := [(Q1, _), (Q1, _), (Q1, _)])
        (u := App Q1 (App Q1 (Ref "Bool.and") (Form.bool (args bk f && (!q.live || value bk x))))
          (App Q1 (Ref "Eval.waits") (Form.maybe (Form.maybe Form.term) (callWalk bk (App q f x)))))
        (.cons (fun _ => .tup (fun _ => .lab) .lab) (.cons (fun _ => value_bool)
          (.cons (fun _ => value_maybe fun _ => value_maybe fun _ => value_term) .nil)))
        (by simp [«evalCopy.Eval.vals.app», walk, bindsAt, Quan.live, Quan.fld, takes, data,
          Form.bool, Form.maybe, ctor, Term.sub, Env.sub, Term.spine] <;> rfl)) ?_
      exact and_run h (.refl value_bool) (waits_copy h)
    · simp only [↓reduceIte, args]
      exact .step (Eval.walk ha (xs := [(Q1, _), (Q1, _), (Q1, _)])
        (.cons (fun _ => .tup (fun _ => .lab) .lab) (.cons (fun _ => value_bool)
          (.cons (fun _ => value_maybe fun _ => value_maybe fun _ => value_term) .nil)))
        (by simp [«evalCopy.Eval.vals.app», walk, bindsAt, Quan.live, Quan.fld, takes, data,
          Form.bool, Form.maybe, ctor, Term.sub, Env.sub, Term.spine] <;> rfl)) (.refl value_bool)
  | Ref k =>
    have hr := h «evalCopy.Eval.vals.ref» (by simp [evalCopy])
    refine .step (Eval.walk hk (xs := [(Q2, _), (Q2, _), (Q1, _)])
      (.cons (fun _ => value_defs) (.cons (fun _ => value_term) (.cons (fun _ => value_bool) .nil)))
      (by simp [«evalCopy.Eval.vals», walk, bindsAt, Quan.live, Quan.fld, takes, data, data_defs',
        Form.term, Form.bool, data_name', ctor, Term.sub, Env.sub, Term.spine] <;> rfl)) ?_
    refine run2 (vref (d := «evalCopy.Eval.vals.ref») h (by simp [evalCopy]) rfl) (.refl value_bool)
      (vapp1 (d := «evalCopy.Eval.vals.ref») h (by simp [evalCopy]) value_bool (by
        cases a <;> simp [«evalCopy.Eval.vals.ref», walk, Quan.live, Quan.fld, takes]))
      (callWalk_copy (t := Ref k) h) ?_
    cases a
    · simp only [Bool.false_eq_true, ↓reduceIte, value]
      refine .step (Eval.walk hr (xs := [(Q1, _), (Q1, _)])
        (u := App Q1 (Ref "Eval.waits") (Form.maybe (Form.maybe Form.term) (callWalk bk (Ref k))))
        (.cons (fun _ => .tup (fun _ => .lab) .lab)
          (.cons (fun _ => value_maybe fun _ => value_maybe fun _ => value_term) .nil))
        (by simp [«evalCopy.Eval.vals.ref», walk, bindsAt, Quan.live, Quan.fld, takes, Form.maybe,
          ctor, Term.sub, Env.sub, Term.spine] <;> rfl)) ?_
      exact waits_copy h
    · simp only [↓reduceIte, args]
      exact .step (Eval.walk hr (xs := [(Q1, _), (Q1, _)])
        (.cons (fun _ => .tup (fun _ => .lab) .lab)
          (.cons (fun _ => value_maybe fun _ => value_maybe fun _ => value_term) .nil))
        (by simp [«evalCopy.Eval.vals.ref», walk, bindsAt, Quan.live, Quan.fld, takes, Form.bool,
          Form.maybe, ctor, Term.sub, Term.spine] <;> rfl)) (.refl (value_bool (b := true)))
  | _ => exact vals_other h (by simp) (by simp) (by simp)

theorem call_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Eval.call") [(Q2, Form.defs bk.defs), (Q2, Form.term t)])
      (Form.maybe Form.term (call bk t)) := by
  have hk := h «evalCopy.Eval.call» (by simp [evalCopy])
  have hi := h «evalCopy.Eval.call.if» (by simp [evalCopy])
  have rv := vals_copy (bk := bk) (t := t) (a := true) h
  simp only [↓reduceIte] at rv
  refine .step (Eval.walk hk (xs := [(Q2, _), (Q2, _)])
    (.cons (fun _ => value_defs) (.cons (fun _ => value_term) .nil))
    (by simp [«evalCopy.Eval.call», walk, bindsAt, Quan.live, takes, data_term', data_defs',
      Term.sub, Env.sub, Term.spine] <;> rfl)) ?_
  refine run2 (vref (d := «evalCopy.Eval.call.if») h (by simp [evalCopy]) rfl) rv
    (vapp1 (d := «evalCopy.Eval.call.if») h (by simp [evalCopy]) value_bool (by
      cases args bk t <;> simp [«evalCopy.Eval.call.if», walk, bindsAt, Quan.live, Quan.fld,
        takes, data, Form.bool, ctor]))
    (callWalk_copy h) ?_
  refine .step (Eval.walk hi (xs := [(Q1, _), (Q1, _)]) (u := Form.maybe Form.term (call bk t))
    (.cons (fun _ => value_bool)
      (.cons (fun _ => value_maybe fun _ => value_maybe fun _ => value_term) .nil))
    ?_) (.refl (value_maybe fun _ => value_term))
  unfold call
  cases args bk t <;> rcases callWalk bk t with _ | _ | _ <;> simp [«evalCopy.Eval.call.if», walk,
    bindsAt, Quan.live, Quan.fld, takes, data, data_term', Form.bool, Form.maybe, Form.some, ctor,
    Term.sub, Env.sub, Term.spine]

-- the first field of a pair takes its steps, when it is live
private theorem steps_tup_a (l : q.live = true) (h : Steps B n a a') :
    Steps B n (Tup q a b) (Tup q a' b) := by
  induction h with
  | refl => exact .refl
  | step e _ ih => exact .step (.tup_a l e) ih

-- the second field of a pair takes its steps, after a first that is a value
private theorem steps_tup_b (va : q.live = true → Value B a) (h : Steps B n b b') :
    Steps B n (Tup q a b) (Tup q a b') := by
  induction h with
  | refl => exact .refl
  | step e _ ih => exact .step (.tup_b va e) ih

-- the form of a split's result, with its quantity still a call, runs to that form
private theorem split_run (hr : Runs B F (Form.quan p)) :
    Runs B (Tup Q1 (Lab "Term.App") (Tup Q1 (Form.quan q) (Tup Q1 (Tup Q1 (Lab "Term.App")
      (Tup Q1 F (Tup Q1 (Form.term h) (Tup Q1 (Form.term a) (Lab "()")))))
      (Tup Q1 (Form.term b) (Lab "()")))))
      (Form.term (App q (App p h a) b)) :=
  have ⟨_, s, _⟩ := hr
  ⟨_, steps_tup_b (fun _ => .lab) (steps_tup_b (fun _ => value_quan) (steps_tup_a rfl
    (steps_tup_b (fun _ => .lab) (steps_tup_a rfl s)))), value_term⟩

-- the if of Eval.redex on a Bool alone is a value
private theorem value_redex_if (h : Contains B evalCopy) :
    Value B (App Q1 (Ref "Eval.redex.if") (Form.bool b)) :=
  vapp1 (d := «evalCopy.Eval.redex.if») h (by simp [evalCopy]) value_bool (by
    cases b <;> simp [«evalCopy.Eval.redex.if», walk, Quan.live, Quan.fld, takes, Form.bool, ctor])

-- the if of Eval.redex on two runs gives the Maybe of the second
private theorem redex_if_run (h : Contains B evalCopy) (hb : Runs B y (Form.bool b))
    (hu : Runs B z (Form.term u)) :
    Runs B (App Q1 (App Q1 (Ref "Eval.redex.if") y) z)
      (Form.maybe Form.term (if b then some u else none)) :=
  run2 (vref (d := «evalCopy.Eval.redex.if») h (by simp [evalCopy]) rfl) hb (value_redex_if h) hu
    (.step (Eval.walk (h «evalCopy.Eval.redex.if» (by simp [evalCopy])) (xs := [(Q1, _), (Q1, _)])
      (u := Form.maybe Form.term (if b then some u else none))
      (.cons (fun _ => value_bool) (.cons (fun _ => value_term) .nil))
      (by cases b <;> simp [«evalCopy.Eval.redex.if», walk, bindsAt, Quan.live, Quan.fld, takes,
        data_term', Form.bool, Form.maybe, Form.some, ctor, Term.sub, Env.sub,
        Term.spine])) (.refl (value_maybe fun _ => value_term)))

-- the pick of Eval.redex on a run of a Bool and two forms of terms
private theorem redex_pick_run (h : Contains B evalCopy) (hb : Runs B y (Form.bool b)) :
    Runs B (App Q1 (App Q1 (App Q1 (Ref "Eval.redex.pick") y) (Form.term u)) (Form.term w))
      (Form.term (if b then u else w)) := by
  have hp := h «evalCopy.Eval.redex.pick» (by simp [evalCopy])
  refine run3 (vref (d := «evalCopy.Eval.redex.pick») h (by simp [evalCopy]) rfl) hb
    (vapp1 (d := «evalCopy.Eval.redex.pick») h (by simp [evalCopy]) value_bool (by
      cases b <;> simp [«evalCopy.Eval.redex.pick», walk, Quan.live, Quan.fld, takes, Form.bool,
        ctor])) (.refl value_term)
    (vapp2 (d := «evalCopy.Eval.redex.pick») h (by simp [evalCopy]) value_bool value_term (by
      cases b <;> simp [«evalCopy.Eval.redex.pick», walk, bindsAt, Quan.live, Quan.fld, takes,
        data_term', Form.bool, ctor])) (.refl value_term)
    (.step (Eval.walk hp (xs := [(Q1, _), (Q1, _), (Q1, _)]) (u := Form.term (if b then u else w))
      (.cons (fun _ => value_bool) (.cons (fun _ => value_term) (.cons (fun _ => value_term) .nil)))
      (by cases b <;> simp [«evalCopy.Eval.redex.pick», walk, bindsAt, Quan.live, Quan.fld, takes,
        Form.bool, ctor, Term.sub, Env.sub, Term.spine])) (.refl value_term))

-- the copy of redex, when its walk ends in a call
private theorem redex_call (h : Contains B evalCopy)
    (w : walk B «evalCopy.Eval.redex».v []
      [(Q1, Form.defs bk.defs), (Q2, Form.quan q), (Q2, Form.term f), (Q2, Form.term x)] =
      some (some (App Q2 (App Q2 (Ref "Eval.call") (Form.defs bk.defs)) (Form.term (App q f x)))))
    (e : redex bk q f x = call bk (App q f x)) :
    Runs B (spine (Ref "Eval.redex")
        [(Q1, Form.defs bk.defs), (Q2, Form.quan q), (Q2, Form.term f), (Q2, Form.term x)])
      (Form.maybe Form.term (redex bk q f x)) := by
  rw [e]
  exact .step (Eval.walk (h «evalCopy.Eval.redex» (by simp [evalCopy]))
    (.cons (fun _ => value_defs) (.cons (fun _ => value_quan) (.cons (fun _ => value_term)
      (.cons (fun _ => value_term) .nil)))) w) (call_copy h)

theorem redex_copy (h : Contains B evalCopy) :
    Runs B (spine (Ref "Eval.redex")
        [(Q1, Form.defs bk.defs), (Q2, Form.quan q), (Q2, Form.term f), (Q2, Form.term x)])
      (Form.maybe Form.term (redex bk q f x)) := by
  have hk := h «evalCopy.Eval.redex» (by simp [evalCopy])
  have vs : Values B [(Q1, Form.defs bk.defs), (Q2, Form.quan q), (Q2, Form.term f), (Q2,
    Form.term x)] :=
    .cons (fun _ => value_defs) (.cons (fun _ => value_quan) (.cons (fun _ => value_term)
      (.cons (fun _ => value_term) .nil)))
  obtain ⟨c, r, eg, -, -, -⟩ := term_tag f
  obtain ⟨d, s, ex, ht, -, -⟩ := term_tag x
  have dr : data r = true := by
    have := data_term' (t := f); rw [eg] at this; simpa [data, Quan.live] using this
  have ds : data s = true := by
    have := data_term' (t := x); rw [ex] at this; simpa [data, Quan.live] using this
  by_cases hl : ∃ p b, f = Lam p b
  · obtain ⟨p, b, rfl⟩ := hl
    refine .step (Eval.walk hk vs (u := App Q1 (App Q1 (Ref "Eval.redex.if")
        (spine (Ref "Quan.binds") [(Q2, Form.quan p), (Q1, Form.quan q), (Q1, Form.term x)]))
        (spine (Ref "Term.inst") [(Q1, Form.term b), (Q1, Form.term x)]))
      (by simp [«evalCopy.Eval.redex», walk, bindsAt, Quan.live, Quan.fld, takes, data_term',
        data_defs', data_quan', Form.term, ctor, Term.sub, Env.sub, Term.spine])) ?_
    simpa [redex] using redex_if_run h (binds_copy h) (inst_copy h)
  by_cases hp : ∃ g, f = Prj g
  · obtain ⟨g, rfl⟩ := hp
    by_cases hd : d = "Term.Tup"
    · obtain ⟨r', a, b, rfl⟩ := ht hd
      refine .step (Eval.walk hk vs (u := App Q1 (App Q1 (Ref "Eval.redex.if")
          (App Q1 (Ref "Quan.live") (Form.quan q)))
          (Tup Q1 (Lab "Term.App") (Tup Q1 (Form.quan q) (Tup Q1 (Tup Q1 (Lab "Term.App")
            (Tup Q1 (spine (Ref "Quan.fld") [(Q1, Form.quan r'), (Q1, Form.quan q)])
              (Tup Q1 (Form.term g) (Tup Q1 (Form.term a) (Lab "()")))))
            (Tup Q1 (Form.term b) (Lab "()"))))))
        (by simp [«evalCopy.Eval.redex», walk, bindsAt, Quan.live, Quan.fld, takes, data_term',
          data_defs', data_quan', Form.term, ctor, Term.sub, Env.sub, Term.spine])) ?_
      simpa [redex, Term.spine] using redex_if_run h (live_copy h) (split_run (fld_copy h))
    · refine redex_call h ?_ (by cases x <;> simp_all [redex, Form.term, ctor])
      simp [«evalCopy.Eval.redex», hd, ds, ex, walk, bindsAt, Quan.live, Quan.fld, takes, data,
        data_term', data_defs', data_quan', Form.term, ctor, Term.sub, Env.sub, Term.spine]
  by_cases hm : ∃ k g m, f = Mat k g m
  · obtain ⟨k, g, m, rfl⟩ := hm
    by_cases hj : ∃ j, x = Lab j
    · obtain ⟨j, rfl⟩ := hj
      refine .step (Eval.walk hk vs (u := App Q1 (App Q1 (Ref "Eval.redex.if")
          (App Q1 (Ref "Quan.live") (Form.quan q)))
          (App Q1 (App Q1 (App Q1 (Ref "Eval.redex.pick")
            (App Q1 (App Q1 (Ref "Name.is_eq") (Form.name j)) (Form.name k)))
            (Form.term g)) (Form.term (App q m (Lab j)))))
        (by simp [«evalCopy.Eval.redex», walk, bindsAt, Quan.live, Quan.fld, takes, data_term',
          data_defs', data_quan', data_name', Form.term, ctor, Term.sub, Env.sub, Term.spine])) ?_
      simpa [redex, Term.spine] using
        redex_if_run h (live_copy h) (redex_pick_run h (name_is_eq_copy h))
    · have hd : d ≠ "Term.Lab" := by rintro rfl; cases x <;> simp_all [Form.term, ctor]
      refine redex_call h ?_ (by cases x <;> simp_all [redex, Form.term, ctor])
      simp [«evalCopy.Eval.redex», hd, ds, ex, walk, bindsAt, Quan.live, Quan.fld, takes, data,
        data_term', data_defs', data_quan', data_name', Form.term, ctor, Term.sub, Env.sub,
        Term.spine]
  have c1 : c ≠ "Term.Lam" := by rintro rfl; cases f <;> simp_all [Form.term, ctor]
  have c2 : c ≠ "Term.Prj" := by rintro rfl; cases f <;> simp_all [Form.term, ctor]
  have c3 : c ≠ "Term.Mat" := by rintro rfl; cases f <;> simp_all [Form.term, ctor]
  refine redex_call h ?_ (by cases f <;> simp_all [redex])
  simp [«evalCopy.Eval.redex», c1, c2, c3, dr, eg, walk, bindsAt, Quan.live, Quan.fld, takes,
    data, data_term', data_defs', data_quan', Form.term, ctor, Term.sub, Env.sub, Term.spine]

end EvalCopy
