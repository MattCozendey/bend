import Bootstrap.EvalSteps.Step

-- EvalSteps
-- =========
--
-- INVARIANTS #2: Eval.steps, the Bend copy of Eval
-- (bootstrap/bend/src/compiler), gives what the kernel's Eval gives,
-- after the same number of steps, in both directions. The proof goes through
-- step (Bootstrap/Interp.lean), which the copy follows case for case
-- (src/Bootstrap/EvalSteps/).

open Quan Term

-- a chain of fields that ends in () gives back its fields
private theorem fields_inj {fs fs' : List Term} :
    fs.foldr (Tup Q1) (Lab "()") = fs'.foldr (Tup Q1) (Lab "()") → fs = fs' := by
  induction fs generalizing fs' with
  | nil => cases fs' <;> simp
  | cons f fs ih =>
    cases fs' with
    | nil => simp
    | cons f' fs' => simp only [List.foldr_cons, Tup.injEq]; exact fun h => by rw [h.2.1, ih h.2.2]

-- constructors with equal forms have equal labels and fields
private theorem ctor_inj : ctor k fs = ctor k' fs' → k = k' ∧ fs = fs' := by
  intro h
  simp only [ctor, Term.Tup.injEq, Term.Lab.injEq] at h
  exact ⟨h.2.1, fields_inj h.2.2⟩

-- the form of a nat says which nat it is
private theorem nat_inj {a b : Nat} : Form.nat a = Form.nat b → a = b := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => intro; rfl
    | succ m => intro h; simp only [Form.nat] at h; have := (ctor_inj h).1; simp at this
  | succ n ih =>
    cases b with
    | zero => intro h; simp only [Form.nat] at h; have := (ctor_inj h).1; simp at this
    | succ m => intro h; have := (ctor_inj h).2; simp at this; exact congrArg (· + 1) (ih this)

-- the form of a quantity says which quantity it is
private theorem quan_inj {a b : Quan} : Form.quan a = Form.quan b → a = b := by
  cases a <;> cases b <;> intro h <;> have := (ctor_inj h).1 <;> simp_all [Form.quan]

-- the form of a list says which list it is
private theorem list_inj {xs ys : List Term} : list xs = list ys → xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> intro h <;> have := (ctor_inj h).1 <;> simp_all [list]
  | cons x xs ih =>
    cases ys with
    | nil => intro h; have := (ctor_inj h).1; simp_all [list]
    | cons y ys => intro h; have := (ctor_inj h).2; simp at this; rw [this.1, ih this.2]

-- the form of a list of names says which names they are
private theorem names_inj {ks ks' : List String} :
    list (ks.map Form.name) = list (ks'.map Form.name) → ks = ks' := by
  intro h
  replace h := list_inj h
  induction ks generalizing ks' with
  | nil => cases ks' <;> simp_all
  | cons k ks ih =>
    cases ks' with
    | nil => simp at h
    | cons k' ks' => simp at h; rw [EvalCopy.name_inj h.1, ih h.2]

-- the form of a term says which term it is
private theorem term_inj {a b : Term} : Form.term a = Form.term b → a = b := by
  induction a generalizing b <;> cases b <;> intro h <;> (try rfl) <;> simp only [Form.term] at h <;>
    have ⟨hk, hf⟩ := ctor_inj h <;> (try simp at hk) <;>
    revert hf <;> simp only [List.cons.injEq, and_true, and_imp] <;> intros <;>
    simp only [Term.Var.injEq, Term.Ref.injEq, Term.Ann.injEq, Term.Let.injEq, Term.Typ.injEq,
      Term.Min.injEq, Term.All.injEq, Term.Lam.injEq, Term.App.injEq, Term.Sig.injEq,
      Term.Tup.injEq, Term.Prj.injEq, Term.Enu.injEq, Term.Lab.injEq, Term.Mat.injEq,
      Term.Eql.injEq, Term.Rwt.injEq] <;>
    (try refine ⟨?_, ?_, ?_⟩) <;> (try refine ⟨?_, ?_⟩) <;>
    first
      | rfl
      | exact nat_inj ‹_›
      | exact quan_inj ‹_›
      | exact names_inj ‹_›
      | exact EvalCopy.name_inj ‹_›
      | (apply_assumption; assumption)

-- a maybe of terms that is some term u was some u
private theorem maybe_term_some {o : Option Term} :
    Form.maybe Form.term o = Form.some (Form.term u) → o = some u := by
  cases o with
  | none => intro h; have := (ctor_inj h).1; simp at this
  | some x =>
    intro h; simp only [Form.maybe, Form.some] at h
    have := (ctor_inj h).2; simp only [List.cons.injEq, and_true] at this
    rw [term_inj this]

-- n steps of step are n steps of Eval
private theorem iterate_iff : EvalCopy.iterate bk n t = some u ↔ Steps bk n t u := by
  induction n generalizing t with
  | zero =>
    simp only [EvalCopy.iterate, Option.some.injEq]
    exact ⟨fun h => h ▸ .refl, fun h => by cases h; rfl⟩
  | succ n ih =>
    simp only [EvalCopy.iterate, Option.bind_eq_some_iff]
    constructor
    · rintro ⟨v, hv, hs⟩; exact .step (step_iff.1 hv) (ih.1 hs)
    · intro h; cases h with
      | step e s => exact ⟨_, step_iff.2 e, ih.2 s⟩

-- in a book that holds the copy of Eval, the copy says that t reaches u after
-- n steps exactly when the kernel's Eval says so
theorem copy_steps : Contains B evalCopy →
    (Runs B (App Q1 (App Q1 (App Q1 (Ref "Eval.steps") (Form.nat n)) (Form.defs bk.defs)) (Form.term t))
      (Form.some (Form.term u)) ↔ Steps bk n t u) := by
  intro h
  rw [← iterate_iff]
  constructor
  · rintro ⟨m, s, v⟩
    have ⟨m', s', v'⟩ := EvalCopy.steps_copy (n := n) (bk := bk) (t := t) h
    exact maybe_term_some (steps_det s' v' s v).2
  · intro hi
    have := EvalCopy.steps_copy (n := n) (bk := bk) (t := t) h
    rwa [hi] at this
