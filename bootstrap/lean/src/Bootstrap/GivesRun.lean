import Bootstrap.Unbytes

-- GivesRun
-- ========
--
-- Program.gives(p, i, n), on the bytes p that the Lean writer writes for the
-- book bk, gives Some{o} exactly when Lean's Gives bk i o n.

open Quan Term

set_option linter.unusedSimpArgs false
set_option maxRecDepth 20000

namespace Gives

-- what Program.gives computes, in Lean: the bytes of the value that the run
-- from start i reaches after exactly n steps of step, if any
def givesL (bk : Book) (i : List UInt8) (n : Nat) : Option (List UInt8) :=
  (EvalCopy.iterate bk n (start i)).bind fun v => if value bk v then unbytes v else none

theorem result_run (h : Holds B) {bk : Book} (r : Runs B R (Form.maybe Form.term o)) :
    Runs B (App Q1 (App Q1 (Ref "Program.result") (Form.defs bk.defs)) R)
      (Form.maybe bytes (o.bind fun v => if value bk v then unbytes v else none)) := by
  have hk := h.get (d := «programCopy.Program.result»)
  have hi := h.get (d := «programCopy.Program.result.if»)
  show Runs B (spine (Ref _) [(Q1, _), (Q1, _)]) _
  refine Kit.runs_args hk (.v rfl value_defs (.r rfl r .nil)) ?_ ?_
  · intro m hm; simp at hm
    rcases o with _ | v <;> rcases m with _ | _ | m <;> first | omega | walks' «programCopy.Program.result»
  rcases o with _ | v
  · exact Kit.call hk (.cons (fun _ => value_defs) (.cons (fun _ => value_maybe' (fun _ => value_term)) .nil))
      (u := ctor "None" []) (by walks' «programCopy.Program.result») ctor0
  refine Kit.call hk (.cons (fun _ => value_defs) (.cons (fun _ => value_maybe' (fun _ => value_term)) .nil))
    (u := App Q1 (App Q1 (Ref "Program.result.if")
      (spine (Ref "Eval.vals") [(Q2, Form.defs bk.defs), (Q2, Form.term v), (Q1, Form.bool false)])) (Form.term v))
    (by simp [«programCopy.Program.result», walk, list, ctor, bindsAt, Quan.live, Quan.fld, takes,
      Term.sub, Env.sub, Term.spine, Form.term, Form.some, Form.maybe, Form.bool, data, ddefs, dterm]) ?_
  show Runs B (spine (Ref _) [(Q1, _), (Q1, _)]) _
  have rv := EvalCopy.vals_copy (bk := bk) (t := v) (a := false) h.eval
  simp only [Bool.false_eq_true, ↓reduceIte] at rv
  refine Kit.runs_args hi (.r rfl rv (.v rfl value_term .nil)) ?_ ?_
  · intro m hm; simp at hm
    rcases m with _ | _ | m <;> first | omega | (cases value bk v <;> walks' «programCopy.Program.result.if»)
  cases hv : value bk v
  · exact Kit.call hi (.cons (fun _ => value_bool) (.cons (fun _ => value_term) .nil)) (u := ctor "None" [])
      (by walks' «programCopy.Program.result.if») (Kit.runs_eq ctor0 (by simp [hv]; rfl))
  · exact Kit.call hi (.cons (fun _ => value_bool) (.cons (fun _ => value_term) .nil))
      (u := App Q1 (Ref "Program.unbytes") (Form.term v))
      (by walks' «programCopy.Program.result.if») (Kit.runs_eq (unbytes_run h) (by simp [hv]))

theorem gives_run (h : Holds B) :
    Runs B (spine (Ref "Program.gives") [(Q1, bytes (write bk)), (Q1, bytes i), (Q1, Form.nat n)])
      (Form.maybe bytes (givesL bk i n)) := by
  have hk := h.get (d := «programCopy.Program.gives»)
  have ho := h.get (d := «programCopy.Program.gives.of»)
  have hs : Book.get B "Eval.steps" = some «evalCopy.Eval.steps» := h.eval «evalCopy.Eval.steps» (by simp [evalCopy])
  refine Kit.call hk (.cons (fun _ => value_bytes) (.cons (fun _ => value_bytes) (.cons (fun _ => value_nat) .nil)))
    (u := spine (Ref "Program.gives.of") [(Q1, App Q1 (Ref "Book.read") (bytes (write bk))), (Q1, bytes i),
      (Q1, Form.nat n)]) (by walks' «programCopy.Program.gives») ?_
  refine Kit.runs_args ho (.r rfl (read_write h.reader) (.v rfl value_bytes (.v rfl value_nat .nil))) ?_ ?_
  · intro m hm; simp at hm
    rcases m with _ | _ | _ | m <;> first | omega | simp [«programCopy.Program.gives.of», walk, list, ctor,
      bindsAt, Quan.live, Quan.fld, takes, Form.some, Form.maybe, data, ddefs, dbytes, dnat]
  refine Kit.call ho (.cons (fun _ => value_ctor (by simp [value_defs])) (.cons (fun _ => value_bytes)
    (.cons (fun _ => value_nat) .nil)))
    (u := App Q1 (App Q1 (Ref "Program.result") (Form.defs bk.defs)) (App Q1 (App Q1 (App Q1 (Ref "Eval.steps")
      (Form.nat n)) (Form.defs bk.defs)) (App Q1 (Ref "Program.start") (bytes i))))
    (by simp [«programCopy.Program.gives.of», walk, list, ctor, bindsAt, Quan.live, Quan.fld, takes,
      Term.sub, Env.sub, Term.spine, Form.term, Form.some, Form.maybe, Form.bool, data, ddefs, dterm, dbytes, dnat]) ?_
  refine result_run h ?_
  show Runs B (spine (Ref _) [(Q1, _), (Q1, _), (Q1, _)]) _
  refine Kit.runs_args hs (.v rfl value_nat (.v rfl value_defs (.r rfl (start_run h) .nil))) ?_
    (EvalCopy.steps_copy h.eval)
  intro m hm; simp at hm
  rcases m with _ | _ | _ | m <;> first | omega | simp [«evalCopy.Eval.steps», walk, takes, bindsAt, Quan.live]

theorem maybe_bytes_inj : Form.maybe bytes o = Form.some (bytes x) → o = some x := by
  cases o with
  | none => simp [Form.maybe, Form.some, ctor]
  | some y =>
    intro e
    simp only [Form.maybe, Form.some, ctor, Tup.injEq, List.foldr, true_and, and_true] at e
    have := congrArg unbytes e
    rw [unbytes_bytes, unbytes_bytes] at this
    rw [Option.some.inj this]

-- exactly n steps of step are exactly n steps of Eval (as EvalSteps' own)
theorem iterate_iff : EvalCopy.iterate bk n t = some u ↔ Steps bk n t u := by
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

theorem givesL_iff : givesL bk i n = some o ↔ Gives bk i o n := by
  simp only [givesL, Option.bind_eq_some_iff, Gives]
  constructor
  · rintro ⟨v, hv, hu⟩
    split at hu
    · exact ⟨v, iterate_iff.1 hv, value_iff.1 ‹_›, hu⟩
    · cases hu
  · rintro ⟨v, hs, hv, hu⟩
    exact ⟨v, iterate_iff.2 hs, by simp [value_iff.2 hv, hu]⟩

-- the bridge: in a book that holds the copies, Program.gives(write bk, i, n)
-- runs to Some{o} exactly when bk gives o on i after n steps
theorem gives_iff (h : Holds B) :
    Runs B (spine (Ref "Program.gives") [(Q1, bytes (write bk)), (Q1, bytes i), (Q1, Form.nat n)])
      (Form.some (bytes o)) ↔ Gives bk i o n := by
  rw [← givesL_iff]
  constructor
  · intro r; exact maybe_bytes_inj (Kit.runs_det (gives_run h) r)
  · intro e; have := gives_run (bk := bk) (i := i) (n := n) h; rw [e] at this; exact this

end Gives
