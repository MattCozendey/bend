import Bootstrap.Read.Nat
import Bootstrap.Read.TokenLow
import Bootstrap.Read.TokenMiddle
import Bootstrap.Read.TokenHigh

-- Read.Go
-- =======
--
-- Book.read.go, the reader's loop, on a stack of values, does what the model
-- does.

open Quan Term

-- Book.read.go on its bytes alone is a value: it waits for its stack
theorem value_go : Contains B reader → Value B (App Q1 (Ref "Book.read.go") (bytes xs)) := by
  intro h
  have hk := h «reader.Book.read.go» (by simp [reader])
  refine Value.call (xs := [(Q1, bytes xs)]) hk (.cons (fun _ => value_bytes) .nil) (walk_iff.1 ?_)
  rcases xs with _ | ⟨_, _ | ⟨_, _⟩⟩ <;>
    simp [«reader.Book.read.go», walk, bytes, list, ctor, cell, bindsAt, Quan.live, takes, data, Quan.fld]

-- Book.read.token alone is a value
theorem value_token : Contains B reader → Value B (Ref "Book.read.token") := by
  intro h
  have hk := h «reader.Book.read.token» (by simp [reader])
  exact Value.call (xs := []) hk .nil (walk_iff.1 (by simp [«reader.Book.read.token», walk, takes]))

-- Book.read.token, on a stack of values, does what the model does, for every tag
theorem token_run : Contains B reader → (∀ x ∈ s, Value B x) → Read.token t b s = some s' →
    Runs B (App Q1 (App Q1 (App Q1 (Ref "Book.read.token") (Form.nat t)) (list s)) (cell b))
      (Form.some (list s')) := by
  intro h hs e
  by_cases h1 : t ≤ 10
  · exact token_low h h1 hs e
  by_cases h2 : t ≤ 21
  · exact token_middle h (by omega) h2 hs e
  · exact token_high h (by omega) hs e

-- Book.read.step on a stack of values does what the model's token does
theorem step_run : Contains B reader → (∀ x ∈ s, Value B x) → Read.token t.toNat b s = some s' →
    ∃ n, Steps B n
      (App Q1 (App Q1 (App Q1 (Ref "Book.read.step") (Form.some (list s))) (cell t)) (cell b))
      (Form.some (list s')) ∧ Value B (Form.some (list s')) := by
  intro h hs e
  have hk := h «reader.Book.read.step» (by simp [reader])
  have ev : Eval B (spine (Ref "Book.read.step")
      [(Q1, Form.some (list s)), (Q1, cell t), (Q1, cell b)])
      (App Q1 (App Q1 (App Q1 (Ref "Book.read.token") (App Q1 (Ref "U32.to_nat") (cell t)))
        (list s)) (cell b)) := by
    refine Eval.walk hk (.cons (fun _ => ?_) (.cons (fun _ => value_cell) (.cons (fun _ => value_cell) .nil))) ?_
    · exact value_ctor (by simpa using value_list hs)
    · simp [«reader.Book.read.step», walk, Form.some, ctor, cell, bindsAt, Quan.live, takes, data,
        Quan.fld, Term.sub, Env.sub, Term.spine]
  obtain ⟨n1, s1, _⟩ := to_nat_cell (b := t) h
  obtain ⟨n2, s2, v2⟩ := token_run h hs e
  exact ⟨_, .step ev ((s1.app_x (value_token h) rfl).app_f.app_f.trans s2), v2⟩

theorem go_run : Contains B reader → ∀ xs s, (∀ x ∈ s, Value B x) →
    (Read.run xs s).bind Read.done = some ds →
    Runs B (App Q1 (App Q1 (Ref "Book.read.go") (bytes xs)) (Form.some (list s)))
      (Form.some ds)
  | h, [], s, hs, e => by
    have hk := h «reader.Book.read.go» (by simp [reader])
    have hk' := h «reader.Book.read.done» (by simp [reader])
    simp only [Read.run, Option.bind_some] at e
    match s, e with
    | [d], e =>
      cases unitem_some e
      have vd := hs _ (List.mem_singleton_self _)
      simp only [Read.item, ctor, List.foldr, value_tup_iff] at vd
      have ev : Eval B (spine (Ref "Book.read.go")
          [(Q1, bytes []), (Q1, Form.some (list [Read.item "defs" ds]))])
          (App Q1 (Ref "Book.read.done") (Form.some (list [Read.item "defs" ds]))) := by
        refine Eval.walk hk (.cons (fun _ => value_bytes)
          (.cons (fun _ => value_ctor (by simpa using value_list hs)) .nil)) ?_
        simp [«reader.Book.read.go», walk, bytes, list, ctor, bindsAt, Quan.live, takes,
          Quan.fld, Term.sub, Env.sub, Term.spine]
      refine .step ev ?_
      refine .step (Eval.walk hk' (xs := [(Q1, _)])
        (.cons (fun _ => value_ctor (by simpa using value_list hs)) .nil) ?_) (.refl (value_ctor (by simpa using vd.2.1)))
      simp [«reader.Book.read.done», walk, Form.some, list, ctor, Read.item, bindsAt, Quan.live, takes,
          Quan.fld, Term.sub, Env.sub, Term.spine]
  | _, [_], _, _, e => by simp [Read.run] at e
  | h, t :: b :: xs, s, hs, e => by
    simp only [Read.run] at e
    obtain ⟨s', e1, e2⟩ : ∃ s', Read.token t.toNat b s = some s' ∧
        (Read.run xs s').bind Read.done = some ds := by
      cases h' : Read.token t.toNat b s <;> simp_all
    have hk := h «reader.Book.read.go» (by simp [reader])
    obtain ⟨n, st, vs⟩ := step_run h hs e1
    have hs' := value_list_of (value_tup_iff.1 (value_tup_iff.1 vs).2).1
    refine .step (Eval.walk hk (xs := [(Q1, _), (Q1, _)])
      (.cons (fun _ => value_bytes) (.cons (fun _ => value_ctor (by simpa using value_list hs)) .nil)) ?_)
      (.steps (st.app_x (value_go h) rfl) (go_run h xs s' hs' e2))
    simp [«reader.Book.read.go», walk, bytes, list, ctor, cell, bindsAt, Quan.live, takes, data,
      Quan.fld, Term.sub, Env.sub, Term.spine]
