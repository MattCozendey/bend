import Bootstrap.Code
import Bootstrap.Copy.Reader
import Bootstrap.Read.Model

-- Read.TokenMiddle
-- ================
--
-- Book.read.token, on a stack of values, does what the model does, for the tags 11 to 21.

open Quan Term

-- a call of Book.read.token on the tag 8 + p goes on to Book.read.token8 with p
private theorem token_eight (h : Contains B reader) (vl : Value B (list s))
    (r : Runs B (App Q1 (App Q1 (Ref "Book.read.token8") (Form.nat p)) (list s)) v) :
    Runs B (App Q1 (App Q1 (App Q1 (Ref "Book.read.token") (Form.nat (p + 8))) (list s)) (cell b)) v := by
  have hk := h «reader.Book.read.token» (by simp [reader])
  refine .step (Eval.walk (xs := [(Q1, _), (Q1, _), (Q1, _)]) hk
    (.cons (fun _ => value_nat) (.cons (fun _ => vl) (.cons (fun _ => value_cell) .nil))) ?_) r
  simp [walk, «reader.Book.read.token», Form.nat, ctor, cell, bindsAt, Quan.live, takes, data,
        Quan.fld, Term.sub, Env.sub, Term.spine]

-- a call of Book.read.token8 on 8 + p goes on to Book.read.token16 with p
private theorem token_sixteen (h : Contains B reader) (vl : Value B (list s))
    (r : Runs B (App Q1 (App Q1 (Ref "Book.read.token16") (Form.nat p)) (list s)) v) :
    Runs B (App Q1 (App Q1 (Ref "Book.read.token8") (Form.nat (p + 8))) (list s)) v := by
  have hk := h «reader.Book.read.token8» (by simp [reader])
  refine .step (Eval.walk (xs := [(Q1, _), (Q1, _)]) hk
    (.cons (fun _ => value_nat) (.cons (fun _ => vl) .nil)) ?_) r
  simp [walk, «reader.Book.read.token8», Form.nat, ctor, bindsAt, Quan.live, takes,
        Quan.fld, Term.sub, Env.sub, Term.spine]

-- a dispatch to a handler, whose call reaches a value
private theorem run_pop (h8 : Book.get B k8 = some d8) (hk : Book.get B k = some d)
    (vn : Value B n) (vl : Value B l)
    (w1 : walk B d8.v [] [(Q1, n), (Q1, l)] = some (some (App Q1 (Ref k) l)))
    (w2 : walk B d.v [] [(Q1, l)] = some (some r)) (vr : Value B r) :
    Runs B (App Q1 (App Q1 (Ref k8) n) l) r :=
  .step (Eval.walk (xs := [(Q1, _), (Q1, _)]) h8 (.cons (fun _ => vn) (.cons (fun _ => vl) .nil)) w1)
    (.step (Eval.walk (xs := [(Q1, _)]) hk (.cons (fun _ => vl) .nil) w2) (.refl vr))

theorem token_middle : Contains B reader → 11 ≤ t → t ≤ 21 → (∀ x ∈ s, Value B x) →
    Read.token t b s = some s' →
    Runs B (App Q1 (App Q1 (App Q1 (Ref "Book.read.token") (Form.nat t)) (list s)) (cell b))
      (Form.some (list s')) := by
  intro h h1 h2 hs e
  have vl := value_list hs
  obtain ⟨p, rfl⟩ : ∃ p, t = p + 8 := ⟨t - 8, by omega⟩
  refine token_eight h vl ?_
  have hk8 := h «reader.Book.read.token8» (by simp [reader])
  have hk16 := h «reader.Book.read.token16» (by simp [reader])
  match p, h1, h2, e with
  | 3, _, _, e =>
    simp only [Read.token, Option.some.injEq] at e
    subst e
    refine .step (Eval.walk (xs := [(Q1, _), (Q1, _)]) hk8
      (.cons (fun _ => value_nat) (.cons (fun _ => vl) .nil)) ?_) (.refl ?_)
    · simp [walk, «reader.Book.read.token8», Form.nat, ctor, bindsAt, Quan.live, takes,
        Quan.fld, Term.sub, Env.sub, Term.spine, Form.some, list, Read.item]
    · have hv := value_list hs
      simp only [Form.some, list, Read.item, ctor, List.foldr, value_tup_iff] at hv ⊢
      simp_all [Value.lab]
  | 4, _, _, e =>
    have hk := h «reader.Book.read.defs» (by simp [reader])
    rcases s with _ | ⟨x1, _ | ⟨x2, rest⟩⟩ <;> simp [Read.token, Option.bind_eq_some_iff] at e
    obtain ⟨a1, e1, a2, e2, rfl⟩ := e
    cases unitem_some e1
    cases unitem_some e2
    refine run_pop hk8 hk value_nat vl ?_ ?_ ?_
    · simp [walk, «reader.Book.read.token8», «reader.Book.read.defs», Form.nat, ctor, bindsAt, Quan.live, takes,
        Quan.fld, Term.sub, Env.sub, Term.spine, list, Read.item]
    · simp [walk, «reader.Book.read.defs», Form.some, ctor, bindsAt, Quan.live, takes,
        Quan.fld, Term.sub, Env.sub, Term.spine, list, Read.item]
    · have hv := value_list hs
      simp only [Form.some, list, Read.item, ctor, List.foldr, value_tup_iff] at hv ⊢
      simp_all [Value.lab]
  | 5, _, _, e =>
    have hk := h «reader.Book.read.def» (by simp [reader])
    rcases s with _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, rest⟩⟩⟩⟩ <;> simp [Read.token, Option.bind_eq_some_iff] at e
    obtain ⟨a1, e1, a2, e2, a3, e3, a4, e4, rfl⟩ := e
    cases unitem_some e1
    cases unitem_some e2
    cases unitem_some e3
    cases unitem_some e4
    refine run_pop hk8 hk value_nat vl ?_ ?_ ?_
    · simp [walk, «reader.Book.read.token8», «reader.Book.read.def», Form.nat, ctor, bindsAt, Quan.live, takes,
        Quan.fld, Term.sub, Env.sub, Term.spine, list, Read.item]
    · simp [walk, «reader.Book.read.def», Form.some, ctor, bindsAt, Quan.live, takes,
        Quan.fld, Term.sub, Env.sub, Term.spine, list, Read.item]
    · have hv := value_list hs
      simp only [Form.some, list, Read.item, ctor, List.foldr, value_tup_iff] at hv ⊢
      simp_all [Value.lab]
  | 6, _, _, e =>
    have hk := h «reader.Book.read.var» (by simp [reader])
    rcases s with _ | ⟨x1, rest⟩ <;> simp [Read.token, Option.bind_eq_some_iff] at e
    obtain ⟨a1, e1, rfl⟩ := e
    cases unitem_some e1
    refine run_pop hk8 hk value_nat vl ?_ ?_ ?_
    · simp [walk, «reader.Book.read.token8», «reader.Book.read.var», Form.nat, ctor, bindsAt, Quan.live, takes,
        Quan.fld, Term.sub, Env.sub, Term.spine, list, Read.item]
    · simp [walk, «reader.Book.read.var», Form.some, ctor, bindsAt, Quan.live, takes,
        Quan.fld, Term.sub, Env.sub, Term.spine, list, Read.item]
    · have hv := value_list hs
      simp only [Form.some, list, Read.item, ctor, List.foldr, value_tup_iff] at hv ⊢
      simp_all [Value.lab]
  | 7, _, _, e =>
    have hk := h «reader.Book.read.ref» (by simp [reader])
    rcases s with _ | ⟨x1, rest⟩ <;> simp [Read.token, Option.bind_eq_some_iff] at e
    obtain ⟨a1, e1, rfl⟩ := e
    cases unitem_some e1
    refine run_pop hk8 hk value_nat vl ?_ ?_ ?_
    · simp [walk, «reader.Book.read.token8», «reader.Book.read.ref», Form.nat, ctor, bindsAt, Quan.live, takes,
        Quan.fld, Term.sub, Env.sub, Term.spine, list, Read.item]
    · simp [walk, «reader.Book.read.ref», Form.some, ctor, bindsAt, Quan.live, takes,
        Quan.fld, Term.sub, Env.sub, Term.spine, list, Read.item]
    · have hv := value_list hs
      simp only [Form.some, list, Read.item, ctor, List.foldr, value_tup_iff] at hv ⊢
      simp_all [Value.lab]
  | 8, _, _, e =>
    have hk := h «reader.Book.read.ann» (by simp [reader])
    rcases s with _ | ⟨x1, _ | ⟨x2, rest⟩⟩ <;> simp [Read.token, Option.bind_eq_some_iff] at e
    obtain ⟨a1, e1, a2, e2, rfl⟩ := e
    cases unitem_some e1
    cases unitem_some e2
    refine token_sixteen (p := 0) h vl (run_pop hk16 hk value_nat vl ?_ ?_ ?_)
    · simp [walk, «reader.Book.read.token16», «reader.Book.read.ann», Form.nat, ctor, bindsAt, Quan.live, takes,
        Quan.fld, Term.sub, Env.sub, Term.spine, list, Read.item]
    · simp [walk, «reader.Book.read.ann», Form.some, ctor, bindsAt, Quan.live, takes,
        Quan.fld, Term.sub, Env.sub, Term.spine, list, Read.item]
    · have hv := value_list hs
      simp only [Form.some, list, Read.item, ctor, List.foldr, value_tup_iff] at hv ⊢
      simp_all [Value.lab]
  | 9, _, _, e =>
    have hk := h «reader.Book.read.let» (by simp [reader])
    rcases s with _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, rest⟩⟩⟩ <;> simp [Read.token, Option.bind_eq_some_iff] at e
    obtain ⟨a1, e1, a2, e2, a3, e3, rfl⟩ := e
    cases unitem_some e1
    cases unitem_some e2
    cases unitem_some e3
    refine token_sixteen (p := 1) h vl (run_pop hk16 hk value_nat vl ?_ ?_ ?_)
    · simp [walk, «reader.Book.read.token16», «reader.Book.read.let», Form.nat, ctor, bindsAt, Quan.live, takes,
        Quan.fld, Term.sub, Env.sub, Term.spine, list, Read.item]
    · simp [walk, «reader.Book.read.let», Form.some, ctor, bindsAt, Quan.live, takes,
        Quan.fld, Term.sub, Env.sub, Term.spine, list, Read.item]
    · have hv := value_list hs
      simp only [Form.some, list, Read.item, ctor, List.foldr, value_tup_iff] at hv ⊢
      simp_all [Value.lab]
  | 10, _, _, e =>
    have hk := h «reader.Book.read.typ» (by simp [reader])
    rcases s with _ | ⟨x1, rest⟩ <;> simp [Read.token, Option.bind_eq_some_iff] at e
    obtain ⟨a1, e1, rfl⟩ := e
    cases unitem_some e1
    refine token_sixteen (p := 2) h vl (run_pop hk16 hk value_nat vl ?_ ?_ ?_)
    · simp [walk, «reader.Book.read.token16», «reader.Book.read.typ», Form.nat, ctor, bindsAt, Quan.live, takes,
        Quan.fld, Term.sub, Env.sub, Term.spine, list, Read.item]
    · simp [walk, «reader.Book.read.typ», Form.some, ctor, bindsAt, Quan.live, takes,
        Quan.fld, Term.sub, Env.sub, Term.spine, list, Read.item]
    · have hv := value_list hs
      simp only [Form.some, list, Read.item, ctor, List.foldr, value_tup_iff] at hv ⊢
      simp_all [Value.lab]
  | 11, _, _, e =>
    have hk := h «reader.Book.read.min» (by simp [reader])
    rcases s with _ | ⟨x1, _ | ⟨x2, rest⟩⟩ <;> simp [Read.token, Option.bind_eq_some_iff] at e
    obtain ⟨a1, e1, a2, e2, rfl⟩ := e
    cases unitem_some e1
    cases unitem_some e2
    refine token_sixteen (p := 3) h vl (run_pop hk16 hk value_nat vl ?_ ?_ ?_)
    · simp [walk, «reader.Book.read.token16», «reader.Book.read.min», Form.nat, ctor, bindsAt, Quan.live, takes,
        Quan.fld, Term.sub, Env.sub, Term.spine, list, Read.item]
    · simp [walk, «reader.Book.read.min», Form.some, ctor, bindsAt, Quan.live, takes,
        Quan.fld, Term.sub, Env.sub, Term.spine, list, Read.item]
    · have hv := value_list hs
      simp only [Form.some, list, Read.item, ctor, List.foldr, value_tup_iff] at hv ⊢
      simp_all [Value.lab]
  | 12, _, _, e =>
    have hk := h «reader.Book.read.all» (by simp [reader])
    rcases s with _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, rest⟩⟩⟩ <;> simp [Read.token, Option.bind_eq_some_iff] at e
    obtain ⟨a1, e1, a2, e2, a3, e3, rfl⟩ := e
    cases unitem_some e1
    cases unitem_some e2
    cases unitem_some e3
    refine token_sixteen (p := 4) h vl (run_pop hk16 hk value_nat vl ?_ ?_ ?_)
    · simp [walk, «reader.Book.read.token16», «reader.Book.read.all», Form.nat, ctor, bindsAt, Quan.live, takes,
        Quan.fld, Term.sub, Env.sub, Term.spine, list, Read.item]
    · simp [walk, «reader.Book.read.all», Form.some, ctor, bindsAt, Quan.live, takes,
        Quan.fld, Term.sub, Env.sub, Term.spine, list, Read.item]
    · have hv := value_list hs
      simp only [Form.some, list, Read.item, ctor, List.foldr, value_tup_iff] at hv ⊢
      simp_all [Value.lab]
  | 13, _, _, e =>
    have hk := h «reader.Book.read.lam» (by simp [reader])
    rcases s with _ | ⟨x1, _ | ⟨x2, rest⟩⟩ <;> simp [Read.token, Option.bind_eq_some_iff] at e
    obtain ⟨a1, e1, a2, e2, rfl⟩ := e
    cases unitem_some e1
    cases unitem_some e2
    refine token_sixteen (p := 5) h vl (run_pop hk16 hk value_nat vl ?_ ?_ ?_)
    · simp [walk, «reader.Book.read.token16», «reader.Book.read.lam», Form.nat, ctor, bindsAt, Quan.live, takes,
        Quan.fld, Term.sub, Env.sub, Term.spine, list, Read.item]
    · simp [walk, «reader.Book.read.lam», Form.some, ctor, bindsAt, Quan.live, takes,
        Quan.fld, Term.sub, Env.sub, Term.spine, list, Read.item]
    · have hv := value_list hs
      simp only [Form.some, list, Read.item, ctor, List.foldr, value_tup_iff] at hv ⊢
      simp_all [Value.lab]
  | _ + 14, _, h2, _ => omega
  | 0, h1, _, _ | 1, h1, _, _ | 2, h1, _, _ => omega
