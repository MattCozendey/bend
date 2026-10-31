import Bootstrap.Code
import Bootstrap.Copy.Reader
import Bootstrap.Read.Model

-- Read.TokenLow
-- =============
--
-- Book.read.token does what the model does, for the tags 0 to 10, on a stack
-- of values.

open Quan Term

-- a stack of values, in a Some, is a value
private theorem value_some_list (hs : ∀ x ∈ s, Value B x) : Value B (Form.some (list s)) :=
  value_ctor (by simpa using value_list hs)

-- the payload of a stack item that is a value is a value
private theorem value_item (h : Value B (Read.item k x)) : Value B x := by
  simp only [Read.item, ctor, List.foldr, value_tup_iff] at h
  exact h.2.1

-- a stack item of a value is a value
private theorem value_item' (h : Value B x) : Value B (Read.item k x) :=
  value_ctor (by simpa using h)

-- the first call of Book.read.token, on a stack of values, steps to its leaf
private theorem token_call (h : Contains B reader) (hs : ∀ x ∈ s, Value B x)
    (w : walk B «reader.Book.read.token».v []
      [(Q1, Form.nat t), (Q1, list s), (Q1, cell b)] = some (some u)) (r : Runs B u v) :
    Runs B (App Q1 (App Q1 (App Q1 (Ref "Book.read.token") (Form.nat t)) (list s)) (cell b)) v :=
  .step (Eval.walk (h «reader.Book.read.token» (by simp [reader])) (xs := [(Q1, _), (Q1, _), (Q1, _)])
    (.cons (fun _ => value_nat) (.cons (fun _ => value_list hs) (.cons (fun _ => value_cell) .nil)))
    w) r

-- a call of Book.read.token8, on a stack of values, steps to its leaf
private theorem token8_call (h : Contains B reader) (hs : ∀ x ∈ s, Value B x)
    (w : walk B «reader.Book.read.token8».v []
      [(Q1, Form.nat t), (Q1, list s)] = some (some u)) (r : Runs B u v) :
    Runs B (App Q1 (App Q1 (Ref "Book.read.token8") (Form.nat t)) (list s)) v :=
  .step (Eval.walk (h «reader.Book.read.token8» (by simp [reader])) (xs := [(Q1, _), (Q1, _)])
    (.cons (fun _ => value_nat) (.cons (fun _ => value_list hs) .nil)) w) r

-- a call of a reader def on one value steps to its leaf
private theorem call1 (h : Contains B reader) (hd : d ∈ reader) (vx : Value B x)
    (w : walk B d.v [] [(Q1, x)] = some (some u)) (r : Runs B u v) :
    Runs B (App Q1 (Ref d.k) x) v :=
  .step (Eval.walk (h d hd) (xs := [(Q1, _)]) (.cons (fun _ => vx) .nil) w) r

-- a call of a reader def on two values steps to its leaf
private theorem call2 (h : Contains B reader) (hd : d ∈ reader) (vx : Value B x) (vy : Value B y)
    (w : walk B d.v [] [(Q1, x), (Q1, y)] = some (some u)) (r : Runs B u v) :
    Runs B (App Q1 (App Q1 (Ref d.k) x) y) v :=
  .step (Eval.walk (h d hd) (xs := [(Q1, _), (Q1, _)])
    (.cons (fun _ => vx) (.cons (fun _ => vy) .nil)) w) r

theorem token_low : Contains B reader → t ≤ 10 → (∀ x ∈ s, Value B x) →
    Read.token t b s = some s' →
    Runs B (App Q1 (App Q1 (App Q1 (Ref "Book.read.token") (Form.nat t)) (list s)) (cell b))
      (Form.some (list s')) := by
  intro h ht hs e
  match t, ht with
  | 0, _ | 1, _ | 2, _ | 3, _ | 5, _ | 7, _ =>
    simp only [Read.token, Option.some.injEq] at e
    subst e
    refine token_call h hs ?_ (.refl (value_some_list ?_))
    · simp [«reader.Book.read.token», walk, Form.nat, Form.quan, Form.some, Read.item,
        list, ctor, bindsAt, Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine]
    · simpa [value_item', value_quan, value_nat, value_list] using hs
  | 9, _ =>
    simp only [Read.token, Option.some.injEq] at e
    subst e
    refine token_call h hs (u := App Q1 (App Q1 (Ref "Book.read.token8") (Form.nat 1)) (list s)) ?_
      (token8_call h hs ?_ (.refl (value_some_list ?_)))
    · simp [«reader.Book.read.token», walk, Form.nat,
        ctor, bindsAt, Quan.live, takes, data, Quan.fld, Term.sub, Env.sub, Term.spine]
    · simp [«reader.Book.read.token8», walk, Form.nat, Form.bool, Form.some, Read.item,
        list, ctor, bindsAt, Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine]
    · simpa [value_item', value_bool] using hs
  | 10, _ =>
    simp only [Read.token, Option.some.injEq] at e
    subst e
    refine token_call h hs (u := App Q1 (App Q1 (Ref "Book.read.token8") (Form.nat 2)) (list s)) ?_
      (token8_call h hs ?_ (.refl (value_some_list ?_)))
    · simp [«reader.Book.read.token», walk, Form.nat,
        ctor, bindsAt, Quan.live, takes, data, Quan.fld, Term.sub, Env.sub, Term.spine]
    · simp [«reader.Book.read.token8», walk, Form.nat, Form.bool, Form.some, Read.item,
        list, ctor, bindsAt, Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine]
    · simpa [value_item', value_bool] using hs
  | 4, _ =>
    match s, e with
    | [], e => simp [Read.token] at e
    | n :: s, e =>
      cases hy : Read.unitem "nat" n with
      | none => simp [Read.token, hy] at e
      | some y =>
        simp only [Read.token, hy] at e
        cases e
        cases unitem_some hy
        have vy := value_item (hs _ List.mem_cons_self)
        refine token_call h hs (u := App Q1 (Ref "Book.read.succ") (list (Read.item "nat" y :: s)))
          ?_ (call1 (d := «reader.Book.read.succ») h (by simp [reader]) (value_list hs) ?_
            (.refl (value_some_list (List.forall_mem_cons.2
              ⟨value_item' (value_ctor (by simpa using vy)), fun x hx => hs x (by simp [hx])⟩))))
        · simp [«reader.Book.read.token», walk, Form.nat,
            ctor, bindsAt, Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine]
        · simp [«reader.Book.read.succ», walk, Form.some, Read.item,
            list, ctor, bindsAt, Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine]
  | 6, _ =>
    match s, e with
    | [], e => simp [Read.token] at e
    | k :: s, e =>
      cases hy : Read.unitem "name" k with
      | none => simp [Read.token, hy] at e
      | some y =>
        simp only [Read.token, hy] at e
        cases e
        cases unitem_some hy
        have vy := value_item (hs _ List.mem_cons_self)
        refine token_call h hs
          (u := App Q1 (App Q1 (Ref "Book.read.byte") (list (Read.item "name" y :: s))) (cell b))
          ?_ (call2 (d := «reader.Book.read.byte») h (by simp [reader]) (value_list hs) value_cell ?_
            (.refl (value_some_list (List.forall_mem_cons.2
              ⟨value_item' (value_ctor (by simpa using ⟨value_cell, vy⟩)),
                fun x hx => hs x (by simp [hx])⟩))))
        · simp [«reader.Book.read.token», walk, Form.nat,
            ctor, bindsAt, Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine]
        · simp [«reader.Book.read.byte», walk, Form.some, Read.item,
            list, ctor, bindsAt, Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine]
  | 8, _ =>
    match s, e with
    | [], e => simp [Read.token] at e
    | [_], e => simp [Read.token] at e
    | k :: ks :: s, e =>
      cases hy : Read.unitem "name" k with
      | none => simp [Read.token, hy] at e
      | some y =>
      cases hz : Read.unitem "names" ks with
      | none => simp [Read.token, hy, hz] at e
      | some z =>
        simp only [Read.token, hy, hz] at e
        cases e
        cases unitem_some hy
        cases unitem_some hz
        have vy := value_item (hs _ List.mem_cons_self)
        have vz := value_item (hs _ (List.mem_cons_of_mem _ List.mem_cons_self))
        let l := list (Read.item "name" y :: Read.item "names" z :: s)
        refine token_call h hs (u := App Q1 (App Q1 (Ref "Book.read.token8") (Form.nat 0)) l) ?_
          (token8_call h hs (u := App Q1 (Ref "Book.read.names") l) ?_
            (call1 (d := «reader.Book.read.names») h (by simp [reader]) (value_list hs) ?_
              (.refl (value_some_list (List.forall_mem_cons.2
                ⟨value_item' (value_ctor (by simpa using ⟨vy, vz⟩)),
                  fun x hx => hs x (by simp [hx])⟩)))))
        · simp [l, «reader.Book.read.token», walk, Form.nat,
            ctor, bindsAt, Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine]
        · simp [l, «reader.Book.read.token8», walk, Form.nat,
            ctor, bindsAt, Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine]
        · simp [l, «reader.Book.read.names», walk, Form.some, Read.item,
            list, ctor, bindsAt, Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine]
