import Bootstrap.Code
import Bootstrap.Copy.Reader
import Bootstrap.Read.Model

-- Read.TokenHigh
-- ==============
--
-- Book.read.token does what the model does, for the tags from 22 on, on a stack
-- of values.

open Quan Term

-- a call steps to the leaf of its walk, then runs on
private theorem runs_walk (hk : Book.get B k = some d) (vs : Values B xs)
    (w : walk B d.v [] xs = some (some u)) (r : Runs B u v) : Runs B (spine (Ref k) xs) v :=
  .step (Eval.walk hk vs w) r

-- a call on a tag and a stack runs as the leaf of its walk
private theorem runs_tag (hk : Book.get B k = some d) (vl : Value B l)
    (w : walk B d.v [] [(Q1, Form.nat m), (Q1, l)] = some (some u)) (r : Runs B u v) :
    Runs B (App Q1 (App Q1 (Ref k) (Form.nat m)) l) v :=
  runs_walk (xs := [(Q1, _), (Q1, _)]) hk (.cons (fun _ => value_nat) (.cons (fun _ => vl) .nil))
    w r

-- a handler on a stack runs to the leaf of its walk, when that is a value
private theorem runs_handler (hk : Book.get B k = some d) (vl : Value B l)
    (w : walk B d.v [] [(Q1, l)] = some (some v)) (vv : Value B v) :
    Runs B (App Q1 (Ref k) l) v :=
  runs_walk (xs := [(Q1, _)]) hk (.cons (fun _ => vl) .nil) w (.refl vv)

-- Book.read.token goes on to Book.read.token8 from the tag 8 on
private theorem token_8 (h : Contains B reader) (vl : Value B l)
    (r : Runs B (App Q1 (App Q1 (Ref "Book.read.token8") (Form.nat n)) l) v) :
    Runs B (App Q1 (App Q1 (App Q1 (Ref "Book.read.token") (Form.nat (n + 8))) l) (cell b)) v := by
  have k1 : Book.get B "Book.read.token" = some «reader.Book.read.token» :=
    h «reader.Book.read.token» (by simp [reader])
  exact runs_walk (xs := [(Q1, _), (Q1, _), (Q1, _)]) k1
      (.cons (fun _ => value_nat) (.cons (fun _ => vl) (.cons (fun _ => value_cell) .nil)))
      (by simp [«reader.Book.read.token», Form.nat, cell, walk, ctor, bindsAt, Quan.live, takes,
          Quan.fld, Term.sub, Env.sub, Term.spine]) r

-- Book.read.token8 goes on to Book.read.token16 from 8 on
private theorem token_16 (h : Contains B reader) (vl : Value B l)
    (r : Runs B (App Q1 (App Q1 (Ref "Book.read.token16") (Form.nat n)) l) v) :
    Runs B (App Q1 (App Q1 (Ref "Book.read.token8") (Form.nat (n + 8))) l) v := by
  have k1 : Book.get B "Book.read.token8" = some «reader.Book.read.token8» :=
    h «reader.Book.read.token8» (by simp [reader])
  exact runs_tag k1 vl
      (by simp [«reader.Book.read.token8», Form.nat, walk, ctor, bindsAt, Quan.live, takes,
          Quan.fld, Term.sub, Env.sub, Term.spine]) r

-- Book.read.token16 goes on to Book.read.token24 from 8 on
private theorem token_24 (h : Contains B reader) (vl : Value B l)
    (r : Runs B (App Q1 (App Q1 (Ref "Book.read.token24") (Form.nat n)) l) v) :
    Runs B (App Q1 (App Q1 (Ref "Book.read.token16") (Form.nat (n + 8))) l) v := by
  have k1 : Book.get B "Book.read.token16" = some «reader.Book.read.token16» :=
    h «reader.Book.read.token16» (by simp [reader])
  exact runs_tag k1 vl
      (by simp [«reader.Book.read.token16», Form.nat, walk, ctor, bindsAt, Quan.live, takes,
          Quan.fld, Term.sub, Env.sub, Term.spine]) r

-- Book.read.token24 goes on to Book.read.token32 from 8 on
private theorem token_32 (h : Contains B reader) (vl : Value B l)
    (r : Runs B (App Q1 (App Q1 (Ref "Book.read.token32") (Form.nat n)) l) v) :
    Runs B (App Q1 (App Q1 (Ref "Book.read.token24") (Form.nat (n + 8))) l) v := by
  have k1 : Book.get B "Book.read.token24" = some «reader.Book.read.token24» :=
    h «reader.Book.read.token24» (by simp [reader])
  exact runs_tag k1 vl
      (by simp [«reader.Book.read.token24», Form.nat, walk, ctor, bindsAt, Quan.live, takes,
          Quan.fld, Term.sub, Env.sub, Term.spine]) r

-- the payload of an item that is a value is a value
private theorem value_item (h : Value B (Read.item k x)) : Value B x :=
  (value_tup_iff.1 (value_tup_iff.1 h).2).1

-- a stack of values, as Form.some, is a value
private theorem value_some (hs : ∀ x ∈ s, Value B x) : Value B (Form.some (list s)) :=
  value_ctor (by simpa using value_list hs)

-- a stack of values, with a term item of values on top, as Form.some, is a value
private theorem value_push (hx : ∀ y ∈ fs, Value B y) (hs : ∀ x ∈ s, Value B x) :
    Value B (Form.some (list (Read.item "term" (ctor j fs) :: s))) :=
  value_some (List.forall_mem_cons.2 ⟨value_ctor (by simpa using value_ctor hx), hs⟩)

theorem token_high : Contains B reader → 22 ≤ t → (∀ x ∈ s, Value B x) →
    Read.token t b s = some s' →
    Runs B (App Q1 (App Q1 (App Q1 (Ref "Book.read.token") (Form.nat t)) (list s)) (cell b))
      (Form.some (list s')) := by
  intro h ht hs e
  have vl := value_list hs
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 22 := ⟨t - 22, by omega⟩
  match n, e with
  | 0, e =>
    rcases s with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;> simp [Read.token,
        Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, _, h2, _, h3, rfl⟩ := e
    cases unitem_some h1; cases unitem_some h2; cases unitem_some h3
    simp only [List.forall_mem_cons] at hs
    obtain ⟨a1, a2, a3, hr⟩ := hs
    simp only [Nat.reduceAdd]
    have k1 : Book.get B "Book.read.token16" = some «reader.Book.read.token16» :=
      h «reader.Book.read.token16» (by simp [reader])
    have k2 : Book.get B "Book.read.app" = some «reader.Book.read.app» :=
      h «reader.Book.read.app» (by simp [reader])
    exact token_8 h vl (token_16 h vl (runs_tag k1 vl
      (by simp [«reader.Book.read.token16», Form.nat, walk, Read.item, list, ctor, bindsAt,
          Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine])
      (runs_handler k2 vl
        (by simp [«reader.Book.read.app», walk, Read.item, list, ctor, Form.some, bindsAt,
            Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine])
        (value_push (by simp [value_item a1, value_item a2, value_item a3]) hr))))
  | 1, e =>
    rcases s with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;> simp [Read.token,
        Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, _, h2, _, h3, rfl⟩ := e
    cases unitem_some h1; cases unitem_some h2; cases unitem_some h3
    simp only [List.forall_mem_cons] at hs
    obtain ⟨a1, a2, a3, hr⟩ := hs
    simp only [Nat.reduceAdd]
    have k1 : Book.get B "Book.read.token16" = some «reader.Book.read.token16» :=
      h «reader.Book.read.token16» (by simp [reader])
    have k2 : Book.get B "Book.read.sig" = some «reader.Book.read.sig» :=
      h «reader.Book.read.sig» (by simp [reader])
    exact token_8 h vl (token_16 h vl (runs_tag k1 vl
      (by simp [«reader.Book.read.token16», Form.nat, walk, Read.item, list, ctor, bindsAt,
          Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine])
      (runs_handler k2 vl
        (by simp [«reader.Book.read.sig», walk, Read.item, list, ctor, Form.some, bindsAt,
            Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine])
        (value_push (by simp [value_item a1, value_item a2, value_item a3]) hr))))
  | 2, e =>
    rcases s with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;> simp [Read.token,
        Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, _, h2, _, h3, rfl⟩ := e
    cases unitem_some h1; cases unitem_some h2; cases unitem_some h3
    simp only [List.forall_mem_cons] at hs
    obtain ⟨a1, a2, a3, hr⟩ := hs
    simp only [Nat.reduceAdd]
    have k1 : Book.get B "Book.read.token24" = some «reader.Book.read.token24» :=
      h «reader.Book.read.token24» (by simp [reader])
    have k2 : Book.get B "Book.read.tup" = some «reader.Book.read.tup» :=
      h «reader.Book.read.tup» (by simp [reader])
    exact token_8 h vl (token_16 h vl (token_24 h vl (runs_tag k1 vl
      (by simp [«reader.Book.read.token24», Form.nat, walk, Read.item, list, ctor, bindsAt,
          Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine])
      (runs_handler k2 vl
        (by simp [«reader.Book.read.tup», walk, Read.item, list, ctor, Form.some, bindsAt,
            Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine])
        (value_push (by simp [value_item a1, value_item a2, value_item a3]) hr)))))
  | 3, e =>
    rcases s with _ | ⟨x, rest⟩ <;> simp [Read.token, Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, rfl⟩ := e
    cases unitem_some h1
    simp only [List.forall_mem_cons] at hs
    obtain ⟨a1, hr⟩ := hs
    simp only [Nat.reduceAdd]
    have k1 : Book.get B "Book.read.token24" = some «reader.Book.read.token24» :=
      h «reader.Book.read.token24» (by simp [reader])
    have k2 : Book.get B "Book.read.prj" = some «reader.Book.read.prj» :=
      h «reader.Book.read.prj» (by simp [reader])
    exact token_8 h vl (token_16 h vl (token_24 h vl (runs_tag k1 vl
      (by simp [«reader.Book.read.token24», Form.nat, walk, Read.item, list, ctor, bindsAt,
          Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine])
      (runs_handler k2 vl
        (by simp [«reader.Book.read.prj», walk, Read.item, list, ctor, Form.some, bindsAt,
            Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine])
        (value_push (by simp [value_item a1]) hr)))))
  | 4, e =>
    rcases s with _ | ⟨x, rest⟩ <;> simp [Read.token, Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, rfl⟩ := e
    cases unitem_some h1
    simp only [List.forall_mem_cons] at hs
    obtain ⟨a1, hr⟩ := hs
    simp only [Nat.reduceAdd]
    have k1 : Book.get B "Book.read.token24" = some «reader.Book.read.token24» :=
      h «reader.Book.read.token24» (by simp [reader])
    have k2 : Book.get B "Book.read.enu" = some «reader.Book.read.enu» :=
      h «reader.Book.read.enu» (by simp [reader])
    exact token_8 h vl (token_16 h vl (token_24 h vl (runs_tag k1 vl
      (by simp [«reader.Book.read.token24», Form.nat, walk, Read.item, list, ctor, bindsAt,
          Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine])
      (runs_handler k2 vl
        (by simp [«reader.Book.read.enu», walk, Read.item, list, ctor, Form.some, bindsAt,
            Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine])
        (value_push (by simp [value_item a1]) hr)))))
  | 5, e =>
    rcases s with _ | ⟨x, rest⟩ <;> simp [Read.token, Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, rfl⟩ := e
    cases unitem_some h1
    simp only [List.forall_mem_cons] at hs
    obtain ⟨a1, hr⟩ := hs
    simp only [Nat.reduceAdd]
    have k1 : Book.get B "Book.read.token24" = some «reader.Book.read.token24» :=
      h «reader.Book.read.token24» (by simp [reader])
    have k2 : Book.get B "Book.read.lab" = some «reader.Book.read.lab» :=
      h «reader.Book.read.lab» (by simp [reader])
    exact token_8 h vl (token_16 h vl (token_24 h vl (runs_tag k1 vl
      (by simp [«reader.Book.read.token24», Form.nat, walk, Read.item, list, ctor, bindsAt,
          Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine])
      (runs_handler k2 vl
        (by simp [«reader.Book.read.lab», walk, Read.item, list, ctor, Form.some, bindsAt,
            Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine])
        (value_push (by simp [value_item a1]) hr)))))
  | 6, e =>
    rcases s with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;> simp [Read.token,
        Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, _, h2, _, h3, rfl⟩ := e
    cases unitem_some h1; cases unitem_some h2; cases unitem_some h3
    simp only [List.forall_mem_cons] at hs
    obtain ⟨a1, a2, a3, hr⟩ := hs
    simp only [Nat.reduceAdd]
    have k1 : Book.get B "Book.read.token24" = some «reader.Book.read.token24» :=
      h «reader.Book.read.token24» (by simp [reader])
    have k2 : Book.get B "Book.read.mat" = some «reader.Book.read.mat» :=
      h «reader.Book.read.mat» (by simp [reader])
    exact token_8 h vl (token_16 h vl (token_24 h vl (runs_tag k1 vl
      (by simp [«reader.Book.read.token24», Form.nat, walk, Read.item, list, ctor, bindsAt,
          Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine])
      (runs_handler k2 vl
        (by simp [«reader.Book.read.mat», walk, Read.item, list, ctor, Form.some, bindsAt,
            Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine])
        (value_push (by simp [value_item a1, value_item a2, value_item a3]) hr)))))
  | 7, e =>
    simp [Read.token] at e
    subst e
    simp only [Nat.reduceAdd]
    have k1 : Book.get B "Book.read.token24" = some «reader.Book.read.token24» :=
      h «reader.Book.read.token24» (by simp [reader])
    exact token_8 h vl (token_16 h vl (token_24 h vl (runs_tag k1 vl
      (by simp [«reader.Book.read.token24», Form.nat, Form.term, walk, Read.item, list, ctor,
          Form.some, bindsAt, Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine])
      (.refl (value_some (List.forall_mem_cons.2 ⟨value_ctor (by simp [value_term]), hs⟩))))))
  | 8, e =>
    rcases s with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;> simp [Read.token,
        Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, _, h2, _, h3, rfl⟩ := e
    cases unitem_some h1; cases unitem_some h2; cases unitem_some h3
    simp only [List.forall_mem_cons] at hs
    obtain ⟨a1, a2, a3, hr⟩ := hs
    simp only [Nat.reduceAdd]
    have k1 : Book.get B "Book.read.token24" = some «reader.Book.read.token24» :=
      h «reader.Book.read.token24» (by simp [reader])
    have k2 : Book.get B "Book.read.eql" = some «reader.Book.read.eql» :=
      h «reader.Book.read.eql» (by simp [reader])
    exact token_8 h vl (token_16 h vl (token_24 h vl (runs_tag k1 vl
      (by simp [«reader.Book.read.token24», Form.nat, walk, Read.item, list, ctor, bindsAt,
          Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine])
      (runs_handler k2 vl
        (by simp [«reader.Book.read.eql», walk, Read.item, list, ctor, Form.some, bindsAt,
            Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine])
        (value_push (by simp [value_item a1, value_item a2, value_item a3]) hr)))))
  | 9, e =>
    simp [Read.token] at e
    subst e
    simp only [Nat.reduceAdd]
    have k1 : Book.get B "Book.read.token24" = some «reader.Book.read.token24» :=
      h «reader.Book.read.token24» (by simp [reader])
    exact token_8 h vl (token_16 h vl (token_24 h vl (runs_tag k1 vl
      (by simp [«reader.Book.read.token24», Form.nat, Form.term, walk, Read.item, list, ctor,
          Form.some, bindsAt, Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine])
      (.refl (value_some (List.forall_mem_cons.2 ⟨value_ctor (by simp [value_term]), hs⟩))))))
  | 10, e =>
    rcases s with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;> simp [Read.token,
        Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, _, h2, _, h3, rfl⟩ := e
    cases unitem_some h1; cases unitem_some h2; cases unitem_some h3
    simp only [List.forall_mem_cons] at hs
    obtain ⟨a1, a2, a3, hr⟩ := hs
    simp only [Nat.reduceAdd]
    have k1 : Book.get B "Book.read.token32" = some «reader.Book.read.token32» :=
      h «reader.Book.read.token32» (by simp [reader])
    have k2 : Book.get B "Book.read.rwt" = some «reader.Book.read.rwt» :=
      h «reader.Book.read.rwt» (by simp [reader])
    exact token_8 h vl (token_16 h vl (token_24 h vl (token_32 h vl (runs_tag k1 vl
      (by simp [«reader.Book.read.token32», Form.nat, walk, Read.item, list, ctor, bindsAt,
          Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine])
      (runs_handler k2 vl
        (by simp [«reader.Book.read.rwt», walk, Read.item, list, ctor, Form.some, bindsAt,
            Quan.live, takes, Quan.fld, Term.sub, Env.sub, Term.spine])
        (value_push (by simp [value_item a1, value_item a2, value_item a3]) hr))))))
  | _ + 11, e => simp [Read.token] at e
