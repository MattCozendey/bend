import Bootstrap.Interp
import Bootstrap.Book

-- Code
-- ====
--
-- How a Lean law talks about our Bend code: Lean cannot see what the kernel's
-- parser gives, so a law is about a Lean copy of the defs that `bend -o` writes
-- for the code (src/Bootstrap/Copy/, made by scripts/Copy.lean), and holds in
-- each book that holds that copy.

open Quan Term

-- the term e reaches the value v in the book B
def Runs (B : Book) (e v : Term) : Prop := ∃ n, Steps B n e v ∧ Value B v

-- each def of ds is in the book B, under its own name
def Contains (B : Book) (ds : List Def) : Prop := ∀ d ∈ ds, Book.get B d.k = some d

-- a value reaches itself
theorem Runs.refl (v : Value B e) : Runs B e e := ⟨0, .refl, v⟩

theorem Steps.trans (h : Steps B n a b) (h' : Steps B m b c) : Steps B (n + m) a c := by
  induction h with
  | refl => rw [Nat.zero_add]; exact h'
  | step e _ ih => rw [Nat.add_right_comm]; exact .step e (ih h')

-- steps, then a run
theorem Runs.steps (h : Steps B n e e') (r : Runs B e' v) : Runs B e v :=
  have ⟨_, s, hv⟩ := r; ⟨_, h.trans s, hv⟩

theorem Runs.step (h : Eval B e e') (r : Runs B e' v) : Runs B e v := .steps (.step h .refl) r

-- the function of an application takes its steps
theorem Steps.app_f (h : Steps B n f f') : Steps B n (App q f x) (App q f' x) := by
  induction h with
  | refl => exact .refl
  | step e _ ih => exact .step (.app_f e) ih

-- a live argument takes its steps, after a function that is a value
theorem Steps.app_x (vf : Value B f) (l : q.live = true) (h : Steps B n x x') :
    Steps B n (App q f x) (App q f x') := by
  induction h with
  | refl => exact .refl
  | step e _ ih => exact .step (.app_x vf l e) ih

-- a call steps to the leaf that its def's case tree walks to
theorem Eval.walk (hk : Book.get B k = some d) (vs : Values B xs)
    (w : walk B d.v [] xs = some (some u)) : Eval B (spine (Ref k) xs) u :=
  .call hk vs (walk_iff.1 w)

-- a pair at quantity 1 is a value when both its fields are
theorem value_tup_iff : Value B (Tup Q1 a b) ↔ Value B a ∧ Value B b := by
  rw [← value_iff, ← value_iff, ← value_iff]; simp [value, Quan.live]

-- a constructor of values is a value
theorem value_ctor (h : ∀ f ∈ fs, Value B f) : Value B (ctor k fs) := by
  refine .tup (fun _ => .lab) ?_
  induction fs with
  | nil => exact .lab
  | cons f fs ih => exact .tup (fun _ => h f (by simp)) (ih fun g hg => h g (by simp [hg]))

theorem value_list (h : ∀ x ∈ xs, Value B x) : Value B (list xs) := by
  induction xs with
  | nil => exact value_ctor nofun
  | cons x xs ih =>
    exact value_ctor (by simpa using ⟨h x (by simp), ih fun y hy => h y (by simp [hy])⟩)

-- each item of a list that is a value is a value
theorem value_list_of : Value B (list s) → ∀ x ∈ s, Value B x := by
  induction s with
  | nil => simp
  | cons x s ih =>
    intro h
    simp only [list, ctor, List.foldr, value_tup_iff] at h
    simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨h.2.1, ih (by simpa [list, ctor] using h.2.2.1)⟩

theorem value_bits : Value B (bits n v) := by
  induction n generalizing v with
  | zero => exact value_ctor nofun
  | succ n ih => exact value_ctor (by simpa using ⟨value_ctor nofun, ih⟩)

theorem value_cell : Value B (cell b) := value_ctor (by simpa using value_bits)

theorem value_bytes : Value B (bytes bs) := value_list (by simpa using fun _ _ => value_cell)

theorem value_nat : Value B (Form.nat n) := by
  induction n with
  | zero => exact value_ctor nofun
  | succ n ih => exact value_ctor (by simpa using ih)

theorem value_quan : Value B (Form.quan q) := by cases q <;> exact value_ctor nofun

theorem value_bool : Value B (Form.bool b) := value_ctor nofun

theorem value_term : Value B (Form.term t) := by
  induction t <;> simp only [Form.term] <;> apply value_ctor <;>
    simp [*, Form.name, value_nat, value_quan, value_bytes, value_list]

theorem value_defs : Value B (Form.defs ds) := by
  apply value_list
  simp only [List.mem_map]
  rintro _ ⟨d, -, rfl⟩
  exact value_ctor (by simpa [Form.name] using ⟨value_bytes, value_term, value_term, value_bool⟩)

theorem value_maybe (h : ∀ x, Value B (f x)) : Value B (Form.maybe f o) := by
  cases o <;> simp only [Form.maybe, Form.some] <;> exact value_ctor (by simp [h])

theorem value_env : Value B (Form.env e) := value_list (by simpa [Form.env] using fun _ _ => value_term)

theorem value_args_form : Value B (Form.args xs) := by
  apply value_list
  simp only [List.mem_map]
  rintro _ ⟨⟨q, x⟩, -, rfl⟩
  exact value_ctor (by simpa using ⟨value_quan, value_term⟩)

-- a constructor of Data is Data
theorem data_ctor (h : ∀ f ∈ fs, Data f) : Data (ctor k fs) := by
  refine .tup (fun _ => .lab) ?_
  induction fs with
  | nil => exact .lab
  | cons f fs ih => exact .tup (fun _ => h f (by simp)) (ih fun g hg => h g (by simp [hg]))

theorem data_list (h : ∀ x ∈ xs, Data x) : Data (list xs) := by
  induction xs with
  | nil => exact data_ctor nofun
  | cons x xs ih =>
    exact data_ctor (by simpa using ⟨h x (by simp), ih fun y hy => h y (by simp [hy])⟩)

theorem data_bits : Data (bits n v) := by
  induction n generalizing v with
  | zero => exact data_ctor nofun
  | succ n ih => exact data_ctor (by simpa using ⟨data_ctor nofun, ih⟩)

theorem data_cell : Data (cell b) := data_ctor (by simpa using data_bits)

theorem data_bytes : Data (bytes bs) := data_list (by simpa using fun _ _ => data_cell)

theorem data_nat : Data (Form.nat n) := by
  induction n with
  | zero => exact data_ctor nofun
  | succ n ih => exact data_ctor (by simpa using ih)

theorem data_quan : Data (Form.quan q) := by cases q <;> exact data_ctor nofun

theorem data_bool : Data (Form.bool b) := data_ctor nofun

theorem data_term : Data (Form.term t) := by
  induction t <;> simp only [Form.term] <;> apply data_ctor <;>
    simp [*, Form.name, data_nat, data_quan, data_bytes, data_list]

theorem data_defs : Data (Form.defs ds) := by
  apply data_list
  simp only [List.mem_map]
  rintro _ ⟨d, -, rfl⟩
  exact data_ctor (by simpa [Form.name] using ⟨data_bytes, data_term, data_term, data_bool⟩)

theorem data_maybe (h : ∀ x, Data (f x)) : Data (Form.maybe f o) := by
  cases o <;> simp only [Form.maybe, Form.some] <;> exact data_ctor (by simp [h])

theorem data_env : Data (Form.env e) := data_list (by simpa [Form.env] using fun _ _ => data_term)

theorem data_args_form : Data (Form.args xs) := by
  apply data_list
  simp only [List.mem_map]
  rintro _ ⟨⟨q, x⟩, -, rfl⟩
  exact data_ctor (by simpa using ⟨data_quan, data_term⟩)
