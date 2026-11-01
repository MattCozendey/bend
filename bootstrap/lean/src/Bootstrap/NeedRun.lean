import Bootstrap.GivesRun
import Bootstrap.Values
import Bootstrap.Copy.Need
import Bootstrap.Copy.Trusted

-- NeedRun
-- =======
--
-- Program.need(p, i, n) and Program.memory(m) (impl.bend), on the bytes p
-- that the Lean writer writes for the book bk, give F of INVARIANTS #4 as Lean
-- computes it (need, memory): 64 × (|p| + S) + 2^24, with S the most nodes of
-- a term that the run from start i reaches within n steps, and the bytes of
-- min(m, 2^16) pages of 2^16 bytes.

open Quan Term

set_option linter.unusedSimpArgs false
set_option maxRecDepth 20000

-- the nodes of a term, as impl.bend's Term.size counts them
def Term.nodes : Term → Nat
  | Var _ | Ref _ | Enu _ | Lab _ | Efq | Rfl => 1
  | Ann a b | Let _ a b | Term.Min a b | All _ a b | App _ a b | Sig _ a b | Tup _ a b | Mat _ a b =>
    a.nodes + b.nodes + 1
  | Typ a | Lam _ a | Prj a => a.nodes + 1
  | Eql a b c | Rwt a b c => a.nodes + (b.nodes + c.nodes) + 1

-- the most nodes of a term that the run from t reaches within n steps of
-- Eval (through step, Interp.lean), t included
def largest (bk : Book) : Nat → Term → Nat
  | 0, t => t.nodes
  | n + 1, t => max t.nodes (match step bk t with
    | none => 0
    | some u => largest bk n u)

-- F of INVARIANTS #4 (C1, approved): 64 × (|p| + S) + 2^24 bytes, for the
-- book bk on the input i, within n steps
def need (bk : Book) (i : List UInt8) (n : Nat) : Nat :=
  64 * ((write bk).length + largest bk n (start i)) + 2 ^ 24

-- the bytes of m pages of 2^16 bytes, up to 2^16 pages
def memory (m : UInt32) : Nat := 65536 * min m.toNat 65536

-- the copies that Program.need and Program.memory need
structure NeedHolds (B : Book) : Prop where
  holds : Holds B
  need : Contains B needCopy
  is_le : Book.get B "Nat.is_le" = some «trustedCopy.Nat.is_le»

namespace Gives

theorem _root_.NeedHolds.get (h : NeedHolds B) (hd : d ∈ needCopy := by simp [needCopy]) :
    Book.get B d.k = some d := h.need d hd

macro "nwalks" d:term : tactic =>
  `(tactic| simp [$d:term, walk, list, ctor, bits, cell, bytes, bindsAt, Quan.live, Quan.fld, takes,
    Term.sub, Env.sub, Term.spine, Form.nat, Form.term, Form.quan, Form.bool, Form.some, Form.maybe, data,
    dbits, dnat, dcell, dbytes, dname, dterm, ddefs])

theorem add_run (h : Holds B) :
    Runs B (spine (Ref "Nat.add") [(Q1, Form.nat a), (Q1, Form.nat b)]) (Form.nat (a + b)) := by
  have hk : Book.get B "Nat.add" = some «evalCopy.Nat.add» := h.eval «evalCopy.Nat.add» (by simp [evalCopy])
  induction a with
  | zero =>
    exact Kit.call hk (.cons (fun _ => value_nat) (.cons (fun _ => value_nat) .nil)) (u := Form.nat b)
      (by nwalks «evalCopy.Nat.add») (by simpa using Runs.refl value_nat)
  | succ a ih =>
    refine Kit.call hk (.cons (fun _ => value_nat) (.cons (fun _ => value_nat) .nil))
      (u := ctor "Succ" [App Q1 (App Q1 (Ref "Nat.add") (Form.nat a)) (Form.nat b)])
      (by nwalks «evalCopy.Nat.add») ?_
    rw [Nat.add_right_comm]
    exact ctor1 ih

theorem value_add (h : Holds B) : Value B (App Q1 (Ref "Nat.add") (Form.nat a)) := by
  have hk : Book.get B "Nat.add" = some «evalCopy.Nat.add» := h.eval «evalCopy.Nat.add» (by simp [evalCopy])
  cases a <;> exact Kit.part (xs := [(Q1, _)]) hk (.cons (fun _ => value_nat) .nil) (by nwalks «evalCopy.Nat.add»)

theorem add_run' (h : Holds B) (rx : Runs B x (Form.nat a)) (ry : Runs B y (Form.nat b)) :
    Runs B (App Q1 (App Q1 (Ref "Nat.add") x) y) (Form.nat (a + b)) := by
  have hk : Book.get B "Nat.add" = some «evalCopy.Nat.add» := h.eval «evalCopy.Nat.add» (by simp [evalCopy])
  exact Kit.run_f (Kit.run_x (Kit.part (xs := []) hk .nil (by nwalks «evalCopy.Nat.add»)) rfl rx
    (.refl (value_add h))) (Kit.run_x (value_add h) rfl ry (add_run h))

theorem value_mul (h : NeedHolds B) : Value B (App Q1 (Ref "Nat.mul") (Form.nat a)) := by
  have hk := h.get (d := «needCopy.Nat.mul»)
  cases a <;> exact Kit.part (xs := [(Q1, _)]) hk (.cons (fun _ => value_nat) .nil) (by nwalks «needCopy.Nat.mul»)

theorem mul_run (h : NeedHolds B) :
    Runs B (spine (Ref "Nat.mul") [(Q1, Form.nat a), (Q2, Form.nat b)]) (Form.nat (a * b)) := by
  have hk := h.get (d := «needCopy.Nat.mul»)
  induction a with
  | zero =>
    exact Kit.call hk (.cons (fun _ => value_nat) (.cons (fun _ => value_nat) .nil)) (u := ctor "Zero" [])
      (by nwalks «needCopy.Nat.mul») (Kit.runs_eq ctor0 (by simp [Form.nat]))
  | succ a ih =>
    refine Kit.call hk (.cons (fun _ => value_nat) (.cons (fun _ => value_nat) .nil))
      (u := App Q1 (App Q1 (Ref "Nat.add") (Form.nat b)) (App Q2 (App Q1 (Ref "Nat.mul") (Form.nat a)) (Form.nat b)))
      (by nwalks «needCopy.Nat.mul») ?_
    rw [Nat.succ_mul, Nat.add_comm]
    exact Kit.run_x (value_add h.holds) rfl ih (add_run h.holds)

theorem mul_run' (h : NeedHolds B) (rx : Runs B x (Form.nat a)) (ry : Runs B y (Form.nat b)) :
    Runs B (App Q2 (App Q1 (Ref "Nat.mul") x) y) (Form.nat (a * b)) := by
  have hk := h.get (d := «needCopy.Nat.mul»)
  exact Kit.run_f (Kit.run_x (Kit.part (xs := []) hk .nil (by nwalks «needCopy.Nat.mul»)) rfl rx
    (.refl (value_mul h))) (Kit.run_x (value_mul h) rfl ry (mul_run h))

theorem nat_run : Runs B (Form.nat n) (Form.nat n) := .refl value_nat

theorem length_run (h : NeedHolds B) :
    Runs B (App Q1 (App Q0 (App Q0 (Ref "List.length") (Lab "Q2")) (Ref "U32")) (bytes p)) (Form.nat p.length) := by
  have hk := h.get (d := «needCopy.List.length»)
  induction p with
  | nil =>
    exact Kit.call (xs := [(Q0, _), (Q0, _), (Q1, _)]) hk (.cons (fun h => by simp [Quan.live] at h)
      (.cons (fun h => by simp [Quan.live] at h) (.cons (fun _ => value_bytes) .nil))) (u := ctor "Zero" [])
      (by nwalks «needCopy.List.length») (Kit.runs_eq ctor0 (by simp [Form.nat]))
  | cons b p ih =>
    refine Kit.call (xs := [(Q0, _), (Q0, _), (Q1, _)]) hk (.cons (fun h => by simp [Quan.live] at h)
      (.cons (fun h => by simp [Quan.live] at h) (.cons (fun _ => value_bytes) .nil)))
      (u := ctor "Succ" [App Q1 (App Q0 (App Q0 (Ref "List.length") (Lab "Q2")) (Ref "U32")) (bytes p)])
      (by nwalks «needCopy.List.length») ?_
    exact ctor1 ih

-- the leaf that Term.size's case tree walks to on the form of t
def sizeLeaf : Term → Term
  | Var _ | Ref _ | Enu _ | Lab _ | Efq | Rfl => ctor "Succ" [ctor "Zero" []]
  | Ann a b | Let _ a b | Term.Min a b | All _ a b | App _ a b | Sig _ a b | Tup _ a b | Mat _ a b =>
    ctor "Succ" [App Q1 (App Q1 (Ref "Nat.add") (App Q1 (Ref "Term.size") (Form.term a)))
      (App Q1 (Ref "Term.size") (Form.term b))]
  | Typ a | Lam _ a | Prj a => ctor "Succ" [App Q1 (Ref "Term.size") (Form.term a)]
  | Eql a b c | Rwt a b c =>
    ctor "Succ" [App Q1 (App Q1 (Ref "Nat.add") (App Q1 (Ref "Term.size") (Form.term a)))
      (App Q1 (App Q1 (Ref "Nat.add") (App Q1 (Ref "Term.size") (Form.term b))) (App Q1 (Ref "Term.size") (Form.term c)))]

theorem size_run (h : NeedHolds B) : Runs B (App Q1 (Ref "Term.size") (Form.term t)) (Form.nat t.nodes) := by
  have hk := h.get (d := «needCopy.Term.size»)
  have key : ∀ t, walk B «needCopy.Term.size».v [] [(Q1, Form.term t)] = some (some (sizeLeaf t)) := by
    intro t; cases t <;> (simp only [sizeLeaf]; nwalks «needCopy.Term.size»)
  induction t <;>
    refine Kit.call (xs := [(Q1, _)]) hk (.cons (fun _ => value_term) .nil) (key _) ?_ <;>
    simp only [sizeLeaf, Term.nodes] <;>
    first
      | exact ctor1 ctor0
      | exact ctor1 (add_run' h.holds ‹_› ‹_›)
      | exact ctor1 ‹_›
      | exact ctor1 (add_run' h.holds ‹_› (add_run' h.holds ‹_› ‹_›))

theorem plain_term : Plain (Form.term t) := by
  have pn : ∀ ks : List String, Plain (list (ks.map Form.name)) := fun ks =>
    plain_list (by simpa [Form.name] using fun _ _ => plain_bytes)
  have pq : ∀ q, Plain (Form.quan q) := fun q => by cases q <;> exact plain_ctor nofun
  induction t <;> simp only [Form.term] <;> apply plain_ctor <;>
    simp [*, Form.name, plain_nat, plain_bytes]

theorem plain_defs : Plain (Form.defs ds) := by
  apply plain_list
  simp only [List.mem_map]
  rintro _ ⟨d, -, rfl⟩
  exact plain_ctor (by simpa [Form.name, Form.bool] using ⟨plain_bytes, plain_term, plain_term,
    plain_ctor (k := if d.o then "True" else "False") nofun⟩)

theorem max_run (h : NeedHolds B) :
    Runs B (spine (Ref "Nat.max") [(Q2, Form.nat a), (Q2, Form.nat b)]) (Form.nat (max a b)) := by
  have hk := h.get (d := «needCopy.Nat.max»)
  have vs : ∀ a b, Values B [(Q2, Form.nat a), (Q2, Form.nat b)] := fun _ _ =>
    .cons (fun _ => value_nat) (.cons (fun _ => value_nat) .nil)
  induction a generalizing b with
  | zero => exact Kit.call hk (vs _ _) (u := Form.nat b) (by nwalks «needCopy.Nat.max») (by simpa using nat_run)
  | succ a ih =>
    cases b with
    | zero => exact Kit.call hk (vs _ _) (u := Form.nat (a + 1)) (by nwalks «needCopy.Nat.max») (by simpa using nat_run)
    | succ b =>
      refine Kit.call hk (vs _ _) (u := ctor "Succ" [spine (Ref "Nat.max") [(Q2, Form.nat a), (Q2, Form.nat b)]])
        (by nwalks «needCopy.Nat.max») ?_
      rw [Nat.succ_max_succ]; exact ctor1 ih

theorem max_run' (h : NeedHolds B) (rx : Runs B x (Form.nat a)) (ry : Runs B y (Form.nat b)) :
    Runs B (App Q2 (App Q2 (Ref "Nat.max") x) y) (Form.nat (max a b)) := by
  have hk := h.get (d := «needCopy.Nat.max»)
  show Runs B (spine (Ref _) [(Q2, _), (Q2, _)]) _
  refine Kit.runs_args hk (.r rfl rx (.r rfl ry .nil)) ?_ (max_run h)
  intro m hm; simp at hm
  rcases m with _ | _ | m <;> first | omega | (cases a <;> nwalks «needCopy.Nat.max»)

theorem go_run (h : NeedHolds B) {bk : Book} :
    Runs B (spine (Ref "Program.largest.go") [(Q1, Form.nat n), (Q2, Form.defs bk.defs), (Q2, Form.term t)])
      (Form.nat (largest bk n t)) := by
  have hk := h.get (d := «needCopy.Program.largest.go»)
  have hx := h.get (d := «needCopy.Program.largest.next»)
  have hs : Book.get B "Eval.step" = some «evalCopy.Eval.step» := h.holds.eval «evalCopy.Eval.step» (by simp [evalCopy])
  have vs : ∀ n t, Values B [(Q1, Form.nat n), (Q2, Form.defs bk.defs), (Q2, Form.term t)] := fun _ _ =>
    .cons (fun _ => value_nat) (.cons (fun _ => value_defs) (.cons (fun _ => value_term) .nil))
  induction n generalizing t with
  | zero =>
    exact Kit.call hk (vs 0 t) (u := App Q1 (Ref "Term.size") (Form.term t)) (by nwalks «needCopy.Program.largest.go»)
      (size_run h)
  | succ n ih =>
    let clo := Lam Q1 (App Q2 (App Q2 (App Q1 (Ref "Program.largest.go") (Form.nat n)) (Form.defs bk.defs)) (Var 0))
    refine Kit.call hk (vs (n + 1) t) (u := App Q2 (App Q2 (Ref "Nat.max") (App Q1 (Ref "Term.size") (Form.term t)))
      (App Q1 (App Q1 (Ref "Program.largest.next") (spine (Ref "Eval.step") [(Q2, Form.defs bk.defs),
        (Q2, Form.term t)])) clo)) ?_ ?_
    · simp [«needCopy.Program.largest.go», walk, bindsAt, Quan.live, Quan.fld, takes, Term.sub, Env.sub,
        Term.spine, Form.nat, ctor, data, dnat, ddefs, dterm, clo, plain_defs.ren, Subst.up]
      exact plain_nat.ren
    refine max_run' h (size_run h) ?_
    show Runs B (spine (Ref _) [(Q1, _), (Q1, _)]) _
    refine Kit.runs_args hx (.r rfl (EvalCopy.step_copy h.holds.eval) (.v rfl .lam .nil)) ?_ ?_
    · intro m hm; simp at hm
      rcases m with _ | _ | m <;> first | omega | (cases step bk t <;> nwalks «needCopy.Program.largest.next»)
    cases hst : step bk t with
    | none =>
      exact Kit.call hx (.cons (fun _ => value_maybe' (fun _ => value_term)) (.cons (fun _ => .lam) .nil))
        (u := ctor "Zero" []) (by nwalks «needCopy.Program.largest.next»)
        (Kit.runs_eq ctor0 (by simp [largest, hst, Form.nat]))
    | some u =>
      refine Kit.call hx (.cons (fun _ => value_maybe' (fun _ => value_term)) (.cons (fun _ => .lam) .nil))
        (u := App Q1 clo (Form.term u)) (by nwalks «needCopy.Program.largest.next») ?_
      refine .step (.beta rfl (fun _ => value_term) nofun) ?_
      simp only [clo, Term.inst, Term.sub, Subst.one, plain_nat.sub, plain_defs.sub]
      exact Kit.runs_eq ih (by simp [largest, hst])

theorem largest_run (h : NeedHolds B) :
    Runs B (spine (Ref "Program.largest") [(Q1, bytes (write bk)), (Q1, bytes i), (Q1, Form.nat n)])
      (Form.nat (largest bk n (start i))) := by
  have hk := h.get (d := «needCopy.Program.largest»)
  have ho := h.get (d := «needCopy.Program.largest.of»)
  have hg := h.get (d := «needCopy.Program.largest.go»)
  refine Kit.call hk (.cons (fun _ => value_bytes) (.cons (fun _ => value_bytes) (.cons (fun _ => value_nat) .nil)))
    (u := spine (Ref "Program.largest.of") [(Q1, App Q1 (Ref "Book.read") (bytes (write bk))), (Q1, bytes i),
      (Q1, Form.nat n)]) (by nwalks «needCopy.Program.largest») ?_
  refine Kit.runs_args ho (.r rfl (read_write h.holds.reader) (.v rfl value_bytes (.v rfl value_nat .nil))) ?_ ?_
  · intro m hm; simp at hm
    rcases m with _ | _ | _ | m <;> first | omega | nwalks «needCopy.Program.largest.of»
  refine Kit.call ho (.cons (fun _ => value_ctor (by simp [value_defs])) (.cons (fun _ => value_bytes)
    (.cons (fun _ => value_nat) .nil)))
    (u := spine (Ref "Program.largest.go") [(Q1, Form.nat n), (Q2, Form.defs bk.defs),
      (Q2, App Q1 (Ref "Program.start") (bytes i))]) (by nwalks «needCopy.Program.largest.of») ?_
  refine Kit.runs_args hg (.v rfl value_nat (.v rfl value_defs (.r rfl (start_run h.holds) .nil))) ?_ (go_run h)
  intro m hm; simp at hm
  rcases m with _ | _ | _ | m <;> first | omega | (cases n <;> nwalks «needCopy.Program.largest.go»)

theorem need_run (h : NeedHolds B) :
    Runs B (spine (Ref "Program.need") [(Q2, bytes (write bk)), (Q1, bytes i), (Q1, Form.nat n)])
      (Form.nat (need bk i n)) := by
  have hk := h.get (d := «needCopy.Program.need»)
  refine Kit.call hk (.cons (fun _ => value_bytes) (.cons (fun _ => value_bytes) (.cons (fun _ => value_nat) .nil)))
    (u := App Q1 (App Q1 (Ref "Nat.add") (App Q2 (App Q1 (Ref "Nat.mul") (Form.nat 64))
      (App Q1 (App Q1 (Ref "Nat.add") (App Q1 (App Q0 (App Q0 (Ref "List.length") (Lab "Q2")) (Ref "U32"))
        (bytes (write bk)))) (spine (Ref "Program.largest") [(Q1, bytes (write bk)), (Q1, bytes i),
          (Q1, Form.nat n)]))))
      (App Q1 (App Q1 (Ref "Nat.add") (App Q2 (App Q1 (Ref "Nat.mul") (Form.nat 4096)) (Form.nat 4096)))
        (ctor "Zero" [])))
    (by simp [«needCopy.Program.need», walk, bindsAt, Quan.live, Quan.fld, takes, Term.sub, Env.sub,
      Term.spine, ctor, data, dbytes, dnat, plain_nat.sub]) ?_
  have r := add_run' h.holds (mul_run' h (nat_run (n := 64)) (add_run' h.holds (length_run (p := write bk) h)
    (largest_run (bk := bk) (i := i) (n := n) h)))
    (add_run' h.holds (mul_run' h (nat_run (n := 4096)) (nat_run (n := 4096))) (nat_run (n := 0)))
  exact Kit.runs_eq r (congrArg Form.nat (by unfold need; rfl))

-- Comparisons
-- -----------

theorem cmp_run (h : Holds B) :
    Runs B (spine (Ref "Nat.cmp") [(Q1, Form.nat a), (Q1, Form.nat b)]) (cmpForm (compare a b)) := by
  have hk : Book.get B "Nat.cmp" = some «evalCopy.Nat.cmp» := h.eval «evalCopy.Nat.cmp» (by simp [evalCopy])
  have vs : ∀ a b, Values B [(Q1, Form.nat a), (Q1, Form.nat b)] := fun _ _ =>
    .cons (fun _ => value_nat) (.cons (fun _ => value_nat) .nil)
  induction a generalizing b with
  | zero =>
    cases b
    · exact Kit.call hk (vs _ _) (u := cmpForm .eq) (by nwalks «evalCopy.Nat.cmp»; rfl) (.refl value_cmp)
    · exact Kit.call hk (vs _ _) (u := cmpForm .lt) (by nwalks «evalCopy.Nat.cmp»; rfl) (Kit.runs_eq (.refl value_cmp) (by
        simp [Nat.compare_eq_lt.2 (Nat.zero_lt_succ _)]))
  | succ a ih =>
    cases b
    · exact Kit.call hk (vs _ _) (u := cmpForm .gt) (by nwalks «evalCopy.Nat.cmp»; rfl) (Kit.runs_eq (.refl value_cmp) (by
        simp [Nat.compare_eq_gt.2 (Nat.zero_lt_succ _)]))
    · rename_i b
      refine Kit.call hk (vs _ _) (u := spine (Ref "Nat.cmp") [(Q1, Form.nat a), (Q1, Form.nat b)])
        (by nwalks «evalCopy.Nat.cmp») ?_
      refine Kit.runs_eq ih (congrArg cmpForm ?_)
      rcases Nat.lt_trichotomy a b with hab | hab | hab
      · rw [Nat.compare_eq_lt.2 hab, Nat.compare_eq_lt.2 (by omega)]
      · rw [Nat.compare_eq_eq.2 hab, Nat.compare_eq_eq.2 (by omega)]
      · rw [Nat.compare_eq_gt.2 hab, Nat.compare_eq_gt.2 (by omega)]

theorem cmp_le_run (h : NeedHolds B) :
    Runs B (App Q1 (Ref "Cmp.is_le") (cmpForm o)) (Form.bool (o != .gt)) := by
  have hk := h.get (d := «needCopy.Cmp.is_le»)
  cases o <;> exact Kit.call (xs := [(Q1, _)]) hk (.cons (fun _ => value_cmp) .nil)
    (by simp [cmpForm]; nwalks «needCopy.Cmp.is_le») (.refl value_bool)

theorem is_le_run (h : NeedHolds B) (rx : Runs B x (Form.nat a)) (ry : Runs B y (Form.nat b)) :
    Runs B (App Q1 (App Q1 (Ref "Nat.is_le") x) y) (Form.bool (decide (a ≤ b))) := by
  have hc := h.get (d := «needCopy.Cmp.is_le»)
  show Runs B (spine (Ref _) [(Q1, _), (Q1, _)]) _
  refine Kit.runs_args h.is_le (.r rfl rx (.r rfl ry .nil)) ?_ ?_
  · intro m hm; simp at hm
    rcases m with _ | _ | m <;> first | omega | simp [«trustedCopy.Nat.is_le», walk, takes, bindsAt, Quan.live]
  refine Kit.call h.is_le (.cons (fun _ => value_nat) (.cons (fun _ => value_nat) .nil))
    (u := App Q1 (Ref "Cmp.is_le") (spine (Ref "Nat.cmp") [(Q1, Form.nat a), (Q1, Form.nat b)]))
    (by simp [«trustedCopy.Nat.is_le», walk, takes, bindsAt, Quan.live, Term.sub, Env.sub, Term.spine]) ?_
  refine Kit.run_x (Kit.part (xs := []) hc .nil (by nwalks «needCopy.Cmp.is_le»)) rfl (cmp_run h.holds)
    (Kit.runs_eq (cmp_le_run h) ?_)
  congr 1
  cases ho : compare a b
  · rw [decide_eq_true (by have := Nat.compare_eq_lt.1 ho; omega)]; rfl
  · rw [decide_eq_true (by have := Nat.compare_eq_eq.1 ho; omega)]; rfl
  · rw [decide_eq_false (by have := Nat.compare_eq_gt.1 ho; omega)]; rfl

theorem u32_is_le (h : NeedHolds B) :
    Runs B (App Q1 (App Q1 (Ref "U32.is_le") (ctor "U32" [bits 32 v])) (ctor "U32" [bits 32 w]))
      (Form.bool (compare (v % 2 ^ 32) (w % 2 ^ 32) != .gt)) := by
  have hk := h.get (d := «needCopy.U32.is_le»)
  have hl := h.get (d := «needCopy.Cmp.is_le»)
  have hc : Book.get B "U32.cmp" = some «evalCopy.U32.cmp» := h.holds.eval «evalCopy.U32.cmp» (by simp [evalCopy])
  have vu : ∀ v, Value B (ctor "U32" [bits 32 v]) := fun _ => value_ctor (by simp [value_bits])
  refine Kit.call (xs := [(Q1, _), (Q1, _)]) hk (.cons (fun _ => vu v) (.cons (fun _ => vu w) .nil))
    (u := App Q1 (Ref "Cmp.is_le") (App Q1 (App Q1 (Ref "U32.cmp") (ctor "U32" [bits 32 v])) (ctor "U32" [bits 32 w])))
    (by nwalks «needCopy.U32.is_le») ?_
  have rc : Runs B (App Q1 (App Q1 (Ref "U32.cmp") (ctor "U32" [bits 32 v])) (ctor "U32" [bits 32 w]))
      (cmpForm (wc 32 v w)) :=
    Kit.call (xs := [(Q1, _), (Q1, _)]) hc (.cons (fun _ => vu v) (.cons (fun _ => vu w) .nil))
      (u := App Q1 (App Q1 (App Q1 (Ref "Word.cmp") (Form.nat 32)) (bits 32 v)) (bits 32 w))
      (by simp [walk, «evalCopy.U32.cmp», ctor, takes, bindsAt, Quan.live, Quan.fld, sub, spine, Env.sub, Form.nat,
        data, dbits])
      (word_cmp h.holds.eval)
  rw [wc_compare] at rc
  exact Kit.run_x (Kit.part (xs := []) hl .nil (by nwalks «needCopy.Cmp.is_le»)) rfl rc (cmp_le_run h)

theorem memory_run (h : NeedHolds B) :
    Runs B (App Q1 (Ref "Program.memory") (Form.u32 m)) (Form.nat (memory m)) := by
  have hk := h.get (d := «needCopy.Program.memory»)
  have hm := h.get (d := «needCopy.Wasm.min»)
  have hi := h.get (d := «needCopy.Wasm.min.if»)
  have ht := h.holds.reader «reader.U32.to_nat» (by simp [reader])
  have vu : ∀ v, Value B (ctor "U32" [bits 32 v]) := fun _ => value_ctor (by simp [value_bits])
  have l : Runs B (Ref "U32.lit65536") (ctor "U32" [bits 32 65536]) := by
    have e : «needCopy.U32.lit65536».v = ctor "U32" [bits 32 65536] := by decide
    have := body_run (h.get (d := «needCopy.U32.lit65536»)) (e ▸ vu _) (by rw [e]; rfl) (by rw [e]; simp [ctor])
    rwa [e] at this
  have hlt : m.toNat < 2 ^ 32 := m.toNat_lt
  -- Wasm.min(m, 2^16)
  have rmin : Runs B (App Q2 (App Q2 (Ref "Wasm.min") (Form.u32 m)) (Ref "U32.lit65536"))
      (ctor "U32" [bits 32 (min m.toNat 65536)]) := by
    show Runs B (spine (Ref _) [(Q2, _), (Q2, _)]) _
    refine Kit.runs_args hm (.v rfl (vu _) (.r rfl l .nil)) ?_ ?_
    · intro k hk; simp at hk
      rcases k with _ | _ | k <;> first | omega | simp [«needCopy.Wasm.min», walk, takes, bindsAt, Quan.live,
        Form.u32, ctor, data, dbits]
    refine Kit.call hm (.cons (fun _ => vu _) (.cons (fun _ => vu _) .nil))
      (u := App Q1 (App Q1 (App Q1 (Ref "Wasm.min.if") (App Q1 (App Q1 (Ref "U32.is_le") (ctor "U32" [bits 32 m.toNat]))
        (ctor "U32" [bits 32 65536]))) (ctor "U32" [bits 32 m.toNat])) (ctor "U32" [bits 32 65536]))
      (by simp [«needCopy.Wasm.min», walk, takes, bindsAt, Quan.live, Term.sub, Env.sub, Term.spine, Form.u32,
        data, ctor, dbits]) ?_
    show Runs B (spine (Ref _) [(Q1, _), (Q1, _), (Q1, _)]) _
    have e1 : m.toNat % 2 ^ 32 = m.toNat := Nat.mod_eq_of_lt hlt
    have rl := u32_is_le h (v := m.toNat) (w := 65536)
    rw [e1, show (65536 : Nat) % 2 ^ 32 = 65536 from rfl] at rl
    refine Kit.runs_args hi (.r rfl rl (.v rfl (vu _) (.v rfl (vu _) .nil))) ?_ ?_
    · intro k hk; simp at hk
      rcases k with _ | _ | _ | k <;> first | omega |
        (cases (compare m.toNat 65536 != .gt) <;> nwalks «needCopy.Wasm.min.if»)
    by_cases hle : m.toNat ≤ 65536
    · have : (compare m.toNat 65536 != .gt) = true := by
        have : compare m.toNat 65536 ≠ .gt := fun e => by rw [Nat.compare_eq_gt] at e; omega
        simpa using this
      rw [this, Nat.min_eq_left hle]
      exact Kit.call hi (.cons (fun _ => value_bool) (.cons (fun _ => vu _) (.cons (fun _ => vu _) .nil)))
        (by nwalks «needCopy.Wasm.min.if») (.refl (vu _))
    · have : (compare m.toNat 65536 != .gt) = false := by
        have : compare m.toNat 65536 = .gt := Nat.compare_eq_gt.2 (by omega)
        simp [this]
      rw [this, Nat.min_eq_right (by omega)]
      exact Kit.call hi (.cons (fun _ => value_bool) (.cons (fun _ => vu _) (.cons (fun _ => vu _) .nil)))
        (by nwalks «needCopy.Wasm.min.if») (.refl (vu _))
  -- U32.to_nat
  have rt : Runs B (App Q1 (Ref "U32.to_nat") (App Q2 (App Q2 (Ref "Wasm.min") (Form.u32 m)) (Ref "U32.lit65536")))
      (Form.nat (min m.toNat 65536)) := by
    refine Kit.run_x (Kit.part (xs := []) ht .nil (by simp [walk, «reader.U32.to_nat», takes])) rfl rmin ?_
    refine Kit.call (xs := [(Q1, _)]) ht (.cons (fun _ => vu _) .nil)
      (u := App Q1 (App Q1 (Ref "Word.to_nat") (Form.nat 32)) (bits 32 (min m.toNat 65536)))
      (by simp [walk, «reader.U32.to_nat», ctor, takes, Quan.live, Quan.fld, sub, spine, bindsAt, Env.sub, Form.nat])
      ?_
    have r := word_nat h.holds.reader (n := 32) (v := min m.toNat 65536)
    rwa [Nat.mod_eq_of_lt (by omega)] at r
  refine Kit.call (xs := [(Q1, _)]) hk (.cons (fun _ => vu _) .nil)
    (u := App Q2 (App Q1 (Ref "Nat.mul") (App Q1 (App Q1 (Ref "Nat.add") (App Q2 (App Q1 (Ref "Nat.mul") (Form.nat 16))
      (Form.nat 4096))) (ctor "Zero" []))) (App Q1 (Ref "U32.to_nat") (App Q2 (App Q2 (Ref "Wasm.min") (Form.u32 m))
        (Ref "U32.lit65536"))))
    (by simp [«needCopy.Program.memory», walk, takes, bindsAt, Quan.live, Term.sub, Env.sub, Term.spine, Form.u32,
      data, ctor, dbits, plain_nat.sub]) ?_
  have r := mul_run' h (add_run' h.holds (mul_run' h (nat_run (n := 16)) (nat_run (n := 4096))) (nat_run (n := 0))) rt
  exact Kit.runs_eq r (congrArg Form.nat (by unfold memory; rfl))

end Gives

namespace Gives

-- Nat.is_le(Program.need(p, i, n), Program.memory(m)) says whether F fits in
-- the memory of m pages
theorem big_run (h : NeedHolds B) :
    Runs B (App Q1 (App Q1 (Ref "Nat.is_le") (spine (Ref "Program.need") [(Q2, bytes (write bk)), (Q1, bytes i),
      (Q1, Form.nat n)])) (App Q1 (Ref "Program.memory") (Form.u32 m)))
      (Form.bool (decide (need bk i n ≤ memory m))) :=
  is_le_run h (need_run h) (memory_run h)

end Gives
