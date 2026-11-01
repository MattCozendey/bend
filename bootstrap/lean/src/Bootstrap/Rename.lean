import Bootstrap.Code

-- Rename
-- ======
--
-- A book runs as itself after a renaming of its names (its defs' names, refs
-- and labels) by an involution σ that keeps the labels of quantities. `bend -o`
-- names the defs and labels of an imported file with a prefix (impl.Term.Var
-- for impl.bend's Term.Var), so a book that imports impl.bend holds its defs
-- renamed: the laws about impl.bend's own book still hold there, through
-- Rename.book.

open Quan Term

namespace Rename

variable (σ : String → String)

def term : Term → Term
  | Var i => Var i
  | Ref k => Ref (σ k)
  | Ann x T => Ann (term x) (term T)
  | Let q v f => Let q (term v) (term f)
  | Typ q => Typ (term q)
  | Term.Min a b => Term.Min (term a) (term b)
  | All q A B => All q (term A) (term B)
  | Lam q f => Lam q (term f)
  | App q f x => App q (term f) (term x)
  | Sig q A B => Sig q (term A) (term B)
  | Tup q a b => Tup q (term a) (term b)
  | Prj h => Prj (term h)
  | Enu ks => Enu (ks.map σ)
  | Lab k => Lab (σ k)
  | Mat k h m => Mat (σ k) (term h) (term m)
  | Efq => Efq
  | Eql a b T => Eql (term a) (term b) (term T)
  | Rfl => Rfl
  | Rwt e P f => Rwt (term e) (term P) (term f)

def defn (d : Def) : Def := ⟨σ d.k, term σ d.T, term σ d.v, d.o⟩

def arg (a : Arg) : Arg := (a.1, term σ a.2)

-- the book of the renamed defs
def book (B : Book) : Book := Book.of (B.defs.map (defn σ))

-- σ is an involution that keeps the labels of quantities
structure Ok : Prop where
  inv : ∀ s, σ (σ s) = s
  qs : ∀ s ∈ QS, σ s = s

variable {σ}

theorem Ok.inj (h : Ok σ) : σ a = σ b ↔ a = b :=
  ⟨fun e => by rw [← h.inv a, e, h.inv], fun e => e ▸ rfl⟩

theorem term_term (h : Ok σ) : term σ (term σ t) = t := by
  induction t <;> simp [term, h.inv, *]
  case Enu ks => simp [Function.comp_def, h.inv]

theorem defn_defn (h : Ok σ) : defn σ (defn σ d) = d := by
  simp [defn, h.inv, term_term h]

theorem term_ren : term σ (ren r t) = ren r (term σ t) := by
  induction t generalizing r <;> simp [term, Term.ren, *]

theorem term_up : term σ (Subst.up s i) = Subst.up (term σ ∘ s) i := by
  cases i <;> simp [Subst.up, term, term_ren]

theorem up_comm : term σ ∘ Subst.up s = Subst.up (term σ ∘ s) := funext fun _ => term_up

theorem term_sub : term σ (sub s t) = sub (term σ ∘ s) (term σ t) := by
  induction t generalizing s <;> simp [term, Term.sub, up_comm, *]

theorem term_inst : term σ (Term.inst f v) = Term.inst (term σ f) (term σ v) := by
  simp only [Term.inst, term_sub]
  congr 1; funext i; cases i <;> rfl

theorem term_spine : term σ (spine t xs) = spine (term σ t) (xs.map (arg σ)) := by
  induction xs generalizing t with
  | nil => rfl
  | cons a xs ih => obtain ⟨q, x⟩ := a; simp [spine, ih, term, arg]

theorem term_env : term σ (Env.sub e i) = Env.sub (e.map (term σ)) i := by
  induction e generalizing i with
  | nil => rfl
  | cons x e ih => cases i <;> simp [Env.sub, ih]

theorem term_env' : term σ ∘ Env.sub e = Env.sub (e.map (term σ)) := funext fun _ => term_env

theorem takes_term : takes (term σ t) = takes t := by cases t <;> rfl

theorem unspine_term : unspine (term σ t) (xs.map (arg σ)) =
    ((unspine t xs).1 |> term σ, (unspine t xs).2.map (arg σ)) := by
  induction t generalizing xs <;> simp [unspine, term, arg, *]
  case App q f x ihf _ => simpa [arg] using ihf (xs := (q, x) :: xs)

theorem node_term : node (term σ t) = node t := by
  cases t <;> try rfl
  case App q f x =>
    cases x <;> try rfl
    have := unspine_term (σ := σ) (t := f) (xs := [])
    simp only [List.map_nil] at this
    simp only [node, term]; rw [this]; exact takes_term

theorem data_term : Data t → Data (term σ t) := by
  intro h; induction h with
  | lab => exact .lab
  | rfl => exact .rfl
  | tup _ _ iha ihb => exact .tup iha ihb

theorem get_book (h : Ok σ) : Book.get (book σ B) k = (Book.get B (σ k)).map (defn σ) := by
  simp only [get_find, book, Book.of]
  generalize B.defs = ds
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    have e : ((defn σ d).k == k) = (d.k == σ k) := by
      have : σ d.k = k ↔ d.k = σ k := ⟨fun e => e ▸ (h.inv _).symm, fun e => e ▸ h.inv _⟩
      show (σ d.k == k) = (d.k == σ k)
      by_cases e : d.k = σ k
      · simp [e, h.inv]
      · have : ¬ σ d.k = k := mt this.1 e
        rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact ⟨fun x => (this x).elim, fun x => (e x).elim⟩
    simp only [List.map_cons, List.find?_cons, e]
    cases d.k == σ k <;> simp [ih]

-- each def of ds, renamed, is in B: so each def of ds is in the renamed B
theorem contains_book (h : Ok σ) (hc : Contains B (ds.map (defn σ))) : Contains (book σ B) ds := by
  intro d hd
  rw [get_book h, show σ d.k = (defn σ d).k from rfl, hc _ (List.mem_map_of_mem hd)]
  simp [defn_defn h]

theorem walk_term (h : Ok σ) (w : Walk B t e xs o) :
    Walk (book σ B) (term σ t) (e.map (term σ)) (xs.map (arg σ)) (o.map (term σ)) := by
  induction w with
  | lam hl hd _ ih => exact .lam hl (fun e => data_term (hd e)) ih
  | prj hl _ ih => exact .prj hl ih
  | hit hl _ ih => exact .hit hl ih
  | miss hl hj _ ih => exact .miss hl (fun e => hj ((h.inj).1 e)) ih
  | app hn _ ih =>
    refine .app (by rw [← node_term (σ := σ)] at hn; exact hn) ?_
    simpa [arg, term_env] using ih
  | need ht => exact .need (by rw [takes_term]; exact ht)
  | done hn =>
    simp only [Option.map_some, term_spine, term_sub, term_env']
    exact .done (by rw [node_term]; exact hn)

mutual
theorem value_term (h : Ok σ) : Value B t → Value (book σ B) (term σ t)
  | .lam => .lam
  | .prj => .prj
  | .mat => .mat
  | .efq => .efq
  | .lab => .lab
  | .rfl => .rfl
  | .typ => .typ
  | .all => .all
  | .sig => .sig
  | .enu => .enu
  | .eql => .eql
  | .tup va vb => .tup (fun l => value_term h (va l)) (value_term h vb)
  | .call (k := k) (d := d) hk vs w => by
    rw [term_spine]
    exact .call (d := defn σ d) (by rw [get_book h, h.inv, hk]; rfl) (values_term h vs)
      (by simpa [defn] using walk_term h w)

theorem values_term (h : Ok σ) : Values B xs → Values (book σ B) (xs.map (arg σ))
  | .nil => .nil
  | .cons v vs => .cons (fun l => value_term h (v l)) (values_term h vs)
end

theorem qmin_term (h : Ok σ) (hi : i ∈ QS) (hj : j ∈ QS) :
    term σ (Term.qmin (Lab i) (Lab j)) = Term.qmin (Lab i) (Lab j) := by
  simp only [QS, List.mem_cons, List.not_mem_nil, or_false] at hi hj
  have : ∀ s ∈ QS, σ s = s := h.qs
  simp only [QS, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at this
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
    simp [Term.qmin, term, this]

theorem eval_term (h : Ok σ) (s : Eval B t u) : Eval (book σ B) (term σ t) (term σ u) := by
  induction s with
  | ann => exact .ann
  | app_f _ ih => exact .app_f ih
  | app_x vf hl _ ih => exact .app_x (value_term h vf) hl ih
  | beta hl hv hd =>
    rw [term_inst]; exact .beta hl (fun l => value_term h (hv l)) (fun e => data_term (hd e))
  | split hl v => exact .split hl (value_term h v)
  | hit hl => exact .hit hl
  | miss hl hj => exact .miss hl (fun e => hj ((h.inj).1 e))
  | call hk vs w =>
    rw [term_spine]
    exact .call (by rw [get_book h, h.inv, hk]; rfl) (values_term h vs) (by simpa [defn] using walk_term h w)
  | lett hl _ ih => exact .lett hl ih
  | unlet hv hd => rw [term_inst]; exact .unlet (fun l => value_term h (hv l)) (fun e => data_term (hd e))
  | tup_a hl _ ih => exact .tup_a hl ih
  | tup_b va _ ih => exact .tup_b (fun l => value_term h (va l)) ih
  | rwt _ ih => exact .rwt ih
  | cast => exact .cast
  | min_a _ ih => exact .min_a ih
  | min_b va _ ih => exact .min_b (value_term h va) ih
  | @meet i j hi hj =>
    rw [qmin_term h hi hj]
    have : ∀ s ∈ QS, σ s = s := h.qs
    have e : term σ (Term.Min (Lab i) (Lab j)) = Term.Min (Lab i) (Lab j) := by
      simp [term, this _ hi, this _ hj]
    rw [e]; exact .meet hi hj

theorem steps_term (h : Ok σ) (s : Steps B n t u) : Steps (book σ B) n (term σ t) (term σ u) := by
  induction s with
  | refl => exact .refl
  | step e _ ih => exact .step (eval_term h e) ih

theorem runs_term (h : Ok σ) : Runs B t v → Runs (book σ B) (term σ t) (term σ v)
  | ⟨n, s, v⟩ => ⟨n, steps_term h s, value_term h v⟩

-- the renamed book of the renamed book is the book
theorem book_book (h : Ok σ) : book σ (book σ B) = B := by
  obtain ⟨ds, lib, ok⟩ := B
  simp only [book, Book.of, List.map_map, Function.comp_def, defn_defn h, List.map_id']
  subst ok; rfl

-- B runs t to v exactly when the renamed B runs the renamed t to the renamed v
theorem runs_iff (h : Ok σ) : Runs (book σ B) (term σ t) (term σ v) ↔ Runs B t v := by
  refine ⟨fun r => ?_, runs_term h⟩
  have := runs_term h r
  rwa [book_book h, term_term h, term_term h] at this

theorem runs_iff' (h : Ok σ) : Runs (book σ B) t v ↔ Runs B (term σ t) (term σ v) := by
  rw [← runs_iff (B := B) h, term_term h, term_term h]

end Rename
