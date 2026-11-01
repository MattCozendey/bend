import Bootstrap.Join
import Bootstrap.Impl
import Bootstrap.Copy.Eval

-- Values
-- ======
--
-- The Bend values that the theorems of Compiler.lean pass to a law: a Nat, a
-- list of bytes, a U32. They are closed, live, renamed as themselves, and
-- typed at Base's Nat, List<&2, U32> and U32 in a book that holds Base's
-- defs of those types; and a value of type Nat is the form of a Nat.

open Quan Term

set_option linter.unusedSimpArgs false

-- a U32, as `bend -o` writes a value of Base's U32
def Form.u32 (m : UInt32) : Term := ctor "U32" [bits 32 m.toNat]

-- Plain terms (Join.lean)
-- -----------------------

theorem plain_ctor (h : ∀ f ∈ fs, Plain f) : Plain (ctor k fs) := by
  refine .tup rfl .lab ?_
  induction fs with
  | nil => exact .lab
  | cons f fs ih => exact .tup rfl (h f (by simp)) (ih fun g hg => h g (by simp [hg]))

theorem plain_list (h : ∀ x ∈ xs, Plain x) : Plain (list xs) := by
  induction xs with
  | nil => exact plain_ctor nofun
  | cons x xs ih => exact plain_ctor (by simpa using ⟨h x (by simp), ih fun y hy => h y (by simp [hy])⟩)

theorem plain_bits : Plain (bits n v) := by
  induction n generalizing v with
  | zero => exact plain_ctor nofun
  | succ n ih => exact plain_ctor (by simpa using ⟨plain_ctor nofun, ih⟩)

theorem plain_cell : Plain (cell b) := plain_ctor (by simpa using plain_bits)

theorem plain_bytes : Plain (bytes bs) := plain_list (by simpa using fun _ _ => plain_cell)

theorem plain_nat : Plain (Form.nat n) := by
  induction n with
  | zero => exact plain_ctor nofun
  | succ n ih => exact plain_ctor (by simpa using ih)

theorem plain_u32 : Plain (Form.u32 m) := plain_ctor (by simpa using plain_bits)

theorem Plain.sub (h : Plain t) : Term.sub s t = t := by
  induction h <;> simp [Term.sub, *]

theorem Plain.ren (h : Plain t) : Term.ren r t = t := by
  induction h <;> simp [Term.ren, *]

theorem Plain.closed (h : Plain t) : Term.Closed t := fun _ => h.sub

theorem Plain.value (h : Plain t) : Value B t := by
  induction h with
  | lab => exact .lab
  | rfl => exact .rfl
  | tup _ _ _ iha ihb => exact .tup (fun _ => iha) ihb

theorem Plain.data (h : Plain t) : Data t := by
  induction h with
  | lab => exact .lab
  | rfl => exact .rfl
  | tup _ _ _ iha ihb => exact .tup (fun _ => iha) ihb

theorem Plain.live (h : Plain t) : Term.live g top t = true := by
  induction h generalizing top <;> simp [Term.live, *]

-- impl keeps Base's names
-- -----------------------

macro "kept_name" : tactic => `(tactic| exact impl_kept (by decide))

@[simp] theorem impl_main : impl "main" = "main" := by kept_name
@[simp] theorem impl_Q0 : impl "Q0" = "Q0" := by kept_name
@[simp] theorem impl_Q1 : impl "Q1" = "Q1" := by kept_name
@[simp] theorem impl_Q2 : impl "Q2" = "Q2" := by kept_name
@[simp] theorem impl_unit : impl "()" = "()" := by kept_name
@[simp] theorem impl_Tuple : impl "Tuple" = "Tuple" := by kept_name
@[simp] theorem impl_Exists : impl "Exists" = "Exists" := by kept_name
@[simp] theorem impl_Zero : impl "Zero" = "Zero" := by kept_name
@[simp] theorem impl_Succ : impl "Succ" = "Succ" := by kept_name
@[simp] theorem impl_Nat : impl "Nat" = "Nat" := by kept_name
@[simp] theorem impl_Nat_arms : impl "Nat.arms" = "Nat.arms" := by kept_name
@[simp] theorem impl_Nil : impl "Nil" = "Nil" := by kept_name
@[simp] theorem impl_Con : impl "Con" = "Con" := by kept_name
@[simp] theorem impl_List : impl "List" = "List" := by kept_name
@[simp] theorem impl_List_arms : impl "List.arms" = "List.arms" := by kept_name
@[simp] theorem impl_U32 : impl "U32" = "U32" := by kept_name
@[simp] theorem impl_U32_arms : impl "U32.arms" = "U32.arms" := by kept_name
@[simp] theorem impl_WNil : impl "WNil" = "WNil" := by kept_name
@[simp] theorem impl_WCon : impl "WCon" = "WCon" := by kept_name
@[simp] theorem impl_Word : impl "Word" = "Word" := by kept_name
@[simp] theorem impl_Word_Nil : impl "Word.Nil" = "Word.Nil" := by kept_name
@[simp] theorem impl_Word_Nil_arms : impl "Word.Nil.arms" = "Word.Nil.arms" := by kept_name
@[simp] theorem impl_Word_Con : impl "Word.Con" = "Word.Con" := by kept_name
@[simp] theorem impl_Word_Con_arms : impl "Word.Con.arms" = "Word.Con.arms" := by kept_name
@[simp] theorem impl_False : impl "False" = "False" := by kept_name
@[simp] theorem impl_True : impl "True" = "True" := by kept_name
@[simp] theorem impl_Bool : impl "Bool" = "Bool" := by kept_name
@[simp] theorem impl_Bool_arms : impl "Bool.arms" = "Bool.arms" := by kept_name
@[simp] theorem impl_None : impl "None" = "None" := by kept_name
@[simp] theorem impl_Some : impl "Some" = "Some" := by kept_name
@[simp] theorem impl_Maybe : impl "Maybe" = "Maybe" := by kept_name
@[simp] theorem impl_Maybe_arms : impl "Maybe.arms" = "Maybe.arms" := by kept_name
@[simp] theorem impl_Or : impl "Or" = "Or" := by kept_name
@[simp] theorem impl_Either : impl "Either" = "Either" := by kept_name
@[simp] theorem impl_Either_arms : impl "Either.arms" = "Either.arms" := by kept_name
@[simp] theorem impl_Inl : impl "Inl" = "Inl" := by kept_name
@[simp] theorem impl_Inr : impl "Inr" = "Inr" := by kept_name

theorem impl_ctor (hk : impl k = k) : Rename.term impl (ctor k fs) = ctor k (fs.map (Rename.term impl)) := by
  simp only [ctor, Rename.term, hk, impl_unit]
  congr 1; congr 1
  induction fs with
  | nil => simp [Rename.term]
  | cons f fs ih => simp [Rename.term, ih]

@[simp] theorem impl_bits : Rename.term impl (bits n v) = bits n v := by
  induction n generalizing v with
  | zero => simp [bits, impl_ctor]
  | succ n ih => by_cases h : v % 2 = 1 <;> simp [bits, impl_ctor, ih, h]

@[simp] theorem impl_cell : Rename.term impl (cell b) = cell b := by simp [cell, impl_ctor]

@[simp] theorem impl_bytes : Rename.term impl (bytes bs) = bytes bs := by
  induction bs with
  | nil => simp [bytes, list, impl_ctor]
  | cons b bs ih => simp only [bytes, List.map_cons, list] at *; simp [impl_ctor, ih]

@[simp] theorem impl_nat : Rename.term impl (Form.nat n) = Form.nat n := by
  induction n with
  | zero => simp [Form.nat, impl_ctor]
  | succ n ih => simp [Form.nat, impl_ctor, ih]

@[simp] theorem impl_u32 : Rename.term impl (Form.u32 m) = Form.u32 m := by simp [Form.u32, impl_ctor]

@[simp] theorem impl_some : Rename.term impl (Form.some x) = Form.some (Rename.term impl x) := by
  simp [Form.some, impl_ctor]

-- Typing
-- ------

-- Base's defs of the types of the values
def baseTypes : List Def :=
  [«evalCopy.Nat», «evalCopy.Nat.arms», «evalCopy.List», «evalCopy.List.arms», «evalCopy.U32»,
   «evalCopy.U32.arms», «evalCopy.Word», «evalCopy.Word.Nil», «evalCopy.Word.Nil.arms»,
   «evalCopy.Word.Con», «evalCopy.Word.Con.arms», «evalCopy.Bool», «evalCopy.Bool.arms»,
   «evalCopy.Maybe», «evalCopy.Maybe.arms»]

-- Base's List<&2, U32>
def listU32 : Term := App Q0 (App Q0 (Ref "List") (Lab "Q2")) (Ref "U32")

-- Base's Maybe<&2, List<&2, U32>>
def maybeList : Term := App Q0 (App Q0 (Ref "Maybe") (Lab "Q2")) listU32

section typing

variable {B : Book}

-- the defs of baseTypes, by name
private theorem bt (hT : Contains B baseTypes) (d : Def) (h : d ∈ baseTypes := by simp [baseTypes]) : Book.get B d.k = some d := hT d h

private theorem delta (hT : Contains B baseTypes) (cl : Book.Closed B) (d : Def) (h : d ∈ baseTypes := by simp [baseTypes]) : Par B (Ref d.k) d.v :=
  .delta (bt hT d h) (cl _ _ (bt hT d h))

-- a pair at quantity 1, at a type that converts to its Σ
private theorem tup1 (ha : Typed B [] a A) (hb : Typed B [] b (Term.inst Bt a))
    (c : Pars B T (Sig Q1 A Bt)) : Typed B [] (Tup Q1 a b) T :=
  .conv (.tup ha hb) (.conv ⟨_, .refl, c⟩)

-- a label, at a type that reduces to its enum
private theorem lab1 (h : k ∈ ks) (c : Pars B T (Enu ks)) : Typed B [] (Lab k) T :=
  .conv (.lab h) (.conv ⟨_, .refl, c⟩)

theorem typed_bool (hT : Contains B baseTypes) (cl : Book.Closed B) (c : Prop) [Decidable c] :
    Typed B [] (ctor (if c then "True" else "False") []) (Ref "Bool") := by
  refine tup1 (.lab (by by_cases hc : c <;> simp [hc])) ?_ (.step (delta hT cl «evalCopy.Bool») .refl)
  refine lab1 (ks := ["()"]) (by simp) ?_
  simp only [Term.inst, Term.sub, Subst.one]
  refine .step (.app (delta hT cl «evalCopy.Bool.arms») par_refl) ?_
  by_cases hc : c <;> simp only [hc, ite_true, ite_false]
  · exact .step (.miss (by decide) par_refl) (.step (.hit par_refl) .refl)
  · exact .step (.hit par_refl) .refl

theorem typed_nat (hT : Contains B baseTypes) (cl : Book.Closed B) : Typed B [] (Form.nat n) (Ref "Nat") := by
  induction n with
  | zero =>
    refine tup1 (.lab (by simp)) ?_ (.step (delta hT cl «evalCopy.Nat») .refl)
    refine lab1 (ks := ["()"]) (by simp) ?_
    simp only [Term.inst, Term.sub, Subst.one]
    exact .step (.app (delta hT cl «evalCopy.Nat.arms») par_refl) (.step (.hit par_refl) .refl)
  | succ n ih =>
    refine tup1 (.lab (by simp)) ?_ (.step (delta hT cl «evalCopy.Nat») .refl)
    simp only [Term.inst, Term.sub, Subst.one]
    refine tup1 (Bt := Enu ["()"]) ih (lab1 (ks := ["()"]) (by simp) ?_) ?_
    · simp only [Term.inst, Term.sub]; exact .refl
    · exact .step (.app (delta hT cl «evalCopy.Nat.arms») par_refl)
        (.step (.miss (by decide) par_refl) (.step (.hit par_refl) .refl))

theorem typed_bits (hT : Contains B baseTypes) (cl : Book.Closed B) :
    Typed B [] (bits n v) (App Q1 (Ref "Word") (Form.nat n)) := by
  induction n generalizing v with
  | zero =>
    refine tup1 (A := Enu ["WNil"]) (Bt := App Q1 (Ref "Word.Nil.arms") (Var 0)) (.lab (by simp)) ?_ ?_
    · refine lab1 (ks := ["()"]) (by simp) ?_
      simp only [Term.inst, Term.sub, Subst.one]
      exact .step (.app (delta hT cl «evalCopy.Word.Nil.arms») par_refl) (.step (.hit par_refl) .refl)
    · refine .step (.app (delta hT cl «evalCopy.Word») par_refl) ?_
      refine .step (.split par_refl par_refl par_refl) ?_
      refine .step (.app (.hit par_refl) par_refl) ?_
      refine .step (.hit par_refl) ?_
      exact .step (delta hT cl «evalCopy.Word.Nil») .refl
  | succ n ih =>
    refine tup1 (A := Enu ["WCon"]) (Bt := App Q1 (App Q0 (Ref "Word.Con.arms") (Form.nat n)) (Var 0))
      (.lab (by simp)) ?_ ?_
    · simp only [Term.inst, Term.sub, Subst.one, Subst.up, plain_nat.ren, plain_nat.sub]
      refine tup1 (Bt := Sig Q1 (App Q1 (Ref "Word") (Form.nat n)) (Enu ["()"])) (typed_bool hT cl _) ?_ ?_
      · try simp only [Term.inst, Term.sub, Subst.one, Subst.up, plain_nat.ren, plain_nat.sub]
        refine tup1 (Bt := Enu ["()"]) ih (lab1 (ks := ["()"]) (by simp) ?_) .refl
        simp only [Term.inst, Term.sub]; exact .refl
      · refine .step (.app (.app (delta hT cl «evalCopy.Word.Con.arms») par_refl) par_refl) ?_
        refine .step (.app (.beta par_refl par_refl) par_refl) ?_
        simp only [Term.inst, Term.sub, Subst.one, Subst.up, plain_nat.ren, plain_nat.sub]
        exact .step (.hit par_refl) .refl
    · refine .step (.app (delta hT cl «evalCopy.Word») par_refl) ?_
      refine .step (.split par_refl par_refl par_refl) ?_
      refine .step (.app (.miss (by decide) par_refl) par_refl) ?_
      refine .step (.app (.hit par_refl) par_refl) ?_
      refine .step (.split par_refl par_refl par_refl) ?_
      refine .step (.app (.beta par_refl par_refl) par_refl) ?_
      simp only [Term.inst, Term.sub, Subst.one, Subst.up, Quan.fld]
      refine .step (.hit par_refl) ?_
      refine .step (.app (delta hT cl «evalCopy.Word.Con») par_refl) ?_
      refine .step (.beta par_refl par_refl) ?_
      simp only [Term.inst, Term.sub, Subst.one, Subst.up, plain_nat.ren, plain_nat.sub]
      exact .refl

theorem typed_u32 (hT : Contains B baseTypes) (cl : Book.Closed B) :
    Typed B [] (ctor "U32" [bits 32 v]) (Ref "U32") := by
  refine tup1 (.lab (by simp)) ?_ (.step (delta hT cl «evalCopy.U32») .refl)
  simp only [Term.inst, Term.sub, Subst.one]
  refine tup1 (Bt := Enu ["()"]) (typed_bits hT cl) (lab1 (ks := ["()"]) (by simp) ?_) ?_
  · simp only [Term.inst, Term.sub]; exact .refl
  · exact .step (.app (delta hT cl «evalCopy.U32.arms») par_refl) (.step (.hit par_refl) .refl)

theorem typed_bytes (hT : Contains B baseTypes) (cl : Book.Closed B) :
    Typed B [] (bytes bs) listU32 := by
  have hl : Pars B listU32 (Sig Q1 (Enu ["Nil", "Con"])
      (App Q1 (App Q0 (App Q0 (Ref "List.arms") (Lab "Q2")) (Ref "U32")) (Var 0))) := by
    refine .step (.app (.app (delta hT cl «evalCopy.List») par_refl) par_refl) ?_
    refine .step (.app (.beta par_refl par_refl) par_refl) ?_
    simp only [Term.inst, Term.sub, Subst.one, Subst.up, Term.ren]
    refine .step (.beta par_refl par_refl) ?_
    simp only [Term.inst, Term.sub, Subst.one, Subst.up, Term.ren]
    exact .refl
  induction bs with
  | nil =>
    refine tup1 (.lab (by simp)) ?_ hl
    refine lab1 (ks := ["()"]) (by simp) ?_
    simp only [Term.inst, Term.sub, Subst.one]
    refine .step (.app (.app (.app (delta hT cl «evalCopy.List.arms») par_refl) par_refl) par_refl) ?_
    refine .step (.app (.app (.beta par_refl par_refl) par_refl) par_refl) ?_
    refine .step (.app (.beta par_refl par_refl) par_refl) ?_
    simp only [Term.inst, Term.sub, Subst.one, Subst.up, Term.ren]
    exact .step (.hit par_refl) .refl
  | cons b bs ih =>
    refine tup1 (.lab (by simp)) ?_ hl
    simp only [Term.inst, Term.sub, Subst.one]
    refine tup1 (Bt := Sig Q1 (App Q0 (App Q0 (Ref "List") (Lab "Q2")) (Ref "U32")) (Enu ["()"]))
      (typed_u32 hT cl) ?_ ?_
    · simp only [Term.inst, Term.sub, Subst.one, Subst.up, Term.ren]
      refine tup1 (Bt := Enu ["()"]) ih (lab1 (ks := ["()"]) (by simp) ?_) .refl
      simp only [Term.inst, Term.sub]; exact .refl
    · refine .step (.app (.app (.app (delta hT cl «evalCopy.List.arms») par_refl) par_refl) par_refl) ?_
      refine .step (.app (.app (.beta par_refl par_refl) par_refl) par_refl) ?_
      refine .step (.app (.beta par_refl par_refl) par_refl) ?_
      simp only [Term.inst, Term.sub, Subst.one, Subst.up, Term.ren]
      refine .step (.miss (by decide) par_refl) ?_
      exact .step (.hit par_refl) .refl

theorem typed_u32' (hT : Contains B baseTypes) (cl : Book.Closed B) :
    Typed B [] (Form.u32 m) (Ref "U32") := typed_u32 hT cl

theorem typed_listU32 (hT : Contains B baseTypes) : Typed B [] listU32 T2 := by
  have h1 := Typed.ref (Γ := []) (σ := Var) (bt hT «evalCopy.List»)
  have h2 := Typed.ref (Γ := []) (σ := Var) (bt hT «evalCopy.U32»)
  rw [sub_var] at h1 h2
  have := Typed.app (Typed.app h1 (.lab (k := "Q2") (by simp))) h2
  simpa [Term.inst, Term.sub, Subst.one, Subst.up, Term.ren, listU32, «evalCopy.List»,
    «evalCopy.U32»] using this

theorem typed_maybeList (hT : Contains B baseTypes) : Typed B [] maybeList T2 := by
  have h1 := Typed.ref (Γ := []) (σ := Var) (bt hT «evalCopy.Maybe»)
  rw [sub_var] at h1
  have := Typed.app (Typed.app h1 (.lab (k := "Q2") (by simp))) (typed_listU32 hT)
  simpa [Term.inst, Term.sub, Subst.one, Subst.up, Term.ren, maybeList, «evalCopy.Maybe»] using this

end typing

-- Canonical forms
-- ---------------

-- canonical forms for pairs (as Join.lean's): a closed value at a Σ type is a
-- pair of its fields
theorem canon_sig (wt : Book.WellTyped B) (v : Value B t) (h : Typed B [] t T)
    (c : Conv B T (Sig q X Y)) :
    ∃ a b, t = Tup q a b ∧ Typed B [] a X ∧ Typed B [] b (Term.inst Y a) := by
  have hf := value_form wt v h c (by simp [former])
  cases v <;> simp [tform, former, ↓tform_call] at hf
  obtain ⟨U, ⟨A', B', rfl, h1, h2⟩, f, -⟩ := gen h
  obtain ⟨rfl, hA, hB⟩ := conv_sig (fits_conv f c (by simp [former]))
  exact ⟨_, _, rfl, .conv h1 (.conv hA), .conv h2 (.conv (conv_sub hB))⟩

-- a closed value of type Nat is the form of a Nat
private theorem canon_nat_lt (wt : Book.WellTyped B) (hT : Contains B baseTypes) (cl : Book.Closed B) :
    ∀ s w, sizeOf w < s → Value B w → Typed B [] w (Ref "Nat") → ∃ n, w = Form.nat n := by
  intro s
  induction s with
  | zero => intro w hs; omega
  | succ s ih =>
  intro w hs v h
  obtain ⟨a, b, rfl, ha, hb⟩ := canon_sig wt v h
    ⟨_, .step (delta hT cl «evalCopy.Nat») .refl, .refl⟩
  have ⟨va, vb⟩ := value_tup v
  obtain ⟨k, hk, rfl⟩ := canon_enu wt (va rfl) ha crefl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  simp only [Term.inst, Term.sub, Subst.one] at hb
  rcases hk with rfl | rfl
  · obtain ⟨u, hu, rfl⟩ := canon_enu wt vb hb
      ⟨_, .step (.app (delta hT cl «evalCopy.Nat.arms») par_refl) (.step (.hit par_refl) .refl), .refl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    subst hu; exact ⟨0, rfl⟩
  · obtain ⟨c, u, rfl, hc, hu⟩ := canon_sig wt vb hb
      ⟨_, .step (.app (delta hT cl «evalCopy.Nat.arms») par_refl)
        (.step (.miss (by decide) par_refl) (.step (.hit par_refl) .refl)), .refl⟩
    have ⟨vc, vu⟩ := value_tup vb
    simp only [Term.inst, Term.sub] at hu
    obtain ⟨u', hu', rfl⟩ := canon_enu wt vu hu crefl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu'
    subst hu'
    obtain ⟨n, rfl⟩ := ih c (by simp at hs; omega) (vc rfl) hc
    exact ⟨n + 1, rfl⟩

theorem canon_nat (wt : Book.WellTyped B) (hT : Contains B baseTypes) (cl : Book.Closed B)
    (v : Value B w) (h : Typed B [] w (Ref "Nat")) : ∃ n, w = Form.nat n :=
  canon_nat_lt wt hT cl _ w (Nat.lt_succ_self _) v h
