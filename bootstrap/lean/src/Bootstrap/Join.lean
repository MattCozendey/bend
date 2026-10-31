import Bootstrap.Code
import Bootstrap.Copy.Exists

-- Join
-- ====
--
-- Step 3 of the plan: what the Bend laws that --verdict accepts say about
-- runs. --verdict is Book.check on the kernel's parse of the `bend -o` text.
-- The kernel's adequate (bend2/bendtt.lean) turns a checked proof of a == b
-- into a conversion of a and b, and conv_runs turns that into a run.
-- runs_rfl goes the other way, so a real run can feed a law's "if" part,
-- and exists_conv reads the witness out of a "there is" proof (Base's Exists).

open Quan Term

-- Data with no dead part: labels, Rfl, and pairs of it at a live quantity
inductive Plain : Term → Prop
  | lab : Plain (Lab k)
  | rfl : Plain Rfl
  | tup : q.live = true → Plain a → Plain b → Plain (Tup q a b)

-- a pair reduces only to a pair at its quantity, field by field
private theorem pars_tup : Pars B (Tup q x y) c →
    ∃ x' y', c = Tup q x' y' ∧ Pars B x x' ∧ Pars B y y' := by
  intro h
  generalize e : Tup q x y = t at h
  induction h generalizing x y with
  | refl => subst e; exact ⟨_, _, rfl, .refl, .refl⟩
  | step s _ ih =>
    subst e; cases s with
    | tup s1 s2 =>
      obtain ⟨x', y', rfl, p1, p2⟩ := ih rfl
      exact ⟨x', y', rfl, .step s1 p1, .step s2 p2⟩

-- a plain term reduces only to itself
private theorem plain_fix (hb : Plain b) : Pars B b c → c = b := by
  induction hb generalizing c with
  | lab => exact lab_fix
  | rfl => exact pars_fix fun _ s => by cases s; rfl
  | tup _ _ _ iha ihb =>
    intro h
    obtain ⟨x', y', rfl, p1, p2⟩ := pars_tup h
    rw [iha p1, ihb p2]

-- a Data term that reduces to a plain term is that term
private theorem data_pars (hb : Plain b) : Data v → Pars B v b → v = b := by
  induction hb generalizing v with
  | lab =>
    intro hv h; cases hv with
    | lab => exact (lab_fix h).symm
    | rfl => cases (pars_fix (fun _ s => by cases s; rfl) h)
    | tup => obtain ⟨_, _, e, _⟩ := pars_tup h; cases e
  | rfl =>
    intro hv h; cases hv with
    | lab => cases lab_fix h
    | rfl => rfl
    | tup => obtain ⟨_, _, e, _⟩ := pars_tup h; cases e
  | tup hq _ _ iha ihb =>
    intro hv h; cases hv with
    | lab => cases lab_fix h
    | rfl => cases (pars_fix (fun _ s => by cases s; rfl) h)
    | tup da db =>
      obtain ⟨_, _, e, p1, p2⟩ := pars_tup h
      cases e
      rw [iha (da hq) p1, ihb db p2]

-- a closed typed term whose evaluation is accessible runs to a value it reduces to
private theorem runs_acc (wt : Book.WellTyped B) (lv : Book.Live B) :
    Acc (fun u t => Eval B t u) t → Typed B [] t A → ∃ v, Runs B t v ∧ Pars B t v := by
  intro hacc
  induction hacc with
  | intro t _ ih =>
    intro ht
    rcases progress B t A wt lv ht with hv | ⟨u, e⟩
    · exact ⟨t, Runs.refl hv, .refl⟩
    · have pu := eval_pars lv.1 e
      obtain ⟨v, r, p⟩ := ih u e (pars_sr wt ht pu)
      exact ⟨v, Runs.step e r, pars_trans pu p⟩

-- in a book that --verdict accepts, a closed, live term a of a Data type,
-- that converts to the plain b, runs to b
theorem conv_runs : Book.check B = .ok () → Term.Closed a → Term.Live B a →
    Typed B [] a A → Typed B [] A T2 → Plain b → Conv B a b → Runs B a b := by
  intro hc hcl hl ht hT hb hv
  obtain ⟨wt, lv⟩ := book_check B hc
  obtain ⟨v, r, pv⟩ := runs_acc wt lv (halts B a lv hcl hl) ht
  obtain ⟨c, pa, pb⟩ := hv
  cases plain_fix hb pb
  obtain ⟨d, p1, p2⟩ := confluent B a v _ pv pa
  cases plain_fix hb p2
  obtain ⟨n, s, vv⟩ := r
  have dv := canon_data wt vv (pars_sr wt ht pv) hT
  rw [← data_pars hb dv p1]
  exact ⟨n, s, vv⟩

-- a run's steps are reductions
private theorem steps_pars (cl : Book.Closed B) : Steps B n a b → Pars B a b := by
  intro s
  induction s with
  | refl => exact .refl
  | step e _ ih => exact pars_trans (eval_pars cl e) ih

-- in a book that --verdict accepts, a run of a to b proves a == b
theorem runs_rfl : Book.check B = .ok () → Runs B a b → Typed B Γ Rfl (Eql a b T) := by
  rintro hc ⟨_, s, _⟩
  exact .rfl ⟨b, steps_pars (book_check B hc).2.1 s, .refl⟩

-- substituting into a shifted term undoes the shift
private theorem one_ren : sub (Subst.one v) (ren Nat.succ t) = t := by
  rw [sub_ren]; exact sub_var t

-- canonical forms for pairs: a closed value at a Σ type is a pair of its fields
private theorem canon_sig (wt : Book.WellTyped B) (v : Value B t) (h : Typed B [] t T)
    (c : Conv B T (Sig q X Y)) :
    ∃ a b, t = Tup q a b ∧ Typed B [] a X ∧ Typed B [] b (Term.inst Y a) := by
  have hf := value_form wt v h c (by simp [former])
  cases v <;> simp [tform, former, ↓tform_call] at hf
  obtain ⟨U, ⟨A', B', rfl, h1, h2⟩, f, -⟩ := gen h
  obtain ⟨rfl, hA, hB⟩ := conv_sig (fits_conv f c (by simp [former]))
  exact ⟨_, _, rfl, .conv h1 (.conv hA), .conv h2 (.conv (conv_sub hB))⟩

-- Base's Exists A P unfolds to a Σ over the one label "Tuple"
private theorem exists_pars (cl : Book.Closed B)
    (hE : Book.get B "Exists" = some «existsCopy.Exists»)
    (hS : Book.get B "Sigma" = some «existsCopy.Sigma») :
    Pars B (App Q0 (App Q0 (Ref "Exists") A) P)
      (Sig Q1 (Enu ["Tuple"])
        (App Q1
          (App Q0
            (App Q0 (App Q0 (App Q0 (Ref "Sigma.arms") (ren Nat.succ (Lab "Q1"))) (ren Nat.succ (Lab "Q1")))
              (ren Nat.succ A))
            (ren Nat.succ (Lam Q0 (App Q0 (ren Nat.succ P) (Var 0)))))
          (Var 0))) := by
  refine .step (.app (.app (.delta hE (cl _ _ hE)) par_refl) par_refl) ?_
  dsimp only [«existsCopy.Exists»]
  refine .step (.app (.beta par_refl par_refl) par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up]
  refine .step (.beta par_refl par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, sub_succ, one_ren]
  refine .step (.app (.app (.app (.app (.delta hS (cl _ _ hS)) par_refl) par_refl) par_refl) par_refl) ?_
  dsimp only [«existsCopy.Sigma»]
  refine .step (.app (.app (.app (.beta par_refl par_refl) par_refl) par_refl) par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up]
  refine .step (.app (.app (.beta par_refl par_refl) par_refl) par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, sub_succ, one_ren]
  refine .step (.app (.beta par_refl par_refl) par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, sub_succ, one_ren]
  refine .step (.beta par_refl par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, sub_succ, one_ren]
  exact .refl

-- Sigma.arms at "Tuple" unfolds to the Σ of the two fields
private theorem arms_pars (cl : Book.Closed B)
    (hA : Book.get B "Sigma.arms" = some «existsCopy.Sigma.arms») :
    Pars B (App Q1 (App Q0 (App Q0 (App Q0 (App Q0 (Ref "Sigma.arms") q0) q1) A) P) (Lab "Tuple"))
      (Sig Q1 A (Sig Q1 (App Q0 (ren Nat.succ P) (Var 0)) (Enu ["()"]))) := by
  refine .step (.app (.app (.app (.app (.app (.delta hA (cl _ _ hA)) par_refl) par_refl) par_refl) par_refl) par_refl) ?_
  dsimp only [«existsCopy.Sigma.arms»]
  refine .step (.app (.app (.app (.app (.beta par_refl par_refl) par_refl) par_refl) par_refl) par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.up]
  refine .step (.app (.app (.app (.beta par_refl par_refl) par_refl) par_refl) par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.up, sub_succ]
  refine .step (.app (.app (.beta par_refl par_refl) par_refl) par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, sub_succ]
  refine .step (.app (.beta par_refl par_refl) par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, sub_succ, one_ren]
  refine .step (.hit par_refl) ?_
  exact .refl

-- in a book that --verdict accepts and that holds Base's Exists, a closed, live
-- proof e that there is a y : A with x == z, for a Data type A, has a witness w:
-- a Data value of type A at which x and z convert
theorem exists_conv : Book.check B = .ok () → Contains B existsCopy →
    Term.Closed e → Term.Live B e →
    Typed B [] e (App Q0 (App Q0 (Ref "Exists") A) (Lam Q0 (Eql x z T))) →
    Typed B [] A T2 →
    ∃ w, Data w ∧ Typed B [] w A ∧ Conv B (Term.inst x w) (Term.inst z w) := by
  intro hc hk hcl hl ht hA
  obtain ⟨wt, lv⟩ := book_check B hc
  have hE := hk «existsCopy.Exists» (by simp [existsCopy])
  have hS := hk «existsCopy.Sigma» (by simp [existsCopy])
  have hR := hk «existsCopy.Sigma.arms» (by simp [existsCopy])
  obtain ⟨v, ⟨_, _, vv⟩, pv⟩ := runs_acc wt lv (halts B e lv hcl hl) ht
  have hv := pars_sr wt ht pv
  -- the pair of the label and the rest
  obtain ⟨a, b, rfl, ha, hb⟩ := canon_sig wt vv hv ⟨_, exists_pars lv.1 hE hS, .refl⟩
  have ⟨va, vb⟩ := value_tup vv
  obtain ⟨k, hk', rfl⟩ := canon_enu wt (va rfl) ha crefl
  simp only [List.mem_singleton] at hk'; subst hk'
  simp only [Term.inst, Term.sub, Subst.one, one_ren] at hb
  -- the pair of the witness and the rest
  obtain ⟨w, b', rfl, hw, hb'⟩ := canon_sig wt vb hb ⟨_, arms_pars lv.1 hR, .refl⟩
  have ⟨vw, vb'⟩ := value_tup vb
  simp only [Term.inst, Term.sub, Subst.one, one_ren] at hb'
  -- the pair of the proof and the unit
  obtain ⟨p, u, rfl, hp, -⟩ := canon_sig wt vb' hb' crefl
  have hxz : Pars B (App Q0 (Lam Q0 (App Q0 (ren Nat.succ (Lam Q0 (Eql x z T))) (Var 0))) w)
      (Eql (Term.inst x w) (Term.inst z w) (Term.inst T w)) := by
    refine .step (.beta par_refl par_refl) ?_
    simp only [Term.inst, Term.sub, Subst.one, one_ren]
    refine .step (.beta par_refl par_refl) ?_
    exact .refl
  obtain ⟨-, c⟩ := canon_eql wt ((value_tup vb').1 rfl) hp ⟨_, hxz, .refl⟩
  exact ⟨w, canon_data wt (vw rfl) hw hA, hw, c⟩
