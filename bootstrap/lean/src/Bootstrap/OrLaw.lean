import Bootstrap.Laws

-- OrLaw
-- =====
--
-- exists_conv (Join.lean) for a "there is" part whose property is an Or of
-- two equations, as no_other_failure states it: the witness, and the
-- equation of the two that its proof proves.

open Quan Term

set_option linter.unusedSimpArgs false

-- Base's Or and Either, under their names in trusted.bend's book
def orCopy : List Def := [«trustedCopy.Or», «trustedCopy.Either», «trustedCopy.Either.arms»]

private theorem one_ren : sub (Subst.one v) (ren Nat.succ t) = t := by
  rw [sub_ren]; exact sub_var t

-- Base's Exists A P unfolds to a Σ over the one label "Tuple" (as Join.lean's)
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

-- Sigma.arms at "Tuple" unfolds to the Σ of the two fields (as Join.lean's)
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

-- Base's Or X Y unfolds to a Σ over Inl and Inr
private theorem or_pars (cl : Book.Closed B) (ho : Contains B orCopy) :
    Pars B (App Q0 (App Q0 (Ref "Or") X) Y)
      (Sig Q1 (Enu ["Inl", "Inr"]) (App Q1 (App Q0 (App Q0 (App Q0 (App Q0 (Ref "Either.arms")
        (Lab "Q1")) (Lab "Q1")) (ren Nat.succ X)) (ren Nat.succ Y)) (Var 0))) := by
  have hO := ho «trustedCopy.Or» (by simp [orCopy])
  have hE := ho «trustedCopy.Either» (by simp [orCopy])
  refine .step (.app (.app (.delta hO (cl _ _ hO)) par_refl) par_refl) ?_
  dsimp only [«trustedCopy.Or»]
  refine .step (.app (.beta par_refl par_refl) par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up]
  refine .step (.beta par_refl par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, sub_succ, one_ren]
  refine .step (.app (.app (.app (.app (.delta hE (cl _ _ hE)) par_refl) par_refl) par_refl) par_refl) ?_
  dsimp only [«trustedCopy.Either»]
  refine .step (.app (.app (.app (.beta par_refl par_refl) par_refl) par_refl) par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up]
  refine .step (.app (.app (.beta par_refl par_refl) par_refl) par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, sub_succ, one_ren]
  refine .step (.app (.beta par_refl par_refl) par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, sub_succ, one_ren]
  refine .step (.beta par_refl par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, sub_succ, one_ren, Term.ren]
  exact .refl

-- Either.arms at Inl, and at Inr, unfolds to the Σ of its field
private theorem either_pars (cl : Book.Closed B) (ho : Contains B orCopy) :
    Pars B (App Q1 (App Q0 (App Q0 (App Q0 (App Q0 (Ref "Either.arms") q0) q1) X) Y) (Lab "Inl"))
      (Sig Q1 X (Enu ["()"])) ∧
    Pars B (App Q1 (App Q0 (App Q0 (App Q0 (App Q0 (Ref "Either.arms") q0) q1) X) Y) (Lab "Inr"))
      (Sig Q1 Y (Enu ["()"])) := by
  have hA := ho «trustedCopy.Either.arms» (by simp [orCopy])
  constructor <;>
  · refine .step (.app (.app (.app (.app (.app (.delta hA (cl _ _ hA)) par_refl) par_refl) par_refl) par_refl) par_refl) ?_
    dsimp only [«trustedCopy.Either.arms»]
    refine .step (.app (.app (.app (.app (.beta par_refl par_refl) par_refl) par_refl) par_refl) par_refl) ?_
    simp only [Term.inst, Term.sub, Subst.up]
    refine .step (.app (.app (.app (.beta par_refl par_refl) par_refl) par_refl) par_refl) ?_
    simp only [Term.inst, Term.sub, Subst.up, sub_succ]
    refine .step (.app (.app (.beta par_refl par_refl) par_refl) par_refl) ?_
    simp only [Term.inst, Term.sub, Subst.one, Subst.up, sub_succ]
    refine .step (.app (.beta par_refl par_refl) par_refl) ?_
    simp only [Term.inst, Term.sub, Subst.one, Subst.up, sub_succ, one_ren]
    first
      | exact .step (.hit par_refl) .refl
      | exact .step (.miss (by decide) par_refl) (.step (.hit par_refl) .refl)

-- in a book that --verdict accepts and that holds Base's Exists and Or, a
-- closed, live proof e that there is a y : A with x == z or x' == z', for a
-- Data type A, has a witness w: a Data value of type A at which x and z, or
-- x' and z', convert
theorem exists_or (hc : Book.check B = .ok ()) (hk : Contains B existsCopy) (ho : Contains B orCopy)
    (hcl : Term.Closed e) (hl : Term.Live B e)
    (ht : Typed B [] e (App Q0 (App Q0 (Ref "Exists") A)
      (Lam Q0 (App Q0 (App Q0 (Ref "Or") (Eql x z T)) (Eql x' z' T')))))
    (hA : Typed B [] A T2) :
    ∃ w, Data w ∧ Typed B [] w A ∧
      (Conv B (Term.inst x w) (Term.inst z w) ∨ Conv B (Term.inst x' w) (Term.inst z' w)) := by
  obtain ⟨wt, lv⟩ := book_check B hc
  have hE := hk «existsCopy.Exists» (by simp [existsCopy])
  have hS := hk «existsCopy.Sigma» (by simp [existsCopy])
  have hR := hk «existsCopy.Sigma.arms» (by simp [existsCopy])
  obtain ⟨v, ⟨_, _, vv⟩, pv⟩ := runs_acc' wt lv (halts B e lv hcl hl) ht
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
  have vp := (value_tup vb').1 rfl
  -- the proof is an Or: a label and the proof of one side
  have hor : Pars B (App Q0 (Lam Q0 (App Q0 (ren Nat.succ (Lam Q0 (App Q0 (App Q0 (Ref "Or") (Eql x z T))
      (Eql x' z' T')))) (Var 0))) w)
      (Sig Q1 (Enu ["Inl", "Inr"]) (App Q1 (App Q0 (App Q0 (App Q0 (App Q0 (Ref "Either.arms")
        (Lab "Q1")) (Lab "Q1")) (ren Nat.succ (Eql (Term.inst x w) (Term.inst z w) (Term.inst T w))))
        (ren Nat.succ (Eql (Term.inst x' w) (Term.inst z' w) (Term.inst T' w)))) (Var 0))) := by
    refine .step (.beta par_refl par_refl) ?_
    simp only [Term.inst, Term.sub, Subst.one, one_ren]
    refine .step (.beta par_refl par_refl) ?_
    exact or_pars lv.1 ho
  obtain ⟨l, r, rfl, hl', hr⟩ := canon_sig wt vp hp ⟨_, hor, .refl⟩
  have ⟨vl, vr⟩ := value_tup vp
  obtain ⟨j, hj, rfl⟩ := canon_enu wt (vl rfl) hl' crefl
  simp only [Term.inst, Term.sub, Subst.one, one_ren] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  have dw := canon_data wt (vw rfl) hw hA
  rcases hj with rfl | rfl
  · obtain ⟨q, -, rfl, hq, -⟩ := canon_sig wt vr hr ⟨_, (either_pars lv.1 ho).1, .refl⟩
    obtain ⟨-, c⟩ := canon_eql wt ((value_tup vr).1 rfl) hq crefl
    exact ⟨w, dw, hw, .inl c⟩
  · obtain ⟨q, -, rfl, hq, -⟩ := canon_sig wt vr hr ⟨_, (either_pars lv.1 ho).2, .refl⟩
    obtain ⟨-, c⟩ := canon_eql wt ((value_tup vr).1 rfl) hq crefl
    exact ⟨w, dw, hw, .inr c⟩
