import Bootstrap.Step

-- Run
-- ===
--
-- The interpreter as a Spec.Compiler: its code is the book and the def to
-- run, and run steps until no step fits. This file proves claims 1
-- (correct) and 2 (total) for it.

open Quan Term Spec

namespace Interp

-- run bk n t: step from t, at most n times. When no step fits, the result
-- is what the term shows. When the fuel ends first, there is no result.
-- It takes each step with next, which is step from one walk (next_eq).
def run (bk : Book) : Nat → Term → Option Obs
  | 0, _ => none
  | n + 1, t =>
    match next bk t with
    | some u => run bk n u
    | none => observe t

-- the interpreter
def compiler : Compiler where
  Code := Book × String
  compile bk k := if Spec.Pure bk k = true then .ok (bk, k) else .error "the def is not Pure"
  run n code := run code.1 n (Ref code.2)

-- Runs
-- ====

-- a result of run is what a reachable term shows, where no step fits
theorem run_spec : run bk n t = some r →
    ∃ v, Evals bk t v ∧ step bk v = none ∧ observe v = some r := by
  induction n generalizing t with
  | zero => simp [run]
  | succ n ih =>
    simp only [run, next_eq]
    split
    · rename_i u hu
      intro h; obtain ⟨v, ev, sv, ov⟩ := ih h
      exact ⟨v, .step (step_sound hu) ev, sv, ov⟩
    · rename_i hn; exact fun h => ⟨t, .refl, hn, h⟩

-- from a term where Eval ends, run ends: some fuel reaches a term where
-- no step fits
theorem run_ends (acc : Acc (fun u t => Eval bk t u) t) :
    ∃ n v, Evals bk t v ∧ step bk v = none ∧ run bk n t = observe v := by
  induction acc with
  | intro t _ ih =>
    cases hs : step bk t with
    | none => exact ⟨1, t, .refl, hs, by simp [run, next_eq, hs]⟩
    | some u =>
      obtain ⟨n, v, ev, sv, rv⟩ := ih u (step_sound hs)
      exact ⟨n + 1, v, .step (step_sound hs) ev, sv, by simp [run, next_eq, hs, rv]⟩

theorem evals_pars (hcl : Book.Closed bk) (h : Evals bk t u) : Pars bk t u := by
  induction h with
  | refl => exact .refl
  | step e _ ih => exact pars_trans (eval_pars hcl e) ih

-- Data
-- ====

theorem observe_data (h : Data t) : ∃ o, observe t = some o := by
  induction h with
  | lab => exact ⟨_, rfl⟩
  | rfl => exact ⟨_, rfl⟩
  | tup _ _ iha ihb =>
    rename_i q a b
    obtain ⟨ob, hob⟩ := ihb
    cases hq : q.live
    · exact ⟨.tup0 ob, by simp [observe, hq, hob]⟩
    · obtain ⟨oa, hoa⟩ := iha hq
      exact ⟨.tup oa ob, by simp [observe, hq, hoa, hob]⟩

-- a reduct of plain data is plain data, and shows the same
theorem data_par (h : Data t) (p : Par bk t c) : Data c ∧ observe c = observe t := by
  induction h generalizing c with
  | lab => cases p; exact ⟨.lab, rfl⟩
  | rfl => cases p; exact ⟨.rfl, rfl⟩
  | tup _ _ iha ihb =>
    rename_i q a b
    cases p with
    | tup pa pb =>
      obtain ⟨db, eb⟩ := ihb pb
      refine ⟨.tup (fun l => (iha l pa).1) db, ?_⟩
      cases hq : q.live
      · simp [observe, hq, eb]
      · simp [observe, hq, eb, (iha hq pa).2]

theorem data_pars (h : Data t) (p : Pars bk t c) : observe c = observe t := by
  induction p with
  | refl => rfl
  | step s _ ih => have ⟨d, e⟩ := data_par h s; exact (ih d).trans e

-- Facts of a Pure def
-- ===================

theorem sees_self (hcl : Book.Closed bk) : Sees bk bk :=
  fun k d h => ⟨d.o, by cases d; exact h, hcl k d h⟩

-- a Pure def of a checked book: its type is Data, and Ref k has it
theorem pure_facts (hcl : Book.Closed bk) (hp : Spec.Pure bk k = true) :
    ∃ d, bk.get k = some d ∧ Typed bk [] (Ref k) d.T ∧ Typed bk [] d.T T2 := by
  unfold Spec.Pure at hp
  split at hp
  · simp at hp
  · rename_i d hd
    simp only [Bool.and_eq_true] at hp
    have hc : Term.check bk FUEL [] d.T T2 = .ok () := by
      revert hp; cases Term.check bk FUEL [] d.T T2 <;> simp
    have K := (chk (sees_self hcl) FUEL [] d.T T2 nofun).2 hc
    simp only [Chk, Ctx.decl, Ctx.drop, sub_var] at K
    have R := Typed.ref (Γ := []) (σ := Var) hd
    rw [sub_var] at R
    exact ⟨d, hd, R, K⟩

theorem live_ref (hd : bk.get k = some d) : Term.Live bk (Ref k) := by
  obtain ⟨i, hi⟩ := index_of_get hd
  simp [Term.Live, Term.live, Term.called, unspine, hi, index_lt hi]

-- a term that Eval reaches from a Pure def, where no step fits, is plain
-- data
theorem final_data (wt : Book.WellTyped bk) (lv : Book.Live bk)
    (R : Typed bk [] (Ref k) T) (K : Typed bk [] T T2)
    (ev : Evals bk (Ref k) v) (sv : step bk v = none) : Data v := by
  have tv := pars_sr wt R (evals_pars lv.1 ev)
  rcases progress bk v T wt lv tv with vv | ⟨u, e⟩
  · exact canon_data wt vv tv K
  · exact absurd sv (step_complete e)

-- two values that Eval reaches from a Pure def show the same
theorem same_show (wt : Book.WellTyped bk) (lv : Book.Live bk)
    (R : Typed bk [] (Ref k) T) (K : Typed bk [] T T2)
    (ev : Evals bk (Ref k) v) (vv : Value bk v) (ev' : Evals bk (Ref k) v') (vv' : Value bk v') :
    observe v' = observe v := by
  have dv := canon_data wt vv (pars_sr wt R (evals_pars lv.1 ev)) K
  have dv' := canon_data wt vv' (pars_sr wt R (evals_pars lv.1 ev')) K
  obtain ⟨c, p, p'⟩ := confluent bk _ _ _ (evals_pars lv.1 ev) (evals_pars lv.1 ev')
  exact (data_pars dv' p').symm.trans (data_pars dv p)

-- Claims 1 and 2
-- ==============

theorem correct : Claim.correct compiler := by
  intro bk k code hc hcomp
  simp only [compiler] at hcomp
  split at hcomp
  · rename_i hp
    cases hcomp
    obtain ⟨wt, lv⟩ := book_check bk hc
    obtain ⟨d, hd, R, K⟩ := pure_facts lv.1 hp
    have acc := halts bk (Ref k) lv (fun _ => rfl) (live_ref hd)
    obtain ⟨n, v, ev, sv, rv⟩ := run_ends acc
    have dv := final_data wt lv R K ev sv
    have vv : Value bk v := by
      rcases progress bk v d.T wt lv (pars_sr wt R (evals_pars lv.1 ev)) with vv | ⟨u, e⟩
      · exact vv
      · exact absurd sv (step_complete e)
    obtain ⟨o, ho⟩ := observe_data dv
    refine ⟨hp, o, ⟨⟨v, ev, vv, ho⟩, fun v' ev' vv' => ?_⟩, ⟨n, rv.trans ho⟩, fun n' r h => ?_⟩
    · exact (same_show wt lv R K ev vv ev' vv').trans ho
    · obtain ⟨v', ev', sv', ov'⟩ := run_spec h
      have vv' : Value bk v' := by
        rcases progress bk v' d.T wt lv (pars_sr wt R (evals_pars lv.1 ev')) with vv' | ⟨u, e⟩
        · exact vv'
        · exact absurd sv' (step_complete e)
      have := (same_show wt lv R K ev vv ev' vv').trans ho
      rw [ov'] at this; exact Option.some.inj this
  · simp at hcomp

theorem total : Claim.total compiler := by
  intro bk k _ hp
  exact ⟨(bk, k), by simp [compiler, hp]⟩

end Interp
