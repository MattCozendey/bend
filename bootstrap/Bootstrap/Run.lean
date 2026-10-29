import Bootstrap.MachineOk

-- Run
-- ===
--
-- The interpreter as a Spec.Compiler: its code is the book and the def to
-- run. The environment machine runs it until it stops (mrun); run then
-- steps the term where it stopped until no step fits. Each step of run is
-- one walk (scanWith), and a call of base's word code jumps to its result
-- (wordJump). This file proves claims 1 (correct) and 2 (total) for it.

open Quan Term Spec

namespace Interp

-- run bk jump n t: step from t with scanWith and jump, at most n times.
-- When no step fits, the result is what the term shows. When the fuel ends
-- first, there is no result.
def run (bk : Book) (jump : Term → Option Term) : Nat → Term → Option Obs
  | 0, _ => none
  | n + 1, t =>
    match (scanWith bk jump t).1 with
    | some u => run bk jump n u
    | none => observe t

-- runM bk jump n t: the machine from t, at most n steps, then run from the
-- term where it stops, with the fuel left
def runM (bk : Book) (jump : Term → Option Term) (n : Nat) (t : Term) : Option Obs :=
  let (s, m) := mrun bk jump n (.eval t [] [])
  run bk jump m (decode s)

-- the interpreter. It compares the book's word code with WordRef once per
-- run.
def compiler : Compiler where
  Code := Book × String
  compile bk k := if Spec.Pure bk k = true then .ok (bk, k) else .error "the def is not Pure"
  run n code := runM code.1 (wordJump (wordOk code.1)) n (Ref code.2)

-- Runs
-- ====

-- a result of run is what a reachable term shows, where no step fits
theorem run_spec (hj : ∀ t u, jump t = some u → Plus bk t u) : run bk jump n t = some r →
    ∃ v, Evals bk t v ∧ step bk v = none ∧ observe v = some r := by
  induction n generalizing t with
  | zero => simp [run]
  | succ n ih =>
    simp only [run]
    split
    · rename_i u hu
      intro h; obtain ⟨v, ev, sv, ov⟩ := ih h
      exact ⟨v, evals_trans (plus_evals (scanWith_sound hj hu)) ev, sv, ov⟩
    · rename_i hn; exact fun h => ⟨t, .refl, scanWith_none hn, h⟩

-- where Eval ends, so does Plus
theorem acc_plus (h : Acc (fun u t => Eval bk t u) t) : Acc (fun u t => Plus bk t u) t := by
  induction h with
  | intro t _ ih =>
    refine ⟨_, fun u hp => ?_⟩
    obtain ⟨m, e, es⟩ := hp
    cases es with
    | refl => exact ih _ e
    | step e' es' => exact (ih _ e).inv ⟨_, e', es'⟩

-- from a term where Eval ends, run ends: some fuel reaches a term where
-- no step fits
theorem run_ends (hj : ∀ t u, jump t = some u → Plus bk t u)
    (acc : Acc (fun u t => Plus bk t u) t) :
    ∃ n v, Evals bk t v ∧ step bk v = none ∧ run bk jump n t = observe v := by
  induction acc with
  | intro t _ ih =>
    cases hs : (scanWith bk jump t).1 with
    | none => exact ⟨1, t, .refl, scanWith_none hs, by simp [run, hs]⟩
    | some u =>
      have p := scanWith_sound hj hs
      obtain ⟨n, v, ev, sv, rv⟩ := ih u p
      exact ⟨n + 1, v, evals_trans (plus_evals p) ev, sv, by simp [run, hs, rv]⟩

theorem decode_init : decode (.eval t [] []) = t := rb_nil t

theorem inv_init : Inv bk (.eval t [] []) := ⟨trivial, trivial⟩

-- a result of runM is what a reachable term shows, where no step fits
theorem runM_spec (hj : ∀ t u, jump t = some u → Plus bk t u) : runM bk jump n t = some r →
    ∃ v, Evals bk t v ∧ step bk v = none ∧ observe v = some r := by
  unfold runM
  generalize hm : mrun bk jump n (.eval t [] []) = sm
  obtain ⟨s, m⟩ := sm
  intro h
  have ev := mrun_sound hj inv_init hm
  rw [decode_init] at ev
  obtain ⟨v, ev', sv, ov⟩ := run_spec hj h
  exact ⟨v, evals_trans ev ev', sv, ov⟩

theorem acc_evals (acc : Acc (fun u t => Plus bk t u) t) (h : Evals bk t u) :
    Acc (fun u t => Plus bk t u) u := by
  cases h with
  | refl => exact acc
  | step e es => exact acc.inv ⟨_, e, es⟩

-- from a term where Eval ends, runM ends: some fuel reaches a term where
-- no step fits
theorem runM_ends (hj : ∀ t u, jump t = some u → Plus bk t u)
    (acc : Acc (fun u t => Plus bk t u) t) :
    ∃ n v, Evals bk t v ∧ step bk v = none ∧ runM bk jump n t = observe v := by
  obtain ⟨k, sf, _, ev, hrun⟩ :=
    mrun_ends hj t acc _ (.eval t [] []) (Nat.le_refl _) decode_init inv_init
  obtain ⟨m, v, ev', sv, rv⟩ := run_ends hj (acc_evals acc ev)
  refine ⟨k + m, v, evals_trans ev ev', sv, ?_⟩
  simp only [runM, hrun m]; exact rv

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

-- a term that Eval reaches from a typed def, where no step fits, is a
-- value
theorem final_value (wt : Book.WellTyped bk) (lv : Book.Live bk) (R : Typed bk [] (Ref k) T)
    (ev : Evals bk (Ref k) v) (sv : step bk v = none) : Value bk v := by
  rcases progress bk v T wt lv (pars_sr wt R (evals_pars lv.1 ev)) with vv | ⟨u, e⟩
  · exact vv
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
    have hj : ∀ t u, wordJump (wordOk bk) t = some u → Plus bk t u := fun _ _ => wordJump_sound
    have acc := acc_plus (halts bk (Ref k) lv (fun _ => rfl) (live_ref hd))
    obtain ⟨n, v, ev, sv, rv⟩ := runM_ends hj acc
    have vv := final_value wt lv R ev sv
    obtain ⟨o, ho⟩ := observe_data (canon_data wt vv (pars_sr wt R (evals_pars lv.1 ev)) K)
    refine ⟨hp, o, ⟨⟨v, ev, vv, ho⟩, fun v' ev' vv' => ?_⟩, ⟨n, rv.trans ho⟩, fun n' r h => ?_⟩
    · exact (same_show wt lv R K ev vv ev' vv').trans ho
    · obtain ⟨v', ev', sv', ov'⟩ := runM_spec hj h
      have := (same_show wt lv R K ev vv ev' (final_value wt lv R ev' sv')).trans ho
      rw [ov'] at this; exact Option.some.inj this
  · simp at hcomp

theorem total : Claim.total compiler := by
  intro bk k _ hp
  exact ⟨(bk, k), by simp [compiler, hp]⟩

end Interp
