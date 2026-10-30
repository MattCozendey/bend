import Cli

-- Laws
-- ====
--
-- The proofs of claim 5 (laws) and claim 7 (input).
-- - Claim 5: a law about def k, or about its body, holds about each value
--   that Eval reaches from k. It joins the kernel's adequate with Eval's
--   reduction, and with one δ step for the body.
-- - Claim 7: an instance of a law at the CLI's input is a closed, live,
--   typed proof in the CLI's book, so the kernel's adequate applies to it.
--   Its equality names main(bs), or the call f(bs) that main makes. RUN
--   reaches W(t), the hole around that call, by δ steps, and by one β step
--   for f(bs); RUN reaches v too, so W(t) and v convert.

open Quan Term Contract

namespace Interp

theorem pars_hole (h : Pars bk x y) : Pars bk (inst C x) (inst C y) := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (par_inst par_refl s) ih

theorem claim_laws : Claim.laws := by
  intro bk k t v p C b A hc ht ev cp lp tp
  obtain ⟨_, lv⟩ := book_check bk hc
  have h0 : Conv bk (inst C (Ref k)) (inst C t) := by
    rcases ht with rfl | ⟨d, hd, rfl⟩
    · exact crefl
    · exact ⟨_, .step (par_inst par_refl (.delta hd (lv.1 k d hd))) .refl, .refl⟩
  have h1 : Conv bk (inst C t) b := adequate bk p _ _ b A hc cp lp tp crefl
  have h2 : Pars bk (inst C (Ref k)) (inst C v) := pars_hole (evals_pars lv.1 ev)
  exact conv_trans (conv_trans ⟨inst C v, .refl, h2⟩ h0) h1

-- Input
-- =====

theorem check_from_at : ∀ (ds : List Def) i, Book.check_from bk ls i ds = .ok () →
    ∀ j d, ds[j]? = some d → Def.check bk ls (i + j) d = .ok ()
  | [], _, _, _, _, e => by simp at e
  | d :: ds, i, h, j, e, he => by
    simp only [Book.check_from] at h
    cases h2 : Def.check bk ls i d with
    | error => simp [h2, Except.mapError, bind, Except.bind] at h
    | ok u =>
      cases u
      simp only [h2, Except.mapError, bind, Except.bind] at h
      cases j with
      | zero => simp at he; subst he; exact h2
      | succ j => simpa [Nat.add_assoc, Nat.add_comm 1] using check_from_at ds (i + 1) h j e he

-- in a checked book, each def is the def that its name finds
theorem check_get {j : Nat} {d : Def} (h : Book.check bk = .ok ()) (e : bk.defs[j]? = some d) :
    Book.get bk d.k = some d := by
  have c := check_from_at bk.defs 0 h j d e
  simp only [Def.check, Res.need, Nat.zero_add] at c
  have hi : Book.index bk d.k = some j := by
    revert c; cases hb : (Book.index bk d.k == some j) <;> simp_all [bind, Except.bind]
  rw [index_find, List.findIdx?_eq_some_iff_getElem] at hi
  obtain ⟨hj, hk, hb⟩ := hi
  rw [get_find, List.find?_eq_some_iff_getElem]
  have hd : bk.defs[j] = d := by simpa [List.getElem?_eq_getElem hj] using e
  exact ⟨by simp, j, hj, hd, fun i hi => by simpa using hb i hi⟩

theorem bytes_closed (bs : List UInt8) : Term.Closed (Bytes.term bs) := by
  have nat (n : Nat) : Term.Closed (Bytes.nat n) := by
    induction n with
    | zero => intro σ; rfl
    | succ n ih => intro σ; simp [Bytes.nat, sub, ih σ]
  induction bs with
  | nil => intro σ; rfl
  | cons b bs ih => intro σ; simp [Bytes.term, sub, ih σ, nat _ σ]

theorem bytes_live (g : Guard) (bs : List UInt8) : Term.live g true (Bytes.term bs) = true := by
  have nat (n : Nat) : Term.live g true (Bytes.nat n) = true := by
    induction n with
    | zero => rfl
    | succ n ih => simp [Bytes.nat, Term.live, ih, Quan.live]
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [Bytes.term, Term.live, ih, nat, Quan.live]

-- in a checked book with more defs, a def of bk is still the def that its name
-- finds
theorem get_of (hc : Book.check (Book.of (bk.defs ++ ds)) = .ok ()) (h : Book.get bk k = some d) :
    Book.get (Book.of (bk.defs ++ ds)) k = some d := by
  rw [get_find] at h
  obtain ⟨-, j, hj, hdj, -⟩ := List.find?_eq_some_iff_getElem.1 h
  obtain rfl : d.k = k := by simpa using List.find?_some h
  exact check_get (j := j) hc (by
    simp only [Book.of]; rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj, hdj])

-- the head of a spine does not depend on the arguments taken so far
theorem unspine_head (t : Term) (xs ys : List Arg) :
    (unspine t xs).1 = (unspine t ys).1 := by
  induction t generalizing xs ys with
  | App q f x ihf _ => exact ihf _ _
  | _ => rfl

-- at the top, the live check of a call adds the check that the call may run
theorem live_top (h : (unspine t []).1 = Ref k) :
    Term.live g true t = (Term.called g t && Term.live g false t) := by
  cases t <;> simp_all [unspine, Term.live, Bool.and_assoc]

-- a call of a def of the book may run outside the book
theorem called_ref (h : (unspine t []).1 = Ref k) (hi : Book.index bk k = some i) :
    Term.called ⟨bk, bk.length, [], [], []⟩ t = true := by
  rcases hu : unspine t [] with ⟨hd, xs⟩
  simp only [hu] at h
  subst h
  simp [Term.called, hu, hi, index_lt hi]

-- a proof p of P, applied to the values ys that fill the binders of P, proves
-- R. It stays closed, live below the top, and a call of the same def.
theorem inst_proof (hi : Inst bk P ys R) (cp : Term.Closed p) (tp : Typed bk [] p P)
    (lp : Term.live ⟨bk, bk.length, [], [], []⟩ false p = true) (hp : (unspine p []).1 = Ref k) :
    ∃ p', Term.Closed p' ∧ Typed bk [] p' R ∧
      Term.live ⟨bk, bk.length, [], [], []⟩ false p' = true ∧ (unspine p' []).1 = Ref k := by
  induction hi generalizing p with
  | nil => exact ⟨p, cp, tp, lp, hp⟩
  | all cy ly ty _ ih =>
    refine ih (p := App _ p _) (fun σ => by simp [sub, cp σ, cy σ]) (.app tp ty) ?_ ?_
    · simp only [Term.Live] at ly
      simp [Term.live, lp, ly]
    · simp only [unspine]; rw [unspine_head p _ []]; exact hp

-- RUN reaches W(t), for the call t that a law names
theorem run_call (hcl : Book.Closed bk)
    (hR : Book.get bk RUN = some ⟨RUN, T, App q (Ref "main") (Ref INPUT), false⟩)
    (hI : Book.get bk INPUT = some ⟨INPUT, A, x, false⟩) (hm : Book.get bk "main" = some dm)
    (h : Call dm q x W t) : Pars bk (Ref RUN) (inst W t) := by
  have hmain : Pars bk (Ref RUN) (App q (Ref "main") x) :=
    .step (.delta hR (hcl _ _ hR)) (.step (.app .ref (.delta hI (hcl _ _ hI))) .refl)
  cases h with
  | main => exact hmain
  | body hb =>
    refine pars_trans hmain (.step (.app (.delta hm (hcl _ _ hm)) par_refl) ?_)
    rw [hb]
    exact .step (.beta par_refl par_refl) .refl
  | inner hb =>
    refine pars_trans hmain (.step (.app (.delta hm (hcl _ _ hm)) par_refl) ?_)
    rw [hb]
    exact .step (.beta par_refl par_refl) .refl

theorem claim_input : Claim.input cli := by
  intro n bk bs o dm q A B L dL r P h hm hT hL hP
  obtain ⟨bk', k, he, hc, hc', -, ⟨v, ev, vv, ov⟩, -⟩ := claim_cli.1 n bk (some bs) o h
  simp only [entry, Input.apply, hm, hT, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨_, v, by simp [entry, Input.apply, hm, hT], ev, vv, ov, fun ys W t C b T hcall hi => ?_⟩
  obtain ⟨wt, lv⟩ := book_check _ hc'
  have hI' := check_get (j := bk.defs.length) (d := ⟨INPUT, A, Bytes.term bs, false⟩) hc'
    (by simp [Book.of])
  have hR' := check_get (j := bk.defs.length + 1)
    (d := ⟨RUN, inst B (Ref INPUT), App q (Ref "main") (Ref INPUT), false⟩) hc' (by simp [Book.of])
  have hL' := get_of hc' hL
  -- the proof of the instance: L applied to bs, then to ys
  have tp := Typed.app (by simpa [sub_var, hP] using Typed.ref (Γ := []) (σ := Var) hL')
    (wt _ _ hI').2.1
  obtain ⟨p, cp, tp, lp, hp⟩ := inst_proof hi (fun σ => by simp [sub, bytes_closed bs σ]) tp
    (by simp [Term.live, bytes_live]) rfl
  obtain ⟨i, hiL⟩ := index_of_get hL'
  have h1 := adequate _ p _ _ b T hc' cp
    (by simp only [Term.Live]; rw [live_top hp, called_ref hp hiL, lp]; rfl) tp crefl
  have h2 := evals_pars lv.1 ev
  have h0 := run_call lv.1 hR' hI' (get_of hc' hm) hcall
  exact ⟨conv_trans ⟨_, .refl, h0⟩ ⟨_, h2, .refl⟩, h1⟩

-- when W is the hole, a law holds of the value v itself: C(v) and b convert,
-- as claim 7 said before W
theorem input_hole (hv : Conv bk (inst (Var 0) t) v) (hb : Conv bk (inst C t) b) :
    Conv bk (inst C v) b := by
  obtain ⟨c, h1, h2⟩ := hv
  exact conv_trans ⟨_, pars_hole h2, pars_hole h1⟩ hb

end Interp
