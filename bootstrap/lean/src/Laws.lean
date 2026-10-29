import Cli

-- Laws
-- ====
--
-- The proofs of claim 5 (laws) and claim 7 (input).
-- - Claim 5: a law about def k, or about its body, holds about each value
--   that Eval reaches from k. It joins the kernel's adequate with Eval's
--   reduction, and with one δ step for the body.
-- - Claim 7: the instance of a law at the CLI's input is a closed, live,
--   typed proof in the CLI's book, so claim 5 applies to it. Its equality
--   names main(bs), and the body of RUN is main(INPUT): one δ step joins
--   them.

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

theorem claim_input : Claim.input cli := by
  intro n bk bs o dm q A B L dL r P C b T h hm hT hL hP hI
  obtain ⟨bk', k, he, hc, hc', -, ⟨v, ev, vv, ov⟩, -⟩ := claim_cli.1 n bk (some bs) o h
  simp only [entry, Input.apply, hm, hT, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  generalize hx : Bytes.term bs = x at *
  have at_ (j : Nat) (d : Def) (e : _) := check_get (j := j) (d := d) hc' e
  have hI' := at_ bk.defs.length ⟨INPUT, A, x, false⟩ (by simp [Book.of])
  have hR' := at_ (bk.defs.length + 1)
    ⟨RUN, inst B (Ref INPUT), App q (Ref "main") (Ref INPUT), false⟩ (by simp [Book.of])
  rw [get_find] at hL
  obtain ⟨-, j, hj, hdj, -⟩ := List.find?_eq_some_iff_getElem.1 hL
  obtain rfl : dL.k = L := by simpa using List.find?_some hL
  have hL' := at_ j dL (by simp only [Book.of]; rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj, hdj])
  have hx' : Typed _ [] x A := ((book_check _ hc').1 _ _ hI').2.1
  have tp := Typed.app (by simpa [sub_var, hP] using Typed.ref (Γ := []) (σ := Var) hL') hx'
  rw [hI] at tp
  have tp' : Typed _ [] _ (Eql (inst C (App q (Ref "main") (Ref INPUT))) b T) :=
    .conv tp (.conv ⟨_, .refl, .step (.eql (par_inst par_refl
      (.app par_refl (.delta hI' (hx ▸ bytes_closed bs)))) par_refl par_refl) .refl⟩)
  have cp : Term.Closed (App r (Ref dL.k) x) := fun σ => by
    simp [sub, ← hx, bytes_closed bs σ]
  refine ⟨_, v, by simp [entry, Input.apply, hm, hT, ← hx], ev, vv, ov, claim_laws _ RUN _ v _ C b T hc' (.inr ⟨_, hR', rfl⟩) ev cp ?_ tp'⟩
  obtain ⟨i, hi⟩ := index_of_get hL'
  subst hx
  simp [Term.Live, Term.live, Term.called, unspine, hi, index_lt hi, bytes_live]

end Interp
