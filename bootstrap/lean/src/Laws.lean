import Run

-- Laws
-- ====
--
-- The proof of claim 5 (laws): a law about def k, or about its body, holds
-- about each value that Eval reaches from k. It joins the kernel's adequate
-- with Eval's reduction, and with one δ step for the body.

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

end Interp
