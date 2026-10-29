import Run

-- Laws
-- ====
--
-- The proof of claim 5 (laws): a law about def k holds about each value
-- that Eval reaches from k. It joins the kernel's adequate with Eval's
-- reduction.

open Quan Term Spec

namespace Interp

theorem pars_hole (h : Pars bk x y) : Pars bk (inst C x) (inst C y) := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (par_inst par_refl s) ih

theorem laws : Claim.laws := by
  intro bk k v p C b A hc ev cp lp tp
  obtain ⟨_, lv⟩ := book_check bk hc
  have h1 : Conv bk (inst C (Ref k)) b := adequate bk p _ _ b A hc cp lp tp crefl
  have h2 : Pars bk (inst C (Ref k)) (inst C v) := pars_hole (evals_pars lv.1 ev)
  exact conv_trans ⟨inst C v, .refl, h2⟩ h1

end Interp
