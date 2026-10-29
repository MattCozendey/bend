import Run

-- Cli
-- ===
--
-- The function that the CLI calls, and the proof of claim 4 (cli).

open Quan Term Contract

namespace Interp

-- the fuel of the CLI's run: 2^64 steps
def FUEL_RUN : Nat := 2 ^ 64

-- cli fuel bk input: the result of def main of bk, or of main(input), with at
-- most fuel steps.
-- 1. The kernel checks bk, as for --verdict.
-- 2. entry gives the book and the def to run. With an input, the kernel also
--    checks that book. Without one, that book is bk.
-- 3. The interpreter compiles the def (only a Pure def) and runs it.
def cli (fuel : Nat) (bk : Book) (input : Option (List UInt8)) : Except String Obs := do
  Book.check bk
  let some (bk', k) := entry bk input
    | .error "with an input, main must be a function of one argument"
  if input.isSome then Book.check bk'
  let code ← compiler.compile bk' k
  let some o := compiler.run fuel code | .error "out of fuel"
  pure o

theorem claim_cli : Claim.cli cli := by
  refine ⟨fun fuel bk input o h => ?_, fun bk input bk' k he hc hc' hp => ?_⟩
  · simp only [cli, bind, Except.bind] at h
    cases hc : Book.check bk with
    | error => simp [hc] at h
    | ok u =>
      cases u
      simp only [hc] at h
      cases he : entry bk input with
      | none => simp [he] at h
      | some p =>
        obtain ⟨bk', k⟩ := p
        have hc' : Book.check bk' = .ok () := by
          cases input with
          | none =>
            simp only [entry, Option.some.injEq, Prod.mk.injEq] at he
            obtain ⟨rfl, -⟩ := he; exact hc
          | some bs => simp only [he, Option.isSome_some, ite_true] at h; revert h; cases Book.check bk' <;> simp
        simp only [he, hc', ite_self, pure, Except.pure] at h
        cases hcomp : compiler.compile bk' k with
        | error => simp [hcomp] at h
        | ok code =>
          cases hr : compiler.run fuel code with
          | none => simp [hcomp, hr] at h
          | some o' =>
            simp [hcomp, hr] at h; subst h
            obtain ⟨hp, o'', ans, -, never⟩ := claim_correct bk' k code hc' hcomp
            cases never _ _ hr
            exact ⟨bk', k, rfl, rfl, hc', hp, ans⟩
  · obtain ⟨code, hcomp⟩ := claim_total bk' k hc' hp
    obtain ⟨-, o, -, ⟨n, hr⟩, -⟩ := claim_correct bk' k code hc' hcomp
    exact ⟨n, o, by simp [cli, bind, Except.bind, he, hc, hc', hcomp, hr, pure, Except.pure]⟩

end Interp
