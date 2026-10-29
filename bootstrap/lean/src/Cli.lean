import Run

-- Cli
-- ===
--
-- The function that the CLI calls, and the proof of claim 4 (cli): when it
-- gives a result, that is the result of the def it runs, and some fuel gives
-- a result for each Pure def of a checked book.

open Quan Term Contract

namespace Interp

-- the fuel of the CLI's run: 2^64 steps
def FUEL_RUN : Nat := 2 ^ 64

-- cli fuel bk input: the result of def main of bk, or of main(input), with
-- at most fuel steps.
-- 1. entry gives the book and the def to run.
-- 2. The kernel checks that book.
-- 3. The interpreter compiles the def (only a Pure def) and runs it.
def cli (fuel : Nat) (bk : Book) (input : Option (List UInt8)) : Except String Obs :=
  match entry bk input with
  | none => .error "with an input, main must be a function of one argument"
  | some (bk', k) =>
    match Book.check bk' with
    | .error e => .error e
    | .ok () =>
      match compiler.compile bk' k with
      | .error e => .error e
      | .ok code =>
        match compiler.run fuel code with
        | some o => .ok o
        | none => .error "out of fuel"

theorem claim_cli : Claim.cli cli := by
  refine ⟨fun fuel bk input o h => ?_, fun bk input bk' k he hc hp => ?_⟩
  · unfold cli at h
    split at h
    · simp at h
    · rename_i bk' k he
      split at h
      · simp at h
      · rename_i hc
        split at h
        · simp at h
        · rename_i code hcomp
          split at h
          · rename_i o' hr
            cases h
            obtain ⟨hp, o'', ans, -, never⟩ := claim_correct bk' k code hc hcomp
            cases never _ _ hr
            exact ⟨bk', k, he, hc, hp, ans⟩
          · simp at h
  · obtain ⟨code, hcomp⟩ := claim_total bk' k hc hp
    obtain ⟨-, o, -, ⟨n, hr⟩, -⟩ := claim_correct bk' k code hc hcomp
    exact ⟨n, o, by simp [cli, he, hc, hcomp, hr]⟩

end Interp
