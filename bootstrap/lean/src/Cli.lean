import Run

-- Cli
-- ===
--
-- The function that the CLI calls, and the proof of claim 4 (cli): when it
-- gives a result, that is the result of the def it runs.

open Quan Term Spec

namespace Interp

-- the fuel of the CLI's run: 2^64 steps
def FUEL_RUN : Nat := 2 ^ 64

-- cli bk input: the result of def main of bk, or of main(input).
-- 1. entry gives the book and the def to run.
-- 2. The kernel checks that book.
-- 3. The interpreter compiles the def (only a Pure def) and runs it.
def cli (bk : Book) (input : Option (List UInt8)) : Except String Obs :=
  match entry bk input with
  | none => .error "with an input, main must be a function of one argument"
  | some (bk', k) =>
    match Book.check bk' with
    | .error e => .error e
    | .ok () =>
      match compiler.compile bk' k with
      | .error e => .error e
      | .ok code =>
        match compiler.run FUEL_RUN code with
        | some o => .ok o
        | none => .error "out of fuel"

theorem cli_ok : Claim.cli cli := by
  intro bk input o h
  unfold cli at h
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
          obtain ⟨hp, o'', ans, -, never⟩ := correct bk' k code hc hcomp
          cases never _ _ hr
          exact ⟨bk', k, he, hc, hp, ans⟩
        · simp at h

end Interp
