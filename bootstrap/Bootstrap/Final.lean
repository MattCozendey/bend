import Bootstrap.Cli
import Bootstrap.Bytes
import Bootstrap.Laws
import Bootstrap.Guard

-- Final
-- =====
--
-- The five claims, stated for the interpreter and for the function that
-- the CLI calls. Change this file only after a review. The build pins its
-- hash.

open Spec

theorem final_correct : Claim.correct Interp.compiler := Interp.correct
theorem final_total : Claim.total Interp.compiler := Interp.total
theorem final_bytes : Claim.bytes := Interp.bytes
theorem final_cli : Claim.cli Interp.cli := Interp.cli_ok
theorem final_laws : Claim.laws := Interp.laws

-- What the CLI function runs is what the proofs see.
#guard_runs Interp.cli

-- The proofs use only Lean's three standard axioms.
#guard_axioms final_correct final_total final_bytes final_cli final_laws
