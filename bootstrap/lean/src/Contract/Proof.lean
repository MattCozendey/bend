import Cli
import Bytes
import Laws
import Guard

-- Contract.Proof
-- ==============
--
-- The five claims, stated for the interpreter and for the function that
-- the CLI calls. Change this file only after a review. The build pins its
-- hash.

open Contract

theorem final_correct : Claim.correct Interp.compiler := Interp.claim_correct
theorem final_total : Claim.total Interp.compiler := Interp.claim_total
theorem final_bytes : Claim.bytes := Interp.claim_bytes
theorem final_cli : Claim.cli Interp.cli := Interp.claim_cli
theorem final_laws : Claim.laws := Interp.claim_laws

-- What the CLI function runs is what the proofs see.
#guard_runs Interp.cli

-- The proofs use only Lean's three standard axioms.
#guard_axioms final_correct final_total final_bytes final_cli final_laws
