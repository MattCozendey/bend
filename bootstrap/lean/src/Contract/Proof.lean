import Cli
import Bytes
import Laws
import Shut
import Guard

-- Contract.Proof
-- ==============
--
-- The seven claims, stated for the interpreter and for the function that the
-- CLI calls, and the guards. The build pins its hash, so change it only after
-- a review.

open Contract

theorem final_correct : Claim.correct Interp.compiler := Interp.claim_correct
theorem final_total : Claim.total Interp.compiler := Interp.claim_total
theorem final_bytes : Claim.bytes := Interp.claim_bytes
theorem final_cli : Claim.cli Interp.cli := Interp.claim_cli
theorem final_laws : Claim.laws := Interp.claim_laws
theorem final_shut : Claim.shut := Interp.claim_shut
theorem final_input : Claim.input Interp.cli := Interp.claim_input

-- What the CLI runs is what the proofs see: the CLI function, and the
-- function that makes its result into output bytes.
#guard_runs Interp.cli
#guard_runs Contract.Bytes.ofObs

-- The proofs use only Lean's three standard axioms.
#guard_axioms final_correct final_total final_bytes final_cli final_laws final_shut
  final_input
