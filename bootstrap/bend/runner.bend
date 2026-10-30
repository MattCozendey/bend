import Base
import ./src/runner/impl.bend as Runner
import ./src/runner/proof.bend as Proof

# The runner in Bend. The interpreter runs main on the bytes of a job (see
# src/runner/impl.bend), and writes the bytes of its output.
def main(+bs: List<&2, Nat>) -> List<&2, Nat>:
  Runner.run(bs)
