import Base
import ./src/compile/spec.bend as Compile
import ./src/compile/impl.bend as Impl

# The compiler in Bend. The interpreter runs main on the bytes of a .bendtt
# text, and writes the bytes of the output.
def main(src: List<&2, Nat>) -> List<&2, Nat>:
  Compile.compile(src)
