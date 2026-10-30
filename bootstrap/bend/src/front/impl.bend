import Base
import ../source/impl.bend as Source

# Front
# =====
#
# The front of the compiler: the parse of a source with a fuel that its length
# gives. Source.run parses with the fuel of the run; spec.bend states that this
# fuel parses each text that some fuel parses, to the same defs. The parser
# nests a call only after it reads a byte, but for the next item of a tuple
# and the next argument of an application; so 2 per byte, and 2 more, are
# enough.

# the fuel of the parse of src
def Front.fuel(src: List<&2, Nat>) -> Nat:
  1n+1n+Nat.double(List.length(&2, Nat, src))

# the defs of src, or none when it does not parse
def Front.book(+src: List<&2, Nat>) -> Maybe<&2, List<&2, Source.Def>>:
  Source.Book.parse(Front.fuel(src), src)
