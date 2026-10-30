import Base
import ../source/impl.bend as Source
import ./impl.bend as Front

# Front laws
# ==========
#
# proof.bend proves them.

# Each fuel from Front.fuel on parses each text that some fuel parses, to the
# same defs. So Front.book gives the defs of each run that has a result, and
# a run with more fuel than Front.fuel parses as Front.book does.
law parse_above:
  for n: Nat
  for k: Nat
  for src: List<&2, Nat>
  for bk: List<&2, Source.Def>
  for h: {Source.Book.parse(n, src) == Some{bk} : Maybe<&2, List<&2, Source.Def>>}
  {Source.Book.parse(Nat.add(Front.Front.fuel(src), k), src) == Some{bk} : Maybe<&2, List<&2, Source.Def>>}
