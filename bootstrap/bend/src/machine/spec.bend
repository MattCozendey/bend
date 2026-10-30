import Base
import ../source/impl.bend as Source
import ./impl.bend as Machine

# Machine laws
# ============
#
# The machine's run of def k of a book gives the result that the source's run
# of Ref k gives: the same data, or none. The laws hold for each book and each
# name, typed or not.

# for a book, a name and a fuel n of the source: a fuel of the machine
law fuel_m:
  for bk: List<&2, Source.Def>
  for k: List<&2, Nat>
  for n: Nat
  Nat

# for a book, a name and a fuel n of the machine: a fuel of the source
law fuel_s:
  for bk: List<&2, Source.Def>
  for k: List<&2, Nat>
  for n: Nat
  Nat

# The machine gives each result that the source gives.
law keeps:
  for bk: List<&2, Source.Def>
  for k: List<&2, Nat>
  for n: Nat
  {Source.Obs.is_kept(Source.Maybe.observe(Source.Term.run(n, Source.Term.Ref{k}, bk)),
    Machine.Machine.start(fuel_m(bk, k, n), bk, k)) == True{} : Bool}

# The machine gives no result that the source does not give.
law adds_none:
  for bk: List<&2, Source.Def>
  for k: List<&2, Nat>
  for n: Nat
  {Source.Obs.is_kept(Machine.Machine.start(n, bk, k),
    Source.Maybe.observe(Source.Term.run(fuel_s(bk, k, n), Source.Term.Ref{k}, bk))) == True{} : Bool}
