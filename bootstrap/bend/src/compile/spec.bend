import Base
import ../source/impl.bend as Source

# Compile
# =======
#
# The contract of the compiler in Bend: its interface and its laws. The source
# and the output are .bendtt texts, and Source.run is the meaning of both. The
# laws hold for each text, typed or not. main is λsrc. compile(src), so claim 7
# (Contract/Spec.lean) carries them to the bytes that the interpreter writes.

# the output for the source src
law compile:
  for src: List<&2, Nat>
  List<&2, Nat>

# for a source, an input and a fuel n of the source: a fuel of the output
law fuel_out:
  for src: List<&2, Nat>
  for input: Maybe<&2, List<&2, Nat>>
  for n: Nat
  Nat

# for a source, an input and a fuel n of the output: a fuel of the source
law fuel_src:
  for src: List<&2, Nat>
  for input: Maybe<&2, List<&2, Nat>>
  for n: Nat
  Nat

# The output gives each result that the source gives (as claim 2, total). So
# the compiler cannot refuse a source that has a result.
law keeps_results:
  for src: List<&2, Nat>
  for input: Maybe<&2, List<&2, Nat>>
  for n: Nat
  {Source.Obs.is_kept(Source.run(n, src, input), Source.run(fuel_out(src, input, n), compile(src), input)) ==
    True{} : Bool}

# The output gives no result that the source does not give (as claim 1,
# correct).
law adds_no_results:
  for src: List<&2, Nat>
  for input: Maybe<&2, List<&2, Nat>>
  for n: Nat
  {Source.Obs.is_kept(Source.run(n, compile(src), input), Source.run(fuel_src(src, input, n), src, input)) ==
    True{} : Bool}
