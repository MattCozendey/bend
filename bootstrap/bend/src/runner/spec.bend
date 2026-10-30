import Base
import ../source/impl.bend as Source
import ./impl.bend as Runner

# Runner laws
# ===========
#
# The laws of the runner in Bend. They hold for each list of bytes and each
# result.

# a job that the runner reads from bytes writes exactly those bytes
law Job.write_after_read:
  for +bs: List<&2, Nat>
  for j: Runner.Job
  for h: {Runner.Job.read(bs) == Some{j} : Maybe<&2, Runner.Job>}
  {Runner.Job.write(j) == bs : List<&2, Nat>}

# the bytes after a first byte 1 of the output show the result r, as an input:
# Source.Obs.is_kept compares them as the compiler's laws compare results
law Obs.bytes_show_result:
  for r: Maybe<&2, Source.Obs>
  for bs: List<&2, Nat>
  for h: {Runner.Obs.output(r) == Con{1n, bs} : List<&2, Nat>}
  {Source.Obs.is_kept(r, Source.Term.observe(Source.Bytes.term(bs))) == True{} : Bool}
