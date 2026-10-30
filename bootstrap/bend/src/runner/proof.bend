import Base
import ../source/impl.bend as Source
import ../source/proof.bend as SourceProof
import ./impl.bend as Runner
import ./spec.bend as Spec

# Runner proofs
# =============
#
# The proofs of the laws of spec.bend. The runner checks each job that it reads
# and each list of bytes that it writes, so each proof takes that check apart.

# Maybes and lists
# ================

# a check that gave some j: f, given that its condition holds and that the
# value it kept is j
def Maybe.when_some(-A: Data, -R: Type, c: Bool, -k: A, -j: A,
  h: {Source.Maybe.when(A, c, u => Some{k}) == Some{j} : Maybe<&2, A>},
  f: {c == True{} : Bool} -> {k == j : A} -> R) -> R:
  match c:
    case True{}:
      f({==}, SourceProof.Maybe.some_inj(A, k, j, h))
    case False{}:
      SourceProof.Empty.elim(R, SourceProof.Maybe.no_none(A, j, h))

# the list l starts with 1
def starts_with_one(l: List<&2, Nat>) -> Bool:
  match l:
    case Nil{}:
      False{}
    case Con{x, t}:
      Nat.is_eq(x, 1n)

# Jobs
# ====

# the job that the check of m keeps writes bs
def Job.read.checked(m: Maybe<&2, Runner.Job>, +bs: List<&2, Nat>, -j: Runner.Job,
  h: {Runner.Job.read.check(m, bs) == Some{j} : Maybe<&2, Runner.Job>}) ->
  {Runner.Job.write(j) == bs : List<&2, Nat>}:
  match m:
    case Some{+k}:
      Maybe.when_some(Runner.Job, {Runner.Job.write(j) == bs : List<&2, Nat>},
        Source.Name.is_eq(Runner.Job.write(k), bs), k, j, h,
        hc => hk => (%hk : {Runner.Job.write(_) == bs : List<&2, Nat>};
          SourceProof.Name.is_eq_true(Runner.Job.write(k), bs, hc)))
    case None{}:
      SourceProof.Empty.elim({Runner.Job.write(j) == bs : List<&2, Nat>},
        SourceProof.Maybe.no_none(Runner.Job, j, h))

def Spec.Job.write_after_read(bs, j, h):
  Job.read.checked(Runner.Job.parse(bs), bs, j, h)

# Output
# ======

# the bytes bs show o, as an input
def Obs.shows(o: Source.Obs, bs: List<&2, Nat>) -> Type:
  {Source.Obs.is_kept(Some{o}, Source.Term.observe(Source.Bytes.term(bs))) == True{} : Bool}

# the bytes that the check of m keeps for o show o
def Obs.checked(m: Maybe<&2, List<&2, Nat>>, +o: Source.Obs, -bs: List<&2, Nat>,
  h: {Runner.Obs.to_bytes.check(m, o) == Some{bs} : Maybe<&2, List<&2, Nat>>}) -> Obs.shows(o, bs):
  match m:
    case Some{+cs}:
      Maybe.when_some(List<&2, Nat>, Obs.shows(o, bs),
        Source.Obs.is_kept(Some{o}, Source.Term.observe(Source.Bytes.term(cs))), cs, bs, h,
        hc => hk => (%hk : Obs.shows(o, _); hc))
    case None{}:
      SourceProof.Empty.elim(Obs.shows(o, bs), SourceProof.Maybe.no_none(List<&2, Nat>, bs, h))

# an output that starts with 1 holds bytes that show o; m is the bytes of o
def Obs.output.one(m: Maybe<&2, List<&2, Nat>>, +o: Source.Obs, -bs: List<&2, Nat>,
  hm: {Runner.Obs.to_bytes(o) == m : Maybe<&2, List<&2, Nat>>},
  h: {Runner.Obs.output.of(m, o) == Con{1n, bs} : List<&2, Nat>}) -> Obs.shows(o, bs):
  match m:
    case Some{cs}:
      %Equal.cong(List<&2, Nat>, List<&2, Nat>, l => List.tail(&2, Nat, l), Con{1n, cs}, Con{1n, bs}, h) :
        Obs.shows(o, _)
      Obs.checked(Runner.Obs.to_bytes.go(o), o, cs, hm)
    case None{}:
      SourceProof.Empty.elim(Obs.shows(o, bs),
        SourceProof.Bool.no(Equal.cong(List<&2, Nat>, Bool, starts_with_one,
          Con{2n, List.append(&2, Nat, Runner.Obs.text(o), [10n])}, Con{1n, bs}, h)))

def Spec.Obs.bytes_show_result(r, bs, h):
  match r:
    case Some{+o}:
      Obs.output.one(Runner.Obs.to_bytes(o), o, bs, {==}, h)
    case None{}:
      {==}
