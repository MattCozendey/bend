import Base
import ../source/impl.bend as Source

# Runner
# ======
#
# A runner of pure kernel programs, written in Bend. It gives the result that
# Source.run gives, as the CLI (Main.lean) writes it. The interpreter runs it on
# one list of bytes, a job:
# - the fuel n: 4 bytes, the high byte first;
# - the length k of the program text: 4 bytes, the high byte first;
# - the program text (.bendtt): k bytes;
# - the input of its main: the rest of the bytes.
# A job runs as Source.run(n, text, Some{input}), unless a def of the text is
# opaque: Eval runs the model of an opaque def, which is no real result. Eval
# needs no types, so the runner checks none.
#
# The first byte of the output says what follows:
# - 0: no result. The bytes are no job, the text does not parse, a def is
#   opaque, main takes no input, n is too small, or the result is not plain
#   data.
# - 1: the result, a list of bytes.
# - 2: the result, as the text that the CLI writes for it.

# Jobs
# ====

type Job is Data:
  Job{fuel: Nat, src: List<&2, Nat>, input: List<&2, Nat>}

# the number that the bytes bs show after acc, the high byte first
def Job.number(bs: List<&2, Nat>, acc: Nat) -> Nat:
  match bs:
    case Nil{}:
      acc
    case Con{b, rest}:
      Job.number(rest, Nat.add(Nat.mul(acc, 256n), b))

# the job of the fuel n, the text length k and the bytes after them; none when
# they hold fewer than k bytes
def Job.of(+n: Nat, +k: Nat, +rest: List<&2, Nat>) -> Maybe<&2, Job>:
  Source.Maybe.when(Job, Nat.is_le(k, List.length(&2, Nat, rest)),
    u => Some{Job{n, List.take(&2, Nat, rest, k), List.drop(&2, Nat, rest, k)}})

# the job that the bytes bs hold, or none
def Job.read(bs: List<&2, Nat>) -> Maybe<&2, Job>:
  match bs:
    case Con{n0, Con{n1, Con{n2, Con{n3, Con{k0, Con{k1, Con{k2, Con{k3, rest}}}}}}}}:
      Job.of(Job.number([n0, n1, n2, n3], 0n), Job.number([k0, k1, k2, k3], 0n), rest)
    case _:
      None{}

# no def of the book bk is opaque
def Book.is_transparent(bk: List<&2, Source.Def>) -> Bool:
  match bk:
    case Nil{}:
      True{}
    case Con{Source.Def{k, t, v, o}, rest}:
      Bool.not(o) && Book.is_transparent(rest)

# the result of a job, after its text parsed to m: Source.run's, when no def is
# opaque
def Job.parsed(+n: Nat, m: Maybe<&2, List<&2, Source.Def>>, input: List<&2, Nat>) ->
  Maybe<&2, Source.Obs>:
  match m:
    case Some{+bk}:
      Source.Maybe.when(Source.Obs, Book.is_transparent(bk),
        u => Source.run.of(n, Some{input}, Some{bk}))
    case None{}:
      None{}

# the result of the job j, or none
def Job.run(j: Maybe<&2, Job>) -> Maybe<&2, Source.Obs>:
  match j:
    case Some{Job{+n, src, input}}:
      Job.parsed(n, Source.Book.parse(n, src), input)
    case None{}:
      None{}

# Output
# ======

# o is the label .k
def Obs.is_lab(o: Source.Obs, k: String) -> Bool:
  match o:
    case Source.Obs.lab{j}:
      Source.Name.is_eq(j, Source.Name.of(k))
    case _:
      False{}

# m plus one
def Obs.to_nat.succ(m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case Some{n}:
      Some{1n+n}
    case None{}:
      None{}

# Bytes.ofNat: the number that o shows, when o is a Nat
def Obs.to_nat(o: Source.Obs) -> Maybe<&2, Nat>:
  match o:
    case Source.Obs.tup{t, Source.Obs.tup{p, u}}:
      Source.Maybe.when(Nat, Obs.is_lab(t, "Succ") && Obs.is_lab(u, "()"),
        w => Obs.to_nat.succ(Obs.to_nat(p)))
    case Source.Obs.tup{t, u}:
      Source.Maybe.when(Nat, Obs.is_lab(t, "Zero") && Obs.is_lab(u, "()"), w => Some{0n})
    case _:
      None{}

# n before bs, when both are some and n is below 256
def Obs.to_bytes.con(h: Maybe<&2, Nat>, t: Maybe<&2, List<&2, Nat>>) ->
  Maybe<&2, List<&2, Nat>>:
  match h t:
    case Some{+n} Some{bs}:
      Source.Maybe.when(List<&2, Nat>, Nat.is_lt(n, 256n), w => Some{Con{n, bs}})
    case _ _:
      None{}

# Bytes.ofObs: the bytes that o shows, when o is a List of Nat below 256
def Obs.to_bytes(o: Source.Obs) -> Maybe<&2, List<&2, Nat>>:
  match o:
    case Source.Obs.tup{t, Source.Obs.tup{h, Source.Obs.tup{r, u}}}:
      Source.Maybe.when(List<&2, Nat>, Obs.is_lab(t, "Con") && Obs.is_lab(u, "()"),
        w => Obs.to_bytes.con(Obs.to_nat(h), Obs.to_bytes(r)))
    case Source.Obs.tup{t, u}:
      Source.Maybe.when(List<&2, Nat>, Obs.is_lab(t, "Nil") && Obs.is_lab(u, "()"),
        w => Some{[]})
    case _:
      None{}

# the decimal digits of n, as bytes, before acc; f bounds their count
def digits(f: Nat, +n: Nat, +acc: List<&2, Nat>) -> List<&2, Nat>:
  match f:
    case 0n:
      acc
    case 1n+g:
      +q = Nat.div(n, 10n)
      +ds = {Con{Nat.add(48n, Nat.mod(n, 10n)), acc} : List<&2, Nat>}
      Source.Bool.lazy(List<&2, Nat>, Nat.is_eq(q, 0n), u => ds, u => digits(g, q, ds))

# the text of a pair: the number that it shows, when m is some; else (a, b)
def Obs.text.tup(m: Maybe<&2, Nat>, a: Unit -> List<&2, Nat>, b: Unit -> List<&2, Nat>) ->
  List<&2, Nat>:
  match m:
    case Some{+n}:
      digits(1n+n, n, [])
    case None{}:
      List.append(&2, Nat, Source.Name.of("("), List.append(&2, Nat, a(Unit{}),
        List.append(&2, Nat, Source.Name.of(", "),
          List.append(&2, Nat, b(Unit{}), Source.Name.of(")")))))

# render (Main.lean): the text of o, as bytes
def Obs.text(o: Source.Obs) -> List<&2, Nat>:
  match o:
    case Source.Obs.lab{+k}:
      Source.Bool.if(List<&2, Nat>, Source.Name.is_eq(k, Source.Name.of("()")), k, Con{46n, k})
    case Source.Obs.rfl{}:
      Source.Name.of("{==}")
    case Source.Obs.tup{+a, +b}:
      Obs.text.tup(Obs.to_nat(Source.Obs.tup{a, b}), u => Obs.text(a), u => Obs.text(b))
    case Source.Obs.tup0{b}:
      List.append(&2, Nat, Source.Name.of("(-, "),
        List.append(&2, Nat, Obs.text(b), Source.Name.of(")")))

# the output of a result whose bytes are m, when it shows bytes
def Obs.output.of(m: Maybe<&2, List<&2, Nat>>, o: Source.Obs) -> List<&2, Nat>:
  match m:
    case Some{bs}:
      Con{1n, bs}
    case None{}:
      Con{2n, List.append(&2, Nat, Obs.text(o), [10n])}

# the output of the result r (see the header)
def Obs.output(r: Maybe<&2, Source.Obs>) -> List<&2, Nat>:
  match r:
    case Some{+o}:
      Obs.output.of(Obs.to_bytes(o), o)
    case None{}:
      [0n]

# Run
# ===

# the output of the job that the bytes bs hold
def run(bs: List<&2, Nat>) -> List<&2, Nat>:
  Obs.output(Job.run(Job.read(bs)))
