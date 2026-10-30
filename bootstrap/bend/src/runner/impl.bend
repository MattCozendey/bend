import Base
import ../source/impl.bend as Source

# Runner
# ======
#
# A runner of pure kernel programs, written in Bend. It gives the result that
# Source.run gives, as the CLI (Main.lean) writes it. The interpreter runs it on
# the bytes of a job, as Job.write writes them:
# - the fuel n: 4 bytes, the high byte first;
# - the program text (.bendtt), with each 0 written as 0 1;
# - 0 0: the end of the text;
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

# the 4 bytes of a fuel, the high byte first
type Fuel is Data:
  Fuel{b3: Nat, b2: Nat, b1: Nat, b0: Nat}

type Job is Data:
  Job{fuel: Fuel, src: List<&2, Nat>, input: List<&2, Nat>}

# a program text, and the bytes after its end
type Split is Data:
  Split{src: List<&2, Nat>, rest: List<&2, Nat>}

# the fuel that f shows
def Fuel.number(f: Fuel) -> Nat:
  match f:
    case Fuel{b3, b2, b1, b0}:
      Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(b3, 256n), b2), 256n), b1), 256n), b0)

# the bytes of the text src, each 0 as 0 1, then 0 0, then rest
def Text.write(src: List<&2, Nat>, rest: List<&2, Nat>) -> List<&2, Nat>:
  match src:
    case Nil{}:
      Con{0n, Con{0n, rest}}
    case Con{0n, t}:
      Con{0n, Con{1n, Text.write(t, rest)}}
    case Con{1n+p, t}:
      Con{1n+p, Text.write(t, rest)}

# the bytes of the job j (see the header)
def Job.write(j: Job) -> List<&2, Nat>:
  match j:
    case Job{Fuel{b3, b2, b1, b0}, src, input}:
      Con{b3, Con{b2, Con{b1, Con{b0, Text.write(src, input)}}}}

# b before the text of m
def Text.read.con(+b: Nat, m: Maybe<&2, Split>) -> Maybe<&2, Split>:
  match m:
    case Some{Split{s, r}}:
      Some{Split{Con{b, s}, r}}
    case None{}:
      None{}

# the text at the start of bs, and the bytes after its end; none when it has no
# end. Job.read checks the result, so this reads 0 and any byte but 0 as 0.
def Text.read(bs: List<&2, Nat>) -> Maybe<&2, Split>:
  match bs:
    case Con{0n, Con{0n, rest}}:
      Some{Split{[], rest}}
    case Con{0n, Con{1n+p, rest}}:
      Text.read.con(0n, Text.read(rest))
    case Con{1n+p, rest}:
      Text.read.con(1n+p, Text.read(rest))
    case _:
      None{}

# the job of the fuel f and the text m
def Job.parse.of(f: Fuel, m: Maybe<&2, Split>) -> Maybe<&2, Job>:
  match m:
    case Some{Split{s, r}}:
      Some{Job{f, s, r}}
    case None{}:
      None{}

# the job that the bytes bs hold, read with no check
def Job.parse(bs: List<&2, Nat>) -> Maybe<&2, Job>:
  match bs:
    case Con{b3, Con{b2, Con{b1, Con{b0, rest}}}}:
      Job.parse.of(Fuel{b3, b2, b1, b0}, Text.read(rest))
    case _:
      None{}

# m, when it writes the bytes bs
def Job.read.check(m: Maybe<&2, Job>, +bs: List<&2, Nat>) -> Maybe<&2, Job>:
  match m:
    case Some{+j}:
      Source.Maybe.when(Job, Source.Name.is_eq(Job.write(j), bs), u => Some{j})
    case None{}:
      None{}

# the job that the bytes bs hold, or none
def Job.read(+bs: List<&2, Nat>) -> Maybe<&2, Job>:
  Job.read.check(Job.parse(bs), bs)

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
    case Some{Job{f, src, input}}:
      +n = Fuel.number(f)
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
def Obs.to_bytes.go(o: Source.Obs) -> Maybe<&2, List<&2, Nat>>:
  match o:
    case Source.Obs.tup{t, Source.Obs.tup{h, Source.Obs.tup{r, u}}}:
      Source.Maybe.when(List<&2, Nat>, Obs.is_lab(t, "Con") && Obs.is_lab(u, "()"),
        w => Obs.to_bytes.con(Obs.to_nat(h), Obs.to_bytes.go(r)))
    case Source.Obs.tup{t, u}:
      Source.Maybe.when(List<&2, Nat>, Obs.is_lab(t, "Nil") && Obs.is_lab(u, "()"),
        w => Some{[]})
    case _:
      None{}

# m, when its bytes show o: as an input, they show o back
def Obs.to_bytes.check(m: Maybe<&2, List<&2, Nat>>, +o: Source.Obs) -> Maybe<&2, List<&2, Nat>>:
  match m:
    case Some{+bs}:
      Source.Maybe.when(List<&2, Nat>,
        Source.Obs.is_kept(Some{o}, Source.Term.observe(Source.Bytes.term(bs))), u => Some{bs})
    case None{}:
      None{}

# the bytes that o shows, when it shows bytes
def Obs.to_bytes(+o: Source.Obs) -> Maybe<&2, List<&2, Nat>>:
  Obs.to_bytes.check(Obs.to_bytes.go(o), o)

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
def run(+bs: List<&2, Nat>) -> List<&2, Nat>:
  Obs.output(Job.run(Job.read(bs)))
