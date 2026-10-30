import Base
import ../source/impl.bend as Source
import ../machine/impl.bend as Machine
import ../compile_wasm/spec.bend as Contract
import ../fun/impl.bend as Fun
import ./impl.bend as FM
import ./code.bend as Code

# Laws of the machine in F
# ========================
#
# From FM.start, the F program ends with the encoding of the output
# (Contract.Out.of) of the machine's result on the entry (Source.entry), when
# the machine has one; and when the program ends, the machine's run of as many
# steps ends with that output. The laws hold for each book. The input must be
# bytes: the program shares one term for each number to 255.

# the encoding of the output of a result of the machine
def Res(m: Maybe<&2, Source.Obs>) -> Maybe<&2, Fun.V>:
  match m:
    case Some{o}:
      Some{FM.Enc.name(Contract.Out.of(o))}
    case None{}:
      None{}

# the machine's run of the entry, with at most n steps
def Run.at(n: Nat, e: Maybe<&2, Source.Entry>) -> Maybe<&2, Source.Obs>:
  match e:
    case Some{Source.Entry{bk, k}}:
      Machine.Machine.start(n, bk, k)
    case None{}:
      None{}

def Input.le(bs: List<&2, Nat>, +c: Nat) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{b, rest}:
      Nat.is_le(b, c) && Input.le(rest, c)

# whether each byte of the input is at most c, or there is no input
def Input.ok(input: Maybe<&2, List<&2, Nat>>, +c: Nat) -> Bool:
  match input:
    case Some{bs}:
      Input.le(bs, c)
    case None{}:
      True{}

# The program ends with the output of the machine's result.
law keeps:
  for bk: List<&2, Source.Def>
  for input: Maybe<&2, List<&2, Nat>>
  for n: Nat
  for c: Nat
  for w: Fun.V
  for hb: {Input.ok(input, c) == True{} : Bool}
  for h: {Res(Run.at(n, Source.entry(input, bk))) == Some{w} : Maybe<&2, Fun.V>}
  Fun.Reach(Code.prog(), Fun.Step.go{FM.start.of(bk, input, c)}, Fun.Step.halt{w})

# The program ends with no other output: an end after n steps is the output of
# the machine's result after n steps.
law adds_none:
  for bk: List<&2, Source.Def>
  for input: Maybe<&2, List<&2, Nat>>
  for n: Nat
  for c: Nat
  for w: Fun.V
  for hb: {Input.ok(input, c) == True{} : Bool}
  for h: {Fun.F.run(n, Code.prog(), FM.start.of(bk, input, c)) == Some{w} : Maybe<&2, Fun.V>}
  {Res(Run.at(n, Source.entry(input, bk))) == Some{w} : Maybe<&2, Fun.V>}
