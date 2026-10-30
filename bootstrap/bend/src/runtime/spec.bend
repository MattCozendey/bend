import Base
import ../wasm/impl.bend as Wasm
import ../imp/impl.bend as Imp
import ../fun/impl.bend as Fun
import ./impl.bend as RT

# Laws of the run time
# ====================
#
# The run time of an F program computes what the abstract machine of F
# computes from Start: the code of the function entry, with the environment
# head, the input (In.val), then tail. Its output is the bytes of the value at
# the end (Out.dec), or Out.oom. The laws hold for each program whose image
# fits (RT.fits).

# the input as an F value: a Maybe of a list of numbers
def In.name(bs: List<&2, Nat>) -> Fun.V:
  match bs:
    case Nil{}:
      Fun.V.num(0n)
    case Con{b, rest}:
      Fun.V.n{1n, Fun.V.num(b), In.name(rest)}

def In.val(input: Maybe<&2, List<&2, Nat>>) -> Fun.V:
  match input:
    case None{}:
      Fun.V.num(0n)
    case Some{bs}:
      Fun.V.n{1n, In.name(bs), Fun.V.z{}}

def Start(c: Fun.C, head: Fun.V, input: Maybe<&2, List<&2, Nat>>, tail: List<&2, Fun.V>) -> Fun.S:
  Fun.S.run{c, Con{head, Con{In.val(input), tail}}, []}

def Out.dec.con(x: Nat, m: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Nat>>:
  match m:
    case Some{xs}:
      Some{Con{x, xs}}
    case None{}:
      None{}

# the numbers of the list w: a node with the tag 0 ends it, and a node with
# the tag 1 holds a number and the rest
def Out.dec(w: Fun.V) -> Maybe<&2, List<&2, Nat>>:
  match w:
    case Fun.V.n{0n, a, b}:
      Some{[]}
    case Fun.V.n{1n, Fun.V.n{x, c, d}, rest}:
      Out.dec.con(x, Out.dec(rest))
    case _:
      None{}

def Out.dec.of(m: Maybe<&2, Fun.V>) -> Maybe<&2, List<&2, Nat>>:
  match m:
    case Some{w}:
      Out.dec(w)
    case None{}:
      None{}

def Bytes.is_eq(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xr} Con{y, yr}:
      Nat.is_eq(x, y) && Bytes.is_eq(xr, yr)
    case _ _:
      False{}

# whether m is the output bs, or Out.oom
def Out.is(m: Maybe<&2, List<&2, Nat>>, bs: List<&2, Nat>) -> Bool:
  match m:
    case Some{+x}:
      Bytes.is_eq(x, bs) || Bytes.is_eq(x, [255n])
    case None{}:
      False{}

# for a program, the start, the input, a number n of steps and the output: a
# fuel of the run time
law fuel:
  for prog: List<&2, Fun.C>
  for c: Fun.C
  for head: Fun.V
  for tail: List<&2, Fun.V>
  for input: Maybe<&2, List<&2, Nat>>
  for n: Nat
  for bs: List<&2, Nat>
  Nat

# The run time gives the output of each end of the abstract machine, or
# Out.oom.
law keeps:
  for prog: List<&2, Fun.C>
  for entry: Nat
  for c: Fun.C
  for head: Fun.V
  for tail: List<&2, Fun.V>
  for pages: Nat
  for input: Maybe<&2, List<&2, Nat>>
  for n: Nat
  for w: Fun.V
  for bs: List<&2, Nat>
  for he: {List.get(&2, Fun.C, prog, entry) == Some{c} : Maybe<&2, Fun.C>}
  for hi: {RT.fits(prog, head, tail) == True{} : Bool}
  for hf: {Wasm.Wasm.fits(pages, input) == True{} : Bool}
  for h: {Fun.F.iter(n, prog, Fun.Step.go{Start(c, head, input, tail)}) == Fun.Step.halt{w} : Fun.Step}
  for hd: {Out.dec(w) == Some{bs} : Maybe<&2, List<&2, Nat>>}
  {Out.is(Imp.Imp.run(pages, fuel(prog, c, head, tail, input, n, bs), RT.RT(prog, entry, head, tail), input),
    bs) == True{} : Bool}

# The run time gives no other output: each output that is not Out.oom is the
# output of the end of the abstract machine after as many steps.
law adds_none:
  for prog: List<&2, Fun.C>
  for entry: Nat
  for c: Fun.C
  for head: Fun.V
  for tail: List<&2, Fun.V>
  for pages: Nat
  for input: Maybe<&2, List<&2, Nat>>
  for n: Nat
  for x: List<&2, Nat>
  for he: {List.get(&2, Fun.C, prog, entry) == Some{c} : Maybe<&2, Fun.C>}
  for hi: {RT.fits(prog, head, tail) == True{} : Bool}
  for h: {Imp.Imp.run(pages, n, RT.RT(prog, entry, head, tail), input) == Some{x} : Maybe<&2, List<&2, Nat>>}
  for hx: {Bytes.is_eq(x, [255n]) == False{} : Bool}
  {Out.dec.of(Fun.F.run(n, prog, Start(c, head, input, tail))) == Some{x} : Maybe<&2, List<&2, Nat>>}
