import Base
import ../source/impl.bend as Source
import ../wasm/impl.bend as Wasm

# Compile to WASM
# ===============
#
# The contract of the compiler in Bend that writes WASM: its interface and its
# laws. Source.run is the meaning of the source, and Wasm.Wasm.run the meaning
# of the module. The laws hold for each text, typed or not, each input, each
# memory size and each fuel. main will be λsrc. Wasm.Wasm.encode(compile(src)),
# so claim 7 (Contract/Spec.lean) carries them to the module that the
# interpreter writes.
#
# The excuses:
# - out of memory: the module can give Out.oom where the source gives a
#   result, because a memory of 65535 pages holds only 4 GiB. A compiler whose
#   modules always give Out.oom meets this contract: only tests show that real
#   programs fit.
# - fits: the laws say nothing when the source is not bytes, or when the host
#   cannot run the module (Wasm.Wasm.fits). The interpreter and the host
#   never give such a source or input.

# Outputs
# =======

# whether the labels k and u start and end a constructor named s
def Ctor.is(k: List<&2, Nat>, u: List<&2, Nat>, s: String) -> Bool:
  Source.Name.is_eq(k, Source.Name.of(s)) && Source.Name.is_eq(u, Source.Name.of("()"))

# the number that o shows, when o is a Nat (Bytes.ofNat of Contract/Spec.lean)
def Obs.nat.succ(m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case Some{n}:
      Some{1n+n}
    case None{}:
      None{}

def Obs.nat(o: Source.Obs) -> Maybe<&2, Nat>:
  match o:
    case Source.Obs.tup{Source.Obs.lab{k}, Source.Obs.lab{u}}:
      Bool.pick(Maybe<&2, Nat>, Ctor.is(k, u, "Zero"), Some{0n}, None{})
    case Source.Obs.tup{Source.Obs.lab{k}, Source.Obs.tup{h, Source.Obs.lab{u}}}:
      Bool.pick(Maybe<&2, Nat>, Ctor.is(k, u, "Succ"), Obs.nat.succ(Obs.nat(h)), None{})
    case _:
      None{}

def Obs.bytes.con(n: Maybe<&2, Nat>, bs: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Nat>>:
  match n bs:
    case Some{+x} Some{ys}:
      Bool.pick(Maybe<&2, List<&2, Nat>>, Wasm.Nat.at_most(x, 255), Some{Con{x, ys}}, None{})
    case _ _:
      None{}

# the bytes that o shows, when o is a list of Nats below 256 (Bytes.ofObs of
# Contract/Spec.lean)
def Obs.bytes(o: Source.Obs) -> Maybe<&2, List<&2, Nat>>:
  match o:
    case Source.Obs.tup{Source.Obs.lab{k}, Source.Obs.lab{u}}:
      Bool.pick(Maybe<&2, List<&2, Nat>>, Ctor.is(k, u, "Nil"), Some{[]}, None{})
    case Source.Obs.tup{Source.Obs.lab{k}, Source.Obs.tup{h, Source.Obs.tup{t, Source.Obs.lab{u}}}}:
      Bool.pick(Maybe<&2, List<&2, Nat>>, Ctor.is(k, u, "Con"), Obs.bytes.con(Obs.nat(h), Obs.bytes(t)),
        None{})
    case _:
      None{}

# o as bytes, each part after a tag: 0, the label's length in LEB128 and its
# bytes; 1 for rfl; 2 and both parts of a tup; 3 and the second part of a tup0
def Obs.write(o: Source.Obs) -> List<&2, Nat>:
  match o:
    case Source.Obs.lab{+k}:
      Con{0n, List.append(&2, Nat, Wasm.Leb.nat(List.length(&2, Nat, k)), k)}
    case Source.Obs.rfl{}:
      [1n]
    case Source.Obs.tup{a, b}:
      Con{2n, List.append(&2, Nat, Obs.write(a), Obs.write(b))}
    case Source.Obs.tup0{b}:
      Con{3n, Obs.write(b)}

def Out.of.bytes(m: Maybe<&2, List<&2, Nat>>, o: Source.Obs) -> List<&2, Nat>:
  match m:
    case Some{bs}:
      Con{0n, bs}
    case None{}:
      Con{1n, Obs.write(o)}

# the output for the result o: 0 and the bytes that o shows, when it is a list
# of bytes (the bytes that the interpreter writes), else 1 and Obs.write(o)
def Out.of(+o: Source.Obs) -> List<&2, Nat>:
  Out.of.bytes(Obs.bytes(o), o)

# the output when the memory is too small for the run
def Out.oom() -> List<&2, Nat>:
  [255n]

# whether x is the output for the result o, or Out.oom
def Out.is(+x: List<&2, Nat>, o: Source.Obs) -> Bool:
  Source.Name.is_eq(x, Out.of(o)) || Source.Name.is_eq(x, Out.oom())

# whether the laws speak of a run: the source is bytes, and the host can run
# the module
def Out.fits(src: List<&2, Nat>, +pages: Nat, input: Maybe<&2, List<&2, Nat>>) -> Bool:
  Wasm.Bytes.is(src) && Wasm.Wasm.fits(pages, input)

# when ok and r is a result: w is its output, or Out.oom
def Out.keeps(ok: Bool, r: Maybe<&2, Source.Obs>, w: Maybe<&2, List<&2, Nat>>) -> Bool:
  match ok r w:
    case True{} Some{o} Some{x}:
      Out.is(x, o)
    case True{} Some{o} None{}:
      False{}
    case _ _ _:
      True{}

# when ok: w is no output, Out.oom, or the output of the result r
def Out.adds_none(ok: Bool, w: Maybe<&2, List<&2, Nat>>, r: Maybe<&2, Source.Obs>) -> Bool:
  match ok w r:
    case True{} Some{x} Some{o}:
      Out.is(x, o)
    case True{} Some{x} None{}:
      Source.Name.is_eq(x, Out.oom())
    case _ _ _:
      True{}

# Laws
# ====

# the module for the source src
law compile:
  for src: List<&2, Nat>
  Wasm.Module

# for a source, an input, the pages and a fuel n of the source: a fuel of the
# module
law fuel_out:
  for src: List<&2, Nat>
  for input: Maybe<&2, List<&2, Nat>>
  for pages: Nat
  for n: Nat
  Nat

# for a source, an input, the pages and a fuel n of the module: a fuel of the
# source
law fuel_src:
  for src: List<&2, Nat>
  for input: Maybe<&2, List<&2, Nat>>
  for pages: Nat
  for n: Nat
  Nat

# The module gives each result that the source gives, or Out.oom.
law keeps_results:
  for src: List<&2, Nat>
  for input: Maybe<&2, List<&2, Nat>>
  for pages: Nat
  for n: Nat
  {Out.keeps(Out.fits(src, pages, input), Source.run(n, src, input),
    Wasm.Wasm.run(pages, fuel_out(src, input, pages, n), compile(src), input)) == True{} : Bool}

# The module gives no result that the source does not give: each output that
# is not Out.oom is the output of a result of the source.
law adds_no_results:
  for src: List<&2, Nat>
  for input: Maybe<&2, List<&2, Nat>>
  for pages: Nat
  for n: Nat
  {Out.adds_none(Out.fits(src, pages, input), Wasm.Wasm.run(pages, n, compile(src), input),
    Source.run(fuel_src(src, input, pages, n), src, input)) == True{} : Bool}
