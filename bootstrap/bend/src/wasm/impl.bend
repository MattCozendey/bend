import Base

# Wasm
# ====
#
# The meaning of the WebAssembly that the compiler in Bend writes: a small part
# of WebAssembly 2.0, copied from its spec (Execution, and Binary Format for
# Wasm.encode). A person reviews it against the spec. The part:
# - a module has one function, of type [] -> [i32], with n i32 locals. It
#   imports its memory as env.memory, of at least 1 page, and exports itself as
#   main;
# - its instructions are those of Code. Each block and loop has the empty type.
# Wasm.run runs a module by the protocol of the host (harness/wasm.ts): the
# memory has some pages, and holds the length of the input (4 bytes, the low
# byte first) at 0 and its bytes at 4, or 0xffffffff at 0 for no input. main
# returns an address p; the output is the length at p and the bytes after it.
#
# The meaning has no validation: an engine refuses an invalid module, so it
# gives no result where this meaning may give one.

# Types
# =====

# the binary operations, each on two i32 values a and b
type Bin is Data:
  Bin.add{}
  Bin.sub{}
  Bin.and{}
  Bin.or{}
  Bin.xor{}
  Bin.shl{}
  Bin.shr_u{}
  Bin.eq{}
  Bin.ne{}
  Bin.lt_u{}
  Bin.ge_u{}

# the code of a body: each instruction holds the code k after it, and a block
# or a loop holds its own body too
type Code is Data:
  Code.end{}
  Code.const{v: U32, k: Code}
  Code.bin{o: Bin, k: Code}
  Code.eqz{k: Code}
  Code.load{off: U32, k: Code}
  Code.load8_u{off: U32, k: Code}
  Code.store{off: U32, k: Code}
  Code.store8{off: U32, k: Code}
  Code.size{k: Code}
  Code.get{i: Nat, k: Code}
  Code.set{i: Nat, k: Code}
  Code.tee{i: Nat, k: Code}
  Code.drop{k: Code}
  Code.block{body: Code, k: Code}
  Code.loop{body: Code, k: Code}
  Code.br{l: Nat, k: Code}
  Code.br_if{l: Nat, k: Code}
  Code.br_table{ls: List<&2, Nat>, d: Nat, k: Code}
  Code.unreachable{k: Code}

type Module is Data:
  Module{locals: Nat, body: Code}

# a memory: a tree on the bits of an address, the lowest first; a byte at each
# leaf, and 0 where no byte was stored
type Mem is Data:
  Mem.zero{}
  Mem.byte{b: Nat}
  Mem.node{lo: Mem, hi: Mem}

# a label: the code that a branch to it runs, the code after its end, and the
# operand stack at its start
type Label is Data:
  Label{br: Code, end: Code, stack: List<&2, U32>}

# the state of a run: the code to run, the operand stack (its top first), the
# locals, the memory and the labels (the innermost first)
type Frame is Data:
  Frame{code: Code, stack: List<&2, U32>, locals: List<&2, U32>, mem: Mem,
    labels: List<&2, Label>}

# the end of a run: the value that main returned, and the memory
type Halted is Data:
  Halted{v: U32, mem: Mem}

type Step is Data:
  Step.next{f: Frame}
  Step.done{d: Halted}
  Step.trap{}

# Words
# =====

# the bits of a word, the lowest first
def Word.bits(n: Nat, w: Word(n)) -> List<&2, Bool>:
  match n:
    case 0n:
      []
    case 1n+p:
      match w:
        case WCon{b, t}:
          Con{b, Word.bits(p, t)}

def U32.bits(a: U32) -> List<&2, Bool>:
  match a:
    case U32{w}:
      Word.bits(32n, w)

# the low byte of a
def U32.low(a: U32) -> Nat:
  U32.to_nat(U32.and(a, 255))

# Memory
# ======

def Mem.child(bit: Bool, m: Mem) -> Mem:
  match m:
    case Mem.node{lo, hi}:
      Bool.pick(Mem, bit, hi, lo)
    case _:
      Mem.zero{}

def Mem.leaf(m: Mem) -> Nat:
  match m:
    case Mem.byte{b}:
      b
    case _:
      0n

# the byte of m at the address whose bits are bs
def Mem.get(bs: List<&2, Bool>, m: Mem) -> Nat:
  match bs:
    case Nil{}:
      Mem.leaf(m)
    case Con{bit, rest}:
      Mem.get(rest, Mem.child(bit, m))

# m with its child at bit set to c
def Mem.put(bit: Bool, +m: Mem, +c: Mem) -> Mem:
  Bool.pick(Mem, bit, Mem.node{Mem.child(False{}, m), c}, Mem.node{c, Mem.child(True{}, m)})

# m with the byte b at the address whose bits are bs
def Mem.set(bs: List<&2, Bool>, +m: Mem, b: Nat) -> Mem:
  match bs:
    case Nil{}:
      Mem.byte{b}
    case Con{+bit, rest}:
      Mem.put(bit, m, Mem.set(rest, Mem.child(bit, m), b))

def Mem.get_at(a: U32, m: Mem) -> Nat:
  Mem.get(U32.bits(a), m)

def Mem.set_at(a: U32, m: Mem, b: Nat) -> Mem:
  Mem.set(U32.bits(a), m, b)

# the i32 at a, the low byte first
def Mem.load(+a: U32, +m: Mem) -> U32:
  U32.or(U32.or(U32.from_nat(Mem.get_at(a, m)), U32.shln(U32.from_nat(Mem.get_at(U32.add(a, 1), m)), 8n)),
    U32.or(U32.shln(U32.from_nat(Mem.get_at(U32.add(a, 2), m)), 16n),
      U32.shln(U32.from_nat(Mem.get_at(U32.add(a, 3), m)), 24n)))

# m with the i32 v at a, the low byte first
def Mem.store(+a: U32, m: Mem, +v: U32) -> Mem:
  Mem.set_at(U32.add(a, 3),
    Mem.set_at(U32.add(a, 2),
      Mem.set_at(U32.add(a, 1), Mem.set_at(a, m, U32.low(v)), U32.low(U32.shrn(v, 8n))),
      U32.low(U32.shrn(v, 16n))),
    U32.low(U32.shrn(v, 24n)))

# the start of an access of n bytes at a + off, when it ends within size bytes
def Mem.addr(+a: U32, off: U32, +n: U32, +size: U32) -> Maybe<&2, U32>:
  +ea = U32.add(a, off)
  +e = U32.add(ea, n)
  Bool.pick(Maybe<&2, U32>,
    Bool.not(U32.is_lt(ea, a)) && Bool.not(U32.is_lt(e, ea)) && U32.is_le(e, size),
    Some{ea}, None{})

# Lists
# =====

# the item of xs at i, or none
def List.at(xs: List<&2, U32>, i: Nat) -> Maybe<&2, U32>:
  match xs i:
    case Con{x, rest} 0n:
      Some{x}
    case Con{x, rest} 1n+j:
      List.at(rest, j)
    case _ _:
      None{}

def List.put.con(x: U32, m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case Some{rest}:
      Some{Con{x, rest}}
    case None{}:
      None{}

# xs with v at i, or none when it has no item at i
def List.put(xs: List<&2, U32>, i: Nat, v: U32) -> Maybe<&2, List<&2, U32>>:
  match xs i:
    case Con{x, rest} 0n:
      Some{Con{v, rest}}
    case Con{x, rest} 1n+j:
      List.put.con(x, List.put(rest, j, v))
    case _ _:
      None{}

# the label of br_table: the one at i in ls, or d
def List.at_u32(ls: List<&2, Nat>, +i: U32, d: Nat) -> Nat:
  match ls:
    case Nil{}:
      d
    case Con{l, rest}:
      Bool.pick(Nat, U32.is_eq(i, 0), l, List.at_u32(rest, U32.sub(i, 1), d))

# Steps
# =====

def Bin.apply(o: Bin, +a: U32, +b: U32) -> U32:
  match o:
    case Bin.add{}:
      U32.add(a, b)
    case Bin.sub{}:
      U32.sub(a, b)
    case Bin.and{}:
      U32.and(a, b)
    case Bin.or{}:
      U32.or(a, b)
    case Bin.xor{}:
      U32.xor(a, b)
    case Bin.shl{}:
      U32.shln(a, U32.to_nat(U32.and(b, 31)))
    case Bin.shr_u{}:
      U32.shrn(a, U32.to_nat(U32.and(b, 31)))
    case Bin.eq{}:
      Bool.to_u32(U32.is_eq(a, b))
    case Bin.ne{}:
      Bool.to_u32(U32.is_ne(a, b))
    case Bin.lt_u{}:
      Bool.to_u32(U32.is_lt(a, b))
    case Bin.ge_u{}:
      Bool.to_u32(U32.is_ge(a, b))

# the next frame, with the code k and the stack m; a trap when m is none
def Frame.with(m: Maybe<&2, List<&2, U32>>, k: Code, locals: List<&2, U32>, mem: Mem,
  labels: List<&2, Label>) -> Step:
  match m:
    case Some{s}:
      Step.next{Frame{k, s, locals, mem, labels}}
    case None{}:
      Step.trap{}

# the stack after a binary operation on its top two values
def Step.bin(o: Bin, s: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match s:
    case Con{b, Con{a, rest}}:
      Some{Con{Bin.apply(o, a, b), rest}}
    case _:
      None{}

def Step.eqz(s: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match s:
    case Con{a, rest}:
      Some{Con{Bool.to_u32(U32.is_eq(a, 0)), rest}}
    case _:
      None{}

def Step.load.at(m: Maybe<&2, U32>, mem: Mem, get: U32 -> Mem -> U32, rest: List<&2, U32>) ->
  Maybe<&2, List<&2, U32>>:
  match m:
    case Some{ea}:
      Some{Con{get(ea, mem), rest}}
    case None{}:
      None{}

# a load of n bytes, by get, at the top of s plus off
def Step.load(off: U32, n: U32, +size: U32, s: List<&2, U32>, +mem: Mem,
  get: U32 -> Mem -> U32) -> Maybe<&2, List<&2, U32>>:
  match s:
    case Con{a, rest}:
      Step.load.at(Mem.addr(a, off, n, size), mem, get, rest)
    case _:
      None{}

def Step.store.at(m: Maybe<&2, U32>, v: U32, put: U32 -> Mem -> U32 -> Mem, k: Code,
  s: List<&2, U32>, locals: List<&2, U32>, mem: Mem, labels: List<&2, Label>) -> Step:
  match m:
    case Some{ea}:
      Step.next{Frame{k, s, locals, put(ea, mem, v), labels}}
    case None{}:
      Step.trap{}

# a store of n bytes, by put, of the top of s at the value below it plus off
def Step.store(off: U32, n: U32, +size: U32, s: List<&2, U32>, k: Code, locals: List<&2, U32>,
  mem: Mem, labels: List<&2, Label>, put: U32 -> Mem -> U32 -> Mem) -> Step:
  match s:
    case Con{v, Con{a, rest}}:
      Step.store.at(Mem.addr(a, off, n, size), v, put, k, rest, locals, mem, labels)
    case _:
      Step.trap{}

# a branch to the label at l: its code, with the stack at its start
def Step.br(l: Nat, labels: List<&2, Label>, locals: List<&2, U32>, mem: Mem) -> Step:
  match l labels:
    case 0n Con{Label{br, end, s}, rest}:
      Step.next{Frame{br, s, locals, mem, rest}}
    case 1n+j Con{x, rest}:
      Step.br(j, rest, locals, mem)
    case _ _:
      Step.trap{}

# a branch when c is not 0
def Step.br_if.of(c: Bool, l: Nat, k: Code, s: List<&2, U32>, locals: List<&2, U32>, mem: Mem,
  labels: List<&2, Label>) -> Step:
  match c:
    case True{}:
      Step.br(l, labels, locals, mem)
    case False{}:
      Step.next{Frame{k, s, locals, mem, labels}}

# the end of a body: the code after the innermost block, or the end of main
def Step.end(labels: List<&2, Label>, s: List<&2, U32>, locals: List<&2, U32>, mem: Mem) -> Step:
  match labels s:
    case Con{Label{br, end, ls}, rest} _:
      Step.next{Frame{end, ls, locals, mem, rest}}
    case Nil{} Con{v, _}:
      Step.done{Halted{v, mem}}
    case Nil{} Nil{}:
      Step.trap{}

def Step.set.of(m: Maybe<&2, List<&2, U32>>, k: Code, s: List<&2, U32>, mem: Mem,
  labels: List<&2, Label>) -> Step:
  match m:
    case Some{locals}:
      Step.next{Frame{k, s, locals, mem, labels}}
    case None{}:
      Step.trap{}

# the local i on top of s, when it is set to the top of s (tee keeps it there)
def Step.set(tee: Bool, i: Nat, k: Code, s: List<&2, U32>, locals: List<&2, U32>, mem: Mem,
  labels: List<&2, Label>) -> Step:
  match s:
    case Con{+v, +rest}:
      Step.set.of(List.put(locals, i, v), k, Bool.pick(List<&2, U32>, tee, Con{v, rest}, rest), mem,
        labels)
    case Nil{}:
      Step.trap{}

# the stack after local.get pushed the local m
def Step.get(m: Maybe<&2, U32>, s: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case Some{v}:
      Some{Con{v, s}}
    case None{}:
      None{}

def Step.drop(s: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match s:
    case Con{v, rest}:
      Some{rest}
    case Nil{}:
      None{}

# one step of f, in a memory of size bytes
def Step.of(+size: U32, f: Frame) -> Step:
  match f:
    case Frame{Code.end{}, s, locals, mem, labels}:
      Step.end(labels, s, locals, mem)
    case Frame{Code.const{v, k}, s, locals, mem, labels}:
      Step.next{Frame{k, Con{v, s}, locals, mem, labels}}
    case Frame{Code.bin{o, k}, s, locals, mem, labels}:
      Frame.with(Step.bin(o, s), k, locals, mem, labels)
    case Frame{Code.eqz{k}, s, locals, mem, labels}:
      Frame.with(Step.eqz(s), k, locals, mem, labels)
    case Frame{Code.load{off, k}, s, locals, +mem, labels}:
      Frame.with(Step.load(off, 4, size, s, mem, a => m => Mem.load(a, m)), k, locals, mem, labels)
    case Frame{Code.load8_u{off, k}, s, locals, +mem, labels}:
      Frame.with(Step.load(off, 1, size, s, mem, a => m => U32.from_nat(Mem.get_at(a, m))), k, locals,
        mem, labels)
    case Frame{Code.store{off, k}, s, locals, mem, labels}:
      Step.store(off, 4, size, s, k, locals, mem, labels, a => m => v => Mem.store(a, m, v))
    case Frame{Code.store8{off, k}, s, locals, mem, labels}:
      Step.store(off, 1, size, s, k, locals, mem, labels, a => m => v => Mem.set_at(a, m, U32.low(v)))
    case Frame{Code.size{k}, s, locals, mem, labels}:
      Step.next{Frame{k, Con{U32.shrn(size, 16n), s}, locals, mem, labels}}
    case Frame{Code.get{i, k}, s, +locals, mem, labels}:
      Frame.with(Step.get(List.at(locals, i), s), k, locals, mem, labels)
    case Frame{Code.set{i, k}, s, locals, mem, labels}:
      Step.set(False{}, i, k, s, locals, mem, labels)
    case Frame{Code.tee{i, k}, s, locals, mem, labels}:
      Step.set(True{}, i, k, s, locals, mem, labels)
    case Frame{Code.drop{k}, s, locals, mem, labels}:
      Frame.with(Step.drop(s), k, locals, mem, labels)
    case Frame{Code.block{body, +k}, +s, locals, mem, labels}:
      Step.next{Frame{body, s, locals, mem, Con{Label{k, k, s}, labels}}}
    case Frame{Code.loop{+body, +k}, +s, locals, mem, labels}:
      Step.next{Frame{body, s, locals, mem, Con{Label{Code.loop{body, k}, k, s}, labels}}}
    case Frame{Code.br{l, k}, s, locals, mem, labels}:
      Step.br(l, labels, locals, mem)
    case Frame{Code.br_if{l, k}, Con{c, s}, locals, mem, labels}:
      Step.br_if.of(U32.is_ne(c, 0), l, k, s, locals, mem, labels)
    case Frame{Code.br_table{ls, d, k}, Con{i, s}, locals, mem, labels}:
      Step.br(List.at_u32(ls, i, d), labels, locals, mem)
    case _:
      Step.trap{}


# Runs
# ====

def Step.then(s: Step, go: Frame -> Maybe<&2, Halted>) -> Maybe<&2, Halted>:
  match s:
    case Step.next{f}:
      go(f)
    case Step.done{d}:
      Some{d}
    case Step.trap{}:
      None{}

# the end of f after at most n steps, or none at a trap or when n runs out
def Frame.run(n: Nat, +size: U32, f: Frame) -> Maybe<&2, Halted>:
  match n:
    case 0n:
      None{}
    case 1n+m:
      Step.then(Step.of(size, f), g => Frame.run(m, size, g))

# zero locals
def Locals.zero(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      []
    case 1n+p:
      Con{0, Locals.zero(p)}

# m with the bytes bs from a on
def Mem.bytes(bs: List<&2, Nat>, +a: U32, m: Mem) -> Mem:
  match bs:
    case Nil{}:
      m
    case Con{b, rest}:
      Mem.bytes(rest, U32.add(a, 1), Mem.set_at(a, m, b))

# the n bytes of m from a on
def Mem.read(n: Nat, +a: U32, +m: Mem) -> List<&2, Nat>:
  match n:
    case 0n:
      []
    case 1n+p:
      Con{Mem.get_at(a, m), Mem.read(p, U32.add(a, 1), m)}

# the n bytes of m at the start ok of the output, when it fits
def Halted.output.at(ok: Maybe<&2, U32>, n: U32, m: Mem) -> Maybe<&2, List<&2, Nat>>:
  match ok:
    case Some{a}:
      Some{Mem.read(U32.to_nat(n), a, m)}
    case None{}:
      None{}

# the output at p: its length at p and its bytes after it, when they fit
def Halted.output.of(+p: U32, +m: Mem, +size: U32, ok: Maybe<&2, U32>) -> Maybe<&2, List<&2, Nat>>:
  match ok:
    case Some{x}:
      +n = Mem.load(p, m)
      Halted.output.at(Mem.addr(p, 4, n, size), n, m)
    case None{}:
      None{}

def Halted.output(d: Maybe<&2, Halted>, +size: U32) -> Maybe<&2, List<&2, Nat>>:
  match d:
    case Some{Halted{+p, +m}}:
      Halted.output.of(p, m, size, Mem.addr(p, 0, 4, size))
    case None{}:
      None{}

# the memory at the start of a run: the input's length and bytes, or
# 0xffffffff for no input
def Input.mem(input: Maybe<&2, List<&2, Nat>>) -> Mem:
  match input:
    case Some{+xs}:
      Mem.bytes(xs, 4, Mem.store(0, Mem.zero{}, U32.from_nat(List.length(&2, Nat, xs))))
    case None{}:
      Mem.store(0, Mem.zero{}, 4294967295)

def Frame.start(m: Module, input: Maybe<&2, List<&2, Nat>>) -> Frame:
  match m:
    case Module{n, body}:
      Frame{body, [], Locals.zero(n), Input.mem(input), []}

# whether n is at most limit; it takes at most limit + 1 steps
def Nat.at_most(n: Nat, +limit: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      U32.is_ne(limit, 0) && Nat.at_most(p, U32.sub(limit, 1))

# whether each item of xs is a byte
def Bytes.is(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, rest}:
      Nat.at_most(x, 255) && Bytes.is(rest)

# the bytes in a memory of the given number of pages
def Wasm.size(pages: Nat) -> U32:
  U32.shln(U32.from_nat(pages), 16n)

def Input.fits(input: Maybe<&2, List<&2, Nat>>, limit: U32) -> Bool:
  match input:
    case Some{+xs}:
      Bytes.is(xs) && Nat.at_most(List.length(&2, Nat, xs), limit)
    case None{}:
      True{}

# whether the host can run a module: the pages are 1 to 65535, and the input
# is bytes that fit after its length
def Wasm.fits(+pages: Nat, input: Maybe<&2, List<&2, Nat>>) -> Bool:
  Bool.not(Nat.is_eq(pages, 0n)) && Nat.at_most(pages, 65535) &&
    Input.fits(input, U32.sub(Wasm.size(pages), 4))

def Wasm.run.of(ok: Bool, n: Nat, +size: U32, m: Module, input: Maybe<&2, List<&2, Nat>>) ->
  Maybe<&2, List<&2, Nat>>:
  match ok:
    case True{}:
      Halted.output(Frame.run(n, size, Frame.start(m, input)), size)
    case False{}:
      None{}

# the output of the module m for the input (none: no input), with at most n
# steps, in a memory of the given number of pages, or none: at a trap, when n
# runs out, when the output does not fit, or when not Wasm.fits
def Wasm.run(+pages: Nat, n: Nat, m: Module, +input: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Nat>>:
  Wasm.run.of(Wasm.fits(pages, input), n, Wasm.size(pages), m, input)

# Binary format
# =============

def Leb.nat.of(q: Nat, r: Nat, go: Nat -> List<&2, Nat>) -> List<&2, Nat>:
  match q:
    case 0n:
      [r]
    case 1n+p:
      Con{Nat.add(r, 128n), go(1n+p)}

# n in unsigned LEB128; f bounds its bytes
def Leb.nat.go(f: Nat, +n: Nat) -> List<&2, Nat>:
  match f:
    case 0n:
      []
    case 1n+g:
      Leb.nat.of(Nat.div(n, 128n), Nat.mod(n, 128n), m => Leb.nat.go(g, m))

# n in unsigned LEB128
def Leb.nat(+n: Nat) -> List<&2, Nat>:
  Leb.nat.go(1n+n, n)

def Leb.u32.of(last: Bool, b: Nat, s: U32, go: U32 -> List<&2, Nat>) -> List<&2, Nat>:
  match last:
    case True{}:
      [b]
    case False{}:
      Con{Nat.add(b, 128n), go(s)}

# v in unsigned LEB128; f bounds its bytes
def Leb.u32.go(f: Nat, +v: U32) -> List<&2, Nat>:
  match f:
    case 0n:
      []
    case 1n+g:
      +s = U32.shrn(v, 7n)
      Leb.u32.of(U32.is_eq(s, 0), U32.to_nat(U32.and(v, 127)), s, w => Leb.u32.go(g, w))

# v >> 7, the sign bit copied in
def U32.asr7(+v: U32) -> U32:
  U32.or(U32.shrn(v, 7n), Bool.pick(U32, U32.is_ne(U32.and(v, 2147483648), 0), 4261412864, 0))

# v in signed LEB128, as an i32; f bounds its bytes
def Leb.i32.go(f: Nat, +v: U32) -> List<&2, Nat>:
  match f:
    case 0n:
      []
    case 1n+g:
      +s = U32.asr7(v)
      +sign = U32.is_ne(U32.and(v, 64), 0)
      Leb.u32.of((U32.is_eq(s, 0) && Bool.not(sign)) || (U32.is_eq(s, 4294967295) && sign),
        U32.to_nat(U32.and(v, 127)), s, w => Leb.i32.go(g, w))

# the labels of br_table, each in LEB128
def Leb.nats(ls: List<&2, Nat>) -> List<&2, Nat>:
  match ls:
    case Nil{}:
      []
    case Con{l, rest}:
      List.append(&2, Nat, Leb.nat(l), Leb.nats(rest))

# the opcode of a binary operation
def Bin.opcode(o: Bin) -> Nat:
  match o:
    case Bin.add{}:
      106n
    case Bin.sub{}:
      107n
    case Bin.and{}:
      113n
    case Bin.or{}:
      114n
    case Bin.xor{}:
      115n
    case Bin.shl{}:
      116n
    case Bin.shr_u{}:
      118n
    case Bin.eq{}:
      70n
    case Bin.ne{}:
      71n
    case Bin.lt_u{}:
      73n
    case Bin.ge_u{}:
      79n

# an instruction with an immediate i, then the code ks
def Code.with(op: List<&2, Nat>, i: List<&2, Nat>, ks: List<&2, Nat>) -> List<&2, Nat>:
  List.append(&2, Nat, op, List.append(&2, Nat, i, ks))

# the bytes of the code c; each body ends in 0x0b
def Code.bytes(c: Code) -> List<&2, Nat>:
  match c:
    case Code.end{}:
      []
    case Code.const{v, k}:
      Code.with([65n], Leb.i32.go(5n, v), Code.bytes(k))
    case Code.bin{o, k}:
      Con{Bin.opcode(o), Code.bytes(k)}
    case Code.eqz{k}:
      Con{69n, Code.bytes(k)}
    case Code.load{off, k}:
      Code.with([40n, 2n], Leb.u32.go(5n, off), Code.bytes(k))
    case Code.load8_u{off, k}:
      Code.with([45n, 0n], Leb.u32.go(5n, off), Code.bytes(k))
    case Code.store{off, k}:
      Code.with([54n, 2n], Leb.u32.go(5n, off), Code.bytes(k))
    case Code.store8{off, k}:
      Code.with([58n, 0n], Leb.u32.go(5n, off), Code.bytes(k))
    case Code.size{k}:
      Code.with([63n], [0n], Code.bytes(k))
    case Code.get{i, k}:
      Code.with([32n], Leb.nat(i), Code.bytes(k))
    case Code.set{i, k}:
      Code.with([33n], Leb.nat(i), Code.bytes(k))
    case Code.tee{i, k}:
      Code.with([34n], Leb.nat(i), Code.bytes(k))
    case Code.drop{k}:
      Con{26n, Code.bytes(k)}
    case Code.block{body, k}:
      Code.with([2n, 64n], List.append(&2, Nat, Code.bytes(body), [11n]), Code.bytes(k))
    case Code.loop{body, k}:
      Code.with([3n, 64n], List.append(&2, Nat, Code.bytes(body), [11n]), Code.bytes(k))
    case Code.br{l, k}:
      Code.with([12n], Leb.nat(l), Code.bytes(k))
    case Code.br_if{l, k}:
      Code.with([13n], Leb.nat(l), Code.bytes(k))
    case Code.br_table{+ls, d, k}:
      Code.with([14n], List.append(&2, Nat, Leb.nat(List.length(&2, Nat, ls)),
        List.append(&2, Nat, Leb.nats(ls), Leb.nat(d))), Code.bytes(k))
    case Code.unreachable{k}:
      Con{0n, Code.bytes(k)}

# the bytes c after their size
def Wasm.sized(+c: List<&2, Nat>) -> List<&2, Nat>:
  List.append(&2, Nat, Leb.nat(List.length(&2, Nat, c)), c)

# a section: its id, then its content after its size
def Wasm.section(id: Nat, c: List<&2, Nat>) -> List<&2, Nat>:
  Con{id, Wasm.sized(c)}

# the local declarations of n locals of type i32
def Wasm.locals(n: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      [0n]
    case 1n+p:
      Con{1n, List.append(&2, Nat, Leb.nat(1n+p), [127n])}

# the code section of one function with n locals and the body c
def Wasm.code(n: Nat, c: Code) -> List<&2, Nat>:
  Wasm.section(10n, Con{1n, Wasm.sized(List.append(&2, Nat, Wasm.locals(n),
    List.append(&2, Nat, Code.bytes(c), [11n])))})

# the binary module of m
def Wasm.encode(m: Module) -> List<&2, Nat>:
  match m:
    case Module{n, body}:
      List.append(&2, Nat,
        # the magic \0asm and version 1
        [0n, 97n, 115n, 109n, 1n, 0n, 0n, 0n,
          # the type section: one type, [] -> [i32]
          1n, 5n, 1n, 96n, 0n, 1n, 127n,
          # the import section: env.memory, a memory of at least 1 page
          2n, 15n, 1n, 3n, 101n, 110n, 118n, 6n, 109n, 101n, 109n, 111n, 114n, 121n, 2n, 0n, 1n,
          # the function section: one function, of type 0
          3n, 2n, 1n, 0n,
          # the export section: main, function 0
          7n, 8n, 1n, 4n, 109n, 97n, 105n, 110n, 0n, 0n],
        Wasm.code(n, body))
