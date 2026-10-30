import Base
import ../../bend/src/wasm/impl.bend as Wasm

# The modules of the cases in wasm.json (by the meaning) and wasm_engines.json
# (by bun and node). The input is a mode, a test and the test's data, which is
# also the module's input:
# - mode 0 runs the module by the meaning, in 1 page: 1 and the output, or 0
#   for no result;
# - mode 1 gives the binary module;
# - mode 2 is mode 0 with no input.
# Tests 0 to 11 store an i32 operation of each vector of the data at 4, 8, ...:
# the operations of Ops, then eqz. A vector is a and b, 4 bytes each, the low
# byte first. Tests 12 to 20 are below.

def Ops() -> List<&2, Wasm.Bin>:
  [Wasm.Bin.add{}, Wasm.Bin.sub{}, Wasm.Bin.and{}, Wasm.Bin.or{}, Wasm.Bin.xor{}, Wasm.Bin.shl{},
    Wasm.Bin.shr_u{}, Wasm.Bin.eq{}, Wasm.Bin.ne{}, Wasm.Bin.lt_u{}, Wasm.Bin.ge_u{}]

def Ops.at(os: List<&2, Wasm.Bin>, t: Nat) -> Maybe<&2, Wasm.Bin>:
  match os t:
    case Con{o, rest} 0n:
      Some{o}
    case Con{o, rest} 1n+p:
      Ops.at(rest, p)
    case _ _:
      None{}

def U32.of(b0: Nat, b1: Nat, b2: Nat, b3: Nat) -> U32:
  U32.or(U32.or(U32.from_nat(b0), U32.shln(U32.from_nat(b1), 8n)),
    U32.or(U32.shln(U32.from_nat(b2), 16n), U32.shln(U32.from_nat(b3), 24n)))

# the operation o (eqz when none) on the top of the stack, then k
def Op.code(o: Maybe<&2, Wasm.Bin>, b: U32, k: Wasm.Code) -> Wasm.Code:
  match o:
    case Some{x}:
      Wasm.Code.const{b, Wasm.Code.bin{x, k}}
    case None{}:
      Wasm.Code.eqz{k}

# the output: its length (4 per vector, from 4 up to the address a), then 0
def Op.end(+a: U32) -> Wasm.Code:
  Wasm.Code.const{0, Wasm.Code.const{U32.sub(a, 4), Wasm.Code.store{0, Wasm.Code.const{0, Wasm.Code.end{}}}}}

# the code that stores the operation o of each vector of bs at a, a + 4, ...
def Op.vectors(+o: Maybe<&2, Wasm.Bin>, bs: List<&2, Nat>, +a: U32) -> Wasm.Code:
  match bs:
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{b0, Con{b1, Con{b2, Con{b3, rest}}}}}}}}:
      Wasm.Code.const{a, Wasm.Code.const{U32.of(a0, a1, a2, a3), Op.code(o, U32.of(b0, b1, b2, b3),
        Wasm.Code.store{0, Op.vectors(o, rest, U32.add(a, 4))})}}
    case _:
      Op.end(a)

# the output of the local l, as an i32
def Test.out.i32(l: Nat) -> Wasm.Code:
  Wasm.Code.const{0, Wasm.Code.const{4, Wasm.Code.store{0,
  Wasm.Code.const{0, Wasm.Code.get{l, Wasm.Code.store{4,
  Wasm.Code.const{0, Wasm.Code.end{}}}}}}}}

# test 12: the sum of the input's bytes, as an i32. Locals: 0 = i, 1 = sum,
# 2 = the input's length.
def Test.sum() -> Wasm.Code:
  Wasm.Code.const{0, Wasm.Code.load{0, Wasm.Code.set{2n,
  Wasm.Code.block{
    Wasm.Code.loop{
      Wasm.Code.get{0n, Wasm.Code.get{2n, Wasm.Code.bin{Wasm.Bin.ge_u{}, Wasm.Code.br_if{1n,
      Wasm.Code.get{1n, Wasm.Code.get{0n, Wasm.Code.load8_u{4, Wasm.Code.bin{Wasm.Bin.add{},
      Wasm.Code.set{1n,
      Wasm.Code.get{0n, Wasm.Code.const{1, Wasm.Code.bin{Wasm.Bin.add{}, Wasm.Code.set{0n,
      Wasm.Code.br{0n, Wasm.Code.end{}}}}}}}}}}}}}}},
      Wasm.Code.end{}},
  Test.out.i32(1n)}}}}

# test 13: br_table on the input's first byte x: 10, 11 or 12 for x = 0, 1
# or 2, else 99. Local 0 is the result.
def Test.br_table() -> Wasm.Code:
  Wasm.Code.const{99, Wasm.Code.set{0n,
  Wasm.Code.block{
    Wasm.Code.block{
      Wasm.Code.block{
        Wasm.Code.block{
          Wasm.Code.const{0, Wasm.Code.load8_u{4, Wasm.Code.br_table{[0n, 1n, 2n], 3n, Wasm.Code.end{}}}},
          Wasm.Code.const{10, Wasm.Code.set{0n, Wasm.Code.br{2n, Wasm.Code.end{}}}}},
        Wasm.Code.const{11, Wasm.Code.set{0n, Wasm.Code.br{1n, Wasm.Code.end{}}}}},
      Wasm.Code.const{12, Wasm.Code.set{0n, Wasm.Code.br{0n, Wasm.Code.end{}}}}},
    Test.out.i32(0n)}}}

# test 14: memory, tee and drop. It stores 0x11223344 at 100 and the byte 0xff
# at 104, then outputs 6 bytes: the byte at 101, the i32 at 101, and local 0,
# which tee set to 1.
def Test.memory() -> Wasm.Code:
  Wasm.Code.const{100, Wasm.Code.const{287454020, Wasm.Code.store{0,
  Wasm.Code.const{104, Wasm.Code.const{511, Wasm.Code.store8{0,
  Wasm.Code.const{1, Wasm.Code.tee{0n, Wasm.Code.drop{
  Wasm.Code.const{0, Wasm.Code.const{6, Wasm.Code.store{0,
  Wasm.Code.const{4, Wasm.Code.const{100, Wasm.Code.load8_u{1, Wasm.Code.store8{0,
  Wasm.Code.const{5, Wasm.Code.const{101, Wasm.Code.load{0, Wasm.Code.store{0,
  Wasm.Code.const{9, Wasm.Code.get{0n, Wasm.Code.store8{0,
  Wasm.Code.const{0, Wasm.Code.end{}}}}}}}}}}}}}}}}}}}}}}}}}

# a load of 4 bytes at a plus off, as main's result
def Test.load(a: U32, off: U32) -> Wasm.Code:
  Wasm.Code.const{a, Wasm.Code.load{off, Wasm.Code.end{}}}

# the module of test t on the input xs
def Test.module(t: Nat, xs: List<&2, Nat>) -> Wasm.Module:
  match t:
    case 12n:
      Wasm.Module{3n, Test.sum()}
    case 13n:
      Wasm.Module{1n, Test.br_table()}
    case 14n:
      Wasm.Module{1n, Test.memory()}
    case 15n:
      # test 15: a load that ends past the memory traps
      Wasm.Module{0n, Test.load(65533, 0)}
    case 16n:
      # test 16: a load whose address passes 2^32 traps
      Wasm.Module{0n, Test.load(4294967295, 4)}
    case 17n:
      # test 17: a load that ends at the end of the memory gives 0: the output
      # at 0 is the input's length (0) and no bytes
      Wasm.Module{0n, Test.load(65532, 0)}
    case 18n:
      # test 18: unreachable traps
      Wasm.Module{0n, Wasm.Code.unreachable{Wasm.Code.end{}}}
    case 19n:
      # test 19: the i32 at 0, which holds the input's length or 0xffffffff
      Wasm.Module{1n, Wasm.Code.const{0, Wasm.Code.load{0, Wasm.Code.set{0n, Test.out.i32(0n)}}}}
    case 20n:
      # test 20: memory.size, the number of pages
      Wasm.Module{1n, Wasm.Code.size{Wasm.Code.set{0n, Test.out.i32(0n)}}}
    case _:
      Wasm.Module{0n, Op.vectors(Ops.at(Ops(), t), xs, 4)}

def Test.result(m: Maybe<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match m:
    case Some{bs}:
      Con{1n, bs}
    case None{}:
      [0n]

def main(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Con{0n, Con{+t, +rest}}:
      Test.result(Wasm.Wasm.run(1n, 100000n, Test.module(t, rest), Some{rest}))
    case Con{1n, Con{t, rest}}:
      Wasm.Wasm.encode(Test.module(t, rest))
    case Con{2n, Con{+t, +rest}}:
      Test.result(Wasm.Wasm.run(1n, 100000n, Test.module(t, rest), None{}))
    case _:
      []
