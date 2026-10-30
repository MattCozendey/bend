import Base
import ../wasm/impl.bend as Wasm

# Imp
# ===
#
# A small structured language, and its translation to the WASM meaning. The
# run time of the compiler is Imp code, so that no proof after this module
# reads WASM. Its values are i32s, in locals and in the memory of
# Wasm.Wasm.run. A loop runs its body again and again; break l leaves the
# l-th loop around it (0: the innermost).
#
# Its meaning computes with the defs of the WASM meaning, so the two agree on
# each operation by their definitions. A run's fuel n bounds the passes of
# each loop. A trap, a break out of all loops and an empty fuel give none.

# Types
# =====

type Exp is Data:
  Exp.const{v: U32}
  Exp.get{i: Nat}
  Exp.bin{o: Wasm.Bin, a: Exp, b: Exp}
  Exp.eqz{a: Exp}
  Exp.load{off: U32, a: Exp}
  Exp.load8{off: U32, a: Exp}

type Stm is Data:
  Stm.skip{}
  Stm.set{i: Nat, e: Exp}
  Stm.store{off: U32, a: Exp, v: Exp}
  Stm.store8{off: U32, a: Exp, v: Exp}
  Stm.seq{a: Stm, b: Stm}
  Stm.if{c: Exp, a: Stm, b: Stm}
  Stm.loop{body: Stm}
  Stm.break{l: Nat}
  Stm.trap{}

# a program: its number of locals, its body, and the value that it returns
type Prog is Data:
  Prog{locals: Nat, body: Stm, ret: Exp}

# the end of a statement: it went on, it broke out of a loop, or it trapped
type Res is Data:
  Res.next{ls: List<&2, U32>, mem: Wasm.Mem}
  Res.brk{l: Nat, ls: List<&2, U32>, mem: Wasm.Mem}
  Res.trap{}

# Expressions
# ===========

def Exp.eval.bin(o: Wasm.Bin, ma: Maybe<&2, U32>, mb: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match ma mb:
    case Some{a} Some{b}:
      Some{Wasm.Bin.apply(o, a, b)}
    case _ _:
      None{}

def Exp.eval.at(m: Maybe<&2, U32>, mem: Wasm.Mem, get: U32 -> Wasm.Mem -> U32) -> Maybe<&2, U32>:
  match m:
    case Some{ea}:
      Some{get(ea, mem)}
    case None{}:
      None{}

# a load of n bytes, by get, at a plus off
def Exp.eval.load(ma: Maybe<&2, U32>, off: U32, n: U32, +size: U32, mem: Wasm.Mem,
  get: U32 -> Wasm.Mem -> U32) -> Maybe<&2, U32>:
  match ma:
    case Some{a}:
      Exp.eval.at(Wasm.Mem.addr(a, off, n, size), mem, get)
    case None{}:
      None{}

# the value of e, or none at a trap
def Exp.eval(e: Exp, +size: U32, +ls: List<&2, U32>, +mem: Wasm.Mem) -> Maybe<&2, U32>:
  match e:
    case Exp.const{v}:
      Some{v}
    case Exp.get{i}:
      Wasm.List.at(ls, i)
    case Exp.bin{o, a, b}:
      Exp.eval.bin(o, Exp.eval(a, size, ls, mem), Exp.eval(b, size, ls, mem))
    case Exp.eqz{a}:
      Maybe.map(&2, U32, U32, x => Bool.to_u32(U32.is_eq(x, 0)), Exp.eval(a, size, ls, mem))
    case Exp.load{off, a}:
      Exp.eval.load(Exp.eval(a, size, ls, mem), off, 4, size, mem, x => m => Wasm.Mem.load(x, m))
    case Exp.load8{off, a}:
      Exp.eval.load(Exp.eval(a, size, ls, mem), off, 1, size, mem,
        x => m => U32.from_nat(Wasm.Mem.get_at(x, m)))

# Statements
# ==========

# go after a statement that went on
def Res.then(r: Maybe<&2, Res>, go: List<&2, U32> -> Wasm.Mem -> Maybe<&2, Res>) -> Maybe<&2, Res>:
  match r:
    case Some{Res.next{ls, mem}}:
      go(ls, mem)
    case _:
      r

# go after a pass of a loop's body that went on; a break 0 leaves the loop
def Res.loop(r: Maybe<&2, Res>, go: List<&2, U32> -> Wasm.Mem -> Maybe<&2, Res>) -> Maybe<&2, Res>:
  match r:
    case Some{Res.next{ls, mem}}:
      go(ls, mem)
    case Some{Res.brk{0n, ls, mem}}:
      Some{Res.next{ls, mem}}
    case Some{Res.brk{1n+l, ls, mem}}:
      Some{Res.brk{l, ls, mem}}
    case _:
      r

def Stm.set.of(m: Maybe<&2, List<&2, U32>>, mem: Wasm.Mem) -> Maybe<&2, Res>:
  match m:
    case Some{ls}:
      Some{Res.next{ls, mem}}
    case None{}:
      Some{Res.trap{}}

def Stm.set(mv: Maybe<&2, U32>, i: Nat, ls: List<&2, U32>, mem: Wasm.Mem) -> Maybe<&2, Res>:
  match mv:
    case Some{v}:
      Stm.set.of(Wasm.List.put(ls, i, v), mem)
    case None{}:
      Some{Res.trap{}}

def Stm.store.at(m: Maybe<&2, U32>, v: U32, put: U32 -> Wasm.Mem -> U32 -> Wasm.Mem, ls: List<&2, U32>,
  mem: Wasm.Mem) -> Maybe<&2, Res>:
  match m:
    case Some{ea}:
      Some{Res.next{ls, put(ea, mem, v)}}
    case None{}:
      Some{Res.trap{}}

# a store of n bytes, by put, of v at a plus off
def Stm.store(ma: Maybe<&2, U32>, mv: Maybe<&2, U32>, off: U32, n: U32, +size: U32,
  put: U32 -> Wasm.Mem -> U32 -> Wasm.Mem, ls: List<&2, U32>, mem: Wasm.Mem) -> Maybe<&2, Res>:
  match ma mv:
    case Some{a} Some{v}:
      Stm.store.at(Wasm.Mem.addr(a, off, n, size), v, put, ls, mem)
    case _ _:
      Some{Res.trap{}}

def Stm.if.of(c: Bool, a: Unit -> Maybe<&2, Res>, b: Unit -> Maybe<&2, Res>) -> Maybe<&2, Res>:
  match c:
    case True{}:
      a(Unit{})
    case False{}:
      b(Unit{})

def Stm.if(mc: Maybe<&2, U32>, a: Unit -> Maybe<&2, Res>, b: Unit -> Maybe<&2, Res>) -> Maybe<&2, Res>:
  match mc:
    case Some{c}:
      Stm.if.of(U32.is_ne(c, 0), a, b)
    case None{}:
      Some{Res.trap{}}

# the end of s, from the locals ls and the memory mem, in a memory of size
# bytes; with fuel n, each loop makes at most n passes
def Stm.run(s: Stm, +n: Nat, +size: U32, +ls: List<&2, U32>, +mem: Wasm.Mem) -> Maybe<&2, Res>:
  match s:
    case Stm.skip{}:
      Some{Res.next{ls, mem}}
    case Stm.set{i, e}:
      Stm.set(Exp.eval(e, size, ls, mem), i, ls, mem)
    case Stm.store{off, a, v}:
      Stm.store(Exp.eval(a, size, ls, mem), Exp.eval(v, size, ls, mem), off, 4, size,
        x => m => y => Wasm.Mem.store(x, m, y), ls, mem)
    case Stm.store8{off, a, v}:
      Stm.store(Exp.eval(a, size, ls, mem), Exp.eval(v, size, ls, mem), off, 1, size,
        x => m => y => Wasm.Mem.set_at(x, m, Wasm.U32.low(y)), ls, mem)
    case Stm.seq{a, b}:
      Res.then(Stm.run(a, n, size, ls, mem), ls2 => mem2 => Stm.run(b, n, size, ls2, mem2))
    case Stm.if{c, a, b}:
      Stm.if(Exp.eval(c, size, ls, mem), u => Stm.run(a, n, size, ls, mem), u => Stm.run(b, n, size, ls, mem))
    case Stm.loop{+body}:
      match n:
        case 0n:
          None{}
        case 1n+p:
          Res.loop(Stm.run(body, p, size, ls, mem),
            ls2 => mem2 => Stm.run(Stm.loop{body}, p, size, ls2, mem2))
    case Stm.break{l}:
      Some{Res.brk{l, ls, mem}}
    case Stm.trap{}:
      Some{Res.trap{}}

# Programs
# ========

def Prog.ret.of(m: Maybe<&2, U32>, mem: Wasm.Mem) -> Maybe<&2, Wasm.Halted>:
  match m:
    case Some{v}:
      Some{Wasm.Halted{v, mem}}
    case None{}:
      None{}

# the value that a program returns, when its body went on
def Prog.ret(r: Maybe<&2, Res>, ret: Exp, +size: U32) -> Maybe<&2, Wasm.Halted>:
  match r:
    case Some{Res.next{+ls, +mem}}:
      Prog.ret.of(Exp.eval(ret, size, ls, mem), mem)
    case _:
      None{}

def Imp.run.of(ok: Bool, n: Nat, +size: U32, p: Prog, input: Maybe<&2, List<&2, Nat>>) ->
  Maybe<&2, List<&2, Nat>>:
  match ok:
    case True{}:
      match p:
        case Prog{k, body, ret}:
          Wasm.Halted.output(
            Prog.ret(Stm.run(body, n, size, Wasm.Locals.zero(k), Wasm.Input.mem(input)), ret, size), size)
    case False{}:
      None{}

# the output of p for the input, as Wasm.Wasm.run gives it for a module: in a
# memory of the given number of pages, with fuel n
def Imp.run(+pages: Nat, n: Nat, p: Prog, +input: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Nat>> :
  Imp.run.of(Wasm.Wasm.fits(pages, input), n, Wasm.Wasm.size(pages), p, input)

# Translation
# ===========

def Exp.code(e: Exp, k: Wasm.Code) -> Wasm.Code:
  match e:
    case Exp.const{v}:
      Wasm.Code.const{v, k}
    case Exp.get{i}:
      Wasm.Code.get{i, k}
    case Exp.bin{o, a, b}:
      Exp.code(a, Exp.code(b, Wasm.Code.bin{o, k}))
    case Exp.eqz{a}:
      Exp.code(a, Wasm.Code.eqz{k})
    case Exp.load{off, a}:
      Exp.code(a, Wasm.Code.load{off, k})
    case Exp.load8{off, a}:
      Exp.code(a, Wasm.Code.load8_u{off, k})

# ds with d more blocks around it
def Ds.up(ds: List<&2, Nat>, +d: Nat) -> List<&2, Nat>:
  match ds:
    case Nil{}:
      []
    case Con{x, rest}:
      Con{Nat.add(x, d), Ds.up(rest, d)}

# a branch to the block at depth m, or a trap when there is no such loop
def Stm.break.code(m: Maybe<&2, Nat>, k: Wasm.Code) -> Wasm.Code:
  match m:
    case Some{d}:
      Wasm.Code.br{d, k}
    case None{}:
      Wasm.Code.unreachable{k}

# the code of s, then k. ds: for each loop around s, the innermost first, the
# depth of the block that break leaves it by.
def Stm.code(s: Stm, +ds: List<&2, Nat>, k: Wasm.Code) -> Wasm.Code:
  match s:
    case Stm.skip{}:
      k
    case Stm.set{i, e}:
      Exp.code(e, Wasm.Code.set{i, k})
    case Stm.store{off, a, v}:
      Exp.code(a, Exp.code(v, Wasm.Code.store{off, k}))
    case Stm.store8{off, a, v}:
      Exp.code(a, Exp.code(v, Wasm.Code.store8{off, k}))
    case Stm.seq{a, b}:
      Stm.code(a, ds, Stm.code(b, ds, k))
    case Stm.if{c, a, b}:
      Wasm.Code.block{
        Wasm.Code.block{
          Exp.code(c, Wasm.Code.br_if{0n, Stm.code(b, Ds.up(ds, 2n), Wasm.Code.br{1n, Wasm.Code.end{}})}),
          Stm.code(a, Ds.up(ds, 1n), Wasm.Code.end{})},
        k}
    case Stm.loop{+body}:
      Wasm.Code.block{
        Wasm.Code.loop{Stm.code(body, Con{1n, Ds.up(ds, 2n)}, Wasm.Code.br{0n, Wasm.Code.end{}}),
          Wasm.Code.end{}},
        k}
    case Stm.break{l}:
      Stm.break.code(List.get(&2, Nat, ds, l), k)
    case Stm.trap{}:
      Wasm.Code.unreachable{k}

# the module of p
def Imp.compile(p: Prog) -> Wasm.Module:
  match p:
    case Prog{k, body, ret}:
      Wasm.Module{k, Stm.code(body, [], Exp.code(ret, Wasm.Code.end{}))}
