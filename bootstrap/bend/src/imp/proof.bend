import Base
import ../wasm/impl.bend as Wasm
import ./impl.bend as Imp
import ./spec.bend as Spec
import ../shared/impl.bend as Shared

# Imp proofs
# ==========
#
# The proofs of the laws of spec.bend. The fuel of a piece of code is in
# continuation style: Exp.fuel e F is the fuel to run e and then have F left.

# Expressions
# ===========

def Exp.fuel(e: Imp.Exp, F: Nat) -> Nat:
  match e:
    case Imp.Exp.const{v}:
      1n+F
    case Imp.Exp.get{i}:
      1n+F
    case Imp.Exp.bin{o, a, b}:
      Exp.fuel(a, Exp.fuel(b, 1n+F))
    case Imp.Exp.eqz{a}:
      Exp.fuel(a, 1n+F)
    case Imp.Exp.load{off, a}:
      Exp.fuel(a, 1n+F)
    case Imp.Exp.load8{off, a}:
      Exp.fuel(a, 1n+F)
    case Imp.Exp.size{}:
      1n+F

# the run after an expression gave m: its value on top of st, then k
def Exp.after(m: Maybe<&2, U32>, +size: U32, k: Wasm.Code, st: List<&2, U32>, ls: List<&2, U32>,
  mem: Wasm.Mem, L: List<&2, Wasm.Label>, F: Nat) -> Maybe<&2, Wasm.Halted>:
  match m:
    case Some{v}:
      Wasm.Frame.run(F, size, Wasm.Frame{k, Con{v, st}, ls, mem, L})
    case None{}:
      None{}

# The code of e, then k, gives e's value on the stack, or traps when e does.
def Exp.runs(e: Imp.Exp, +size: U32, +ls: List<&2, U32>, +mem: Wasm.Mem, +k: Wasm.Code,
  +st: List<&2, U32>, +L: List<&2, Wasm.Label>, +F: Nat) ->
  {Wasm.Frame.run(Exp.fuel(e, F), size, Wasm.Frame{Imp.Exp.code(e, k), st, ls, mem, L}) ==
    Exp.after(Imp.Exp.eval(e, size, ls, mem), size, k, st, ls, mem, L, F) : Maybe<&2, Wasm.Halted>}:
  match e:
    case Imp.Exp.const{v}:
      {==}
    case Imp.Exp.get{i}:
      Shared.Maybe.elim(U32, Wasm.List.at(ls, i),
        m => {Wasm.Step.then(Wasm.Frame.with(Wasm.Step.get(m, st), k, ls, mem, L),
          g => Wasm.Frame.run(F, size, g)) == Exp.after(m, size, k, st, ls, mem, L, F) :
          Maybe<&2, Wasm.Halted>},
        v => {==}, {==})
    case Imp.Exp.bin{+o, +a, +b}:
      Equal.trans(Maybe<&2, Wasm.Halted>,
        Wasm.Frame.run(Exp.fuel(a, Exp.fuel(b, 1n+F)), size,
          Wasm.Frame{Imp.Exp.code(a, Imp.Exp.code(b, Wasm.Code.bin{o, k})), st, ls, mem, L}),
        Exp.after(Imp.Exp.eval(a, size, ls, mem), size, Imp.Exp.code(b, Wasm.Code.bin{o, k}), st, ls, mem, L,
          Exp.fuel(b, 1n+F)),
        Exp.after(Imp.Exp.eval.bin(o, Imp.Exp.eval(a, size, ls, mem), Imp.Exp.eval(b, size, ls, mem)), size,
          k, st, ls, mem, L, F),
        Exp.runs(a, size, ls, mem, Imp.Exp.code(b, Wasm.Code.bin{o, k}), st, L, Exp.fuel(b, 1n+F)),
        Shared.Maybe.elim(U32, Imp.Exp.eval(a, size, ls, mem),
          ma => {Exp.after(ma, size, Imp.Exp.code(b, Wasm.Code.bin{o, k}), st, ls, mem, L, Exp.fuel(b, 1n+F)) ==
            Exp.after(Imp.Exp.eval.bin(o, ma, Imp.Exp.eval(b, size, ls, mem)), size, k, st, ls, mem, L, F) :
            Maybe<&2, Wasm.Halted>},
          +va => Equal.trans(Maybe<&2, Wasm.Halted>,
            Wasm.Frame.run(Exp.fuel(b, 1n+F), size,
              Wasm.Frame{Imp.Exp.code(b, Wasm.Code.bin{o, k}), Con{va, st}, ls, mem, L}),
            Exp.after(Imp.Exp.eval(b, size, ls, mem), size, Wasm.Code.bin{o, k}, Con{va, st}, ls, mem, L, 1n+F),
            Exp.after(Imp.Exp.eval.bin(o, Some{va}, Imp.Exp.eval(b, size, ls, mem)), size, k, st, ls, mem, L, F),
            Exp.runs(b, size, ls, mem, Wasm.Code.bin{o, k}, Con{va, st}, L, 1n+F),
            Shared.Maybe.elim(U32, Imp.Exp.eval(b, size, ls, mem),
              mb => {Exp.after(mb, size, Wasm.Code.bin{o, k}, Con{va, st}, ls, mem, L, 1n+F) ==
                Exp.after(Imp.Exp.eval.bin(o, Some{va}, mb), size, k, st, ls, mem, L, F) :
                Maybe<&2, Wasm.Halted>},
              vb => {==}, {==})),
          {==}))
    case Imp.Exp.eqz{+a}:
      Equal.trans(Maybe<&2, Wasm.Halted>,
        Wasm.Frame.run(Exp.fuel(a, 1n+F), size, Wasm.Frame{Imp.Exp.code(a, Wasm.Code.eqz{k}), st, ls, mem, L}),
        Exp.after(Imp.Exp.eval(a, size, ls, mem), size, Wasm.Code.eqz{k}, st, ls, mem, L, 1n+F),
        Exp.after(Maybe.map(&2, U32, U32, x => Bool.to_u32(U32.is_eq(x, 0)), Imp.Exp.eval(a, size, ls, mem)),
          size, k, st, ls, mem, L, F),
        Exp.runs(a, size, ls, mem, Wasm.Code.eqz{k}, st, L, 1n+F),
        Shared.Maybe.elim(U32, Imp.Exp.eval(a, size, ls, mem),
          ma => {Exp.after(ma, size, Wasm.Code.eqz{k}, st, ls, mem, L, 1n+F) ==
            Exp.after(Maybe.map(&2, U32, U32, x => Bool.to_u32(U32.is_eq(x, 0)), ma), size, k, st, ls, mem, L, F) :
            Maybe<&2, Wasm.Halted>},
          va => {==}, {==}))
    case Imp.Exp.load{+off, +a}:
      Equal.trans(Maybe<&2, Wasm.Halted>,
        Wasm.Frame.run(Exp.fuel(a, 1n+F), size,
          Wasm.Frame{Imp.Exp.code(a, Wasm.Code.load{off, k}), st, ls, mem, L}),
        Exp.after(Imp.Exp.eval(a, size, ls, mem), size, Wasm.Code.load{off, k}, st, ls, mem, L, 1n+F),
        Exp.after(Imp.Exp.eval.load(Imp.Exp.eval(a, size, ls, mem), off, 4, size, mem,
          x => m => Wasm.Mem.load(x, m)), size, k, st, ls, mem, L, F),
        Exp.runs(a, size, ls, mem, Wasm.Code.load{off, k}, st, L, 1n+F),
        Shared.Maybe.elim(U32, Imp.Exp.eval(a, size, ls, mem),
          ma => {Exp.after(ma, size, Wasm.Code.load{off, k}, st, ls, mem, L, 1n+F) ==
            Exp.after(Imp.Exp.eval.load(ma, off, 4, size, mem, x => m => Wasm.Mem.load(x, m)), size, k, st, ls,
              mem, L, F) : Maybe<&2, Wasm.Halted>},
          va => Shared.Maybe.elim(U32, Wasm.Mem.addr(va, off, 4, size),
            mm => {Wasm.Step.then(Wasm.Frame.with(Wasm.Step.load.at(mm, mem, x => m => Wasm.Mem.load(x, m), st),
              k, ls, mem, L), g => Wasm.Frame.run(F, size, g)) ==
              Exp.after(Imp.Exp.eval.at(mm, mem, x => m => Wasm.Mem.load(x, m)), size, k, st, ls, mem, L, F) :
              Maybe<&2, Wasm.Halted>},
            ea => {==}, {==}),
          {==}))
    case Imp.Exp.load8{+off, +a}:
      Equal.trans(Maybe<&2, Wasm.Halted>,
        Wasm.Frame.run(Exp.fuel(a, 1n+F), size,
          Wasm.Frame{Imp.Exp.code(a, Wasm.Code.load8_u{off, k}), st, ls, mem, L}),
        Exp.after(Imp.Exp.eval(a, size, ls, mem), size, Wasm.Code.load8_u{off, k}, st, ls, mem, L, 1n+F),
        Exp.after(Imp.Exp.eval.load(Imp.Exp.eval(a, size, ls, mem), off, 1, size, mem,
          x => m => U32.from_nat(Wasm.Mem.get_at(x, m))), size, k, st, ls, mem, L, F),
        Exp.runs(a, size, ls, mem, Wasm.Code.load8_u{off, k}, st, L, 1n+F),
        Shared.Maybe.elim(U32, Imp.Exp.eval(a, size, ls, mem),
          ma => {Exp.after(ma, size, Wasm.Code.load8_u{off, k}, st, ls, mem, L, 1n+F) ==
            Exp.after(Imp.Exp.eval.load(ma, off, 1, size, mem, x => m => U32.from_nat(Wasm.Mem.get_at(x, m))), size,
              k, st, ls, mem, L, F) : Maybe<&2, Wasm.Halted>},
          va => Shared.Maybe.elim(U32, Wasm.Mem.addr(va, off, 1, size),
            mm => {Wasm.Step.then(Wasm.Frame.with(Wasm.Step.load.at(mm, mem,
              x => m => U32.from_nat(Wasm.Mem.get_at(x, m)), st), k, ls, mem, L), g => Wasm.Frame.run(F, size, g)) ==
              Exp.after(Imp.Exp.eval.at(mm, mem, x => m => U32.from_nat(Wasm.Mem.get_at(x, m))), size, k, st, ls,
                mem, L, F) : Maybe<&2, Wasm.Halted>},
            ea => {==}, {==}),
          {==}))
    case Imp.Exp.size{}:
      {==}

# Statements
# ==========

def Res.elim(r: Maybe<&2, Imp.Res>, -P: Maybe<&2, Imp.Res> -> Type,
  next: @ls:List<&2, U32> -> @mem:Wasm.Mem -> P(Some{Imp.Res.next{ls, mem}}),
  brk0: @ls:List<&2, U32> -> @mem:Wasm.Mem -> P(Some{Imp.Res.brk{0n, ls, mem}}),
  brk: @l:Nat -> @ls:List<&2, U32> -> @mem:Wasm.Mem -> P(Some{Imp.Res.brk{1n+l, ls, mem}}),
  trap: P(Some{Imp.Res.trap{}}), none: P(None{})) -> P(r):
  match r:
    case Some{Imp.Res.next{ls, mem}}:
      next(ls, mem)
    case Some{Imp.Res.brk{0n, ls, mem}}:
      brk0(ls, mem)
    case Some{Imp.Res.brk{1n+l, ls, mem}}:
      brk(l, ls, mem)
    case Some{Imp.Res.trap{}}:
      trap
    case None{}:
      none

# go's fuel after a statement that went on; else F
def Fuel.next(r: Maybe<&2, Imp.Res>, go: List<&2, U32> -> Wasm.Mem -> Nat, F: Nat) -> Nat:
  match r:
    case Some{Imp.Res.next{ls, mem}}:
      go(ls, mem)
    case _:
      F

# the fuel after a branch of an if: one more step when it went on
def Fuel.end(r: Maybe<&2, Imp.Res>, F: Nat) -> Nat:
  match r:
    case Some{Imp.Res.next{ls, mem}}:
      1n+F
    case _:
      F

def Fuel.pick(c: Bool, a: Nat, b: Nat) -> Nat:
  match c:
    case True{}:
      a
    case False{}:
      b

def Fuel.if(mc: Maybe<&2, U32>, a: Nat, b: Nat, F: Nat) -> Nat:
  match mc:
    case Some{c}:
      Fuel.pick(U32.is_ne(c, 0), a, b)
    case None{}:
      F

def Stm.fuel(s: Imp.Stm, +n: Nat, +size: U32, +ls: List<&2, U32>, +mem: Wasm.Mem, +F: Nat) -> Nat:
  match s:
    case Imp.Stm.skip{}:
      F
    case Imp.Stm.set{i, e}:
      Exp.fuel(e, 1n+F)
    case Imp.Stm.store{off, a, v}:
      Exp.fuel(a, Exp.fuel(v, 1n+F))
    case Imp.Stm.store8{off, a, v}:
      Exp.fuel(a, Exp.fuel(v, 1n+F))
    case Imp.Stm.seq{+a, b}:
      Stm.fuel(a, n, size, ls, mem, Fuel.next(Imp.Stm.run(a, n, size, ls, mem),
        ls2 => mem2 => Stm.fuel(b, n, size, ls2, mem2, F), F))
    case Imp.Stm.if{+c, +a, +b}:
      Nat.add(2n, Exp.fuel(c, 1n+Fuel.if(Imp.Exp.eval(c, size, ls, mem),
        Stm.fuel(a, n, size, ls, mem, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F)),
        Stm.fuel(b, n, size, ls, mem, Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F)), F)))
    case Imp.Stm.loop{+body}:
      match n:
        case 0n:
          0n
        case 1n+p:
          Nat.add(2n, Stm.fuel(body, p, size, ls, mem, Fuel.next(Imp.Stm.run(body, p, size, ls, mem),
            ls2 => mem2 => 1n+Shared.Nat.dec(Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F)), F)))
    case Imp.Stm.break{l}:
      1n+F
    case Imp.Stm.trap{}:
      1n+F

# the run after a branch to the block at depth m, with F fuel left after it
def Brk.after(m: Maybe<&2, Nat>, L: List<&2, Wasm.Label>, ls: List<&2, U32>, mem: Wasm.Mem, F: Nat,
  +size: U32) -> Maybe<&2, Wasm.Halted>:
  match m:
    case Some{d}:
      Wasm.Step.then(Wasm.Step.br(d, L, ls, mem), g => Wasm.Frame.run(F, size, g))
    case None{}:
      None{}

# the run after a statement ended with r: k when it went on, the block of its
# loop when it broke out of one
def Stm.after(r: Maybe<&2, Imp.Res>, +ds: List<&2, Nat>, k: Wasm.Code, st: List<&2, U32>,
  L: List<&2, Wasm.Label>, F: Nat, +size: U32) -> Maybe<&2, Wasm.Halted>:
  match r:
    case Some{Imp.Res.next{ls, mem}}:
      Wasm.Frame.run(F, size, Wasm.Frame{k, st, ls, mem, L})
    case Some{Imp.Res.brk{l, ls, mem}}:
      Brk.after(List.get(&2, Nat, ds, l), L, ls, mem, F, size)
    case _:
      None{}

def Ds.get_up(ds: List<&2, Nat>, +d: Nat, l: Nat) ->
  {List.get(&2, Nat, Imp.Ds.up(ds, d), l) == Maybe.map(&2, Nat, Nat, x => Nat.add(d, x), List.get(&2, Nat, ds, l)) :
    Maybe<&2, Nat>}:
  match ds l:
    case Nil{} _:
      {==}
    case Con{x, rest} 0n:
      {==}
    case Con{x, rest} 1n+j:
      Ds.get_up(rest, d, j)

# a break through one more block
def Brk.up1(+ds: List<&2, Nat>, +l: Nat, +B: Wasm.Label, +L: List<&2, Wasm.Label>, +ls: List<&2, U32>,
  +mem: Wasm.Mem, +F: Nat, +size: U32) ->
  {Brk.after(List.get(&2, Nat, Imp.Ds.up(ds, 1n), l), Con{B, L}, ls, mem, F, size) ==
    Brk.after(List.get(&2, Nat, ds, l), L, ls, mem, F, size) : Maybe<&2, Wasm.Halted>}:
  Equal.trans(Maybe<&2, Wasm.Halted>,
    Brk.after(List.get(&2, Nat, Imp.Ds.up(ds, 1n), l), Con{B, L}, ls, mem, F, size),
    Brk.after(Maybe.map(&2, Nat, Nat, x => Nat.add(1n, x), List.get(&2, Nat, ds, l)), Con{B, L}, ls, mem, F, size),
    Brk.after(List.get(&2, Nat, ds, l), L, ls, mem, F, size),
    Equal.cong(Maybe<&2, Nat>, Maybe<&2, Wasm.Halted>, m => Brk.after(m, Con{B, L}, ls, mem, F, size),
      List.get(&2, Nat, Imp.Ds.up(ds, 1n), l),
      Maybe.map(&2, Nat, Nat, x => Nat.add(1n, x), List.get(&2, Nat, ds, l)), Ds.get_up(ds, 1n, l)),
    Shared.Maybe.elim(Nat, List.get(&2, Nat, ds, l),
      m => {Brk.after(Maybe.map(&2, Nat, Nat, x => Nat.add(1n, x), m), Con{B, L}, ls, mem, F, size) ==
        Brk.after(m, L, ls, mem, F, size) : Maybe<&2, Wasm.Halted>},
      x => {==}, {==}))

# a break through two more blocks
def Brk.up2(+ds: List<&2, Nat>, +l: Nat, +B: Wasm.Label, +C: Wasm.Label, +L: List<&2, Wasm.Label>,
  +ls: List<&2, U32>, +mem: Wasm.Mem, +F: Nat, +size: U32) ->
  {Brk.after(List.get(&2, Nat, Imp.Ds.up(ds, 2n), l), Con{B, Con{C, L}}, ls, mem, F, size) ==
    Brk.after(List.get(&2, Nat, ds, l), L, ls, mem, F, size) : Maybe<&2, Wasm.Halted>}:
  Equal.trans(Maybe<&2, Wasm.Halted>,
    Brk.after(List.get(&2, Nat, Imp.Ds.up(ds, 2n), l), Con{B, Con{C, L}}, ls, mem, F, size),
    Brk.after(Maybe.map(&2, Nat, Nat, x => Nat.add(2n, x), List.get(&2, Nat, ds, l)), Con{B, Con{C, L}}, ls, mem,
      F, size),
    Brk.after(List.get(&2, Nat, ds, l), L, ls, mem, F, size),
    Equal.cong(Maybe<&2, Nat>, Maybe<&2, Wasm.Halted>, m => Brk.after(m, Con{B, Con{C, L}}, ls, mem, F, size),
      List.get(&2, Nat, Imp.Ds.up(ds, 2n), l),
      Maybe.map(&2, Nat, Nat, x => Nat.add(2n, x), List.get(&2, Nat, ds, l)), Ds.get_up(ds, 2n, l)),
    Shared.Maybe.elim(Nat, List.get(&2, Nat, ds, l),
      m => {Brk.after(Maybe.map(&2, Nat, Nat, x => Nat.add(2n, x), m), Con{B, Con{C, L}}, ls, mem, F, size) ==
        Brk.after(m, L, ls, mem, F, size) : Maybe<&2, Wasm.Halted>},
      x => {==}, {==}))

# a loop entered after its block has the fuel of the whole loop, less one
def Loop.dec(X: Nat, +body: Wasm.Code, +k: Wasm.Code, +st: List<&2, U32>, ls: List<&2, U32>, mem: Wasm.Mem,
  L: List<&2, Wasm.Label>, +size: U32) ->
  {Wasm.Frame.run(Shared.Nat.dec(X), size, Wasm.Frame{Wasm.Code.loop{body, Wasm.Code.end{}}, st, ls, mem,
    Con{Wasm.Label{k, k, st}, L}}) ==
    Wasm.Frame.run(X, size, Wasm.Frame{Wasm.Code.block{Wasm.Code.loop{body, Wasm.Code.end{}}, k}, st, ls, mem, L}) :
    Maybe<&2, Wasm.Halted>}:
  match X:
    case 0n:
      {==}
    case 1n+Y:
      {==}

# The code of s, then k, ends where the meaning says: at k when s went on, at
# its loop's block when it broke out of one, or at none.
def Stm.runs(s: Imp.Stm, +n: Nat, +size: U32, +ls: List<&2, U32>, +mem: Wasm.Mem, +ds: List<&2, Nat>,
  +k: Wasm.Code, +st: List<&2, U32>, +L: List<&2, Wasm.Label>, +F: Nat) ->
  {Wasm.Frame.run(Stm.fuel(s, n, size, ls, mem, F), size, Wasm.Frame{Imp.Stm.code(s, ds, k), st, ls, mem, L}) ==
    Stm.after(Imp.Stm.run(s, n, size, ls, mem), ds, k, st, L, F, size) : Maybe<&2, Wasm.Halted>}:
  match s:
    case Imp.Stm.skip{}:
      {==}
    case Imp.Stm.set{+i, +e}:
      Equal.trans(Maybe<&2, Wasm.Halted>,
        Wasm.Frame.run(Exp.fuel(e, 1n+F), size, Wasm.Frame{Imp.Exp.code(e, Wasm.Code.set{i, k}), st, ls, mem, L}),
        Exp.after(Imp.Exp.eval(e, size, ls, mem), size, Wasm.Code.set{i, k}, st, ls, mem, L, 1n+F),
        Stm.after(Some{Imp.Stm.set(Imp.Exp.eval(e, size, ls, mem), i, ls, mem)}, ds, k, st, L, F, size),
        Exp.runs(e, size, ls, mem, Wasm.Code.set{i, k}, st, L, 1n+F),
        Shared.Maybe.elim(U32, Imp.Exp.eval(e, size, ls, mem),
          me => {Exp.after(me, size, Wasm.Code.set{i, k}, st, ls, mem, L, 1n+F) ==
            Stm.after(Some{Imp.Stm.set(me, i, ls, mem)}, ds, k, st, L, F, size) : Maybe<&2, Wasm.Halted>},
          v => Shared.Maybe.elim(List<&2, U32>, Wasm.List.put(ls, i, v),
            mp => {Wasm.Step.then(Wasm.Step.set.of(mp, k, st, mem, L), g => Wasm.Frame.run(F, size, g)) ==
              Stm.after(Some{Imp.Stm.set.of(mp, mem)}, ds, k, st, L, F, size) : Maybe<&2, Wasm.Halted>},
            ls2 => {==}, {==}),
          {==}))
    case Imp.Stm.store{+off, +a, +v}:
      Equal.trans(Maybe<&2, Wasm.Halted>,
        Wasm.Frame.run(Exp.fuel(a, Exp.fuel(v, 1n+F)), size,
          Wasm.Frame{Imp.Exp.code(a, Imp.Exp.code(v, Wasm.Code.store{off, k})), st, ls, mem, L}),
        Exp.after(Imp.Exp.eval(a, size, ls, mem), size, Imp.Exp.code(v, Wasm.Code.store{off, k}), st, ls, mem, L,
          Exp.fuel(v, 1n+F)),
        Stm.after(Some{Imp.Stm.store(Imp.Exp.eval(a, size, ls, mem), Imp.Exp.eval(v, size, ls, mem), off, 4, size,
          x => m => y => Wasm.Mem.store(x, m, y), ls, mem)}, ds, k, st, L, F, size),
        Exp.runs(a, size, ls, mem, Imp.Exp.code(v, Wasm.Code.store{off, k}), st, L, Exp.fuel(v, 1n+F)),
        Shared.Maybe.elim(U32, Imp.Exp.eval(a, size, ls, mem),
          ma => {Exp.after(ma, size, Imp.Exp.code(v, Wasm.Code.store{off, k}), st, ls, mem, L, Exp.fuel(v, 1n+F)) ==
            Stm.after(Some{Imp.Stm.store(ma, Imp.Exp.eval(v, size, ls, mem), off, 4, size, x => m => y => Wasm.Mem.store(x, m, y), ls, mem)}, ds, k, st,
              L, F, size) : Maybe<&2, Wasm.Halted>},
          +va => Equal.trans(Maybe<&2, Wasm.Halted>,
            Wasm.Frame.run(Exp.fuel(v, 1n+F), size,
              Wasm.Frame{Imp.Exp.code(v, Wasm.Code.store{off, k}), Con{va, st}, ls, mem, L}),
            Exp.after(Imp.Exp.eval(v, size, ls, mem), size, Wasm.Code.store{off, k}, Con{va, st}, ls, mem, L, 1n+F),
            Stm.after(Some{Imp.Stm.store(Some{va}, Imp.Exp.eval(v, size, ls, mem), off, 4, size, x => m => y => Wasm.Mem.store(x, m, y), ls, mem)}, ds,
              k, st, L, F, size),
            Exp.runs(v, size, ls, mem, Wasm.Code.store{off, k}, Con{va, st}, L, 1n+F),
            Shared.Maybe.elim(U32, Imp.Exp.eval(v, size, ls, mem),
              mv => {Exp.after(mv, size, Wasm.Code.store{off, k}, Con{va, st}, ls, mem, L, 1n+F) ==
                Stm.after(Some{Imp.Stm.store(Some{va}, mv, off, 4, size, x => m => y => Wasm.Mem.store(x, m, y), ls, mem)}, ds, k, st, L, F, size) :
                Maybe<&2, Wasm.Halted>},
              +vv => Shared.Maybe.elim(U32, Wasm.Mem.addr(va, off, 4, size),
                mm => {Wasm.Step.then(Wasm.Step.store.at(mm, vv, x => m => y => Wasm.Mem.store(x, m, y), k, st, ls, mem, L),
                  g => Wasm.Frame.run(F, size, g)) ==
                  Stm.after(Some{Imp.Stm.store.at(mm, vv, x => m => y => Wasm.Mem.store(x, m, y), ls, mem)}, ds, k, st, L, F, size) :
                  Maybe<&2, Wasm.Halted>},
                ea => {==}, {==}),
              {==})),
          {==}))
    case Imp.Stm.store8{+off, +a, +v}:
      Equal.trans(Maybe<&2, Wasm.Halted>,
        Wasm.Frame.run(Exp.fuel(a, Exp.fuel(v, 1n+F)), size,
          Wasm.Frame{Imp.Exp.code(a, Imp.Exp.code(v, Wasm.Code.store8{off, k})), st, ls, mem, L}),
        Exp.after(Imp.Exp.eval(a, size, ls, mem), size, Imp.Exp.code(v, Wasm.Code.store8{off, k}), st, ls, mem, L,
          Exp.fuel(v, 1n+F)),
        Stm.after(Some{Imp.Stm.store(Imp.Exp.eval(a, size, ls, mem), Imp.Exp.eval(v, size, ls, mem), off, 1, size,
          x => m => y => Wasm.Mem.set_at(x, m, Wasm.U32.low(y)), ls, mem)}, ds, k, st, L, F, size),
        Exp.runs(a, size, ls, mem, Imp.Exp.code(v, Wasm.Code.store8{off, k}), st, L, Exp.fuel(v, 1n+F)),
        Shared.Maybe.elim(U32, Imp.Exp.eval(a, size, ls, mem),
          ma => {Exp.after(ma, size, Imp.Exp.code(v, Wasm.Code.store8{off, k}), st, ls, mem, L, Exp.fuel(v, 1n+F)) ==
            Stm.after(Some{Imp.Stm.store(ma, Imp.Exp.eval(v, size, ls, mem), off, 1, size, x => m => y => Wasm.Mem.set_at(x, m, Wasm.U32.low(y)), ls, mem)}, ds, k, st,
              L, F, size) : Maybe<&2, Wasm.Halted>},
          +va => Equal.trans(Maybe<&2, Wasm.Halted>,
            Wasm.Frame.run(Exp.fuel(v, 1n+F), size,
              Wasm.Frame{Imp.Exp.code(v, Wasm.Code.store8{off, k}), Con{va, st}, ls, mem, L}),
            Exp.after(Imp.Exp.eval(v, size, ls, mem), size, Wasm.Code.store8{off, k}, Con{va, st}, ls, mem, L, 1n+F),
            Stm.after(Some{Imp.Stm.store(Some{va}, Imp.Exp.eval(v, size, ls, mem), off, 1, size, x => m => y => Wasm.Mem.set_at(x, m, Wasm.U32.low(y)), ls, mem)}, ds,
              k, st, L, F, size),
            Exp.runs(v, size, ls, mem, Wasm.Code.store8{off, k}, Con{va, st}, L, 1n+F),
            Shared.Maybe.elim(U32, Imp.Exp.eval(v, size, ls, mem),
              mv => {Exp.after(mv, size, Wasm.Code.store8{off, k}, Con{va, st}, ls, mem, L, 1n+F) ==
                Stm.after(Some{Imp.Stm.store(Some{va}, mv, off, 1, size, x => m => y => Wasm.Mem.set_at(x, m, Wasm.U32.low(y)), ls, mem)}, ds, k, st, L, F, size) :
                Maybe<&2, Wasm.Halted>},
              +vv => Shared.Maybe.elim(U32, Wasm.Mem.addr(va, off, 1, size),
                mm => {Wasm.Step.then(Wasm.Step.store.at(mm, vv, x => m => y => Wasm.Mem.set_at(x, m, Wasm.U32.low(y)), k, st, ls, mem, L),
                  g => Wasm.Frame.run(F, size, g)) ==
                  Stm.after(Some{Imp.Stm.store.at(mm, vv, x => m => y => Wasm.Mem.set_at(x, m, Wasm.U32.low(y)), ls, mem)}, ds, k, st, L, F, size) :
                  Maybe<&2, Wasm.Halted>},
                ea => {==}, {==}),
              {==})),
          {==}))
    case Imp.Stm.seq{+a, +b}:
      Equal.trans(Maybe<&2, Wasm.Halted>,
        Wasm.Frame.run(Stm.fuel(a, n, size, ls, mem, Fuel.next(Imp.Stm.run(a, n, size, ls, mem),
          ls2 => mem2 => Stm.fuel(b, n, size, ls2, mem2, F), F)), size,
          Wasm.Frame{Imp.Stm.code(a, ds, Imp.Stm.code(b, ds, k)), st, ls, mem, L}),
        Stm.after(Imp.Stm.run(a, n, size, ls, mem), ds, Imp.Stm.code(b, ds, k), st, L,
          Fuel.next(Imp.Stm.run(a, n, size, ls, mem), ls2 => mem2 => Stm.fuel(b, n, size, ls2, mem2, F), F), size),
        Stm.after(Imp.Res.then(Imp.Stm.run(a, n, size, ls, mem), ls2 => mem2 => Imp.Stm.run(b, n, size, ls2, mem2)),
          ds, k, st, L, F, size),
        Stm.runs(a, n, size, ls, mem, ds, Imp.Stm.code(b, ds, k), st, L,
          Fuel.next(Imp.Stm.run(a, n, size, ls, mem), ls2 => mem2 => Stm.fuel(b, n, size, ls2, mem2, F), F)),
        Res.elim(Imp.Stm.run(a, n, size, ls, mem),
          r => {Stm.after(r, ds, Imp.Stm.code(b, ds, k), st, L,
            Fuel.next(r, ls2 => mem2 => Stm.fuel(b, n, size, ls2, mem2, F), F), size) ==
            Stm.after(Imp.Res.then(r, ls2 => mem2 => Imp.Stm.run(b, n, size, ls2, mem2)), ds, k, st, L, F, size) :
            Maybe<&2, Wasm.Halted>},
          ls2 => mem2 => Stm.runs(b, n, size, ls2, mem2, ds, k, st, L, F),
          ls2 => mem2 => {==},
          l => ls2 => mem2 => {==},
          {==}, {==}))
    case Imp.Stm.if{+c, +a, +b}:
      Equal.trans(Maybe<&2, Wasm.Halted>,
        Wasm.Frame.run(Exp.fuel(c, 1n+Fuel.if(Imp.Exp.eval(c, size, ls, mem), Stm.fuel(a, n, size, ls, mem, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F)), Stm.fuel(b, n, size, ls, mem, Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F)), F)), size,
          Wasm.Frame{Imp.Exp.code(c, Wasm.Code.br_if{0n, Imp.Stm.code(b, Imp.Ds.up(ds, 2n), Wasm.Code.br{1n, Wasm.Code.end{}})}), st, ls, mem, Con{Wasm.Label{Imp.Stm.code(a, Imp.Ds.up(ds, 1n), Wasm.Code.end{}), Imp.Stm.code(a, Imp.Ds.up(ds, 1n), Wasm.Code.end{}), st}, Con{Wasm.Label{k, k, st}, L}}}),
        Exp.after(Imp.Exp.eval(c, size, ls, mem), size, Wasm.Code.br_if{0n, Imp.Stm.code(b, Imp.Ds.up(ds, 2n), Wasm.Code.br{1n, Wasm.Code.end{}})}, st, ls, mem, Con{Wasm.Label{Imp.Stm.code(a, Imp.Ds.up(ds, 1n), Wasm.Code.end{}), Imp.Stm.code(a, Imp.Ds.up(ds, 1n), Wasm.Code.end{}), st}, Con{Wasm.Label{k, k, st}, L}}, 1n+Fuel.if(Imp.Exp.eval(c, size, ls, mem), Stm.fuel(a, n, size, ls, mem, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F)), Stm.fuel(b, n, size, ls, mem, Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F)), F)),
        Stm.after(Imp.Stm.if(Imp.Exp.eval(c, size, ls, mem), u => Imp.Stm.run(a, n, size, ls, mem), u => Imp.Stm.run(b, n, size, ls, mem)), ds, k, st, L, F, size),
        Exp.runs(c, size, ls, mem, Wasm.Code.br_if{0n, Imp.Stm.code(b, Imp.Ds.up(ds, 2n), Wasm.Code.br{1n, Wasm.Code.end{}})}, st, Con{Wasm.Label{Imp.Stm.code(a, Imp.Ds.up(ds, 1n), Wasm.Code.end{}), Imp.Stm.code(a, Imp.Ds.up(ds, 1n), Wasm.Code.end{}), st}, Con{Wasm.Label{k, k, st}, L}}, 1n+Fuel.if(Imp.Exp.eval(c, size, ls, mem), Stm.fuel(a, n, size, ls, mem, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F)), Stm.fuel(b, n, size, ls, mem, Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F)), F)),
        Shared.Maybe.elim(U32, Imp.Exp.eval(c, size, ls, mem),
          mc => {Exp.after(mc, size, Wasm.Code.br_if{0n, Imp.Stm.code(b, Imp.Ds.up(ds, 2n), Wasm.Code.br{1n, Wasm.Code.end{}})}, st, ls, mem, Con{Wasm.Label{Imp.Stm.code(a, Imp.Ds.up(ds, 1n), Wasm.Code.end{}), Imp.Stm.code(a, Imp.Ds.up(ds, 1n), Wasm.Code.end{}), st}, Con{Wasm.Label{k, k, st}, L}}, 1n+Fuel.if(mc, Stm.fuel(a, n, size, ls, mem, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F)), Stm.fuel(b, n, size, ls, mem, Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F)), F)) ==
            Stm.after(Imp.Stm.if(mc, u => Imp.Stm.run(a, n, size, ls, mem), u => Imp.Stm.run(b, n, size, ls, mem)), ds, k, st, L, F, size) : Maybe<&2, Wasm.Halted>},
          vc => Shared.Bool.elim(U32.is_ne(vc, 0),
            cb => {Wasm.Step.then(Wasm.Step.br_if.of(cb, 0n, Imp.Stm.code(b, Imp.Ds.up(ds, 2n), Wasm.Code.br{1n, Wasm.Code.end{}}), st, ls, mem, Con{Wasm.Label{Imp.Stm.code(a, Imp.Ds.up(ds, 1n), Wasm.Code.end{}), Imp.Stm.code(a, Imp.Ds.up(ds, 1n), Wasm.Code.end{}), st}, Con{Wasm.Label{k, k, st}, L}}),
              g => Wasm.Frame.run(Fuel.pick(cb, Stm.fuel(a, n, size, ls, mem, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F)), Stm.fuel(b, n, size, ls, mem, Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F))), size, g)) ==
              Stm.after(Imp.Stm.if.of(cb, u => Imp.Stm.run(a, n, size, ls, mem), u => Imp.Stm.run(b, n, size, ls, mem)), ds, k, st, L, F, size) : Maybe<&2, Wasm.Halted>},
            Equal.trans(Maybe<&2, Wasm.Halted>,
              Wasm.Frame.run(Stm.fuel(a, n, size, ls, mem, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F)), size, Wasm.Frame{Imp.Stm.code(a, Imp.Ds.up(ds, 1n), Wasm.Code.end{}), st, ls, mem, Con{Wasm.Label{k, k, st}, L}}),
              Stm.after(Imp.Stm.run(a, n, size, ls, mem), Imp.Ds.up(ds, 1n), Wasm.Code.end{}, st, Con{Wasm.Label{k, k, st}, L}, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F), size),
              Stm.after(Imp.Stm.run(a, n, size, ls, mem), ds, k, st, L, F, size),
              Stm.runs(a, n, size, ls, mem, Imp.Ds.up(ds, 1n), Wasm.Code.end{}, st, Con{Wasm.Label{k, k, st}, L}, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F)),
              Res.elim(Imp.Stm.run(a, n, size, ls, mem),
                r => {Stm.after(r, Imp.Ds.up(ds, 1n), Wasm.Code.end{}, st, Con{Wasm.Label{k, k, st}, L}, Fuel.end(r, F), size) ==
                  Stm.after(r, ds, k, st, L, F, size) : Maybe<&2, Wasm.Halted>},
                ls2 => mem2 => {==},
                ls2 => mem2 => Brk.up1(ds, 0n, Wasm.Label{k, k, st}, L, ls2, mem2, F, size),
                l => ls2 => mem2 => Brk.up1(ds, 1n+l, Wasm.Label{k, k, st}, L, ls2, mem2, F, size),
                {==}, {==})),
            Equal.trans(Maybe<&2, Wasm.Halted>,
              Wasm.Frame.run(Stm.fuel(b, n, size, ls, mem, Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F)), size, Wasm.Frame{Imp.Stm.code(b, Imp.Ds.up(ds, 2n), Wasm.Code.br{1n, Wasm.Code.end{}}), st, ls, mem, Con{Wasm.Label{Imp.Stm.code(a, Imp.Ds.up(ds, 1n), Wasm.Code.end{}), Imp.Stm.code(a, Imp.Ds.up(ds, 1n), Wasm.Code.end{}), st}, Con{Wasm.Label{k, k, st}, L}}}),
              Stm.after(Imp.Stm.run(b, n, size, ls, mem), Imp.Ds.up(ds, 2n), Wasm.Code.br{1n, Wasm.Code.end{}}, st, Con{Wasm.Label{Imp.Stm.code(a, Imp.Ds.up(ds, 1n), Wasm.Code.end{}), Imp.Stm.code(a, Imp.Ds.up(ds, 1n), Wasm.Code.end{}), st}, Con{Wasm.Label{k, k, st}, L}}, Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F), size),
              Stm.after(Imp.Stm.run(b, n, size, ls, mem), ds, k, st, L, F, size),
              Stm.runs(b, n, size, ls, mem, Imp.Ds.up(ds, 2n), Wasm.Code.br{1n, Wasm.Code.end{}}, st, Con{Wasm.Label{Imp.Stm.code(a, Imp.Ds.up(ds, 1n), Wasm.Code.end{}), Imp.Stm.code(a, Imp.Ds.up(ds, 1n), Wasm.Code.end{}), st}, Con{Wasm.Label{k, k, st}, L}},
                Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F)),
              Res.elim(Imp.Stm.run(b, n, size, ls, mem),
                r => {Stm.after(r, Imp.Ds.up(ds, 2n), Wasm.Code.br{1n, Wasm.Code.end{}}, st, Con{Wasm.Label{Imp.Stm.code(a, Imp.Ds.up(ds, 1n), Wasm.Code.end{}), Imp.Stm.code(a, Imp.Ds.up(ds, 1n), Wasm.Code.end{}), st}, Con{Wasm.Label{k, k, st}, L}}, Fuel.end(r, F), size) ==
                  Stm.after(r, ds, k, st, L, F, size) : Maybe<&2, Wasm.Halted>},
                ls2 => mem2 => {==},
                ls2 => mem2 => Brk.up2(ds, 0n, Wasm.Label{Imp.Stm.code(a, Imp.Ds.up(ds, 1n), Wasm.Code.end{}), Imp.Stm.code(a, Imp.Ds.up(ds, 1n), Wasm.Code.end{}), st}, Wasm.Label{k, k, st}, L, ls2, mem2, F, size),
                l => ls2 => mem2 => Brk.up2(ds, 1n+l, Wasm.Label{Imp.Stm.code(a, Imp.Ds.up(ds, 1n), Wasm.Code.end{}), Imp.Stm.code(a, Imp.Ds.up(ds, 1n), Wasm.Code.end{}), st}, Wasm.Label{k, k, st}, L, ls2, mem2, F, size),
                {==}, {==}))),
          {==}))
    case Imp.Stm.loop{+body}:
      match n:
        case 0n:
          {==}
        case 1n+p:
          Equal.trans(Maybe<&2, Wasm.Halted>,
            Wasm.Frame.run(Stm.fuel(body, p, size, ls, mem, Fuel.next(Imp.Stm.run(body, p, size, ls, mem), ls2 => mem2 => 1n+Shared.Nat.dec(Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F)), F)), size, Wasm.Frame{Imp.Stm.code(body, Con{1n, Imp.Ds.up(ds, 2n)}, Wasm.Code.br{0n, Wasm.Code.end{}}), st, ls, mem, Con{Wasm.Label{Wasm.Code.loop{Imp.Stm.code(body, Con{1n, Imp.Ds.up(ds, 2n)}, Wasm.Code.br{0n, Wasm.Code.end{}}), Wasm.Code.end{}}, Wasm.Code.end{}, st}, Con{Wasm.Label{k, k, st}, L}}}),
            Stm.after(Imp.Stm.run(body, p, size, ls, mem), Con{1n, Imp.Ds.up(ds, 2n)}, Wasm.Code.br{0n, Wasm.Code.end{}}, st, Con{Wasm.Label{Wasm.Code.loop{Imp.Stm.code(body, Con{1n, Imp.Ds.up(ds, 2n)}, Wasm.Code.br{0n, Wasm.Code.end{}}), Wasm.Code.end{}}, Wasm.Code.end{}, st}, Con{Wasm.Label{k, k, st}, L}}, Fuel.next(Imp.Stm.run(body, p, size, ls, mem), ls2 => mem2 => 1n+Shared.Nat.dec(Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F)), F), size),
            Stm.after(Imp.Res.loop(Imp.Stm.run(body, p, size, ls, mem), ls2 => mem2 => Imp.Stm.run(Imp.Stm.loop{body}, p, size, ls2, mem2)), ds, k, st, L, F, size),
            Stm.runs(body, p, size, ls, mem, Con{1n, Imp.Ds.up(ds, 2n)}, Wasm.Code.br{0n, Wasm.Code.end{}}, st, Con{Wasm.Label{Wasm.Code.loop{Imp.Stm.code(body, Con{1n, Imp.Ds.up(ds, 2n)}, Wasm.Code.br{0n, Wasm.Code.end{}}), Wasm.Code.end{}}, Wasm.Code.end{}, st}, Con{Wasm.Label{k, k, st}, L}}, Fuel.next(Imp.Stm.run(body, p, size, ls, mem), ls2 => mem2 => 1n+Shared.Nat.dec(Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F)), F)),
            Res.elim(Imp.Stm.run(body, p, size, ls, mem),
              r => {Stm.after(r, Con{1n, Imp.Ds.up(ds, 2n)}, Wasm.Code.br{0n, Wasm.Code.end{}}, st, Con{Wasm.Label{Wasm.Code.loop{Imp.Stm.code(body, Con{1n, Imp.Ds.up(ds, 2n)}, Wasm.Code.br{0n, Wasm.Code.end{}}), Wasm.Code.end{}}, Wasm.Code.end{}, st}, Con{Wasm.Label{k, k, st}, L}}, Fuel.next(r, ls2 => mem2 => 1n+Shared.Nat.dec(Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F)), F), size) ==
                Stm.after(Imp.Res.loop(r, ls2 => mem2 => Imp.Stm.run(Imp.Stm.loop{body}, p, size, ls2, mem2)), ds, k, st, L, F, size) : Maybe<&2, Wasm.Halted>},
              +ls2 => +mem2 => Equal.trans(Maybe<&2, Wasm.Halted>,
                Wasm.Frame.run(Shared.Nat.dec(Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F)), size,
                  Wasm.Frame{Wasm.Code.loop{Imp.Stm.code(body, Con{1n, Imp.Ds.up(ds, 2n)}, Wasm.Code.br{0n, Wasm.Code.end{}}), Wasm.Code.end{}}, st, ls2, mem2, Con{Wasm.Label{k, k, st}, L}}),
                Wasm.Frame.run(Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F), size,
                  Wasm.Frame{Wasm.Code.block{Wasm.Code.loop{Imp.Stm.code(body, Con{1n, Imp.Ds.up(ds, 2n)}, Wasm.Code.br{0n, Wasm.Code.end{}}), Wasm.Code.end{}}, k}, st, ls2, mem2, L}),
                Stm.after(Imp.Stm.run(Imp.Stm.loop{body}, p, size, ls2, mem2), ds, k, st, L, F, size),
                Loop.dec(Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F), Imp.Stm.code(body, Con{1n, Imp.Ds.up(ds, 2n)}, Wasm.Code.br{0n, Wasm.Code.end{}}), k, st, ls2, mem2, L, size),
                Stm.runs(Imp.Stm.loop{body}, p, size, ls2, mem2, ds, k, st, L, F)),
              ls2 => mem2 => {==},
              l => ls2 => mem2 => Brk.up2(ds, l, Wasm.Label{Wasm.Code.loop{Imp.Stm.code(body, Con{1n, Imp.Ds.up(ds, 2n)}, Wasm.Code.br{0n, Wasm.Code.end{}}), Wasm.Code.end{}}, Wasm.Code.end{}, st}, Wasm.Label{k, k, st}, L, ls2, mem2, F, size),
              {==}, {==}))
    case Imp.Stm.break{+l}:
      Shared.Maybe.elim(Nat, List.get(&2, Nat, ds, l),
        md => {Wasm.Frame.run(1n+F, size, Wasm.Frame{Imp.Stm.break.code(md, k), st, ls, mem, L}) ==
          Brk.after(md, L, ls, mem, F, size) : Maybe<&2, Wasm.Halted>},
        d => {==}, {==})
    case Imp.Stm.trap{}:
      {==}

# Programs
# ========

# A program's code ends with the value that the meaning returns; X fuel is left
# after the end.
def Prog.runs(+body: Imp.Stm, +ret: Imp.Exp, +n: Nat, +size: U32, +ls: List<&2, U32>, +mem: Wasm.Mem, +X: Nat) ->
  {Wasm.Frame.run(Stm.fuel(body, n, size, ls, mem, Exp.fuel(ret, 1n+X)), size,
    Wasm.Frame{Imp.Stm.code(body, [], Imp.Exp.code(ret, Wasm.Code.end{})), [], ls, mem, []}) ==
    Imp.Prog.ret(Imp.Stm.run(body, n, size, ls, mem), ret, size) : Maybe<&2, Wasm.Halted>}:
  Equal.trans(Maybe<&2, Wasm.Halted>,
    Wasm.Frame.run(Stm.fuel(body, n, size, ls, mem, Exp.fuel(ret, 1n+X)), size,
      Wasm.Frame{Imp.Stm.code(body, [], Imp.Exp.code(ret, Wasm.Code.end{})), [], ls, mem, []}),
    Stm.after(Imp.Stm.run(body, n, size, ls, mem), [], Imp.Exp.code(ret, Wasm.Code.end{}), [], [],
      Exp.fuel(ret, 1n+X), size),
    Imp.Prog.ret(Imp.Stm.run(body, n, size, ls, mem), ret, size),
    Stm.runs(body, n, size, ls, mem, [], Imp.Exp.code(ret, Wasm.Code.end{}), [], [], Exp.fuel(ret, 1n+X)),
    Res.elim(Imp.Stm.run(body, n, size, ls, mem),
      r => {Stm.after(r, [], Imp.Exp.code(ret, Wasm.Code.end{}), [], [], Exp.fuel(ret, 1n+X), size) ==
        Imp.Prog.ret(r, ret, size) : Maybe<&2, Wasm.Halted>},
      +ls2 => +mem2 => Equal.trans(Maybe<&2, Wasm.Halted>,
        Wasm.Frame.run(Exp.fuel(ret, 1n+X), size,
          Wasm.Frame{Imp.Exp.code(ret, Wasm.Code.end{}), [], ls2, mem2, []}),
        Exp.after(Imp.Exp.eval(ret, size, ls2, mem2), size, Wasm.Code.end{}, [], ls2, mem2, [], 1n+X),
        Imp.Prog.ret.of(Imp.Exp.eval(ret, size, ls2, mem2), mem2),
        Exp.runs(ret, size, ls2, mem2, Wasm.Code.end{}, [], [], 1n+X),
        Shared.Maybe.elim(U32, Imp.Exp.eval(ret, size, ls2, mem2),
          m => {Exp.after(m, size, Wasm.Code.end{}, [], ls2, mem2, [], 1n+X) == Imp.Prog.ret.of(m, mem2) :
            Maybe<&2, Wasm.Halted>},
          v => {==}, {==})),
      ls2 => mem2 => {==},
      l => ls2 => mem2 => {==},
      {==}, {==}))

def Spec.fuel_out(p, pages, input, n):
  match p:
    case Imp.Prog{k, body, ret}:
      Stm.fuel(body, n, Wasm.Wasm.size(pages), Wasm.Locals.zero(k), Wasm.Input.mem(input), Exp.fuel(ret, 1n))

# The module's run, with the fuel of fuel_out, is the program's run.
def Prog.keeps(+k: Nat, +body: Imp.Stm, +ret: Imp.Exp, +pages: Nat, +input: Maybe<&2, List<&2, Nat>>, +n: Nat) ->
  {Wasm.Wasm.run(pages, Spec.fuel_out(Imp.Prog{k, body, ret}, pages, input, n),
    Imp.Imp.compile(Imp.Prog{k, body, ret}), input) == Imp.Imp.run(pages, n, Imp.Prog{k, body, ret}, input) :
    Maybe<&2, List<&2, Nat>>}:
  Shared.Bool.elim(Wasm.Wasm.fits(pages, input),
    ok => {Wasm.Wasm.run.of(ok, Spec.fuel_out(Imp.Prog{k, body, ret}, pages, input, n), Wasm.Wasm.size(pages),
      Imp.Imp.compile(Imp.Prog{k, body, ret}), input) ==
      Imp.Imp.run.of(ok, n, Wasm.Wasm.size(pages), Imp.Prog{k, body, ret}, input) : Maybe<&2, List<&2, Nat>>},
    Equal.cong(Maybe<&2, Wasm.Halted>, Maybe<&2, List<&2, Nat>>, d => Wasm.Halted.output(d, Wasm.Wasm.size(pages)),
      Wasm.Frame.run(Stm.fuel(body, n, Wasm.Wasm.size(pages), Wasm.Locals.zero(k), Wasm.Input.mem(input),
        Exp.fuel(ret, 1n)), Wasm.Wasm.size(pages),
        Wasm.Frame{Imp.Stm.code(body, [], Imp.Exp.code(ret, Wasm.Code.end{})), [], Wasm.Locals.zero(k),
          Wasm.Input.mem(input), []}),
      Imp.Prog.ret(Imp.Stm.run(body, n, Wasm.Wasm.size(pages), Wasm.Locals.zero(k), Wasm.Input.mem(input)), ret,
        Wasm.Wasm.size(pages)),
      Prog.runs(body, ret, n, Wasm.Wasm.size(pages), Wasm.Locals.zero(k), Wasm.Input.mem(input), 0n)),
    {==})

def Spec.compile_keeps(p, pages, input, n, w, h):
  match p:
    case Imp.Prog{k, body, ret}:
      Equal.trans(Maybe<&2, List<&2, Nat>>,
        Wasm.Wasm.run(pages, Spec.fuel_out(Imp.Prog{k, body, ret}, pages, input, n),
          Imp.Imp.compile(Imp.Prog{k, body, ret}), input),
        Imp.Imp.run(pages, n, Imp.Prog{k, body, ret}, input),
        Some{w},
        Prog.keeps(k, body, ret, pages, input, n), h)

# Lower bounds of the fuel
# ========================

def Exp.fuel_ge(e: Imp.Exp, +F: Nat) -> {Nat.is_le(F, Exp.fuel(e, F)) == True{} : Bool}:
  match e:
    case Imp.Exp.const{v}:
      Shared.Nat.is_le_succ(F, F, Shared.Nat.is_le_refl(F))
    case Imp.Exp.get{i}:
      Shared.Nat.is_le_succ(F, F, Shared.Nat.is_le_refl(F))
    case Imp.Exp.bin{o, +a, +b}:
      Shared.Nat.is_le_trans(F, Exp.fuel(b, 1n+F), Exp.fuel(a, Exp.fuel(b, 1n+F)),
        Shared.Nat.is_le_trans(F, 1n+F, Exp.fuel(b, 1n+F), Shared.Nat.is_le_succ(F, F, Shared.Nat.is_le_refl(F)), Exp.fuel_ge(b, 1n+F)),
        Exp.fuel_ge(a, Exp.fuel(b, 1n+F)))
    case Imp.Exp.eqz{+a}:
      Shared.Nat.is_le_trans(F, 1n+F, Exp.fuel(a, 1n+F), Shared.Nat.is_le_succ(F, F, Shared.Nat.is_le_refl(F)), Exp.fuel_ge(a, 1n+F))
    case Imp.Exp.load{off, +a}:
      Shared.Nat.is_le_trans(F, 1n+F, Exp.fuel(a, 1n+F), Shared.Nat.is_le_succ(F, F, Shared.Nat.is_le_refl(F)), Exp.fuel_ge(a, 1n+F))
    case Imp.Exp.load8{off, +a}:
      Shared.Nat.is_le_trans(F, 1n+F, Exp.fuel(a, 1n+F), Shared.Nat.is_le_succ(F, F, Shared.Nat.is_le_refl(F)), Exp.fuel_ge(a, 1n+F))
    case Imp.Exp.size{}:
      Shared.Nat.is_le_succ(F, F, Shared.Nat.is_le_refl(F))

# the fuel that a statement takes at least: n when it ran out, else F
def Stm.lower(r: Maybe<&2, Imp.Res>, n: Nat, F: Nat) -> Nat:
  match r:
    case Some{x}:
      F
    case None{}:
      n

def Nat.is_le_up2(+a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+1n+b) == True{} : Bool}:
  Shared.Nat.is_le_succ(a, 1n+b, Shared.Nat.is_le_succ(a, b, h))

def Stm.lower_end(r: Maybe<&2, Imp.Res>, +n: Nat, +F: Nat) -> {Nat.is_le(Stm.lower(r, n, F), Stm.lower(r, n, Fuel.end(r, F))) == True{} : Bool}:
  match r:
    case Some{Imp.Res.next{ls, mem}}:
      Shared.Nat.is_le_succ(F, F, Shared.Nat.is_le_refl(F))
    case Some{Imp.Res.brk{l, ls, mem}}:
      Shared.Nat.is_le_refl(F)
    case Some{Imp.Res.trap{}}:
      Shared.Nat.is_le_refl(F)
    case None{}:
      Shared.Nat.is_le_refl(n)

# The code of s takes at least n fuel when the meaning ran out, else at least F.
def Stm.fuel_ge(s: Imp.Stm, +n: Nat, +size: U32, +ls: List<&2, U32>, +mem: Wasm.Mem, +F: Nat) ->
  {Nat.is_le(Stm.lower(Imp.Stm.run(s, n, size, ls, mem), n, F), Stm.fuel(s, n, size, ls, mem, F)) == True{} : Bool}:
  match s:
    case Imp.Stm.skip{}:
      Shared.Nat.is_le_refl(F)
    case Imp.Stm.set{i, +e}:
      Shared.Nat.is_le_trans(F, 1n+F, Exp.fuel(e, 1n+F), Shared.Nat.is_le_succ(F, F, Shared.Nat.is_le_refl(F)), Exp.fuel_ge(e, 1n+F))
    case Imp.Stm.store{off, +a, +v}:
      Shared.Nat.is_le_trans(F, Exp.fuel(v, 1n+F), Exp.fuel(a, Exp.fuel(v, 1n+F)),
        Shared.Nat.is_le_trans(F, 1n+F, Exp.fuel(v, 1n+F), Shared.Nat.is_le_succ(F, F, Shared.Nat.is_le_refl(F)), Exp.fuel_ge(v, 1n+F)),
        Exp.fuel_ge(a, Exp.fuel(v, 1n+F)))
    case Imp.Stm.store8{off, +a, +v}:
      Shared.Nat.is_le_trans(F, Exp.fuel(v, 1n+F), Exp.fuel(a, Exp.fuel(v, 1n+F)),
        Shared.Nat.is_le_trans(F, 1n+F, Exp.fuel(v, 1n+F), Shared.Nat.is_le_succ(F, F, Shared.Nat.is_le_refl(F)), Exp.fuel_ge(v, 1n+F)),
        Exp.fuel_ge(a, Exp.fuel(v, 1n+F)))
    case Imp.Stm.seq{+a, +b}:
      go = Res.elim(Imp.Stm.run(a, n, size, ls, mem),
        r => {Nat.is_le(Stm.lower(r, n, Fuel.next(r, ls2 => mem2 => Stm.fuel(b, n, size, ls2, mem2, F), F)), Stm.fuel(a, n, size, ls, mem, Fuel.next(r, ls2 => mem2 => Stm.fuel(b, n, size, ls2, mem2, F), F))) == True{} : Bool} ->
          {Nat.is_le(Stm.lower(Imp.Res.then(r, ls2 => mem2 => Imp.Stm.run(b, n, size, ls2, mem2)), n, F), Stm.fuel(a, n, size, ls, mem, Fuel.next(r, ls2 => mem2 => Stm.fuel(b, n, size, ls2, mem2, F), F))) == True{} : Bool},
        +ls2 => +mem2 => h => Shared.Nat.is_le_trans(Stm.lower(Imp.Stm.run(b, n, size, ls2, mem2), n, F),
          Stm.fuel(b, n, size, ls2, mem2, F),
          Stm.fuel(a, n, size, ls, mem, Stm.fuel(b, n, size, ls2, mem2, F)),
          Stm.fuel_ge(b, n, size, ls2, mem2, F), h),
        ls2 => mem2 => h => h,
        l => ls2 => mem2 => h => h,
        h => h, h => h)
      go(Stm.fuel_ge(a, n, size, ls, mem, Fuel.next(Imp.Stm.run(a, n, size, ls, mem), ls2 => mem2 => Stm.fuel(b, n, size, ls2, mem2, F), F)))
    case Imp.Stm.if{+c, +a, +b}:
      Shared.Maybe.elim(U32, Imp.Exp.eval(c, size, ls, mem),
        mc => {Nat.is_le(Stm.lower(Imp.Stm.if(mc, u => Imp.Stm.run(a, n, size, ls, mem), u => Imp.Stm.run(b, n, size, ls, mem)), n, F), Nat.add(2n, Exp.fuel(c, 1n+Fuel.if(mc, Stm.fuel(a, n, size, ls, mem, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F)), Stm.fuel(b, n, size, ls, mem, Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F)), F)))) == True{} : Bool},
        vc => Shared.Bool.elim(U32.is_ne(vc, 0),
          cb => {Nat.is_le(Stm.lower(Imp.Stm.if.of(cb, u => Imp.Stm.run(a, n, size, ls, mem), u => Imp.Stm.run(b, n, size, ls, mem)), n, F), Nat.add(2n, Exp.fuel(c, 1n+Fuel.pick(cb, Stm.fuel(a, n, size, ls, mem, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F)), Stm.fuel(b, n, size, ls, mem, Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F)))))) == True{} : Bool},
          Shared.Nat.is_le_trans(Stm.lower(Imp.Stm.run(a, n, size, ls, mem), n, F), Stm.fuel(a, n, size, ls, mem, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F)), Nat.add(2n, Exp.fuel(c, 1n+Stm.fuel(a, n, size, ls, mem, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F)))),
              Shared.Nat.is_le_trans(Stm.lower(Imp.Stm.run(a, n, size, ls, mem), n, F), Stm.lower(Imp.Stm.run(a, n, size, ls, mem), n, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F)), Stm.fuel(a, n, size, ls, mem, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F)),
                Stm.lower_end(Imp.Stm.run(a, n, size, ls, mem), n, F), Stm.fuel_ge(a, n, size, ls, mem, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F))),
              Nat.is_le_up2(Stm.fuel(a, n, size, ls, mem, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F)), Exp.fuel(c, 1n+Stm.fuel(a, n, size, ls, mem, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F))), Shared.Nat.is_le_trans(Stm.fuel(a, n, size, ls, mem, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F)), 1n+Stm.fuel(a, n, size, ls, mem, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F)), Exp.fuel(c, 1n+Stm.fuel(a, n, size, ls, mem, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F))), Shared.Nat.is_le_succ(Stm.fuel(a, n, size, ls, mem, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F)), Stm.fuel(a, n, size, ls, mem, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F)), Shared.Nat.is_le_refl(Stm.fuel(a, n, size, ls, mem, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F)))),
                Exp.fuel_ge(c, 1n+Stm.fuel(a, n, size, ls, mem, Fuel.end(Imp.Stm.run(a, n, size, ls, mem), F)))))),
          Shared.Nat.is_le_trans(Stm.lower(Imp.Stm.run(b, n, size, ls, mem), n, F), Stm.fuel(b, n, size, ls, mem, Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F)), Nat.add(2n, Exp.fuel(c, 1n+Stm.fuel(b, n, size, ls, mem, Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F)))),
              Shared.Nat.is_le_trans(Stm.lower(Imp.Stm.run(b, n, size, ls, mem), n, F), Stm.lower(Imp.Stm.run(b, n, size, ls, mem), n, Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F)), Stm.fuel(b, n, size, ls, mem, Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F)),
                Stm.lower_end(Imp.Stm.run(b, n, size, ls, mem), n, F), Stm.fuel_ge(b, n, size, ls, mem, Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F))),
              Nat.is_le_up2(Stm.fuel(b, n, size, ls, mem, Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F)), Exp.fuel(c, 1n+Stm.fuel(b, n, size, ls, mem, Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F))), Shared.Nat.is_le_trans(Stm.fuel(b, n, size, ls, mem, Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F)), 1n+Stm.fuel(b, n, size, ls, mem, Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F)), Exp.fuel(c, 1n+Stm.fuel(b, n, size, ls, mem, Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F))), Shared.Nat.is_le_succ(Stm.fuel(b, n, size, ls, mem, Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F)), Stm.fuel(b, n, size, ls, mem, Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F)), Shared.Nat.is_le_refl(Stm.fuel(b, n, size, ls, mem, Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F)))),
                Exp.fuel_ge(c, 1n+Stm.fuel(b, n, size, ls, mem, Fuel.end(Imp.Stm.run(b, n, size, ls, mem), F))))))),
        Nat.is_le_up2(F, Exp.fuel(c, 1n+F), Shared.Nat.is_le_trans(F, 1n+F, Exp.fuel(c, 1n+F), Shared.Nat.is_le_succ(F, F, Shared.Nat.is_le_refl(F)),
          Exp.fuel_ge(c, 1n+F))))
    case Imp.Stm.loop{+body}:
      match n:
        case 0n:
          {==}
        case 1n+p:
          go = Res.elim(Imp.Stm.run(body, p, size, ls, mem),
            r => {Nat.is_le(Stm.lower(r, p, Fuel.next(r, ls2 => mem2 => 1n+Shared.Nat.dec(Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F)), F)), Stm.fuel(body, p, size, ls, mem, Fuel.next(r, ls2 => mem2 => 1n+Shared.Nat.dec(Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F)), F))) == True{} : Bool} ->
              {Nat.is_le(Stm.lower(Imp.Res.loop(r, ls2 => mem2 => Imp.Stm.run(Imp.Stm.loop{body}, p, size, ls2, mem2)), 1n+p, F), Nat.add(2n, Stm.fuel(body, p, size, ls, mem, Fuel.next(r, ls2 => mem2 => 1n+Shared.Nat.dec(Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F)), F)))) == True{} : Bool},
            +ls2 => +mem2 => +h =>
              go2 = Shared.Maybe.elim(Imp.Res, Imp.Stm.run(Imp.Stm.loop{body}, p, size, ls2, mem2),
                m => {Nat.is_le(Stm.lower(m, p, F), Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F)) == True{} : Bool} -> {Nat.is_le(Stm.lower(m, 1n+p, F), 1n+1n+Stm.fuel(body, p, size, ls, mem, 1n+Shared.Nat.dec(Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F)))) == True{} : Bool},
                x => h2 => Nat.is_le_up2(F, Stm.fuel(body, p, size, ls, mem, 1n+Shared.Nat.dec(Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F))), Shared.Nat.is_le_trans(F, 1n+Shared.Nat.dec(Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F)), Stm.fuel(body, p, size, ls, mem, 1n+Shared.Nat.dec(Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F))),
                  Shared.Nat.is_le_trans(F, Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F), 1n+Shared.Nat.dec(Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F)), h2, Shared.Nat.is_le_dec(Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F))), h)),
                h2 => Shared.Nat.is_le_succ(p, Stm.fuel(body, p, size, ls, mem, 1n+Shared.Nat.dec(Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F))), Shared.Nat.is_le_trans(p, 1n+Shared.Nat.dec(Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F)), Stm.fuel(body, p, size, ls, mem, 1n+Shared.Nat.dec(Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F))),
                  Shared.Nat.is_le_trans(p, Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F), 1n+Shared.Nat.dec(Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F)), h2, Shared.Nat.is_le_dec(Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F))), h)))
              go2(Stm.fuel_ge(Imp.Stm.loop{body}, p, size, ls2, mem2, F)),
            ls2 => mem2 => h => Nat.is_le_up2(F, Stm.fuel(body, p, size, ls, mem, F), h),
            l => ls2 => mem2 => h => Nat.is_le_up2(F, Stm.fuel(body, p, size, ls, mem, F), h),
            h => Nat.is_le_up2(F, Stm.fuel(body, p, size, ls, mem, F), h),
            h => Shared.Nat.is_le_succ(p, Stm.fuel(body, p, size, ls, mem, F), h))
          go(Stm.fuel_ge(body, p, size, ls, mem, Fuel.next(Imp.Stm.run(body, p, size, ls, mem), ls2 => mem2 => 1n+Shared.Nat.dec(Stm.fuel(Imp.Stm.loop{body}, p, size, ls2, mem2, F)), F)))
    case Imp.Stm.break{l}:
      Shared.Nat.is_le_succ(F, F, Shared.Nat.is_le_refl(F))
    case Imp.Stm.trap{}:
      Shared.Nat.is_le_succ(F, F, Shared.Nat.is_le_refl(F))

# More fuel
# =========

def Step.elim(s: Wasm.Step, -P: Wasm.Step -> Type, next: @g:Wasm.Frame -> P(Wasm.Step.next{g}),
  done: @d:Wasm.Halted -> P(Wasm.Step.done{d}), trap: P(Wasm.Step.trap{})) -> P(s):
  match s:
    case Wasm.Step.next{g}:
      next(g)
    case Wasm.Step.done{d}:
      done(d)
    case Wasm.Step.trap{}:
      trap

# A run that halts within G steps halts the same way within M >= G steps.
def Run.up(G: Nat, M: Nat, +size: U32, f: Wasm.Frame, +x: Wasm.Halted, hle: {Nat.is_le(G, M) == True{} : Bool},
  h: {Wasm.Frame.run(G, size, f) == Some{x} : Maybe<&2, Wasm.Halted>}) -> {Wasm.Frame.run(M, size, f) == Some{x} : Maybe<&2, Wasm.Halted>}:
  match G M:
    case 0n _:
      Empty.absurd({Wasm.Frame.run(M, size, f) == Some{x} : Maybe<&2, Wasm.Halted>}, Shared.Maybe.no_none(Wasm.Halted, x, h))
    case 1n+g 0n:
      Shared.Bool.absurd({Wasm.Frame.run(0n, size, f) == Some{x} : Maybe<&2, Wasm.Halted>}, hle)
    case 1n+g 1n+m:
      go = Step.elim(Wasm.Step.of(size, f),
        s => {Wasm.Step.then(s, y => Wasm.Frame.run(g, size, y)) == Some{x} : Maybe<&2, Wasm.Halted>} ->
          {Wasm.Step.then(s, y => Wasm.Frame.run(m, size, y)) == Some{x} : Maybe<&2, Wasm.Halted>},
        y => h2 => Run.up(g, m, size, y, x, hle, h2),
        d => h2 => h2,
        h2 => Empty.absurd({None{} == Some{x} : Maybe<&2, Wasm.Halted>}, Shared.Maybe.no_none(Wasm.Halted, x, h2)))
      go(h)

# n is at most the fuel that Prog.runs gives with n left after the end
def Prog.fuel_ge(+body: Imp.Stm, +ret: Imp.Exp, +n: Nat, +size: U32, +ls: List<&2, U32>, +mem: Wasm.Mem) ->
  {Nat.is_le(n, Stm.fuel(body, n, size, ls, mem, Exp.fuel(ret, 1n+n))) == True{} : Bool}:
  Shared.Nat.is_le_trans(n, Stm.lower(Imp.Stm.run(body, n, size, ls, mem), n, Exp.fuel(ret, 1n+n)), Stm.fuel(body, n, size, ls, mem, Exp.fuel(ret, 1n+n)),
    Shared.Maybe.elim(Imp.Res, Imp.Stm.run(body, n, size, ls, mem),
      m => {Nat.is_le(n, Stm.lower(m, n, Exp.fuel(ret, 1n+n))) == True{} : Bool},
      x => Shared.Nat.is_le_trans(n, 1n+n, Exp.fuel(ret, 1n+n), Shared.Nat.is_le_succ(n, n, Shared.Nat.is_le_refl(n)), Exp.fuel_ge(ret, 1n+n)),
      Shared.Nat.is_le_refl(n)),
    Stm.fuel_ge(body, n, size, ls, mem, Exp.fuel(ret, 1n+n)))

# the program gives the output that its code gives in n steps; d is that run
def Prog.adds.of(d: Maybe<&2, Wasm.Halted>, +body: Imp.Stm, +ret: Imp.Exp, +n: Nat, +size: U32, +ls: List<&2, U32>,
  +mem: Wasm.Mem, +w: List<&2, Nat>, e: {Wasm.Frame.run(n, size, Wasm.Frame{Imp.Stm.code(body, [], Imp.Exp.code(ret, Wasm.Code.end{})), [], ls, mem, []}) == d : Maybe<&2, Wasm.Halted>},
  h: {Wasm.Halted.output(d, size) == Some{w} : Maybe<&2, List<&2, Nat>>}) -> {Wasm.Halted.output(Imp.Prog.ret(Imp.Stm.run(body, n, size, ls, mem), ret, size), size) == Some{w} : Maybe<&2, List<&2, Nat>>}:
  match d:
    case Some{+x}:
      Equal.trans(Maybe<&2, List<&2, Nat>>, Wasm.Halted.output(Imp.Prog.ret(Imp.Stm.run(body, n, size, ls, mem), ret, size), size), Wasm.Halted.output(Some{x}, size), Some{w},
        Equal.cong(Maybe<&2, Wasm.Halted>, Maybe<&2, List<&2, Nat>>, q => Wasm.Halted.output(q, size), Imp.Prog.ret(Imp.Stm.run(body, n, size, ls, mem), ret, size), Some{x},
          Equal.trans(Maybe<&2, Wasm.Halted>, Imp.Prog.ret(Imp.Stm.run(body, n, size, ls, mem), ret, size), Wasm.Frame.run(Stm.fuel(body, n, size, ls, mem, Exp.fuel(ret, 1n+n)), size, Wasm.Frame{Imp.Stm.code(body, [], Imp.Exp.code(ret, Wasm.Code.end{})), [], ls, mem, []}), Some{x},
            Equal.sym(Maybe<&2, Wasm.Halted>, Wasm.Frame.run(Stm.fuel(body, n, size, ls, mem, Exp.fuel(ret, 1n+n)), size, Wasm.Frame{Imp.Stm.code(body, [], Imp.Exp.code(ret, Wasm.Code.end{})), [], ls, mem, []}), Imp.Prog.ret(Imp.Stm.run(body, n, size, ls, mem), ret, size), Prog.runs(body, ret, n, size, ls, mem, n)),
            Run.up(n, Stm.fuel(body, n, size, ls, mem, Exp.fuel(ret, 1n+n)), size, Wasm.Frame{Imp.Stm.code(body, [], Imp.Exp.code(ret, Wasm.Code.end{})), [], ls, mem, []}, x, Prog.fuel_ge(body, ret, n, size, ls, mem), e))),
        h)
    case None{}:
      Empty.absurd({Wasm.Halted.output(Imp.Prog.ret(Imp.Stm.run(body, n, size, ls, mem), ret, size), size) == Some{w} : Maybe<&2, List<&2, Nat>>}, Shared.Maybe.no_none(List<&2, Nat>, w, h))

# the law, for a program with k locals, body and ret
def Prog.adds(+k: Nat, +body: Imp.Stm, +ret: Imp.Exp, +pages: Nat, +input: Maybe<&2, List<&2, Nat>>, +n: Nat,
  +w: List<&2, Nat>, h: {Wasm.Wasm.run(pages, n, Imp.Imp.compile(Imp.Prog{k, body, ret}), input) == Some{w} : Maybe<&2, List<&2, Nat>>}) ->
  {Imp.Imp.run(pages, n, Imp.Prog{k, body, ret}, input) == Some{w} : Maybe<&2, List<&2, Nat>>}:
  go = Shared.Bool.elim(Wasm.Wasm.fits(pages, input),
    ok => {Wasm.Wasm.run.of(ok, n, Wasm.Wasm.size(pages), Imp.Imp.compile(Imp.Prog{k, body, ret}), input) ==
      Some{w} : Maybe<&2, List<&2, Nat>>} ->
      {Imp.Imp.run.of(ok, n, Wasm.Wasm.size(pages), Imp.Prog{k, body, ret}, input) == Some{w} : Maybe<&2, List<&2, Nat>>},
    h1 => Prog.adds.of(Wasm.Frame.run(n, Wasm.Wasm.size(pages),
        Wasm.Frame{Imp.Stm.code(body, [], Imp.Exp.code(ret, Wasm.Code.end{})), [], Wasm.Locals.zero(k),
          Wasm.Input.mem(input), []}),
      body, ret, n, Wasm.Wasm.size(pages), Wasm.Locals.zero(k), Wasm.Input.mem(input), w, {==}, h1),
    h1 => Empty.absurd({None{} == Some{w} : Maybe<&2, List<&2, Nat>>}, Shared.Maybe.no_none(List<&2, Nat>, w, h1)))
  go(h)

def Spec.compile_adds_none(p, pages, input, n, w, h):
  match p:
    case Imp.Prog{k, body, ret}:
      Prog.adds(k, body, ret, pages, input, n, w, h)
