import Base
import ../shared/impl.bend as Shared
import ../wasm/impl.bend as Wasm
import ../imp/impl.bend as Imp
import ../fun/impl.bend as Fun
import ../fun/proof.bend as FP
import ../word/impl.bend as WD
import ../word/proof.bend as WP
import ../machine/proof.bend as MP
import ./impl.bend as RT
import ./spec.bend as Spec

# Proof of the run time
# =====================
#
# A pass of the run time's main loop makes one step of the abstract machine.
# Rd(mem, hp, p, v) states that the memory holds the value v at the address
# p, below hp. A pass stores only at hp and above, so each value that the
# memory held stays; the new nodes go below the new hp.

# Bools and numbers
# =================

def And.l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def And.r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Shared.Bool.absurd({b == True{} : Bool}, h)

def And.mk(a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def Nat.lt_add(a: Nat, +d: Nat) -> {Nat.is_lt(Nat.add(a, d), a) == False{} : Bool}:
  match a:
    case 0n:
      MP.Nat.is_lt_zero(d)
    case 1n+p:
      Nat.lt_add(p, d)

def Nat.sub_add(a: Nat, b: Nat, h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.add(Nat.sub(a, b), b) == a : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Shared.Bool.absurd({Nat.add(0n, 1n+q) == 0n : Nat}, h)
    case 1n+p 0n:
      MP.Nat.add_zero(1n+p)
    case 1n++p 1n++q:
      %Equal.sym(Nat, Nat.add(Nat.sub(p, q), 1n+q), 1n+Nat.add(Nat.sub(p, q), q), MP.Nat.add_succ(Nat.sub(p, q), q)) :
        {_ == 1n+p : Nat}
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(Nat.sub(p, q), q), p, Nat.sub_add(p, q, h))

def Nat.sub_le(a: Nat, b: Nat) -> {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Shared.Nat.is_le_refl(1n+p)
    case 1n++p 1n++q:
      Shared.Nat.is_le_succ(Nat.sub(p, q), p, Nat.sub_le(p, q))

# i32s
# ====

# x fits in an i32 when it is at most an i32
def Fits.sum(+x: Nat, +u: U32, h: {Nat.is_le(x, U32.to_nat(u)) == True{} : Bool}) ->
  WD.Fits(Nat.add(Nat.sub(U32.to_nat(u), x), x)):
  %Equal.sym(Nat, Nat.add(Nat.sub(U32.to_nat(u), x), x), U32.to_nat(u), Nat.sub_add(U32.to_nat(u), x, h)) :
    WD.Fits(_)
  WP.Fits.to_nat(u)

def Fits.le(+x: Nat, +u: U32, h: {Nat.is_le(x, U32.to_nat(u)) == True{} : Bool}) -> WD.Fits(x):
  WP.Fits.down(Nat.sub(U32.to_nat(u), x), x, Fits.sum(x, u, h))

def U.add_eq(+a: U32, +b: U32) -> {U32.from_nat(Nat.add(U32.to_nat(a), U32.to_nat(b))) == U32.add(a, b) : U32}:
  %U32.add_comm(b, a) : {U32.from_nat(Nat.add(U32.to_nat(a), U32.to_nat(b))) == _ : U32}
  %WP.U.from_to_nat(b) : {U32.from_nat(Nat.add(U32.to_nat(a), U32.to_nat(b))) == U32.add(_, a) : U32}
  %WP.U.from_to_nat(a) : {U32.from_nat(Nat.add(U32.to_nat(a), U32.to_nat(b))) == U32.add(U32.from_nat(U32.to_nat(b)), _) : U32}
  WP.U.from_nat_add(U32.to_nat(a), U32.to_nat(b))

# the sum of two i32s, when it fits
def U.add_nat(+a: U32, +b: U32, h: WD.Fits(Nat.add(U32.to_nat(a), U32.to_nat(b)))) ->
  {U32.to_nat(U32.add(a, b)) == Nat.add(U32.to_nat(a), U32.to_nat(b)) : Nat}:
  %U.add_eq(a, b) : {U32.to_nat(_) == Nat.add(U32.to_nat(a), U32.to_nat(b)) : Nat}
  h

# the difference of two i32s, when it is not below 0
def U.sub_nat(+a: U32, +b: U32, h: {Nat.is_le(U32.to_nat(b), U32.to_nat(a)) == True{} : Bool}) ->
  {U32.to_nat(U32.sub(a, b)) == Nat.sub(U32.to_nat(a), U32.to_nat(b)) : Nat}:
  +d = Nat.sub(U32.to_nat(a), U32.to_nat(b))
  +e = Nat.sub_add(U32.to_nat(a), U32.to_nat(b), h)
  %WP.U.from_to_nat(a) : {U32.to_nat(U32.sub(_, b)) == d : Nat}
  %e : {U32.to_nat(U32.sub(U32.from_nat(_), b)) == d : Nat}
  %WP.U.from_to_nat(b) : {U32.to_nat(U32.sub(U32.from_nat(Nat.add(d, U32.to_nat(b))), _)) == d : Nat}
  %Equal.sym(U32, U32.from_nat(Nat.add(d, U32.to_nat(b))), U32.add(U32.from_nat(U32.to_nat(b)), U32.from_nat(d)),
    WP.U.from_nat_add(d, U32.to_nat(b))) :
    {U32.to_nat(U32.sub(_, U32.from_nat(U32.to_nat(b)))) == d : Nat}
  %U32.add_comm(U32.from_nat(d), U32.from_nat(U32.to_nat(b))) :
    {U32.to_nat(U32.sub(_, U32.from_nat(U32.to_nat(b)))) == d : Nat}
  %Equal.sym(U32, U32.sub(U32.add(U32.from_nat(d), U32.from_nat(U32.to_nat(b))), U32.from_nat(U32.to_nat(b))),
    U32.from_nat(d), WP.U.sub_add(U32.from_nat(d), U32.from_nat(U32.to_nat(b)))) : {U32.to_nat(_) == d : Nat}
  Fits.le(d, a, Nat.sub_le(U32.to_nat(a), U32.to_nat(b)))

# Addresses
# =========

def Addr.pick(x: Bool, y: Bool, z: Bool, -s: Maybe<&2, U32>, hx: {x == False{} : Bool}, hy: {y == False{} : Bool},
  hz: {z == True{} : Bool}) ->
  {Bool.pick(Maybe<&2, U32>, Bool.and(Bool.and(Bool.not(x), Bool.not(y)), z), s, None{}) == s : Maybe<&2, U32>}:
  %Equal.sym(Bool, x, False{}, hx) :
    {Bool.pick(Maybe<&2, U32>, Bool.and(Bool.and(Bool.not(_), Bool.not(y)), z), s, None{}) == s : Maybe<&2, U32>}
  %Equal.sym(Bool, y, False{}, hy) :
    {Bool.pick(Maybe<&2, U32>, Bool.and(Bool.and(True{}, Bool.not(_)), z), s, None{}) == s : Maybe<&2, U32>}
  %Equal.sym(Bool, z, True{}, hz) :
    {Bool.pick(Maybe<&2, U32>, Bool.and(Bool.and(True{}, True{}), _), s, None{}) == s : Maybe<&2, U32>}
  {==}

def Addr.lt(+a: U32, +b: U32, +d: Nat, +e: {U32.to_nat(a) == Nat.add(U32.to_nat(b), d) : Nat}) ->
  {Cmp.is_lt(U32.cmp(a, b)) == False{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), WP.U.cmp(a, b)) :
    {Cmp.is_lt(_) == False{} : Bool}
  %Equal.sym(Nat, U32.to_nat(a), Nat.add(U32.to_nat(b), d), e) : {Cmp.is_lt(Nat.cmp(_, U32.to_nat(b))) == False{} : Bool}
  Nat.lt_add(U32.to_nat(b), d)

# the address a + off of an access of n bytes that ends within size
def Addr(+a: U32, +off: U32, +n: U32, +size: U32,
  +h: {Nat.is_le(Nat.add(Nat.add(U32.to_nat(a), U32.to_nat(off)), U32.to_nat(n)), U32.to_nat(size)) == True{} : Bool}) ->
  {Wasm.Mem.addr(a, off, n, size) == Some{U32.add(a, off)} : Maybe<&2, U32>}:
  +ao = Nat.add(U32.to_nat(a), U32.to_nat(off))
  +e1 = U.add_nat(a, off, Fits.le(ao, size,
    Shared.Nat.is_le_trans(ao, Nat.add(ao, U32.to_nat(n)), U32.to_nat(size), Shared.Nat.is_le_add(ao, U32.to_nat(n)), h)))
  +e2 = U.add_nat(U32.add(a, off), n,
    %Equal.sym(Nat, U32.to_nat(U32.add(a, off)), ao, e1) : WD.Fits(Nat.add(_, U32.to_nat(n)))
    Fits.le(Nat.add(ao, U32.to_nat(n)), size, h))
  Addr.pick(Cmp.is_lt(U32.cmp(U32.add(a, off), a)), Cmp.is_lt(U32.cmp(U32.add(U32.add(a, off), n), U32.add(a, off))),
    Cmp.is_le(U32.cmp(U32.add(U32.add(a, off), n), size)), Some{U32.add(a, off)},
    Addr.lt(U32.add(a, off), a, U32.to_nat(off), e1),
    Addr.lt(U32.add(U32.add(a, off), n), U32.add(a, off), U32.to_nat(n), e2),
    %Equal.sym(Cmp, U32.cmp(U32.add(U32.add(a, off), n), size),
      Nat.cmp(U32.to_nat(U32.add(U32.add(a, off), n)), U32.to_nat(size)), WP.U.cmp(U32.add(U32.add(a, off), n), size)) :
      {Cmp.is_le(_) == True{} : Bool}
    %Equal.sym(Nat, U32.to_nat(U32.add(U32.add(a, off), n)), Nat.add(U32.to_nat(U32.add(a, off)), U32.to_nat(n)), e2) :
      {Cmp.is_le(Nat.cmp(_, U32.to_nat(size))) == True{} : Bool}
    %Equal.sym(Nat, U32.to_nat(U32.add(a, off)), ao, e1) :
      {Cmp.is_le(Nat.cmp(Nat.add(_, U32.to_nat(n)), U32.to_nat(size))) == True{} : Bool}
    h)

# Statements
# ==========
#
# The run of each kind of statement, from the values of its expressions.

def R.seq(+a: Imp.Stm, +b: Imp.Stm, +n: Nat, +size: U32, +ls: List<&2, U32>, +mem: Wasm.Mem, +ls2: List<&2, U32>,
  +mem2: Wasm.Mem, -r: Maybe<&2, Imp.Res>,
  ha: {Imp.Stm.run(a, n, size, ls, mem) == Some{Imp.Res.next{ls2, mem2}} : Maybe<&2, Imp.Res>},
  hb: {Imp.Stm.run(b, n, size, ls2, mem2) == r : Maybe<&2, Imp.Res>}) ->
  {Imp.Stm.run(Imp.Stm.seq{a, b}, n, size, ls, mem) == r : Maybe<&2, Imp.Res>}:
  %Equal.sym(Maybe<&2, Imp.Res>, Imp.Stm.run(a, n, size, ls, mem), Some{Imp.Res.next{ls2, mem2}}, ha) :
    {Imp.Res.then(_, x => y => Imp.Stm.run(b, n, size, x, y)) == r : Maybe<&2, Imp.Res>}
  hb

# whether r went on
def R.goes(r: Maybe<&2, Imp.Res>) -> Bool:
  match r:
    case Some{Imp.Res.next{ls, mem}}:
      True{}
    case _:
      False{}

def R.then_end(+r: Maybe<&2, Imp.Res>, go: List<&2, U32> -> Wasm.Mem -> Maybe<&2, Imp.Res>,
  hr: {R.goes(r) == False{} : Bool}) -> {Imp.Res.then(r, go) == r : Maybe<&2, Imp.Res>}:
  match r:
    case Some{Imp.Res.next{ls, mem}}:
      Shared.Bool.absurd({Imp.Res.then(Some{Imp.Res.next{ls, mem}}, go) == Some{Imp.Res.next{ls, mem}} : Maybe<&2, Imp.Res>},
        Equal.sym(Bool, True{}, False{}, hr))
    case Some{Imp.Res.brk{l, ls, mem}}:
      {==}
    case Some{Imp.Res.trap{}}:
      {==}
    case None{}:
      {==}

# a statement that does not go on ends its sequence
def R.seq_end(+a: Imp.Stm, +b: Imp.Stm, +n: Nat, +size: U32, +ls: List<&2, U32>, +mem: Wasm.Mem,
  +r: Maybe<&2, Imp.Res>, hr: {R.goes(r) == False{} : Bool},
  ha: {Imp.Stm.run(a, n, size, ls, mem) == r : Maybe<&2, Imp.Res>}) ->
  {Imp.Stm.run(Imp.Stm.seq{a, b}, n, size, ls, mem) == r : Maybe<&2, Imp.Res>}:
  %Equal.sym(Maybe<&2, Imp.Res>, Imp.Stm.run(a, n, size, ls, mem), r, ha) :
    {Imp.Res.then(_, x => y => Imp.Stm.run(b, n, size, x, y)) == r : Maybe<&2, Imp.Res>}
  R.then_end(r, x => y => Imp.Stm.run(b, n, size, x, y), hr)

def R.set(+i: Nat, +e: Imp.Exp, +n: Nat, +size: U32, +ls: List<&2, U32>, +mem: Wasm.Mem, +v: U32,
  +ls2: List<&2, U32>, he: {Imp.Exp.eval(e, size, ls, mem) == Some{v} : Maybe<&2, U32>},
  hp: {Wasm.List.put(ls, i, v) == Some{ls2} : Maybe<&2, List<&2, U32>>}) ->
  {Imp.Stm.run(Imp.Stm.set{i, e}, n, size, ls, mem) == Some{Imp.Res.next{ls2, mem}} : Maybe<&2, Imp.Res>}:
  %Equal.sym(Maybe<&2, U32>, Imp.Exp.eval(e, size, ls, mem), Some{v}, he) :
    {Some{Imp.Stm.set(_, i, ls, mem)} == Some{Imp.Res.next{ls2, mem}} : Maybe<&2, Imp.Res>}
  %Equal.sym(Maybe<&2, List<&2, U32>>, Wasm.List.put(ls, i, v), Some{ls2}, hp) :
    {Some{Imp.Stm.set.of(_, mem)} == Some{Imp.Res.next{ls2, mem}} : Maybe<&2, Imp.Res>}
  {==}

def R.store(+off: U32, +a: Imp.Exp, +x: Imp.Exp, +n: Nat, +size: U32, +ls: List<&2, U32>, +mem: Wasm.Mem,
  +pa: U32, +vx: U32, +ea: U32, ha: {Imp.Exp.eval(a, size, ls, mem) == Some{pa} : Maybe<&2, U32>},
  hx: {Imp.Exp.eval(x, size, ls, mem) == Some{vx} : Maybe<&2, U32>},
  hd: {Wasm.Mem.addr(pa, off, 4, size) == Some{ea} : Maybe<&2, U32>}) ->
  {Imp.Stm.run(Imp.Stm.store{off, a, x}, n, size, ls, mem) == Some{Imp.Res.next{ls, Wasm.Mem.store(ea, mem, vx)}} :
    Maybe<&2, Imp.Res>}:
  %Equal.sym(Maybe<&2, U32>, Imp.Exp.eval(a, size, ls, mem), Some{pa}, ha) :
    {Some{Imp.Stm.store(_, Imp.Exp.eval(x, size, ls, mem), off, 4, size, p => m => y => Wasm.Mem.store(p, m, y), ls, mem)} ==
      Some{Imp.Res.next{ls, Wasm.Mem.store(ea, mem, vx)}} : Maybe<&2, Imp.Res>}
  %Equal.sym(Maybe<&2, U32>, Imp.Exp.eval(x, size, ls, mem), Some{vx}, hx) :
    {Some{Imp.Stm.store(Some{pa}, _, off, 4, size, p => m => y => Wasm.Mem.store(p, m, y), ls, mem)} ==
      Some{Imp.Res.next{ls, Wasm.Mem.store(ea, mem, vx)}} : Maybe<&2, Imp.Res>}
  %Equal.sym(Maybe<&2, U32>, Wasm.Mem.addr(pa, off, 4, size), Some{ea}, hd) :
    {Some{Imp.Stm.store.at(_, vx, p => m => y => Wasm.Mem.store(p, m, y), ls, mem)} ==
      Some{Imp.Res.next{ls, Wasm.Mem.store(ea, mem, vx)}} : Maybe<&2, Imp.Res>}
  {==}

def R.store8(+off: U32, +a: Imp.Exp, +x: Imp.Exp, +n: Nat, +size: U32, +ls: List<&2, U32>, +mem: Wasm.Mem,
  +pa: U32, +vx: U32, +ea: U32, ha: {Imp.Exp.eval(a, size, ls, mem) == Some{pa} : Maybe<&2, U32>},
  hx: {Imp.Exp.eval(x, size, ls, mem) == Some{vx} : Maybe<&2, U32>},
  hd: {Wasm.Mem.addr(pa, off, 1, size) == Some{ea} : Maybe<&2, U32>}) ->
  {Imp.Stm.run(Imp.Stm.store8{off, a, x}, n, size, ls, mem) ==
    Some{Imp.Res.next{ls, Wasm.Mem.set_at(ea, mem, Wasm.U32.low(vx))}} : Maybe<&2, Imp.Res>}:
  %Equal.sym(Maybe<&2, U32>, Imp.Exp.eval(a, size, ls, mem), Some{pa}, ha) :
    {Some{Imp.Stm.store(_, Imp.Exp.eval(x, size, ls, mem), off, 1, size,
      p => m => y => Wasm.Mem.set_at(p, m, Wasm.U32.low(y)), ls, mem)} ==
      Some{Imp.Res.next{ls, Wasm.Mem.set_at(ea, mem, Wasm.U32.low(vx))}} : Maybe<&2, Imp.Res>}
  %Equal.sym(Maybe<&2, U32>, Imp.Exp.eval(x, size, ls, mem), Some{vx}, hx) :
    {Some{Imp.Stm.store(Some{pa}, _, off, 1, size, p => m => y => Wasm.Mem.set_at(p, m, Wasm.U32.low(y)), ls, mem)} ==
      Some{Imp.Res.next{ls, Wasm.Mem.set_at(ea, mem, Wasm.U32.low(vx))}} : Maybe<&2, Imp.Res>}
  %Equal.sym(Maybe<&2, U32>, Wasm.Mem.addr(pa, off, 1, size), Some{ea}, hd) :
    {Some{Imp.Stm.store.at(_, vx, p => m => y => Wasm.Mem.set_at(p, m, Wasm.U32.low(y)), ls, mem)} ==
      Some{Imp.Res.next{ls, Wasm.Mem.set_at(ea, mem, Wasm.U32.low(vx))}} : Maybe<&2, Imp.Res>}
  {==}

def R.if(+c: Imp.Exp, +s1: Imp.Stm, +s2: Imp.Stm, +n: Nat, +size: U32, +ls: List<&2, U32>, +mem: Wasm.Mem,
  +v: U32, +b: Bool, -r: Maybe<&2, Imp.Res>, hc: {Imp.Exp.eval(c, size, ls, mem) == Some{v} : Maybe<&2, U32>},
  hv: {U32.is_ne(v, 0) == b : Bool},
  h: {Imp.Stm.if.of(b, u => Imp.Stm.run(s1, n, size, ls, mem), u => Imp.Stm.run(s2, n, size, ls, mem)) == r :
    Maybe<&2, Imp.Res>}) ->
  {Imp.Stm.run(Imp.Stm.if{c, s1, s2}, n, size, ls, mem) == r : Maybe<&2, Imp.Res>}:
  %Equal.sym(Maybe<&2, U32>, Imp.Exp.eval(c, size, ls, mem), Some{v}, hc) :
    {Imp.Stm.if(_, u => Imp.Stm.run(s1, n, size, ls, mem), u => Imp.Stm.run(s2, n, size, ls, mem)) == r :
      Maybe<&2, Imp.Res>}
  %Equal.sym(Bool, U32.is_ne(v, 0), b, hv) :
    {Imp.Stm.if.of(_, u => Imp.Stm.run(s1, n, size, ls, mem), u => Imp.Stm.run(s2, n, size, ls, mem)) == r :
      Maybe<&2, Imp.Res>}
  h

# Expressions
# ===========

def E.load(+off: U32, +a: Imp.Exp, +size: U32, +ls: List<&2, U32>, +mem: Wasm.Mem, +pa: U32, +ea: U32,
  ha: {Imp.Exp.eval(a, size, ls, mem) == Some{pa} : Maybe<&2, U32>},
  hd: {Wasm.Mem.addr(pa, off, 4, size) == Some{ea} : Maybe<&2, U32>}) ->
  {Imp.Exp.eval(Imp.Exp.load{off, a}, size, ls, mem) == Some{Wasm.Mem.load(ea, mem)} : Maybe<&2, U32>}:
  %Equal.sym(Maybe<&2, U32>, Imp.Exp.eval(a, size, ls, mem), Some{pa}, ha) :
    {Imp.Exp.eval.load(_, off, 4, size, mem, x => m => Wasm.Mem.load(x, m)) == Some{Wasm.Mem.load(ea, mem)} :
      Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, Wasm.Mem.addr(pa, off, 4, size), Some{ea}, hd) :
    {Imp.Exp.eval.at(_, mem, x => m => Wasm.Mem.load(x, m)) == Some{Wasm.Mem.load(ea, mem)} : Maybe<&2, U32>}
  {==}

def E.bin(+o: Wasm.Bin, +a: Imp.Exp, +b: Imp.Exp, +size: U32, +ls: List<&2, U32>, +mem: Wasm.Mem, +va: U32, +vb: U32,
  ha: {Imp.Exp.eval(a, size, ls, mem) == Some{va} : Maybe<&2, U32>},
  hb: {Imp.Exp.eval(b, size, ls, mem) == Some{vb} : Maybe<&2, U32>}) ->
  {Imp.Exp.eval(Imp.Exp.bin{o, a, b}, size, ls, mem) == Some{Wasm.Bin.apply(o, va, vb)} : Maybe<&2, U32>}:
  %Equal.sym(Maybe<&2, U32>, Imp.Exp.eval(a, size, ls, mem), Some{va}, ha) :
    {Imp.Exp.eval.bin(o, _, Imp.Exp.eval(b, size, ls, mem)) == Some{Wasm.Bin.apply(o, va, vb)} : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, Imp.Exp.eval(b, size, ls, mem), Some{vb}, hb) :
    {Imp.Exp.eval.bin(o, Some{va}, _) == Some{Wasm.Bin.apply(o, va, vb)} : Maybe<&2, U32>}
  {==}

# Values in the memory
# ====================

# whether the memory holds v at p, below hp: z is 0; a node {t, a, b} is
# three words at p, its tag and the addresses of a and b
def Rd(v: Fun.V, +mem: Wasm.Mem, +hp: Nat, +p: U32) -> Bool:
  match v:
    case Fun.V.z{}:
      Nat.is_eq(U32.to_nat(p), 0n)
    case Fun.V.n{t, a, b}:
      Bool.and(Nat.is_le(1n, U32.to_nat(p)), Bool.and(Nat.is_le(12n+U32.to_nat(p), hp),
        Bool.and(Nat.is_eq(U32.to_nat(Wasm.Mem.load(p, mem)), t),
          Bool.and(Rd(a, mem, hp, Wasm.Mem.load(U32.add(p, 4), mem)), Rd(b, mem, hp, Wasm.Mem.load(U32.add(p, 8), mem))))))

def Rd.n3(+mem: Wasm.Mem, +hp: Nat, +p: U32, a: Fun.V, b: Fun.V) -> Bool:
  Bool.and(Rd(a, mem, hp, Wasm.Mem.load(U32.add(p, 4), mem)), Rd(b, mem, hp, Wasm.Mem.load(U32.add(p, 8), mem)))

def Rd.n2(+mem: Wasm.Mem, +hp: Nat, +p: U32, t: Nat, a: Fun.V, b: Fun.V) -> Bool:
  Bool.and(Nat.is_eq(U32.to_nat(Wasm.Mem.load(p, mem)), t), Rd.n3(mem, hp, p, a, b))

def Rd.n1(+mem: Wasm.Mem, +hp: Nat, +p: U32, t: Nat, a: Fun.V, b: Fun.V) -> Bool:
  Bool.and(Nat.is_le(12n+U32.to_nat(p), hp), Rd.n2(mem, hp, p, t, a, b))

def Rd.nz(+mem: Wasm.Mem, +hp: Nat, +p: U32, +t: Nat, +a: Fun.V, +b: Fun.V,
  h: {Rd(Fun.V.n{t, a, b}, mem, hp, p) == True{} : Bool}) -> {Nat.is_le(1n, U32.to_nat(p)) == True{} : Bool}:
  And.l(Nat.is_le(1n, U32.to_nat(p)), Rd.n1(mem, hp, p, t, a, b), h)

def Rd.hi(+mem: Wasm.Mem, +hp: Nat, +p: U32, +t: Nat, +a: Fun.V, +b: Fun.V,
  h: {Rd(Fun.V.n{t, a, b}, mem, hp, p) == True{} : Bool}) -> {Nat.is_le(12n+U32.to_nat(p), hp) == True{} : Bool}:
  And.l(Nat.is_le(12n+U32.to_nat(p), hp), Rd.n2(mem, hp, p, t, a, b),
    And.r(Nat.is_le(1n, U32.to_nat(p)), Rd.n1(mem, hp, p, t, a, b), h))

def Rd.tag(+mem: Wasm.Mem, +hp: Nat, +p: U32, +t: Nat, +a: Fun.V, +b: Fun.V,
  h: {Rd(Fun.V.n{t, a, b}, mem, hp, p) == True{} : Bool}) -> {Nat.is_eq(U32.to_nat(Wasm.Mem.load(p, mem)), t) == True{} : Bool}:
  And.l(Nat.is_eq(U32.to_nat(Wasm.Mem.load(p, mem)), t), Rd.n3(mem, hp, p, a, b),
    And.r(Nat.is_le(12n+U32.to_nat(p), hp), Rd.n2(mem, hp, p, t, a, b),
      And.r(Nat.is_le(1n, U32.to_nat(p)), Rd.n1(mem, hp, p, t, a, b), h)))

def Rd.n3_of(+mem: Wasm.Mem, +hp: Nat, +p: U32, +t: Nat, +a: Fun.V, +b: Fun.V,
  h: {Rd(Fun.V.n{t, a, b}, mem, hp, p) == True{} : Bool}) -> {Rd.n3(mem, hp, p, a, b) == True{} : Bool}:
  And.r(Nat.is_eq(U32.to_nat(Wasm.Mem.load(p, mem)), t), Rd.n3(mem, hp, p, a, b),
    And.r(Nat.is_le(12n+U32.to_nat(p), hp), Rd.n2(mem, hp, p, t, a, b),
      And.r(Nat.is_le(1n, U32.to_nat(p)), Rd.n1(mem, hp, p, t, a, b), h)))

def Rd.a(+mem: Wasm.Mem, +hp: Nat, +p: U32, +t: Nat, +a: Fun.V, +b: Fun.V,
  h: {Rd(Fun.V.n{t, a, b}, mem, hp, p) == True{} : Bool}) ->
  {Rd(a, mem, hp, Wasm.Mem.load(U32.add(p, 4), mem)) == True{} : Bool}:
  And.l(Rd(a, mem, hp, Wasm.Mem.load(U32.add(p, 4), mem)), Rd(b, mem, hp, Wasm.Mem.load(U32.add(p, 8), mem)),
    Rd.n3_of(mem, hp, p, t, a, b, h))

def Rd.b(+mem: Wasm.Mem, +hp: Nat, +p: U32, +t: Nat, +a: Fun.V, +b: Fun.V,
  h: {Rd(Fun.V.n{t, a, b}, mem, hp, p) == True{} : Bool}) ->
  {Rd(b, mem, hp, Wasm.Mem.load(U32.add(p, 8), mem)) == True{} : Bool}:
  And.r(Rd(a, mem, hp, Wasm.Mem.load(U32.add(p, 4), mem)), Rd(b, mem, hp, Wasm.Mem.load(U32.add(p, 8), mem)),
    Rd.n3_of(mem, hp, p, t, a, b, h))

def Rd.mk(+mem: Wasm.Mem, +hp: Nat, +p: U32, +t: Nat, +a: Fun.V, +b: Fun.V,
  h1: {Nat.is_le(1n, U32.to_nat(p)) == True{} : Bool}, h2: {Nat.is_le(12n+U32.to_nat(p), hp) == True{} : Bool},
  h3: {Nat.is_eq(U32.to_nat(Wasm.Mem.load(p, mem)), t) == True{} : Bool},
  h4: {Rd(a, mem, hp, Wasm.Mem.load(U32.add(p, 4), mem)) == True{} : Bool},
  h5: {Rd(b, mem, hp, Wasm.Mem.load(U32.add(p, 8), mem)) == True{} : Bool}) ->
  {Rd(Fun.V.n{t, a, b}, mem, hp, p) == True{} : Bool}:
  And.mk(Nat.is_le(1n, U32.to_nat(p)), Rd.n1(mem, hp, p, t, a, b), h1,
    And.mk(Nat.is_le(12n+U32.to_nat(p), hp), Rd.n2(mem, hp, p, t, a, b), h2,
      And.mk(Nat.is_eq(U32.to_nat(Wasm.Mem.load(p, mem)), t), Rd.n3(mem, hp, p, a, b), h3,
        And.mk(Rd(a, mem, hp, Wasm.Mem.load(U32.add(p, 4), mem)), Rd(b, mem, hp, Wasm.Mem.load(U32.add(p, 8), mem)),
          h4, h5))))

# Nodes
# =====

def Nat.add_add(+P: Nat, +a: Nat, +b: Nat) -> {Nat.add(Nat.add(a, b), P) == Nat.add(Nat.add(P, a), b) : Nat}:
  Equal.sym(Nat, Nat.add(Nat.add(P, a), b), Nat.add(Nat.add(a, b), P),
    Equal.trans(Nat, Nat.add(Nat.add(P, a), b), Nat.add(P, Nat.add(a, b)), Nat.add(Nat.add(a, b), P),
      MP.Nat.add_assoc(P, a, b), MP.Nat.add_comm(P, Nat.add(a, b))))

def Le.t(+a: Nat, +b: Nat, +c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool}) ->
  {Nat.is_le(a, c) == True{} : Bool}:
  Shared.Nat.is_le_trans(a, b, c, h1, h2)

# the i32 p + k, for a constant k, when it fits
def U.add_lit(+p: U32, +k: U32, h: WD.Fits(Nat.add(U32.to_nat(k), U32.to_nat(p)))) ->
  {U32.to_nat(U32.add(p, k)) == Nat.add(U32.to_nat(k), U32.to_nat(p)) : Nat}:
  %MP.Nat.add_comm(U32.to_nat(p), U32.to_nat(k)) : {U32.to_nat(U32.add(p, k)) == _ : Nat}
  U.add_nat(p, k,
    %MP.Nat.add_comm(U32.to_nat(k), U32.to_nat(p)) : WD.Fits(_)
    h)

# the words of a node at p, below hp, below the end of the memory
def Ad0(+p: U32, +hp: Nat, +size: U32, +hn: {Nat.is_le(12n+U32.to_nat(p), hp) == True{} : Bool},
  +hs: {Nat.is_le(hp, U32.to_nat(size)) == True{} : Bool}) ->
  {Wasm.Mem.addr(p, 0, 4, size) == Some{p} : Maybe<&2, U32>}:
  %WP.U.add_zero(p) : {Wasm.Mem.addr(p, 0, 4, size) == Some{_} : Maybe<&2, U32>}
  Addr(p, 0, 4, size,
    %Nat.add_add(U32.to_nat(p), 0n, 4n) : {Nat.is_le(_, U32.to_nat(size)) == True{} : Bool}
    Le.t(4n+U32.to_nat(p), 12n+U32.to_nat(p), U32.to_nat(size), Shared.Nat.is_le_add_left(U32.to_nat(p), 8n),
      Le.t(12n+U32.to_nat(p), hp, U32.to_nat(size), hn, hs)))

def Ad4(+p: U32, +hp: Nat, +size: U32, +hn: {Nat.is_le(12n+U32.to_nat(p), hp) == True{} : Bool},
  +hs: {Nat.is_le(hp, U32.to_nat(size)) == True{} : Bool}) ->
  {Wasm.Mem.addr(p, 4, 4, size) == Some{U32.add(p, 4)} : Maybe<&2, U32>}:
  Addr(p, 4, 4, size,
    %Nat.add_add(U32.to_nat(p), 4n, 4n) : {Nat.is_le(_, U32.to_nat(size)) == True{} : Bool}
    Le.t(8n+U32.to_nat(p), 12n+U32.to_nat(p), U32.to_nat(size), Shared.Nat.is_le_add_left(U32.to_nat(p), 4n),
      Le.t(12n+U32.to_nat(p), hp, U32.to_nat(size), hn, hs)))

def Ad8(+p: U32, +hp: Nat, +size: U32, +hn: {Nat.is_le(12n+U32.to_nat(p), hp) == True{} : Bool},
  +hs: {Nat.is_le(hp, U32.to_nat(size)) == True{} : Bool}) ->
  {Wasm.Mem.addr(p, 8, 4, size) == Some{U32.add(p, 8)} : Maybe<&2, U32>}:
  Addr(p, 8, 4, size,
    %Nat.add_add(U32.to_nat(p), 8n, 4n) : {Nat.is_le(_, U32.to_nat(size)) == True{} : Bool}
    Le.t(12n+U32.to_nat(p), hp, U32.to_nat(size), hn, hs))

# Stores
# ======

# a load below a store reads what it read before
def Ld.far(+p: U32, +q: U32, +mem: Wasm.Mem, +x: U32, +size: U32,
  +hpq: {Nat.is_le(4n+U32.to_nat(p), U32.to_nat(q)) == True{} : Bool},
  +hq: {Nat.is_le(4n+U32.to_nat(q), U32.to_nat(size)) == True{} : Bool}) ->
  {Wasm.Mem.load(p, Wasm.Mem.store(q, mem, x)) == Wasm.Mem.load(p, mem) : U32}:
  +hqs = Le.t(U32.to_nat(q), 4n+U32.to_nat(q), U32.to_nat(size), Shared.Nat.is_le_add_left(U32.to_nat(q), 4n), hq)
  %WP.U.from_to_nat(p) : {Wasm.Mem.load(_, Wasm.Mem.store(q, mem, x)) == Wasm.Mem.load(_, mem) : U32}
  %WP.U.from_to_nat(q) :
    {Wasm.Mem.load(U32.from_nat(U32.to_nat(p)), Wasm.Mem.store(_, mem, x)) == Wasm.Mem.load(U32.from_nat(U32.to_nat(p)), mem) :
      U32}
  WP.M.load_store_lo(U32.to_nat(p), U32.to_nat(q), mem, x,
    Fits.le(3n+U32.to_nat(p), size,
      Le.t(3n+U32.to_nat(p), U32.to_nat(q), U32.to_nat(size), Shared.Nat.is_le_pred(3n+U32.to_nat(p), U32.to_nat(q), hpq), hqs)),
    Fits.le(3n+U32.to_nat(q), size, Shared.Nat.is_le_pred(3n+U32.to_nat(q), U32.to_nat(size), hq)), hpq)

# the address of the word k of a node at p (k: 4 or 8)
def Nd.at(+p: U32, +k: U32, +size: U32, +hk: {Nat.is_le(Nat.add(U32.to_nat(k), U32.to_nat(p)), U32.to_nat(size)) == True{} : Bool}) ->
  {U32.to_nat(U32.add(p, k)) == Nat.add(U32.to_nat(k), U32.to_nat(p)) : Nat}:
  U.add_lit(p, k, Fits.le(Nat.add(U32.to_nat(k), U32.to_nat(p)), size, hk))

# a load of the word k of a node below hp, after a store at hp or above
def Ld.word(+p: U32, +k: U32, +q: U32, +mem: Wasm.Mem, +x: U32, +size: U32, +hp: Nat,
  +hn: {Nat.is_le(Nat.add(Nat.add(4n, U32.to_nat(k)), U32.to_nat(p)), hp) == True{} : Bool},
  +hpq: {Nat.is_le(hp, U32.to_nat(q)) == True{} : Bool},
  +hq: {Nat.is_le(4n+U32.to_nat(q), U32.to_nat(size)) == True{} : Bool}) ->
  {Wasm.Mem.load(U32.add(p, k), Wasm.Mem.store(q, mem, x)) == Wasm.Mem.load(U32.add(p, k), mem) : U32}:
  +hqs = Le.t(U32.to_nat(q), 4n+U32.to_nat(q), U32.to_nat(size), Shared.Nat.is_le_add_left(U32.to_nat(q), 4n), hq)
  +hk = Le.t(Nat.add(U32.to_nat(k), U32.to_nat(p)), Nat.add(Nat.add(4n, U32.to_nat(k)), U32.to_nat(p)), U32.to_nat(size),
    Shared.Nat.is_le_add_left(Nat.add(U32.to_nat(k), U32.to_nat(p)), 4n), Le.t(Nat.add(Nat.add(4n, U32.to_nat(k)), U32.to_nat(p)), hp, U32.to_nat(size), hn, Le.t(hp, U32.to_nat(q), U32.to_nat(size), hpq, hqs)))
  Ld.far(U32.add(p, k), q, mem, x, size,
    %Equal.sym(Nat, U32.to_nat(U32.add(p, k)), Nat.add(U32.to_nat(k), U32.to_nat(p)), Nd.at(p, k, size, hk)) :
      {Nat.is_le(4n+_, U32.to_nat(q)) == True{} : Bool}
    Le.t(Nat.add(Nat.add(4n, U32.to_nat(k)), U32.to_nat(p)), hp, U32.to_nat(q), hn, hpq), hq)

# a store at hp or above keeps each value below hp
def Rd.store(v: Fun.V, +mem: Wasm.Mem, +hp: Nat, +p: U32, +q: U32, +x: U32, +size: U32,
  +hpq: {Nat.is_le(hp, U32.to_nat(q)) == True{} : Bool},
  +hq: {Nat.is_le(4n+U32.to_nat(q), U32.to_nat(size)) == True{} : Bool},
  +h: {Rd(v, mem, hp, p) == True{} : Bool}) ->
  {Rd(v, Wasm.Mem.store(q, mem, x), hp, p) == True{} : Bool}:
  match v:
    case Fun.V.z{}:
      h
    case Fun.V.n{+t, +a, +b}:
      +m2 = Wasm.Mem.store(q, mem, x)
      +hn = Rd.hi(mem, hp, p, t, a, b, h)
      Rd.mk(m2, hp, p, t, a, b, Rd.nz(mem, hp, p, t, a, b, h), hn,
        %Equal.sym(U32, Wasm.Mem.load(p, m2), Wasm.Mem.load(p, mem),
          Ld.far(p, q, mem, x, size,
            Le.t(4n+U32.to_nat(p), hp, U32.to_nat(q),
              Le.t(4n+U32.to_nat(p), 12n+U32.to_nat(p), hp, Shared.Nat.is_le_add_left(U32.to_nat(p), 8n), hn), hpq), hq)) :
          {Nat.is_eq(U32.to_nat(_), t) == True{} : Bool}
        Rd.tag(mem, hp, p, t, a, b, h),
        %Equal.sym(U32, Wasm.Mem.load(U32.add(p, 4), m2), Wasm.Mem.load(U32.add(p, 4), mem),
          Ld.word(p, 4, q, mem, x, size, hp,
            Le.t(8n+U32.to_nat(p), 12n+U32.to_nat(p), hp, Shared.Nat.is_le_add_left(U32.to_nat(p), 4n), hn), hpq, hq)) :
          {Rd(a, m2, hp, _) == True{} : Bool}
        Rd.store(a, mem, hp, Wasm.Mem.load(U32.add(p, 4), mem), q, x, size, hpq, hq, Rd.a(mem, hp, p, t, a, b, h)),
        %Equal.sym(U32, Wasm.Mem.load(U32.add(p, 8), m2), Wasm.Mem.load(U32.add(p, 8), mem),
          Ld.word(p, 8, q, mem, x, size, hp, hn, hpq, hq)) :
          {Rd(b, m2, hp, _) == True{} : Bool}
        Rd.store(b, mem, hp, Wasm.Mem.load(U32.add(p, 8), mem), q, x, size, hpq, hq, Rd.b(mem, hp, p, t, a, b, h)))

# a value below hp is below each hp2 above it
def Rd.up(v: Fun.V, +mem: Wasm.Mem, +hp: Nat, +hp2: Nat, +p: U32, +hle: {Nat.is_le(hp, hp2) == True{} : Bool},
  +h: {Rd(v, mem, hp, p) == True{} : Bool}) -> {Rd(v, mem, hp2, p) == True{} : Bool}:
  match v:
    case Fun.V.z{}:
      h
    case Fun.V.n{+t, +a, +b}:
      Rd.mk(mem, hp2, p, t, a, b, Rd.nz(mem, hp, p, t, a, b, h),
        Le.t(12n+U32.to_nat(p), hp, hp2, Rd.hi(mem, hp, p, t, a, b, h), hle), Rd.tag(mem, hp, p, t, a, b, h),
        Rd.up(a, mem, hp, hp2, Wasm.Mem.load(U32.add(p, 4), mem), hle, Rd.a(mem, hp, p, t, a, b, h)),
        Rd.up(b, mem, hp, hp2, Wasm.Mem.load(U32.add(p, 8), mem), hle, Rd.b(mem, hp, p, t, a, b, h)))

# Allocations
# ===========

# the memory after the node {vt, va, vb} at hp
def M3(+hp: U32, mem: Wasm.Mem, vt: U32, va: U32, vb: U32) -> Wasm.Mem:
  Wasm.Mem.store(U32.add(hp, 8), Wasm.Mem.store(U32.add(hp, 4), Wasm.Mem.store(hp, mem, vt), va), vb)

def R.alloc(+t: Imp.Exp, +a: Imp.Exp, +b: Imp.Exp, +n: Nat, +size: U32, +ls: List<&2, U32>, +mem: Wasm.Mem, +hp: U32,
  +vt: U32, +va: U32, +vb: U32, +ls1: List<&2, U32>, +ls2: List<&2, U32>,
  +hh: {Wasm.List.at(ls, 0n) == Some{hp} : Maybe<&2, U32>},
  ht: {Imp.Exp.eval(t, size, ls, mem) == Some{vt} : Maybe<&2, U32>},
  ha: {Imp.Exp.eval(a, size, ls, Wasm.Mem.store(hp, mem, vt)) == Some{va} : Maybe<&2, U32>},
  hb: {Imp.Exp.eval(b, size, ls, Wasm.Mem.store(U32.add(hp, 4), Wasm.Mem.store(hp, mem, vt), va)) == Some{vb} :
    Maybe<&2, U32>},
  +hr: {Nat.is_le(12n+U32.to_nat(hp), U32.to_nat(size)) == True{} : Bool},
  h17: {Wasm.List.put(ls, 17n, hp) == Some{ls1} : Maybe<&2, List<&2, U32>>},
  hh1: {Wasm.List.at(ls1, 0n) == Some{hp} : Maybe<&2, U32>},
  h0: {Wasm.List.put(ls1, 0n, U32.add(hp, 12)) == Some{ls2} : Maybe<&2, List<&2, U32>>}) ->
  {Imp.Stm.run(RT.S.alloc(t, a, b), n, size, ls, mem) == Some{Imp.Res.next{ls2, M3(hp, mem, vt, va, vb)}} :
    Maybe<&2, Imp.Res>}:
  +m1 = Wasm.Mem.store(hp, mem, vt)
  +m2 = Wasm.Mem.store(U32.add(hp, 4), m1, va)
  +m3 = M3(hp, mem, vt, va, vb)
  +r = {Some{Imp.Res.next{ls2, m3}} : Maybe<&2, Imp.Res>}
  +H = {12n+U32.to_nat(hp) : Nat}
  +hl = Shared.Nat.is_le_refl(H)
  +s5 = RT.S.all([Imp.Stm.set{0n, RT.E.add(RT.E.l(0n), RT.E.k(12))}])
  +s4 = RT.S.all([Imp.Stm.set{17n, RT.E.l(0n)}, Imp.Stm.set{0n, RT.E.add(RT.E.l(0n), RT.E.k(12))}])
  +s3 = RT.S.all([Imp.Stm.store{8, RT.E.l(0n), b}, Imp.Stm.set{17n, RT.E.l(0n)},
    Imp.Stm.set{0n, RT.E.add(RT.E.l(0n), RT.E.k(12))}])
  +s2 = RT.S.all([Imp.Stm.store{4, RT.E.l(0n), a}, Imp.Stm.store{8, RT.E.l(0n), b}, Imp.Stm.set{17n, RT.E.l(0n)},
    Imp.Stm.set{0n, RT.E.add(RT.E.l(0n), RT.E.k(12))}])
  R.seq(Imp.Stm.store{0, RT.E.l(0n), t}, s2, n, size, ls, mem, ls, m1, r,
    R.store(0, RT.E.l(0n), t, n, size, ls, mem, hp, vt, hp, hh, ht, Ad0(hp, H, size, hl, hr)),
    R.seq(Imp.Stm.store{4, RT.E.l(0n), a}, s3, n, size, ls, m1, ls, m2, r,
      R.store(4, RT.E.l(0n), a, n, size, ls, m1, hp, va, U32.add(hp, 4), hh, ha, Ad4(hp, H, size, hl, hr)),
      R.seq(Imp.Stm.store{8, RT.E.l(0n), b}, s4, n, size, ls, m2, ls, m3, r,
        R.store(8, RT.E.l(0n), b, n, size, ls, m2, hp, vb, U32.add(hp, 8), hh, hb, Ad8(hp, H, size, hl, hr)),
        R.seq(Imp.Stm.set{17n, RT.E.l(0n)}, s5, n, size, ls, m3, ls1, m3, r,
          R.set(17n, RT.E.l(0n), n, size, ls, m3, hp, ls1, hh, h17),
          R.seq(Imp.Stm.set{0n, RT.E.add(RT.E.l(0n), RT.E.k(12))}, Imp.Stm.skip{}, n, size, ls1, m3, ls2, m3, r,
            R.set(0n, RT.E.add(RT.E.l(0n), RT.E.k(12)), n, size, ls1, m3, U32.add(hp, 12), ls2,
              E.bin(Wasm.Bin.add{}, RT.E.l(0n), RT.E.k(12), size, ls1, m3, hp, 12, hh1, {==}), h0),
            {==})))))

# a load of the word just stored
def Ld.same(+p: U32, +mem: Wasm.Mem, +x: U32, +size: U32,
  +h: {Nat.is_le(4n+U32.to_nat(p), U32.to_nat(size)) == True{} : Bool}) ->
  {Wasm.Mem.load(p, Wasm.Mem.store(p, mem, x)) == x : U32}:
  %WP.U.from_to_nat(p) : {Wasm.Mem.load(_, Wasm.Mem.store(_, mem, x)) == x : U32}
  WP.M.load_store(U32.to_nat(p), mem, x,
    Fits.le(3n+U32.to_nat(p), size, Shared.Nat.is_le_pred(3n+U32.to_nat(p), U32.to_nat(size), h)))

def Le.k4(+hp: U32, +size: U32, +hr: {Nat.is_le(12n+U32.to_nat(hp), U32.to_nat(size)) == True{} : Bool}) ->
  {Nat.is_le(4n+U32.to_nat(hp), U32.to_nat(size)) == True{} : Bool}:
  Le.t(4n+U32.to_nat(hp), 12n+U32.to_nat(hp), U32.to_nat(size), Shared.Nat.is_le_add_left(U32.to_nat(hp), 8n), hr)

def Le.k8(+hp: U32, +size: U32, +hr: {Nat.is_le(12n+U32.to_nat(hp), U32.to_nat(size)) == True{} : Bool}) ->
  {Nat.is_le(8n+U32.to_nat(hp), U32.to_nat(size)) == True{} : Bool}:
  Le.t(8n+U32.to_nat(hp), 12n+U32.to_nat(hp), U32.to_nat(size), Shared.Nat.is_le_add_left(U32.to_nat(hp), 4n), hr)

def T4(+hp: U32, +size: U32, +hr: {Nat.is_le(12n+U32.to_nat(hp), U32.to_nat(size)) == True{} : Bool}) ->
  {U32.to_nat(U32.add(hp, 4)) == 4n+U32.to_nat(hp) : Nat}:
  Nd.at(hp, 4, size, Le.k4(hp, size, hr))

def T8(+hp: U32, +size: U32, +hr: {Nat.is_le(12n+U32.to_nat(hp), U32.to_nat(size)) == True{} : Bool}) ->
  {U32.to_nat(U32.add(hp, 8)) == 8n+U32.to_nat(hp) : Nat}:
  Nd.at(hp, 8, size, Le.k8(hp, size, hr))

# the words of the node just stored
def Ld.n0(+hp: U32, +mem: Wasm.Mem, +vt: U32, +va: U32, +vb: U32, +size: U32,
  +hr: {Nat.is_le(12n+U32.to_nat(hp), U32.to_nat(size)) == True{} : Bool}) ->
  {Wasm.Mem.load(hp, M3(hp, mem, vt, va, vb)) == vt : U32}:
  +m1 = Wasm.Mem.store(hp, mem, vt)
  +m2 = Wasm.Mem.store(U32.add(hp, 4), m1, va)
  +P = U32.to_nat(hp)
  +S = U32.to_nat(size)
  Equal.trans(U32, Wasm.Mem.load(hp, M3(hp, mem, vt, va, vb)), Wasm.Mem.load(hp, m2), vt,
    Ld.far(hp, U32.add(hp, 8), m2, vb, size,
      %Equal.sym(Nat, U32.to_nat(U32.add(hp, 8)), 8n+P, T8(hp, size, hr)) : {Nat.is_le(4n+P, _) == True{} : Bool}
      Shared.Nat.is_le_add_left(P, 4n),
      %Equal.sym(Nat, U32.to_nat(U32.add(hp, 8)), 8n+P, T8(hp, size, hr)) : {Nat.is_le(4n+_, S) == True{} : Bool}
      hr),
    Equal.trans(U32, Wasm.Mem.load(hp, m2), Wasm.Mem.load(hp, m1), vt,
      Ld.far(hp, U32.add(hp, 4), m1, va, size,
        %Equal.sym(Nat, U32.to_nat(U32.add(hp, 4)), 4n+P, T4(hp, size, hr)) : {Nat.is_le(4n+P, _) == True{} : Bool}
        Shared.Nat.is_le_refl(4n+P),
        %Equal.sym(Nat, U32.to_nat(U32.add(hp, 4)), 4n+P, T4(hp, size, hr)) : {Nat.is_le(4n+_, S) == True{} : Bool}
        Le.k8(hp, size, hr)),
      Ld.same(hp, mem, vt, size, Le.k4(hp, size, hr))))

def Ld.n4(+hp: U32, +mem: Wasm.Mem, +vt: U32, +va: U32, +vb: U32, +size: U32,
  +hr: {Nat.is_le(12n+U32.to_nat(hp), U32.to_nat(size)) == True{} : Bool}) ->
  {Wasm.Mem.load(U32.add(hp, 4), M3(hp, mem, vt, va, vb)) == va : U32}:
  +m1 = Wasm.Mem.store(hp, mem, vt)
  +m2 = Wasm.Mem.store(U32.add(hp, 4), m1, va)
  +P = U32.to_nat(hp)
  +S = U32.to_nat(size)
  Equal.trans(U32, Wasm.Mem.load(U32.add(hp, 4), M3(hp, mem, vt, va, vb)), Wasm.Mem.load(U32.add(hp, 4), m2), va,
    Ld.far(U32.add(hp, 4), U32.add(hp, 8), m2, vb, size,
      %Equal.sym(Nat, U32.to_nat(U32.add(hp, 8)), 8n+P, T8(hp, size, hr)) :
        {Nat.is_le(4n+U32.to_nat(U32.add(hp, 4)), _) == True{} : Bool}
      %Equal.sym(Nat, U32.to_nat(U32.add(hp, 4)), 4n+P, T4(hp, size, hr)) : {Nat.is_le(4n+_, 8n+P) == True{} : Bool}
      Shared.Nat.is_le_refl(8n+P),
      %Equal.sym(Nat, U32.to_nat(U32.add(hp, 8)), 8n+P, T8(hp, size, hr)) : {Nat.is_le(4n+_, S) == True{} : Bool}
      hr),
    Ld.same(U32.add(hp, 4), m1, va, size,
      %Equal.sym(Nat, U32.to_nat(U32.add(hp, 4)), 4n+P, T4(hp, size, hr)) : {Nat.is_le(4n+_, S) == True{} : Bool}
      Le.k8(hp, size, hr)))

def Ld.n8(+hp: U32, +mem: Wasm.Mem, +vt: U32, +va: U32, +vb: U32, +size: U32,
  +hr: {Nat.is_le(12n+U32.to_nat(hp), U32.to_nat(size)) == True{} : Bool}) ->
  {Wasm.Mem.load(U32.add(hp, 8), M3(hp, mem, vt, va, vb)) == vb : U32}:
  Ld.same(U32.add(hp, 8), Wasm.Mem.store(U32.add(hp, 4), Wasm.Mem.store(hp, mem, vt), va), vb, size,
    %Equal.sym(Nat, U32.to_nat(U32.add(hp, 8)), 8n+U32.to_nat(hp), T8(hp, size, hr)) :
      {Nat.is_le(4n+_, U32.to_nat(size)) == True{} : Bool}
    hr)

# the node's stores keep each value below hp
def Rd.store3(+v: Fun.V, +mem: Wasm.Mem, +H: Nat, +p: U32, +hp: U32, +vt: U32, +va: U32, +vb: U32, +size: U32,
  +hh: {Nat.is_le(H, U32.to_nat(hp)) == True{} : Bool},
  +hr: {Nat.is_le(12n+U32.to_nat(hp), U32.to_nat(size)) == True{} : Bool},
  h: {Rd(v, mem, H, p) == True{} : Bool}) -> {Rd(v, M3(hp, mem, vt, va, vb), H, p) == True{} : Bool}:
  +m1 = Wasm.Mem.store(hp, mem, vt)
  +m2 = Wasm.Mem.store(U32.add(hp, 4), m1, va)
  +P = U32.to_nat(hp)
  +S = U32.to_nat(size)
  Rd.store(v, m2, H, p, U32.add(hp, 8), vb, size,
    %Equal.sym(Nat, U32.to_nat(U32.add(hp, 8)), 8n+P, T8(hp, size, hr)) : {Nat.is_le(H, _) == True{} : Bool}
    Le.t(H, P, 8n+P, hh, Shared.Nat.is_le_add_left(P, 8n)),
    %Equal.sym(Nat, U32.to_nat(U32.add(hp, 8)), 8n+P, T8(hp, size, hr)) : {Nat.is_le(4n+_, S) == True{} : Bool}
    hr,
    Rd.store(v, m1, H, p, U32.add(hp, 4), va, size,
      %Equal.sym(Nat, U32.to_nat(U32.add(hp, 4)), 4n+P, T4(hp, size, hr)) : {Nat.is_le(H, _) == True{} : Bool}
      Le.t(H, P, 4n+P, hh, Shared.Nat.is_le_add_left(P, 4n)),
      %Equal.sym(Nat, U32.to_nat(U32.add(hp, 4)), 4n+P, T4(hp, size, hr)) : {Nat.is_le(4n+_, S) == True{} : Bool}
      Le.k8(hp, size, hr),
      Rd.store(v, mem, H, p, hp, vt, size, hh, Le.k4(hp, size, hr), h)))

# the new node, below hp + 12, and each value below hp, below hp + 12
def Rd.new(+hp: U32, +mem: Wasm.Mem, +vt: U32, +va: U32, +vb: U32, +size: U32, +t: Nat, +a: Fun.V, +b: Fun.V,
  +hz: {Nat.is_le(1n, U32.to_nat(hp)) == True{} : Bool},
  +hr: {Nat.is_le(12n+U32.to_nat(hp), U32.to_nat(size)) == True{} : Bool},
  +ht: {Nat.is_eq(U32.to_nat(vt), t) == True{} : Bool},
  +ha: {Rd(a, mem, U32.to_nat(hp), va) == True{} : Bool},
  +hb: {Rd(b, mem, U32.to_nat(hp), vb) == True{} : Bool}) ->
  {Rd(Fun.V.n{t, a, b}, M3(hp, mem, vt, va, vb), 12n+U32.to_nat(hp), hp) == True{} : Bool}:
  +m = M3(hp, mem, vt, va, vb)
  +P = U32.to_nat(hp)
  Rd.mk(m, 12n+P, hp, t, a, b, hz, Shared.Nat.is_le_refl(12n+P),
    %Equal.sym(U32, Wasm.Mem.load(hp, m), vt, Ld.n0(hp, mem, vt, va, vb, size, hr)) :
      {Nat.is_eq(U32.to_nat(_), t) == True{} : Bool}
    ht,
    %Equal.sym(U32, Wasm.Mem.load(U32.add(hp, 4), m), va, Ld.n4(hp, mem, vt, va, vb, size, hr)) :
      {Rd(a, m, 12n+P, _) == True{} : Bool}
    Rd.up(a, m, P, 12n+P, va, Shared.Nat.is_le_add_left(P, 12n),
      Rd.store3(a, mem, P, va, hp, vt, va, vb, size, Shared.Nat.is_le_refl(P), hr, ha)),
    %Equal.sym(U32, Wasm.Mem.load(U32.add(hp, 8), m), vb, Ld.n8(hp, mem, vt, va, vb, size, hr)) :
      {Rd(b, m, 12n+P, _) == True{} : Bool}
    Rd.up(b, m, P, 12n+P, vb, Shared.Nat.is_le_add_left(P, 12n),
      Rd.store3(b, mem, P, vb, hp, vt, va, vb, size, Shared.Nat.is_le_refl(P), hr, hb)))

# each value below hp stays, below hp + 12
def Rd.keep(+v: Fun.V, +mem: Wasm.Mem, +p: U32, +hp: U32, +vt: U32, +va: U32, +vb: U32, +size: U32,
  +hr: {Nat.is_le(12n+U32.to_nat(hp), U32.to_nat(size)) == True{} : Bool},
  h: {Rd(v, mem, U32.to_nat(hp), p) == True{} : Bool}) ->
  {Rd(v, M3(hp, mem, vt, va, vb), 12n+U32.to_nat(hp), p) == True{} : Bool}:
  Rd.up(v, M3(hp, mem, vt, va, vb), U32.to_nat(hp), 12n+U32.to_nat(hp), p, Shared.Nat.is_le_add_left(U32.to_nat(hp), 12n),
    Rd.store3(v, mem, U32.to_nat(hp), p, hp, vt, va, vb, size, Shared.Nat.is_le_refl(U32.to_nat(hp)), hr, h))

# Conditions
# ==========

def Nat.eq_of(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, Nat.eq_of(p, q, h))
    case 0n 1n+q:
      Shared.Bool.absurd({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      Shared.Bool.absurd({1n+p == 0n : Nat}, h)

def Cond.b(b: Bool) -> {U32.is_ne(Bool.to_u32(b), 0) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the condition of eqz w
def Cond.eqz(+w: U32, +b: Bool, h: {Nat.is_eq(U32.to_nat(w), 0n) == b : Bool}) ->
  {U32.is_ne(Bool.to_u32(U32.is_eq(w, 0)), 0) == b : Bool}:
  %Equal.sym(Cmp, U32.cmp(w, 0), Nat.cmp(U32.to_nat(w), 0n), WP.U.cmp(w, 0)) :
    {U32.is_ne(Bool.to_u32(Cmp.is_eq(_)), 0) == b : Bool}
  %Equal.sym(Bool, Nat.is_eq(U32.to_nat(w), 0n), b, h) : {U32.is_ne(Bool.to_u32(_), 0) == b : Bool}
  Cond.b(b)

def Nat.ne_zero(+a: Nat, h: {Nat.is_le(1n, a) == True{} : Bool}) -> {Nat.is_eq(a, 0n) == False{} : Bool}:
  match a:
    case 0n:
      Shared.Bool.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 1n+p:
      {==}

# eqz of the address of a node
def Cond.node(+w: U32, h: {Nat.is_le(1n, U32.to_nat(w)) == True{} : Bool}) ->
  {U32.is_ne(Bool.to_u32(U32.is_eq(w, 0)), 0) == False{} : Bool}:
  Cond.eqz(w, False{}, Nat.ne_zero(U32.to_nat(w), h))

# the condition of the room check lim - hp < k
def Cond.room(+lim: U32, +hp: U32, +k: U32, +hle: {Nat.is_le(U32.to_nat(hp), U32.to_nat(lim)) == True{} : Bool}) ->
  {U32.is_ne(Bool.to_u32(U32.is_lt(U32.sub(lim, hp), k)), 0) ==
    Nat.is_lt(Nat.sub(U32.to_nat(lim), U32.to_nat(hp)), U32.to_nat(k)) : Bool}:
  +b = Nat.is_lt(Nat.sub(U32.to_nat(lim), U32.to_nat(hp)), U32.to_nat(k))
  %Equal.sym(Cmp, U32.cmp(U32.sub(lim, hp), k), Nat.cmp(U32.to_nat(U32.sub(lim, hp)), U32.to_nat(k)),
    WP.U.cmp(U32.sub(lim, hp), k)) : {U32.is_ne(Bool.to_u32(Cmp.is_lt(_)), 0) == b : Bool}
  %Equal.sym(Nat, U32.to_nat(U32.sub(lim, hp)), Nat.sub(U32.to_nat(lim), U32.to_nat(hp)), U.sub_nat(lim, hp, hle)) :
    {U32.is_ne(Bool.to_u32(Cmp.is_lt(Nat.cmp(_, U32.to_nat(k)))), 0) == b : Bool}
  Cond.b(b)

# a word whose number is k
def Tag.lit(+p: U32, +mem: Wasm.Mem, +k: Nat, h: {Nat.is_eq(U32.to_nat(Wasm.Mem.load(p, mem)), k) == True{} : Bool}) ->
  {Wasm.Mem.load(p, mem) == U32.from_nat(k) : U32}:
  %Nat.eq_of(U32.to_nat(Wasm.Mem.load(p, mem)), k, h) : {Wasm.Mem.load(p, mem) == U32.from_nat(_) : U32}
  Equal.sym(U32, U32.from_nat(U32.to_nat(Wasm.Mem.load(p, mem))), Wasm.Mem.load(p, mem), WP.U.from_to_nat(Wasm.Mem.load(p, mem)))

# Room
# ====

def Oom.mem(mem: Wasm.Mem) -> Wasm.Mem:
  Wasm.Mem.set_at(4, Wasm.Mem.store(0, mem, 1), 255n)

def R.oom(+d: Nat, +n: Nat, +size: U32, +ls: List<&2, U32>, +mem: Wasm.Mem, +ls2: List<&2, U32>,
  +hs: {Nat.is_le(5n, U32.to_nat(size)) == True{} : Bool},
  h8: {Wasm.List.put(ls, 8n, 0) == Some{ls2} : Maybe<&2, List<&2, U32>>}) ->
  {Imp.Stm.run(RT.S.oom(d), n, size, ls, mem) == Some{Imp.Res.brk{d, ls2, Oom.mem(mem)}} : Maybe<&2, Imp.Res>}:
  +m1 = Wasm.Mem.store(0, mem, 1)
  +m2 = Oom.mem(mem)
  +r = {Some{Imp.Res.brk{d, ls2, m2}} : Maybe<&2, Imp.Res>}
  R.seq(Imp.Stm.store{0, RT.E.k(0), RT.E.k(1)},
    RT.S.all([Imp.Stm.store8{4, RT.E.k(0), RT.E.k(255)}, Imp.Stm.set{8n, RT.E.k(0)}, Imp.Stm.break{d}]),
    n, size, ls, mem, ls, m1, r,
    R.store(0, RT.E.k(0), RT.E.k(1), n, size, ls, mem, 0, 1, 0, {==}, {==},
      Addr(0, 0, 4, size, Shared.Nat.is_le_pred(4n, U32.to_nat(size), hs))),
    R.seq(Imp.Stm.store8{4, RT.E.k(0), RT.E.k(255)}, RT.S.all([Imp.Stm.set{8n, RT.E.k(0)}, Imp.Stm.break{d}]),
      n, size, ls, m1, ls, m2, r,
      R.store8(4, RT.E.k(0), RT.E.k(255), n, size, ls, m1, 0, 255, 4, {==}, {==}, Addr(0, 4, 1, size, hs)),
      R.seq(Imp.Stm.set{8n, RT.E.k(0)}, RT.S.all([Imp.Stm.break{d}]), n, size, ls, m2, ls2, m2, r,
        R.set(8n, RT.E.k(0), n, size, ls, m2, 0, ls2, {==}, h8),
        R.seq_end(Imp.Stm.break{d}, Imp.Stm.skip{}, n, size, ls2, m2, r, {==}, {==}))))

def R.room_ok(+ke: Imp.Exp, +k: U32, +d: Nat, +n: Nat, +size: U32, +ls: List<&2, U32>, +mem: Wasm.Mem, +hp: U32, +lim: U32,
  hh: {Wasm.List.at(ls, 0n) == Some{hp} : Maybe<&2, U32>}, hl: {Wasm.List.at(ls, 1n) == Some{lim} : Maybe<&2, U32>},
  hk: {Imp.Exp.eval(ke, size, ls, mem) == Some{k} : Maybe<&2, U32>}, +hle: {Nat.is_le(U32.to_nat(hp), U32.to_nat(lim)) == True{} : Bool},
  hok: {Nat.is_lt(Nat.sub(U32.to_nat(lim), U32.to_nat(hp)), U32.to_nat(k)) == False{} : Bool}) ->
  {Imp.Stm.run(RT.S.room(ke, d), n, size, ls, mem) == Some{Imp.Res.next{ls, mem}} : Maybe<&2, Imp.Res>}:
  +c = RT.E.lt(RT.E.sub(RT.E.l(1n), RT.E.l(0n)), ke)
  R.if(c, RT.S.oom(d), Imp.Stm.skip{}, n, size, ls, mem, Bool.to_u32(U32.is_lt(U32.sub(lim, hp), k)), False{},
    Some{Imp.Res.next{ls, mem}},
    E.bin(Wasm.Bin.lt_u{}, RT.E.sub(RT.E.l(1n), RT.E.l(0n)), ke, size, ls, mem, U32.sub(lim, hp), k,
      E.bin(Wasm.Bin.sub{}, RT.E.l(1n), RT.E.l(0n), size, ls, mem, lim, hp, hl, hh), hk),
    Equal.trans(Bool, U32.is_ne(Bool.to_u32(U32.is_lt(U32.sub(lim, hp), k)), 0),
      Nat.is_lt(Nat.sub(U32.to_nat(lim), U32.to_nat(hp)), U32.to_nat(k)), False{}, Cond.room(lim, hp, k, hle), hok),
    {==})

def R.room_oom(+ke: Imp.Exp, +k: U32, +d: Nat, +n: Nat, +size: U32, +ls: List<&2, U32>, +mem: Wasm.Mem, +hp: U32, +lim: U32,
  hh: {Wasm.List.at(ls, 0n) == Some{hp} : Maybe<&2, U32>}, hl: {Wasm.List.at(ls, 1n) == Some{lim} : Maybe<&2, U32>},
  hk: {Imp.Exp.eval(ke, size, ls, mem) == Some{k} : Maybe<&2, U32>}, +hle: {Nat.is_le(U32.to_nat(hp), U32.to_nat(lim)) == True{} : Bool},
  hno: {Nat.is_lt(Nat.sub(U32.to_nat(lim), U32.to_nat(hp)), U32.to_nat(k)) == True{} : Bool}) ->
  {Imp.Stm.run(RT.S.room(ke, d), n, size, ls, mem) == Imp.Stm.run(RT.S.oom(d), n, size, ls, mem) : Maybe<&2, Imp.Res>}:
  +c = RT.E.lt(RT.E.sub(RT.E.l(1n), RT.E.l(0n)), ke)
  R.if(c, RT.S.oom(d), Imp.Stm.skip{}, n, size, ls, mem, Bool.to_u32(U32.is_lt(U32.sub(lim, hp), k)), True{},
    Imp.Stm.run(RT.S.oom(d), n, size, ls, mem),
    E.bin(Wasm.Bin.lt_u{}, RT.E.sub(RT.E.l(1n), RT.E.l(0n)), ke, size, ls, mem, U32.sub(lim, hp), k,
      E.bin(Wasm.Bin.sub{}, RT.E.l(1n), RT.E.l(0n), size, ls, mem, lim, hp, hl, hh), hk),
    Equal.trans(Bool, U32.is_ne(Bool.to_u32(U32.is_lt(U32.sub(lim, hp), k)), 0),
      Nat.is_lt(Nat.sub(U32.to_nat(lim), U32.to_nat(hp)), U32.to_nat(k)), True{}, Cond.room(lim, hp, k, hle), hno),
    {==})

def Nat.not_lt(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Shared.Bool.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Nat.not_lt(p, q, h)

def Nat.le_add_r(a: Nat, b: Nat, +c: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool}:
  match a b:
    case 0n _:
      Shared.Nat.is_le_add_left(c, b)
    case 1n+p 0n:
      Shared.Bool.absurd({Nat.is_le(Nat.add(1n+p, c), c) == True{} : Bool}, h)
    case 1n+p 1n+q:
      Nat.le_add_r(p, q, c, h)

# after the room check: k more bytes fit
def Room.fits(+L: Nat, +H: Nat, +K: Nat, +hle: {Nat.is_le(H, L) == True{} : Bool},
  +hok: {Nat.is_lt(Nat.sub(L, H), K) == False{} : Bool}) -> {Nat.is_le(Nat.add(K, H), L) == True{} : Bool}:
  %Nat.sub_add(L, H, hle) : {Nat.is_le(Nat.add(K, H), _) == True{} : Bool}
  Nat.le_add_r(K, Nat.sub(L, H), H, Nat.not_lt(Nat.sub(L, H), K, hok))

# Locals
# ======

def L(x0: U32, x1: U32, x2: U32, x3: U32, x4: U32, x5: U32, x6: U32, x7: U32, x8: U32, x9: U32, x10: U32, x11: U32, x12: U32, x13: U32, x14: U32, x15: U32, x16: U32, x17: U32) -> List<&2, U32>:
  [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17]

# Variables
# =========

# the cell of the variable i of the environment at w, and the counter
def Walk.w(i: Nat, w: U32, +mem: Wasm.Mem) -> U32:
  match i:
    case 0n:
      w
    case 1n+j:
      Walk.w(j, Wasm.Mem.load(U32.add(w, 8), mem), mem)

def Walk.i(i: Nat, iv: U32) -> U32:
  match i:
    case 0n:
      iv
    case 1n+j:
      Walk.i(j, U32.sub(iv, 1))

# when m is a value: p is a node below hp whose a is m
def Rd.mnode(m: Maybe<&2, Fun.V>, +mem: Wasm.Mem, +hp: Nat, +p: U32) -> Bool:
  match m:
    case Some{v}:
      Bool.and(Nat.is_le(12n+U32.to_nat(p), hp), Rd(v, mem, hp, Wasm.Mem.load(U32.add(p, 4), mem)))
    case None{}:
      True{}

# a pass of the walk that goes to the next cell
def Body.step(+x0: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32, +x8: U32, +x9: U32, +x10: U32, +x11: U32, +x12: U32, +x13: U32, +x14: U32, +x15: U32, +iv: U32, +w: U32, +n: Nat, +size: U32, +mem: Wasm.Mem, +H: Nat,
  +hz: {Nat.is_le(1n, U32.to_nat(w)) == True{} : Bool}, +hh: {Nat.is_le(12n+U32.to_nat(w), H) == True{} : Bool},
  +hs: {Nat.is_le(H, U32.to_nat(size)) == True{} : Bool}, +hi: {Nat.is_le(1n, U32.to_nat(iv)) == True{} : Bool}) ->
  {Imp.Stm.run(RT.S.walk.body(), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem) == Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, U32.sub(iv, 1), Wasm.Mem.load(U32.add(w, 8), mem)), mem}} : Maybe<&2, Imp.Res>}:
  +r = {Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, U32.sub(iv, 1), Wasm.Mem.load(U32.add(w, 8), mem)), mem}} : Maybe<&2, Imp.Res>}
  R.seq(RT.S.if(Imp.Exp.eqz{RT.E.l(17n)}, Imp.Stm.trap{}, Imp.Stm.skip{}), RT.S.all([RT.S.if(Imp.Exp.eqz{RT.E.l(16n)}, Imp.Stm.break{0n}, Imp.Stm.skip{}), Imp.Stm.set{17n, RT.E.ld(8, RT.E.l(17n))}, Imp.Stm.set{16n, RT.E.sub(RT.E.l(16n), RT.E.k(1))}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem, r,
    R.if(Imp.Exp.eqz{RT.E.l(17n)}, Imp.Stm.trap{}, Imp.Stm.skip{}, n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem, Bool.to_u32(U32.is_eq(w, 0)), False{},
      Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem}}, {==}, Cond.node(w, hz), {==}),
    R.seq(RT.S.if(Imp.Exp.eqz{RT.E.l(16n)}, Imp.Stm.break{0n}, Imp.Stm.skip{}), RT.S.all([Imp.Stm.set{17n, RT.E.ld(8, RT.E.l(17n))}, Imp.Stm.set{16n, RT.E.sub(RT.E.l(16n), RT.E.k(1))}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem, r,
      R.if(Imp.Exp.eqz{RT.E.l(16n)}, Imp.Stm.break{0n}, Imp.Stm.skip{}, n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem, Bool.to_u32(U32.is_eq(iv, 0)),
        False{}, Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem}}, {==}, Cond.node(iv, hi), {==}),
      R.seq(Imp.Stm.set{17n, RT.E.ld(8, RT.E.l(17n))}, RT.S.all([Imp.Stm.set{16n, RT.E.sub(RT.E.l(16n), RT.E.k(1))}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, Wasm.Mem.load(U32.add(w, 8), mem)), mem, r,
        R.set(17n, RT.E.ld(8, RT.E.l(17n)), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem, Wasm.Mem.load(U32.add(w, 8), mem), L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, Wasm.Mem.load(U32.add(w, 8), mem)),
          E.load(8, RT.E.l(17n), size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem, w, U32.add(w, 8), {==}, Ad8(w, H, size, hh, hs)), {==}),
        R.seq(Imp.Stm.set{16n, RT.E.sub(RT.E.l(16n), RT.E.k(1))}, Imp.Stm.skip{}, n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, Wasm.Mem.load(U32.add(w, 8), mem)), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, U32.sub(iv, 1), Wasm.Mem.load(U32.add(w, 8), mem)), mem, r,
          R.set(16n, RT.E.sub(RT.E.l(16n), RT.E.k(1)), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, Wasm.Mem.load(U32.add(w, 8), mem)), mem, U32.sub(iv, 1), L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, U32.sub(iv, 1), Wasm.Mem.load(U32.add(w, 8), mem)), {==}, {==}), {==}))))

# a pass of the walk at the variable
def Body.brk(+x0: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32, +x8: U32, +x9: U32, +x10: U32, +x11: U32, +x12: U32, +x13: U32, +x14: U32, +x15: U32, +iv: U32, +w: U32, +n: Nat, +size: U32, +mem: Wasm.Mem,
  +hz: {Nat.is_le(1n, U32.to_nat(w)) == True{} : Bool}, +hi: {Nat.is_eq(U32.to_nat(iv), 0n) == True{} : Bool}) ->
  {Imp.Stm.run(RT.S.walk.body(), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem) == Some{Imp.Res.brk{0n, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem}} : Maybe<&2, Imp.Res>}:
  +r = {Some{Imp.Res.brk{0n, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem}} : Maybe<&2, Imp.Res>}
  R.seq(RT.S.if(Imp.Exp.eqz{RT.E.l(17n)}, Imp.Stm.trap{}, Imp.Stm.skip{}), RT.S.all([RT.S.if(Imp.Exp.eqz{RT.E.l(16n)}, Imp.Stm.break{0n}, Imp.Stm.skip{}), Imp.Stm.set{17n, RT.E.ld(8, RT.E.l(17n))}, Imp.Stm.set{16n, RT.E.sub(RT.E.l(16n), RT.E.k(1))}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem, r,
    R.if(Imp.Exp.eqz{RT.E.l(17n)}, Imp.Stm.trap{}, Imp.Stm.skip{}, n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem, Bool.to_u32(U32.is_eq(w, 0)), False{},
      Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem}}, {==}, Cond.node(w, hz), {==}),
    R.seq_end(RT.S.if(Imp.Exp.eqz{RT.E.l(16n)}, Imp.Stm.break{0n}, Imp.Stm.skip{}), RT.S.all([Imp.Stm.set{17n, RT.E.ld(8, RT.E.l(17n))}, Imp.Stm.set{16n, RT.E.sub(RT.E.l(16n), RT.E.k(1))}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem, r, {==},
      R.if(Imp.Exp.eqz{RT.E.l(16n)}, Imp.Stm.break{0n}, Imp.Stm.skip{}, n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem, Bool.to_u32(U32.is_eq(iv, 0)),
        True{}, r, {==}, Cond.eqz(iv, True{}, hi), {==})))

# a pass of the walk past the end of the environment
def Body.trap(+x0: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32, +x8: U32, +x9: U32, +x10: U32, +x11: U32, +x12: U32, +x13: U32, +x14: U32, +x15: U32, +iv: U32, +w: U32, +n: Nat, +size: U32, +mem: Wasm.Mem,
  +hw: {Nat.is_eq(U32.to_nat(w), 0n) == True{} : Bool}) ->
  {Imp.Stm.run(RT.S.walk.body(), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem) == Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>}:
  +r = {Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>}
  R.seq_end(RT.S.if(Imp.Exp.eqz{RT.E.l(17n)}, Imp.Stm.trap{}, Imp.Stm.skip{}), RT.S.all([RT.S.if(Imp.Exp.eqz{RT.E.l(16n)}, Imp.Stm.break{0n}, Imp.Stm.skip{}), Imp.Stm.set{17n, RT.E.ld(8, RT.E.l(17n))}, Imp.Stm.set{16n, RT.E.sub(RT.E.l(16n), RT.E.k(1))}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem, r, {==},
    R.if(Imp.Exp.eqz{RT.E.l(17n)}, Imp.Stm.trap{}, Imp.Stm.skip{}, n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem, Bool.to_u32(U32.is_eq(w, 0)), True{},
      r, {==}, Cond.eqz(w, True{}, hw), {==}))

def Walk.cnt(+iv: U32, +j: Nat, +hi: {U32.to_nat(iv) == 1n+j : Nat}) -> {U32.to_nat(U32.sub(iv, 1)) == j : Nat}:
  Equal.trans(Nat, U32.to_nat(U32.sub(iv, 1)), Nat.sub(U32.to_nat(iv), 1n), j,
    U.sub_nat(iv, 1,
      %Equal.sym(Nat, U32.to_nat(iv), 1n+j, hi) : {Nat.is_le(1n, _) == True{} : Bool}
      Shared.Nat.is_le_zero(j)),
    %Equal.sym(Nat, U32.to_nat(iv), 1n+j, hi) : {Nat.sub(_, 1n) == j : Nat}
    MP.Nat.sub_zero(j))

# the walk to the variable i, when the environment has it
def Walk.some(env: List<&2, Fun.V>, i: Nat, n: Nat, -v: Fun.V, +x0: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32, +x8: U32, +x9: U32, +x10: U32, +x11: U32, +x12: U32, +x13: U32, +x14: U32, +x15: U32, +iv: U32, +w: U32, +mem: Wasm.Mem, +size: U32,
  +H: Nat, +hw: {Rd(RT.Enc.list(env), mem, H, w) == True{} : Bool}, +hi: {U32.to_nat(iv) == i : Nat},
  +hs: {Nat.is_le(H, U32.to_nat(size)) == True{} : Bool},
  he: {List.get(&2, Fun.V, env, i) == Some{v} : Maybe<&2, Fun.V>}, hn: {Nat.is_le(1n+i, n) == True{} : Bool}) ->
  {Imp.Stm.run(RT.S.walk(), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem) == Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, Walk.i(i, iv), Walk.w(i, w, mem)), mem}} : Maybe<&2, Imp.Res>}:
  match env i n:
    case Nil{} _ _:
      Empty.absurd({Imp.Stm.run(RT.S.walk(), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem) == Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, Walk.i(i, iv), Walk.w(i, w, mem)), mem}} :
        Maybe<&2, Imp.Res>}, Shared.Maybe.no_none(Fun.V, v, he))
    case Con{+x, +rest} 0n 0n:
      Shared.Bool.absurd({Imp.Stm.run(RT.S.walk(), 0n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem) == Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem}} : Maybe<&2, Imp.Res>}, hn)
    case Con{+x, +rest} 1n++j 0n:
      Shared.Bool.absurd({Imp.Stm.run(RT.S.walk(), 0n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem) == Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, Walk.i(j, U32.sub(iv, 1)), Walk.w(j, Wasm.Mem.load(U32.add(w, 8), mem), mem)), mem}} : Maybe<&2, Imp.Res>}, hn)
    case Con{+x, +rest} 0n 1n+k:
      %Equal.sym(Maybe<&2, Imp.Res>, Imp.Stm.run(RT.S.walk.body(), k, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem), Some{Imp.Res.brk{0n, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem}},
        Body.brk(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w, k, size, mem, Rd.nz(mem, H, w, 0n, x, RT.Enc.list(rest), hw),
          %Equal.sym(Nat, U32.to_nat(iv), 0n, hi) : {Nat.is_eq(_, 0n) == True{} : Bool}
          {==})) :
        {Imp.Res.loop(_, x => y => Imp.Stm.run(RT.S.walk(), k, size, x, y)) == Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem}} : Maybe<&2, Imp.Res>}
      {==}
    case Con{+x, +rest} 1n++j 1n++k:
      %Equal.sym(Maybe<&2, Imp.Res>, Imp.Stm.run(RT.S.walk.body(), k, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem), Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, U32.sub(iv, 1), Wasm.Mem.load(U32.add(w, 8), mem)), mem}},
        Body.step(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w, k, size, mem, H, Rd.nz(mem, H, w, 0n, x, RT.Enc.list(rest), hw),
          Rd.hi(mem, H, w, 0n, x, RT.Enc.list(rest), hw), hs,
          %Equal.sym(Nat, U32.to_nat(iv), 1n+j, hi) : {Nat.is_le(1n, _) == True{} : Bool}
          Shared.Nat.is_le_zero(j))) :
        {Imp.Res.loop(_, x => y => Imp.Stm.run(RT.S.walk(), k, size, x, y)) == Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, Walk.i(j, U32.sub(iv, 1)), Walk.w(j, Wasm.Mem.load(U32.add(w, 8), mem), mem)), mem}} :
          Maybe<&2, Imp.Res>}
      Walk.some(rest, j, k, v, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, U32.sub(iv, 1), Wasm.Mem.load(U32.add(w, 8), mem), mem, size, H, Rd.b(mem, H, w, 0n, x, RT.Enc.list(rest), hw),
        Walk.cnt(iv, j, hi), hs, he, hn)

# the walk to the variable i, when the environment has no such variable
def Walk.none(env: List<&2, Fun.V>, i: Nat, n: Nat, +x0: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32, +x8: U32, +x9: U32, +x10: U32, +x11: U32, +x12: U32, +x13: U32, +x14: U32, +x15: U32, +iv: U32, +w: U32, +mem: Wasm.Mem, +size: U32,
  +H: Nat, +hw: {Rd(RT.Enc.list(env), mem, H, w) == True{} : Bool}, +hi: {U32.to_nat(iv) == i : Nat},
  +hs: {Nat.is_le(H, U32.to_nat(size)) == True{} : Bool},
  he: {List.get(&2, Fun.V, env, i) == None{} : Maybe<&2, Fun.V>}, hn: {Nat.is_le(1n+i, n) == True{} : Bool}) ->
  {Imp.Stm.run(RT.S.walk(), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem) == Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>}:
  match env i n:
    case Nil{} _ 0n:
      Shared.Bool.absurd({Imp.Stm.run(RT.S.walk(), 0n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem) == Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>}, hn)
    case Nil{} _ 1n+k:
      %Equal.sym(Maybe<&2, Imp.Res>, Imp.Stm.run(RT.S.walk.body(), k, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem), Some{Imp.Res.trap{}},
        Body.trap(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w, k, size, mem, hw)) :
        {Imp.Res.loop(_, x => y => Imp.Stm.run(RT.S.walk(), k, size, x, y)) == Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>}
      {==}
    case Con{x, rest} 0n _:
      Empty.absurd({Imp.Stm.run(RT.S.walk(), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem) == Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>},
        Shared.Maybe.no_none(Fun.V, x, Equal.sym(Maybe<&2, Fun.V>, Some{x}, None{}, he)))
    case Con{+x, +rest} 1n++j 0n:
      Shared.Bool.absurd({Imp.Stm.run(RT.S.walk(), 0n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem) == Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>}, hn)
    case Con{+x, +rest} 1n++j 1n++k:
      %Equal.sym(Maybe<&2, Imp.Res>, Imp.Stm.run(RT.S.walk.body(), k, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w), mem), Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, U32.sub(iv, 1), Wasm.Mem.load(U32.add(w, 8), mem)), mem}},
        Body.step(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, iv, w, k, size, mem, H, Rd.nz(mem, H, w, 0n, x, RT.Enc.list(rest), hw),
          Rd.hi(mem, H, w, 0n, x, RT.Enc.list(rest), hw), hs,
          %Equal.sym(Nat, U32.to_nat(iv), 1n+j, hi) : {Nat.is_le(1n, _) == True{} : Bool}
          Shared.Nat.is_le_zero(j))) :
        {Imp.Res.loop(_, x => y => Imp.Stm.run(RT.S.walk(), k, size, x, y)) == Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>}
      Walk.none(rest, j, k, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, U32.sub(iv, 1), Wasm.Mem.load(U32.add(w, 8), mem), mem, size, H, Rd.b(mem, H, w, 0n, x, RT.Enc.list(rest), hw),
        Walk.cnt(iv, j, hi), hs, he, hn)

# the cell that the walk reaches holds the variable
def Walk.node(env: List<&2, Fun.V>, i: Nat, +w: U32, +mem: Wasm.Mem, +H: Nat,
  +hw: {Rd(RT.Enc.list(env), mem, H, w) == True{} : Bool}) ->
  {Rd.mnode(List.get(&2, Fun.V, env, i), mem, H, Walk.w(i, w, mem)) == True{} : Bool}:
  match env i:
    case Nil{} _:
      {==}
    case Con{+x, +rest} 0n:
      And.mk(Nat.is_le(12n+U32.to_nat(w), H), Rd(x, mem, H, Wasm.Mem.load(U32.add(w, 4), mem)),
        Rd.hi(mem, H, w, 0n, x, RT.Enc.list(rest), hw), Rd.a(mem, H, w, 0n, x, RT.Enc.list(rest), hw))
    case Con{+x, +rest} 1n+j:
      Walk.node(rest, j, Wasm.Mem.load(U32.add(w, 8), mem), mem, H, Rd.b(mem, H, w, 0n, x, RT.Enc.list(rest), hw))

# Atoms
# =====

# the fuel of the walk to an atom's value
def Atom.need(a: Fun.A) -> Nat:
  match a:
    case Fun.A.var{i}:
      i
    case _:
      0n

# the value of the atom a at ap, with the environment at env
def Atom.val(a: Fun.A, +ap: U32, +env: U32, +mem: Wasm.Mem) -> U32:
  match a:
    case Fun.A.var{i}:
      Wasm.Mem.load(U32.add(Walk.w(i, env, mem), 4), mem)
    case _:
      Wasm.Mem.load(U32.add(ap, 4), mem)

# when m is a value: the memory holds it at p
def Rd.m(m: Maybe<&2, Fun.V>, +mem: Wasm.Mem, +hp: Nat, +p: U32) -> Bool:
  match m:
    case Some{v}:
      Rd(v, mem, hp, p)
    case None{}:
      True{}

def Mnode.m(m: Maybe<&2, Fun.V>, +mem: Wasm.Mem, +hp: Nat, +p: U32, h: {Rd.mnode(m, mem, hp, p) == True{} : Bool}) ->
  {Rd.m(m, mem, hp, Wasm.Mem.load(U32.add(p, 4), mem)) == True{} : Bool}:
  match m:
    case Some{v}:
      And.r(Nat.is_le(12n+U32.to_nat(p), hp), Rd(v, mem, hp, Wasm.Mem.load(U32.add(p, 4), mem)), h)
    case None{}:
      {==}

def Mnode.hi(+m: Maybe<&2, Fun.V>, -v: Fun.V, +mem: Wasm.Mem, +hp: Nat, +p: U32, hm: {m == Some{v} : Maybe<&2, Fun.V>},
  h: {Rd.mnode(m, mem, hp, p) == True{} : Bool}) -> {Nat.is_le(12n+U32.to_nat(p), hp) == True{} : Bool}:
  And.l(Nat.is_le(12n+U32.to_nat(p), hp), Rd(v, mem, hp, Wasm.Mem.load(U32.add(p, 4), mem)),
    %hm : {Rd.mnode(_, mem, hp, p) == True{} : Bool}
    h)

# the memory holds the value of the atom
def Atom.rd(a: Fun.A, +env: List<&2, Fun.V>, +ap: U32, +envp: U32, +mem: Wasm.Mem, +H: Nat,
  +ha: {Rd(RT.Enc.atom(a), mem, H, ap) == True{} : Bool}, +hv: {Rd(RT.Enc.list(env), mem, H, envp) == True{} : Bool}) ->
  {Rd.m(Fun.A.get(a, env), mem, H, Atom.val(a, ap, envp, mem)) == True{} : Bool}:
  match a:
    case Fun.A.var{+i}:
      Mnode.m(List.get(&2, Fun.V, env, i), mem, H, Walk.w(i, envp, mem), Walk.node(env, i, envp, mem, H, hv))
    case Fun.A.num{+t}:
      Rd.a(mem, H, ap, 1n, Fun.V.num(t), Fun.V.z{}, ha)
    case Fun.A.z{}:
      Rd.a(mem, H, ap, 1n, Fun.V.z{}, Fun.V.z{}, ha)

# the atom's value, when the environment has it
def Atom.some(a: Fun.A, +env: List<&2, Fun.V>, +e: Imp.Exp, +x0: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32, +x8: U32, +x9: U32, +x10: U32, +x11: U32, +x12: U32, +x13: U32, +x14: U32, +x15: U32, +x16: U32, +x17: U32, +ap: U32, +mem: Wasm.Mem, +size: U32, +H: Nat,
  he: {Imp.Exp.eval(e, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17), mem) == Some{ap} : Maybe<&2, U32>},
  +ha: {Rd(RT.Enc.atom(a), mem, H, ap) == True{} : Bool}, +hv: {Rd(RT.Enc.list(env), mem, H, x4) == True{} : Bool},
  +hs: {Nat.is_le(H, U32.to_nat(size)) == True{} : Bool}, +n: Nat, -v: Fun.V,
  +hg: {Fun.A.get(a, env) == Some{v} : Maybe<&2, Fun.V>}, +hn: {Nat.is_le(1n+Atom.need(a), n) == True{} : Bool}) ->
  {Imp.Stm.run(RT.S.atom(e), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17), mem) ==
    Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(a, ap, x4, mem), x12, x13, x14, 0, 0, 0), mem}} : Maybe<&2, Imp.Res>}:
  match a:
    case Fun.A.var{+i}:
      R.seq(Imp.Stm.set{15n, e}, RT.S.all([RT.S.if(RT.E.eq(RT.E.ld(0, RT.E.l(15n)), RT.E.k(1)), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(15n))}, RT.S.all([Imp.Stm.set{16n, RT.E.ld(0, RT.E.ld(4, RT.E.l(15n)))}, Imp.Stm.set{17n, RT.E.l(4n)}, RT.S.walk(), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(17n))}])), Imp.Stm.set{15n, RT.E.k(0)}, Imp.Stm.set{16n, RT.E.k(0)}, Imp.Stm.set{17n, RT.E.k(0)}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, {Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, 0, 0, 0), mem}} : Maybe<&2, Imp.Res>},
        R.set(15n, e, n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17), mem, ap, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), he, {==}),
        R.seq(RT.S.if(RT.E.eq(RT.E.ld(0, RT.E.l(15n)), RT.E.k(1)), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(15n))}, RT.S.all([Imp.Stm.set{16n, RT.E.ld(0, RT.E.ld(4, RT.E.l(15n)))}, Imp.Stm.set{17n, RT.E.l(4n)}, RT.S.walk(), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(17n))}])), RT.S.all([Imp.Stm.set{15n, RT.E.k(0)}, Imp.Stm.set{16n, RT.E.k(0)}, Imp.Stm.set{17n, RT.E.k(0)}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, ap, Walk.i(i, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem)), Walk.w(i, x4, mem)), mem, {Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, 0, 0, 0), mem}} : Maybe<&2, Imp.Res>},
          R.if(RT.E.eq(RT.E.ld(0, RT.E.l(15n)), RT.E.k(1)), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(15n))}, RT.S.all([Imp.Stm.set{16n, RT.E.ld(0, RT.E.ld(4, RT.E.l(15n)))}, Imp.Stm.set{17n, RT.E.l(4n)}, RT.S.walk(), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(17n))}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, Bool.to_u32(U32.is_eq(Wasm.Mem.load(ap, mem), 1)), False{}, {Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, ap, Walk.i(i, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem)), Walk.w(i, x4, mem)), mem}} : Maybe<&2, Imp.Res>},
            E.bin(Wasm.Bin.eq{}, RT.E.ld(0, RT.E.l(15n)), RT.E.k(1), size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, Wasm.Mem.load(ap, mem), 1, E.load(0, RT.E.l(15n), size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, ap, ap, {==}, Ad0(ap, H, size, Rd.hi(mem, H, ap, 0n, Fun.V.num(i), Fun.V.z{}, ha), hs)), {==}),
            %Equal.sym(U32, Wasm.Mem.load(ap, mem), U32.from_nat(0n), Tag.lit(ap, mem, 0n, Rd.tag(mem, H, ap, 0n, Fun.V.num(i), Fun.V.z{}, ha))) :
              {U32.is_ne(Bool.to_u32(U32.is_eq(_, 1)), 0) == False{} : Bool}
            {==},
            R.seq(Imp.Stm.set{16n, RT.E.ld(0, RT.E.ld(4, RT.E.l(15n)))}, RT.S.all([Imp.Stm.set{17n, RT.E.l(4n)}, RT.S.walk(), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(17n))}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem), x17), mem, {Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, ap, Walk.i(i, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem)), Walk.w(i, x4, mem)), mem}} : Maybe<&2, Imp.Res>},
              R.set(16n, RT.E.ld(0, RT.E.ld(4, RT.E.l(15n))), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem), L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem), x17),
                E.load(0, RT.E.ld(4, RT.E.l(15n)), size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, Wasm.Mem.load(U32.add(ap, 4), mem), Wasm.Mem.load(U32.add(ap, 4), mem),
                  E.load(4, RT.E.l(15n), size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, ap, U32.add(ap, 4), {==}, Ad4(ap, H, size, Rd.hi(mem, H, ap, 0n, Fun.V.num(i), Fun.V.z{}, ha), hs)),
                  Ad0(Wasm.Mem.load(U32.add(ap, 4), mem), H, size, Rd.hi(mem, H, Wasm.Mem.load(U32.add(ap, 4), mem), i, Fun.V.z{}, Fun.V.z{}, Rd.a(mem, H, ap, 0n, Fun.V.num(i), Fun.V.z{}, ha)), hs)), {==}),
              R.seq(Imp.Stm.set{17n, RT.E.l(4n)}, RT.S.all([RT.S.walk(), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(17n))}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem), x17), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem), x4), mem, {Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, ap, Walk.i(i, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem)), Walk.w(i, x4, mem)), mem}} : Maybe<&2, Imp.Res>},
                R.set(17n, RT.E.l(4n), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem), x17), mem, x4, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem), x4), {==}, {==}),
                R.seq(RT.S.walk(), RT.S.all([Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(17n))}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem), x4), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, Walk.i(i, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem)), Walk.w(i, x4, mem)), mem, {Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, ap, Walk.i(i, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem)), Walk.w(i, x4, mem)), mem}} : Maybe<&2, Imp.Res>},
                  Walk.some(env, i, n, v, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem), x4, mem, size, H, hv, Nat.eq_of(U32.to_nat(Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem)), i, Rd.tag(mem, H, Wasm.Mem.load(U32.add(ap, 4), mem), i, Fun.V.z{}, Fun.V.z{}, Rd.a(mem, H, ap, 0n, Fun.V.num(i), Fun.V.z{}, ha))), hs, hg, hn),
                  R.seq(Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(17n))}, Imp.Stm.skip{}, n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, Walk.i(i, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem)), Walk.w(i, x4, mem)), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, ap, Walk.i(i, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem)), Walk.w(i, x4, mem)), mem, {Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, ap, Walk.i(i, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem)), Walk.w(i, x4, mem)), mem}} : Maybe<&2, Imp.Res>},
                    R.set(11n, RT.E.ld(4, RT.E.l(17n)), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, Walk.i(i, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem)), Walk.w(i, x4, mem)), mem, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, ap, Walk.i(i, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem)), Walk.w(i, x4, mem)),
                      E.load(4, RT.E.l(17n), size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, Walk.i(i, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem)), Walk.w(i, x4, mem)), mem, Walk.w(i, x4, mem), U32.add(Walk.w(i, x4, mem), 4), {==},
                        Ad4(Walk.w(i, x4, mem), H, size, Mnode.hi(List.get(&2, Fun.V, env, i), v, mem, H, Walk.w(i, x4, mem), hg, Walk.node(env, i, x4, mem, H, hv)), hs)),
                      {==}), {==}))))),
          R.seq(Imp.Stm.set{15n, RT.E.k(0)}, RT.S.all([Imp.Stm.set{16n, RT.E.k(0)}, Imp.Stm.set{17n, RT.E.k(0)}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, ap, Walk.i(i, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem)), Walk.w(i, x4, mem)), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, 0, Walk.i(i, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem)), Walk.w(i, x4, mem)), mem, {Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, 0, 0, 0), mem}} : Maybe<&2, Imp.Res>},
          R.set(15n, RT.E.k(0), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, ap, Walk.i(i, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem)), Walk.w(i, x4, mem)), mem, 0, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, 0, Walk.i(i, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem)), Walk.w(i, x4, mem)), {==}, {==}),
          R.seq(Imp.Stm.set{16n, RT.E.k(0)}, RT.S.all([Imp.Stm.set{17n, RT.E.k(0)}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, 0, Walk.i(i, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem)), Walk.w(i, x4, mem)), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, 0, 0, Walk.w(i, x4, mem)), mem, {Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, 0, 0, 0), mem}} : Maybe<&2, Imp.Res>},
            R.set(16n, RT.E.k(0), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, 0, Walk.i(i, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem)), Walk.w(i, x4, mem)), mem, 0, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, 0, 0, Walk.w(i, x4, mem)), {==}, {==}),
            R.seq(Imp.Stm.set{17n, RT.E.k(0)}, Imp.Stm.skip{}, n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, 0, 0, Walk.w(i, x4, mem)), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, 0, 0, 0), mem, {Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, 0, 0, 0), mem}} : Maybe<&2, Imp.Res>},
              R.set(17n, RT.E.k(0), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, 0, 0, Walk.w(i, x4, mem)), mem, 0, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(Walk.w(i, x4, mem), 4), mem), x12, x13, x14, 0, 0, 0), {==}, {==}), {==})))))
    case Fun.A.num{+t}:
      R.seq(Imp.Stm.set{15n, e}, RT.S.all([RT.S.if(RT.E.eq(RT.E.ld(0, RT.E.l(15n)), RT.E.k(1)), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(15n))}, RT.S.all([Imp.Stm.set{16n, RT.E.ld(0, RT.E.ld(4, RT.E.l(15n)))}, Imp.Stm.set{17n, RT.E.l(4n)}, RT.S.walk(), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(17n))}])), Imp.Stm.set{15n, RT.E.k(0)}, Imp.Stm.set{16n, RT.E.k(0)}, Imp.Stm.set{17n, RT.E.k(0)}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, {Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, 0, 0), mem}} : Maybe<&2, Imp.Res>},
        R.set(15n, e, n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17), mem, ap, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), he, {==}),
        R.seq(RT.S.if(RT.E.eq(RT.E.ld(0, RT.E.l(15n)), RT.E.k(1)), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(15n))}, RT.S.all([Imp.Stm.set{16n, RT.E.ld(0, RT.E.ld(4, RT.E.l(15n)))}, Imp.Stm.set{17n, RT.E.l(4n)}, RT.S.walk(), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(17n))}])), RT.S.all([Imp.Stm.set{15n, RT.E.k(0)}, Imp.Stm.set{16n, RT.E.k(0)}, Imp.Stm.set{17n, RT.E.k(0)}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, ap, x16, x17), mem, {Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, 0, 0), mem}} : Maybe<&2, Imp.Res>},
          R.if(RT.E.eq(RT.E.ld(0, RT.E.l(15n)), RT.E.k(1)), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(15n))}, RT.S.all([Imp.Stm.set{16n, RT.E.ld(0, RT.E.ld(4, RT.E.l(15n)))}, Imp.Stm.set{17n, RT.E.l(4n)}, RT.S.walk(), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(17n))}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, Bool.to_u32(U32.is_eq(Wasm.Mem.load(ap, mem), 1)), True{}, Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, ap, x16, x17), mem}},
            E.bin(Wasm.Bin.eq{}, RT.E.ld(0, RT.E.l(15n)), RT.E.k(1), size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, Wasm.Mem.load(ap, mem), 1, E.load(0, RT.E.l(15n), size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, ap, ap, {==}, Ad0(ap, H, size, Rd.hi(mem, H, ap, 1n, Fun.V.num(t), Fun.V.z{}, ha), hs)), {==}),
            %Equal.sym(U32, Wasm.Mem.load(ap, mem), U32.from_nat(1n), Tag.lit(ap, mem, 1n, Rd.tag(mem, H, ap, 1n, Fun.V.num(t), Fun.V.z{}, ha))) :
              {U32.is_ne(Bool.to_u32(U32.is_eq(_, 1)), 0) == True{} : Bool}
            {==},
            R.set(11n, RT.E.ld(4, RT.E.l(15n)), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, Wasm.Mem.load(U32.add(ap, 4), mem), L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, ap, x16, x17),
              E.load(4, RT.E.l(15n), size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, ap, U32.add(ap, 4), {==}, Ad4(ap, H, size, Rd.hi(mem, H, ap, 1n, Fun.V.num(t), Fun.V.z{}, ha), hs)), {==})),
          R.seq(Imp.Stm.set{15n, RT.E.k(0)}, RT.S.all([Imp.Stm.set{16n, RT.E.k(0)}, Imp.Stm.set{17n, RT.E.k(0)}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, ap, x16, x17), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, x16, x17), mem, {Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, 0, 0), mem}} : Maybe<&2, Imp.Res>},
          R.set(15n, RT.E.k(0), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, ap, x16, x17), mem, 0, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, x16, x17), {==}, {==}),
          R.seq(Imp.Stm.set{16n, RT.E.k(0)}, RT.S.all([Imp.Stm.set{17n, RT.E.k(0)}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, x16, x17), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, 0, x17), mem, {Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, 0, 0), mem}} : Maybe<&2, Imp.Res>},
            R.set(16n, RT.E.k(0), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, x16, x17), mem, 0, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, 0, x17), {==}, {==}),
            R.seq(Imp.Stm.set{17n, RT.E.k(0)}, Imp.Stm.skip{}, n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, 0, x17), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, 0, 0), mem, {Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, 0, 0), mem}} : Maybe<&2, Imp.Res>},
              R.set(17n, RT.E.k(0), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, 0, x17), mem, 0, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, 0, 0), {==}, {==}), {==})))))
    case Fun.A.z{}:
      R.seq(Imp.Stm.set{15n, e}, RT.S.all([RT.S.if(RT.E.eq(RT.E.ld(0, RT.E.l(15n)), RT.E.k(1)), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(15n))}, RT.S.all([Imp.Stm.set{16n, RT.E.ld(0, RT.E.ld(4, RT.E.l(15n)))}, Imp.Stm.set{17n, RT.E.l(4n)}, RT.S.walk(), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(17n))}])), Imp.Stm.set{15n, RT.E.k(0)}, Imp.Stm.set{16n, RT.E.k(0)}, Imp.Stm.set{17n, RT.E.k(0)}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, {Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, 0, 0), mem}} : Maybe<&2, Imp.Res>},
        R.set(15n, e, n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17), mem, ap, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), he, {==}),
        R.seq(RT.S.if(RT.E.eq(RT.E.ld(0, RT.E.l(15n)), RT.E.k(1)), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(15n))}, RT.S.all([Imp.Stm.set{16n, RT.E.ld(0, RT.E.ld(4, RT.E.l(15n)))}, Imp.Stm.set{17n, RT.E.l(4n)}, RT.S.walk(), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(17n))}])), RT.S.all([Imp.Stm.set{15n, RT.E.k(0)}, Imp.Stm.set{16n, RT.E.k(0)}, Imp.Stm.set{17n, RT.E.k(0)}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, ap, x16, x17), mem, {Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, 0, 0), mem}} : Maybe<&2, Imp.Res>},
          R.if(RT.E.eq(RT.E.ld(0, RT.E.l(15n)), RT.E.k(1)), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(15n))}, RT.S.all([Imp.Stm.set{16n, RT.E.ld(0, RT.E.ld(4, RT.E.l(15n)))}, Imp.Stm.set{17n, RT.E.l(4n)}, RT.S.walk(), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(17n))}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, Bool.to_u32(U32.is_eq(Wasm.Mem.load(ap, mem), 1)), True{}, Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, ap, x16, x17), mem}},
            E.bin(Wasm.Bin.eq{}, RT.E.ld(0, RT.E.l(15n)), RT.E.k(1), size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, Wasm.Mem.load(ap, mem), 1, E.load(0, RT.E.l(15n), size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, ap, ap, {==}, Ad0(ap, H, size, Rd.hi(mem, H, ap, 1n, Fun.V.z{}, Fun.V.z{}, ha), hs)), {==}),
            %Equal.sym(U32, Wasm.Mem.load(ap, mem), U32.from_nat(1n), Tag.lit(ap, mem, 1n, Rd.tag(mem, H, ap, 1n, Fun.V.z{}, Fun.V.z{}, ha))) :
              {U32.is_ne(Bool.to_u32(U32.is_eq(_, 1)), 0) == True{} : Bool}
            {==},
            R.set(11n, RT.E.ld(4, RT.E.l(15n)), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, Wasm.Mem.load(U32.add(ap, 4), mem), L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, ap, x16, x17),
              E.load(4, RT.E.l(15n), size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, ap, U32.add(ap, 4), {==}, Ad4(ap, H, size, Rd.hi(mem, H, ap, 1n, Fun.V.z{}, Fun.V.z{}, ha), hs)), {==})),
          R.seq(Imp.Stm.set{15n, RT.E.k(0)}, RT.S.all([Imp.Stm.set{16n, RT.E.k(0)}, Imp.Stm.set{17n, RT.E.k(0)}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, ap, x16, x17), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, x16, x17), mem, {Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, 0, 0), mem}} : Maybe<&2, Imp.Res>},
          R.set(15n, RT.E.k(0), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, ap, x16, x17), mem, 0, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, x16, x17), {==}, {==}),
          R.seq(Imp.Stm.set{16n, RT.E.k(0)}, RT.S.all([Imp.Stm.set{17n, RT.E.k(0)}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, x16, x17), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, 0, x17), mem, {Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, 0, 0), mem}} : Maybe<&2, Imp.Res>},
            R.set(16n, RT.E.k(0), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, x16, x17), mem, 0, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, 0, x17), {==}, {==}),
            R.seq(Imp.Stm.set{17n, RT.E.k(0)}, Imp.Stm.skip{}, n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, 0, x17), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, 0, 0), mem, {Some{Imp.Res.next{L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, 0, 0), mem}} : Maybe<&2, Imp.Res>},
              R.set(17n, RT.E.k(0), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, 0, x17), mem, 0, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Wasm.Mem.load(U32.add(ap, 4), mem), x12, x13, x14, 0, 0, 0), {==}, {==}), {==})))))

# a trap, when the environment has no such variable
def Atom.none(a: Fun.A, +env: List<&2, Fun.V>, +e: Imp.Exp, +x0: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32, +x8: U32, +x9: U32, +x10: U32, +x11: U32, +x12: U32, +x13: U32, +x14: U32, +x15: U32, +x16: U32, +x17: U32, +ap: U32, +mem: Wasm.Mem, +size: U32, +H: Nat,
  he: {Imp.Exp.eval(e, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17), mem) == Some{ap} : Maybe<&2, U32>},
  +ha: {Rd(RT.Enc.atom(a), mem, H, ap) == True{} : Bool}, +hv: {Rd(RT.Enc.list(env), mem, H, x4) == True{} : Bool},
  +hs: {Nat.is_le(H, U32.to_nat(size)) == True{} : Bool}, +n: Nat,
  hg: {Fun.A.get(a, env) == None{} : Maybe<&2, Fun.V>}, hn: {Nat.is_le(1n+Atom.need(a), n) == True{} : Bool}) ->
  {Imp.Stm.run(RT.S.atom(e), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17), mem) == Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>}:
  match a:
    case Fun.A.var{+i}:
      R.seq(Imp.Stm.set{15n, e}, RT.S.all([RT.S.if(RT.E.eq(RT.E.ld(0, RT.E.l(15n)), RT.E.k(1)), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(15n))}, RT.S.all([Imp.Stm.set{16n, RT.E.ld(0, RT.E.ld(4, RT.E.l(15n)))}, Imp.Stm.set{17n, RT.E.l(4n)}, RT.S.walk(), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(17n))}])), Imp.Stm.set{15n, RT.E.k(0)}, Imp.Stm.set{16n, RT.E.k(0)}, Imp.Stm.set{17n, RT.E.k(0)}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, {Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>},
        R.set(15n, e, n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17), mem, ap, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), he, {==}),
        R.seq_end(RT.S.if(RT.E.eq(RT.E.ld(0, RT.E.l(15n)), RT.E.k(1)), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(15n))}, RT.S.all([Imp.Stm.set{16n, RT.E.ld(0, RT.E.ld(4, RT.E.l(15n)))}, Imp.Stm.set{17n, RT.E.l(4n)}, RT.S.walk(), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(17n))}])), RT.S.all([Imp.Stm.set{15n, RT.E.k(0)}, Imp.Stm.set{16n, RT.E.k(0)}, Imp.Stm.set{17n, RT.E.k(0)}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, {Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>}, {==},
          R.if(RT.E.eq(RT.E.ld(0, RT.E.l(15n)), RT.E.k(1)), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(15n))}, RT.S.all([Imp.Stm.set{16n, RT.E.ld(0, RT.E.ld(4, RT.E.l(15n)))}, Imp.Stm.set{17n, RT.E.l(4n)}, RT.S.walk(), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(17n))}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, Bool.to_u32(U32.is_eq(Wasm.Mem.load(ap, mem), 1)), False{}, {Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>},
            E.bin(Wasm.Bin.eq{}, RT.E.ld(0, RT.E.l(15n)), RT.E.k(1), size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, Wasm.Mem.load(ap, mem), 1, E.load(0, RT.E.l(15n), size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, ap, ap, {==}, Ad0(ap, H, size, Rd.hi(mem, H, ap, 0n, Fun.V.num(i), Fun.V.z{}, ha), hs)), {==}),
            %Equal.sym(U32, Wasm.Mem.load(ap, mem), U32.from_nat(0n), Tag.lit(ap, mem, 0n, Rd.tag(mem, H, ap, 0n, Fun.V.num(i), Fun.V.z{}, ha))) :
              {U32.is_ne(Bool.to_u32(U32.is_eq(_, 1)), 0) == False{} : Bool}
            {==},
            R.seq(Imp.Stm.set{16n, RT.E.ld(0, RT.E.ld(4, RT.E.l(15n)))}, RT.S.all([Imp.Stm.set{17n, RT.E.l(4n)}, RT.S.walk(), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(17n))}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem), x17), mem, {Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>},
              R.set(16n, RT.E.ld(0, RT.E.ld(4, RT.E.l(15n))), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem), L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem), x17),
                E.load(0, RT.E.ld(4, RT.E.l(15n)), size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, Wasm.Mem.load(U32.add(ap, 4), mem), Wasm.Mem.load(U32.add(ap, 4), mem),
                  E.load(4, RT.E.l(15n), size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, x16, x17), mem, ap, U32.add(ap, 4), {==}, Ad4(ap, H, size, Rd.hi(mem, H, ap, 0n, Fun.V.num(i), Fun.V.z{}, ha), hs)),
                  Ad0(Wasm.Mem.load(U32.add(ap, 4), mem), H, size, Rd.hi(mem, H, Wasm.Mem.load(U32.add(ap, 4), mem), i, Fun.V.z{}, Fun.V.z{}, Rd.a(mem, H, ap, 0n, Fun.V.num(i), Fun.V.z{}, ha)), hs)), {==}),
              R.seq(Imp.Stm.set{17n, RT.E.l(4n)}, RT.S.all([RT.S.walk(), Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(17n))}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem), x17), mem, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem), x4), mem, {Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>},
                R.set(17n, RT.E.l(4n), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem), x17), mem, x4, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem), x4), {==}, {==}),
                R.seq_end(RT.S.walk(), RT.S.all([Imp.Stm.set{11n, RT.E.ld(4, RT.E.l(17n))}]), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem), x4), mem, {Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>}, {==},
                  Walk.none(env, i, n, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, ap, Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem), x4, mem, size, H, hv, Nat.eq_of(U32.to_nat(Wasm.Mem.load(Wasm.Mem.load(U32.add(ap, 4), mem), mem)), i, Rd.tag(mem, H, Wasm.Mem.load(U32.add(ap, 4), mem), i, Fun.V.z{}, Fun.V.z{}, Rd.a(mem, H, ap, 0n, Fun.V.num(i), Fun.V.z{}, ha))), hs, hg, hn)))))))
    case Fun.A.num{+t}:
      Empty.absurd({Imp.Stm.run(RT.S.atom(e), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17), mem) == Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>},
        Shared.Maybe.no_none(Fun.V, Fun.V.num(t), Equal.sym(Maybe<&2, Fun.V>, Some{Fun.V.num(t)}, None{}, hg)))
    case Fun.A.z{}:
      Empty.absurd({Imp.Stm.run(RT.S.atom(e), n, size, L(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17), mem) == Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>},
        Shared.Maybe.no_none(Fun.V, Fun.V.z{}, Equal.sym(Maybe<&2, Fun.V>, Some{Fun.V.z{}}, None{}, hg)))

# Frames
# ======

type RdP is Data:
  RdP{v: Fun.V, p: U32}

# whether the memory holds each value at its address, below hp
def Rds(ps: List<&2, RdP>, +mem: Wasm.Mem, +hp: Nat) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{RdP{v, p}, rest}:
      Bool.and(Rd(v, mem, hp, p), Rds(rest, mem, hp))

# a load below hp, after a node at hp
def Ld.keep(+p: U32, +mem: Wasm.Mem, +hp: U32, +vt: U32, +va: U32, +vb: U32, +size: U32,
  +hr: {Nat.is_le(12n+U32.to_nat(hp), U32.to_nat(size)) == True{} : Bool},
  +hp4: {Nat.is_le(4n+U32.to_nat(p), U32.to_nat(hp)) == True{} : Bool}) ->
  {Wasm.Mem.load(p, M3(hp, mem, vt, va, vb)) == Wasm.Mem.load(p, mem) : U32}:
  +m1 = Wasm.Mem.store(hp, mem, vt)
  +m2 = Wasm.Mem.store(U32.add(hp, 4), m1, va)
  +P = U32.to_nat(hp)
  +S = U32.to_nat(size)
  Equal.trans(U32, Wasm.Mem.load(p, M3(hp, mem, vt, va, vb)), Wasm.Mem.load(p, m2), Wasm.Mem.load(p, mem),
    Ld.far(p, U32.add(hp, 8), m2, vb, size,
      %Equal.sym(Nat, U32.to_nat(U32.add(hp, 8)), 8n+P, T8(hp, size, hr)) : {Nat.is_le(4n+U32.to_nat(p), _) == True{} : Bool}
      Le.t(4n+U32.to_nat(p), P, 8n+P, hp4, Shared.Nat.is_le_add_left(P, 8n)),
      %Equal.sym(Nat, U32.to_nat(U32.add(hp, 8)), 8n+P, T8(hp, size, hr)) : {Nat.is_le(4n+_, S) == True{} : Bool}
      hr),
    Equal.trans(U32, Wasm.Mem.load(p, m2), Wasm.Mem.load(p, m1), Wasm.Mem.load(p, mem),
      Ld.far(p, U32.add(hp, 4), m1, va, size,
        %Equal.sym(Nat, U32.to_nat(U32.add(hp, 4)), 4n+P, T4(hp, size, hr)) : {Nat.is_le(4n+U32.to_nat(p), _) == True{} : Bool}
        Le.t(4n+U32.to_nat(p), P, 4n+P, hp4, Shared.Nat.is_le_add_left(P, 4n)),
        %Equal.sym(Nat, U32.to_nat(U32.add(hp, 4)), 4n+P, T4(hp, size, hr)) : {Nat.is_le(4n+_, S) == True{} : Bool}
        Le.k8(hp, size, hr)),
      Ld.far(p, hp, mem, vt, size, hp4, Le.k4(hp, size, hr))))

# Rd.keep, with the bound H of hp
def Rd.keepH(+v: Fun.V, +mem: Wasm.Mem, +p: U32, +hp: U32, +H: Nat, +hH: {U32.to_nat(hp) == H : Nat}, +vt: U32, +va: U32,
  +vb: U32, +size: U32, +hr: {Nat.is_le(12n+H, U32.to_nat(size)) == True{} : Bool},
  +h: {Rd(v, mem, H, p) == True{} : Bool}) -> {Rd(v, M3(hp, mem, vt, va, vb), 12n+H, p) == True{} : Bool}:
  %hH : {Rd(v, M3(hp, mem, vt, va, vb), 12n+_, p) == True{} : Bool}
  Rd.keep(v, mem, p, hp, vt, va, vb, size,
    %Equal.sym(Nat, U32.to_nat(hp), H, hH) : {Nat.is_le(12n+_, U32.to_nat(size)) == True{} : Bool}
    hr,
    %Equal.sym(Nat, U32.to_nat(hp), H, hH) : {Rd(v, mem, _, p) == True{} : Bool}
    h)

def Rds.keep(ps: List<&2, RdP>, +mem: Wasm.Mem, +hp: U32, +H: Nat, +hH: {U32.to_nat(hp) == H : Nat}, +vt: U32, +va: U32,
  +vb: U32, +size: U32, +hr: {Nat.is_le(12n+H, U32.to_nat(size)) == True{} : Bool},
  +h: {Rds(ps, mem, H) == True{} : Bool}) -> {Rds(ps, M3(hp, mem, vt, va, vb), 12n+H) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case Con{RdP{+v, +p}, +rest}:
      And.mk(Rd(v, M3(hp, mem, vt, va, vb), 12n+H, p), Rds(rest, M3(hp, mem, vt, va, vb), 12n+H),
        Rd.keepH(v, mem, p, hp, H, hH, vt, va, vb, size, hr, And.l(Rd(v, mem, H, p), Rds(rest, mem, H), h)),
        Rds.keep(rest, mem, hp, H, hH, vt, va, vb, size, hr, And.r(Rd(v, mem, H, p), Rds(rest, mem, H), h)))

# Calls
# =====

# the atoms ys, the first first
def Enc.atoms(ys: List<&2, Fun.A>) -> Fun.V:
  match ys:
    case Nil{}:
      Fun.V.z{}
    case Con{y, rest}:
      Fun.V.n{0n, RT.Enc.atom(y), Enc.atoms(rest)}

def Mb.d(m: Maybe<&2, Fun.V>) -> Fun.V:
  match m:
    case Some{v}:
      v
    case None{}:
      Fun.V.z{}

def Mb.some(m: Maybe<&2, Fun.V>, h: {Maybe.is_some(&2, Fun.V, m) == True{} : Bool}) -> {m == Some{Mb.d(m)} : Maybe<&2, Fun.V>}:
  match m:
    case Some{v}:
      {==}
    case None{}:
      Shared.Bool.absurd({None{} == Some{Fun.V.z{}} : Maybe<&2, Fun.V>}, h)

def Mb.none(m: Maybe<&2, Fun.V>, h: {Maybe.is_some(&2, Fun.V, m) == False{} : Bool}) -> {m == None{} : Maybe<&2, Fun.V>}:
  match m:
    case Some{v}:
      Shared.Bool.absurd({Some{v} == None{} : Maybe<&2, Fun.V>}, Equal.sym(Bool, True{}, False{}, h))
    case None{}:
      {==}

def A.ok(a: Fun.A, +env: List<&2, Fun.V>) -> Bool:
  Maybe.is_some(&2, Fun.V, Fun.A.get(a, env))

def A.d(a: Fun.A, +env: List<&2, Fun.V>) -> Fun.V:
  Mb.d(Fun.A.get(a, env))

# whether the environment has each atom of ys
def Args.all(ys: List<&2, Fun.A>, +env: List<&2, Fun.V>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{y, rest}:
      Bool.and(A.ok(y, env), Args.all(rest, env))

# the values of ys onto vs, the last first
def Args.list(ys: List<&2, Fun.A>, +env: List<&2, Fun.V>, vs: List<&2, Fun.V>) -> List<&2, Fun.V>:
  match ys:
    case Nil{}:
      vs
    case Con{y, rest}:
      Args.list(rest, env, Con{A.d(y, env), vs})

# the fuel of the loop on ys
def Args.need(ys: List<&2, Fun.A>) -> Nat:
  match ys:
    case Nil{}:
      1n
    case Con{y, rest}:
      1n+Nat.add(1n+Atom.need(y), Args.need(rest))

# the top of the heap after the loop on ys, from H
def Args.top(ys: List<&2, Fun.A>, H: Nat) -> Nat:
  match ys:
    case Nil{}:
      H
    case Con{y, rest}:
      Args.top(rest, 12n+H)

def Args.top_ge(ys: List<&2, Fun.A>, +H: Nat) -> {Nat.is_le(H, Args.top(ys, H)) == True{} : Bool}:
  match ys:
    case Nil{}:
      Shared.Nat.is_le_refl(H)
    case Con{y, +rest}:
      Le.t(H, 12n+H, Args.top(rest, 12n+H), Shared.Nat.is_le_add_left(H, 12n), Args.top_ge(rest, 12n+H))

# the locals of the loop: hp, y, q, acc, a, i, w, and the memory
type AS is Data:
  AS{hp: U32, y: U32, q: U32, acc: U32, a: U32, i: U32, w: U32, mem: Wasm.Mem}

def AS.step(e: Fun.A, s: AS, +env: U32) -> AS:
  match s:
    case AS{+hp, y, +q, +acc, a, i, w, +mem}:
      +v = Atom.val(e, Wasm.Mem.load(U32.add(q, 4), mem), env, mem)
      +m3 = M3(hp, mem, 0, v, acc)
      AS{U32.add(hp, 12), v, Wasm.Mem.load(U32.add(q, 8), m3), hp, 0, 0, hp, m3}

def AS.run(ys: List<&2, Fun.A>, s: AS, +env: U32) -> AS:
  match ys:
    case Nil{}:
      s
    case Con{y, rest}:
      AS.run(rest, AS.step(y, s, env), env)

def AS.ls(s: AS, x1: U32, x2: U32, x3: U32, x4: U32, x5: U32, x6: U32, x7: U32, x8: U32, x9: U32, x10: U32, x12: U32) -> List<&2, U32>:
  match s:
    case AS{hp, y, q, acc, a, i, w, mem}:
      L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y, x12, q, acc, a, i, w)

def AS.mem(s: AS) -> Wasm.Mem:
  match s:
    case AS{hp, y, q, acc, a, i, w, mem}:
      mem

def AS.hp(s: AS) -> U32:
  match s:
    case AS{hp, y, q, acc, a, i, w, mem}:
      hp

def AS.acc(s: AS) -> U32:
  match s:
    case AS{hp, y, q, acc, a, i, w, mem}:
      acc

# the loop of the arguments, when the environment has each atom
def Args.some(ys: List<&2, Fun.A>, n: Nat, +env: List<&2, Fun.V>, +hp: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32, +x8: U32, +x9: U32, +x10: U32, +x12: U32, +y0: U32, +q: U32, +acc: U32, +t15: U32,
  +t16: U32, +w: U32, +mem: Wasm.Mem, +size: U32, +H: Nat, +hH: {U32.to_nat(hp) == H : Nat},
  +hq: {Rd(Enc.atoms(ys), mem, H, q) == True{} : Bool}, +hv: {Rd(RT.Enc.list(env), mem, H, x4) == True{} : Bool},
  +hz: {Nat.is_le(1n, H) == True{} : Bool}, +hr: {Nat.is_le(Args.top(ys, H), U32.to_nat(size)) == True{} : Bool},
  +hs: {Nat.is_le(H, U32.to_nat(size)) == True{} : Bool}, +hn: {Nat.is_le(Args.need(ys), n) == True{} : Bool},
  +hall: {Args.all(ys, env) == True{} : Bool}) ->
  {Imp.Stm.run(Imp.Stm.loop{RT.S.args.body()}, n, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem) == Some{Imp.Res.next{AS.ls(AS.run(ys, AS{hp, y0, q, acc, t15, t16, w, mem}, x4), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x12), AS.mem(AS.run(ys, AS{hp, y0, q, acc, t15, t16, w, mem}, x4))}} : Maybe<&2, Imp.Res>}:
  match ys n:
    case Nil{} 0n:
      Shared.Bool.absurd({Imp.Stm.run(Imp.Stm.loop{RT.S.args.body()}, 0n, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem) == Some{Imp.Res.next{L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem}} : Maybe<&2, Imp.Res>}, hn)
    case Nil{} 1n++m:
      %Equal.sym(Maybe<&2, Imp.Res>, Imp.Stm.run(RT.S.args.body(), m, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem), Some{Imp.Res.brk{0n, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem}},
        R.seq_end(RT.S.if(Imp.Exp.eqz{RT.E.l(13n)}, Imp.Stm.break{0n}, Imp.Stm.skip{}), RT.S.all([RT.S.atom(RT.E.ld(4, RT.E.l(13n))), RT.S.alloc(RT.E.k(0), RT.E.l(11n), RT.E.l(14n)), Imp.Stm.set{14n, RT.E.l(17n)}, Imp.Stm.set{13n, RT.E.ld(8, RT.E.l(13n))}]), m, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem,
          {Some{Imp.Res.brk{0n, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem}} : Maybe<&2, Imp.Res>}, {==},
          R.if(Imp.Exp.eqz{RT.E.l(13n)}, Imp.Stm.break{0n}, Imp.Stm.skip{}, m, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem, Bool.to_u32(U32.is_eq(q, 0)), True{},
            Some{Imp.Res.brk{0n, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem}}, {==}, Cond.eqz(q, True{}, hq), {==}))) :
        {Imp.Res.loop(_, x => z => Imp.Stm.run(Imp.Stm.loop{RT.S.args.body()}, m, size, x, z)) == Some{Imp.Res.next{L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem}} : Maybe<&2, Imp.Res>}
      {==}
    case Con{+y, +rest} 0n:
      Shared.Bool.absurd({Imp.Stm.run(Imp.Stm.loop{RT.S.args.body()}, 0n, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem) == Some{Imp.Res.next{AS.ls(AS.run(rest, AS{U32.add(hp, 12), Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), hp, 0, 0, hp, M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)}, x4), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x12), AS.mem(AS.run(rest, AS{U32.add(hp, 12), Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), hp, 0, 0, hp, M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)}, x4))}} : Maybe<&2, Imp.Res>}, hn)
    case Con{+y, +rest} 1n++m:
      %Equal.sym(Maybe<&2, Imp.Res>, Imp.Stm.run(RT.S.args.body(), m, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem), Some{Imp.Res.next{L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), hp, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)}},
        R.seq(RT.S.if(Imp.Exp.eqz{RT.E.l(13n)}, Imp.Stm.break{0n}, Imp.Stm.skip{}), RT.S.all([RT.S.atom(RT.E.ld(4, RT.E.l(13n))), RT.S.alloc(RT.E.k(0), RT.E.l(11n), RT.E.l(14n)), Imp.Stm.set{14n, RT.E.l(17n)}, Imp.Stm.set{13n, RT.E.ld(8, RT.E.l(13n))}]), m, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem, {Some{Imp.Res.next{L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), hp, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)}} : Maybe<&2, Imp.Res>},
    R.if(Imp.Exp.eqz{RT.E.l(13n)}, Imp.Stm.break{0n}, Imp.Stm.skip{}, m, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem, Bool.to_u32(U32.is_eq(q, 0)), False{}, Some{Imp.Res.next{L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem}}, {==}, Cond.node(q, Rd.nz(mem, H, q, 0n, RT.Enc.atom(y), Enc.atoms(rest), hq)), {==}),
  R.seq(RT.S.atom(RT.E.ld(4, RT.E.l(13n))), RT.S.all([RT.S.alloc(RT.E.k(0), RT.E.l(11n), RT.E.l(14n)), Imp.Stm.set{14n, RT.E.l(17n)}, Imp.Stm.set{13n, RT.E.ld(8, RT.E.l(13n))}]), m, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, acc, 0, 0, 0), mem, {Some{Imp.Res.next{L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), hp, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)}} : Maybe<&2, Imp.Res>},
    Atom.some(y, env, RT.E.ld(4, RT.E.l(13n)), hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w, Wasm.Mem.load(U32.add(q, 4), mem), mem, size, H,
      E.load(4, RT.E.l(13n), size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem, q, U32.add(q, 4), {==}, Ad4(q, H, size, Rd.hi(mem, H, q, 0n, RT.Enc.atom(y), Enc.atoms(rest), hq), hs)),
      Rd.a(mem, H, q, 0n, RT.Enc.atom(y), Enc.atoms(rest), hq), hv, hs, m, A.d(y, env), Mb.some(Fun.A.get(y, env), And.l(A.ok(y, env), Args.all(rest, env), hall)), Le.t(1n+Atom.need(y), Nat.add(1n+Atom.need(y), Args.need(rest)), m, Shared.Nat.is_le_add(1n+Atom.need(y), Args.need(rest)), hn)),
  R.seq(RT.S.alloc(RT.E.k(0), RT.E.l(11n), RT.E.l(14n)), RT.S.all([Imp.Stm.set{14n, RT.E.l(17n)}, Imp.Stm.set{13n, RT.E.ld(8, RT.E.l(13n))}]), m, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, acc, 0, 0, 0), mem, L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, acc, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc), {Some{Imp.Res.next{L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), hp, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)}} : Maybe<&2, Imp.Res>},
    R.alloc(RT.E.k(0), RT.E.l(11n), RT.E.l(14n), m, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, acc, 0, 0, 0), mem, hp, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, acc, 0, 0, hp), L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, acc, 0, 0, hp), {==}, {==}, {==}, {==},
        %Equal.sym(Nat, U32.to_nat(hp), H, hH) : {Nat.is_le(12n+_, U32.to_nat(size)) == True{} : Bool}
        Le.t(12n+H, Args.top(rest, 12n+H), U32.to_nat(size), Args.top_ge(rest, 12n+H), hr), {==}, {==}, {==}),
  R.seq(Imp.Stm.set{14n, RT.E.l(17n)}, RT.S.all([Imp.Stm.set{13n, RT.E.ld(8, RT.E.l(13n))}]), m, size, L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, acc, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc), L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, hp, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc), {Some{Imp.Res.next{L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), hp, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)}} : Maybe<&2, Imp.Res>},
    R.set(14n, RT.E.l(17n), m, size, L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, acc, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc), hp, L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, hp, 0, 0, hp), {==}, {==}),
  R.seq(Imp.Stm.set{13n, RT.E.ld(8, RT.E.l(13n))}, Imp.Stm.skip{}, m, size, L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, hp, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc), L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), hp, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc), {Some{Imp.Res.next{L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), hp, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)}} : Maybe<&2, Imp.Res>},
    R.set(13n, RT.E.ld(8, RT.E.l(13n)), m, size, L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, hp, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc), Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), hp, 0, 0, hp),
        E.load(8, RT.E.l(13n), size, L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, hp, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc), q, U32.add(q, 8), {==}, Ad8(q, H, size, Rd.hi(mem, H, q, 0n, RT.Enc.atom(y), Enc.atoms(rest), hq), hs)), {==}),
  {==})))))) :
        {Imp.Res.loop(_, x => z => Imp.Stm.run(Imp.Stm.loop{RT.S.args.body()}, m, size, x, z)) == Some{Imp.Res.next{AS.ls(AS.run(rest, AS{U32.add(hp, 12), Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), hp, 0, 0, hp, M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)}, x4), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x12), AS.mem(AS.run(rest, AS{U32.add(hp, 12), Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), hp, 0, 0, hp, M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)}, x4))}} : Maybe<&2, Imp.Res>}
      Args.some(rest, m, env, U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x12, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), hp, 0, 0, hp, M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc), size, 12n+H,
        %hH : {U32.to_nat(U32.add(hp, 12)) == 12n+_ : Nat}
        U.add_lit(hp, 12, Fits.le(12n+U32.to_nat(hp), size, %Equal.sym(Nat, U32.to_nat(hp), H, hH) : {Nat.is_le(12n+_, U32.to_nat(size)) == True{} : Bool}
        Le.t(12n+H, Args.top(rest, 12n+H), U32.to_nat(size), Args.top_ge(rest, 12n+H), hr))),
        %Equal.sym(U32, Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), Wasm.Mem.load(U32.add(q, 8), mem),
          Ld.keep(U32.add(q, 8), mem, hp, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc, size, %Equal.sym(Nat, U32.to_nat(hp), H, hH) : {Nat.is_le(12n+_, U32.to_nat(size)) == True{} : Bool}
        Le.t(12n+H, Args.top(rest, 12n+H), U32.to_nat(size), Args.top_ge(rest, 12n+H), hr),
            %Equal.sym(Nat, U32.to_nat(U32.add(q, 8)), 8n+U32.to_nat(q), T8(q, size, Le.t(12n+U32.to_nat(q), H, U32.to_nat(size), Rd.hi(mem, H, q, 0n, RT.Enc.atom(y), Enc.atoms(rest), hq), hs))) :
              {Nat.is_le(4n+_, U32.to_nat(hp)) == True{} : Bool}
            %Equal.sym(Nat, U32.to_nat(hp), H, hH) : {Nat.is_le(12n+U32.to_nat(q), _) == True{} : Bool}
            Rd.hi(mem, H, q, 0n, RT.Enc.atom(y), Enc.atoms(rest), hq))) : {Rd(Enc.atoms(rest), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc), 12n+H, _) == True{} : Bool}
        Rd.keepH(Enc.atoms(rest), mem, Wasm.Mem.load(U32.add(q, 8), mem), hp, H, hH, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc, size,
          Le.t(12n+H, Args.top(rest, 12n+H), U32.to_nat(size), Args.top_ge(rest, 12n+H), hr), Rd.b(mem, H, q, 0n, RT.Enc.atom(y), Enc.atoms(rest), hq)),
        Rd.keepH(RT.Enc.list(env), mem, x4, hp, H, hH, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc, size,
        Le.t(12n+H, Args.top(rest, 12n+H), U32.to_nat(size), Args.top_ge(rest, 12n+H), hr), hv), {==}, hr, Le.t(12n+H, Args.top(rest, 12n+H), U32.to_nat(size), Args.top_ge(rest, 12n+H), hr), Le.t(Args.need(rest), Nat.add(1n+Atom.need(y), Args.need(rest)), m, Shared.Nat.is_le_add_left(Args.need(rest), 1n+Atom.need(y)), hn), And.r(A.ok(y, env), Args.all(rest, env), hall))

def And.r_false(+a: Bool, +b: Bool, +ha: {a == True{} : Bool}, +h: {Bool.and(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  %ha : {Bool.and(_, b) == False{} : Bool}
  h

# the loop of the arguments, when the environment lacks an atom
def Args.none(ys: List<&2, Fun.A>, n: Nat, +env: List<&2, Fun.V>, +hp: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32, +x8: U32, +x9: U32, +x10: U32, +x12: U32, +y0: U32, +q: U32, +acc: U32, +t15: U32,
  +t16: U32, +w: U32, +mem: Wasm.Mem, +size: U32, +H: Nat, +hH: {U32.to_nat(hp) == H : Nat},
  +hq: {Rd(Enc.atoms(ys), mem, H, q) == True{} : Bool}, +hv: {Rd(RT.Enc.list(env), mem, H, x4) == True{} : Bool},
  +hz: {Nat.is_le(1n, H) == True{} : Bool}, +hr: {Nat.is_le(Args.top(ys, H), U32.to_nat(size)) == True{} : Bool},
  +hs: {Nat.is_le(H, U32.to_nat(size)) == True{} : Bool}, +hn: {Nat.is_le(Args.need(ys), n) == True{} : Bool},
  +hall: {Args.all(ys, env) == False{} : Bool}) ->
  {Imp.Stm.run(Imp.Stm.loop{RT.S.args.body()}, n, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem) == Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>}:
  match ys n:
    case Nil{} _:
      Shared.Bool.absurd({Imp.Stm.run(Imp.Stm.loop{RT.S.args.body()}, n, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem) == Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>},
        Equal.sym(Bool, True{}, False{}, hall))
    case Con{+y, +rest} 0n:
      Shared.Bool.absurd({Imp.Stm.run(Imp.Stm.loop{RT.S.args.body()}, 0n, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem) == Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>}, hn)
    case Con{+y, +rest} 1n++m:
      Shared.Bool.elim(A.ok(y, env), b => {A.ok(y, env) == b : Bool} -> {Imp.Stm.run(Imp.Stm.loop{RT.S.args.body()}, 1n+m, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem) == Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>},
        +hc =>
          %Equal.sym(Maybe<&2, Imp.Res>, Imp.Stm.run(RT.S.args.body(), m, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem), Some{Imp.Res.next{L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), hp, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)}},
            R.seq(RT.S.if(Imp.Exp.eqz{RT.E.l(13n)}, Imp.Stm.break{0n}, Imp.Stm.skip{}), RT.S.all([RT.S.atom(RT.E.ld(4, RT.E.l(13n))), RT.S.alloc(RT.E.k(0), RT.E.l(11n), RT.E.l(14n)), Imp.Stm.set{14n, RT.E.l(17n)}, Imp.Stm.set{13n, RT.E.ld(8, RT.E.l(13n))}]), m, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem, {Some{Imp.Res.next{L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), hp, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)}} : Maybe<&2, Imp.Res>},
    R.if(Imp.Exp.eqz{RT.E.l(13n)}, Imp.Stm.break{0n}, Imp.Stm.skip{}, m, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem, Bool.to_u32(U32.is_eq(q, 0)), False{}, Some{Imp.Res.next{L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem}}, {==}, Cond.node(q, Rd.nz(mem, H, q, 0n, RT.Enc.atom(y), Enc.atoms(rest), hq)), {==}),
  R.seq(RT.S.atom(RT.E.ld(4, RT.E.l(13n))), RT.S.all([RT.S.alloc(RT.E.k(0), RT.E.l(11n), RT.E.l(14n)), Imp.Stm.set{14n, RT.E.l(17n)}, Imp.Stm.set{13n, RT.E.ld(8, RT.E.l(13n))}]), m, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, acc, 0, 0, 0), mem, {Some{Imp.Res.next{L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), hp, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)}} : Maybe<&2, Imp.Res>},
    Atom.some(y, env, RT.E.ld(4, RT.E.l(13n)), hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w, Wasm.Mem.load(U32.add(q, 4), mem), mem, size, H,
      E.load(4, RT.E.l(13n), size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem, q, U32.add(q, 4), {==}, Ad4(q, H, size, Rd.hi(mem, H, q, 0n, RT.Enc.atom(y), Enc.atoms(rest), hq), hs)),
      Rd.a(mem, H, q, 0n, RT.Enc.atom(y), Enc.atoms(rest), hq), hv, hs, m, A.d(y, env), Mb.some(Fun.A.get(y, env), hc), Le.t(1n+Atom.need(y), Nat.add(1n+Atom.need(y), Args.need(rest)), m, Shared.Nat.is_le_add(1n+Atom.need(y), Args.need(rest)), hn)),
  R.seq(RT.S.alloc(RT.E.k(0), RT.E.l(11n), RT.E.l(14n)), RT.S.all([Imp.Stm.set{14n, RT.E.l(17n)}, Imp.Stm.set{13n, RT.E.ld(8, RT.E.l(13n))}]), m, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, acc, 0, 0, 0), mem, L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, acc, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc), {Some{Imp.Res.next{L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), hp, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)}} : Maybe<&2, Imp.Res>},
    R.alloc(RT.E.k(0), RT.E.l(11n), RT.E.l(14n), m, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, acc, 0, 0, 0), mem, hp, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, acc, 0, 0, hp), L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, acc, 0, 0, hp), {==}, {==}, {==}, {==},
        %Equal.sym(Nat, U32.to_nat(hp), H, hH) : {Nat.is_le(12n+_, U32.to_nat(size)) == True{} : Bool}
        Le.t(12n+H, Args.top(rest, 12n+H), U32.to_nat(size), Args.top_ge(rest, 12n+H), hr), {==}, {==}, {==}),
  R.seq(Imp.Stm.set{14n, RT.E.l(17n)}, RT.S.all([Imp.Stm.set{13n, RT.E.ld(8, RT.E.l(13n))}]), m, size, L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, acc, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc), L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, hp, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc), {Some{Imp.Res.next{L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), hp, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)}} : Maybe<&2, Imp.Res>},
    R.set(14n, RT.E.l(17n), m, size, L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, acc, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc), hp, L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, hp, 0, 0, hp), {==}, {==}),
  R.seq(Imp.Stm.set{13n, RT.E.ld(8, RT.E.l(13n))}, Imp.Stm.skip{}, m, size, L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, hp, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc), L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), hp, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc), {Some{Imp.Res.next{L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), hp, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)}} : Maybe<&2, Imp.Res>},
    R.set(13n, RT.E.ld(8, RT.E.l(13n)), m, size, L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, hp, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc), Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), hp, 0, 0, hp),
        E.load(8, RT.E.l(13n), size, L(U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), x12, q, hp, 0, 0, hp), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc), q, U32.add(q, 8), {==}, Ad8(q, H, size, Rd.hi(mem, H, q, 0n, RT.Enc.atom(y), Enc.atoms(rest), hq), hs)), {==}),
  {==})))))) :
            {Imp.Res.loop(_, x => z => Imp.Stm.run(Imp.Stm.loop{RT.S.args.body()}, m, size, x, z)) == Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>}
          Args.none(rest, m, env, U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x12, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), hp, 0, 0, hp, M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc), size, 12n+H,
            %hH : {U32.to_nat(U32.add(hp, 12)) == 12n+_ : Nat}
        U.add_lit(hp, 12, Fits.le(12n+U32.to_nat(hp), size, %Equal.sym(Nat, U32.to_nat(hp), H, hH) : {Nat.is_le(12n+_, U32.to_nat(size)) == True{} : Bool}
        Le.t(12n+H, Args.top(rest, 12n+H), U32.to_nat(size), Args.top_ge(rest, 12n+H), hr))),
            %Equal.sym(U32, Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), Wasm.Mem.load(U32.add(q, 8), mem),
          Ld.keep(U32.add(q, 8), mem, hp, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc, size, %Equal.sym(Nat, U32.to_nat(hp), H, hH) : {Nat.is_le(12n+_, U32.to_nat(size)) == True{} : Bool}
        Le.t(12n+H, Args.top(rest, 12n+H), U32.to_nat(size), Args.top_ge(rest, 12n+H), hr),
            %Equal.sym(Nat, U32.to_nat(U32.add(q, 8)), 8n+U32.to_nat(q), T8(q, size, Le.t(12n+U32.to_nat(q), H, U32.to_nat(size), Rd.hi(mem, H, q, 0n, RT.Enc.atom(y), Enc.atoms(rest), hq), hs))) :
              {Nat.is_le(4n+_, U32.to_nat(hp)) == True{} : Bool}
            %Equal.sym(Nat, U32.to_nat(hp), H, hH) : {Nat.is_le(12n+U32.to_nat(q), _) == True{} : Bool}
            Rd.hi(mem, H, q, 0n, RT.Enc.atom(y), Enc.atoms(rest), hq))) : {Rd(Enc.atoms(rest), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc), 12n+H, _) == True{} : Bool}
        Rd.keepH(Enc.atoms(rest), mem, Wasm.Mem.load(U32.add(q, 8), mem), hp, H, hH, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc, size,
          Le.t(12n+H, Args.top(rest, 12n+H), U32.to_nat(size), Args.top_ge(rest, 12n+H), hr), Rd.b(mem, H, q, 0n, RT.Enc.atom(y), Enc.atoms(rest), hq)),
            Rd.keepH(RT.Enc.list(env), mem, x4, hp, H, hH, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc, size,
        Le.t(12n+H, Args.top(rest, 12n+H), U32.to_nat(size), Args.top_ge(rest, 12n+H), hr), hv), {==}, hr, Le.t(12n+H, Args.top(rest, 12n+H), U32.to_nat(size), Args.top_ge(rest, 12n+H), hr), Le.t(Args.need(rest), Nat.add(1n+Atom.need(y), Args.need(rest)), m, Shared.Nat.is_le_add_left(Args.need(rest), 1n+Atom.need(y)), hn), And.r_false(A.ok(y, env), Args.all(rest, env), hc, hall)),
        +hc =>
          %Equal.sym(Maybe<&2, Imp.Res>, Imp.Stm.run(RT.S.args.body(), m, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem), Some{Imp.Res.trap{}},
            R.seq(RT.S.if(Imp.Exp.eqz{RT.E.l(13n)}, Imp.Stm.break{0n}, Imp.Stm.skip{}), RT.S.all([RT.S.atom(RT.E.ld(4, RT.E.l(13n))), RT.S.alloc(RT.E.k(0), RT.E.l(11n), RT.E.l(14n)), Imp.Stm.set{14n, RT.E.l(17n)}, Imp.Stm.set{13n, RT.E.ld(8, RT.E.l(13n))}]), m, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem, {Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>},
    R.if(Imp.Exp.eqz{RT.E.l(13n)}, Imp.Stm.break{0n}, Imp.Stm.skip{}, m, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem, Bool.to_u32(U32.is_eq(q, 0)), False{}, Some{Imp.Res.next{L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem}}, {==}, Cond.node(q, Rd.nz(mem, H, q, 0n, RT.Enc.atom(y), Enc.atoms(rest), hq)), {==}),
  R.seq_end(RT.S.atom(RT.E.ld(4, RT.E.l(13n))), RT.S.all([RT.S.alloc(RT.E.k(0), RT.E.l(11n), RT.E.l(14n)), Imp.Stm.set{14n, RT.E.l(17n)}, Imp.Stm.set{13n, RT.E.ld(8, RT.E.l(13n))}]), m, size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem, {Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>}, {==},
    Atom.none(y, env, RT.E.ld(4, RT.E.l(13n)), hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w, Wasm.Mem.load(U32.add(q, 4), mem), mem, size, H,
      E.load(4, RT.E.l(13n), size, L(hp, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y0, x12, q, acc, t15, t16, w), mem, q, U32.add(q, 4), {==}, Ad4(q, H, size, Rd.hi(mem, H, q, 0n, RT.Enc.atom(y), Enc.atoms(rest), hq), hs)),
      Rd.a(mem, H, q, 0n, RT.Enc.atom(y), Enc.atoms(rest), hq), hv, hs, m, Mb.none(Fun.A.get(y, env), hc), Le.t(1n+Atom.need(y), Nat.add(1n+Atom.need(y), Args.need(rest)), m, Shared.Nat.is_le_add(1n+Atom.need(y), Args.need(rest)), hn))))) :
            {Imp.Res.loop(_, x => z => Imp.Stm.run(Imp.Stm.loop{RT.S.args.body()}, m, size, x, z)) == Some{Imp.Res.trap{}} : Maybe<&2, Imp.Res>}
          {==})({==})

# Rd.new, with the bound H of hp
def Rd.newH(+hp: U32, +H: Nat, +hH: {U32.to_nat(hp) == H : Nat}, +mem: Wasm.Mem, +vt: U32, +va: U32, +vb: U32, +size: U32,
  +t: Nat, +a: Fun.V, +b: Fun.V, +hz: {Nat.is_le(1n, H) == True{} : Bool},
  +hr: {Nat.is_le(12n+H, U32.to_nat(size)) == True{} : Bool}, +ht: {Nat.is_eq(U32.to_nat(vt), t) == True{} : Bool},
  +ha: {Rd(a, mem, H, va) == True{} : Bool}, +hb: {Rd(b, mem, H, vb) == True{} : Bool}) ->
  {Rd(Fun.V.n{t, a, b}, M3(hp, mem, vt, va, vb), 12n+H, hp) == True{} : Bool}:
  %hH : {Rd(Fun.V.n{t, a, b}, M3(hp, mem, vt, va, vb), 12n+_, hp) == True{} : Bool}
  Rd.new(hp, mem, vt, va, vb, size, t, a, b,
    %Equal.sym(Nat, U32.to_nat(hp), H, hH) : {Nat.is_le(1n, _) == True{} : Bool}
    hz,
    %Equal.sym(Nat, U32.to_nat(hp), H, hH) : {Nat.is_le(12n+_, U32.to_nat(size)) == True{} : Bool}
    hr, ht,
    %Equal.sym(Nat, U32.to_nat(hp), H, hH) : {Rd(a, mem, _, va) == True{} : Bool}
    ha,
    %Equal.sym(Nat, U32.to_nat(hp), H, hH) : {Rd(b, mem, _, vb) == True{} : Bool}
    hb)

def Rdm.some(+m: Maybe<&2, Fun.V>, -v: Fun.V, +mem: Wasm.Mem, +hp: Nat, +p: U32, +hm: {m == Some{v} : Maybe<&2, Fun.V>},
  +h: {Rd.m(m, mem, hp, p) == True{} : Bool}) -> {Rd(v, mem, hp, p) == True{} : Bool}:
  %hm : {Rd.m(_, mem, hp, p) == True{} : Bool}
  h

# what the memory holds after the loop of the arguments: their values onto
# vs, the environment, and the values of ps
def Args.rd(ys: List<&2, Fun.A>, +env: List<&2, Fun.V>, +vs: List<&2, Fun.V>, +hp: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32, +x8: U32, +x9: U32, +x10: U32, +x12: U32, +y0: U32, +q: U32, +acc: U32,
  +t15: U32, +t16: U32, +w: U32, +mem: Wasm.Mem, +size: U32, +H: Nat, +hH: {U32.to_nat(hp) == H : Nat},
  +hq: {Rd(Enc.atoms(ys), mem, H, q) == True{} : Bool}, +hv: {Rd(RT.Enc.list(env), mem, H, x4) == True{} : Bool},
  +hacc: {Rd(RT.Enc.list(vs), mem, H, acc) == True{} : Bool},
  +hz: {Nat.is_le(1n, H) == True{} : Bool}, +hr: {Nat.is_le(Args.top(ys, H), U32.to_nat(size)) == True{} : Bool},
  +hs: {Nat.is_le(H, U32.to_nat(size)) == True{} : Bool}, +hall: {Args.all(ys, env) == True{} : Bool},
  +ps: List<&2, RdP>, +hps: {Rds(ps, mem, H) == True{} : Bool}) ->
  {Bool.and(Rd(RT.Enc.list(Args.list(ys, env, vs)), AS.mem(AS.run(ys, AS{hp, y0, q, acc, t15, t16, w, mem}, x4)), Args.top(ys, H), AS.acc(AS.run(ys, AS{hp, y0, q, acc, t15, t16, w, mem}, x4))),
    Bool.and(Rd(RT.Enc.list(env), AS.mem(AS.run(ys, AS{hp, y0, q, acc, t15, t16, w, mem}, x4)), Args.top(ys, H), x4), Rds(ps, AS.mem(AS.run(ys, AS{hp, y0, q, acc, t15, t16, w, mem}, x4)), Args.top(ys, H)))) == True{} : Bool}:
  match ys:
    case Nil{}:
      And.mk(Rd(RT.Enc.list(vs), mem, H, acc), Bool.and(Rd(RT.Enc.list(env), mem, H, x4), Rds(ps, mem, H)), hacc,
        And.mk(Rd(RT.Enc.list(env), mem, H, x4), Rds(ps, mem, H), hv, hps))
    case Con{+y, +rest}:
      Args.rd(rest, env, Con{A.d(y, env), vs}, U32.add(hp, 12), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x12, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), hp, 0, 0, hp, M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc), size, 12n+H,
        %hH : {U32.to_nat(U32.add(hp, 12)) == 12n+_ : Nat}
        U.add_lit(hp, 12, Fits.le(12n+U32.to_nat(hp), size, %Equal.sym(Nat, U32.to_nat(hp), H, hH) : {Nat.is_le(12n+_, U32.to_nat(size)) == True{} : Bool}
        Le.t(12n+H, Args.top(rest, 12n+H), U32.to_nat(size), Args.top_ge(rest, 12n+H), hr))),
        %Equal.sym(U32, Wasm.Mem.load(U32.add(q, 8), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc)), Wasm.Mem.load(U32.add(q, 8), mem),
          Ld.keep(U32.add(q, 8), mem, hp, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc, size, %Equal.sym(Nat, U32.to_nat(hp), H, hH) : {Nat.is_le(12n+_, U32.to_nat(size)) == True{} : Bool}
        Le.t(12n+H, Args.top(rest, 12n+H), U32.to_nat(size), Args.top_ge(rest, 12n+H), hr),
            %Equal.sym(Nat, U32.to_nat(U32.add(q, 8)), 8n+U32.to_nat(q), T8(q, size, Le.t(12n+U32.to_nat(q), H, U32.to_nat(size), Rd.hi(mem, H, q, 0n, RT.Enc.atom(y), Enc.atoms(rest), hq), hs))) :
              {Nat.is_le(4n+_, U32.to_nat(hp)) == True{} : Bool}
            %Equal.sym(Nat, U32.to_nat(hp), H, hH) : {Nat.is_le(12n+U32.to_nat(q), _) == True{} : Bool}
            Rd.hi(mem, H, q, 0n, RT.Enc.atom(y), Enc.atoms(rest), hq))) : {Rd(Enc.atoms(rest), M3(hp, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc), 12n+H, _) == True{} : Bool}
        Rd.keepH(Enc.atoms(rest), mem, Wasm.Mem.load(U32.add(q, 8), mem), hp, H, hH, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc, size,
          Le.t(12n+H, Args.top(rest, 12n+H), U32.to_nat(size), Args.top_ge(rest, 12n+H), hr), Rd.b(mem, H, q, 0n, RT.Enc.atom(y), Enc.atoms(rest), hq)),
        Rd.keepH(RT.Enc.list(env), mem, x4, hp, H, hH, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc, size,
        Le.t(12n+H, Args.top(rest, 12n+H), U32.to_nat(size), Args.top_ge(rest, 12n+H), hr), hv),
        Rd.newH(hp, H, hH, mem, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc, size, 0n, A.d(y, env), RT.Enc.list(vs), hz, Le.t(12n+H, Args.top(rest, 12n+H), U32.to_nat(size), Args.top_ge(rest, 12n+H), hr), {==},
          Rdm.some(Fun.A.get(y, env), A.d(y, env), mem, H, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), Mb.some(Fun.A.get(y, env), And.l(A.ok(y, env), Args.all(rest, env), hall)),
            Atom.rd(y, env, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem, H, Rd.a(mem, H, q, 0n, RT.Enc.atom(y), Enc.atoms(rest), hq), hv)), hacc),
        {==}, hr, Le.t(12n+H, Args.top(rest, 12n+H), U32.to_nat(size), Args.top_ge(rest, 12n+H), hr), And.r(A.ok(y, env), Args.all(rest, env), hall), ps,
        Rds.keep(ps, mem, hp, H, hH, 0, Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), x4, mem), acc, size, Le.t(12n+H, Args.top(rest, 12n+H), U32.to_nat(size), Args.top_ge(rest, 12n+H), hr), hps))

def Args.hp(ys: List<&2, Fun.A>, +env: U32, +hp: U32, +y0: U32, +q: U32, +acc: U32, +t15: U32, +t16: U32, +w: U32,
  +mem: Wasm.Mem, +size: U32, +H: Nat, +hH: {U32.to_nat(hp) == H : Nat},
  +hr: {Nat.is_le(Args.top(ys, H), U32.to_nat(size)) == True{} : Bool}) ->
  {U32.to_nat(AS.hp(AS.run(ys, AS{hp, y0, q, acc, t15, t16, w, mem}, env))) == Args.top(ys, H) : Nat}:
  match ys:
    case Nil{}:
      hH
    case Con{+y, +rest}:
      +v = Atom.val(y, Wasm.Mem.load(U32.add(q, 4), mem), env, mem)
      +m3 = M3(hp, mem, 0, v, acc)
      Args.hp(rest, env, U32.add(hp, 12), v, Wasm.Mem.load(U32.add(q, 8), m3), hp, 0, 0, hp, m3, size, 12n+H,
        %hH : {U32.to_nat(U32.add(hp, 12)) == 12n+_ : Nat}
        U.add_lit(hp, 12, Fits.le(12n+U32.to_nat(hp), size, %Equal.sym(Nat, U32.to_nat(hp), H, hH) : {Nat.is_le(12n+_, U32.to_nat(size)) == True{} : Bool}
        Le.t(12n+H, Args.top(rest, 12n+H), U32.to_nat(size), Args.top_ge(rest, 12n+H), hr))), hr)

# The arguments of a call
# =======================
#
# The image holds the atoms of a call from the last; the loop of the
# arguments makes the environment of the call from the first.

def Rev(xs: List<&2, Fun.A>, us: List<&2, Fun.A>) -> List<&2, Fun.A>:
  match xs:
    case Nil{}:
      us
    case Con{x, rest}:
      Rev(rest, Con{x, us})

def Args.enc(xs: List<&2, Fun.A>, us: List<&2, Fun.A>) -> {RT.Enc.args(xs, Enc.atoms(us)) == Enc.atoms(Rev(xs, us)) : Fun.V}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      Args.enc(rest, Con{x, us})

# the values of xs, z where the environment has none
def Ds(xs: List<&2, Fun.A>, +env: List<&2, Fun.V>) -> List<&2, Fun.V>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      Con{A.d(x, env), Ds(rest, env)}

# whether the environment has each atom of xs
def Ok(xs: List<&2, Fun.A>, +env: List<&2, Fun.V>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, rest}:
      Bool.and(A.ok(x, env), Ok(rest, env))

def Args.list_rev(xs: List<&2, Fun.A>, +env: List<&2, Fun.V>, us: List<&2, Fun.A>, vs: List<&2, Fun.V>) ->
  {Args.list(Rev(xs, us), env, vs) == Args.list(us, env, List.append(&2, Fun.V, Ds(xs, env), vs)) : List<&2, Fun.V>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      Args.list_rev(rest, env, Con{x, us}, vs)

def Band.swap(a: Bool, b: Bool, c: Bool) -> {Bool.and(b, Bool.and(a, c)) == Bool.and(Bool.and(a, b), c) : Bool}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} _:
      {==}
    case False{} True{} _:
      {==}
    case False{} False{} _:
      {==}

def Band.true(b: Bool) -> {Bool.and(b, True{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Args.all_rev(xs: List<&2, Fun.A>, +env: List<&2, Fun.V>, +us: List<&2, Fun.A>) ->
  {Args.all(Rev(xs, us), env) == Bool.and(Ok(xs, env), Args.all(us, env)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Equal.trans(Bool, Args.all(Rev(rest, Con{x, us}), env), Bool.and(Ok(rest, env), Bool.and(A.ok(x, env), Args.all(us, env))),
        Bool.and(Bool.and(A.ok(x, env), Ok(rest, env)), Args.all(us, env)),
        Args.all_rev(rest, env, Con{x, us}), Band.swap(A.ok(x, env), Ok(rest, env), Args.all(us, env)))

def Ok.some(xs: List<&2, Fun.A>, +env: List<&2, Fun.V>, +h: {Ok(xs, env) == True{} : Bool}) ->
  {Fun.As.get(xs, env) == Some{Ds(xs, env)} : Maybe<&2, List<&2, Fun.V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %Equal.sym(Maybe<&2, Fun.V>, Fun.A.get(x, env), Some{A.d(x, env)},
        Mb.some(Fun.A.get(x, env), And.l(A.ok(x, env), Ok(rest, env), h))) :
        {Fun.As.get.con(_, Fun.As.get(rest, env)) == Some{Ds(Con{x, rest}, env)} : Maybe<&2, List<&2, Fun.V>>}
      %Equal.sym(Maybe<&2, List<&2, Fun.V>>, Fun.As.get(rest, env), Some{Ds(rest, env)},
        Ok.some(rest, env, And.r(A.ok(x, env), Ok(rest, env), h))) :
        {Fun.As.get.con(Some{A.d(x, env)}, _) == Some{Ds(Con{x, rest}, env)} : Maybe<&2, List<&2, Fun.V>>}
      {==}

def Ok.none(xs: List<&2, Fun.A>, +env: List<&2, Fun.V>, +h: {Ok(xs, env) == False{} : Bool}) ->
  {Fun.As.get(xs, env) == None{} : Maybe<&2, List<&2, Fun.V>>}:
  match xs:
    case Nil{}:
      Shared.Bool.absurd({Fun.As.get([], env) == None{} : Maybe<&2, List<&2, Fun.V>>}, Equal.sym(Bool, True{}, False{}, h))
    case Con{+x, +rest}:
      Shared.Bool.elim(A.ok(x, env),
        b => {A.ok(x, env) == b : Bool} -> {Fun.As.get(Con{x, rest}, env) == None{} : Maybe<&2, List<&2, Fun.V>>},
        +hc =>
          %Equal.sym(Maybe<&2, Fun.V>, Fun.A.get(x, env), Some{A.d(x, env)}, Mb.some(Fun.A.get(x, env), hc)) :
            {Fun.As.get.con(_, Fun.As.get(rest, env)) == None{} : Maybe<&2, List<&2, Fun.V>>}
          %Equal.sym(Maybe<&2, List<&2, Fun.V>>, Fun.As.get(rest, env), None{},
            Ok.none(rest, env, And.r_false(A.ok(x, env), Ok(rest, env), hc, h))) :
            {Fun.As.get.con(Some{A.d(x, env)}, _) == None{} : Maybe<&2, List<&2, Fun.V>>}
          {==},
        +hc =>
          %Equal.sym(Maybe<&2, Fun.V>, Fun.A.get(x, env), None{}, Mb.none(Fun.A.get(x, env), hc)) :
            {Fun.As.get.con(_, Fun.As.get(rest, env)) == None{} : Maybe<&2, List<&2, Fun.V>>}
          {==})({==})

def List.append_nil(xs: List<&2, Fun.V>) -> {List.append(&2, Fun.V, xs, []) == xs : List<&2, Fun.V>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      Equal.cong(List<&2, Fun.V>, List<&2, Fun.V>, t => Con{x, t}, List.append(&2, Fun.V, rest, []), rest, List.append_nil(rest))
