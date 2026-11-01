# compiler: the copy's view of the heap
# =====================================
#
# In the middle of a copy (M.copy.walk), HS does not hold of the cells: a
# new cell on the walk's stack has a term's tag, field 1 is the stack's link,
# not a count, and its fields hold the parts of its source that are still to
# copy, which their counts do not count. The proofs of the copy (proof_copy_hs
# and the rest) keep HS of a view instead: the cells v, which agree with the
# real cells m but at the cells zs of the stacks (Agr), where v holds cells
# that point nowhere and that nothing points to. The machine's statements run
# on m; a statement that never reads nor writes a cell of zs runs the same
# on v, so the shared lemmas (alloc.post) can be used on v.
#
# Here: Agr and Kp (the cells zs stay), their stores, and the simulation of
# M.dec (sim.dec): its run on m and on v ends with the same registers, and
# cells that still agree.

import Base
import ./impl.bend as C
import ./proof_need.bend as N
import ./proof_mach_defs.bend as PM
import ./proof_mach_exec.bend as X

# Agreement
# ---------

# the cells m and v agree at every cell out of zs
def Agr(+m: C.Cir.Cells, +v: C.Cir.Cells, +zs: List<&2, U32>) -> Type:
  @q: U32 -> {PM.Mem(zs, q) == False{} : Bool} -> {C.Cir.Cells.get(m, q) == C.Cir.Cells.get(v, q) : C.Cir.Cell}

# the cells m2 keep the cells of zs that m has
def Kp(+m: C.Cir.Cells, +m2: C.Cir.Cells, +zs: List<&2, U32>) -> Type:
  @q: U32 -> {PM.Mem(zs, q) == True{} : Bool} -> {C.Cir.Cells.get(m2, q) == C.Cir.Cells.get(m, q) : C.Cir.Cell}

def kp.refl(+m: C.Cir.Cells, +zs: List<&2, U32>) -> Kp(m, m, zs):
  +q => +h => {==}

def kp.trans(+m: C.Cir.Cells, +m2: C.Cir.Cells, +m3: C.Cir.Cells, +zs: List<&2, U32>, a: Kp(m, m2, zs), b: Kp(m2, m3, zs)) ->
  Kp(m, m3, zs):
  +q => +h => Equal.trans(C.Cir.Cell, C.Cir.Cells.get(m3, q), C.Cir.Cells.get(m2, q), C.Cir.Cells.get(m, q), b(q, h), a(q, h))

# a cell of zs is not one out of zs
def mem.ne.b(b: Bool, +zs: List<&2, U32>, +q: U32, +i: U32, eb: {U32.is_eq(q, i) == b : Bool},
  hq: {PM.Mem(zs, q) == True{} : Bool}, hi: {PM.Mem(zs, i) == False{} : Bool}) -> {U32.is_eq(q, i) == False{} : Bool}:
  match b:
    case True{}:
      +e = PM.u32.eq(q, i, eb)
      PM.bool.ft({U32.is_eq(q, i) == False{} : Bool}, Equal.trans(Bool, False{}, PM.Mem(zs, q), True{},
        Equal.sym(Bool, PM.Mem(zs, q), False{}, (%Equal.sym(U32, q, i, e) : {PM.Mem(zs, _) == False{} : Bool}; hi)), hq))
    case False{}:
      eb

def mem.ne(+zs: List<&2, U32>, +q: U32, +i: U32, hq: {PM.Mem(zs, q) == True{} : Bool}, hi: {PM.Mem(zs, i) == False{} : Bool}) ->
  {U32.is_eq(q, i) == False{} : Bool}:
  mem.ne.b(U32.is_eq(q, i), zs, q, i, {==}, hq, hi)

# a set at a cell out of zs keeps the cells of zs
def kp.set(+m: C.Cir.Cells, +m2: C.Cir.Cells, +zs: List<&2, U32>, +i: U32, +c: C.Cir.Cell, k: Kp(m, m2, zs),
  hi: {PM.Mem(zs, i) == False{} : Bool}) -> Kp(m, C.Cir.Cells.set(m2, i, c), zs):
  +q => +h => Equal.trans(C.Cir.Cell, C.Cir.Cells.get(C.Cir.Cells.set(m2, i, c), q), C.Cir.Cells.get(m2, q), C.Cir.Cells.get(m, q),
    PM.cl.go(m2, q, i, c, mem.ne(zs, q, i, h, hi)), k(q, h))

# the same set of both keeps the agreement
def agr.set.b(b: Bool, +m: C.Cir.Cells, +v: C.Cir.Cells, +zs: List<&2, U32>, +i: U32, +c: C.Cir.Cell, +q: U32,
  +eb: {U32.is_eq(q, i) == b : Bool}, a: Agr(m, v, zs), hq: {PM.Mem(zs, q) == False{} : Bool}) ->
  {C.Cir.Cells.get(C.Cir.Cells.set(m, i, c), q) == C.Cir.Cells.get(C.Cir.Cells.set(v, i, c), q) : C.Cir.Cell}:
  match b:
    case True{}:
      +e = PM.u32.eq(q, i, eb)
      %Equal.sym(U32, q, i, e) : {C.Cir.Cells.get(C.Cir.Cells.set(m, i, c), _) == C.Cir.Cells.get(C.Cir.Cells.set(v, i, c), _) : C.Cir.Cell}
      Equal.trans(C.Cir.Cell, C.Cir.Cells.get(C.Cir.Cells.set(m, i, c), i), c, C.Cir.Cells.get(C.Cir.Cells.set(v, i, c), i),
        PM.cl.gs(m, i, c), Equal.sym(C.Cir.Cell, C.Cir.Cells.get(C.Cir.Cells.set(v, i, c), i), c, PM.cl.gs(v, i, c)))
    case False{}:
      Equal.trans(C.Cir.Cell, C.Cir.Cells.get(C.Cir.Cells.set(m, i, c), q), C.Cir.Cells.get(m, q), C.Cir.Cells.get(C.Cir.Cells.set(v, i, c), q),
        PM.cl.go(m, q, i, c, eb),
        Equal.trans(C.Cir.Cell, C.Cir.Cells.get(m, q), C.Cir.Cells.get(v, q), C.Cir.Cells.get(C.Cir.Cells.set(v, i, c), q), a(q, hq),
          Equal.sym(C.Cir.Cell, C.Cir.Cells.get(C.Cir.Cells.set(v, i, c), q), C.Cir.Cells.get(v, q), PM.cl.go(v, q, i, c, eb))))

def agr.set(+m: C.Cir.Cells, +v: C.Cir.Cells, +zs: List<&2, U32>, +i: U32, +c: C.Cir.Cell, a: Agr(m, v, zs)) ->
  Agr(C.Cir.Cells.set(m, i, c), C.Cir.Cells.set(v, i, c), zs):
  +q => +hq => agr.set.b(U32.is_eq(q, i), m, v, zs, i, c, q, {==}, a, hq)

# a store of a field of a cell out of zs, in both
def agr.put.b(b: Bool, +m: C.Cir.Cells, +v: C.Cir.Cells, +zs: List<&2, U32>, +k: Nat, +i: U32, +x: U32, +q: U32,
  +eb: {U32.is_eq(q, i) == b : Bool}, a: Agr(m, v, zs), +hi: {PM.Mem(zs, i) == False{} : Bool},
  +hq: {PM.Mem(zs, q) == False{} : Bool}) ->
  {C.Cir.Cells.get(X.X.put(m, k, i, x), q) == C.Cir.Cells.get(X.X.put(v, k, i, x), q) : C.Cir.Cell}:
  match b:
    case True{}:
      +e = PM.u32.eq(q, i, eb)
      +ci = a(i, hi)
      %Equal.sym(U32, q, i, e) : {C.Cir.Cells.get(X.X.put(m, k, i, x), _) == C.Cir.Cells.get(X.X.put(v, k, i, x), _) : C.Cir.Cell}
      %ci : {C.Cir.Cells.get(X.X.put(m, k, i, x), i) == C.Cir.Cells.get(C.Cir.Cells.set(v, i, C.Cir.Cell.set(k, _, x)), i) : C.Cir.Cell}
      Equal.trans(C.Cir.Cell, C.Cir.Cells.get(X.X.put(m, k, i, x), i), C.Cir.Cell.set(k, C.Cir.Cells.get(m, i), x),
        C.Cir.Cells.get(C.Cir.Cells.set(v, i, C.Cir.Cell.set(k, C.Cir.Cells.get(m, i), x)), i),
        PM.cl.gs(m, i, C.Cir.Cell.set(k, C.Cir.Cells.get(m, i), x)),
        Equal.sym(C.Cir.Cell, C.Cir.Cells.get(C.Cir.Cells.set(v, i, C.Cir.Cell.set(k, C.Cir.Cells.get(m, i), x)), i),
          C.Cir.Cell.set(k, C.Cir.Cells.get(m, i), x), PM.cl.gs(v, i, C.Cir.Cell.set(k, C.Cir.Cells.get(m, i), x))))
    case False{}:
      Equal.trans(C.Cir.Cell, C.Cir.Cells.get(X.X.put(m, k, i, x), q), C.Cir.Cells.get(m, q), C.Cir.Cells.get(X.X.put(v, k, i, x), q),
        PM.cl.go(m, q, i, C.Cir.Cell.set(k, C.Cir.Cells.get(m, i), x), eb),
        Equal.trans(C.Cir.Cell, C.Cir.Cells.get(m, q), C.Cir.Cells.get(v, q), C.Cir.Cells.get(X.X.put(v, k, i, x), q), a(q, hq),
          Equal.sym(C.Cir.Cell, C.Cir.Cells.get(X.X.put(v, k, i, x), q), C.Cir.Cells.get(v, q),
            PM.cl.go(v, q, i, C.Cir.Cell.set(k, C.Cir.Cells.get(v, i), x), eb))))

def agr.put(+m: C.Cir.Cells, +v: C.Cir.Cells, +zs: List<&2, U32>, +k: Nat, +i: U32, +x: U32, a: Agr(m, v, zs),
  +hi: {PM.Mem(zs, i) == False{} : Bool}) -> Agr(X.X.put(m, k, i, x), X.X.put(v, k, i, x), zs):
  +q => +hq => agr.put.b(U32.is_eq(q, i), m, v, zs, k, i, x, q, {==}, a, hi, hq)

def kp.put(+m: C.Cir.Cells, +m2: C.Cir.Cells, +zs: List<&2, U32>, +k: Nat, +i: U32, +x: U32, kk: Kp(m, m2, zs),
  hi: {PM.Mem(zs, i) == False{} : Bool}) -> Kp(m, X.X.put(m2, k, i, x), zs):
  kp.set(m, m2, zs, i, C.Cir.Cell.set(k, C.Cir.Cells.get(m2, i), x), kk, hi)

# Field 1
# -------

# the cells m2 differ from m in field 1 only
def F1(+m: C.Cir.Cells, +m2: C.Cir.Cells) -> Type:
  @q: U32 -> {C.Cir.Cells.get(m2, q) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, q), PM.Fd(1n, m2, q)) : C.Cir.Cell}

def c1.get(+y: C.Cir.Cell, +w: U32) -> {C.Cir.Cell.get(1n, C.Cir.Cell.set(1n, y, w)) == w : U32}:
  match y:
    case C.Cir.Cell{a, b, x2, x3, x4}:
      {==}

def c1.set2(+y: C.Cir.Cell, +a: U32, +b: U32) -> {C.Cir.Cell.set(1n, C.Cir.Cell.set(1n, y, a), b) == C.Cir.Cell.set(1n, y, b) : C.Cir.Cell}:
  match y:
    case C.Cir.Cell{c0, c1, x2, x3, x4}:
      {==}

# a field other than 1 of a cell set in field 1
def c1.other(+k: Nat, +y: C.Cir.Cell, +w: U32, hk: {Nat.is_eq(k, 1n) == False{} : Bool}) ->
  {C.Cir.Cell.get(k, C.Cir.Cell.set(1n, y, w)) == C.Cir.Cell.get(k, y) : U32}:
  match k y:
    case 0n C.Cir.Cell{c0, c1, x2, x3, x4}:
      {==}
    case 1n C.Cir.Cell{c0, c1, x2, x3, x4}:
      X.k.ft({C.Cir.Cell.get(1n, C.Cir.Cell.set(1n, C.Cir.Cell{c0, c1, x2, x3, x4}, w)) == C.Cir.Cell.get(1n, C.Cir.Cell{c0, c1, x2, x3, x4}) : U32}, hk)
    case 2n C.Cir.Cell{c0, c1, x2, x3, x4}:
      {==}
    case 3n C.Cir.Cell{c0, c1, x2, x3, x4}:
      {==}
    case 4n+p C.Cir.Cell{c0, c1, x2, x3, x4}:
      {==}

def f1.refl(+m: C.Cir.Cells) -> F1(m, m):
  +q => PM.set1.id(C.Cir.Cells.get(m, q))

def f1.put.b(b: Bool, +m: C.Cir.Cells, +i: U32, +x: U32, +q: U32, +eb: {U32.is_eq(q, i) == b : Bool}) ->
  {C.Cir.Cells.get(X.X.put(m, 1n, i, x), q) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, q), PM.Fd(1n, X.X.put(m, 1n, i, x), q)) : C.Cir.Cell}:
  match b:
    case True{}:
      +e = PM.u32.eq(q, i, eb)
      +y = C.Cir.Cell.set(1n, C.Cir.Cells.get(m, i), x)
      %Equal.sym(U32, q, i, e) : {C.Cir.Cells.get(X.X.put(m, 1n, i, x), _) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, _), PM.Fd(1n, X.X.put(m, 1n, i, x), _)) : C.Cir.Cell}
      %Equal.sym(C.Cir.Cell, C.Cir.Cells.get(X.X.put(m, 1n, i, x), i), y, PM.cl.gs(m, i, y)) :
        {_ == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, i), C.Cir.Cell.get(1n, _)) : C.Cir.Cell}
      %Equal.sym(U32, C.Cir.Cell.get(1n, y), x, c1.get(C.Cir.Cells.get(m, i), x)) : {y == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, i), _) : C.Cir.Cell}
      {==}
    case False{}:
      %Equal.sym(C.Cir.Cell, C.Cir.Cells.get(X.X.put(m, 1n, i, x), q), C.Cir.Cells.get(m, q),
        PM.cl.go(m, q, i, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, i), x), eb)) :
        {_ == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, q), C.Cir.Cell.get(1n, _)) : C.Cir.Cell}
      PM.set1.id(C.Cir.Cells.get(m, q))

def f1.put(+m: C.Cir.Cells, +i: U32, +x: U32) -> F1(m, X.X.put(m, 1n, i, x)):
  +q => f1.put.b(U32.is_eq(q, i), m, i, x, q, {==})

def f1.trans(+m: C.Cir.Cells, +m2: C.Cir.Cells, +m3: C.Cir.Cells, a: F1(m, m2), b: F1(m2, m3)) -> F1(m, m3):
  +q =>
    +w2 = PM.Fd(1n, m2, q)
    +w3 = PM.Fd(1n, m3, q)
    Equal.trans(C.Cir.Cell, C.Cir.Cells.get(m3, q), C.Cir.Cell.set(1n, C.Cir.Cells.get(m2, q), w3),
      C.Cir.Cell.set(1n, C.Cir.Cells.get(m, q), w3), b(q),
      Equal.trans(C.Cir.Cell, C.Cir.Cell.set(1n, C.Cir.Cells.get(m2, q), w3),
        C.Cir.Cell.set(1n, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, q), w2), w3), C.Cir.Cell.set(1n, C.Cir.Cells.get(m, q), w3),
        Equal.cong(C.Cir.Cell, C.Cir.Cell, y => C.Cir.Cell.set(1n, y, w3), C.Cir.Cells.get(m2, q), C.Cir.Cell.set(1n, C.Cir.Cells.get(m, q), w2), a(q)),
        c1.set2(C.Cir.Cells.get(m, q), w2, w3)))

# Two runs
# --------

# after a run from the registers regs on m and on v: the registers regs2,
# cells m2 and v2 that agree but at zs and keep zs; m2 differs from m in
# field 1 only; 64 registers, of which aq and am stay
def Rel2(+regs: List<&2, U32>, +regs2: List<&2, U32>, +m: C.Cir.Cells, +v: C.Cir.Cells, +m2: C.Cir.Cells, +v2: C.Cir.Cells,
  +zs: List<&2, U32>) -> Type:
  Agr(m2, v2, zs) & (Kp(m, m2, zs) & (Kp(v, v2, zs) & (F1(m, m2) & ({List.length(&2, U32, regs2) == 64n : Nat} &
    ({List.get(&2, U32, regs2, 6n) == List.get(&2, U32, regs, 6n) : Maybe<&2, U32>} &
     {List.get(&2, U32, regs2, 7n) == List.get(&2, U32, regs, 7n) : Maybe<&2, U32>})))))

# s runs on m and on v to such states
def Two(+f: Nat, +s: C.Cir.Stmt, +regs: List<&2, U32>, +m: C.Cir.Cells, +v: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, U32>, +zs: List<&2, U32>) -> Type:
  Sigma<&1, &1, List<&2, U32>, regs2 => Sigma<&1, &1, C.Cir.Cells, m2 => Sigma<&1, &1, C.Cir.Cells, v2 =>
    {C.Cir.exec(f, s, X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == C.Cir.Out.next{X.X.st(regs2, m2, nx, fi, im, pg, lim, inp)} : C.Cir.Out} &
    ({C.Cir.exec(f, s, X.X.st(regs, v, nx, fi, im, pg, lim, inp)) == C.Cir.Out.next{X.X.st(regs2, v2, nx, fi, im, pg, lim, inp)} : C.Cir.Out} &
    Rel2(regs, regs2, m, v, m2, v2, zs))>>>

# a run that changes nothing
def two.id(+f: Nat, +s: C.Cir.Stmt, +regs: List<&2, U32>, +m: C.Cir.Cells, +v: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, U32>, +zs: List<&2, U32>, a: Agr(m, v, zs), +hl: {List.length(&2, U32, regs) == 64n : Nat},
  em: {C.Cir.exec(f, s, X.X.st(regs, m, nx, fi, im, pg, lim, inp)) == C.Cir.Out.next{X.X.st(regs, m, nx, fi, im, pg, lim, inp)} : C.Cir.Out},
  ev: {C.Cir.exec(f, s, X.X.st(regs, v, nx, fi, im, pg, lim, inp)) == C.Cir.Out.next{X.X.st(regs, v, nx, fi, im, pg, lim, inp)} : C.Cir.Out}) ->
  Two(f, s, regs, m, v, nx, fi, im, pg, lim, inp, zs):
  (regs, (m, (v, (em, (ev, (a, (kp.refl(m, zs), (kp.refl(v, zs), (f1.refl(m), (hl, ({==}, {==})))))))))))

# a set of r keeps the register j
def L.keep(xs: List<&2, U32>, r: Nat, j: Nat, +v: U32, ne: {Nat.is_eq(r, j) == False{} : Bool}) ->
  {List.get(&2, U32, List.set(&2, U32, xs, r, v), j) == List.get(&2, U32, xs, j) : Maybe<&2, U32>}:
  match xs r j:
    case Nil{} _ _:
      {==}
    case Con{x, t} 0n 0n:
      X.k.ft({List.get(&2, U32, List.set(&2, U32, Con{x, t}, 0n, v), 0n) == List.get(&2, U32, Con{x, t}, 0n) : Maybe<&2, U32>}, ne)
    case Con{x, t} 0n 1n+q:
      {==}
    case Con{x, t} 1n+p 0n:
      {==}
    case Con{x, t} 1n+p 1n+q:
      L.keep(t, p, q, v, ne)

# a property of a cell, carried along an equation
def tr.cell(-P: C.Cir.Cell -> Type, -y1: C.Cir.Cell, -y2: C.Cir.Cell, e: {y1 == y2 : C.Cir.Cell}, h: P(y1)) -> P(y2):
  %e : P(_)
  h

def tr.u32(-P: U32 -> Type, -a: U32, -b: U32, e: {a == b : U32}, h: P(a)) -> P(b):
  %e : P(_)
  h

# M.dec(dx)
# ---------

def sim.dec.d(b: Bool, +f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +v: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, U32>, +zs: List<&2, U32>, +x: U32, +pend: U32,
  +hl: {List.length(&2, U32, regs) == 64n : Nat}, +h4: {List.get(&2, U32, regs, 4n) == Some{x} : Maybe<&2, U32>},
  +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}, a: Agr(m, v, zs),
  +hz: {U32.is_eq(x, 0) == False{} : Bool}, +hc: {C.Cir.is_cell(x, im, fi, nx) == True{} : Bool},
  +hm: {PM.Mem(zs, x) == False{} : Bool}, +ex: {C.Cir.Cells.get(m, x) == C.Cir.Cells.get(v, x) : C.Cir.Cell},
  +hs: {U32.is_ne(U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x)), 1024), 0) == False{} : Bool},
  +eb: {U32.is_eq(U32.sub(C.Cir.Cell.get(1n, C.Cir.Cells.get(m, x)), 1), 0) == b : Bool}) ->
  Two(f, C.M.dec(C.R.dx()), regs, m, v, nx, fi, im, pg, lim, inp, zs):
  match b:
    case False{}:
      +d = U32.sub(C.Cir.Cell.get(1n, C.Cir.Cells.get(m, x)), 1)
      +hsv = tr.cell(y => {U32.is_ne(U32.and(C.Cir.Cell.get(0n, y), 1024), 0) == False{} : Bool}, C.Cir.Cells.get(m, x), C.Cir.Cells.get(v, x), ex, hs)
      +em = X.dec.eq.n(f, regs, m, nx, fi, im, pg, lim, inp, 4n, x, hl, h4, hz, hc, hs, eb, {==})
      +ev0 = X.dec.eq.n(f, regs, v, nx, fi, im, pg, lim, inp, 4n, x, hl, h4, hz, hc, hsv,
        tr.cell(y => {U32.is_eq(U32.sub(C.Cir.Cell.get(1n, y), 1), 0) == False{} : Bool}, C.Cir.Cells.get(m, x), C.Cir.Cells.get(v, x), ex, eb), {==})
      +ev = tr.cell(y => {C.Cir.exec(f, C.M.dec(4n), X.X.st(regs, v, nx, fi, im, pg, lim, inp)) ==
          C.Cir.Out.next{X.X.st(X.X.set(regs, 5n, U32.sub(C.Cir.Cell.get(1n, y), 1)), X.X.put(v, 1n, x, U32.sub(C.Cir.Cell.get(1n, y), 1)), nx, fi, im, pg, lim, inp)} : C.Cir.Out},
        C.Cir.Cells.get(v, x), C.Cir.Cells.get(m, x), Equal.sym(C.Cir.Cell, C.Cir.Cells.get(m, x), C.Cir.Cells.get(v, x), ex), ev0)
      (X.X.set(regs, 5n, d), (X.X.put(m, 1n, x, d), (X.X.put(v, 1n, x, d), (em, (ev,
        (agr.put(m, v, zs, 1n, x, d, a, hm), (kp.put(m, m, zs, 1n, x, d, kp.refl(m, zs), hm), (kp.put(v, v, zs, 1n, x, d, kp.refl(v, zs), hm),
        (f1.put(m, x, d), (X.L.len(regs, 5n, d, 64n, hl), (L.keep(regs, 5n, 6n, d, {==}), L.keep(regs, 5n, 7n, d, {==}))))))))))))
    case True{}:
      +d = U32.sub(C.Cir.Cell.get(1n, C.Cir.Cells.get(m, x)), 1)
      +hsv = tr.cell(y => {U32.is_ne(U32.and(C.Cir.Cell.get(0n, y), 1024), 0) == False{} : Bool}, C.Cir.Cells.get(m, x), C.Cir.Cells.get(v, x), ex, hs)
      +em = X.dec.eq.p(f, regs, m, nx, fi, im, pg, lim, inp, 4n, x, pend, hl, h4, h3, hz, hc, hs, eb, {==})
      +ev0 = X.dec.eq.p(f, regs, v, nx, fi, im, pg, lim, inp, 4n, x, pend, hl, h4, h3, hz, hc, hsv,
        tr.cell(y => {U32.is_eq(U32.sub(C.Cir.Cell.get(1n, y), 1), 0) == True{} : Bool}, C.Cir.Cells.get(m, x), C.Cir.Cells.get(v, x), ex, eb), {==})
      +ev = tr.cell(y => {C.Cir.exec(f, C.M.dec(4n), X.X.st(regs, v, nx, fi, im, pg, lim, inp)) ==
          C.Cir.Out.next{X.X.st(X.X.set(X.X.set(regs, 5n, U32.sub(C.Cir.Cell.get(1n, y), 1)), 3n, x),
            X.X.put(X.X.put(v, 1n, x, U32.sub(C.Cir.Cell.get(1n, y), 1)), 1n, x, pend), nx, fi, im, pg, lim, inp)} : C.Cir.Out},
        C.Cir.Cells.get(v, x), C.Cir.Cells.get(m, x), Equal.sym(C.Cir.Cell, C.Cir.Cells.get(m, x), C.Cir.Cells.get(v, x), ex), ev0)
      +r1 = X.X.set(regs, 5n, d)
      +m1 = X.X.put(m, 1n, x, d)
      +v1 = X.X.put(v, 1n, x, d)
      k1 = kp.put(m, m, zs, 1n, x, d, kp.refl(m, zs), hm)
      j1 = kp.put(v, v, zs, 1n, x, d, kp.refl(v, zs), hm)
      (X.X.set(r1, 3n, x), (X.X.put(m1, 1n, x, pend), (X.X.put(v1, 1n, x, pend), (em, (ev,
        (agr.put(m1, v1, zs, 1n, x, pend, agr.put(m, v, zs, 1n, x, d, a, hm), hm),
        (kp.trans(m, m, X.X.put(m1, 1n, x, pend), zs, kp.refl(m, zs), kp.put(m, m1, zs, 1n, x, pend, k1, hm)),
        (kp.trans(v, v, X.X.put(v1, 1n, x, pend), zs, kp.refl(v, zs), kp.put(v, v1, zs, 1n, x, pend, j1, hm)),
        (f1.trans(m, m1, X.X.put(m1, 1n, x, pend), f1.put(m, x, d), f1.put(m1, x, pend)),
        (X.L.len(r1, 3n, x, 64n, X.L.len(regs, 5n, d, 64n, hl)),
        (Equal.trans(Maybe<&2, U32>, List.get(&2, U32, X.X.set(r1, 3n, x), 6n), List.get(&2, U32, r1, 6n), List.get(&2, U32, regs, 6n),
           L.keep(r1, 3n, 6n, x, {==}), L.keep(regs, 5n, 6n, d, {==})),
         Equal.trans(Maybe<&2, U32>, List.get(&2, U32, X.X.set(r1, 3n, x), 7n), List.get(&2, U32, r1, 7n), List.get(&2, U32, regs, 7n),
           L.keep(r1, 3n, 7n, x, {==}), L.keep(regs, 5n, 7n, d, {==})))))))))))))

def sim.dec.s(b: Bool, +f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +v: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, U32>, +zs: List<&2, U32>, +x: U32, +pend: U32,
  +hl: {List.length(&2, U32, regs) == 64n : Nat}, +h4: {List.get(&2, U32, regs, 4n) == Some{x} : Maybe<&2, U32>},
  +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}, a: Agr(m, v, zs),
  +hz: {U32.is_eq(x, 0) == False{} : Bool}, +hc: {C.Cir.is_cell(x, im, fi, nx) == True{} : Bool},
  +hm: {PM.Mem(zs, x) == False{} : Bool}, +ex: {C.Cir.Cells.get(m, x) == C.Cir.Cells.get(v, x) : C.Cir.Cell},
  +eb: {U32.is_ne(U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x)), 1024), 0) == b : Bool}) ->
  Two(f, C.M.dec(C.R.dx()), regs, m, v, nx, fi, im, pg, lim, inp, zs):
  match b:
    case True{}:
      two.id(f, C.M.dec(C.R.dx()), regs, m, v, nx, fi, im, pg, lim, inp, zs, a, hl,
        X.dec.eq.s(f, regs, m, nx, fi, im, pg, lim, inp, 4n, x, h4, hz, hc, eb),
        X.dec.eq.s(f, regs, v, nx, fi, im, pg, lim, inp, 4n, x, h4, hz, hc,
          tr.cell(y => {U32.is_ne(U32.and(C.Cir.Cell.get(0n, y), 1024), 0) == True{} : Bool}, C.Cir.Cells.get(m, x), C.Cir.Cells.get(v, x), ex, eb)))
    case False{}:
      sim.dec.d(U32.is_eq(U32.sub(C.Cir.Cell.get(1n, C.Cir.Cells.get(m, x)), 1), 0), f, regs, m, v, nx, fi, im, pg, lim, inp, zs, x, pend,
        hl, h4, h3, a, hz, hc, hm, ex, eb, {==})

# M.dec(dx) of the cell x in dx: 0, or a cell out of zs
def sim.dec.z(b: Bool, +f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +v: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, U32>, +zs: List<&2, U32>, +x: U32, +pend: U32,
  +hl: {List.length(&2, U32, regs) == 64n : Nat}, +h4: {List.get(&2, U32, regs, 4n) == Some{x} : Maybe<&2, U32>},
  +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}, a: Agr(m, v, zs),
  +hx: {Bool.or(U32.is_eq(x, 0), Bool.and(Bool.not(PM.Mem(zs, x)), C.Cir.is_cell(x, im, fi, nx))) == True{} : Bool},
  +eb: {U32.is_eq(x, 0) == b : Bool}) ->
  Two(f, C.M.dec(C.R.dx()), regs, m, v, nx, fi, im, pg, lim, inp, zs):
  match b:
    case True{}:
      +e = PM.u32.eq(x, 0, eb)
      +h40 = tr.u32(y => {List.get(&2, U32, regs, 4n) == Some{y} : Maybe<&2, U32>}, x, 0, e, h4)
      two.id(f, C.M.dec(C.R.dx()), regs, m, v, nx, fi, im, pg, lim, inp, zs, a, hl,
        X.dec.eq.z(f, regs, m, nx, fi, im, pg, lim, inp, 4n, h40), X.dec.eq.z(f, regs, v, nx, fi, im, pg, lim, inp, 4n, h40))
    case False{}:
      +hy = PM.or.f.l(U32.is_eq(x, 0), Bool.and(Bool.not(PM.Mem(zs, x)), C.Cir.is_cell(x, im, fi, nx)), eb)
      ?TODO
