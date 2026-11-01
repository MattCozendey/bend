# compiler: the state relation of the simulation
# ===============================================
#
# The model's run, inside run's body, holds a Cir state st when its locals
# are Loc(a, n, s, next, outn, t, need, addr, regs), with register r at local
# 8 + r, and its memory is {pages, limit, bytes}, with Inv: the book's cells
# (RC from cell 1) and the machine's own (RC from first to next) read from
# the bytes as Cir.Cells.get gives them, the input's bytes from a and the
# output's from 20 × next (RB), and the bounds of the numbers (Bounds). The
# queries give what the code of an expression reads.

import Base
import ./impl.bend as C
import ./proof_need.bend as N
import ./proof_instrs.bend as I
import ./proof_halt.bend as PH
import ./proof_module.bend as M
import ./proof_valid.bend as V
import ./proof_sim_step.bend as S
import ./proof_sim_mem.bend as Y
import ./proof_sim_nat.bend as Z

# Kit
# ---

# a U32 with a property, as Data
def EXU(-B: U32 -> Data) -> Data:
  Sigma<&2, &2, U32, x => B(x)>

def some.inj(-x: U32, -y: U32, e: {Some{x} == Some{y} : Maybe<&2, U32>}) -> {x == y : U32}:
  Equal.cong(Maybe<&2, U32>, U32, z => Maybe.default(&2, U32, z, 0), Some{x}, Some{y}, e)

def is.some(x: Maybe<&2, U32>) -> Data:
  match x:
    case None{}:
      Empty
    case Some{_}:
      Unit

def none.some(-y: U32, e: {None{} == Some{y} : Maybe<&2, U32>}) -> Empty:
  %Equal.sym(Maybe<&2, U32>, None{}, Some{y}, e) : is.some(_)
  Unit{}

# The configurations
# ------------------

# run's locals: its two parameters, then status, next, outn, tmp, need and
# addr, then the registers
def Loc(+a: U32, +n: U32, +s: U32, +nx: U32, +on: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>) -> List<&2, U32>:
  Con{a, Con{n, Con{s, Con{nx, Con{on, Con{t, Con{nd, Con{ad, rg}}}}}}}}

# a running frame of run, with one result
def Cfg(+code: List<&2, C.Wasm.Instr>, +ls: List<&2, C.Wasm.Label>, +stk: List<&2, U32>, +loc: List<&2, U32>,
  +mem: C.Wasm.Memory) -> C.Wasm.Step:
  C.Wasm.Step.next{C.Wasm.Frame{code, ls, 1n, stk, loc}, mem}

def St(+rg: List<&2, U32>, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32) -> C.Cir.State:
  C.Cir.State{rg, cl, nx, fi, im, pg, lm, inp, ou, on}

# The views of the memory
# -----------------------

# the first byte of field j of the cell c
def at.f(+c: U32, +j: Nat) -> U32:
  U32.add(C.Cir.at(c), U32.shln(U32.from_nat(j), 2n))

# the cell c, as the bytes hold it
def RCell(+m: C.Wasm.Bytes, +c: U32) -> C.Cir.Cell:
  C.Cir.Cell{Y.V32(m, at.f(c, 0n)), Y.V32(m, at.f(c, 1n)), Y.V32(m, at.f(c, 2n)), Y.V32(m, at.f(c, 3n)), Y.V32(m, at.f(c, 4n))}

# q cells from c, as the bytes hold them
def RC(q: Nat, +m: C.Wasm.Bytes, +c: U32) -> List<&2, C.Cir.Cell>:
  match q:
    case 0n:
      Nil{}
    case 1n+p:
      Con{RCell(m, c), RC(p, m, U32.inc(c))}

# q cells from c, as Cir has them
def GC(q: Nat, +cl: C.Cir.Cells, +c: U32) -> List<&2, C.Cir.Cell>:
  match q:
    case 0n:
      Nil{}
    case 1n+p:
      Con{C.Cir.Cells.get(cl, c), GC(p, cl, U32.inc(c))}

# q bytes from x
def RB(q: Nat, +m: C.Wasm.Bytes, +x: U32) -> List<&2, U32>:
  match q:
    case 0n:
      Nil{}
    case 1n+p:
      Con{Y.R8(m, x), RB(p, m, U32.inc(x))}

# The relation
# ------------

# 2^16 × the pages: the memory's bytes
def PB(+pg: U32) -> Nat:
  N.D(16n, U32.to_nat(pg))

# what the state of a run of run holds, beside its locals: the input's
# address a and length n, the cells, the input's bytes and the output's
def Inv(+P: Nat, +G: Nat, +a: U32, +n: U32, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32, +m: C.Wasm.Bytes) -> Data:
  +NX = U32.to_nat(nx)
  +FI = U32.to_nat(fi)
  +K = U32.to_nat(im)
  +L = List.length(&2, U32, inp)
  S.P2(S.P2(S.P2({a == C.Cir.input.at(im) : U32}, {n == C.Wasm.encode.len(U32, inp) : U32}),
            S.P2({RC(K, m, 1) == GC(K, cl, 1) : List<&2, C.Cir.Cell>}, {RB(L, m, a) == inp : List<&2, U32>})),
       S.P2(S.P2(N.Le(FI, NX), {RC(Nat.sub(NX, FI), m, fi) == GC(Nat.sub(NX, FI), cl, fi) : List<&2, C.Cir.Cell>}),
            S.P2({RB(U32.to_nat(on), m, C.Cir.at(nx)) == List.reverse(&2, U32, ou) : List<&2, U32>},
              Bounds(P, G, a, nx, fi, im, pg, lm, inp, on))))

# no cell, or the cells up to next fit in B bytes
def CF(q: Nat, +NX: Nat, +B: Nat) -> Data:
  match q:
    case 0n:
      Unit
    case 1n+_:
      N.Le(PH.H.t20(NX), B)

# no output, or the output after 20 × next fits in B bytes
def OF(o: Nat, +NX: Nat, +B: Nat) -> Data:
  match o:
    case 0n:
      Unit
    case 1n+p:
      N.Le(Nat.add(PH.H.t20(NX), 1n+p), B)

# the numbers' bounds, with P = (2^32 - 16) / 20 and G = 2^16, kept as
# variables: the book's cells, the input's end below 2^32 - 16, in the
# memory, and before the first cell of the machine; next at most P; the
# cells and the output in the memory; the limit below G pages, and the pages
# at most the limit
def Bounds(+P: Nat, +G: Nat, +a: U32, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32, +inp: List<&2, U32>, +on: U32) -> Data:
  +A = U32.to_nat(a)
  +NX = U32.to_nat(nx)
  +FI = U32.to_nat(fi)
  +K = U32.to_nat(im)
  +E = Nat.add(A, List.length(&2, U32, inp))
  S.P2(S.P2(S.P2({A == PH.H.t20(1n+K) : Nat}, N.Le(1n+K, P)), S.P2(N.Le(E, PH.H.t20(P)), N.Le(E, PB(pg)))),
       S.P2(S.P2(N.Le(E, PH.H.t20(FI)), N.Le(NX, P)),
            S.P2(S.P2(CF(Nat.sub(NX, FI), NX, PB(pg)), OF(U32.to_nat(on), NX, PB(pg))),
                 S.P2(N.Le(1n+U32.to_nat(lm), G), N.Le(U32.to_nat(pg), U32.to_nat(lm))))))

# The parts of the relation
# -------------------------

def inv.ea(-P: Nat, -G: Nat, -a: U32, -n: U32, -cl: C.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -pg: U32, -lm: U32,
  -inp: List<&2, U32>, -ou: List<&2, U32>, -on: U32, -m: C.Wasm.Bytes, +hI: Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m)) ->
  {a == C.Cir.input.at(im) : U32}:
  (h0, h1) = hI
  (h00, h01) = h0
  (ea, en) = h00
  ea

def inv.book(-P: Nat, -G: Nat, -a: U32, -n: U32, -cl: C.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -pg: U32, -lm: U32,
  -inp: List<&2, U32>, -ou: List<&2, U32>, -on: U32, -m: C.Wasm.Bytes, +hI: Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m)) ->
  {RC(U32.to_nat(im), m, 1) == GC(U32.to_nat(im), cl, 1) : List<&2, C.Cir.Cell>}:
  (h0, h1) = hI
  (h00, h01) = h0
  (hb, hi) = h01
  hb

def inv.inp(-P: Nat, -G: Nat, -a: U32, -n: U32, -cl: C.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -pg: U32, -lm: U32,
  -inp: List<&2, U32>, -ou: List<&2, U32>, -on: U32, -m: C.Wasm.Bytes, +hI: Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m)) ->
  {RB(List.length(&2, U32, inp), m, a) == inp : List<&2, U32>}:
  (h0, h1) = hI
  (h00, h01) = h0
  (hb, hi) = h01
  hi

def inv.fle(-P: Nat, -G: Nat, -a: U32, -n: U32, -cl: C.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -pg: U32, -lm: U32,
  -inp: List<&2, U32>, -ou: List<&2, U32>, -on: U32, -m: C.Wasm.Bytes, +hI: Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m)) ->
  N.Le(U32.to_nat(fi), U32.to_nat(nx)):
  (h0, h1) = hI
  (h10, h11) = h1
  (hf, hm) = h10
  hf

def inv.mach(-P: Nat, -G: Nat, -a: U32, -n: U32, -cl: C.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -pg: U32, -lm: U32,
  -inp: List<&2, U32>, -ou: List<&2, U32>, -on: U32, -m: C.Wasm.Bytes, +hI: Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m)) ->
  {RC(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) == GC(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), cl, fi) : List<&2, C.Cir.Cell>}:
  (h0, h1) = hI
  (h10, h11) = h1
  (hf, hm) = h10
  hm

def inv.out(-P: Nat, -G: Nat, -a: U32, -n: U32, -cl: C.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -pg: U32, -lm: U32,
  -inp: List<&2, U32>, -ou: List<&2, U32>, -on: U32, -m: C.Wasm.Bytes, +hI: Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m)) ->
  {RB(U32.to_nat(on), m, C.Cir.at(nx)) == List.reverse(&2, U32, ou) : List<&2, U32>}:
  (h0, h1) = hI
  (h10, h11) = h1
  (ho, hb) = h11
  ho

def inv.bounds(-P: Nat, -G: Nat, -a: U32, -n: U32, -cl: C.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -pg: U32, -lm: U32,
  -inp: List<&2, U32>, -ou: List<&2, U32>, -on: U32, -m: C.Wasm.Bytes, +hI: Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m)) ->
  Bounds(P, G, a, nx, fi, im, pg, lm, inp, on):
  (h0, h1) = hI
  (h10, h11) = h1
  (ho, hb) = h11
  hb

# The bounds, one by one

def b.a(-P: Nat, -G: Nat, -a: U32, -nx: U32, -fi: U32, -im: U32, -pg: U32, -lm: U32, -inp: List<&2, U32>, -on: U32,
  +hB: Bounds(P, G, a, nx, fi, im, pg, lm, inp, on)) -> {U32.to_nat(a) == PH.H.t20(1n+U32.to_nat(im)) : Nat}:
  (x0, x1) = hB
  (x00, x01) = x0
  (y0, y1) = x00
  y0

def b.k(-P: Nat, -G: Nat, -a: U32, -nx: U32, -fi: U32, -im: U32, -pg: U32, -lm: U32, -inp: List<&2, U32>, -on: U32,
  +hB: Bounds(P, G, a, nx, fi, im, pg, lm, inp, on)) -> N.Le(1n+U32.to_nat(im), P):
  (x0, x1) = hB
  (x00, x01) = x0
  (y0, y1) = x00
  y1

def b.e20(-P: Nat, -G: Nat, -a: U32, -nx: U32, -fi: U32, -im: U32, -pg: U32, -lm: U32, -inp: List<&2, U32>, -on: U32,
  +hB: Bounds(P, G, a, nx, fi, im, pg, lm, inp, on)) -> N.Le(Nat.add(U32.to_nat(a), List.length(&2, U32, inp)), PH.H.t20(P)):
  (x0, x1) = hB
  (x00, x01) = x0
  (y0, y1) = x01
  y0

def b.epb(-P: Nat, -G: Nat, -a: U32, -nx: U32, -fi: U32, -im: U32, -pg: U32, -lm: U32, -inp: List<&2, U32>, -on: U32,
  +hB: Bounds(P, G, a, nx, fi, im, pg, lm, inp, on)) -> N.Le(Nat.add(U32.to_nat(a), List.length(&2, U32, inp)), PB(pg)):
  (x0, x1) = hB
  (x00, x01) = x0
  (y0, y1) = x01
  y1

def b.efi(-P: Nat, -G: Nat, -a: U32, -nx: U32, -fi: U32, -im: U32, -pg: U32, -lm: U32, -inp: List<&2, U32>, -on: U32,
  +hB: Bounds(P, G, a, nx, fi, im, pg, lm, inp, on)) -> N.Le(Nat.add(U32.to_nat(a), List.length(&2, U32, inp)), PH.H.t20(U32.to_nat(fi))):
  (x0, x1) = hB
  (x10, x11) = x1
  (y0, y1) = x10
  y0

def b.nx(-P: Nat, -G: Nat, -a: U32, -nx: U32, -fi: U32, -im: U32, -pg: U32, -lm: U32, -inp: List<&2, U32>, -on: U32,
  +hB: Bounds(P, G, a, nx, fi, im, pg, lm, inp, on)) -> N.Le(U32.to_nat(nx), P):
  (x0, x1) = hB
  (x10, x11) = x1
  (y0, y1) = x10
  y1

def b.cf(-P: Nat, -G: Nat, -a: U32, -nx: U32, -fi: U32, -im: U32, -pg: U32, -lm: U32, -inp: List<&2, U32>, -on: U32,
  +hB: Bounds(P, G, a, nx, fi, im, pg, lm, inp, on)) -> CF(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), U32.to_nat(nx), PB(pg)):
  (x0, x1) = hB
  (x10, x11) = x1
  (y0, y1) = x11
  (z0, z1) = y0
  z0

def b.of(-P: Nat, -G: Nat, -a: U32, -nx: U32, -fi: U32, -im: U32, -pg: U32, -lm: U32, -inp: List<&2, U32>, -on: U32,
  +hB: Bounds(P, G, a, nx, fi, im, pg, lm, inp, on)) -> OF(U32.to_nat(on), U32.to_nat(nx), PB(pg)):
  (x0, x1) = hB
  (x10, x11) = x1
  (y0, y1) = x11
  (z0, z1) = y0
  z1

def b.lm(-P: Nat, -G: Nat, -a: U32, -nx: U32, -fi: U32, -im: U32, -pg: U32, -lm: U32, -inp: List<&2, U32>, -on: U32,
  +hB: Bounds(P, G, a, nx, fi, im, pg, lm, inp, on)) -> N.Le(1n+U32.to_nat(lm), G):
  (x0, x1) = hB
  (x10, x11) = x1
  (y0, y1) = x11
  (z0, z1) = y1
  z0

def b.pg(-P: Nat, -G: Nat, -a: U32, -nx: U32, -fi: U32, -im: U32, -pg: U32, -lm: U32, -inp: List<&2, U32>, -on: U32,
  +hB: Bounds(P, G, a, nx, fi, im, pg, lm, inp, on)) -> N.Le(U32.to_nat(pg), U32.to_nat(lm)):
  (x0, x1) = hB
  (x10, x11) = x1
  (y0, y1) = x11
  (z0, z1) = y1
  z1

# Elements of the views
# ---------------------

def hd.cell(l: List<&2, C.Cir.Cell>) -> C.Cir.Cell:
  match l:
    case Nil{}:
      C.Cir.Cell.zero()
    case Con{h, _}:
      h

def tl.cell(l: List<&2, C.Cir.Cell>) -> List<&2, C.Cir.Cell>:
  match l:
    case Nil{}:
      Nil{}
    case Con{_, t}:
      t

# the cell j of two equal views
def view.at(q: Nat, +m: C.Wasm.Bytes, +cl: C.Cir.Cells, +c: U32, j: Nat, h: N.Le(1n+j, q),
  e: {RC(q, m, c) == GC(q, cl, c) : List<&2, C.Cir.Cell>}) -> {RCell(m, Z.incn(j, c)) == C.Cir.Cells.get(cl, Z.incn(j, c)) : C.Cir.Cell}:
  match q j:
    case 0n _:
      Empty.absurd({RCell(m, Z.incn(j, c)) == C.Cir.Cells.get(cl, Z.incn(j, c)) : C.Cir.Cell}, h)
    case 1n+p 0n:
      Equal.cong(List<&2, C.Cir.Cell>, C.Cir.Cell, l => hd.cell(l), RC(1n+p, m, c), GC(1n+p, cl, c), e)
    case 1n+p 1n+i:
      view.at(p, m, cl, U32.inc(c), i, h,
        Equal.cong(List<&2, C.Cir.Cell>, List<&2, C.Cir.Cell>, l => tl.cell(l), RC(1n+p, m, c), GC(1n+p, cl, c), e))

# the byte j of a view
def RB.get(q: Nat, +m: C.Wasm.Bytes, +c: U32, j: Nat, h: N.Le(1n+j, q)) ->
  {List.get(&2, U32, RB(q, m, c), j) == Some{Y.R8(m, Z.incn(j, c))} : Maybe<&2, U32>}:
  match q j:
    case 0n _:
      Empty.absurd({List.get(&2, U32, RB(0n, m, c), j) == Some{Y.R8(m, Z.incn(j, c))} : Maybe<&2, U32>}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+i:
      RB.get(p, m, U32.inc(c), i, h)

# an element of a list is below its length
def get.lt(l: List<&2, U32>, j: Nat, -b: U32, e: {List.get(&2, U32, l, j) == Some{b} : Maybe<&2, U32>}) ->
  N.Le(1n+j, List.length(&2, U32, l)):
  match l j:
    case Nil{} _:
      Empty.absurd(N.Le(1n+j, 0n), none.some(b, e))
    case Con{h, +t} 0n:
      N.le_zero(List.length(&2, U32, t))
    case Con{h, t} 1n+i:
      get.lt(t, i, b, e)

# field k of a cell, as the bytes hold it
def rcell.get(+m: C.Wasm.Bytes, +i: U32, k: Nat, hk: {Nat.is_le(k, 4n) == True{} : Bool}) ->
  {C.Cir.Cell.get(k, RCell(m, i)) == Y.V32(m, U32.add(C.Cir.at(i), U32.shln(U32.from_nat(k), 2n))) : U32}:
  match k:
    case 0n:
      {==}
    case 1n+k1:
      match k1:
        case 0n:
          {==}
        case 1n+k2:
          match k2:
            case 0n:
              {==}
            case 1n+k3:
              match k3:
                case 0n:
                  {==}
                case 1n+k4:
                  match k4:
                    case 0n:
                      {==}
                    case 1n+k5:
                      Empty.absurd({C.Cir.Cell.get(5n+k5, RCell(m, i)) == Y.V32(m, U32.add(C.Cir.at(i), U32.shln(U32.from_nat(5n+k5), 2n))) : U32},
                        N.false_ne_true(hk))

# Numbers
# -------

def sub0(x: Nat) -> {Nat.sub(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def succ.sub(+x: Nat, h: N.Le(1n, x)) -> {1n+Nat.sub(x, 1n) == x : Nat}:
  match x:
    case 0n:
      Empty.absurd({1n+Nat.sub(0n, 1n) == 0n : Nat}, h)
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.sub(p, 0n), p, sub0(p))

# f <= i < x gives i - f < x - f
def sub.lt(+f: Nat, +i: Nat, +x: Nat, h1: N.Le(f, i), h2: N.Le(1n+i, x)) -> N.Le(1n+Nat.sub(i, f), Nat.sub(x, f)):
  match f:
    case 0n:
      N.le_rw_r(1n+Nat.sub(i, 0n), x, Nat.sub(x, 0n), Equal.sym(Nat, Nat.sub(x, 0n), x, sub0(x)),
        N.le_rw_l(1n+i, 1n+Nat.sub(i, 0n), x, Equal.cong(Nat, Nat, z => 1n+z, i, Nat.sub(i, 0n), Equal.sym(Nat, Nat.sub(i, 0n), i, sub0(i))), h2))
    case 1n+g:
      match i x:
        case 0n _:
          Empty.absurd(N.Le(1n+Nat.sub(0n, 1n+g), Nat.sub(x, 1n+g)), h1)
        case 1n+j 0n:
          Empty.absurd(N.Le(1n+Nat.sub(1n+j, 1n+g), Nat.sub(0n, 1n+g)), h2)
        case 1n+j 1n+y:
          sub.lt(g, j, y, h1, h2)

# The cells that the machine may use
# ----------------------------------

def qf.cell.if(b1: Bool, +P: Nat, +G: Nat, +a: U32, +n: U32, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32, +m: C.Wasm.Bytes, +hI: Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +i: U32, +e1: {Bool.and(Bool.not(U32.is_zero(i)), U32.is_le(i, im)) == b1 : Bool},
  +hc: {Bool.or(b1, Bool.and(U32.is_le(fi, i), U32.is_lt(i, nx))) == True{} : Bool}) ->
  {RCell(m, i) == C.Cir.Cells.get(cl, i) : C.Cir.Cell}:
  match b1:
    case True{}:
      +hnz = I.and.l(Bool.not(U32.is_zero(i)), U32.is_le(i, im), e1)
      +hle = I.and.r(Bool.not(U32.is_zero(i)), U32.is_le(i, im), e1)
      +I1 = Z.nz.of(i, Z.not.t(U32.is_zero(i), hnz))
      +K = U32.to_nat(im)
      +j = Nat.sub(U32.to_nat(i), 1n)
      +hj = N.le_rw_l(U32.to_nat(i), 1n+j, K, Equal.sym(Nat, 1n+j, U32.to_nat(i), succ.sub(U32.to_nat(i), I1)), Z.le.of(i, im, hle))
      +va = view.at(K, m, cl, 1, j, hj, inv.book(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI))
      +ei = Z.incn.one(i, I1)
      Equal.trans(C.Cir.Cell, RCell(m, i), RCell(m, Z.incn(j, 1)), C.Cir.Cells.get(cl, i),
        Equal.cong(U32, C.Cir.Cell, z => RCell(m, z), i, Z.incn(j, 1), Equal.sym(U32, Z.incn(j, 1), i, ei)),
        Equal.trans(C.Cir.Cell, RCell(m, Z.incn(j, 1)), C.Cir.Cells.get(cl, Z.incn(j, 1)), C.Cir.Cells.get(cl, i), va,
          Equal.cong(U32, C.Cir.Cell, z => C.Cir.Cells.get(cl, z), Z.incn(j, 1), i, ei)))
    case False{}:
      +hfi = Z.le.of(fi, i, I.and.l(U32.is_le(fi, i), U32.is_lt(i, nx), hc))
      +hnx = Z.lt.of(i, nx, I.and.r(U32.is_le(fi, i), U32.is_lt(i, nx), hc))
      +FI = U32.to_nat(fi)
      +j = Nat.sub(U32.to_nat(i), FI)
      +hj = sub.lt(FI, U32.to_nat(i), U32.to_nat(nx), hfi, hnx)
      +va = view.at(Nat.sub(U32.to_nat(nx), FI), m, cl, fi, j, hj, inv.mach(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI))
      +ei = Z.incn.sub(i, fi, hfi)
      Equal.trans(C.Cir.Cell, RCell(m, i), RCell(m, Z.incn(j, fi)), C.Cir.Cells.get(cl, i),
        Equal.cong(U32, C.Cir.Cell, z => RCell(m, z), i, Z.incn(j, fi), Equal.sym(U32, Z.incn(j, fi), i, ei)),
        Equal.trans(C.Cir.Cell, RCell(m, Z.incn(j, fi)), C.Cir.Cells.get(cl, Z.incn(j, fi)), C.Cir.Cells.get(cl, i), va,
          Equal.cong(U32, C.Cir.Cell, z => C.Cir.Cells.get(cl, z), Z.incn(j, fi), i, ei)))

# Queries
# -------

# a field of a cell that the machine may use is inside the memory
def q.field.in(+P: Nat, +G: Nat, +a: U32, +n: U32, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32, +m: C.Wasm.Bytes, +hI: Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +i: U32, +k: Nat, hc: {C.Cir.is_cell(i, im, fi, nx) == True{} : Bool}, hk: {Nat.is_le(k, 4n) == True{} : Bool}) ->
  {C.Wasm.inside(pg, C.Cir.at(i), U32.shln(U32.from_nat(k), 2n), 4) == True{} : Bool}:
  ?TODO

# a field of a cell that the machine may use holds what Cir says
def q.field.val(+P: Nat, +G: Nat, +a: U32, +n: U32, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32, +m: C.Wasm.Bytes, +hI: Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +i: U32, +k: Nat, hc: {C.Cir.is_cell(i, im, fi, nx) == True{} : Bool}, hk: {Nat.is_le(k, 4n) == True{} : Bool}) ->
  {Y.V32(m, U32.add(C.Cir.at(i), U32.shln(U32.from_nat(k), 2n))) == C.Cir.Cell.get(k, C.Cir.Cells.get(cl, i)) : U32}:
  Equal.trans(U32, Y.V32(m, U32.add(C.Cir.at(i), U32.shln(U32.from_nat(k), 2n))), C.Cir.Cell.get(k, RCell(m, i)),
    C.Cir.Cell.get(k, C.Cir.Cells.get(cl, i)),
    Equal.sym(U32, C.Cir.Cell.get(k, RCell(m, i)), Y.V32(m, U32.add(C.Cir.at(i), U32.shln(U32.from_nat(k), 2n))), rcell.get(m, i, k, hk)),
    Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(k, z), RCell(m, i), C.Cir.Cells.get(cl, i),
      qf.cell.if(Bool.and(Bool.not(U32.is_zero(i)), U32.is_le(i, im)), P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI, i, {==}, hc)))

# a byte of the input is inside the memory
def q.byte.in(+P: Nat, +G: Nat, +a: U32, +n: U32, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32, +m: C.Wasm.Bytes, +hI: Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +x: U32, +b: U32, +hb: {List.get(&2, U32, inp, U32.to_nat(x)) == Some{b} : Maybe<&2, U32>}) ->
  {C.Wasm.inside(pg, U32.add(x, a), 0, 1) == True{} : Bool}:
  ?TODO

# a byte of the input holds what Cir says
def q.byte.val(+P: Nat, +G: Nat, +a: U32, +n: U32, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32, +m: C.Wasm.Bytes, +hI: Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +x: U32, +b: U32, +hb: {List.get(&2, U32, inp, U32.to_nat(x)) == Some{b} : Maybe<&2, U32>}) ->
  {Y.R8(m, U32.add(U32.add(x, a), 0)) == b : U32}:
  +X = U32.to_nat(x)
  +L = List.length(&2, U32, inp)
  +hL = get.lt(inp, X, b, hb)
  +e1 = Equal.trans(Maybe<&2, U32>, Some{Y.R8(m, Z.incn(X, a))}, List.get(&2, U32, RB(L, m, a), X), Some{b},
    Equal.sym(Maybe<&2, U32>, List.get(&2, U32, RB(L, m, a), X), Some{Y.R8(m, Z.incn(X, a))}, RB.get(L, m, a, X, hL)),
    Equal.trans(Maybe<&2, U32>, List.get(&2, U32, RB(L, m, a), X), List.get(&2, U32, inp, X), Some{b},
      Equal.cong(List<&2, U32>, Maybe<&2, U32>, l => List.get(&2, U32, l, X), RB(L, m, a), inp,
        inv.inp(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)), hb))
  +ex = Equal.trans(U32, U32.add(U32.add(x, a), 0), U32.add(x, a), Z.incn(X, a), Y.U32.add_zero(U32.add(x, a)),
    Equal.trans(U32, U32.add(x, a), U32.add(U32.from_nat(X), a), Z.incn(X, a),
      Equal.cong(U32, U32, z => U32.add(z, a), x, U32.from_nat(X), Equal.sym(U32, U32.from_nat(X), x, Z.from.to(x))),
      Equal.sym(U32, Z.incn(X, a), U32.add(U32.from_nat(X), a), Z.incn.add(X, a))))
  Equal.trans(U32, Y.R8(m, U32.add(U32.add(x, a), 0)), Y.R8(m, Z.incn(X, a)), b,
    Equal.cong(U32, U32, z => Y.R8(m, z), U32.add(U32.add(x, a), 0), Z.incn(X, a), ex), some.inj(Y.R8(m, Z.incn(X, a)), b, e1))

# the input's length is n
def q.size(+P: Nat, +G: Nat, +a: U32, +n: U32, +cl: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, U32>, +ou: List<&2, U32>, +on: U32, +m: C.Wasm.Bytes, hI: Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m)) ->
  {n == C.Wasm.encode.len(U32, inp) : U32}:
  (h0, h1) = hI
  (h00, h01) = h0
  (ea, en) = h00
  en

