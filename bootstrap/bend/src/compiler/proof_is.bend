# compiler: the term that Is says a cell stands for, as T.tm.of reads it
# =====================================================================
#
# The bridge from proof_mach.bend's Is (a cell stands for a term, node by
# node) to proof_term.bend's T.tm.of (the term that a cell's fields give):
#
#   is.tm: when the cell c stands for t, T.tm.of reads t from c with the fuel
#     Term.size(t) (is.tm.at: with any fuel at least that);
#   is.rd: and every cell that T.tm.of reads from c is a cell that the
#     machine may access (Cir.is_cell, from Nd), as Rd says;
#   quan.img: T.tm.quan reads back the quantity that Img.quan writes.

import Base
import ./impl.bend as C
import ./proof_term.bend as T
import ./proof_need.bend as N
import ./proof_mach.bend as PM

# Kit
# ---

# T.tm.quan reads back the quantity that Img.quan writes
def quan.img(q: C.Quan) -> {T.tm.quan(C.Img.quan(q)) == q : C.Quan}:
  match q:
    case C.Quan.Q0{}:
      {==}
    case C.Quan.Q1{}:
      {==}
    case C.Quan.Q2{}:
      {==}

# the quantity of a cell, as T.tm.of reads it, is the one that Qs says
def quan.of(+x: C.Cir.Cell, +q: C.Quan, h: PM.Qs(x, q)) -> {T.tm.quan(PM.QnW(C.Cir.Cell.get(0n, x))) == q : C.Quan}:
  %Equal.sym(U32, PM.QnW(C.Cir.Cell.get(0n, x)), C.Img.quan(q), h) : {T.tm.quan(_) == q : C.Quan}
  quan.img(q)

# a term of no fuel is none: the fuel of a term is at least 1
def size.nz(t: C.Term, le: N.Le(C.Term.size(t), 0n)) -> Empty:
  match t:
    case C.Term.Var{_}:
      le
    case C.Term.Ref{_}:
      le
    case C.Term.Ann{_, _}:
      le
    case C.Term.Let{_, _, _}:
      le
    case C.Term.Typ{_}:
      le
    case C.Term.Min{_, _}:
      le
    case C.Term.All{_, _, _}:
      le
    case C.Term.Lam{_, _}:
      le
    case C.Term.App{_, _, _}:
      le
    case C.Term.Sig{_, _, _}:
      le
    case C.Term.Tup{_, _, _}:
      le
    case C.Term.Prj{_}:
      le
    case C.Term.Enu{_}:
      le
    case C.Term.Lab{_}:
      le
    case C.Term.Mat{_, _, _}:
      le
    case C.Term.Efq{}:
      le
    case C.Term.Eql{_, _, _}:
      le
    case C.Term.Rfl{}:
      le
    case C.Term.Rwt{_, _, _}:
      le

# the first part's fuel, and the second's, of a node of two parts
def le.l(+a: Nat, +b: Nat, +g: Nat, le: N.Le(Nat.add(a, b), g)) -> N.Le(a, g):
  N.le_trans(a, Nat.add(a, b), g, N.le_add_r(a, b), le)

def le.r(+a: Nat, +b: Nat, +g: Nat, le: N.Le(Nat.add(a, b), g)) -> N.Le(b, g):
  N.le_trans(b, Nat.add(a, b), g, N.le_add_l(a, b), le)

# the second part's fuel, and the third's, of a node of three parts
def le.m(+a: Nat, +b: Nat, +d: Nat, +g: Nat, le: N.Le(Nat.add(a, Nat.add(b, d)), g)) -> N.Le(b, g):
  le.l(b, d, g, le.r(a, Nat.add(b, d), g, le))

def le.e(+a: Nat, +b: Nat, +d: Nat, +g: Nat, le: N.Le(Nat.add(a, Nat.add(b, d)), g)) -> N.Le(d, g):
  le.r(b, d, g, le.r(a, Nat.add(b, d), g, le))

# what the node of a cell says: it is a cell, of its tag
def nd.cell(-ds: List<&2, C.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, -x: C.Cir.Cell, -t: C.Term, -tag: U32,
  h: PM.Nd(ds, im, fi, nx, c, x, t, tag)) -> {C.Cir.is_cell(c, im, fi, nx) == True{} : Bool}:
  (e, r) = h
  e

def nd.tag(-ds: List<&2, C.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, -x: C.Cir.Cell, -t: C.Term, -tag: U32,
  h: PM.Nd(ds, im, fi, nx, c, x, t, tag)) -> {PM.TgW(C.Cir.Cell.get(0n, x)) == tag : U32}:
  (e0, r0) = h
  (e1, r1) = r0
  (e, r) = r1
  e

def and.i(a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, N.false_ne_true(ha))

# The terms of the parts
# ----------------------

def one.of(-k: C.Term -> C.Term, -r: Maybe<&2, C.Term>, -a: C.Term, -t: C.Term,
  er: {r == Some{a} : Maybe<&2, C.Term>}, ek: {k(a) == t : C.Term}) -> {T.tm.one(k, r) == Some{t} : Maybe<&2, C.Term>}:
  %Equal.sym(Maybe<&2, C.Term>, r, Some{a}, er) : {T.tm.one(k, _) == Some{t} : Maybe<&2, C.Term>}
  %ek : {Some{k(a)} == Some{_} : Maybe<&2, C.Term>}
  {==}

def two.of(-k: C.Term -> C.Term -> C.Term, -r: Maybe<&2, C.Term>, -s: Maybe<&2, C.Term>, -a: C.Term, -b: C.Term, -t: C.Term,
  er: {r == Some{a} : Maybe<&2, C.Term>}, es: {s == Some{b} : Maybe<&2, C.Term>}, ek: {k(a, b) == t : C.Term}) ->
  {T.tm.two(k, r, s) == Some{t} : Maybe<&2, C.Term>}:
  %Equal.sym(Maybe<&2, C.Term>, r, Some{a}, er) : {T.tm.two(k, _, s) == Some{t} : Maybe<&2, C.Term>}
  %Equal.sym(Maybe<&2, C.Term>, s, Some{b}, es) : {T.tm.two(k, Some{a}, _) == Some{t} : Maybe<&2, C.Term>}
  %ek : {Some{k(a, b)} == Some{_} : Maybe<&2, C.Term>}
  {==}

def three.of(-k: C.Term -> C.Term -> C.Term -> C.Term, -r: Maybe<&2, C.Term>, -s: Maybe<&2, C.Term>, -u: Maybe<&2, C.Term>,
  -a: C.Term, -b: C.Term, -d: C.Term,
  er: {r == Some{a} : Maybe<&2, C.Term>}, es: {s == Some{b} : Maybe<&2, C.Term>}, eu: {u == Some{d} : Maybe<&2, C.Term>}) ->
  {T.tm.three(k, r, s, u) == Some{k(a, b, d)} : Maybe<&2, C.Term>}:
  %Equal.sym(Maybe<&2, C.Term>, r, Some{a}, er) : {T.tm.three(k, _, s, u) == Some{k(a, b, d)} : Maybe<&2, C.Term>}
  %Equal.sym(Maybe<&2, C.Term>, s, Some{b}, es) : {T.tm.three(k, Some{a}, _, u) == Some{k(a, b, d)} : Maybe<&2, C.Term>}
  %Equal.sym(Maybe<&2, C.Term>, u, Some{d}, eu) : {T.tm.three(k, Some{a}, Some{b}, _) == Some{k(a, b, d)} : Maybe<&2, C.Term>}
  {==}

def named.of(-n: Maybe<&2, List<&2, U32>>, -k: List<&2, U32>, en: {n == Some{k} : Maybe<&2, List<&2, U32>>}) ->
  {T.tm.named(n, j => C.Term.Lab{j}) == Some{C.Term.Lab{k}} : Maybe<&2, C.Term>}:
  %Equal.sym(Maybe<&2, List<&2, U32>>, n, Some{k}, en) : {T.tm.named(_, j => C.Term.Lab{j}) == Some{C.Term.Lab{k}} : Maybe<&2, C.Term>}
  {==}

def mat.of(-n: Maybe<&2, List<&2, U32>>, -r: Maybe<&2, C.Term>, -s: Maybe<&2, C.Term>, -k: List<&2, U32>, -a: C.Term, -b: C.Term,
  en: {n == Some{k} : Maybe<&2, List<&2, U32>>}, er: {r == Some{a} : Maybe<&2, C.Term>}, es: {s == Some{b} : Maybe<&2, C.Term>}) ->
  {T.tm.mat(n, r, s) == Some{C.Term.Mat{k, a, b}} : Maybe<&2, C.Term>}:
  %Equal.sym(Maybe<&2, List<&2, U32>>, n, Some{k}, en) : {T.tm.mat(_, r, s) == Some{C.Term.Mat{k, a, b}} : Maybe<&2, C.Term>}
  %Equal.sym(Maybe<&2, C.Term>, r, Some{a}, er) : {T.tm.mat(Some{k}, _, s) == Some{C.Term.Mat{k, a, b}} : Maybe<&2, C.Term>}
  %Equal.sym(Maybe<&2, C.Term>, s, Some{b}, es) : {T.tm.mat(Some{k}, Some{a}, _) == Some{C.Term.Mat{k, a, b}} : Maybe<&2, C.Term>}
  {==}

# T.tm.of one level down, at the cell's tag tg
def of.at(+g: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, +tg: U32,
  e: {PM.Tg(m, c) == tg : U32}) ->
  {T.tm.cell(U32.to_nat(tg), T.tm.quan(PM.Qn(m, c)), c, PM.Fd(2n, m, c), ks, img, u => T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)),
    u => T.tm.of(g, m, ks, img, PM.Fd(3n, m, c)), u => T.tm.of(g, m, ks, img, PM.Fd(4n, m, c))) == T.tm.of(1n+g, m, ks, img, c) : Maybe<&2, C.Term>}:
  %e : {T.tm.cell(U32.to_nat(_), T.tm.quan(PM.Qn(m, c)), c, PM.Fd(2n, m, c), ks, img, u => T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)),
    u => T.tm.of(g, m, ks, img, PM.Fd(3n, m, c)), u => T.tm.of(g, m, ks, img, PM.Fd(4n, m, c))) == T.tm.of(1n+g, m, ks, img, c) : Maybe<&2, C.Term>}
  {==}

# The bridge
# ----------

# the cell c stands for t: T.tm.of reads t from it, with any fuel f that is at
# least t's size
def is.tm.at(+f: Nat, +ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +c: U32, t: C.Term, +le: N.Le(C.Term.size(t), f), h: PM.Is(ds, m, im, fi, nx, ks, img, c, t)) ->
  {T.tm.of(f, m, ks, img, c) == Some{t} : Maybe<&2, C.Term>}:
  match f:
    case 0n:
      Empty.absurd({T.tm.of(0n, m, ks, img, c) == Some{t} : Maybe<&2, C.Term>}, size.nz(t, le))
    case 1n+(+g):
      match t:
        case C.Term.Var{+i}:
          (nd, ei) = h
          %of.at(g, m, ks, img, c, 0, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Var{i}, 0, nd)) : {_ == Some{C.Term.Var{i}} : Maybe<&2, C.Term>}
          %ei : {Some{C.Term.Var{U32.to_nat(PM.Fd(2n, m, c))}} == Some{C.Term.Var{_}} : Maybe<&2, C.Term>}
          {==}
        case C.Term.Ref{+k}:
          (nd, r) = h
          (ei, r2) = r
          %of.at(g, m, ks, img, c, 1, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Ref{k}, 1, nd)) : {_ == Some{C.Term.Ref{k}} : Maybe<&2, C.Term>}
          ei
        case C.Term.Ann{+y, +z}:
          (nd, r) = h
          (py, pz) = r
          (sy, hy) = py
          (sz, hz) = pz
          %of.at(g, m, ks, img, c, 2, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Ann{y, z}, 2, nd)) : {_ == Some{C.Term.Ann{y, z}} : Maybe<&2, C.Term>}
          two.of(a => b => C.Term.Ann{a, b}, T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(3n, m, c)), y, z, C.Term.Ann{y, z},
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, le.l(C.Term.size(y), C.Term.size(z), g, le), hy),
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, le.r(C.Term.size(y), C.Term.size(z), g, le), hz), {==})
        case C.Term.Let{+q, +v, +b}:
          (nd, r) = h
          (hq, r2) = r
          (pv, pb) = r2
          (sv, hv) = pv
          (sb, hb) = pb
          %of.at(g, m, ks, img, c, 3, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Let{q, v, b}, 3, nd)) : {_ == Some{C.Term.Let{q, v, b}} : Maybe<&2, C.Term>}
          two.of(a => d => C.Term.Let{T.tm.quan(PM.Qn(m, c)), a, d}, T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(3n, m, c)), v, b, C.Term.Let{q, v, b},
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), v, le.l(C.Term.size(v), C.Term.size(b), g, le), hv),
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), b, le.r(C.Term.size(v), C.Term.size(b), g, le), hb),
            Equal.cong(C.Quan, C.Term, p => C.Term.Let{p, v, b}, T.tm.quan(PM.Qn(m, c)), q, quan.of(C.Cir.Cells.get(m, c), q, hq)))
        case C.Term.Typ{+y}:
          (nd, r) = h
          (sy, hy) = r
          %of.at(g, m, ks, img, c, 4, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Typ{y}, 4, nd)) : {_ == Some{C.Term.Typ{y}} : Maybe<&2, C.Term>}
          one.of(a => C.Term.Typ{a}, T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)), y, C.Term.Typ{y},
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, le, hy), {==})
        case C.Term.Min{+y, +z}:
          (nd, r) = h
          (py, pz) = r
          (sy, hy) = py
          (sz, hz) = pz
          %of.at(g, m, ks, img, c, 5, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Min{y, z}, 5, nd)) : {_ == Some{C.Term.Min{y, z}} : Maybe<&2, C.Term>}
          two.of(a => b => C.Term.Min{a, b}, T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(3n, m, c)), y, z, C.Term.Min{y, z},
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, le.l(C.Term.size(y), C.Term.size(z), g, le), hy),
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, le.r(C.Term.size(y), C.Term.size(z), g, le), hz), {==})
        case C.Term.All{+q, +y, +z}:
          (nd, r) = h
          (hq, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          %of.at(g, m, ks, img, c, 6, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.All{q, y, z}, 6, nd)) : {_ == Some{C.Term.All{q, y, z}} : Maybe<&2, C.Term>}
          two.of(a => d => C.Term.All{T.tm.quan(PM.Qn(m, c)), a, d}, T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(3n, m, c)), y, z, C.Term.All{q, y, z},
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, le.l(C.Term.size(y), C.Term.size(z), g, le), hy),
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, le.r(C.Term.size(y), C.Term.size(z), g, le), hz),
            Equal.cong(C.Quan, C.Term, p => C.Term.All{p, y, z}, T.tm.quan(PM.Qn(m, c)), q, quan.of(C.Cir.Cells.get(m, c), q, hq)))
        case C.Term.Lam{+q, +y}:
          (nd, r) = h
          (hq, r2) = r
          (sy, hy) = r2
          %of.at(g, m, ks, img, c, 7, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Lam{q, y}, 7, nd)) : {_ == Some{C.Term.Lam{q, y}} : Maybe<&2, C.Term>}
          one.of(a => C.Term.Lam{T.tm.quan(PM.Qn(m, c)), a}, T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)), y, C.Term.Lam{q, y},
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, le, hy),
            Equal.cong(C.Quan, C.Term, p => C.Term.Lam{p, y}, T.tm.quan(PM.Qn(m, c)), q, quan.of(C.Cir.Cells.get(m, c), q, hq)))
        case C.Term.App{+q, +y, +z}:
          (nd, r) = h
          (hq, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          %of.at(g, m, ks, img, c, 8, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.App{q, y, z}, 8, nd)) : {_ == Some{C.Term.App{q, y, z}} : Maybe<&2, C.Term>}
          two.of(a => d => C.Term.App{T.tm.quan(PM.Qn(m, c)), a, d}, T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(3n, m, c)), y, z, C.Term.App{q, y, z},
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, le.l(C.Term.size(y), C.Term.size(z), g, le), hy),
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, le.r(C.Term.size(y), C.Term.size(z), g, le), hz),
            Equal.cong(C.Quan, C.Term, p => C.Term.App{p, y, z}, T.tm.quan(PM.Qn(m, c)), q, quan.of(C.Cir.Cells.get(m, c), q, hq)))
        case C.Term.Sig{+q, +y, +z}:
          (nd, r) = h
          (hq, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          %of.at(g, m, ks, img, c, 9, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Sig{q, y, z}, 9, nd)) : {_ == Some{C.Term.Sig{q, y, z}} : Maybe<&2, C.Term>}
          two.of(a => d => C.Term.Sig{T.tm.quan(PM.Qn(m, c)), a, d}, T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(3n, m, c)), y, z, C.Term.Sig{q, y, z},
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, le.l(C.Term.size(y), C.Term.size(z), g, le), hy),
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, le.r(C.Term.size(y), C.Term.size(z), g, le), hz),
            Equal.cong(C.Quan, C.Term, p => C.Term.Sig{p, y, z}, T.tm.quan(PM.Qn(m, c)), q, quan.of(C.Cir.Cells.get(m, c), q, hq)))
        case C.Term.Tup{+q, +y, +z}:
          (nd, r) = h
          (hq, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          %of.at(g, m, ks, img, c, 10, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Tup{q, y, z}, 10, nd)) : {_ == Some{C.Term.Tup{q, y, z}} : Maybe<&2, C.Term>}
          two.of(a => d => C.Term.Tup{T.tm.quan(PM.Qn(m, c)), a, d}, T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(3n, m, c)), y, z, C.Term.Tup{q, y, z},
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, le.l(C.Term.size(y), C.Term.size(z), g, le), hy),
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, le.r(C.Term.size(y), C.Term.size(z), g, le), hz),
            Equal.cong(C.Quan, C.Term, p => C.Term.Tup{p, y, z}, T.tm.quan(PM.Qn(m, c)), q, quan.of(C.Cir.Cells.get(m, c), q, hq)))
        case C.Term.Prj{+y}:
          (nd, r) = h
          (sy, hy) = r
          %of.at(g, m, ks, img, c, 11, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Prj{y}, 11, nd)) : {_ == Some{C.Term.Prj{y}} : Maybe<&2, C.Term>}
          one.of(a => C.Term.Prj{a}, T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)), y, C.Term.Prj{y},
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, le, hy), {==})
        case C.Term.Enu{+e}:
          (nd, r) = h
          (ei, r2) = r
          %of.at(g, m, ks, img, c, 12, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Enu{e}, 12, nd)) : {_ == Some{C.Term.Enu{e}} : Maybe<&2, C.Term>}
          ei
        case C.Term.Lab{+k}:
          (nd, nm) = h
          (en, ej) = nm
          %of.at(g, m, ks, img, c, 13, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Lab{k}, 13, nd)) : {_ == Some{C.Term.Lab{k}} : Maybe<&2, C.Term>}
          named.of(T.tm.name(ks, PM.Fd(2n, m, c)), k, en)
        case C.Term.Mat{+k, +y, +z}:
          (nd, r) = h
          (nm, r2) = r
          (en, ej) = nm
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          %of.at(g, m, ks, img, c, 14, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Mat{k, y, z}, 14, nd)) : {_ == Some{C.Term.Mat{k, y, z}} : Maybe<&2, C.Term>}
          mat.of(T.tm.name(ks, PM.Fd(2n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(3n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(4n, m, c)), k, y, z, en,
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), y, le.l(C.Term.size(y), C.Term.size(z), g, le), hy),
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(4n, m, c), z, le.r(C.Term.size(y), C.Term.size(z), g, le), hz))
        case C.Term.Efq{}:
          %of.at(g, m, ks, img, c, 15, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Efq{}, 15, h)) : {_ == Some{C.Term.Efq{}} : Maybe<&2, C.Term>}
          {==}
        case C.Term.Eql{+y, +z, +w}:
          (nd, r) = h
          (py, r2) = r
          (sy, hy) = py
          (pz, pw) = r2
          (sz, hz) = pz
          (sw, hw) = pw
          %of.at(g, m, ks, img, c, 16, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Eql{y, z, w}, 16, nd)) : {_ == Some{C.Term.Eql{y, z, w}} : Maybe<&2, C.Term>}
          three.of(a => b => d => C.Term.Eql{a, b, d}, T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(3n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(4n, m, c)), y, z, w,
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, le.l(C.Term.size(y), Nat.add(C.Term.size(z), C.Term.size(w)), g, le), hy),
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, le.m(C.Term.size(y), C.Term.size(z), C.Term.size(w), g, le), hz),
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(4n, m, c), w, le.e(C.Term.size(y), C.Term.size(z), C.Term.size(w), g, le), hw))
        case C.Term.Rfl{}:
          %of.at(g, m, ks, img, c, 17, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Rfl{}, 17, h)) : {_ == Some{C.Term.Rfl{}} : Maybe<&2, C.Term>}
          {==}
        case C.Term.Rwt{+y, +z, +w}:
          (nd, r) = h
          (py, r2) = r
          (sy, hy) = py
          (pz, pw) = r2
          (sz, hz) = pz
          (sw, hw) = pw
          %of.at(g, m, ks, img, c, 18, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Rwt{y, z, w}, 18, nd)) : {_ == Some{C.Term.Rwt{y, z, w}} : Maybe<&2, C.Term>}
          three.of(a => b => d => C.Term.Rwt{a, b, d}, T.tm.of(g, m, ks, img, PM.Fd(2n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(3n, m, c)), T.tm.of(g, m, ks, img, PM.Fd(4n, m, c)), y, z, w,
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, le.l(C.Term.size(y), Nat.add(C.Term.size(z), C.Term.size(w)), g, le), hy),
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, le.m(C.Term.size(y), C.Term.size(z), C.Term.size(w), g, le), hz),
            is.tm.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(4n, m, c), w, le.e(C.Term.size(y), C.Term.size(z), C.Term.size(w), g, le), hw))

# the cell c stands for t: T.tm.of reads t from it
def is.tm(+ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +c: U32, +t: C.Term, h: PM.Is(ds, m, im, fi, nx, ks, img, c, t)) ->
  {T.tm.of(C.Term.size(t), m, ks, img, c) == Some{t} : Maybe<&2, C.Term>}:
  is.tm.at(C.Term.size(t), ds, m, im, fi, nx, ks, img, c, t, N.le_refl(C.Term.size(t)), h)

# Cells that T.tm.of reads
# ------------------------

# the parts that T.tm.of reads of a cell of the tag, by what each part says
def Rd.cell(tag: Nat, r2: Bool, r3: Bool, r4: Bool) -> Bool:
  match tag:
    case 0n:
      True{}
    case 1n:
      True{}
    case 2n:
      r2 && r3
    case 3n:
      r2 && r3
    case 4n:
      r2
    case 5n:
      r2 && r3
    case 6n:
      r2 && r3
    case 7n:
      r2
    case 8n:
      r2 && r3
    case 9n:
      r2 && r3
    case 10n:
      r2 && r3
    case 11n:
      r2
    case 12n:
      True{}
    case 13n:
      True{}
    case 14n:
      r3 && r4
    case 15n:
      True{}
    case 16n:
      r2 && (r3 && r4)
    case 17n:
      True{}
    case 18n:
      r2 && (r3 && r4)
    case 19n+k:
      True{}

# every cell that T.tm.of reads from c, with the fuel f, is a cell that the
# machine may access
def Rd(f: Nat, +m: C.Cir.Cells, +c: U32, +im: U32, +fi: U32, +nx: U32) -> Bool:
  match f:
    case 0n:
      True{}
    case 1n+(+g):
      C.Cir.is_cell(c, im, fi, nx) && Rd.cell(U32.to_nat(PM.Tg(m, c)), Rd(g, m, PM.Fd(2n, m, c), im, fi, nx),
        Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), Rd(g, m, PM.Fd(4n, m, c), im, fi, nx))

# Rd one level down, at the cell's tag tg
def rd.at(+g: Nat, +m: C.Cir.Cells, +c: U32, +im: U32, +fi: U32, +nx: U32, +tg: U32, e: {PM.Tg(m, c) == tg : U32},
  hc: {C.Cir.is_cell(c, im, fi, nx) == True{} : Bool},
  hp: {Rd.cell(U32.to_nat(tg), Rd(g, m, PM.Fd(2n, m, c), im, fi, nx), Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), Rd(g, m, PM.Fd(4n, m, c), im, fi, nx)) == True{} : Bool}) ->
  {Rd(1n+g, m, c, im, fi, nx) == True{} : Bool}:
  %Equal.sym(U32, PM.Tg(m, c), tg, e) : {Bool.and(C.Cir.is_cell(c, im, fi, nx), Rd.cell(U32.to_nat(_), Rd(g, m, PM.Fd(2n, m, c), im, fi, nx),
    Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), Rd(g, m, PM.Fd(4n, m, c), im, fi, nx))) == True{} : Bool}
  and.i(C.Cir.is_cell(c, im, fi, nx), Rd.cell(U32.to_nat(tg), Rd(g, m, PM.Fd(2n, m, c), im, fi, nx), Rd(g, m, PM.Fd(3n, m, c), im, fi, nx),
    Rd(g, m, PM.Fd(4n, m, c), im, fi, nx)), hc, hp)

# the cell c stands for t: every cell that T.tm.of reads from it, with any
# fuel f, is a cell (Nd)
def is.rd.at(+f: Nat, +ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +c: U32, t: C.Term, h: PM.Is(ds, m, im, fi, nx, ks, img, c, t)) ->
  {Rd(f, m, c, im, fi, nx) == True{} : Bool}:
  match f:
    case 0n:
      {==}
    case 1n+(+g):
      match t:
        case C.Term.Var{+i}:
          (nd, ei) = h
          rd.at(g, m, c, im, fi, nx, 0, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Var{i}, 0, nd), nd.cell(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Var{i}, 0, nd),
            {==})
        case C.Term.Ref{+k}:
          (nd, r) = h
          rd.at(g, m, c, im, fi, nx, 1, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Ref{k}, 1, nd), nd.cell(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Ref{k}, 1, nd),
            {==})
        case C.Term.Ann{+y, +z}:
          (nd, r) = h
          (py, pz) = r
          (sy, hy) = py
          (sz, hz) = pz
          rd.at(g, m, c, im, fi, nx, 2, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Ann{y, z}, 2, nd), nd.cell(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Ann{y, z}, 2, nd),
            and.i(Rd(g, m, PM.Fd(2n, m, c), im, fi, nx), Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, hy), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, hz)))
        case C.Term.Let{+q, +y, +z}:
          (nd, r) = h
          (hq, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          rd.at(g, m, c, im, fi, nx, 3, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Let{q, y, z}, 3, nd), nd.cell(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Let{q, y, z}, 3, nd),
            and.i(Rd(g, m, PM.Fd(2n, m, c), im, fi, nx), Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, hy), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, hz)))
        case C.Term.Typ{+y}:
          (nd, r) = h
          (sy, hy) = r
          rd.at(g, m, c, im, fi, nx, 4, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Typ{y}, 4, nd), nd.cell(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Typ{y}, 4, nd),
            is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, hy))
        case C.Term.Min{+y, +z}:
          (nd, r) = h
          (py, pz) = r
          (sy, hy) = py
          (sz, hz) = pz
          rd.at(g, m, c, im, fi, nx, 5, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Min{y, z}, 5, nd), nd.cell(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Min{y, z}, 5, nd),
            and.i(Rd(g, m, PM.Fd(2n, m, c), im, fi, nx), Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, hy), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, hz)))
        case C.Term.All{+q, +y, +z}:
          (nd, r) = h
          (hq, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          rd.at(g, m, c, im, fi, nx, 6, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.All{q, y, z}, 6, nd), nd.cell(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.All{q, y, z}, 6, nd),
            and.i(Rd(g, m, PM.Fd(2n, m, c), im, fi, nx), Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, hy), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, hz)))
        case C.Term.Lam{+q, +y}:
          (nd, r) = h
          (hq, r2) = r
          (sy, hy) = r2
          rd.at(g, m, c, im, fi, nx, 7, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Lam{q, y}, 7, nd), nd.cell(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Lam{q, y}, 7, nd),
            is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, hy))
        case C.Term.App{+q, +y, +z}:
          (nd, r) = h
          (hq, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          rd.at(g, m, c, im, fi, nx, 8, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.App{q, y, z}, 8, nd), nd.cell(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.App{q, y, z}, 8, nd),
            and.i(Rd(g, m, PM.Fd(2n, m, c), im, fi, nx), Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, hy), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, hz)))
        case C.Term.Sig{+q, +y, +z}:
          (nd, r) = h
          (hq, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          rd.at(g, m, c, im, fi, nx, 9, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Sig{q, y, z}, 9, nd), nd.cell(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Sig{q, y, z}, 9, nd),
            and.i(Rd(g, m, PM.Fd(2n, m, c), im, fi, nx), Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, hy), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, hz)))
        case C.Term.Tup{+q, +y, +z}:
          (nd, r) = h
          (hq, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          rd.at(g, m, c, im, fi, nx, 10, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Tup{q, y, z}, 10, nd), nd.cell(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Tup{q, y, z}, 10, nd),
            and.i(Rd(g, m, PM.Fd(2n, m, c), im, fi, nx), Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, hy), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, hz)))
        case C.Term.Prj{+y}:
          (nd, r) = h
          (sy, hy) = r
          rd.at(g, m, c, im, fi, nx, 11, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Prj{y}, 11, nd), nd.cell(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Prj{y}, 11, nd),
            is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, hy))
        case C.Term.Enu{+e}:
          (nd, r) = h
          rd.at(g, m, c, im, fi, nx, 12, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Enu{e}, 12, nd), nd.cell(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Enu{e}, 12, nd),
            {==})
        case C.Term.Lab{+k}:
          (nd, r) = h
          rd.at(g, m, c, im, fi, nx, 13, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Lab{k}, 13, nd), nd.cell(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Lab{k}, 13, nd),
            {==})
        case C.Term.Mat{+k, +y, +z}:
          (nd, r) = h
          (nm, r2) = r
          (py, pz) = r2
          (sy, hy) = py
          (sz, hz) = pz
          rd.at(g, m, c, im, fi, nx, 14, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Mat{k, y, z}, 14, nd), nd.cell(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Mat{k, y, z}, 14, nd),
            and.i(Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), Rd(g, m, PM.Fd(4n, m, c), im, fi, nx), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), y, hy), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(4n, m, c), z, hz)))
        case C.Term.Efq{}:
          rd.at(g, m, c, im, fi, nx, 15, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Efq{}, 15, h), nd.cell(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Efq{}, 15, h),
            {==})
        case C.Term.Eql{+y, +z, +w}:
          (nd, r) = h
          (py, r2) = r
          (sy, hy) = py
          (pz, pw) = r2
          (sz, hz) = pz
          (sw, hw) = pw
          rd.at(g, m, c, im, fi, nx, 16, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Eql{y, z, w}, 16, nd), nd.cell(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Eql{y, z, w}, 16, nd),
            and.i(Rd(g, m, PM.Fd(2n, m, c), im, fi, nx), Bool.and(Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), Rd(g, m, PM.Fd(4n, m, c), im, fi, nx)), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, hy), and.i(Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), Rd(g, m, PM.Fd(4n, m, c), im, fi, nx), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, hz), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(4n, m, c), w, hw))))
        case C.Term.Rfl{}:
          rd.at(g, m, c, im, fi, nx, 17, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Rfl{}, 17, h), nd.cell(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Rfl{}, 17, h),
            {==})
        case C.Term.Rwt{+y, +z, +w}:
          (nd, r) = h
          (py, r2) = r
          (sy, hy) = py
          (pz, pw) = r2
          (sz, hz) = pz
          (sw, hw) = pw
          rd.at(g, m, c, im, fi, nx, 18, nd.tag(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Rwt{y, z, w}, 18, nd), nd.cell(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Rwt{y, z, w}, 18, nd),
            and.i(Rd(g, m, PM.Fd(2n, m, c), im, fi, nx), Bool.and(Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), Rd(g, m, PM.Fd(4n, m, c), im, fi, nx)), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), y, hy), and.i(Rd(g, m, PM.Fd(3n, m, c), im, fi, nx), Rd(g, m, PM.Fd(4n, m, c), im, fi, nx), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, c), z, hz), is.rd.at(g, ds, m, im, fi, nx, ks, img, PM.Fd(4n, m, c), w, hw))))

# the cell c stands for t: every cell that T.tm.of reads from it is a cell
def is.rd(+ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +c: U32, +t: C.Term, h: PM.Is(ds, m, im, fi, nx, ks, img, c, t)) ->
  {Rd(C.Term.size(t), m, c, im, fi, nx) == True{} : Bool}:
  is.rd.at(C.Term.size(t), ds, m, im, fi, nx, ks, img, c, t, h)
