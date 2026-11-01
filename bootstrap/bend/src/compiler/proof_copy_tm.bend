# compiler: checked terms stay
# ============================
#
# A checked term (D.Tm) reads only cells that may be read, by its tag's
# parts; it stays when the run writes a cell that it may not read, when it
# writes only a count (field 1), with more fuel, and when more cells may be
# read. Each proof goes by the fuel, and at a cell by Cg: T.tm.cell gives the
# same term from parts that give at least what they gave.

import Base
import ./impl.bend as C
import ./proof_term.bend as T
import ./proof_need.bend as N
import ./proof_copy.bend as D
import ./proof_copy_kit.bend as K

# Parts
# -----

# a part that gave a gives a again
def Pt(p: Unit -> Maybe<&2, C.Term>, q: Unit -> Maybe<&2, C.Term>) -> Type:
  @a: C.Term -> {p(Unit{}) == Some{a} : Maybe<&2, C.Term>} -> {q(Unit{}) == Some{a} : Maybe<&2, C.Term>}

def Mb.some(-A: Data, -a: A, -b: A, e: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  Equal.cong(Maybe<&2, A>, A, x => Maybe.default(&2, A, x, a), Some{a}, Some{b}, e)

def Mb.ns(-A: Data, -b: A, -G: Type, e: {None{} == Some{b} : Maybe<&2, A>}) -> G:
  Empty.absurd(G, N.true_ne_false(Equal.cong(Maybe<&2, A>, Bool, x => Maybe.is_none(&2, A, x), None{}, Some{b}, e)))

def Cg.one(-k: C.Term -> C.Term, r: Maybe<&2, C.Term>, s: Maybe<&2, C.Term>, -t: C.Term,
  h: {T.tm.one(k, r) == Some{t} : Maybe<&2, C.Term>}, g: @a: C.Term -> {r == Some{a} : Maybe<&2, C.Term>} -> {s == Some{a} : Maybe<&2, C.Term>}) ->
  {T.tm.one(k, s) == Some{t} : Maybe<&2, C.Term>}:
  match r:
    case None{}:
      Mb.ns(C.Term, t, {T.tm.one(k, s) == Some{t} : Maybe<&2, C.Term>}, h)
    case Some{+a}:
      %Equal.sym(Maybe<&2, C.Term>, s, Some{a}, g(a, {==})) : {T.tm.one(k, _) == Some{t} : Maybe<&2, C.Term>}
      h

def Cg.two.s(-k: C.Term -> C.Term -> C.Term, +a: C.Term, r2: Maybe<&2, C.Term>, s1: Maybe<&2, C.Term>, s2: Maybe<&2, C.Term>, -t: C.Term,
  e1: {s1 == Some{a} : Maybe<&2, C.Term>}, h: {T.tm.two(k, Some{a}, r2) == Some{t} : Maybe<&2, C.Term>},
  g2: @b: C.Term -> {r2 == Some{b} : Maybe<&2, C.Term>} -> {s2 == Some{b} : Maybe<&2, C.Term>}) ->
  {T.tm.two(k, s1, s2) == Some{t} : Maybe<&2, C.Term>}:
  match r2:
    case None{}:
      Mb.ns(C.Term, t, {T.tm.two(k, s1, s2) == Some{t} : Maybe<&2, C.Term>}, h)
    case Some{+b}:
      %Equal.sym(Maybe<&2, C.Term>, s1, Some{a}, e1) : {T.tm.two(k, _, s2) == Some{t} : Maybe<&2, C.Term>}
      %Equal.sym(Maybe<&2, C.Term>, s2, Some{b}, g2(b, {==})) : {T.tm.two(k, Some{a}, _) == Some{t} : Maybe<&2, C.Term>}
      h

def Cg.two(-k: C.Term -> C.Term -> C.Term, r1: Maybe<&2, C.Term>, r2: Maybe<&2, C.Term>, s1: Maybe<&2, C.Term>, s2: Maybe<&2, C.Term>,
  -t: C.Term, h: {T.tm.two(k, r1, r2) == Some{t} : Maybe<&2, C.Term>},
  g1: @a: C.Term -> {r1 == Some{a} : Maybe<&2, C.Term>} -> {s1 == Some{a} : Maybe<&2, C.Term>},
  g2: @b: C.Term -> {r2 == Some{b} : Maybe<&2, C.Term>} -> {s2 == Some{b} : Maybe<&2, C.Term>}) ->
  {T.tm.two(k, s1, s2) == Some{t} : Maybe<&2, C.Term>}:
  match r1:
    case None{}:
      Mb.ns(C.Term, t, {T.tm.two(k, s1, s2) == Some{t} : Maybe<&2, C.Term>}, h)
    case Some{+a}:
      Cg.two.s(k, a, r2, s1, s2, t, g1(a, {==}), h, g2)

def Cg.three.t(-k: C.Term -> C.Term -> C.Term -> C.Term, +a: C.Term, +b: C.Term, r3: Maybe<&2, C.Term>, s1: Maybe<&2, C.Term>,
  s2: Maybe<&2, C.Term>, s3: Maybe<&2, C.Term>, -t: C.Term, e1: {s1 == Some{a} : Maybe<&2, C.Term>}, e2: {s2 == Some{b} : Maybe<&2, C.Term>},
  h: {T.tm.three(k, Some{a}, Some{b}, r3) == Some{t} : Maybe<&2, C.Term>},
  g3: @c: C.Term -> {r3 == Some{c} : Maybe<&2, C.Term>} -> {s3 == Some{c} : Maybe<&2, C.Term>}) ->
  {T.tm.three(k, s1, s2, s3) == Some{t} : Maybe<&2, C.Term>}:
  match r3:
    case None{}:
      Mb.ns(C.Term, t, {T.tm.three(k, s1, s2, s3) == Some{t} : Maybe<&2, C.Term>}, h)
    case Some{+c}:
      %Equal.sym(Maybe<&2, C.Term>, s1, Some{a}, e1) : {T.tm.three(k, _, s2, s3) == Some{t} : Maybe<&2, C.Term>}
      %Equal.sym(Maybe<&2, C.Term>, s2, Some{b}, e2) : {T.tm.three(k, Some{a}, _, s3) == Some{t} : Maybe<&2, C.Term>}
      %Equal.sym(Maybe<&2, C.Term>, s3, Some{c}, g3(c, {==})) : {T.tm.three(k, Some{a}, Some{b}, _) == Some{t} : Maybe<&2, C.Term>}
      h

def Cg.three.s(-k: C.Term -> C.Term -> C.Term -> C.Term, +a: C.Term, r2: Maybe<&2, C.Term>, r3: Maybe<&2, C.Term>, s1: Maybe<&2, C.Term>,
  s2: Maybe<&2, C.Term>, s3: Maybe<&2, C.Term>, -t: C.Term, e1: {s1 == Some{a} : Maybe<&2, C.Term>},
  h: {T.tm.three(k, Some{a}, r2, r3) == Some{t} : Maybe<&2, C.Term>},
  g2: @b: C.Term -> {r2 == Some{b} : Maybe<&2, C.Term>} -> {s2 == Some{b} : Maybe<&2, C.Term>},
  g3: @c: C.Term -> {r3 == Some{c} : Maybe<&2, C.Term>} -> {s3 == Some{c} : Maybe<&2, C.Term>}) ->
  {T.tm.three(k, s1, s2, s3) == Some{t} : Maybe<&2, C.Term>}:
  match r2:
    case None{}:
      Mb.ns(C.Term, t, {T.tm.three(k, s1, s2, s3) == Some{t} : Maybe<&2, C.Term>}, h)
    case Some{+b}:
      Cg.three.t(k, a, b, r3, s1, s2, s3, t, e1, g2(b, {==}), h, g3)

def Cg.three(-k: C.Term -> C.Term -> C.Term -> C.Term, r1: Maybe<&2, C.Term>, r2: Maybe<&2, C.Term>, r3: Maybe<&2, C.Term>,
  s1: Maybe<&2, C.Term>, s2: Maybe<&2, C.Term>, s3: Maybe<&2, C.Term>, -t: C.Term,
  h: {T.tm.three(k, r1, r2, r3) == Some{t} : Maybe<&2, C.Term>},
  g1: @a: C.Term -> {r1 == Some{a} : Maybe<&2, C.Term>} -> {s1 == Some{a} : Maybe<&2, C.Term>},
  g2: @b: C.Term -> {r2 == Some{b} : Maybe<&2, C.Term>} -> {s2 == Some{b} : Maybe<&2, C.Term>},
  g3: @c: C.Term -> {r3 == Some{c} : Maybe<&2, C.Term>} -> {s3 == Some{c} : Maybe<&2, C.Term>}) ->
  {T.tm.three(k, s1, s2, s3) == Some{t} : Maybe<&2, C.Term>}:
  match r1:
    case None{}:
      Mb.ns(C.Term, t, {T.tm.three(k, s1, s2, s3) == Some{t} : Maybe<&2, C.Term>}, h)
    case Some{+a}:
      Cg.three.s(k, a, r2, r3, s1, s2, s3, t, g1(a, {==}), h, g2, g3)

def Cg.mat.t(+kk: List<&2, U32>, +a: C.Term, r2: Maybe<&2, C.Term>, s1: Maybe<&2, C.Term>, s2: Maybe<&2, C.Term>, -t: C.Term,
  e1: {s1 == Some{a} : Maybe<&2, C.Term>}, h: {T.tm.mat(Some{kk}, Some{a}, r2) == Some{t} : Maybe<&2, C.Term>},
  g2: @b: C.Term -> {r2 == Some{b} : Maybe<&2, C.Term>} -> {s2 == Some{b} : Maybe<&2, C.Term>}) ->
  {T.tm.mat(Some{kk}, s1, s2) == Some{t} : Maybe<&2, C.Term>}:
  match r2:
    case None{}:
      Mb.ns(C.Term, t, {T.tm.mat(Some{kk}, s1, s2) == Some{t} : Maybe<&2, C.Term>}, h)
    case Some{+b}:
      %Equal.sym(Maybe<&2, C.Term>, s1, Some{a}, e1) : {T.tm.mat(Some{kk}, _, s2) == Some{t} : Maybe<&2, C.Term>}
      %Equal.sym(Maybe<&2, C.Term>, s2, Some{b}, g2(b, {==})) : {T.tm.mat(Some{kk}, Some{a}, _) == Some{t} : Maybe<&2, C.Term>}
      h

def Cg.mat.s(+kk: List<&2, U32>, r1: Maybe<&2, C.Term>, r2: Maybe<&2, C.Term>, s1: Maybe<&2, C.Term>, s2: Maybe<&2, C.Term>, -t: C.Term,
  h: {T.tm.mat(Some{kk}, r1, r2) == Some{t} : Maybe<&2, C.Term>},
  g1: @a: C.Term -> {r1 == Some{a} : Maybe<&2, C.Term>} -> {s1 == Some{a} : Maybe<&2, C.Term>},
  g2: @b: C.Term -> {r2 == Some{b} : Maybe<&2, C.Term>} -> {s2 == Some{b} : Maybe<&2, C.Term>}) ->
  {T.tm.mat(Some{kk}, s1, s2) == Some{t} : Maybe<&2, C.Term>}:
  match r1:
    case None{}:
      Mb.ns(C.Term, t, {T.tm.mat(Some{kk}, s1, s2) == Some{t} : Maybe<&2, C.Term>}, h)
    case Some{+a}:
      Cg.mat.t(kk, a, r2, s1, s2, t, g1(a, {==}), h, g2)

def Cg.mat(n: Maybe<&2, List<&2, U32>>, r1: Maybe<&2, C.Term>, r2: Maybe<&2, C.Term>, s1: Maybe<&2, C.Term>, s2: Maybe<&2, C.Term>, -t: C.Term,
  h: {T.tm.mat(n, r1, r2) == Some{t} : Maybe<&2, C.Term>},
  g1: @a: C.Term -> {r1 == Some{a} : Maybe<&2, C.Term>} -> {s1 == Some{a} : Maybe<&2, C.Term>},
  g2: @b: C.Term -> {r2 == Some{b} : Maybe<&2, C.Term>} -> {s2 == Some{b} : Maybe<&2, C.Term>}) ->
  {T.tm.mat(n, s1, s2) == Some{t} : Maybe<&2, C.Term>}:
  match n:
    case None{}:
      Mb.ns(C.Term, t, {T.tm.mat(None{}, s1, s2) == Some{t} : Maybe<&2, C.Term>}, h)
    case Some{+kk}:
      Cg.mat.s(kk, r1, r2, s1, s2, t, h, g1, g2)

# T.tm.cell gives the same term t from parts that give at least what they gave
def Cg(tag: Nat, +q: C.Quan, +c: U32, +f2: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  p2: Unit -> Maybe<&2, C.Term>, p3: Unit -> Maybe<&2, C.Term>, p4: Unit -> Maybe<&2, C.Term>,
  q2: Unit -> Maybe<&2, C.Term>, q3: Unit -> Maybe<&2, C.Term>, q4: Unit -> Maybe<&2, C.Term>, -t: C.Term,
  h: {T.tm.cell(tag, q, c, f2, ks, img, p2, p3, p4) == Some{t} : Maybe<&2, C.Term>},
  g2: Pt(p2, q2), g3: Pt(p3, q3), g4: Pt(p4, q4)) ->
  {T.tm.cell(tag, q, c, f2, ks, img, q2, q3, q4) == Some{t} : Maybe<&2, C.Term>}:
  match tag:
    case 0n:
      h
    case 1n:
      h
    case 2n:
      Cg.two(a => b => C.Term.Ann{a, b}, p2(Unit{}), p3(Unit{}), q2(Unit{}), q3(Unit{}), t, h, g2, g3)
    case 3n:
      Cg.two(a => b => C.Term.Let{q, a, b}, p2(Unit{}), p3(Unit{}), q2(Unit{}), q3(Unit{}), t, h, g2, g3)
    case 4n:
      Cg.one(a => C.Term.Typ{a}, p2(Unit{}), q2(Unit{}), t, h, g2)
    case 5n:
      Cg.two(a => b => C.Term.Min{a, b}, p2(Unit{}), p3(Unit{}), q2(Unit{}), q3(Unit{}), t, h, g2, g3)
    case 6n:
      Cg.two(a => b => C.Term.All{q, a, b}, p2(Unit{}), p3(Unit{}), q2(Unit{}), q3(Unit{}), t, h, g2, g3)
    case 7n:
      Cg.one(a => C.Term.Lam{q, a}, p2(Unit{}), q2(Unit{}), t, h, g2)
    case 8n:
      Cg.two(a => b => C.Term.App{q, a, b}, p2(Unit{}), p3(Unit{}), q2(Unit{}), q3(Unit{}), t, h, g2, g3)
    case 9n:
      Cg.two(a => b => C.Term.Sig{q, a, b}, p2(Unit{}), p3(Unit{}), q2(Unit{}), q3(Unit{}), t, h, g2, g3)
    case 10n:
      Cg.two(a => b => C.Term.Tup{q, a, b}, p2(Unit{}), p3(Unit{}), q2(Unit{}), q3(Unit{}), t, h, g2, g3)
    case 11n:
      Cg.one(a => C.Term.Prj{a}, p2(Unit{}), q2(Unit{}), t, h, g2)
    case 12n:
      h
    case 13n:
      h
    case 14n:
      Cg.mat(T.tm.name(ks, f2), p3(Unit{}), p4(Unit{}), q3(Unit{}), q4(Unit{}), t, h, g3, g4)
    case 15n:
      h
    case 16n:
      Cg.three(a => b => y => C.Term.Eql{a, b, y}, p2(Unit{}), p3(Unit{}), p4(Unit{}), q2(Unit{}), q3(Unit{}), q4(Unit{}), t, h, g2, g3, g4)
    case 17n:
      h
    case 18n:
      Cg.three(a => b => y => C.Term.Rwt{a, b, y}, p2(Unit{}), p3(Unit{}), p4(Unit{}), q2(Unit{}), q3(Unit{}), q4(Unit{}), t, h, g2, g3, g4)
    case 19n+r:
      h

# Checked terms
# -------------

# Tm.chk gives t from a part that gives at least what it gave
def Tm.chk.cg(+tag: Nat, +fvf: U32, r: Maybe<&2, C.Term>, s: Maybe<&2, C.Term>, -t: C.Term,
  h: {D.Tm.chk(tag, fvf, r) == Some{t} : Maybe<&2, C.Term>},
  g: @a: C.Term -> {r == Some{a} : Maybe<&2, C.Term>} -> {s == Some{a} : Maybe<&2, C.Term>}) ->
  {D.Tm.chk(tag, fvf, s) == Some{t} : Maybe<&2, C.Term>}:
  match r:
    case None{}:
      Mb.ns(C.Term, t, {D.Tm.chk(tag, fvf, s) == Some{t} : Maybe<&2, C.Term>}, h)
    case Some{+a}:
      %Equal.sym(Maybe<&2, C.Term>, s, Some{a}, g(a, {==})) : {D.Tm.chk(tag, fvf, _) == Some{t} : Maybe<&2, C.Term>}
      h

# the checked term of the cell c, whose content is cell, with the fuel 1 + f,
# when ok says that c may be read
def Tm.at.b(ok: Bool, +f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32, +cell: C.Cir.Cell) -> Maybe<&2, C.Term>:
  +f0 = C.Cir.Cell.get(0n, cell)
  +tag = U32.to_nat(U32.and(f0, 63))
  D.Tm.if(ok, u => D.Tm.chk(tag, U32.shrn(f0, 13n),
    T.tm.cell(tag, T.tm.quan(U32.and(U32.shrn(f0, 6n), 3)), c, C.Cir.Cell.get(2n, cell), ks, img,
      u => D.Tm(f, m, ks, img, K, F, X, N, C.Cir.Cell.get(2n, cell)),
      u => D.Tm(f, m, ks, img, K, F, X, N, C.Cir.Cell.get(3n, cell)),
      u => D.Tm(f, m, ks, img, K, F, X, N, C.Cir.Cell.get(4n, cell)))))

def Tm.at(+f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32, +cell: C.Cir.Cell) -> Maybe<&2, C.Term>:
  Tm.at.b(D.Al(K, F, X, N, c), f, m, ks, img, K, F, X, N, c, cell)

def Tm.at.eq(+f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32) ->
  {D.Tm(1n+f, m, ks, img, K, F, X, N, c) == Tm.at(f, m, ks, img, K, F, X, N, c, C.Cir.Cells.get(m, c)) : Maybe<&2, C.Term>}:
  {==}

# a cell that a checked term reads may be read
def Tm.al.if(b: Bool, +f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32, +cell: C.Cir.Cell, -t: C.Term, eb: {b == D.Al(K, F, X, N, c) : Bool},
  h: {Tm.at.b(b, f, m, ks, img, K, F, X, N, c, cell) == Some{t} : Maybe<&2, C.Term>}) -> {D.Al(K, F, X, N, c) == True{} : Bool}:
  match b:
    case True{}:
      Equal.sym(Bool, True{}, D.Al(K, F, X, N, c), eb)
    case False{}:
      Mb.ns(C.Term, t, {D.Al(K, F, X, N, c) == True{} : Bool}, h)

# a cell that may be read is not one that may not
def Al.ne.if(b: Bool, +K: U32, +F: U32, +X: List<&2, U32>, +N: U32, +c: U32, +i: U32, eb: {b == U32.is_eq(c, i) : Bool},
  ha: {D.Al(K, F, X, N, c) == True{} : Bool}, hi: {False{} == D.Al(K, F, X, N, i) : Bool}) -> {U32.is_eq(c, i) == False{} : Bool}:
  match b:
    case True{}:
      +e = K.U.eq(c, i, Equal.sym(Bool, True{}, U32.is_eq(c, i), eb))
      K.Bo.ft({U32.is_eq(c, i) == False{} : Bool}, Equal.trans(Bool, True{}, D.Al(K, F, X, N, c), False{},
        Equal.sym(Bool, D.Al(K, F, X, N, c), True{}, ha),
        Equal.trans(Bool, D.Al(K, F, X, N, c), D.Al(K, F, X, N, i), False{}, Equal.cong(U32, Bool, y => D.Al(K, F, X, N, y), c, i, e),
          Equal.sym(Bool, False{}, D.Al(K, F, X, N, i), hi))))
    case False{}:
      Equal.sym(Bool, False{}, U32.is_eq(c, i), eb)

# the round at a readable cell, from parts that give at least what they gave
def Tm.at.cg(b: Bool, +f: Nat, +f2: Nat, +m: C.Cir.Cells, +m2: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +K: U32, +F: U32, +X: List<&2, U32>, +N: U32, +X2: List<&2, U32>, +N2: U32, +b2: Bool, +c: U32, +cell: C.Cir.Cell, -t: C.Term,
  eb: {b == b2 : Bool},
  h: {Tm.at.b(b, f, m, ks, img, K, F, X, N, c, cell) == Some{t} : Maybe<&2, C.Term>},
  g2: Pt(u => D.Tm(f, m, ks, img, K, F, X, N, C.Cir.Cell.get(2n, cell)), u => D.Tm(f2, m2, ks, img, K, F, X2, N2, C.Cir.Cell.get(2n, cell))),
  g3: Pt(u => D.Tm(f, m, ks, img, K, F, X, N, C.Cir.Cell.get(3n, cell)), u => D.Tm(f2, m2, ks, img, K, F, X2, N2, C.Cir.Cell.get(3n, cell))),
  g4: Pt(u => D.Tm(f, m, ks, img, K, F, X, N, C.Cir.Cell.get(4n, cell)), u => D.Tm(f2, m2, ks, img, K, F, X2, N2, C.Cir.Cell.get(4n, cell)))) ->
  {Tm.at.b(b2, f2, m2, ks, img, K, F, X2, N2, c, cell) == Some{t} : Maybe<&2, C.Term>}:
  match b:
    case False{}:
      Mb.ns(C.Term, t, {Tm.at.b(b2, f2, m2, ks, img, K, F, X2, N2, c, cell) == Some{t} : Maybe<&2, C.Term>}, h)
    case True{}:
      %eb : {Tm.at.b(_, f2, m2, ks, img, K, F, X2, N2, c, cell) == Some{t} : Maybe<&2, C.Term>}
      +f0 = C.Cir.Cell.get(0n, cell)
      +tag = U32.to_nat(U32.and(f0, 63))
      +q = T.tm.quan(U32.and(U32.shrn(f0, 6n), 3))
      Tm.chk.cg(tag, U32.shrn(f0, 13n),
        T.tm.cell(tag, q, c, C.Cir.Cell.get(2n, cell), ks, img,
          u => D.Tm(f, m, ks, img, K, F, X, N, C.Cir.Cell.get(2n, cell)), u => D.Tm(f, m, ks, img, K, F, X, N, C.Cir.Cell.get(3n, cell)),
          u => D.Tm(f, m, ks, img, K, F, X, N, C.Cir.Cell.get(4n, cell))),
        T.tm.cell(tag, q, c, C.Cir.Cell.get(2n, cell), ks, img,
          u => D.Tm(f2, m2, ks, img, K, F, X2, N2, C.Cir.Cell.get(2n, cell)), u => D.Tm(f2, m2, ks, img, K, F, X2, N2, C.Cir.Cell.get(3n, cell)),
          u => D.Tm(f2, m2, ks, img, K, F, X2, N2, C.Cir.Cell.get(4n, cell))),
        t, h,
        a => ha => Cg(tag, q, c, C.Cir.Cell.get(2n, cell), ks, img,
          u => D.Tm(f, m, ks, img, K, F, X, N, C.Cir.Cell.get(2n, cell)), u => D.Tm(f, m, ks, img, K, F, X, N, C.Cir.Cell.get(3n, cell)),
          u => D.Tm(f, m, ks, img, K, F, X, N, C.Cir.Cell.get(4n, cell)),
          u => D.Tm(f2, m2, ks, img, K, F, X2, N2, C.Cir.Cell.get(2n, cell)), u => D.Tm(f2, m2, ks, img, K, F, X2, N2, C.Cir.Cell.get(3n, cell)),
          u => D.Tm(f2, m2, ks, img, K, F, X2, N2, C.Cir.Cell.get(4n, cell)), a, ha, g2, g3, g4))

# writing a cell i that may not be read keeps a checked term
def Tm.wx(f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32, +i: U32, +x: C.Cir.Cell, -t: C.Term, +hi: {False{} == D.Al(K, F, X, N, i) : Bool},
  +h: {D.Tm(f, m, ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, C.Term>}) ->
  {D.Tm(f, C.Cir.Cells.set(m, i, x), ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, C.Term>}:
  match f:
    case 0n:
      Mb.ns(C.Term, t, {D.Tm(0n, C.Cir.Cells.set(m, i, x), ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, C.Term>}, h)
    case 1n+(+p):
      +m2 = C.Cir.Cells.set(m, i, x)
      +cell = C.Cir.Cells.get(m, c)
      +ha = Tm.al.if(D.Al(K, F, X, N, c), p, m, ks, img, K, F, X, N, c, cell, t, {==}, h)
      +ne = Al.ne.if(U32.is_eq(c, i), K, F, X, N, c, i, {==}, ha, hi)
      %Equal.sym(C.Cir.Cell, C.Cir.Cells.get(m2, c), cell, K.Cl.get_ne(m, c, i, x, ne)) :
        {Tm.at(p, m2, ks, img, K, F, X, N, c, _) == Some{t} : Maybe<&2, C.Term>}
      Tm.at.cg(D.Al(K, F, X, N, c), p, p, m, m2, ks, img, K, F, X, N, X, N, D.Al(K, F, X, N, c), c, cell, t, {==}, h,
        a => ha2 => Tm.wx(p, m, ks, img, K, F, X, N, C.Cir.Cell.get(2n, cell), i, x, a, hi, ha2),
        a => ha3 => Tm.wx(p, m, ks, img, K, F, X, N, C.Cir.Cell.get(3n, cell), i, x, a, hi, ha3),
        a => ha4 => Tm.wx(p, m, ks, img, K, F, X, N, C.Cir.Cell.get(4n, cell), i, x, a, hi, ha4))

# a count's write leaves the cell's term the same
def Tm.at.s1(+f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32, cl: C.Cir.Cell, +v: U32) ->
  {Tm.at(f, m, ks, img, K, F, X, N, c, cl) == Tm.at(f, m, ks, img, K, F, X, N, c, C.Cir.Cell.set(1n, cl, v)) : Maybe<&2, C.Term>}:
  match cl:
    case C.Cir.Cell{+a, +b, +x, +y, +z}:
      {==}

# the cell c after a write of the count of i: c's cell, or i's with another count
def Tm.w1.cell(b: Bool, +f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32, +i: U32, +v: U32, eb: {b == U32.is_eq(c, i) : Bool}) ->
  {Tm.at(f, C.Cir.Cells.set(m, i, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, i), v)), ks, img, K, F, X, N, c, C.Cir.Cells.get(m, c)) ==
    Tm.at(f, C.Cir.Cells.set(m, i, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, i), v)), ks, img, K, F, X, N, c,
      C.Cir.Cells.get(C.Cir.Cells.set(m, i, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, i), v)), c)) : Maybe<&2, C.Term>}:
  match b:
    case True{}:
      +m2 = C.Cir.Cells.set(m, i, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, i), v))
      +e = K.U.eq(c, i, Equal.sym(Bool, True{}, U32.is_eq(c, i), eb))
      %Equal.sym(U32, c, i, e) : {Tm.at(f, m2, ks, img, K, F, X, N, c, C.Cir.Cells.get(m, _)) == Tm.at(f, m2, ks, img, K, F, X, N, c, C.Cir.Cells.get(m2, _)) : Maybe<&2, C.Term>}
      %Equal.sym(C.Cir.Cell, C.Cir.Cells.get(m2, i), C.Cir.Cell.set(1n, C.Cir.Cells.get(m, i), v), K.Cl.get_set(m, i, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, i), v))) :
        {Tm.at(f, m2, ks, img, K, F, X, N, c, C.Cir.Cells.get(m, i)) == Tm.at(f, m2, ks, img, K, F, X, N, c, _) : Maybe<&2, C.Term>}
      Tm.at.s1(f, m2, ks, img, K, F, X, N, c, C.Cir.Cells.get(m, i), v)
    case False{}:
      +m2 = C.Cir.Cells.set(m, i, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, i), v))
      %Equal.sym(C.Cir.Cell, C.Cir.Cells.get(m2, c), C.Cir.Cells.get(m, c), K.Cl.get_ne(m, c, i, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, i), v), Equal.sym(Bool, False{}, U32.is_eq(c, i), eb))) :
        {Tm.at(f, m2, ks, img, K, F, X, N, c, C.Cir.Cells.get(m, c)) == Tm.at(f, m2, ks, img, K, F, X, N, c, _) : Maybe<&2, C.Term>}
      {==}

# writing the count of any cell i keeps a checked term: no term reads it
def Tm.w1(f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32, +i: U32, +v: U32, -t: C.Term,
  +h: {D.Tm(f, m, ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, C.Term>}) ->
  {D.Tm(f, C.Cir.Cells.set(m, i, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, i), v)), ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, C.Term>}:
  match f:
    case 0n:
      Mb.ns(C.Term, t, {D.Tm(0n, C.Cir.Cells.set(m, i, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, i), v)), ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, C.Term>}, h)
    case 1n+(+p):
      +m2 = C.Cir.Cells.set(m, i, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, i), v))
      +cell = C.Cir.Cells.get(m, c)
      %Tm.w1.cell(U32.is_eq(c, i), p, m, ks, img, K, F, X, N, c, i, v, {==}) :
        {_ == Some{t} : Maybe<&2, C.Term>}
      Tm.at.cg(D.Al(K, F, X, N, c), p, p, m, m2, ks, img, K, F, X, N, X, N, D.Al(K, F, X, N, c), c, cell, t, {==}, h,
        a => ha2 => Tm.w1(p, m, ks, img, K, F, X, N, C.Cir.Cell.get(2n, cell), i, v, a, ha2),
        a => ha3 => Tm.w1(p, m, ks, img, K, F, X, N, C.Cir.Cell.get(3n, cell), i, v, a, ha3),
        a => ha4 => Tm.w1(p, m, ks, img, K, F, X, N, C.Cir.Cell.get(4n, cell), i, v, a, ha4))

# more fuel keeps a checked term
def Tm.lift(f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32, -t: C.Term, +h: {D.Tm(f, m, ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, C.Term>}) ->
  {D.Tm(1n+f, m, ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, C.Term>}:
  match f:
    case 0n:
      Mb.ns(C.Term, t, {D.Tm(1n, m, ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, C.Term>}, h)
    case 1n+(+p):
      +cell = C.Cir.Cells.get(m, c)
      Tm.at.cg(D.Al(K, F, X, N, c), p, 1n+p, m, m, ks, img, K, F, X, N, X, N, D.Al(K, F, X, N, c), c, cell, t, {==}, h,
        a => ha2 => Tm.lift(p, m, ks, img, K, F, X, N, C.Cir.Cell.get(2n, cell), a, ha2),
        a => ha3 => Tm.lift(p, m, ks, img, K, F, X, N, C.Cir.Cell.get(3n, cell), a, ha3),
        a => ha4 => Tm.lift(p, m, ks, img, K, F, X, N, C.Cir.Cell.get(4n, cell), a, ha4))

def Tm.chk.inv.ok(b: Bool, +a: C.Term, -t: C.Term, h: {D.Tm.ok(b, a) == Some{t} : Maybe<&2, C.Term>}) -> {Some{a} == Some{t} : Maybe<&2, C.Term>}:
  match b:
    case True{}:
      h
    case False{}:
      Mb.ns(C.Term, t, {Some{a} == Some{t} : Maybe<&2, C.Term>}, h)

# Tm.chk keeps only the terms that its part gives
def Tm.chk.inv(+tag: Nat, +fvf: U32, r: Maybe<&2, C.Term>, -t: C.Term, h: {D.Tm.chk(tag, fvf, r) == Some{t} : Maybe<&2, C.Term>}) ->
  {r == Some{t} : Maybe<&2, C.Term>}:
  match r:
    case None{}:
      Mb.ns(C.Term, t, {None{} == Some{t} : Maybe<&2, C.Term>}, h)
    case Some{+a}:
      Tm.chk.inv.ok(D.FvOK(tag, fvf, a), a, t, h)

# the cell's term by T.tm.of, at a cell that Tm reads, from parts that give what Tm gave
def Tm.of.at(b: Bool, +f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32, +cell: C.Cir.Cell, -t: C.Term,
  h: {Tm.at.b(b, f, m, ks, img, K, F, X, N, c, cell) == Some{t} : Maybe<&2, C.Term>},
  g2: Pt(u => D.Tm(f, m, ks, img, K, F, X, N, C.Cir.Cell.get(2n, cell)), u => T.tm.of(f, m, ks, img, C.Cir.Cell.get(2n, cell))),
  g3: Pt(u => D.Tm(f, m, ks, img, K, F, X, N, C.Cir.Cell.get(3n, cell)), u => T.tm.of(f, m, ks, img, C.Cir.Cell.get(3n, cell))),
  g4: Pt(u => D.Tm(f, m, ks, img, K, F, X, N, C.Cir.Cell.get(4n, cell)), u => T.tm.of(f, m, ks, img, C.Cir.Cell.get(4n, cell)))) ->
  {T.tm.cell(U32.to_nat(U32.and(C.Cir.Cell.get(0n, cell), 63)), T.tm.quan(U32.and(U32.shrn(C.Cir.Cell.get(0n, cell), 6n), 3)), c,
    C.Cir.Cell.get(2n, cell), ks, img, u => T.tm.of(f, m, ks, img, C.Cir.Cell.get(2n, cell)), u => T.tm.of(f, m, ks, img, C.Cir.Cell.get(3n, cell)),
    u => T.tm.of(f, m, ks, img, C.Cir.Cell.get(4n, cell))) == Some{t} : Maybe<&2, C.Term>}:
  match b:
    case False{}:
      +f0 = C.Cir.Cell.get(0n, cell)
      +tag = U32.to_nat(U32.and(f0, 63))
      +q = T.tm.quan(U32.and(U32.shrn(f0, 6n), 3))
      Mb.ns(C.Term, t, {T.tm.cell(tag, q, c, C.Cir.Cell.get(2n, cell), ks, img, u => T.tm.of(f, m, ks, img, C.Cir.Cell.get(2n, cell)),
        u => T.tm.of(f, m, ks, img, C.Cir.Cell.get(3n, cell)), u => T.tm.of(f, m, ks, img, C.Cir.Cell.get(4n, cell))) == Some{t} : Maybe<&2, C.Term>}, h)
    case True{}:
      +f0 = C.Cir.Cell.get(0n, cell)
      +tag = U32.to_nat(U32.and(f0, 63))
      +q = T.tm.quan(U32.and(U32.shrn(f0, 6n), 3))
      Cg(tag, q, c, C.Cir.Cell.get(2n, cell), ks, img,
        u => D.Tm(f, m, ks, img, K, F, X, N, C.Cir.Cell.get(2n, cell)), u => D.Tm(f, m, ks, img, K, F, X, N, C.Cir.Cell.get(3n, cell)),
        u => D.Tm(f, m, ks, img, K, F, X, N, C.Cir.Cell.get(4n, cell)),
        u => T.tm.of(f, m, ks, img, C.Cir.Cell.get(2n, cell)), u => T.tm.of(f, m, ks, img, C.Cir.Cell.get(3n, cell)),
        u => T.tm.of(f, m, ks, img, C.Cir.Cell.get(4n, cell)), t,
        Tm.chk.inv(tag, U32.shrn(f0, 13n), T.tm.cell(tag, q, c, C.Cir.Cell.get(2n, cell), ks, img,
          u => D.Tm(f, m, ks, img, K, F, X, N, C.Cir.Cell.get(2n, cell)), u => D.Tm(f, m, ks, img, K, F, X, N, C.Cir.Cell.get(3n, cell)),
          u => D.Tm(f, m, ks, img, K, F, X, N, C.Cir.Cell.get(4n, cell))), t, h), g2, g3, g4)

# a checked term is the cell's term by T.tm.of (proof_term.bend)
def Tm.of(f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32, -t: C.Term, +h: {D.Tm(f, m, ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, C.Term>}) ->
  {T.tm.of(f, m, ks, img, c) == Some{t} : Maybe<&2, C.Term>}:
  match f:
    case 0n:
      Mb.ns(C.Term, t, {T.tm.of(0n, m, ks, img, c) == Some{t} : Maybe<&2, C.Term>}, h)
    case 1n+(+p):
      +cell = C.Cir.Cells.get(m, c)
      Tm.of.at(D.Al(K, F, X, N, c), p, m, ks, img, K, F, X, N, c, cell, t, h,
        a => ha2 => Tm.of(p, m, ks, img, K, F, X, N, C.Cir.Cell.get(2n, cell), a, ha2),
        a => ha3 => Tm.of(p, m, ks, img, K, F, X, N, C.Cir.Cell.get(3n, cell), a, ha3),
        a => ha4 => Tm.of(p, m, ks, img, K, F, X, N, C.Cir.Cell.get(4n, cell), a, ha4))

# More cells that may be read
# ---------------------------

def Has.incl.if(b: Bool, +z: U32, rest: List<&2, U32>, +X: List<&2, U32>, +N: U32, +y: U32, +eb: {b == U32.is_eq(z, y) : Bool},
  +hz: {Bool.or(D.Has(X, z), U32.is_le(N, z)) == True{} : Bool},
  hr: {D.Has(rest, y) == True{} : Bool} -> {Bool.or(D.Has(X, y), U32.is_le(N, y)) == True{} : Bool},
  +hy: {Bool.or(b, D.Has(rest, y)) == True{} : Bool}) -> {Bool.or(D.Has(X, y), U32.is_le(N, y)) == True{} : Bool}:
  match b:
    case True{}:
      +e = K.U.eq(z, y, Equal.sym(Bool, True{}, U32.is_eq(z, y), eb))
      %e : {Bool.or(D.Has(X, _), U32.is_le(N, _)) == True{} : Bool}
      hz
    case False{}:
      hr(hy)

# a cell of X2 is one of X or from N on
def Has.incl(X2: List<&2, U32>, +X: List<&2, U32>, +N: U32, +y: U32, +hi: {D.Incl.go(X2, X, N) == True{} : Bool},
  +hy: {D.Has(X2, y) == True{} : Bool}) -> {Bool.or(D.Has(X, y), U32.is_le(N, y)) == True{} : Bool}:
  match X2:
    case Nil{}:
      K.Bo.tf({Bool.or(D.Has(X, y), U32.is_le(N, y)) == True{} : Bool}, hy)
    case Con{+z, +rest}:
      Has.incl.if(U32.is_eq(z, y), z, rest, X, N, y, {==},
        K.Bo.and_l(Bool.or(D.Has(X, z), U32.is_le(N, z)), D.Incl.go(rest, X, N), hi),
        k => Has.incl(rest, X, N, y, K.Bo.and_r(Bool.or(D.Has(X, z), U32.is_le(N, z)), D.Incl.go(rest, X, N), hi), k), hy)

def Al.incl.cell(b: Bool, +K: U32, +F: U32, +N: U32, +N2: U32, +x: U32, +eb: {b == Bool.and(Bool.not(U32.is_zero(x)), U32.is_le(x, K)) : Bool},
  +ic: {Bool.or(b, Bool.and(U32.is_le(F, x), U32.is_lt(x, N))) == True{} : Bool}, +hn: {U32.is_le(N, N2) == True{} : Bool}) ->
  {C.Cir.is_cell(x, K, F, N2) == True{} : Bool}:
  match b:
    case True{}:
      %eb : {Bool.or(_, Bool.and(U32.is_le(F, x), U32.is_lt(x, N2))) == True{} : Bool}
      {==}
    case False{}:
      %eb : {Bool.or(_, Bool.and(U32.is_le(F, x), U32.is_lt(x, N2))) == True{} : Bool}
      K.Bo.and_i(U32.is_le(F, x), U32.is_lt(x, N2), K.Bo.and_l(U32.is_le(F, x), U32.is_lt(x, N), ic),
        K.U.lt_le(x, N, N2, K.Bo.and_r(U32.is_le(F, x), U32.is_lt(x, N), ic), hn))

def Al.incl.has.c(c: Bool, +K: U32, +F: U32, +N: U32, +x: U32, +ec: {c == Bool.and(Bool.not(U32.is_zero(x)), U32.is_le(x, K)) : Bool},
  +ic: {Bool.or(c, Bool.and(U32.is_le(F, x), U32.is_lt(x, N))) == True{} : Bool}, +hkn: {U32.is_lt(K, N) == True{} : Bool},
  +le: {U32.is_le(N, x) == True{} : Bool}) -> {True{} == False{} : Bool}:
  match c:
    case True{}:
      +xk = K.Bo.and_r(Bool.not(U32.is_zero(x)), U32.is_le(x, K), Equal.sym(Bool, True{}, Bool.and(Bool.not(U32.is_zero(x)), U32.is_le(x, K)), ec))
      K.U.lt_ge(x, N, {True{} == False{} : Bool}, K.U.le_lt(x, K, N, xk, hkn), le)
    case False{}:
      K.U.lt_ge(x, N, {True{} == False{} : Bool}, K.Bo.and_r(U32.is_le(F, x), U32.is_lt(x, N), ic), le)

def Al.incl.has(b: Bool, c: Bool, +K: U32, +F: U32, +N: U32, +x: U32, +ec: {c == Bool.and(Bool.not(U32.is_zero(x)), U32.is_le(x, K)) : Bool},
  +ic: {Bool.or(c, Bool.and(U32.is_le(F, x), U32.is_lt(x, N))) == True{} : Bool}, +hkn: {U32.is_lt(K, N) == True{} : Bool},
  hnx: {b == True{} : Bool} -> {U32.is_le(N, x) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Al.incl.has.c(c, K, F, N, x, ec, ic, hkn, hnx({==}))

# a cell that may be read still may once more cells may be read
def Al.incl(+K: U32, +F: U32, +X: List<&2, U32>, +N: U32, +X2: List<&2, U32>, +N2: U32, +x: U32,
  +hin: {D.Incl(X, N, X2, N2) == True{} : Bool}, +hkn: {U32.is_lt(K, N) == True{} : Bool},
  +ha: {D.Al(K, F, X, N, x) == True{} : Bool}) -> {D.Al(K, F, X2, N2, x) == True{} : Bool}:
  +ic = K.Bo.and_l(C.Cir.is_cell(x, K, F, N), Bool.and(Bool.not(D.Has(X, x)), Bool.not(D.Tbc(x))), ha)
  +rest = K.Bo.and_r(C.Cir.is_cell(x, K, F, N), Bool.and(Bool.not(D.Has(X, x)), Bool.not(D.Tbc(x))), ha)
  +nh = K.Bo.not_t(D.Has(X, x), K.Bo.and_l(Bool.not(D.Has(X, x)), Bool.not(D.Tbc(x)), rest))
  +nt = K.Bo.and_r(Bool.not(D.Has(X, x)), Bool.not(D.Tbc(x)), rest)
  +hn = K.Bo.and_l(U32.is_le(N, N2), D.Incl.go(X2, X, N), hin)
  +hg = K.Bo.and_r(U32.is_le(N, N2), D.Incl.go(X2, X, N), hin)
  +b1 = Bool.and(Bool.not(U32.is_zero(x)), U32.is_le(x, K))
  +ic2 = Al.incl.cell(b1, K, F, N, N2, x, {==}, ic, hn)
  +nh2 = Al.incl.has(D.Has(X2, x), b1, K, F, N, x, {==}, ic, hkn,
    k => K.Bo.or_r(D.Has(X, x), U32.is_le(N, x), Has.incl(X2, X, N, x, hg, k), nh))
  K.Bo.and_i(C.Cir.is_cell(x, K, F, N2), Bool.and(Bool.not(D.Has(X2, x)), Bool.not(D.Tbc(x))), ic2,
    K.Bo.and_i(Bool.not(D.Has(X2, x)), Bool.not(D.Tbc(x)), K.Bo.not_i(D.Has(X2, x), nh2), nt))

# more cells that may be read keep a checked term
def Tm.mono(f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +X2: List<&2, U32>, +N2: U32, +c: U32, -t: C.Term,
  +hin: {D.Incl(X, N, X2, N2) == True{} : Bool}, +hkn: {U32.is_lt(K, N) == True{} : Bool},
  +h: {D.Tm(f, m, ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, C.Term>}) ->
  {D.Tm(f, m, ks, img, K, F, X2, N2, c) == Some{t} : Maybe<&2, C.Term>}:
  match f:
    case 0n:
      Mb.ns(C.Term, t, {D.Tm(0n, m, ks, img, K, F, X2, N2, c) == Some{t} : Maybe<&2, C.Term>}, h)
    case 1n+(+p):
      +cell = C.Cir.Cells.get(m, c)
      +ha = Tm.al.if(D.Al(K, F, X, N, c), p, m, ks, img, K, F, X, N, c, cell, t, {==}, h)
      +ha2 = Al.incl(K, F, X, N, X2, N2, c, hin, hkn, ha)
      Tm.at.cg(D.Al(K, F, X, N, c), p, p, m, m, ks, img, K, F, X, N, X2, N2, D.Al(K, F, X2, N2, c), c, cell, t,
        Equal.trans(Bool, D.Al(K, F, X, N, c), True{}, D.Al(K, F, X2, N2, c), ha, Equal.sym(Bool, D.Al(K, F, X2, N2, c), True{}, ha2)), h,
        a => k2 => Tm.mono(p, m, ks, img, K, F, X, N, X2, N2, C.Cir.Cell.get(2n, cell), a, hin, hkn, k2),
        a => k3 => Tm.mono(p, m, ks, img, K, F, X, N, X2, N2, C.Cir.Cell.get(3n, cell), a, hin, hkn, k3),
        a => k4 => Tm.mono(p, m, ks, img, K, F, X, N, X2, N2, C.Cir.Cell.get(4n, cell), a, hin, hkn, k4))
