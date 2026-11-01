# compiler: layer B, the swap moves
# =================================
#
# The moves of M.ret that swap the focus into the top frame (M.swap): App q □ a
# with q live and a not known (mv.ret.swap), Tup q □ b (mv.ret.tupb) and
# Min □ b (mv.ret.minb). The frame's cell sp gets a new header and the focus
# in field 2; its old field 2 becomes the focus, to evaluate. An admin move.
#
# The store to sp is one store (sw.mem): the cell {hd, y1, foc, y3, y4}. It
# keeps every term (a frame's tag is 32 or more: is.st), the rest of the
# frames (sp is not in the rest of its own chain, by the chain's length:
# Hops, frs.st), the image (ImgOK.fz: nothing points to a frame) and the heap:
# the pointer of sp's field 2 and the root trade places (Ptr.sw, Heap.sw).

import Base
import ./impl.bend as C
import ./proof_need.bend as N
import ./proof_mach_defs.bend as D
import ./proof_mach_exec.bend as X

# Kit
# ---

# Nat algebra (proof_sim_nat.bend's, copied)
def add.comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, N.add_zero(b))
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, b), Nat.add(b, p), add.comm(p, b)),
        Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), N.add_succ_r(b, p)))

def add.assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), add.assoc(p, b, c))

# (a + b) + c = (c + b) + a
def add.swap3(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(c, b), a) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(c, Nat.add(a, b)), Nat.add(Nat.add(c, b), a),
    add.comm(Nat.add(a, b), c),
    Equal.trans(Nat, Nat.add(c, Nat.add(a, b)), Nat.add(c, Nat.add(b, a)), Nat.add(Nat.add(c, b), a),
      Equal.cong(Nat, Nat, y => Nat.add(c, y), Nat.add(a, b), Nat.add(b, a), add.comm(a, b)),
      Equal.sym(Nat, Nat.add(Nat.add(c, b), a), Nat.add(c, Nat.add(b, a)), add.assoc(c, b, a))))

# the second of a pair
def p2.snd(-A: Data, -B: Data, p: D.P2(A, B)) -> B:
  match p:
    case Tuple{_, b}:
      b

# a number below another one as a U32 comparison (proof_copy_kit.bend's, copied)
def u.lt_t.of(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(1n+x, y)) -> {Cmp.is_lt(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(y, N.le_rw_l(1n+x, 1n+y, y, Equal.cong(Nat, Nat, z => 1n+z, x, y, r), h)))
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(y, N.le_trans(1n+y, x, y, r, N.weaken(x, y, h))))

def u.lt_t(+a: U32, +b: U32, h: N.Le(1n+U32.to_nat(a), U32.to_nat(b))) -> {U32.is_lt(a, b) == True{} : Bool}:
  u.lt_t.of(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), h)

# a cell past z is not z
def ne.lt.b(b: Bool, +o: U32, +z: U32, eb: {U32.is_eq(o, z) == b : Bool}, h: N.Le(1n+U32.to_nat(z), U32.to_nat(o))) ->
  {U32.is_eq(o, z) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +e = D.u32.eq(o, z, eb)
      Empty.absurd({U32.is_eq(o, z) == False{} : Bool},
        N.not_succ_le(U32.to_nat(z), (%e : N.Le(1n+U32.to_nat(z), U32.to_nat(_)); h)))

def ne.lt(+o: U32, +z: U32, h: N.Le(1n+U32.to_nat(z), U32.to_nat(o))) -> {U32.is_eq(o, z) == False{} : Bool}:
  ne.lt.b(U32.is_eq(o, z), o, z, {==}, h)

# a cell of a tag below 19 is not z, whose tag is 19 or more
def tg.ne.b(b: Bool, +m: C.Cir.Cells, +y: U32, +z: U32, eb: {U32.is_eq(y, z) == b : Bool},
  hy: {U32.is_lt(D.Tg(m, y), 19) == True{} : Bool}, hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}) ->
  {U32.is_eq(y, z) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +e = D.u32.eq(y, z, eb)
      +hz2 = {(%Equal.sym(U32, y, z, e) : {U32.is_lt(D.Tg(m, _), 19) == False{} : Bool}; hz) : {U32.is_lt(D.Tg(m, y), 19) == False{} : Bool}}
      D.bool.ft({U32.is_eq(y, z) == False{} : Bool},
        Equal.trans(Bool, False{}, U32.is_lt(D.Tg(m, y), 19), True{}, Equal.sym(Bool, U32.is_lt(D.Tg(m, y), 19), False{}, hz2), hy))

def tg.ne(+m: C.Cir.Cells, +y: U32, +z: U32, hy: {U32.is_lt(D.Tg(m, y), 19) == True{} : Bool},
  hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}) -> {U32.is_eq(y, z) == False{} : Bool}:
  tg.ne.b(U32.is_eq(y, z), m, y, z, {==}, hy, hz)

# A store that trades a pointer
# -----------------------------
#
# A store to the cell z, of the machine's own and of a tag of 19 or more,
# whose pointers go from [b] to [a], while the roots go from [a] to [b]: every
# count Ptr stays (Pc.mv, by induction on the cells from fi, with z among them
# once), and so does the heap (Heap.sw).

# a store to z keeps the pointers of the k cells from o, all past z and below nx
def Pc.out(k: Nat, +m: C.Cir.Cells, +z: U32, +x: C.Cir.Cell, +ps: List<&2, U32>, +o: U32, +c: U32, +nx: U32,
  hz: N.Le(1n+U32.to_nat(z), U32.to_nat(o)), hb: N.Le(Nat.add(U32.to_nat(o), k), U32.to_nat(nx)),
  ht: {D.TblR(k, m, o, z) == True{} : Bool}) ->
  {D.Pc(k, C.Cir.Cells.set(m, z, x), ps, o, c) == D.Pc(k, m, ps, o, c) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +M2 = C.Cir.Cells.set(m, z, x)
      +ht2 = ht
      +hz2 = hz
      +hb2 = hb
      +lt1 = N.le_trans(1n+U32.to_nat(o), Nat.add(U32.to_nat(o), 1n+j), U32.to_nat(nx), N.lt_add(U32.to_nat(o), j), hb2)
      +ei = D.u.inc(o, nx, lt1)
      +hzi = N.le_rw_r(1n+U32.to_nat(z), 1n+U32.to_nat(o), U32.to_nat(U32.inc(o)),
        Equal.sym(Nat, U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei), N.le_succ(1n+U32.to_nat(z), U32.to_nat(o), hz2))
      +hbi = N.le_rw_l(Nat.add(U32.to_nat(o), 1n+j), Nat.add(U32.to_nat(U32.inc(o)), j), U32.to_nat(nx),
        Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+j), 1n+Nat.add(U32.to_nat(o), j), Nat.add(U32.to_nat(U32.inc(o)), j),
          N.add_succ_r(U32.to_nat(o), j),
          Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(o)), j), 1n+Nat.add(U32.to_nat(o), j),
            Equal.cong(Nat, Nat, y => Nat.add(y, j), U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei))), hb2)
      +e1 = D.fs.eq(m, z, x, ps, o, ne.lt(o, z, hz2), D.and.l(D.TblAt(m, o, z), D.TblR(j, m, U32.inc(o), z), ht2))
      +e2 = Pc.out(j, m, z, x, ps, U32.inc(o), c, nx, hzi, hbi, D.and.r(D.TblAt(m, o, z), D.TblR(j, m, U32.inc(o), z), ht2))
      %Equal.sym(List<&2, U32>, D.Fs(M2, ps, o), D.Fs(m, ps, o), e1) :
        {Nat.add(D.RcL(_, c), D.Pc(j, M2, ps, U32.inc(o), c)) == Nat.add(D.RcL(D.Fs(m, ps, o), c), D.Pc(j, m, ps, U32.inc(o), c)) : Nat}
      %Equal.sym(Nat, D.Pc(j, M2, ps, U32.inc(o), c), D.Pc(j, m, ps, U32.inc(o), c), e2) :
        {Nat.add(D.RcL(D.Fs(m, ps, o), c), _) == Nat.add(D.RcL(D.Fs(m, ps, o), c), D.Pc(j, m, ps, U32.inc(o), c)) : Nat}
      {==}

# the step of Pc.mv: o is z, or z is past o
def Pc.mv.b(bb: Bool, +j: Nat, +m: C.Cir.Cells, +z: U32, +x: C.Cir.Cell, +ps: List<&2, U32>, +o: U32, +c: U32, +nx: U32,
  +eb: {U32.is_eq(o, z) == bb : Bool}, +h1: N.Le(U32.to_nat(o), U32.to_nat(z)),
  +h2: N.Le(1n+U32.to_nat(z), Nat.add(U32.to_nat(o), 1n+j)), +hb: N.Le(Nat.add(U32.to_nat(o), 1n+j), U32.to_nat(nx)),
  +ht: {D.TblR(1n+j, m, o, z) == True{} : Bool},
  ih: N.Le(U32.to_nat(U32.inc(o)), U32.to_nat(z)) -> N.Le(1n+U32.to_nat(z), Nat.add(U32.to_nat(U32.inc(o)), j)) ->
    N.Le(Nat.add(U32.to_nat(U32.inc(o)), j), U32.to_nat(nx)) -> {D.TblR(j, m, U32.inc(o), z) == True{} : Bool} ->
    {Nat.add(D.Pc(j, C.Cir.Cells.set(m, z, x), ps, U32.inc(o), c), D.RcL(D.Fs(m, ps, z), c)) ==
      Nat.add(D.Pc(j, m, ps, U32.inc(o), c), D.RcL(D.Fs(C.Cir.Cells.set(m, z, x), ps, z), c)) : Nat}) ->
  {Nat.add(D.Pc(1n+j, C.Cir.Cells.set(m, z, x), ps, o, c), D.RcL(D.Fs(m, ps, z), c)) ==
    Nat.add(D.Pc(1n+j, m, ps, o, c), D.RcL(D.Fs(C.Cir.Cells.set(m, z, x), ps, z), c)) : Nat}:
  match bb:
    case True{}:
      +M2 = C.Cir.Cells.set(m, z, x)
      +R0 = D.RcL(D.Fs(m, ps, z), c)
      +R1 = D.RcL(D.Fs(M2, ps, z), c)
      +eadd = Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+j), 1n+Nat.add(U32.to_nat(o), j), Nat.add(1n+U32.to_nat(o), j),
        N.add_succ_r(U32.to_nat(o), j), {==})
      +eo = D.u32.eq(o, z, eb)
      +lt1 = N.le_trans(1n+U32.to_nat(o), Nat.add(U32.to_nat(o), 1n+j), U32.to_nat(nx), N.lt_add(U32.to_nat(o), j), hb)
      +ei = D.u.inc(o, nx, lt1)
      +hzo = {(%eo : N.Le(1n+U32.to_nat(_), U32.to_nat(U32.inc(o)));
        N.le_rw_r(1n+U32.to_nat(o), 1n+U32.to_nat(o), U32.to_nat(U32.inc(o)), Equal.sym(Nat, U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei),
          N.le_refl(1n+U32.to_nat(o)))) : N.Le(1n+U32.to_nat(z), U32.to_nat(U32.inc(o)))}
      +hbi = N.le_rw_l(Nat.add(U32.to_nat(o), 1n+j), Nat.add(U32.to_nat(U32.inc(o)), j), U32.to_nat(nx),
        Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+j), Nat.add(1n+U32.to_nat(o), j), Nat.add(U32.to_nat(U32.inc(o)), j), eadd,
          Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(o)), j), Nat.add(1n+U32.to_nat(o), j),
            Equal.cong(Nat, Nat, y => Nat.add(y, j), U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei))), hb)
      +e2 = Pc.out(j, m, z, x, ps, U32.inc(o), c, nx, hzo, hbi, D.and.r(D.TblAt(m, o, z), D.TblR(j, m, U32.inc(o), z), ht))
      %Equal.sym(U32, o, z, eo) :
        {Nat.add(Nat.add(D.RcL(D.Fs(M2, ps, _), c), D.Pc(j, M2, ps, U32.inc(o), c)), R0) ==
          Nat.add(Nat.add(D.RcL(D.Fs(m, ps, _), c), D.Pc(j, m, ps, U32.inc(o), c)), R1) : Nat}
      %Equal.sym(Nat, D.Pc(j, M2, ps, U32.inc(o), c), D.Pc(j, m, ps, U32.inc(o), c), e2) :
        {Nat.add(Nat.add(R1, _), R0) == Nat.add(Nat.add(R0, D.Pc(j, m, ps, U32.inc(o), c)), R1) : Nat}
      add.swap3(R1, D.Pc(j, m, ps, U32.inc(o), c), R0)
    case False{}:
      +M2 = C.Cir.Cells.set(m, z, x)
      +R0 = D.RcL(D.Fs(m, ps, z), c)
      +R1 = D.RcL(D.Fs(M2, ps, z), c)
      +eadd = Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+j), 1n+Nat.add(U32.to_nat(o), j), Nat.add(1n+U32.to_nat(o), j),
        N.add_succ_r(U32.to_nat(o), j), {==})
      +lt = D.lt.ne(U32.cmp(o, z), U32.to_nat(o), U32.to_nat(z), N.U32.rel(o, z), eb, h1)
      +ei = D.u.inc(o, z, lt)
      +ej = Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+j), Nat.add(1n+U32.to_nat(o), j), Nat.add(U32.to_nat(U32.inc(o)), j), eadd,
        Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(o)), j), Nat.add(1n+U32.to_nat(o), j),
          Equal.cong(Nat, Nat, y => Nat.add(y, j), U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei)))
      +h1b = N.le_rw_l(1n+U32.to_nat(o), U32.to_nat(U32.inc(o)), U32.to_nat(z), Equal.sym(Nat, U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei), lt)
      +h2b = N.le_rw_r(1n+U32.to_nat(z), Nat.add(U32.to_nat(o), 1n+j), Nat.add(U32.to_nat(U32.inc(o)), j), ej, h2)
      +hbb = N.le_rw_l(Nat.add(U32.to_nat(o), 1n+j), Nat.add(U32.to_nat(U32.inc(o)), j), U32.to_nat(nx), ej, hb)
      +e1 = D.fs.eq(m, z, x, ps, o, eb, D.and.l(D.TblAt(m, o, z), D.TblR(j, m, U32.inc(o), z), ht))
      +e2 = ih(h1b, h2b, hbb, D.and.r(D.TblAt(m, o, z), D.TblR(j, m, U32.inc(o), z), ht))
      +A = D.RcL(D.Fs(m, ps, o), c)
      +P1 = D.Pc(j, M2, ps, U32.inc(o), c)
      +P0 = D.Pc(j, m, ps, U32.inc(o), c)
      %Equal.sym(List<&2, U32>, D.Fs(M2, ps, o), D.Fs(m, ps, o), e1) :
        {Nat.add(Nat.add(D.RcL(_, c), P1), R0) == Nat.add(Nat.add(A, P0), R1) : Nat}
      Equal.trans(Nat, Nat.add(Nat.add(A, P1), R0), Nat.add(A, Nat.add(P1, R0)), Nat.add(Nat.add(A, P0), R1),
        add.assoc(A, P1, R0),
        Equal.trans(Nat, Nat.add(A, Nat.add(P1, R0)), Nat.add(A, Nat.add(P0, R1)), Nat.add(Nat.add(A, P0), R1),
          Equal.cong(Nat, Nat, y => Nat.add(A, y), Nat.add(P1, R0), Nat.add(P0, R1), e2),
          Equal.sym(Nat, Nat.add(Nat.add(A, P0), R1), Nat.add(A, Nat.add(P0, R1)), add.assoc(A, P0, R1))))

# a store to z, one of the k cells from o (below nx), trades z's pointers in Pc
def Pc.mv(k: Nat, +m: C.Cir.Cells, +z: U32, +x: C.Cir.Cell, +ps: List<&2, U32>, +o: U32, +c: U32, +nx: U32,
  h1: N.Le(U32.to_nat(o), U32.to_nat(z)), h2: N.Le(1n+U32.to_nat(z), Nat.add(U32.to_nat(o), k)),
  hb: N.Le(Nat.add(U32.to_nat(o), k), U32.to_nat(nx)), ht: {D.TblR(k, m, o, z) == True{} : Bool}) ->
  {Nat.add(D.Pc(k, C.Cir.Cells.set(m, z, x), ps, o, c), D.RcL(D.Fs(m, ps, z), c)) ==
    Nat.add(D.Pc(k, m, ps, o, c), D.RcL(D.Fs(C.Cir.Cells.set(m, z, x), ps, z), c)) : Nat}:
  match k:
    case 0n:
      Empty.absurd({Nat.add(0n, D.RcL(D.Fs(m, ps, z), c)) == Nat.add(0n, D.RcL(D.Fs(C.Cir.Cells.set(m, z, x), ps, z), c)) : Nat},
        N.not_succ_le(U32.to_nat(z), N.le_trans(1n+U32.to_nat(z), U32.to_nat(o), U32.to_nat(z),
          N.le_rw_r(1n+U32.to_nat(z), Nat.add(U32.to_nat(o), 0n), U32.to_nat(o), N.add_zero(U32.to_nat(o)), h2), h1)))
    case 1n+(+j):
      Pc.mv.b(U32.is_eq(o, z), j, m, z, x, ps, o, c, nx, {==}, h1, h2, hb, ht,
        a => b => d => e => Pc.mv(j, m, z, x, ps, U32.inc(o), c, nx, a, b, d, e))

# the counts, with the roots [a] and then [b]
def Ptr.sw(+m: C.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +z: U32, +x: C.Cir.Cell, +a: U32, +b: U32, +c: U32,
  hf0: {D.Fs(m, ps, z) == [b] : List<&2, U32>}, hf1: {D.Fs(C.Cir.Cells.set(m, z, x), ps, z) == [a] : List<&2, U32>},
  hzo: {D.Own(fi, nx, z) == True{} : Bool}, ht: {D.TblR(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, z) == True{} : Bool}) ->
  {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), C.Cir.Cells.set(m, z, x), fi, ps, [b], c) ==
    D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, [a], c) : Nat}:
  +o2 = hzo
  +M2 = C.Cir.Cells.set(m, z, x)
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +h1 = D.u.le(fi, z, D.and.l(U32.is_le(fi, z), U32.is_lt(z, nx), o2))
  +hl = D.u.lt(z, nx, D.and.r(U32.is_le(fi, z), U32.is_lt(z, nx), o2))
  +es = D.add.sub(U32.to_nat(fi), U32.to_nat(nx), N.le_trans(U32.to_nat(fi), U32.to_nat(z), U32.to_nat(nx), h1, N.weaken(U32.to_nat(z), U32.to_nat(nx), hl)))
  +es2 = Equal.sym(Nat, Nat.add(U32.to_nat(fi), n), U32.to_nat(nx), es)
  +h2 = N.le_rw_r(1n+U32.to_nat(z), U32.to_nat(nx), Nat.add(U32.to_nat(fi), n), es2, hl)
  +hb = N.le_rw_l(U32.to_nat(nx), Nat.add(U32.to_nat(fi), n), U32.to_nat(nx), es2, N.le_refl(U32.to_nat(nx)))
  %hf0 : {Nat.add(D.Pc(n, M2, ps, fi, c), D.RcL(_, c)) == Nat.add(D.Pc(n, m, ps, fi, c), D.RcL([a], c)) : Nat}
  %hf1 : {Nat.add(D.Pc(n, M2, ps, fi, c), D.RcL(D.Fs(m, ps, z), c)) == Nat.add(D.Pc(n, m, ps, fi, c), D.RcL(_, c)) : Nat}
  Pc.mv(n, m, z, x, ps, fi, c, nx, h1, h2, hb, ht)

# Cnt at the cell o, after the store, from Cnt before it
def cnt.sw.at(b: Bool, +m: C.Cir.Cells, +z: U32, +x: C.Cir.Cell, +o: U32, +n: Nat, +fi: U32, +ps: List<&2, U32>,
  +rs1: List<&2, U32>, +rs2: List<&2, U32>, eb: {U32.is_eq(o, z) == b : Bool},
  hxt: {U32.is_lt(D.TgW(C.Cir.Cell.get(0n, x)), 19) == False{} : Bool},
  hP: {D.Ptr(n, C.Cir.Cells.set(m, z, x), fi, ps, rs2, o) == D.Ptr(n, m, fi, ps, rs1, o) : Nat},
  h: {D.CntC(C.Cir.Cells.get(m, o), D.Ptr(n, m, fi, ps, rs1, o), ps, o) == True{} : Bool}) ->
  {D.CntC(C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), o), D.Ptr(n, C.Cir.Cells.set(m, z, x), fi, ps, rs2, o), ps, o) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(U32, o, z, D.u32.eq(o, z, eb)) :
        {D.CntC(C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), _), D.Ptr(n, C.Cir.Cells.set(m, z, x), fi, ps, rs2, _), ps, _) == True{} : Bool}
      %Equal.sym(C.Cir.Cell, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), z), x, D.cl.gs(m, z, x)) :
        {D.CntC(_, D.Ptr(n, C.Cir.Cells.set(m, z, x), fi, ps, rs2, z), ps, z) == True{} : Bool}
      D.or.l(Bool.not(U32.is_lt(D.TgW(C.Cir.Cell.get(0n, x)), 19)), Bool.or(D.FlW(C.Cir.Cell.get(0n, x), 1024), Bool.or(D.Mem(ps, z),
        Nat.is_eq(U32.to_nat(C.Cir.Cell.get(1n, x)), D.Ptr(n, C.Cir.Cells.set(m, z, x), fi, ps, rs2, z)))),
        (%Equal.sym(Bool, U32.is_lt(D.TgW(C.Cir.Cell.get(0n, x)), 19), False{}, hxt) : {Bool.not(_) == True{} : Bool}; {==}))
    case False{}:
      %Equal.sym(C.Cir.Cell, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), o), C.Cir.Cells.get(m, o), D.cl.go(m, o, z, x, eb)) :
        {D.CntC(_, D.Ptr(n, C.Cir.Cells.set(m, z, x), fi, ps, rs2, o), ps, o) == True{} : Bool}
      %Equal.sym(Nat, D.Ptr(n, C.Cir.Cells.set(m, z, x), fi, ps, rs2, o), D.Ptr(n, m, fi, ps, rs1, o), hP) :
        {D.CntC(C.Cir.Cells.get(m, o), _, ps, o) == True{} : Bool}
      h

# the counts of k cells from o, after the store
def Cnt.sw(k: Nat, +m: C.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +z: U32, +x: C.Cir.Cell, +a: U32, +b: U32, +o: U32,
  +hf0: {D.Fs(m, ps, z) == [b] : List<&2, U32>}, +hf1: {D.Fs(C.Cir.Cells.set(m, z, x), ps, z) == [a] : List<&2, U32>},
  +hzo: {D.Own(fi, nx, z) == True{} : Bool}, +ht: {D.TblR(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, z) == True{} : Bool},
  +hxt: {U32.is_lt(D.TgW(C.Cir.Cell.get(0n, x)), 19) == False{} : Bool},
  h: {D.Cnt(k, m, o, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, ps, [a]) == True{} : Bool}) ->
  {D.Cnt(k, C.Cir.Cells.set(m, z, x), o, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, ps, [b]) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +M2 = C.Cir.Cells.set(m, z, x)
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +h2 = h
      D.and.i(D.CntC(C.Cir.Cells.get(M2, o), D.Ptr(n, M2, fi, ps, [b], o), ps, o), D.Cnt(j, M2, U32.inc(o), n, fi, ps, [b]),
        cnt.sw.at(U32.is_eq(o, z), m, z, x, o, n, fi, ps, [a], [b], {==}, hxt, Ptr.sw(m, nx, fi, ps, z, x, a, b, o, hf0, hf1, hzo, ht),
          D.and.l(D.CntC(C.Cir.Cells.get(m, o), D.Ptr(n, m, fi, ps, [a], o), ps, o), D.Cnt(j, m, U32.inc(o), n, fi, ps, [a]), h2)),
        Cnt.sw(j, m, nx, fi, ps, z, x, a, b, U32.inc(o), hf0, hf1, hzo, ht, hxt,
          D.and.r(D.CntC(C.Cir.Cells.get(m, o), D.Ptr(n, m, fi, ps, [a], o), ps, o), D.Cnt(j, m, U32.inc(o), n, fi, ps, [a]), h2)))

# the pend list's cells, none of them z, after the store
def PendOK.sw(qs: List<&2, U32>, +ps: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +z: U32, +x: C.Cir.Cell, +a: U32, +b: U32,
  +hf0: {D.Fs(m, ps, z) == [b] : List<&2, U32>}, +hf1: {D.Fs(C.Cir.Cells.set(m, z, x), ps, z) == [a] : List<&2, U32>},
  +hzo: {D.Own(fi, nx, z) == True{} : Bool}, +ht: {D.TblR(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, z) == True{} : Bool},
  hq: {D.Mem(qs, z) == False{} : Bool}, h: D.PendOK(qs, ps, m, fi, nx, [a])) -> D.PendOK(qs, ps, C.Cir.Cells.set(m, z, x), fi, nx, [b]):
  match qs:
    case Nil{}:
      Unit{}
    case Con{+p, +rest}:
      (ho, r1) = h
      (hs, r2) = r1
      (htg, r3) = r2
      (hp0, r4) = r3
      +M2 = C.Cir.Cells.set(m, z, x)
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +hq2 = hq
      +ne = D.or.f.l(U32.is_eq(p, z), D.Mem(rest, z), hq2)
      +ec = D.cl.go(m, p, z, x, ne)
      (ho, ((%Equal.sym(C.Cir.Cell, C.Cir.Cells.get(M2, p), C.Cir.Cells.get(m, p), ec) :
          {U32.is_ne(U32.and(C.Cir.Cell.get(0n, _), 1024), 0) == False{} : Bool}; hs),
        ((%Equal.sym(C.Cir.Cell, C.Cir.Cells.get(M2, p), C.Cir.Cells.get(m, p), ec) :
          {Bool.or(U32.is_lt(U32.and(C.Cir.Cell.get(0n, _), 63), 19), U32.is_le(32, U32.and(C.Cir.Cell.get(0n, _), 63))) == True{} : Bool}; htg),
        ((%Equal.sym(Nat, D.Ptr(n, M2, fi, ps, [b], p), D.Ptr(n, m, fi, ps, [a], p), Ptr.sw(m, nx, fi, ps, z, x, a, b, p, hf0, hf1, hzo, ht)) :
            {_ == 0n : Nat}; hp0),
          PendOK.sw(rest, ps, m, nx, fi, z, x, a, b, hf0, hf1, hzo, ht, D.or.f.r(U32.is_eq(p, z), D.Mem(rest, z), hq2), r4)))))

# no pointer of xs, to a term cell, is z, whose tag is 19 or more
def rcl.none(xs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +z: U32, +hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool},
  h: {D.Lt.all(xs, m, nx) == True{} : Bool}) -> {D.RcL(xs, z) == 0n : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +h2 = h
      +hy = D.and.l(Bool.and(U32.is_lt(y, nx), U32.is_lt(D.Tg(m, y), 19)), D.Lt.all(rest, m, nx), h2)
      +ne = tg.ne(m, y, z, D.and.r(U32.is_lt(y, nx), U32.is_lt(D.Tg(m, y), 19), hy), hz)
      %Equal.sym(Bool, U32.is_eq(y, z), False{}, ne) : {Nat.add(D.Nat.of(_), D.RcL(rest, z)) == 0n : Nat}
      rcl.none(rest, m, nx, z, hz, D.and.r(Bool.and(U32.is_lt(y, nx), U32.is_lt(D.Tg(m, y), 19)), D.Lt.all(rest, m, nx), h2))

# no cell points to z, whose tag is 19 or more
def pc.none(k: Nat, +m: C.Cir.Cells, +ps: List<&2, U32>, +o: U32, +nx: U32, +z: U32,
  +hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, h: {D.Pts(k, m, ps, o, nx) == True{} : Bool}) ->
  {D.Pc(k, m, ps, o, z) == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +h2 = h
      %Equal.sym(Nat, D.RcL(D.Fs(m, ps, o), z), 0n,
        rcl.none(D.Fs(m, ps, o), m, nx, z, hz, D.and.l(D.Lt.all(D.Fs(m, ps, o), m, nx), D.Pts(j, m, ps, U32.inc(o), nx), h2))) :
        {Nat.add(_, D.Pc(j, m, ps, U32.inc(o), z)) == 0n : Nat}
      pc.none(j, m, ps, U32.inc(o), nx, z, hz, D.and.r(D.Lt.all(D.Fs(m, ps, o), m, nx), D.Pts(j, m, ps, U32.inc(o), nx), h2))

# the pointers xs, to term cells, after a store to z, whose tag is 19 or more
def lt.tg(xs: List<&2, U32>, +m: C.Cir.Cells, +z: U32, +x: C.Cir.Cell, +nx: U32, +hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool},
  h: {D.Lt.all(xs, m, nx) == True{} : Bool}) -> {D.Lt.all(xs, C.Cir.Cells.set(m, z, x), nx) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +M2 = C.Cir.Cells.set(m, z, x)
      +h2 = h
      +hy = D.and.l(Bool.and(U32.is_lt(y, nx), U32.is_lt(D.Tg(m, y), 19)), D.Lt.all(rest, m, nx), h2)
      +ne = tg.ne(m, y, z, D.and.r(U32.is_lt(y, nx), U32.is_lt(D.Tg(m, y), 19), hy), hz)
      %Equal.sym(C.Cir.Cell, C.Cir.Cells.get(M2, y), C.Cir.Cells.get(m, y), D.cl.go(m, y, z, x, ne)) :
        {Bool.and(Bool.and(U32.is_lt(y, nx), U32.is_lt(U32.and(C.Cir.Cell.get(0n, _), 63), 19)), D.Lt.all(rest, M2, nx)) == True{} : Bool}
      D.and.i(Bool.and(U32.is_lt(y, nx), U32.is_lt(D.Tg(m, y), 19)), D.Lt.all(rest, M2, nx), hy,
        lt.tg(rest, m, z, x, nx, hz, D.and.r(Bool.and(U32.is_lt(y, nx), U32.is_lt(D.Tg(m, y), 19)), D.Lt.all(rest, m, nx), h2)))

# the pointers of the cell o after the store: z's are [a]
def pts.sw.at(b: Bool, +m: C.Cir.Cells, +z: U32, +x: C.Cir.Cell, +ps: List<&2, U32>, +o: U32, +nx: U32, +a: U32,
  eb: {U32.is_eq(o, z) == b : Bool}, hf1: {D.Fs(C.Cir.Cells.set(m, z, x), ps, z) == [a] : List<&2, U32>},
  hal: {D.Lt.all([a], C.Cir.Cells.set(m, z, x), nx) == True{} : Bool}, ht: {D.TblAt(m, o, z) == True{} : Bool},
  hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, h: {D.Lt.all(D.Fs(m, ps, o), m, nx) == True{} : Bool}) ->
  {D.Lt.all(D.Fs(C.Cir.Cells.set(m, z, x), ps, o), C.Cir.Cells.set(m, z, x), nx) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(U32, o, z, D.u32.eq(o, z, eb)) : {D.Lt.all(D.Fs(C.Cir.Cells.set(m, z, x), ps, _), C.Cir.Cells.set(m, z, x), nx) == True{} : Bool}
      %Equal.sym(List<&2, U32>, D.Fs(C.Cir.Cells.set(m, z, x), ps, z), [a], hf1) : {D.Lt.all(_, C.Cir.Cells.set(m, z, x), nx) == True{} : Bool}
      hal
    case False{}:
      %Equal.sym(List<&2, U32>, D.Fs(C.Cir.Cells.set(m, z, x), ps, o), D.Fs(m, ps, o), D.fs.eq(m, z, x, ps, o, eb, ht)) :
        {D.Lt.all(_, C.Cir.Cells.set(m, z, x), nx) == True{} : Bool}
      lt.tg(D.Fs(m, ps, o), m, z, x, nx, hz, h)

# every pointer points to a term cell, after the store
def Pts.sw(k: Nat, +m: C.Cir.Cells, +z: U32, +x: C.Cir.Cell, +ps: List<&2, U32>, +o: U32, +nx: U32, +a: U32,
  +hf1: {D.Fs(C.Cir.Cells.set(m, z, x), ps, z) == [a] : List<&2, U32>}, +hal: {D.Lt.all([a], C.Cir.Cells.set(m, z, x), nx) == True{} : Bool},
  +hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, ht: {D.TblR(k, m, o, z) == True{} : Bool},
  h: {D.Pts(k, m, ps, o, nx) == True{} : Bool}) -> {D.Pts(k, C.Cir.Cells.set(m, z, x), ps, o, nx) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +M2 = C.Cir.Cells.set(m, z, x)
      +ht2 = ht
      +h2 = h
      D.and.i(D.Lt.all(D.Fs(M2, ps, o), M2, nx), D.Pts(j, M2, ps, U32.inc(o), nx),
        pts.sw.at(U32.is_eq(o, z), m, z, x, ps, o, nx, a, {==}, hf1, hal, D.and.l(D.TblAt(m, o, z), D.TblR(j, m, U32.inc(o), z), ht2), hz,
          D.and.l(D.Lt.all(D.Fs(m, ps, o), m, nx), D.Pts(j, m, ps, U32.inc(o), nx), h2)),
        Pts.sw(j, m, z, x, ps, U32.inc(o), nx, a, hf1, hal, hz, D.and.r(D.TblAt(m, o, z), D.TblR(j, m, U32.inc(o), z), ht2),
          D.and.r(D.Lt.all(D.Fs(m, ps, o), m, nx), D.Pts(j, m, ps, U32.inc(o), nx), h2)))

# the heap after the store: the pointer [b] of z and the root [a] trade places
def Heap.sw(+m: C.Cir.Cells, +nx: U32, +fi: U32, +pend: U32, +ps: List<&2, U32>, +z: U32, +x: C.Cir.Cell, +a: U32, +b: U32,
  +hf0: {D.Fs(m, ps, z) == [b] : List<&2, U32>}, +hf1: {D.Fs(C.Cir.Cells.set(m, z, x), ps, z) == [a] : List<&2, U32>},
  +hzo: {D.Own(fi, nx, z) == True{} : Bool}, +hz363: N.Le(1n+U32.to_nat(363), U32.to_nat(z)), +hzm: {D.Mem(ps, z) == False{} : Bool},
  +hzt: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, +hxt: {U32.is_lt(D.TgW(C.Cir.Cell.get(0n, x)), 19) == False{} : Bool},
  +hal: {D.Lt.all([a], C.Cir.Cells.set(m, z, x), nx) == True{} : Bool},
  h: D.Heap(m, nx, fi, [a], pend, ps)) -> D.Heap(C.Cir.Cells.set(m, z, x), nx, fi, [b], pend, ps):
  (hc, r1) = h
  (hp, r2) = r1
  (hcn, r3) = r2
  (hpt, hr) = r3
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +ht = D.TblR.of(n, m, fi, z, hz363)
  (D.Chain.fz(ps, m, z, x, pend, hzm, hc), (PendOK.sw(ps, ps, m, nx, fi, z, x, a, b, hf0, hf1, hzo, ht, hzm, hp),
    (Cnt.sw(n, m, nx, fi, ps, z, x, a, b, fi, hf0, hf1, hzo, ht, hxt, hcn),
    (Pts.sw(n, m, z, x, ps, fi, nx, a, hf1, hal, hzt, ht, hpt), hr))))

# no pointer to z, of a tag of 19 or more, from the cells or the root [a]
def ptr.none(+m: C.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +pend: U32, +a: U32, +z: U32,
  +hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, ha: {U32.is_lt(D.Tg(m, a), 19) == True{} : Bool},
  h: D.Heap(m, nx, fi, [a], pend, ps)) -> {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, [a], z) == 0n : Nat}:
  (hc, r1) = h
  (hp, r2) = r1
  (hcn, r3) = r2
  (hpt, hr) = r3
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  %Equal.sym(Nat, D.Pc(n, m, ps, fi, z), 0n, pc.none(n, m, ps, fi, nx, z, hz, hpt)) : {Nat.add(_, D.RcL([a], z)) == 0n : Nat}
  %Equal.sym(Bool, U32.is_eq(a, z), False{}, tg.ne(m, a, z, ha, hz)) : {Nat.add(0n, Nat.add(D.Nat.of(_), 0n)) == 0n : Nat}
  {==}
