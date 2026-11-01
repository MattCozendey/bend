# compiler: the walk of a copy
# ============================
#
# M.copy.walk keeps a stack of new cells (frames), each a copy of a source
# cell whose parts it copies in order: a part is done (its field holds the
# copy, a cell of Mo.F of the part's term under the frame's depth and the
# binders above the part), current (its field holds the frame above, which
# copies it), pending (its field still holds the source's part, a cell of
# its term), or no part of the tag. The top frame has no current part; each
# frame below it has one, the last part that is not pending. The walk's
# invariant (WI) holds of each round: the frames from the stack register,
# the cells that may be read (all but the garbage and the frames), the
# allocation's invariant, the roots and the kept cells, and a measure that
# bounds the rounds left and the counts that they add.

import Base
import ./impl.bend as C
import ./proof_term.bend as T
import ./proof_need.bend as N
import ./proof_copy.bend as D
import ./proof_copy_kit.bend as K

# The tags
# --------

# the field k (2, 3 or 4) of a cell of the tag tg is a part of its term
def Tg.u(tg: Nat, +k: Nat) -> Bool:
  match tg:
    case 2n:
      Bool.or(Nat.is_eq(k, 2n), Nat.is_eq(k, 3n))
    case 3n:
      Bool.or(Nat.is_eq(k, 2n), Nat.is_eq(k, 3n))
    case 4n:
      Nat.is_eq(k, 2n)
    case 5n:
      Bool.or(Nat.is_eq(k, 2n), Nat.is_eq(k, 3n))
    case 6n:
      Bool.or(Nat.is_eq(k, 2n), Nat.is_eq(k, 3n))
    case 7n:
      Nat.is_eq(k, 2n)
    case 8n:
      Bool.or(Nat.is_eq(k, 2n), Nat.is_eq(k, 3n))
    case 9n:
      Bool.or(Nat.is_eq(k, 2n), Nat.is_eq(k, 3n))
    case 10n:
      Bool.or(Nat.is_eq(k, 2n), Nat.is_eq(k, 3n))
    case 11n:
      Nat.is_eq(k, 2n)
    case 14n:
      Bool.or(Nat.is_eq(k, 3n), Nat.is_eq(k, 4n))
    case 16n:
      Bool.or(Nat.is_eq(k, 2n), Bool.or(Nat.is_eq(k, 3n), Nat.is_eq(k, 4n)))
    case 18n:
      Bool.or(Nat.is_eq(k, 2n), Bool.or(Nat.is_eq(k, 3n), Nat.is_eq(k, 4n)))
    case _:
      False{}

# the binders above the field k of a cell of the tag tg
def Tg.b(tg: Nat, +k: Nat) -> Nat:
  match tg:
    case 3n:
      Bool.pick(Nat, Nat.is_eq(k, 3n), 1n, 0n)
    case 6n:
      Bool.pick(Nat, Nat.is_eq(k, 3n), 1n, 0n)
    case 7n:
      Bool.pick(Nat, Nat.is_eq(k, 2n), 1n, 0n)
    case 9n:
      Bool.pick(Nat, Nat.is_eq(k, 3n), 1n, 0n)
    case 18n:
      Bool.pick(Nat, Nat.is_eq(k, 3n), 2n, 0n)
    case _:
      0n

# a tag that a walk copies: a term's, but no Var, Ref or Enu (which it never
# pushes)
def Tg.ok(+tg: Nat) -> Bool:
  match tg:
    case 0n:
      False{}
    case 1n:
      False{}
    case 12n:
      False{}
    case _:
      Nat.is_le(tg, 18n)

# The frames
# ----------

type St is Data:
  St.un{}
  St.pe{}
  St.dn{}
  St.cu{}

# a frame: the new cell n, the low byte h of its header (its tag and
# quantity), its source's field 2 x2 (a name, for Lab and Mat) and source
# term T, the cells x and terms t of the source's parts, their statuses, and
# its depth d
type Fr is Data:
  Fr{n: U32, h: U32, x2: U32, T: C.Term, y2: U32, y3: U32, y4: U32, t2: C.Term, t3: C.Term, t4: C.Term,
    s2: St, s3: St, s4: St, d: Nat}

# what the copy needs of a part's term: a shift's variables fit it
def MoOK(+mo: D.Mo, t: C.Term) -> Bool:
  match mo:
    case D.Mo.shift{a}:
      D.Fit(t, U32.from_nat(a))
    case D.Mo.subst{_}:
      True{}

# the field v of a frame, of the part of status s: the source's cell x, or
# its copy, of Mo.F(mo, t, dd), or the frame above (cn, of the source term
# cT, at the depth cd)
def FS(+mo: D.Mo, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +v: U32, +x: U32, +t: C.Term, s: St, +dd: Nat, +cn: U32, +cT: C.Term, +cd: Nat) -> Data:
  match s:
    case St.un{}:
      {v == x : U32}
    case St.pe{}:
      D.P2({v == x : U32}, D.P2(D.Ex(Nat, g => {D.Tm(g, m, ks, img, K, F, X, N, x) == Some{t} : Maybe<&2, C.Term>}),
        {MoOK(mo, t) == True{} : Bool}))
    case St.dn{}:
      D.Ex(Nat, g => {D.Tm(g, m, ks, img, K, F, X, N, v) == Some{D.Mo.F(mo, t, dd)} : Maybe<&2, C.Term>})
    case St.cu{}:
      D.P2({v == cn : U32}, D.P2({cT == t : C.Term}, {cd == dd : Nat}))

def St.is_pe(s: St) -> Bool:
  match s:
    case St.pe{}:
      True{}
    case _:
      False{}

# the bit of the todo bits for a pending part of field k (M.todo.bit)
def Bit(+s: St, +b: U32) -> U32:
  Bool.pick(U32, St.is_pe(s), b, 0)

# some part is pending
def HasPe(+s2: St, +s3: St, +s4: St) -> Bool:
  Bool.or(St.is_pe(s2), Bool.or(St.is_pe(s3), St.is_pe(s4)))

# the todo bits of a frame, from bit 8 (bits 0 to 2 here)
def Todo(+s2: St, +s3: St, +s4: St) -> U32:
  U32.or(Bit(s2, 1), U32.or(Bit(s3, 2), Bit(s4, 4)))

# the statuses of the parts: un for the fields that are no part of the tag; in
# order, done parts, then (below the top) one current part, then pending ones
def Ph(s: St) -> Nat:
  match s:
    case St.un{}:
      0n
    case St.dn{}:
      1n
    case St.cu{}:
      2n
    case St.pe{}:
      3n

def Ph.cu(s: St) -> Nat:
  match s:
    case St.cu{}:
      1n
    case _:
      0n

def St.is_un(s: St) -> Bool:
  match s:
    case St.un{}:
      True{}
    case _:
      False{}

def Bo.eq(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

# the phases of the used parts are in order: a field that is no part is skipped
def SOK.go(s: St, +p: Nat) -> Nat:
  match s:
    case St.un{}:
      p
    case _:
      Ph(s)

def SOK(+tg: Nat, +top: Bool, +s2: St, +s3: St, +s4: St) -> Bool:
  +p2 = SOK.go(s2, 1n)
  +p3 = SOK.go(s3, p2)
  +p4 = SOK.go(s4, p3)
  Bool.and(Bool.and(Bool.and(Bo.eq(Tg.u(tg, 2n), Bool.not(St.is_un(s2))),
    Bo.eq(Tg.u(tg, 3n), Bool.not(St.is_un(s3)))), Bo.eq(Tg.u(tg, 4n), Bool.not(St.is_un(s4)))),
  Bool.and(Bool.and(Nat.is_le(p2, p3), Nat.is_le(p3, p4)),
    Nat.is_eq(Nat.add(Ph.cu(s2), Nat.add(Ph.cu(s3), Ph.cu(s4))), Bool.pick(Nat, top, 0n, 1n))))

# the tag of the header byte h
def Fr.tag(+h: U32) -> Nat:
  U32.to_nat(U32.and(h, 63))

# the source term of a frame: of its tag and quantity, the name in field 2,
# and the terms of its parts
def Fr.src(+h: U32, +n: U32, +y2: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +t2: C.Term, +t3: C.Term,
  +t4: C.Term) -> Maybe<&2, C.Term>:
  T.tm.cell(Fr.tag(h), T.tm.quan(U32.and(U32.shrn(h, 6n), 3)), n, y2, ks, img, u => Some{t2}, u => Some{t3}, u => Some{t4})

# the frame fr, the top one (top) or below the frame (cn, cT, cd): its cell
# holds the header h with the todo bits of its pending parts, and its parts
# by their statuses; it is one of the machine's own cells, which may not be
# read (one of X), with a tag that the walk copies
def FrOK(+mo: D.Mo, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, fr: Fr, +top: Bool, +cn: U32, +cT: C.Term, +cd: Nat) -> Data:
  match fr:
    case Fr{+n, +h, +x2, +T0, +y2, +y3, +y4, +t2, +t3, +t4, +s2, +s3, +s4, +d}:
      +tg = Fr.tag(h)
      D.P2({D.Fd(0n, m, n) == U32.or(h, U32.shln(Todo(s2, s3, s4), 8n)) : U32},
      D.P2(FS(mo, m, ks, img, K, F, X, N, D.Fd(2n, m, n), y2, t2, s2, Nat.add(d, Tg.b(tg, 2n)), cn, cT, cd),
      D.P2(FS(mo, m, ks, img, K, F, X, N, D.Fd(3n, m, n), y3, t3, s3, Nat.add(d, Tg.b(tg, 3n)), cn, cT, cd),
      D.P2(FS(mo, m, ks, img, K, F, X, N, D.Fd(4n, m, n), y4, t4, s4, Nat.add(d, Tg.b(tg, 4n)), cn, cT, cd),
      D.P2({SOK(tg, top, s2, s3, s4) == True{} : Bool},
      D.P2({Tg.ok(tg) == True{} : Bool},
      D.P2({U32.and(h, 255) == h : U32},
      D.P2({x2 == y2 : U32},
      D.P2({Fr.src(h, n, y2, ks, img, t2, t3, t4) == Some{T0} : Maybe<&2, C.Term>},
      D.P2({C.Cir.is_cell(n, K, F, N) == True{} : Bool},
      D.P2({U32.is_le(F, n) == True{} : Bool},
        {D.Has(X, n) == True{} : Bool})))))))))))

# the frames frs, from the cell at on, linked by field 1, the top first (top),
# each below the one before (cn, cT, cd); 0 after the last
def Frs(+mo: D.Mo, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, frs: List<&2, Fr>, +at: U32, +top: Bool, +cn: U32, +cT: C.Term, +cd: Nat) -> Data:
  match frs:
    case Nil{}:
      {at == 0 : U32}
    case Con{+fr, rest}:
      match fr:
        case Fr{+n, +h, +x2, +T0, +y2, +y3, +y4, +t2, +t3, +t4, +s2, +s3, +s4, +d}:
          D.P2({at == n : U32},
          D.P2(FrOK(mo, m, ks, img, K, F, X, N, Fr{n, h, x2, T0, y2, y3, y4, t2, t3, t4, s2, s3, s4, d}, top, cn, cT, cd),
            Frs(mo, m, ks, img, K, F, X, N, rest, D.Fd(1n, m, n), False{}, n, T0, d)))

# the cells of the frames
def Ns(frs: List<&2, Fr>) -> List<&2, U32>:
  match frs:
    case Nil{}:
      Nil{}
    case Con{Fr{n, _, _, _, _, _, _, _, _, _, _, _, _, _}, rest}:
      Con{n, Ns(rest)}

# twice the nodes of a pending part
def Wp(s: St, t: C.Term) -> Nat:
  match s:
    case St.pe{}:
      Nat.double(D.Sz(t))
    case _:
      0n

# the measure of the frames: a round for each, and two for each node of a
# pending part
def Wm(frs: List<&2, Fr>) -> Nat:
  match frs:
    case Nil{}:
      0n
    case Con{Fr{_, _, _, _, _, _, _, t2, t3, t4, s2, s3, s4, _}, rest}:
      1n+Nat.add(Wp(s2, t2), Nat.add(Wp(s3, t3), Nat.add(Wp(s4, t4), Wm(rest))))

# the last of the frames is the root: a Prj of the source's cell x, of the term
# t, at the depth 0, in the cell root; once the frames are gone, the root's field 2 holds the
# copy, of Mo.F(mo, t, 0)
def Root(+mo: D.Mo, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, frs: List<&2, Fr>, +root: U32, +x: U32, +t: C.Term) -> Data:
  match frs:
    case Nil{}:
      D.Ex(Nat, g => {D.Tm(g, m, ks, img, K, F, X, N, D.Fd(2n, m, root)) == Some{D.Mo.F(mo, t, 0n)} : Maybe<&2, C.Term>})
    case Con{Fr{n, h, _, _, y2, _, _, t2, _, _, _, _, _, d}, Nil{}}:
      D.P2({n == root : U32}, D.P2({h == 11 : U32}, D.P2({y2 == x : U32}, D.P2({t2 == t : C.Term}, {d == 0n : Nat}))))
    case Con{_, rest}:
      Root(mo, m, ks, img, K, F, X, N, rest, root, x, t)

# no frame's cell is in P
def Dj(xs: List<&2, U32>, +P: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Bool.not(D.Has(P, x)), Dj(rest, P))

# the depth d of each frame and twice its source's nodes are at most B: a part
# under it never wraps its U32 depth
def DB(frs: List<&2, Fr>, +B: Nat) -> Bool:
  match frs:
    case Nil{}:
      True{}
    case Con{Fr{_, _, _, T0, _, _, _, _, _, _, _, _, _, d}, rest}:
      Bool.and(Nat.is_le(Nat.add(d, Nat.double(D.Sz(T0))), B), DB(rest, B))

# the depth register holds the top frame's depth
def Dp(frs: List<&2, Fr>, +depth: U32) -> Data:
  match frs:
    case Nil{}:
      Unit
    case Con{Fr{_, _, _, _, _, _, _, _, _, _, _, _, _, d}, _}:
      {depth == U32.from_nat(d) : U32}

# The allocation
# --------------

# the registers xs with 3 to 7 (pend, dx, dr, aq, am) set to the values a
def Rp(+a: List<&2, U32>, xs: List<&2, U32>) -> List<&2, U32>:
  D.Ups([D.Up{3n, T.tm.reg(a, 0n)}, D.Up{4n, T.tm.reg(a, 1n)}, D.Up{5n, T.tm.reg(a, 2n)}, D.Up{6n, T.tm.reg(a, 3n)},
    D.Up{7n, T.tm.reg(a, 4n)}], xs)

# a write of field 1 (a count or a link) of the cell x
type W1 is Data:
  W1{x: U32, v: U32}

def W1s(ws: List<&2, W1>, +m: C.Cir.Cells) -> C.Cir.Cells:
  match ws:
    case Nil{}:
      m
    case Con{W1{+x, v}, rest}:
      W1s(rest, C.Cir.Cells.set(m, x, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x), v)))

# each write is to a cell of P
def W1s.in(ws: List<&2, W1>, +P: List<&2, U32>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{W1{+x, _}, rest}:
      Bool.and(D.Has(P, x), W1s.in(rest, P))

# xs without its first x
def Del(xs: List<&2, U32>, +x: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+y, +rest}:
      Bool.pick(List<&2, U32>, U32.is_eq(y, x), rest, Con{y, Del(rest, x)})

# what M.alloc did: the cell c, a new one (fresh) or the first of the pend
# list, after the counts ws of the garbage's cells that its reuse dropped;
# the garbage P2 and pend list Q2 after it, and the registers 3 to 7
type Aw is Data:
  Aw{c: U32, fresh: Bool, P2: List<&2, U32>, Q2: List<&2, U32>, ws: List<&2, W1>, a: List<&2, U32>}

def Al.how(fresh: Bool, +P: List<&2, U32>, +c: U32, +P2: List<&2, U32>, +nx: U32, +nx2: U32) -> Data:
  match fresh:
    case True{}:
      D.P2({c == nx : U32}, D.P2({P2 == P : List<&2, U32>}, D.P2({nx2 == U32.inc(nx) : U32},
        {U32.is_lt(nx, 214748364) == True{} : Bool})))
    case False{}:
      D.P2({D.Has(P, c) == True{} : Bool}, D.P2({P2 == Del(P, c) : List<&2, U32>}, {nx2 == nx : U32}))

def Al.post(+r: Nat, +R: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +K: U32, +F: U32, +P: List<&2, U32>, +Bu: U32, w: Aw,
  +rg: List<&2, U32>, +ms: C.Cir.Cells, +nx2: U32) -> Data:
  match w:
    case Aw{+c, +fresh, +P2, +Q2, +ws, +a}:
      D.P2({rg == List.set(&2, U32, Rp(a, D.Rg.ex(64n, R, 0n)), r, c) : List<&2, U32>},
      D.P2({ms == C.Cir.Cells.set(W1s(ws, m), c, C.Cir.Cell.zero()) : C.Cir.Cells},
      D.P2({W1s.in(ws, P) == True{} : Bool},
      D.P2(Al.how(fresh, P, c, P2, nx, nx2),
      D.P2({D.AL(ms, T.tm.reg(a, 0n), P2, Q2, K, F, nx2, Bu) == True{} : Bool},
      D.P2({U32.is_le(F, c) == True{} : Bool},
      D.P2({C.Cir.is_cell(c, K, F, nx2) == True{} : Bool},
      D.P2({D.Has(P2, c) == False{} : Bool}, D.Tb(ms)))))))))

# M.alloc(r): the cell that it gives is a new one or the first of the pend
# list, whose reuse drops the counts of its parts; the allocation's invariant
# holds again, without that cell
def Al.ok(+f: Nat, +r: Nat, +R: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +F: U32, +K: U32, +pg: U32, +L: U32,
  +I: List<&2, U32>, +P: List<&2, U32>, +Q: List<&2, U32>, +Bu: U32,
  hal: {D.AL(m, T.tm.reg(R, 3n), P, Q, K, F, nx, Bu) == True{} : Bool},
  hr: {Bool.and(Nat.is_lt(r, 64n), Bool.not(Bool.and(Nat.is_le(3n, r), Nat.is_le(r, 7n)))) == True{} : Bool},
  hk: {U32.is_le(363, K) == True{} : Bool}, hkf: {U32.is_lt(K, F) == True{} : Bool}, hfn: {U32.is_le(F, nx) == True{} : Bool},
  tb: D.Tb(m)) ->
  D.Ok(C.Cir.exec(1n+f, C.M.alloc(r), D.S(D.Rg.ex(64n, R, 0n), m, nx, F, K, pg, L, I)), F, K, L, I,
    rg => ms => nx2 => pg2 => D.Ex(Aw, w => Al.post(r, R, m, nx, K, F, P, Bu, w, rg, ms, nx2))):
  ?TODO
