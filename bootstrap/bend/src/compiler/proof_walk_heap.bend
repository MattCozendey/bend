# compiler: the shared heap, for M.data and M.walk (layer B)
# ==========================================================
#
# Facts of proof_mach_defs.bend's heap (Fs, Pc, Ptr, Is) that the phases
# which take cells need, beyond the heap's operations:
#
#   ptr.part: a part of a node c of a term, where c is one of the machine's
#     own cells, has a pointer (Ptr >= 1): c is a term cell, whose mask in
#     the table (Tbl) names the part, and Pc counts c's pointers (Pc.at).
#   part.ne, is.fz: so a cell z that nothing points to (Ptr 0) and that is
#     not STATIC is no node of a term that Is says, and a store to z keeps
#     every such term (is.fz, by induction on the term).
#   The registers: List.get after List.set (rg.*), Kept after a set.
#
# It imports only proof_mach_defs.bend and what that file imports.

import Base
import ./impl.bend as C
import ./proof_term.bend as T
import ./proof_need.bend as N
import ./proof_mach_defs.bend as PM

# Kit
# ---

def and.l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def and.r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      PM.bool.ft({b == True{} : Bool}, h)

def or.r(b: Bool, -c: Bool, h: {c == True{} : Bool}) -> {Bool.or(b, c) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      h

# Numbers
# -------

# 2a <= 2b gives a <= b
def dle(a: Nat, b: Nat, h: N.Le(Nat.double(a), Nat.double(b))) -> N.Le(a, b):
  match a:
    case 0n:
      N.le_zero(b)
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(N.Le(1n+p, 0n), h)
        case 1n+q:
          dle(p, q, h)

# 2 + 2a <= 1 + 2b gives 1 + a <= b
def dle1(a: Nat, b: Nat, h: N.Le(2n+Nat.double(a), 1n+Nat.double(b))) -> N.Le(1n+a, b):
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd(N.Le(1n, 0n), h)
        case 1n+q:
          N.le_zero(q)
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(N.Le(2n+p, 0n), h)
        case 1n+q:
          dle1(p, q, h)

# a word below another one adds 1 when it grows
def w.inc(+n: Nat, w: Word(n), w2: Word(n), h: N.Le(1n+Word.to_nat(n, w), Word.to_nat(n, w2))) ->
  {Word.to_nat(n, Word.inc(n, w)) == 1n+Word.to_nat(n, w) : Nat}:
  match n:
    case 0n:
      match w w2:
        case WNil{} WNil{}:
          Empty.absurd({0n == 1n : Nat}, h)
    case 1n+p:
      match w w2:
        case WCon{False{}, t} _:
          {==}
        case WCon{True{}, +t} WCon{False{}, +t2}:
          %Equal.sym(Nat, Word.to_nat(p, Word.inc(p, t)), 1n+Word.to_nat(p, t), w.inc(p, t, t2, dle(1n+Word.to_nat(p, t), Word.to_nat(p, t2), h))) :
            {Nat.double(_) == 2n+Nat.double(Word.to_nat(p, t)) : Nat}
          {==}
        case WCon{True{}, +t} WCon{True{}, +t2}:
          %Equal.sym(Nat, Word.to_nat(p, Word.inc(p, t)), 1n+Word.to_nat(p, t), w.inc(p, t, t2, dle1(Word.to_nat(p, t), Word.to_nat(p, t2), h))) :
            {Nat.double(_) == 2n+Nat.double(Word.to_nat(p, t)) : Nat}
          {==}

# a U32 below another one adds 1 when it grows
def u.inc(+a: U32, +b: U32, h: N.Le(1n+U32.to_nat(a), U32.to_nat(b))) -> {U32.to_nat(U32.inc(a)) == 1n+U32.to_nat(a) : Nat}:
  match a b:
    case U32{x} U32{y}:
      w.inc(32n, x, y, h)

# what the comparisons of U32s say of their numbers
def rel.lt(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), e: {Cmp.is_lt(c) == True{} : Bool}) -> N.Le(1n+x, y):
  match c:
    case LT{}:
      r
    case EQ{}:
      PM.bool.ft(N.Le(1n+x, y), e)
    case GT{}:
      PM.bool.ft(N.Le(1n+x, y), e)

def lt.ne(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), ne: {Cmp.is_eq(c) == False{} : Bool}, le: N.Le(x, y)) -> N.Le(1n+x, y):
  match c:
    case LT{}:
      r
    case EQ{}:
      Empty.absurd(N.Le(1n+x, y), N.true_ne_false(ne))
    case GT{}:
      Empty.absurd(N.Le(1n+x, y), N.not_succ_le(y, N.le_trans(1n+y, x, y, r, le)))

def u.le(+a: U32, +b: U32, e: {U32.is_le(a, b) == True{} : Bool}) -> N.Le(U32.to_nat(a), U32.to_nat(b)):
  N.rel_le(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), N.toT(U32.is_le(a, b), e))

def u.lt(+a: U32, +b: U32, e: {U32.is_lt(a, b) == True{} : Bool}) -> N.Le(1n+U32.to_nat(a), U32.to_nat(b)):
  rel.lt(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), e)

# f + (x - f) = x, when f <= x
def add.sub(f: Nat, x: Nat, h: N.Le(f, x)) -> {Nat.add(f, Nat.sub(x, f)) == x : Nat}:
  match f:
    case 0n:
      match x:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      match x:
        case 0n:
          Empty.absurd({1n+Nat.add(p, 0n) == 0n : Nat}, h)
        case 1n+q:
          %add.sub(p, q, h) : {1n+Nat.add(p, Nat.sub(q, p)) == 1n+_ : Nat}
          {==}

# Pointers
# --------

# RcL counts c in a list where c is
def rcl.mem.b(b: Bool, -M: Bool, +r: Nat, hm: {Bool.or(b, M) == True{} : Bool}, ih: {M == True{} : Bool} -> N.Le(1n, r)) ->
  N.Le(1n, Nat.add(PM.Nat.of(b), r)):
  match b:
    case True{}:
      N.le_zero(r)
    case False{}:
      ih(hm)

def rcl.mem(xs: List<&2, U32>, +c: U32, h: {PM.Mem(xs, c) == True{} : Bool}) -> N.Le(1n, PM.RcL(xs, c)):
  match xs:
    case Nil{}:
      PM.bool.ft(N.Le(1n, 0n), h)
    case Con{+x, +rest}:
      rcl.mem.b(U32.is_eq(x, c), PM.Mem(rest, c), PM.RcL(rest, c), h, e => rcl.mem(rest, c, e))

# c is in a list that starts with it
def mem.hd(+x: U32, -rest: List<&2, U32>) -> {PM.Mem(Con{x, rest}, x) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(x, x), True{}, PM.u32.refl(x)) : {Bool.or(_, PM.Mem(rest, x)) == True{} : Bool}
  {==}

def mem.tl(+x: U32, +c: U32, -rest: List<&2, U32>, h: {PM.Mem(rest, c) == True{} : Bool}) -> {PM.Mem(Con{x, rest}, c) == True{} : Bool}:
  or.r(U32.is_eq(x, c), PM.Mem(rest, c), h)

# the cell p, at or after o and before n cells from o, counts its pointers to
# c in Pc
def Pc.at.b(b: Bool, +k: Nat, +m: C.Cir.Cells, +ps: List<&2, U32>, +o: U32, +p: U32, +c: U32, eb: {U32.is_eq(o, p) == b : Bool},
  h1: N.Le(U32.to_nat(o), U32.to_nat(p)), h2: N.Le(1n+U32.to_nat(p), Nat.add(U32.to_nat(o), 1n+k)),
  ih: N.Le(U32.to_nat(U32.inc(o)), U32.to_nat(p)) -> N.Le(1n+U32.to_nat(p), Nat.add(U32.to_nat(U32.inc(o)), k)) ->
    N.Le(PM.RcL(PM.Fs(m, ps, p), c), PM.Pc(k, m, ps, U32.inc(o), c))) ->
  N.Le(PM.RcL(PM.Fs(m, ps, p), c), Nat.add(PM.RcL(PM.Fs(m, ps, o), c), PM.Pc(k, m, ps, U32.inc(o), c))):
  match b:
    case True{}:
      %Equal.sym(U32, o, p, PM.u32.eq(o, p, eb)) : N.Le(PM.RcL(PM.Fs(m, ps, p), c), Nat.add(PM.RcL(PM.Fs(m, ps, _), c), PM.Pc(k, m, ps, U32.inc(o), c)))
      N.le_add_r(PM.RcL(PM.Fs(m, ps, p), c), PM.Pc(k, m, ps, U32.inc(o), c))
    case False{}:
      +lt = lt.ne(U32.cmp(o, p), U32.to_nat(o), U32.to_nat(p), N.U32.rel(o, p), eb, h1)
      +ei = u.inc(o, p, lt)
      +h1b = N.le_rw_l(1n+U32.to_nat(o), U32.to_nat(U32.inc(o)), U32.to_nat(p), Equal.sym(Nat, U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei), lt)
      +h2b = N.le_rw_r(1n+U32.to_nat(p), Nat.add(U32.to_nat(o), 1n+k), Nat.add(U32.to_nat(U32.inc(o)), k),
        Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+k), 1n+Nat.add(U32.to_nat(o), k), Nat.add(U32.to_nat(U32.inc(o)), k),
          N.add_succ_r(U32.to_nat(o), k),
          Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(o)), k), 1n+Nat.add(U32.to_nat(o), k),
            Equal.cong(Nat, Nat, x => Nat.add(x, k), U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei))), h2)
      N.le_trans(PM.RcL(PM.Fs(m, ps, p), c), PM.Pc(k, m, ps, U32.inc(o), c), Nat.add(PM.RcL(PM.Fs(m, ps, o), c), PM.Pc(k, m, ps, U32.inc(o), c)),
        ih(h1b, h2b), N.le_add_l(PM.RcL(PM.Fs(m, ps, o), c), PM.Pc(k, m, ps, U32.inc(o), c)))

def Pc.at(n: Nat, +m: C.Cir.Cells, +ps: List<&2, U32>, +o: U32, +p: U32, +c: U32,
  h1: N.Le(U32.to_nat(o), U32.to_nat(p)), h2: N.Le(1n+U32.to_nat(p), Nat.add(U32.to_nat(o), n))) ->
  N.Le(PM.RcL(PM.Fs(m, ps, p), c), PM.Pc(n, m, ps, o, c)):
  match n:
    case 0n:
      Empty.absurd(N.Le(PM.RcL(PM.Fs(m, ps, p), c), 0n),
        N.not_succ_le(U32.to_nat(p), N.le_trans(1n+U32.to_nat(p), U32.to_nat(o), U32.to_nat(p),
          N.le_rw_r(1n+U32.to_nat(p), Nat.add(U32.to_nat(o), 0n), U32.to_nat(o), N.add_zero(U32.to_nat(o)), h2), h1)))
    case 1n+(+k):
      Pc.at.b(U32.is_eq(o, p), k, m, ps, o, p, c, {==}, h1, h2, x => y => Pc.at(k, m, ps, U32.inc(o), p, c, x, y))

# a cell of the machine's own counts its pointers to c in Ptr
def Ptr.at(+m: C.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +p: U32, +c: U32,
  own: {PM.Own(fi, nx, p) == True{} : Bool}) ->
  N.Le(PM.RcL(PM.Fs(m, ps, p), c), PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, c)):
  +o2 = own
  +h1 = u.le(fi, p, and.l(U32.is_le(fi, p), U32.is_lt(p, nx), o2))
  +hl = u.lt(p, nx, and.r(U32.is_le(fi, p), U32.is_lt(p, nx), o2))
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +es = add.sub(U32.to_nat(fi), U32.to_nat(nx), N.le_trans(U32.to_nat(fi), U32.to_nat(p), U32.to_nat(nx), h1, N.weaken(U32.to_nat(p), U32.to_nat(nx), hl)))
  N.le_trans(PM.RcL(PM.Fs(m, ps, p), c), PM.Pc(n, m, ps, fi, c), PM.Ptr(n, m, fi, ps, rs, c),
    Pc.at(n, m, ps, fi, p, c, h1, N.le_rw_r(1n+U32.to_nat(p), U32.to_nat(nx), Nat.add(U32.to_nat(fi), n), Equal.sym(Nat, Nat.add(U32.to_nat(fi), n), U32.to_nat(nx), es), hl)),
    N.le_add_r(PM.Pc(n, m, ps, fi, c), PM.RcL(rs, c)))

# The table
# ---------

# the mask of a term's tag: the fields of its parts (1 for field 2, 2 for 3,
# 4 for 4), as I.table holds it
def Mask(t: C.Term) -> U32:
  match t:
    case C.Term.Var{_}:
      0
    case C.Term.Ref{_}:
      0
    case C.Term.Ann{_, _}:
      3
    case C.Term.Let{_, _, _}:
      3
    case C.Term.Typ{_}:
      1
    case C.Term.Min{_, _}:
      3
    case C.Term.All{_, _, _}:
      3
    case C.Term.Lam{_, _}:
      1
    case C.Term.App{_, _, _}:
      3
    case C.Term.Sig{_, _, _}:
      3
    case C.Term.Tup{_, _, _}:
      3
    case C.Term.Prj{_}:
      1
    case C.Term.Enu{_}:
      0
    case C.Term.Lab{_}:
      0
    case C.Term.Mat{_, _, _}:
      6
    case C.Term.Efq{}:
      0
    case C.Term.Eql{_, _, _}:
      7
    case C.Term.Rfl{}:
      0
    case C.Term.Rwt{_, _, _}:
      7

# the table's mask for the tag of t (Tbl)
def tbl.mask(-m: C.Cir.Cells, -im: U32, -fi: U32, -nx: U32, t: C.Term, h: PM.Tbl(m, im, fi, nx)) ->
  {PM.Fd(2n, m, U32.add(345, PM.A.tag(t))) == Mask(t) : U32}:
  match t:
    case C.Term.Var{_}:
      match h:
        case Tuple{_, Tuple{e, _}}:
          e
    case C.Term.Ref{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}:
          e
    case C.Term.Ann{_, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}:
          e
    case C.Term.Let{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}:
          e
    case C.Term.Typ{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Min{_, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.All{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Lam{_, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.App{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Sig{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Tup{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Prj{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Enu{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Lab{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Mat{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Efq{}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Eql{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Rfl{}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Rwt{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e

# The parts of a node
# -------------------

# Fs, with the test of the tag b and the tag tg apart
def FsP(b: Bool, +m: C.Cir.Cells, +ps: List<&2, U32>, +o: U32, +tg: U32) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, b, PM.Fs.term(PM.Fd(2n, m, U32.add(345, tg)), PM.Fd(2n, m, o), PM.Fd(3n, m, o), PM.Fd(4n, m, o)),
    Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, tg), U32.is_le(tg, 40)), Bool.not(PM.Mem(ps, o))),
      Con{PM.Fd(2n, m, o), PM.Fs.opt(U32.is_eq(tg, 38), PM.Fd(3n, m, o), Nil{})},
      Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(tg, 41), PM.FlW(PM.Fd(0n, m, o), 4096)), Bool.not(PM.Mem(ps, o))),
        [PM.Fd(2n, m, o)], Nil{})))

# the pointers of a term cell of the tag tg, whose mask is mask, are its parts
# by the mask
def fs.term(+m: C.Cir.Cells, +ps: List<&2, U32>, +o: U32, +tg: U32, +mask: U32, etag: {PM.TgW(PM.Fd(0n, m, o)) == tg : U32},
  hlt: {U32.is_lt(tg, 19) == True{} : Bool}, emask: {PM.Fd(2n, m, U32.add(345, tg)) == mask : U32}) ->
  {PM.Fs(m, ps, o) == PM.Fs.term(mask, PM.Fd(2n, m, o), PM.Fd(3n, m, o), PM.Fd(4n, m, o)) : List<&2, U32>}:
  %Equal.sym(U32, PM.TgW(PM.Fd(0n, m, o)), tg, etag) :
    {FsP(U32.is_lt(_, 19), m, ps, o, _) == PM.Fs.term(mask, PM.Fd(2n, m, o), PM.Fd(3n, m, o), PM.Fd(4n, m, o)) : List<&2, U32>}
  %Equal.sym(Bool, U32.is_lt(tg, 19), True{}, hlt) :
    {FsP(_, m, ps, o, tg) == PM.Fs.term(mask, PM.Fd(2n, m, o), PM.Fd(3n, m, o), PM.Fd(4n, m, o)) : List<&2, U32>}
  %Equal.sym(U32, PM.Fd(2n, m, U32.add(345, tg)), mask, emask) :
    {PM.Fs.term(_, PM.Fd(2n, m, o), PM.Fd(3n, m, o), PM.Fd(4n, m, o)) == PM.Fs.term(mask, PM.Fd(2n, m, o), PM.Fd(3n, m, o), PM.Fd(4n, m, o)) : List<&2, U32>}
  {==}

# a part y, by the mask, of a term cell c of the machine's own has a pointer
def ptr.part(+m: C.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +c: U32, +y: U32, +tg: U32, +mask: U32,
  etag: {PM.TgW(PM.Fd(0n, m, c)) == tg : U32}, hlt: {U32.is_lt(tg, 19) == True{} : Bool},
  emask: {PM.Fd(2n, m, U32.add(345, tg)) == mask : U32}, own: {PM.Own(fi, nx, c) == True{} : Bool},
  hm: {PM.Mem(PM.Fs.term(mask, PM.Fd(2n, m, c), PM.Fd(3n, m, c), PM.Fd(4n, m, c)), y) == True{} : Bool}) ->
  N.Le(1n, PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, y)):
  +e = fs.term(m, ps, c, tg, mask, etag, hlt, emask)
  N.le_trans(1n, PM.RcL(PM.Fs(m, ps, c), y), PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, y),
    (%Equal.sym(List<&2, U32>, PM.Fs(m, ps, c), PM.Fs.term(mask, PM.Fd(2n, m, c), PM.Fd(3n, m, c), PM.Fd(4n, m, c)), e) : N.Le(1n, PM.RcL(_, y));
      rcl.mem(PM.Fs.term(mask, PM.Fd(2n, m, c), PM.Fd(3n, m, c), PM.Fd(4n, m, c)), y, hm)),
    Ptr.at(m, nx, fi, ps, rs, c, y, own))

# a cell with a pointer is not one with none
def ne.ptr(b: Bool, +y: U32, +z: U32, +n: Nat, +m: C.Cir.Cells, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  eb: {U32.is_eq(y, z) == b : Bool}, hy: N.Le(1n, PM.Ptr(n, m, fi, ps, rs, y)), hz: {PM.Ptr(n, m, fi, ps, rs, z) == 0n : Nat}) ->
  {U32.is_eq(y, z) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +e = PM.u32.eq(y, z, eb)
      Empty.absurd({U32.is_eq(y, z) == False{} : Bool},
        N.le_rw_r(1n, PM.Ptr(n, m, fi, ps, rs, z), 0n, hz,
          N.le_rw_r(1n, PM.Ptr(n, m, fi, ps, rs, y), PM.Ptr(n, m, fi, ps, rs, z), Equal.cong(U32, Nat, w => PM.Ptr(n, m, fi, ps, rs, w), y, z, e), hy)))

# a STATIC cell is not one that is not STATIC
def ne.st(b: Bool, +m: C.Cir.Cells, +y: U32, +z: U32, eb: {U32.is_eq(y, z) == b : Bool},
  hy: {PM.Fl(m, y, 1024) == True{} : Bool}, hz: {PM.Fl(m, z, 1024) == False{} : Bool}) -> {U32.is_eq(y, z) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +e = PM.u32.eq(y, z, eb)
      PM.bool.ft({U32.is_eq(y, z) == False{} : Bool}, Equal.trans(Bool, False{}, PM.Fl(m, z, 1024), True{}, Equal.sym(Bool, PM.Fl(m, z, 1024), False{}, hz),
        (%e : {PM.Fl(m, _, 1024) == True{} : Bool}; hy)))

def part.ne.b(o: Bool, +m: C.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +c: U32, +y: U32, +z: U32,
  +tg: U32, +mask: U32, eo: {PM.Own(fi, nx, c) == o : Bool},
  sp: {Bool.or(o, PM.FlW(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, y)), 1024)) == True{} : Bool},
  etag: {PM.TgW(PM.Fd(0n, m, c)) == tg : U32}, hlt: {U32.is_lt(tg, 19) == True{} : Bool},
  emask: {PM.Fd(2n, m, U32.add(345, tg)) == mask : U32},
  hm: {PM.Mem(PM.Fs.term(mask, PM.Fd(2n, m, c), PM.Fd(3n, m, c), PM.Fd(4n, m, c)), y) == True{} : Bool},
  hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat},
  hzs: {PM.Fl(m, z, 1024) == False{} : Bool}) -> {U32.is_eq(y, z) == False{} : Bool}:
  match o:
    case True{}:
      ne.ptr(U32.is_eq(y, z), y, z, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, {==},
        ptr.part(m, nx, fi, ps, rs, c, y, tg, mask, etag, hlt, emask, eo, hm), hz0)
    case False{}:
      ne.st(U32.is_eq(y, z), m, y, z, {==}, sp, hzs)

# a part y of a node c (by the mask of c's tag tg) is not the cell z, which
# nothing points to and is not STATIC
def part.ne(+m: C.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +c: U32, +y: U32, +z: U32,
  +tg: U32, +mask: U32, sp: PM.Sp(fi, nx, c, C.Cir.Cells.get(m, y)),
  etag: {PM.TgW(PM.Fd(0n, m, c)) == tg : U32}, hlt: {U32.is_lt(tg, 19) == True{} : Bool},
  emask: {PM.Fd(2n, m, U32.add(345, tg)) == mask : U32},
  hm: {PM.Mem(PM.Fs.term(mask, PM.Fd(2n, m, c), PM.Fd(3n, m, c), PM.Fd(4n, m, c)), y) == True{} : Bool},
  hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat},
  hzs: {PM.Fl(m, z, 1024) == False{} : Bool}) -> {U32.is_eq(y, z) == False{} : Bool}:
  part.ne.b(PM.Own(fi, nx, c), m, nx, fi, ps, rs, c, y, z, tg, mask, {==}, sp, etag, hlt, emask, hm, hz0, hzs)

# the tag that a node says
def nd.tg(-ds: List<&2, C.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, -x: C.Cir.Cell, -t: C.Term, -tag: U32,
  h: PM.Nd(ds, im, fi, nx, c, x, t, tag)) -> {PM.TgW(C.Cir.Cell.get(0n, x)) == tag : U32}:
  (e0, r0) = h
  (e1, r1) = r0
  (e, r) = r1
  e

# a part of a node, after a store to the cell z, which nothing points to and
# is not STATIC: the part is not z, so the store keeps it (rec)
def part.fz(ty: C.Term, +ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32, +x: C.Cir.Cell, +c: U32, +y: U32, +tg: U32, +mask: U32,
  hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat}, hzs: {PM.Fl(m, z, 1024) == False{} : Bool},
  etag: {PM.TgW(PM.Fd(0n, m, c)) == tg : U32}, hlt: {U32.is_lt(tg, 19) == True{} : Bool},
  emask: {PM.Fd(2n, m, U32.add(345, tg)) == mask : U32},
  hm: {PM.Mem(PM.Fs.term(mask, PM.Fd(2n, m, c), PM.Fd(3n, m, c), PM.Fd(4n, m, c)), y) == True{} : Bool},
  rec: {U32.is_eq(y, z) == False{} : Bool} -> PM.Is(ds, m, im, fi, nx, ks, img, y, ty) -> PM.Is(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, y, ty),
  hp: PM.P2(PM.Sp(fi, nx, c, C.Cir.Cells.get(m, y)), PM.IsC(ds, m, im, fi, nx, ks, img, y, C.Cir.Cells.get(m, y), ty))) ->
  PM.P2(PM.Sp(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), y)),
    PM.IsC(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, y, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), y), ty)):
  (+sp, hy) = hp
  +ne = part.ne(m, nx, fi, ps, rs, c, y, z, tg, mask, sp, etag, hlt, emask, hm, hz0, hzs)
  (PM.sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), y), C.Cir.Cells.get(m, y), PM.cl.go(m, y, z, x, ne), sp), rec(ne, hy))

# a store to the cell z, which nothing points to (Ptr 0) and is not STATIC,
# keeps the term of every cell c but z
def is.fz(t: C.Term, +ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32, +x: C.Cir.Cell, +c: U32, +tbl: PM.Tbl(m, im, fi, nx),
  +hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat}, +hzs: {PM.Fl(m, z, 1024) == False{} : Bool},
  hc: {U32.is_eq(c, z) == False{} : Bool}, h: PM.Is(ds, m, im, fi, nx, ks, img, c, t)) ->
  PM.Is(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, t):
  match t:
    case C.Term.Var{+i}:
      PM.isc.at(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), c), C.Cir.Cells.get(m, c), C.Term.Var{i}, PM.cl.go(m, c, z, x, hc),
            h)
    case C.Term.Ref{+k}:
      PM.isc.at(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), c), C.Cir.Cells.get(m, c), C.Term.Ref{k}, PM.cl.go(m, c, z, x, hc),
            h)
    case C.Term.Enu{+e}:
      PM.isc.at(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), c), C.Cir.Cells.get(m, c), C.Term.Enu{e}, PM.cl.go(m, c, z, x, hc),
            h)
    case C.Term.Lab{+k}:
      PM.isc.at(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), c), C.Cir.Cells.get(m, c), C.Term.Lab{k}, PM.cl.go(m, c, z, x, hc),
            h)
    case C.Term.Efq{}:
      PM.isc.at(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), c), C.Cir.Cells.get(m, c), C.Term.Efq{}, PM.cl.go(m, c, z, x, hc),
            h)
    case C.Term.Rfl{}:
      PM.isc.at(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), c), C.Cir.Cells.get(m, c), C.Term.Rfl{}, PM.cl.go(m, c, z, x, hc),
            h)
    case C.Term.Ann{+a, +b}:
      (+nd, r) = h
      (pa, pb) = r
      PM.isc.at(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), c), C.Cir.Cells.get(m, c), C.Term.Ann{a, b}, PM.cl.go(m, c, z, x, hc),
            (nd, (part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(2n, m, c), 2, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Ann{a, b}, 2, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.Ann{a, b}, tbl), mem.hd(PM.Fd(2n, m, c), Con{PM.Fd(3n, m, c), Nil{}}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, c), tbl, hz0, hzs, e, hh), pa),
              part.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(3n, m, c), 2, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Ann{a, b}, 2, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.Ann{a, b}, tbl), mem.tl(PM.Fd(2n, m, c), PM.Fd(3n, m, c), Con{PM.Fd(3n, m, c), Nil{}}, mem.hd(PM.Fd(3n, m, c), Nil{})),
              e => hh => is.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, c), tbl, hz0, hzs, e, hh), pb))))
    case C.Term.Min{+a, +b}:
      (+nd, r) = h
      (pa, pb) = r
      PM.isc.at(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), c), C.Cir.Cells.get(m, c), C.Term.Min{a, b}, PM.cl.go(m, c, z, x, hc),
            (nd, (part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(2n, m, c), 5, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Min{a, b}, 5, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.Min{a, b}, tbl), mem.hd(PM.Fd(2n, m, c), Con{PM.Fd(3n, m, c), Nil{}}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, c), tbl, hz0, hzs, e, hh), pa),
              part.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(3n, m, c), 5, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Min{a, b}, 5, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.Min{a, b}, tbl), mem.tl(PM.Fd(2n, m, c), PM.Fd(3n, m, c), Con{PM.Fd(3n, m, c), Nil{}}, mem.hd(PM.Fd(3n, m, c), Nil{})),
              e => hh => is.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, c), tbl, hz0, hzs, e, hh), pb))))
    case C.Term.Let{+q, +a, +b}:
      (+nd, r) = h
      (qs, r2) = r
      (pa, pb) = r2
      PM.isc.at(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), c), C.Cir.Cells.get(m, c), C.Term.Let{q, a, b}, PM.cl.go(m, c, z, x, hc),
            (nd, (qs, (part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(2n, m, c), 3, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Let{q, a, b}, 3, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.Let{q, a, b}, tbl), mem.hd(PM.Fd(2n, m, c), Con{PM.Fd(3n, m, c), Nil{}}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, c), tbl, hz0, hzs, e, hh), pa),
              part.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(3n, m, c), 3, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Let{q, a, b}, 3, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.Let{q, a, b}, tbl), mem.tl(PM.Fd(2n, m, c), PM.Fd(3n, m, c), Con{PM.Fd(3n, m, c), Nil{}}, mem.hd(PM.Fd(3n, m, c), Nil{})),
              e => hh => is.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, c), tbl, hz0, hzs, e, hh), pb)))))
    case C.Term.All{+q, +a, +b}:
      (+nd, r) = h
      (qs, r2) = r
      (pa, pb) = r2
      PM.isc.at(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), c), C.Cir.Cells.get(m, c), C.Term.All{q, a, b}, PM.cl.go(m, c, z, x, hc),
            (nd, (qs, (part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(2n, m, c), 6, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.All{q, a, b}, 6, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.All{q, a, b}, tbl), mem.hd(PM.Fd(2n, m, c), Con{PM.Fd(3n, m, c), Nil{}}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, c), tbl, hz0, hzs, e, hh), pa),
              part.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(3n, m, c), 6, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.All{q, a, b}, 6, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.All{q, a, b}, tbl), mem.tl(PM.Fd(2n, m, c), PM.Fd(3n, m, c), Con{PM.Fd(3n, m, c), Nil{}}, mem.hd(PM.Fd(3n, m, c), Nil{})),
              e => hh => is.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, c), tbl, hz0, hzs, e, hh), pb)))))
    case C.Term.App{+q, +a, +b}:
      (+nd, r) = h
      (qs, r2) = r
      (pa, pb) = r2
      PM.isc.at(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), c), C.Cir.Cells.get(m, c), C.Term.App{q, a, b}, PM.cl.go(m, c, z, x, hc),
            (nd, (qs, (part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(2n, m, c), 8, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.App{q, a, b}, 8, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.App{q, a, b}, tbl), mem.hd(PM.Fd(2n, m, c), Con{PM.Fd(3n, m, c), Nil{}}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, c), tbl, hz0, hzs, e, hh), pa),
              part.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(3n, m, c), 8, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.App{q, a, b}, 8, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.App{q, a, b}, tbl), mem.tl(PM.Fd(2n, m, c), PM.Fd(3n, m, c), Con{PM.Fd(3n, m, c), Nil{}}, mem.hd(PM.Fd(3n, m, c), Nil{})),
              e => hh => is.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, c), tbl, hz0, hzs, e, hh), pb)))))
    case C.Term.Sig{+q, +a, +b}:
      (+nd, r) = h
      (qs, r2) = r
      (pa, pb) = r2
      PM.isc.at(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), c), C.Cir.Cells.get(m, c), C.Term.Sig{q, a, b}, PM.cl.go(m, c, z, x, hc),
            (nd, (qs, (part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(2n, m, c), 9, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Sig{q, a, b}, 9, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.Sig{q, a, b}, tbl), mem.hd(PM.Fd(2n, m, c), Con{PM.Fd(3n, m, c), Nil{}}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, c), tbl, hz0, hzs, e, hh), pa),
              part.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(3n, m, c), 9, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Sig{q, a, b}, 9, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.Sig{q, a, b}, tbl), mem.tl(PM.Fd(2n, m, c), PM.Fd(3n, m, c), Con{PM.Fd(3n, m, c), Nil{}}, mem.hd(PM.Fd(3n, m, c), Nil{})),
              e => hh => is.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, c), tbl, hz0, hzs, e, hh), pb)))))
    case C.Term.Tup{+q, +a, +b}:
      (+nd, r) = h
      (qs, r2) = r
      (pa, pb) = r2
      PM.isc.at(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), c), C.Cir.Cells.get(m, c), C.Term.Tup{q, a, b}, PM.cl.go(m, c, z, x, hc),
            (nd, (qs, (part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(2n, m, c), 10, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Tup{q, a, b}, 10, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.Tup{q, a, b}, tbl), mem.hd(PM.Fd(2n, m, c), Con{PM.Fd(3n, m, c), Nil{}}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, c), tbl, hz0, hzs, e, hh), pa),
              part.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(3n, m, c), 10, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Tup{q, a, b}, 10, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.Tup{q, a, b}, tbl), mem.tl(PM.Fd(2n, m, c), PM.Fd(3n, m, c), Con{PM.Fd(3n, m, c), Nil{}}, mem.hd(PM.Fd(3n, m, c), Nil{})),
              e => hh => is.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, c), tbl, hz0, hzs, e, hh), pb)))))
    case C.Term.Typ{+a}:
      (+nd, pa) = h
      PM.isc.at(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), c), C.Cir.Cells.get(m, c), C.Term.Typ{a}, PM.cl.go(m, c, z, x, hc),
            (nd, part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(2n, m, c), 4, 1, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Typ{a}, 4, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.Typ{a}, tbl), mem.hd(PM.Fd(2n, m, c), Nil{}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, c), tbl, hz0, hzs, e, hh), pa)))
    case C.Term.Prj{+a}:
      (+nd, pa) = h
      PM.isc.at(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), c), C.Cir.Cells.get(m, c), C.Term.Prj{a}, PM.cl.go(m, c, z, x, hc),
            (nd, part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(2n, m, c), 11, 1, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Prj{a}, 11, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.Prj{a}, tbl), mem.hd(PM.Fd(2n, m, c), Nil{}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, c), tbl, hz0, hzs, e, hh), pa)))
    case C.Term.Lam{+q, +a}:
      (+nd, r) = h
      (qs, pa) = r
      PM.isc.at(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), c), C.Cir.Cells.get(m, c), C.Term.Lam{q, a}, PM.cl.go(m, c, z, x, hc),
            (nd, (qs, part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(2n, m, c), 7, 1, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Lam{q, a}, 7, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.Lam{q, a}, tbl), mem.hd(PM.Fd(2n, m, c), Nil{}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, c), tbl, hz0, hzs, e, hh), pa))))
    case C.Term.Mat{+k, +a, +b}:
      (+nd, r) = h
      (nm, r2) = r
      (pa, pb) = r2
      PM.isc.at(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), c), C.Cir.Cells.get(m, c), C.Term.Mat{k, a, b}, PM.cl.go(m, c, z, x, hc),
            (nd, (nm, (part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(3n, m, c), 14, 6, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Mat{k, a, b}, 14, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.Mat{k, a, b}, tbl), mem.hd(PM.Fd(3n, m, c), Con{PM.Fd(4n, m, c), Nil{}}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, c), tbl, hz0, hzs, e, hh), pa),
              part.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(4n, m, c), 14, 6, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Mat{k, a, b}, 14, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.Mat{k, a, b}, tbl), mem.tl(PM.Fd(3n, m, c), PM.Fd(4n, m, c), Con{PM.Fd(4n, m, c), Nil{}}, mem.hd(PM.Fd(4n, m, c), Nil{})),
              e => hh => is.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(4n, m, c), tbl, hz0, hzs, e, hh), pb)))))
    case C.Term.Eql{+a, +b, +d}:
      (+nd, r) = h
      (pa, r2) = r
      (pb, pd) = r2
      PM.isc.at(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), c), C.Cir.Cells.get(m, c), C.Term.Eql{a, b, d}, PM.cl.go(m, c, z, x, hc),
            (nd, (part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(2n, m, c), 16, 7, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Eql{a, b, d}, 16, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.Eql{a, b, d}, tbl), mem.hd(PM.Fd(2n, m, c), Con{PM.Fd(3n, m, c), Con{PM.Fd(4n, m, c), Nil{}}}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, c), tbl, hz0, hzs, e, hh), pa),
              (part.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(3n, m, c), 16, 7, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Eql{a, b, d}, 16, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.Eql{a, b, d}, tbl), mem.tl(PM.Fd(2n, m, c), PM.Fd(3n, m, c), Con{PM.Fd(3n, m, c), Con{PM.Fd(4n, m, c), Nil{}}}, mem.hd(PM.Fd(3n, m, c), Con{PM.Fd(4n, m, c), Nil{}})),
              e => hh => is.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, c), tbl, hz0, hzs, e, hh), pb),
              part.fz(d, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(4n, m, c), 16, 7, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Eql{a, b, d}, 16, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.Eql{a, b, d}, tbl), mem.tl(PM.Fd(2n, m, c), PM.Fd(4n, m, c), Con{PM.Fd(3n, m, c), Con{PM.Fd(4n, m, c), Nil{}}}, mem.tl(PM.Fd(3n, m, c), PM.Fd(4n, m, c), Con{PM.Fd(4n, m, c), Nil{}}, mem.hd(PM.Fd(4n, m, c), Nil{}))),
              e => hh => is.fz(d, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(4n, m, c), tbl, hz0, hzs, e, hh), pd)))))
    case C.Term.Rwt{+a, +b, +d}:
      (+nd, r) = h
      (pa, r2) = r
      (pb, pd) = r2
      PM.isc.at(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), c), C.Cir.Cells.get(m, c), C.Term.Rwt{a, b, d}, PM.cl.go(m, c, z, x, hc),
            (nd, (part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(2n, m, c), 18, 7, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Rwt{a, b, d}, 18, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.Rwt{a, b, d}, tbl), mem.hd(PM.Fd(2n, m, c), Con{PM.Fd(3n, m, c), Con{PM.Fd(4n, m, c), Nil{}}}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, c), tbl, hz0, hzs, e, hh), pa),
              (part.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(3n, m, c), 18, 7, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Rwt{a, b, d}, 18, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.Rwt{a, b, d}, tbl), mem.tl(PM.Fd(2n, m, c), PM.Fd(3n, m, c), Con{PM.Fd(3n, m, c), Con{PM.Fd(4n, m, c), Nil{}}}, mem.hd(PM.Fd(3n, m, c), Con{PM.Fd(4n, m, c), Nil{}})),
              e => hh => is.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, c), tbl, hz0, hzs, e, hh), pb),
              part.fz(d, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(4n, m, c), 18, 7, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), C.Term.Rwt{a, b, d}, 18, nd), {==}, tbl.mask(m, im, fi, nx, C.Term.Rwt{a, b, d}, tbl), mem.tl(PM.Fd(2n, m, c), PM.Fd(4n, m, c), Con{PM.Fd(3n, m, c), Con{PM.Fd(4n, m, c), Nil{}}}, mem.tl(PM.Fd(3n, m, c), PM.Fd(4n, m, c), Con{PM.Fd(4n, m, c), Nil{}}, mem.hd(PM.Fd(4n, m, c), Nil{}))),
              e => hh => is.fz(d, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(4n, m, c), tbl, hz0, hzs, e, hh), pd)))))


# A store to a cell that nothing points to: the heap
# --------------------------------------------------
#
# Fs of a cell o reads o and the table's cell of o's tag. A store to z keeps
# Fs of every other cell o, when z is not the table's cell that o reads
# (TblR); and Fs of z, when z holds no pointer before or after (Nil). So it
# keeps every count Pc and Ptr, and with them Cnt, Pts, PendOK and Chain.

# the term cell o does not read its mask at z
def TblAt(+m: C.Cir.Cells, +o: U32, +z: U32) -> Bool:
  Bool.or(Bool.not(U32.is_lt(PM.Tg(m, o), 19)), Bool.not(U32.is_eq(U32.add(345, PM.Tg(m, o)), z)))

# none of the n cells from o reads its mask at z
def TblR(n: Nat, +m: C.Cir.Cells, +o: U32, +z: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+k:
      Bool.and(TblAt(m, o, z), TblR(k, m, U32.inc(o), z))

def not.t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      PM.bool.ft({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def tbl.ne(l: Bool, e: Bool, ht: {Bool.or(Bool.not(l), Bool.not(e)) == True{} : Bool}, el: {l == True{} : Bool}) -> {e == False{} : Bool}:
  match l:
    case True{}:
      not.t(e, ht)
    case False{}:
      PM.bool.ft({e == False{} : Bool}, el)

# Fs of the cell o, by its value y, with the mask a
def FsK(b: Bool, +a: U32, +y: C.Cir.Cell, +ps: List<&2, U32>, +o: U32) -> List<&2, U32>:
  +tg = PM.TgW(C.Cir.Cell.get(0n, y))
  Bool.pick(List<&2, U32>, b, PM.Fs.term(a, C.Cir.Cell.get(2n, y), C.Cir.Cell.get(3n, y), C.Cir.Cell.get(4n, y)),
    Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, tg), U32.is_le(tg, 40)), Bool.not(PM.Mem(ps, o))),
      Con{C.Cir.Cell.get(2n, y), PM.Fs.opt(U32.is_eq(tg, 38), C.Cir.Cell.get(3n, y), Nil{})},
      Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(tg, 41), PM.FlW(C.Cir.Cell.get(0n, y), 4096)), Bool.not(PM.Mem(ps, o))),
        [C.Cir.Cell.get(2n, y)], Nil{})))

def fsk.b(b: Bool, +a1: U32, +a2: U32, +y: C.Cir.Cell, +ps: List<&2, U32>, +o: U32, h: {b == True{} : Bool} -> {a1 == a2 : U32}) ->
  {FsK(b, a1, y, ps, o) == FsK(b, a2, y, ps, o) : List<&2, U32>}:
  match b:
    case False{}:
      {==}
    case True{}:
      %h({==}) : {FsK(True{}, a1, y, ps, o) == FsK(True{}, _, y, ps, o) : List<&2, U32>}
      {==}

# a store to z keeps Fs of another cell o, that does not read its mask at z
def fs.eq(+m: C.Cir.Cells, +z: U32, +x: C.Cir.Cell, +ps: List<&2, U32>, +o: U32, ne: {U32.is_eq(o, z) == False{} : Bool},
  ht: {TblAt(m, o, z) == True{} : Bool}) -> {PM.Fs(C.Cir.Cells.set(m, z, x), ps, o) == PM.Fs(m, ps, o) : List<&2, U32>}:
  +M2 = C.Cir.Cells.set(m, z, x)
  +Y = C.Cir.Cells.get(m, o)
  +tg = PM.TgW(C.Cir.Cell.get(0n, Y))
  %Equal.sym(C.Cir.Cell, C.Cir.Cells.get(M2, o), Y, PM.cl.go(m, o, z, x, ne)) :
    {FsK(U32.is_lt(PM.TgW(C.Cir.Cell.get(0n, _)), 19), PM.Fd(2n, M2, U32.add(345, PM.TgW(C.Cir.Cell.get(0n, _)))), _, ps, o) ==
      FsK(U32.is_lt(tg, 19), PM.Fd(2n, m, U32.add(345, tg)), Y, ps, o) : List<&2, U32>}
  fsk.b(U32.is_lt(tg, 19), PM.Fd(2n, M2, U32.add(345, tg)), PM.Fd(2n, m, U32.add(345, tg)), Y, ps, o,
    e => Equal.cong(C.Cir.Cell, U32, w => C.Cir.Cell.get(2n, w), C.Cir.Cells.get(M2, U32.add(345, tg)), C.Cir.Cells.get(m, U32.add(345, tg)),
      PM.cl.go(m, U32.add(345, tg), z, x, tbl.ne(U32.is_lt(tg, 19), U32.is_eq(U32.add(345, tg), z), ht, e))))

# a store to z keeps Fs of every cell: of z too, when it holds no pointer
# before or after
def fs.eq2(b: Bool, +m: C.Cir.Cells, +z: U32, +x: C.Cir.Cell, +ps: List<&2, U32>, +o: U32, eb: {U32.is_eq(o, z) == b : Bool},
  ht: {TblAt(m, o, z) == True{} : Bool}, hf0: {PM.Fs(m, ps, z) == Nil{} : List<&2, U32>},
  hf1: {PM.Fs(C.Cir.Cells.set(m, z, x), ps, z) == Nil{} : List<&2, U32>}) ->
  {PM.Fs(C.Cir.Cells.set(m, z, x), ps, o) == PM.Fs(m, ps, o) : List<&2, U32>}:
  match b:
    case False{}:
      fs.eq(m, z, x, ps, o, eb, ht)
    case True{}:
      %Equal.sym(U32, o, z, PM.u32.eq(o, z, eb)) : {PM.Fs(C.Cir.Cells.set(m, z, x), ps, _) == PM.Fs(m, ps, _) : List<&2, U32>}
      Equal.trans(List<&2, U32>, PM.Fs(C.Cir.Cells.set(m, z, x), ps, z), Nil{}, PM.Fs(m, ps, z), hf1, Equal.sym(List<&2, U32>, PM.Fs(m, ps, z), Nil{}, hf0))

def fs.all(+m: C.Cir.Cells, +z: U32, +x: C.Cir.Cell, +ps: List<&2, U32>, +o: U32,
  ht: {TblAt(m, o, z) == True{} : Bool}, hf0: {PM.Fs(m, ps, z) == Nil{} : List<&2, U32>},
  hf1: {PM.Fs(C.Cir.Cells.set(m, z, x), ps, z) == Nil{} : List<&2, U32>}) ->
  {PM.Fs(C.Cir.Cells.set(m, z, x), ps, o) == PM.Fs(m, ps, o) : List<&2, U32>}:
  fs.eq2(U32.is_eq(o, z), m, z, x, ps, o, {==}, ht, hf0, hf1)

# a store to z keeps the pointers that the n cells from o hold
def Pc.eq(n: Nat, +m: C.Cir.Cells, +z: U32, +x: C.Cir.Cell, +ps: List<&2, U32>, +o: U32, +c: U32,
  +hf0: {PM.Fs(m, ps, z) == Nil{} : List<&2, U32>}, +hf1: {PM.Fs(C.Cir.Cells.set(m, z, x), ps, z) == Nil{} : List<&2, U32>},
  ht: {TblR(n, m, o, z) == True{} : Bool}) -> {PM.Pc(n, C.Cir.Cells.set(m, z, x), ps, o, c) == PM.Pc(n, m, ps, o, c) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      +M2 = C.Cir.Cells.set(m, z, x)
      +ht2 = ht
      +e1 = fs.all(m, z, x, ps, o, and.l(TblAt(m, o, z), TblR(k, m, U32.inc(o), z), ht2), hf0, hf1)
      +e2 = Pc.eq(k, m, z, x, ps, U32.inc(o), c, hf0, hf1, and.r(TblAt(m, o, z), TblR(k, m, U32.inc(o), z), ht2))
      %Equal.sym(List<&2, U32>, PM.Fs(M2, ps, o), PM.Fs(m, ps, o), e1) :
        {Nat.add(PM.RcL(_, c), PM.Pc(k, M2, ps, U32.inc(o), c)) == Nat.add(PM.RcL(PM.Fs(m, ps, o), c), PM.Pc(k, m, ps, U32.inc(o), c)) : Nat}
      %Equal.sym(Nat, PM.Pc(k, M2, ps, U32.inc(o), c), PM.Pc(k, m, ps, U32.inc(o), c), e2) :
        {Nat.add(PM.RcL(PM.Fs(m, ps, o), c), _) == Nat.add(PM.RcL(PM.Fs(m, ps, o), c), PM.Pc(k, m, ps, U32.inc(o), c)) : Nat}
      {==}

# and every count
def Ptr.eq(+n: Nat, +m: C.Cir.Cells, +z: U32, +x: C.Cir.Cell, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +c: U32,
  hf0: {PM.Fs(m, ps, z) == Nil{} : List<&2, U32>}, hf1: {PM.Fs(C.Cir.Cells.set(m, z, x), ps, z) == Nil{} : List<&2, U32>},
  ht: {TblR(n, m, fi, z) == True{} : Bool}) -> {PM.Ptr(n, C.Cir.Cells.set(m, z, x), fi, ps, rs, c) == PM.Ptr(n, m, fi, ps, rs, c) : Nat}:
  Equal.cong(Nat, Nat, w => Nat.add(w, PM.RcL(rs, c)), PM.Pc(n, C.Cir.Cells.set(m, z, x), ps, fi, c), PM.Pc(n, m, ps, fi, c),
    Pc.eq(n, m, z, x, ps, fi, c, hf0, hf1, ht))

def and.i(a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      PM.bool.ft({False{} == True{} : Bool}, ha)

def or.l(a: Bool, -b: Bool, h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      PM.bool.ft({b == True{} : Bool}, h)

def or.f.l(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, N.true_ne_false(h))
    case False{}:
      {==}

def or.f.r(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, N.true_ne_false(h))
    case False{}:
      h

def Disc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def add0.l(a: Nat, -b: Nat, h: {Nat.add(a, b) == 0n : Nat}) -> {a == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, (%h : Disc(_); Unit{}))

def add0.r(a: Nat, -b: Nat, h: {Nat.add(a, b) == 0n : Nat}) -> {b == 0n : Nat}:
  match a:
    case 0n:
      h
    case 1n+p:
      Empty.absurd({b == 0n : Nat}, (%h : Disc(_); Unit{}))

# Nat.of(b) + r = 0 gives b false
def of.z(b: Bool, -r: Nat, h: {Nat.add(PM.Nat.of(b), r) == 0n : Nat}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, (%h : Disc(_); Unit{}))
    case False{}:
      {==}

def ge.of(c: Cmp, h: {Cmp.is_lt(c) == False{} : Bool}) -> {Cmp.is_ge(c) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({False{} == True{} : Bool}, N.true_ne_false(h))
    case EQ{}:
      {==}
    case GT{}:
      {==}

# Cnt at a cell, by its value y and its pointers P
def CntC(+y: C.Cir.Cell, +P: Nat, +ps: List<&2, U32>, +o: U32) -> Bool:
  Bool.or(Bool.not(U32.is_lt(PM.TgW(C.Cir.Cell.get(0n, y)), 19)), Bool.or(PM.FlW(C.Cir.Cell.get(0n, y), 1024), Bool.or(PM.Mem(ps, o),
    Nat.is_eq(U32.to_nat(C.Cir.Cell.get(1n, y)), P))))

def cnt.at(b: Bool, +m: C.Cir.Cells, +z: U32, +x: C.Cir.Cell, +o: U32, +n: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  eb: {U32.is_eq(o, z) == b : Bool}, hxt: {U32.is_lt(PM.TgW(C.Cir.Cell.get(0n, x)), 19) == False{} : Bool},
  hP: {PM.Ptr(n, C.Cir.Cells.set(m, z, x), fi, ps, rs, o) == PM.Ptr(n, m, fi, ps, rs, o) : Nat},
  h: {CntC(C.Cir.Cells.get(m, o), PM.Ptr(n, m, fi, ps, rs, o), ps, o) == True{} : Bool}) ->
  {CntC(C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), o), PM.Ptr(n, C.Cir.Cells.set(m, z, x), fi, ps, rs, o), ps, o) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(U32, o, z, PM.u32.eq(o, z, eb)) : {CntC(C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), _), PM.Ptr(n, C.Cir.Cells.set(m, z, x), fi, ps, rs, _), ps, _) == True{} : Bool}
      %Equal.sym(C.Cir.Cell, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), z), x, PM.cl.gs(m, z, x)) : {CntC(_, PM.Ptr(n, C.Cir.Cells.set(m, z, x), fi, ps, rs, z), ps, z) == True{} : Bool}
      or.l(Bool.not(U32.is_lt(PM.TgW(C.Cir.Cell.get(0n, x)), 19)), Bool.or(PM.FlW(C.Cir.Cell.get(0n, x), 1024), Bool.or(PM.Mem(ps, z),
        Nat.is_eq(U32.to_nat(C.Cir.Cell.get(1n, x)), PM.Ptr(n, C.Cir.Cells.set(m, z, x), fi, ps, rs, z)))),
        (%Equal.sym(Bool, U32.is_lt(PM.TgW(C.Cir.Cell.get(0n, x)), 19), False{}, hxt) : {Bool.not(_) == True{} : Bool}; {==}))
    case False{}:
      %Equal.sym(C.Cir.Cell, C.Cir.Cells.get(C.Cir.Cells.set(m, z, x), o), C.Cir.Cells.get(m, o), PM.cl.go(m, o, z, x, eb)) : {CntC(_, PM.Ptr(n, C.Cir.Cells.set(m, z, x), fi, ps, rs, o), ps, o) == True{} : Bool}
      %Equal.sym(Nat, PM.Ptr(n, C.Cir.Cells.set(m, z, x), fi, ps, rs, o), PM.Ptr(n, m, fi, ps, rs, o), hP) : {CntC(C.Cir.Cells.get(m, o), _, ps, o) == True{} : Bool}
      h

# a store to z, which gets a cell of the machine's own kinds (a tag of 32 or
# more), keeps the counts
def Cnt.fz(k: Nat, +m: C.Cir.Cells, +z: U32, +x: C.Cir.Cell, +o: U32, +n: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  +hf0: {PM.Fs(m, ps, z) == Nil{} : List<&2, U32>}, +hf1: {PM.Fs(C.Cir.Cells.set(m, z, x), ps, z) == Nil{} : List<&2, U32>},
  +htN: {TblR(n, m, fi, z) == True{} : Bool}, +hxt: {U32.is_lt(PM.TgW(C.Cir.Cell.get(0n, x)), 19) == False{} : Bool},
  h: {PM.Cnt(k, m, o, n, fi, ps, rs) == True{} : Bool}) -> {PM.Cnt(k, C.Cir.Cells.set(m, z, x), o, n, fi, ps, rs) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +M2 = C.Cir.Cells.set(m, z, x)
      +h2 = h
      and.i(CntC(C.Cir.Cells.get(M2, o), PM.Ptr(n, M2, fi, ps, rs, o), ps, o), PM.Cnt(j, M2, U32.inc(o), n, fi, ps, rs),
        cnt.at(U32.is_eq(o, z), m, z, x, o, n, fi, ps, rs, {==}, hxt, Ptr.eq(n, m, z, x, fi, ps, rs, o, hf0, hf1, htN),
          and.l(CntC(C.Cir.Cells.get(m, o), PM.Ptr(n, m, fi, ps, rs, o), ps, o), PM.Cnt(j, m, U32.inc(o), n, fi, ps, rs), h2)),
        Cnt.fz(j, m, z, x, U32.inc(o), n, fi, ps, rs, hf0, hf1, htN, hxt,
          and.r(CntC(C.Cir.Cells.get(m, o), PM.Ptr(n, m, fi, ps, rs, o), ps, o), PM.Cnt(j, m, U32.inc(o), n, fi, ps, rs), h2)))

# the pointers xs, none of them z, point to term cells after a store to z
def lt.fz(xs: List<&2, U32>, +m: C.Cir.Cells, +z: U32, +x: C.Cir.Cell, +nx: U32, hr: {PM.RcL(xs, z) == 0n : Nat},
  h: {PM.Lt.all(xs, m, nx) == True{} : Bool}) -> {PM.Lt.all(xs, C.Cir.Cells.set(m, z, x), nx) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +M2 = C.Cir.Cells.set(m, z, x)
      +hr2 = hr
      +h2 = h
      +ne = of.z(U32.is_eq(y, z), PM.RcL(rest, z), hr2)
      %Equal.sym(C.Cir.Cell, C.Cir.Cells.get(M2, y), C.Cir.Cells.get(m, y), PM.cl.go(m, y, z, x, ne)) :
        {Bool.and(Bool.and(U32.is_lt(y, nx), U32.is_lt(U32.and(C.Cir.Cell.get(0n, _), 63), 19)), PM.Lt.all(rest, M2, nx)) == True{} : Bool}
      and.i(Bool.and(U32.is_lt(y, nx), U32.is_lt(PM.Tg(m, y), 19)), PM.Lt.all(rest, M2, nx),
        and.l(Bool.and(U32.is_lt(y, nx), U32.is_lt(PM.Tg(m, y), 19)), PM.Lt.all(rest, m, nx), h2),
        lt.fz(rest, m, z, x, nx, add0.r(PM.Nat.of(U32.is_eq(y, z)), PM.RcL(rest, z), hr2),
          and.r(Bool.and(U32.is_lt(y, nx), U32.is_lt(PM.Tg(m, y), 19)), PM.Lt.all(rest, m, nx), h2)))

def pts.at(b: Bool, +m: C.Cir.Cells, +z: U32, +x: C.Cir.Cell, +ps: List<&2, U32>, +o: U32, +nx: U32, eb: {U32.is_eq(o, z) == b : Bool},
  hf1: {PM.Fs(C.Cir.Cells.set(m, z, x), ps, z) == Nil{} : List<&2, U32>}, ht: {TblAt(m, o, z) == True{} : Bool},
  hr: {PM.RcL(PM.Fs(m, ps, o), z) == 0n : Nat}, h: {PM.Lt.all(PM.Fs(m, ps, o), m, nx) == True{} : Bool}) ->
  {PM.Lt.all(PM.Fs(C.Cir.Cells.set(m, z, x), ps, o), C.Cir.Cells.set(m, z, x), nx) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(U32, o, z, PM.u32.eq(o, z, eb)) : {PM.Lt.all(PM.Fs(C.Cir.Cells.set(m, z, x), ps, _), C.Cir.Cells.set(m, z, x), nx) == True{} : Bool}
      %Equal.sym(List<&2, U32>, PM.Fs(C.Cir.Cells.set(m, z, x), ps, z), Nil{}, hf1) : {PM.Lt.all(_, C.Cir.Cells.set(m, z, x), nx) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(List<&2, U32>, PM.Fs(C.Cir.Cells.set(m, z, x), ps, o), PM.Fs(m, ps, o), fs.eq(m, z, x, ps, o, eb, ht)) : {PM.Lt.all(_, C.Cir.Cells.set(m, z, x), nx) == True{} : Bool}
      lt.fz(PM.Fs(m, ps, o), m, z, x, nx, hr, h)

# and keeps that every pointer points to a term cell
def Pts.fz(k: Nat, +m: C.Cir.Cells, +z: U32, +x: C.Cir.Cell, +ps: List<&2, U32>, +o: U32, +nx: U32,
  +hf1: {PM.Fs(C.Cir.Cells.set(m, z, x), ps, z) == Nil{} : List<&2, U32>}, hz: {PM.Pc(k, m, ps, o, z) == 0n : Nat},
  ht: {TblR(k, m, o, z) == True{} : Bool}, h: {PM.Pts(k, m, ps, o, nx) == True{} : Bool}) ->
  {PM.Pts(k, C.Cir.Cells.set(m, z, x), ps, o, nx) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +M2 = C.Cir.Cells.set(m, z, x)
      +hz2 = hz
      +ht2 = ht
      +h2 = h
      and.i(PM.Lt.all(PM.Fs(M2, ps, o), M2, nx), PM.Pts(j, M2, ps, U32.inc(o), nx),
        pts.at(U32.is_eq(o, z), m, z, x, ps, o, nx, {==}, hf1, and.l(TblAt(m, o, z), TblR(j, m, U32.inc(o), z), ht2),
          add0.l(PM.RcL(PM.Fs(m, ps, o), z), PM.Pc(j, m, ps, U32.inc(o), z), hz2),
          and.l(PM.Lt.all(PM.Fs(m, ps, o), m, nx), PM.Pts(j, m, ps, U32.inc(o), nx), h2)),
        Pts.fz(j, m, z, x, ps, U32.inc(o), nx, hf1, add0.r(PM.RcL(PM.Fs(m, ps, o), z), PM.Pc(j, m, ps, U32.inc(o), z), hz2),
          and.r(TblAt(m, o, z), TblR(j, m, U32.inc(o), z), ht2), and.r(PM.Lt.all(PM.Fs(m, ps, o), m, nx), PM.Pts(j, m, ps, U32.inc(o), nx), h2)))

# the pend list's cells, none of them z
def PendOK.fz(qs: List<&2, U32>, +ps: List<&2, U32>, +m: C.Cir.Cells, +z: U32, +x: C.Cir.Cell, +fi: U32, +nx: U32, +rs: List<&2, U32>,
  +hf0: {PM.Fs(m, ps, z) == Nil{} : List<&2, U32>}, +hf1: {PM.Fs(C.Cir.Cells.set(m, z, x), ps, z) == Nil{} : List<&2, U32>},
  +htN: {TblR(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, z) == True{} : Bool}, hq: {PM.Mem(qs, z) == False{} : Bool},
  h: PM.PendOK(qs, ps, m, fi, nx, rs)) -> PM.PendOK(qs, ps, C.Cir.Cells.set(m, z, x), fi, nx, rs):
  match qs:
    case Nil{}:
      Unit{}
    case Con{+p, +rest}:
      (ho, r1) = h
      (hs, r2) = r1
      (hp0, r3) = r2
      +M2 = C.Cir.Cells.set(m, z, x)
      +hq2 = hq
      +ne = or.f.l(U32.is_eq(p, z), PM.Mem(rest, z), hq2)
      (ho, ((%Equal.sym(C.Cir.Cell, C.Cir.Cells.get(M2, p), C.Cir.Cells.get(m, p), PM.cl.go(m, p, z, x, ne)) :
          {U32.is_ne(U32.and(C.Cir.Cell.get(0n, _), 1024), 0) == False{} : Bool}; hs),
        ((%Equal.sym(Nat, PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), M2, fi, ps, rs, p), PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, p),
            Ptr.eq(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, z, x, fi, ps, rs, p, hf0, hf1, htN)) : {_ == 0n : Nat}; hp0),
          PendOK.fz(rest, ps, m, z, x, fi, nx, rs, hf0, hf1, htN, or.f.r(U32.is_eq(p, z), PM.Mem(rest, z), hq2), r3))))

# the pend list's links, none of them at z
def Chain.fz(qs: List<&2, U32>, +m: C.Cir.Cells, +z: U32, +x: C.Cir.Cell, +p: U32, hq: {PM.Mem(qs, z) == False{} : Bool},
  h: PM.Chain(qs, m, p)) -> PM.Chain(qs, C.Cir.Cells.set(m, z, x), p):
  match qs:
    case Nil{}:
      h
    case Con{+y, +rest}:
      (e1, r1) = h
      (e2, r2) = r1
      +M2 = C.Cir.Cells.set(m, z, x)
      +hq2 = hq
      +ne = or.f.l(U32.is_eq(y, z), PM.Mem(rest, z), hq2)
      (e1, (e2, (%Equal.sym(U32, PM.Fd(1n, M2, y), PM.Fd(1n, m, y),
          Equal.cong(C.Cir.Cell, U32, w => C.Cir.Cell.get(1n, w), C.Cir.Cells.get(M2, y), C.Cir.Cells.get(m, y), PM.cl.go(m, y, z, x, ne))) :
          PM.Chain(rest, M2, _);
        Chain.fz(rest, m, z, x, PM.Fd(1n, m, y), or.f.r(U32.is_eq(y, z), PM.Mem(rest, z), hq2), r2))))

# a store to z, out of the pend list, with no pointer to it, which gets a
# cell of the machine's own kinds with no pointer in it, keeps the heap
def Heap.fz(+m: C.Cir.Cells, +nx: U32, +fi: U32, +rs: List<&2, U32>, +pend: U32, +ps: List<&2, U32>, +z: U32, +x: C.Cir.Cell,
  +hf0: {PM.Fs(m, ps, z) == Nil{} : List<&2, U32>}, +hf1: {PM.Fs(C.Cir.Cells.set(m, z, x), ps, z) == Nil{} : List<&2, U32>},
  +htN: {TblR(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, z) == True{} : Bool}, +hzm: {PM.Mem(ps, z) == False{} : Bool},
  hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat},
  hxt: {U32.is_lt(PM.TgW(C.Cir.Cell.get(0n, x)), 19) == False{} : Bool},
  h: PM.Heap(m, nx, fi, rs, pend, ps)) -> PM.Heap(C.Cir.Cells.set(m, z, x), nx, fi, rs, pend, ps):
  (hc, r1) = h
  (hp, r2) = r1
  (hcn, r3) = r2
  (hpt, hr) = r3
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  (Chain.fz(ps, m, z, x, pend, hzm, hc), (PendOK.fz(ps, ps, m, z, x, fi, nx, rs, hf0, hf1, htN, hzm, hp),
    (Cnt.fz(n, m, z, x, fi, n, fi, ps, rs, hf0, hf1, htN, hxt, hcn),
    (Pts.fz(n, m, z, x, ps, fi, nx, hf1, add0.l(PM.Pc(n, m, ps, fi, z), PM.RcL(rs, z), hz0), htN, hpt), hr))))

# A store to a cell that nothing points to: the terms
# --------------------------------------------------

# no cell of cs is z
def NeAll(cs: List<&2, U32>, +z: U32) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, rest}:
      Bool.not(U32.is_eq(c, z)) && NeAll(rest, z)

def neall.hd(+c: U32, +z: U32, -rest: List<&2, U32>, h: {NeAll(Con{c, rest}, z) == True{} : Bool}) -> {U32.is_eq(c, z) == False{} : Bool}:
  not.t(U32.is_eq(c, z), and.l(Bool.not(U32.is_eq(c, z)), NeAll(rest, z), h))

def neall.tl(+c: U32, +z: U32, -rest: List<&2, U32>, h: {NeAll(Con{c, rest}, z) == True{} : Bool}) -> {NeAll(rest, z) == True{} : Bool}:
  and.r(Bool.not(U32.is_eq(c, z)), NeAll(rest, z), h)

def neall.cons(+c: U32, +z: U32, -rest: List<&2, U32>, ne: {U32.is_eq(c, z) == False{} : Bool}, h: {NeAll(rest, z) == True{} : Bool}) ->
  {NeAll(Con{c, rest}, z) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(c, z), False{}, ne) : {Bool.and(Bool.not(_), NeAll(rest, z)) == True{} : Bool}
  h

# no root is z, when no root points to z
def neall.rcl(rs: List<&2, U32>, +z: U32, h: {PM.RcL(rs, z) == 0n : Nat}) -> {NeAll(rs, z) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      +h2 = h
      neall.cons(r, z, rest, of.z(U32.is_eq(r, z), PM.RcL(rest, z), h2),
        neall.rcl(rest, z, add0.r(PM.Nat.of(U32.is_eq(r, z)), PM.RcL(rest, z), h2)))

def lt0.le1(p: Nat, h: {Nat.is_lt(0n, p) == True{} : Bool}) -> N.Le(1n, p):
  match p:
    case 0n:
      PM.bool.ft(N.Le(1n, 0n), h)
    case 1n+q:
      N.le_zero(q)

def held.ne(f: Bool, +m: C.Cir.Cells, +c: U32, +z: U32, +n: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  ef: {PM.Fl(m, c, 1024) == f : Bool}, h: {Bool.or(f, Nat.is_lt(0n, PM.Ptr(n, m, fi, ps, rs, c))) == True{} : Bool},
  hz0: {PM.Ptr(n, m, fi, ps, rs, z) == 0n : Nat}, hzs: {PM.Fl(m, z, 1024) == False{} : Bool}) -> {U32.is_eq(c, z) == False{} : Bool}:
  match f:
    case True{}:
      ne.st(U32.is_eq(c, z), m, c, z, {==}, ef, hzs)
    case False{}:
      ne.ptr(U32.is_eq(c, z), c, z, n, m, fi, ps, rs, {==}, lt0.le1(PM.Ptr(n, m, fi, ps, rs, c), h), hz0)

# no borrowed cell is z, which is not STATIC and has no pointer
def neall.held(bs: List<&2, PM.Rt>, +m: C.Cir.Cells, +z: U32, +n: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  +hz0: {PM.Ptr(n, m, fi, ps, rs, z) == 0n : Nat}, +hzs: {PM.Fl(m, z, 1024) == False{} : Bool}, h: PM.Held(m, n, fi, ps, rs, bs)) ->
  {NeAll(PM.Rt.cells(bs), z) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Con{PM.Rt{+c, _}, +rest}:
      (hh, hr) = h
      neall.cons(c, z, PM.Rt.cells(rest), held.ne(PM.Fl(m, c, 1024), m, c, z, n, fi, ps, rs, {==}, hh, hz0, hzs),
        neall.held(rest, m, z, n, fi, ps, rs, hz0, hzs, hr))

# a store to z keeps the terms of cells that are not z
def Rts.fz(xs: List<&2, PM.Rt>, +ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32, +x: C.Cir.Cell, +tbl: PM.Tbl(m, im, fi, nx),
  +hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat}, +hzs: {PM.Fl(m, z, 1024) == False{} : Bool},
  hn: {NeAll(PM.Rt.cells(xs), z) == True{} : Bool}, h: PM.Rts(ds, m, im, fi, nx, ks, img, xs)) ->
  PM.Rts(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, xs):
  match xs:
    case Nil{}:
      Unit{}
    case Con{PM.Rt{+c, +u}, +rest}:
      (hc, hr) = h
      +hn2 = hn
      (is.fz(u, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, tbl, hz0, hzs, neall.hd(c, z, PM.Rt.cells(rest), hn2), hc),
        Rts.fz(rest, ds, m, im, fi, nx, ks, img, ps, rs, z, x, tbl, hz0, hzs, neall.tl(c, z, PM.Rt.cells(rest), hn2), hr))

# a store to z keeps Held
def Held.fz(bs: List<&2, PM.Rt>, +m: C.Cir.Cells, +n: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32, +x: C.Cir.Cell,
  +hf0: {PM.Fs(m, ps, z) == Nil{} : List<&2, U32>}, +hf1: {PM.Fs(C.Cir.Cells.set(m, z, x), ps, z) == Nil{} : List<&2, U32>},
  +htN: {TblR(n, m, fi, z) == True{} : Bool}, hn: {NeAll(PM.Rt.cells(bs), z) == True{} : Bool}, h: PM.Held(m, n, fi, ps, rs, bs)) ->
  PM.Held(C.Cir.Cells.set(m, z, x), n, fi, ps, rs, bs):
  match bs:
    case Nil{}:
      Unit{}
    case Con{PM.Rt{+c, _}, +rest}:
      (hh, hr) = h
      +hn2 = hn
      +M2 = C.Cir.Cells.set(m, z, x)
      ((%Equal.sym(C.Cir.Cell, C.Cir.Cells.get(M2, c), C.Cir.Cells.get(m, c), PM.cl.go(m, c, z, x, neall.hd(c, z, PM.Rt.cells(rest), hn2))) :
          {Bool.or(U32.is_ne(U32.and(C.Cir.Cell.get(0n, _), 1024), 0), Nat.is_lt(0n, PM.Ptr(n, M2, fi, ps, rs, c))) == True{} : Bool};
        %Equal.sym(Nat, PM.Ptr(n, M2, fi, ps, rs, c), PM.Ptr(n, m, fi, ps, rs, c), Ptr.eq(n, m, z, x, fi, ps, rs, c, hf0, hf1, htN)) :
          {Bool.or(PM.Fl(m, c, 1024), Nat.is_lt(0n, _)) == True{} : Bool};
        hh),
        Held.fz(rest, m, n, fi, ps, rs, z, x, hf0, hf1, htN, neall.tl(c, z, PM.Rt.cells(rest), hn2), hr))

# Fs of a frame, past the test of its tag
def FsR(c: Bool, +m: C.Cir.Cells, +ps: List<&2, U32>, +o: U32, +tg: U32) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, c, Con{PM.Fd(2n, m, o), PM.Fs.opt(U32.is_eq(tg, 38), PM.Fd(3n, m, o), Nil{})},
    Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(tg, 41), PM.FlW(PM.Fd(0n, m, o), 4096)), Bool.not(PM.Mem(ps, o))),
      [PM.Fd(2n, m, o)], Nil{}))

# the pointers of a frame out of the pend list: its field 2, and 3 for Rwt
def fs.frame(+m: C.Cir.Cells, +ps: List<&2, U32>, +o: U32, +tg: U32, etag: {PM.TgW(PM.Fd(0n, m, o)) == tg : U32},
  hlt: {U32.is_lt(tg, 32) == False{} : Bool}, hle: {U32.is_le(tg, 40) == True{} : Bool}, hm: {PM.Mem(ps, o) == False{} : Bool}) ->
  {PM.Fs(m, ps, o) == Con{PM.Fd(2n, m, o), PM.Fs.opt(U32.is_eq(tg, 38), PM.Fd(3n, m, o), Nil{})} : List<&2, U32>}:
  +R = {Con{PM.Fd(2n, m, o), PM.Fs.opt(U32.is_eq(tg, 38), PM.Fd(3n, m, o), Nil{})} : List<&2, U32>}
  %Equal.sym(U32, PM.TgW(PM.Fd(0n, m, o)), tg, etag) : {FsP(U32.is_lt(_, 19), m, ps, o, _) == R : List<&2, U32>}
  %Equal.sym(Bool, U32.is_lt(tg, 32), False{}, hlt) : {FsP(_, m, ps, o, tg) == R : List<&2, U32>}
  %Equal.sym(Bool, U32.is_le(tg, 40), True{}, hle) : {FsR(Bool.and(_, Bool.not(PM.Mem(ps, o))), m, ps, o, tg) == R : List<&2, U32>}
  %Equal.sym(Bool, PM.Mem(ps, o), False{}, hm) : {FsR(Bool.and(True{}, Bool.not(_)), m, ps, o, tg) == R : List<&2, U32>}
  {==}

def fk.lt(kind: PM.FK) -> {U32.is_lt(PM.FK.tag(kind), 32) == False{} : Bool}:
  match kind:
    case PM.FK.arg{}:
      {==}
    case PM.FK.val{}:
      {==}
    case PM.FK.fun{}:
      {==}
    case PM.FK.let{}:
      {==}
    case PM.FK.tupb{}:
      {==}
    case PM.FK.tupa{}:
      {==}
    case PM.FK.rwt{}:
      {==}
    case PM.FK.minb{}:
      {==}
    case PM.FK.mina{}:
      {==}

def fk.le(kind: PM.FK) -> {U32.is_le(PM.FK.tag(kind), 40) == True{} : Bool}:
  match kind:
    case PM.FK.arg{}:
      {==}
    case PM.FK.val{}:
      {==}
    case PM.FK.fun{}:
      {==}
    case PM.FK.let{}:
      {==}
    case PM.FK.tupb{}:
      {==}
    case PM.FK.tupa{}:
      {==}
    case PM.FK.rwt{}:
      {==}
    case PM.FK.minb{}:
      {==}
    case PM.FK.mina{}:
      {==}

# a part y of a frame fr is not z, which has no pointer
def fr.ne(+m: C.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +fr: U32, +y: U32, +z: U32, +tg: U32,
  etag: {PM.TgW(PM.Fd(0n, m, fr)) == tg : U32}, hlt: {U32.is_lt(tg, 32) == False{} : Bool}, hle: {U32.is_le(tg, 40) == True{} : Bool},
  em: {PM.Mem(ps, fr) == False{} : Bool}, own: {PM.Own(fi, nx, fr) == True{} : Bool},
  hy: {PM.Mem(Con{PM.Fd(2n, m, fr), PM.Fs.opt(U32.is_eq(tg, 38), PM.Fd(3n, m, fr), Nil{})}, y) == True{} : Bool},
  hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat}) -> {U32.is_eq(y, z) == False{} : Bool}:
  +L = {Con{PM.Fd(2n, m, fr), PM.Fs.opt(U32.is_eq(tg, 38), PM.Fd(3n, m, fr), Nil{})} : List<&2, U32>}
  +e = fs.frame(m, ps, fr, tg, etag, hlt, hle, em)
  ne.ptr(U32.is_eq(y, z), y, z, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, {==},
    N.le_trans(1n, PM.RcL(PM.Fs(m, ps, fr), y), PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, y),
      (%Equal.sym(List<&2, U32>, PM.Fs(m, ps, fr), L, e) : N.Le(1n, PM.RcL(_, y)); rcl.mem(L, y, hy)),
      Ptr.at(m, nx, fi, ps, rs, fr, y, own)), hz0)

# the part b of a frame, after a store to z
def Frs.b.fz(kind: PM.FK, +ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32, +x: C.Cir.Cell, +fr: U32, +b: C.Term,
  +tbl: PM.Tbl(m, im, fi, nx), +hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat},
  +hzs: {PM.Fl(m, z, 1024) == False{} : Bool}, etag: {PM.TgW(PM.Fd(0n, m, fr)) == PM.FK.tag(kind) : U32},
  em: {PM.Mem(ps, fr) == False{} : Bool}, own: {PM.Own(fi, nx, fr) == True{} : Bool},
  h: PM.Frs.b(ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, fr), kind, b)) ->
  PM.Frs.b(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, PM.Fd(3n, m, fr), kind, b):
  match kind:
    case PM.FK.rwt{}:
      is.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, fr), tbl, hz0, hzs,
        fr.ne(m, nx, fi, ps, rs, fr, PM.Fd(3n, m, fr), z, 38, etag, {==}, {==}, em, own,
          mem.tl(PM.Fd(2n, m, fr), PM.Fd(3n, m, fr), Con{PM.Fd(3n, m, fr), Nil{}}, mem.hd(PM.Fd(3n, m, fr), Nil{})), hz0), h)
    case PM.FK.arg{}:
      Unit{}
    case PM.FK.val{}:
      Unit{}
    case PM.FK.fun{}:
      Unit{}
    case PM.FK.let{}:
      Unit{}
    case PM.FK.tupb{}:
      Unit{}
    case PM.FK.tupa{}:
      Unit{}
    case PM.FK.minb{}:
      Unit{}
    case PM.FK.mina{}:
      Unit{}

# a store to z, a cell of a tag below 32 with no pointer, keeps the frames
def Frs.fz(fs: List<&2, PM.AF>, +ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32, +x: C.Cir.Cell, +fr: U32,
  +tbl: PM.Tbl(m, im, fi, nx), +hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat},
  +hzs: {PM.Fl(m, z, 1024) == False{} : Bool}, +hzt: {U32.is_lt(PM.TgW(PM.Fd(0n, m, z)), 32) == True{} : Bool},
  h: PM.Frs(ds, m, im, fi, nx, ks, img, ps, fr, fs)) -> PM.Frs(ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, ps, fr, fs):
  match fs:
    case Nil{}:
      h
    case Con{PM.AF{+kind, +q, +k, +a, +b}, +rest}:
      match h:
        case Tuple{e0, Tuple{ev, Tuple{+eo, Tuple{es, Tuple{+em, Tuple{+etg, Tuple{eq, Tuple{ek, Tuple{ia, Tuple{ib, ir}}}}}}}}}}:
          +M2 = C.Cir.Cells.set(m, z, x)
          +ne = PM.ne.fr(U32.is_eq(fr, z), m, fr, z, kind, {==}, etg, hzt)
          PM.frs.uc(ds, M2, im, fi, nx, ks, img, ps, fr, Con{PM.AF{kind, q, k, a, b}, rest},
            PM.frsc.at(ds, M2, im, fi, nx, ks, img, ps, fr, C.Cir.Cells.get(M2, fr), C.Cir.Cells.get(m, fr), Con{PM.AF{kind, q, k, a, b}, rest},
              PM.cl.go(m, fr, z, x, ne),
              (e0, (ev, (eo, (es, (em, (etg, (eq, (ek,
                (is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, fr), tbl, hz0, hzs,
                  fr.ne(m, nx, fi, ps, rs, fr, PM.Fd(2n, m, fr), z, PM.FK.tag(kind), etg, fk.lt(kind), fk.le(kind), em, eo,
                    mem.hd(PM.Fd(2n, m, fr), PM.Fs.opt(U32.is_eq(PM.FK.tag(kind), 38), PM.Fd(3n, m, fr), Nil{})), hz0), ia),
                (Frs.b.fz(kind, ds, m, im, fi, nx, ks, img, ps, rs, z, x, fr, b, tbl, hz0, hzs, etg, em, eo, ib),
                  Frs.fz(rest, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(1n, m, fr), tbl, hz0, hzs, hzt, ir)))))))))))))

# The image, after a store to a cell of the machine's own
# -------------------------------------------------------

# the table's cells from at, for the rows rs, are at most 363
def TblB(rs: List<&2, PM.Row>, +at: U32) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{_, rest}:
      Bool.and(U32.is_le(at, 363), TblB(rest, U32.inc(at)))

# a cell at most 363 is not z, past 363
def lit.ne(b: Bool, +l: U32, +z: U32, eb: {U32.is_eq(l, z) == b : Bool}, hl: {U32.is_le(l, 363) == True{} : Bool},
  hz: N.Le(1n+U32.to_nat(363), U32.to_nat(z))) -> {U32.is_eq(l, z) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +e = PM.u32.eq(l, z, eb)
      Empty.absurd({U32.is_eq(l, z) == False{} : Bool}, N.not_succ_le(U32.to_nat(363), N.le_trans(1n+U32.to_nat(363), U32.to_nat(z), U32.to_nat(363), hz,
        N.le_rw_l(U32.to_nat(l), U32.to_nat(z), U32.to_nat(363), Equal.cong(U32, Nat, w => U32.to_nat(w), l, z, e), u.le(l, 363, hl)))))

def Tbl.fz(rs: List<&2, PM.Row>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +z: U32, +x: C.Cir.Cell, +at: U32,
  +hz: N.Le(1n+U32.to_nat(363), U32.to_nat(z)), hb: {TblB(rs, at) == True{} : Bool}, h: PM.Tbl.go(rs, m, im, fi, nx, at)) ->
  PM.Tbl.go(rs, C.Cir.Cells.set(m, z, x), im, fi, nx, at):
  match rs:
    case Nil{}:
      Unit{}
    case Con{PM.Row{+a, +b, +c}, +rest}:
      (ec, r1) = h
      (e2, r2) = r1
      (e3, r3) = r2
      (e4, r4) = r3
      +hb2 = hb
      +M2 = C.Cir.Cells.set(m, z, x)
      +ne = lit.ne(U32.is_eq(at, z), at, z, {==}, and.l(U32.is_le(at, 363), TblB(rest, U32.inc(at)), hb2), hz)
      +ea = PM.cl.go(m, at, z, x, ne)
      (ec, ((%Equal.sym(C.Cir.Cell, C.Cir.Cells.get(M2, at), C.Cir.Cells.get(m, at), ea) : {C.Cir.Cell.get(2n, _) == a : U32}; e2),
        ((%Equal.sym(C.Cir.Cell, C.Cir.Cells.get(M2, at), C.Cir.Cells.get(m, at), ea) : {C.Cir.Cell.get(3n, _) == b : U32}; e3),
        ((%Equal.sym(C.Cir.Cell, C.Cir.Cells.get(M2, at), C.Cir.Cells.get(m, at), ea) : {C.Cir.Cell.get(4n, _) == c : U32}; e4),
          Tbl.fz(rest, m, im, fi, nx, z, x, U32.inc(at), hz, and.r(U32.is_le(at, 363), TblB(rest, U32.inc(at)), hb2), r4)))))

# no root of the defs dl, from at, is z
def Roots.ne(dl: List<&2, C.Def>, +at: U32, +z: U32) -> Bool:
  match dl:
    case Nil{}:
      True{}
    case Con{C.Def{_, _, +v, _}, rest}:
      Bool.and(Bool.not(U32.is_eq(at, z)), Roots.ne(rest, U32.add(at, C.Img.size(v)), z))

def Defs.fz(dl: List<&2, C.Def>, +ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32, +x: C.Cir.Cell, +at: U32, +tbl: PM.Tbl(m, im, fi, nx),
  +hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat}, +hzs: {PM.Fl(m, z, 1024) == False{} : Bool},
  hr: {Roots.ne(dl, at, z) == True{} : Bool}, h: PM.Defs(dl, ds, m, im, fi, nx, ks, img, at)) ->
  PM.Defs(dl, ds, C.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, at):
  match dl:
    case Nil{}:
      Unit{}
    case Con{C.Def{_, _, +v, _}, +rest}:
      (e0, r1) = h
      (hv, r2) = r1
      +hr2 = hr
      (e0, (is.fz(v, ds, m, im, fi, nx, ks, img, ps, rs, z, x, at, tbl, hz0, hzs,
          not.t(U32.is_eq(at, z), and.l(Bool.not(U32.is_eq(at, z)), Roots.ne(rest, U32.add(at, C.Img.size(v)), z), hr2)), hv),
        Defs.fz(rest, ds, m, im, fi, nx, ks, img, ps, rs, z, x, U32.add(at, C.Img.size(v)), tbl, hz0, hzs,
          and.r(Bool.not(U32.is_eq(at, z)), Roots.ne(rest, U32.add(at, C.Img.size(v)), z), hr2), r2)))

# a store to z, one of the machine's own cells, keeps the image
def ImgOK.fz(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32, +x: C.Cir.Cell,
  +hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat}, +hzs: {PM.Fl(m, z, 1024) == False{} : Bool},
  hzo: {PM.Own(fi, nx, z) == True{} : Bool}, hr: {Roots.ne(ds, C.I.book(), z) == True{} : Bool},
  h: PM.ImgOK(ds, ks, img, m, im, fi, nx)) -> PM.ImgOK(ds, ks, img, C.Cir.Cells.set(m, z, x), im, fi, nx):
  (+tbl, r1) = h
  (hd, r2) = r1
  (h9, r3) = r2
  (h10, r4) = r3
  (h11, r5) = r4
  (hks, r6) = r5
  (e363a, eima) = r6
  +e363 = {e363a : {U32.is_le(363, im) == True{} : Bool}}
  +eim = {eima : {U32.is_lt(im, fi) == True{} : Bool}}
  +hz = N.le_trans(1n+U32.to_nat(363), U32.to_nat(fi), U32.to_nat(z),
    N.le_trans(1n+U32.to_nat(363), 1n+U32.to_nat(im), U32.to_nat(fi), u.le(363, im, e363), u.lt(im, fi, eim)),
    u.le(fi, z, and.l(U32.is_le(fi, z), U32.is_lt(z, nx), hzo)))
  (Tbl.fz(PM.Tbl.rows(), m, im, fi, nx, z, x, 345, hz, {==}, tbl),
    (Defs.fz(ds, ds, m, im, fi, nx, ks, img, ps, rs, z, x, C.I.book(), tbl, hz0, hzs, hr, hd),
    (is.fz(C.Term.Lab{C.Quan.name(C.Quan.Q0{})}, ds, m, im, fi, nx, ks, img, ps, rs, z, x, 9, tbl, hz0, hzs, lit.ne(U32.is_eq(9, z), 9, z, {==}, {==}, hz), h9),
    (is.fz(C.Term.Lab{C.Quan.name(C.Quan.Q1{})}, ds, m, im, fi, nx, ks, img, ps, rs, z, x, 10, tbl, hz0, hzs, lit.ne(U32.is_eq(10, z), 10, z, {==}, {==}, hz), h10),
    (is.fz(C.Term.Lab{C.Quan.name(C.Quan.Q2{})}, ds, m, im, fi, nx, ks, img, ps, rs, z, x, 11, tbl, hz0, hzs, lit.ne(U32.is_eq(11, z), 11, z, {==}, {==}, hz), h11),
    (hks, (e363, eim)))))))

# the table, of the image
def img.tbl(-ds: List<&2, C.Def>, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, -m: C.Cir.Cells, -im: U32,
  -fi: U32, -nx: U32, io: PM.ImgOK(ds, ks, img, m, im, fi, nx)) -> PM.Tbl(m, im, fi, nx):
  (tb, r) = io
  tb

# A store to a cell that nothing points to: HS
# -------------------------------------------
#
# M.make's stores, after M.alloc: the cell z is one of the machine's own, out
# of the pend list, not STATIC, of a tag below 32, holds no pointer and has
# none; it gets a cell x of the machine's own kinds (a tag of 32 or more) that
# holds no pointer. Then HS holds with the same terms. TblR (no term cell
# reads its mask at z) and Roots.ne (no def's body is at z) are what HS does
# not say yet.

def hs.fz(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, PM.Rt>, +bs: List<&2, PM.Rt>, +fs: List<&2, PM.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +z: U32, +x: C.Cir.Cell,
  hs: PM.HS(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps),
  hzo: {PM.Own(fi, nx, z) == True{} : Bool}, +hzm: {PM.Mem(ps, z) == False{} : Bool},
  +hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, PM.Rt.cells(os), z) == 0n : Nat},
  +hzs: {PM.Fl(m, z, 1024) == False{} : Bool}, hzt: {U32.is_lt(PM.TgW(PM.Fd(0n, m, z)), 32) == True{} : Bool},
  +hf0: {PM.Fs(m, ps, z) == Nil{} : List<&2, U32>}, +hf1: {PM.Fs(C.Cir.Cells.set(m, z, x), ps, z) == Nil{} : List<&2, U32>},
  hxt: {U32.is_lt(PM.TgW(C.Cir.Cell.get(0n, x)), 19) == False{} : Bool},
  +htN: {TblR(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, z) == True{} : Bool},
  hr: {Roots.ne(ds, C.I.book(), z) == True{} : Bool}) ->
  PM.HS(ds, ks, img, C.Cir.Cells.set(m, z, x), nx, fi, im, os, bs, fs, sp, pend, ps):
  (ho, r1) = hs
  (hb, r2) = r1
  (hh0, r3) = r2
  (hf, r4) = r3
  (hp, hi0) = r4
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +rs = PM.Rt.cells(os)
  +hh = {hh0 : PM.Held(m, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, ps, PM.Rt.cells(os), bs)}
  +hi = {hi0 : PM.ImgOK(ds, ks, img, m, im, fi, nx)}
  +tbl = img.tbl(ds, ks, img, m, im, fi, nx, hi)
  +hnb = neall.held(bs, m, z, n, fi, ps, rs, hz0, hzs, hh)
  (Rts.fz(os, ds, m, im, fi, nx, ks, img, ps, rs, z, x, tbl, hz0, hzs, neall.rcl(rs, z, add0.r(PM.Pc(n, m, ps, fi, z), PM.RcL(rs, z), hz0)), ho),
    (Rts.fz(bs, ds, m, im, fi, nx, ks, img, ps, rs, z, x, tbl, hz0, hzs, hnb, hb),
    (Held.fz(bs, m, n, fi, ps, rs, z, x, hf0, hf1, htN, hnb, hh),
    (Frs.fz(fs, ds, m, im, fi, nx, ks, img, ps, rs, z, x, sp, tbl, hz0, hzs, hzt, hf),
    (Heap.fz(m, nx, fi, rs, pend, ps, z, x, hf0, hf1, htN, hzm, hz0, hxt, hp),
      ImgOK.fz(ds, ks, img, m, im, fi, nx, ps, rs, z, x, hz0, hzs, hzo, hr, hi))))))

# Cells set twice
# ---------------

# a cell set twice holds the second value (M.make's stores, one by one)
def cl.ss.at(n: Nat, +w: Word(n), +m: C.Cir.Cells, +c: C.Cir.Cell, +d: C.Cir.Cell) ->
  {C.Cir.Cells.set.at(n, w, C.Cir.Cells.set.at(n, w, m, c), d) == C.Cir.Cells.set.at(n, w, m, d) : C.Cir.Cells}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          match m:
            case C.Cir.Cells.node{+lo, +hi}:
              %cl.ss.at(p, t, lo, c, d) : {C.Cir.Cells.node{_, hi} == C.Cir.Cells.node{C.Cir.Cells.set.at(p, t, lo, d), hi} : C.Cir.Cells}
              {==}
            case C.Cir.Cells.none{}:
              %cl.ss.at(p, t, C.Cir.Cells.none{}, c, d) : {C.Cir.Cells.node{_, C.Cir.Cells.none{}} == C.Cir.Cells.node{C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, d), C.Cir.Cells.none{}} : C.Cir.Cells}
              {==}
            case C.Cir.Cells.one{+e}:
              %cl.ss.at(p, t, C.Cir.Cells.none{}, c, d) : {C.Cir.Cells.node{_, C.Cir.Cells.none{}} == C.Cir.Cells.node{C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, d), C.Cir.Cells.none{}} : C.Cir.Cells}
              {==}
        case WCon{True{}, +t}:
          match m:
            case C.Cir.Cells.node{+lo, +hi}:
              %cl.ss.at(p, t, hi, c, d) : {C.Cir.Cells.node{lo, _} == C.Cir.Cells.node{lo, C.Cir.Cells.set.at(p, t, hi, d)} : C.Cir.Cells}
              {==}
            case C.Cir.Cells.none{}:
              %cl.ss.at(p, t, C.Cir.Cells.none{}, c, d) : {C.Cir.Cells.node{C.Cir.Cells.none{}, _} == C.Cir.Cells.node{C.Cir.Cells.none{}, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, d)} : C.Cir.Cells}
              {==}
            case C.Cir.Cells.one{+e}:
              %cl.ss.at(p, t, C.Cir.Cells.none{}, c, d) : {C.Cir.Cells.node{C.Cir.Cells.none{}, _} == C.Cir.Cells.node{C.Cir.Cells.none{}, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, d)} : C.Cir.Cells}
              {==}

def cl.ss(+m: C.Cir.Cells, +i: U32, +c: C.Cir.Cell, +d: C.Cir.Cell) ->
  {C.Cir.Cells.set(C.Cir.Cells.set(m, i, c), i, d) == C.Cir.Cells.set(m, i, d) : C.Cir.Cells}:
  match i:
    case U32{+w}:
      cl.ss.at(32n, w, m, c, d)

# a store of field k of z, set before to y, sets it to y with field k
def cl.st(+m: C.Cir.Cells, +z: U32, +y: C.Cir.Cell, +k: Nat, +v: U32) ->
  {C.Cir.Cells.set(C.Cir.Cells.set(m, z, y), z, C.Cir.Cell.set(k, C.Cir.Cells.get(C.Cir.Cells.set(m, z, y), z), v)) ==
    C.Cir.Cells.set(m, z, C.Cir.Cell.set(k, y, v)) : C.Cir.Cells}:
  %Equal.sym(C.Cir.Cell, C.Cir.Cells.get(C.Cir.Cells.set(m, z, y), z), y, PM.cl.gs(m, z, y)) :
    {C.Cir.Cells.set(C.Cir.Cells.set(m, z, y), z, C.Cir.Cell.set(k, _, v)) == C.Cir.Cells.set(m, z, C.Cir.Cell.set(k, y, v)) : C.Cir.Cells}
  cl.ss(m, z, y, C.Cir.Cell.set(k, y, v))

# The registers
# -------------

# a set keeps the length
def rg.len(xs: List<&2, U32>, +i: Nat, +v: U32) -> {List.length(&2, U32, List.set(&2, U32, xs, i, v)) == List.length(&2, U32, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      match i:
        case 0n:
          {==}
        case 1n+j:
          %rg.len(t, j, v) : {1n+_ == 1n+List.length(&2, U32, t) : Nat}
          {==}

# a set register holds its value
def rg.same(xs: List<&2, U32>, +i: Nat, +v: U32, h: {Nat.is_lt(i, List.length(&2, U32, xs)) == True{} : Bool}) ->
  {List.get(&2, U32, List.set(&2, U32, xs, i, v), i) == Some{v} : Maybe<&2, U32>}:
  match xs:
    case Nil{}:
      PM.bool.ft({List.get(&2, U32, Nil{}, i) == Some{v} : Maybe<&2, U32>}, (%Equal.sym(Bool, Nat.is_lt(i, 0n), True{}, h) : {_ == True{} : Bool}; h))
    case Con{+hd, +t}:
      match i:
        case 0n:
          {==}
        case 1n+j:
          rg.same(t, j, v, h)

# and keeps the others
def rg.other(xs: List<&2, U32>, +i: Nat, +j: Nat, +v: U32, h: {Nat.is_eq(i, j) == False{} : Bool}) ->
  {List.get(&2, U32, List.set(&2, U32, xs, i, v), j) == List.get(&2, U32, xs, j) : Maybe<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+hd, +t}:
      match i j:
        case 0n 0n:
          PM.bool.ft({Some{v} == Some{hd} : Maybe<&2, U32>}, h)
        case 0n 1n+q:
          {==}
        case 1n+p 0n:
          {==}
        case 1n+p 1n+q:
          rg.other(t, p, q, v, h)

# Nat.is_eq is symmetric, on False
def ne.sym(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      h
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ne.sym(p, q, h)

# a register that keep has not: a set to it keeps the registers of keep
def kept.set(+regs: List<&2, U32>, +regs2: List<&2, U32>, keep: List<&2, Nat>, +i: Nat, +v: U32,
  hi: {PM.Nat.mem(keep, i) == False{} : Bool}, h: PM.Kept(regs, regs2, keep)) -> PM.Kept(regs, List.set(&2, U32, regs2, i, v), keep):
  match keep:
    case Nil{}:
      Unit{}
    case Con{+j, +rest}:
      (e, r) = h
      +hi2 = hi
      (Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.set(&2, U32, regs2, i, v), j), List.get(&2, U32, regs2, j), List.get(&2, U32, regs, j),
          rg.other(regs2, i, j, v, ne.sym(j, i, or.f.l(Nat.is_eq(j, i), PM.Nat.mem(rest, i), hi2))), e),
        kept.set(regs, regs2, rest, i, v, or.f.r(Nat.is_eq(j, i), PM.Nat.mem(rest, i), hi2), r))
