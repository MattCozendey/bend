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
