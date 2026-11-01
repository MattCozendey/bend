# compiler: the data check of the machine (layer B)
# ===================================================
#
# data.post and data.done of proof_mach.bend (PM.DataPost, PM.DataDone), for
# M.data of impl.bend's Machine.
#
# The check's stack is a chain of K.check cells from register ds. Each one
# holds, in field 2, the cell of a part of v: the cell that a path of pair
# fields from c reaches (Cl), whose term is the path's part of v (Sub). A
# path from c keeps its cells across the run: M.alloc keeps each cell out of
# the pend list (AlFr), and the other stores are to K.check cells or set the
# flag DATA.
#
# When v is Data, every part on the stack is Data (data.sub), so each flag
# that the check sets is true (data.flag) and HS holds throughout. When it is
# not, the run goes on under HSK(False) and a witness says the check fails:
# a path to a part of v that is not Data, and on to a cell that is not a
# pair, a label or Rfl, all of its cells unflagged, the first on the stack.

import Base
import ./impl.bend as C
import ./proof_term.bend as T
import ./proof_need.bend as N
import ./proof_mach_defs.bend as PM
import ./proof_mach_exec.bend as X

# Kit
# ---

def mt.get(x: Maybe<&2, C.Term>, d: C.Term) -> C.Term:
  match x:
    case None{}:
      d
    case Some{y}:
      y

def mt.inj(+a: C.Term, -b: C.Term, e: {Some{a} == Some{b} : Maybe<&2, C.Term>}) -> {a == b : C.Term}:
  Equal.cong(Maybe<&2, C.Term>, C.Term, x => mt.get(x, a), Some{a}, Some{b}, e)

def mt.ms(x: Maybe<&2, C.Term>) -> Type:
  match x:
    case None{}:
      Unit
    case Some{_}:
      Empty

def mt.ne(-u: C.Term, e: {None{} == Some{u} : Maybe<&2, C.Term>}) -> Empty:
  %e : mt.ms(_)
  Unit{}

# Paths
# -----

# the cell that the path p of pair fields reaches from c: True for field 2
# (the first field), False for field 3 (the second)
def Cl(+m: C.Cir.Cells, p: List<&2, Bool>, +c: U32) -> U32:
  match p:
    case Nil{}:
      c
    case Con{True{}, rest}:
      Cl(m, rest, PM.Fd(2n, m, c))
    case Con{False{}, rest}:
      Cl(m, rest, PM.Fd(3n, m, c))

def Sub.a(l: Bool, r: Maybe<&2, C.Term>) -> Maybe<&2, C.Term>:
  match l:
    case True{}:
      r
    case False{}:
      None{}

# the part of v at the path p: through pairs only, and through a first field
# only when it is live
def Sub(v: C.Term, p: List<&2, Bool>) -> Maybe<&2, C.Term>:
  match v p:
    case x Nil{}:
      Some{x}
    case C.Term.Tup{q, a, b} Con{True{}, rest}:
      Sub.a(C.Quan.live(q), Sub(a, rest))
    case C.Term.Tup{q, a, b} Con{False{}, rest}:
      Sub(b, rest)
    case _ Con{_, _}:
      None{}

def is.sub.l(l: Bool, +dk: Bool, +ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +x: U32, -a: C.Term, -rest: List<&2, Bool>, -u: C.Term,
  e: {Sub.a(l, Sub(a, rest)) == Some{u} : Maybe<&2, C.Term>},
  ih: {Sub(a, rest) == Some{u} : Maybe<&2, C.Term>} -> PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, rest, x), u)) ->
  PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, rest, x), u):
  match l:
    case True{}:
      ih(e)
    case False{}:
      Empty.absurd(PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, rest, x), u), mt.ne(u, e))

# the cell at a path of v's cell stands for v's part there
def is.sub(+dk: Bool, +ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, v: C.Term, p: List<&2, Bool>, +c: U32, -u: C.Term,
  h: PM.IsK(dk, ds, m, im, fi, nx, ks, img, c, v), e: {Sub(v, p) == Some{u} : Maybe<&2, C.Term>}) ->
  PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, p, c), u):
  match v p:
    case +x Nil{}:
      %mt.inj(x, u, e) : PM.IsK(dk, ds, m, im, fi, nx, ks, img, c, _)
      h
    case C.Term.Tup{+q, +a, +b} Con{True{}, +rest}:
      (nd, r1) = h
      (hq, r2) = r1
      (pa, pb) = r2
      (spa, ia) = pa
      is.sub.l(C.Quan.live(q), dk, ds, m, im, fi, nx, ks, img, PM.Fd(2n, m, c), a, rest, u, e,
        e2 => is.sub(dk, ds, m, im, fi, nx, ks, img, a, rest, PM.Fd(2n, m, c), u, ia, e2))
    case C.Term.Tup{+q, +a, +b} Con{False{}, rest}:
      (nd, r1) = h
      (hq, r2) = r1
      (pa, pb) = r2
      (spb, ib) = pb
      is.sub(dk, ds, m, im, fi, nx, ks, img, b, rest, PM.Fd(3n, m, c), u, ib, e)
    case _ Con{d, rest}:
      Empty.absurd(PM.IsK(dk, ds, m, im, fi, nx, ks, img, Cl(m, Con{d, rest}, c), u), mt.ne(u, e))
