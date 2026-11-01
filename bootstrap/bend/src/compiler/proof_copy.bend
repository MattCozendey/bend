# compiler: the copy of the machine computes the kernel's substitution
# ====================================================================
#
# M.copy(r, src) (impl.bend, Machine) puts a term's variables in by copying:
# from a state whose register src holds a cell of the term t, and whose
# register cenv holds a list of clen cells of the terms e_0 .. e_{clen-1}, it
# gives in register r a cell of Term.subst(t, [e_0, ..]), or runs out of
# memory; M.shift(r, v) gives Term.shift(t, amt, 0). Both are M.copy.walk.
#
# The terms of cells are checked terms (Tm): T.tm.of's term, from cells that
# the run may read (Al: a cell of the state, not one of the cells X that an
# allocation may return, nor one of the table's), whose fv bounds the term's
# free variables (FvOK). A Tm stays when the run writes a cell that it does
# not read, or only the count (field 1) of a cell.
#
# The allocation (AL): the cells that M.alloc may take are the cells from
# next on and the garbage P, whose pend list Q is a chain from register pend;
# reusing a garbage cell drops a count of each of its parts, and the counts
# make sure that only garbage reaches 0: a garbage cell counts at least the
# garbage's pointers to it (none for Q's), and a live part of the garbage
# counts more than them, below the bound Bu. The copy shares parts of its
# source and adds a count to each, at most W times in all, so Bu + W must
# not wrap.

import Base
import ./impl.bend as C
import ./proof_term.bend as T
import ./proof_need.bend as N

# Kit
# ---

# a pair of two Data types, itself Data
def P2(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

# a witness x of A, and B(x), as Data
def Ex(-A: Data, -B: @-x: A -> Data) -> Data:
  Sigma<&2, &2, A, B>

def Nat.of(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# field k of the cell c
def Fd(+k: Nat, +m: C.Cir.Cells, +c: U32) -> U32:
  C.Cir.Cell.get(k, C.Cir.Cells.get(m, c))

# x is one of xs
def Has(xs: List<&2, U32>, +x: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, rest}:
      Bool.or(U32.is_eq(y, x), Has(rest, x))

# every one of xs is in ys
def Sub(xs: List<&2, U32>, +ys: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Has(ys, x), Sub(rest, ys))

# no cell is twice in xs
def Nodup(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      Bool.and(Bool.not(Has(rest, x)), Nodup(rest))

# Terms
# -----

# 1 + the highest free variable of t, 0 when it has none (Img.fv, unbounded)
def Fv(t: C.Term) -> Nat:
  match t:
    case C.Term.Var{i}:
      1n+i
    case C.Term.Ref{_}:
      0n
    case C.Term.Ann{x, T}:
      Nat.max(Fv(x), Fv(T))
    case C.Term.Let{_, v, f}:
      Nat.max(Fv(v), Nat.sub(Fv(f), 1n))
    case C.Term.Typ{q}:
      Fv(q)
    case C.Term.Min{a, b}:
      Nat.max(Fv(a), Fv(b))
    case C.Term.All{_, A, B}:
      Nat.max(Fv(A), Nat.sub(Fv(B), 1n))
    case C.Term.Lam{_, f}:
      Nat.sub(Fv(f), 1n)
    case C.Term.App{_, f, x}:
      Nat.max(Fv(f), Fv(x))
    case C.Term.Sig{_, A, B}:
      Nat.max(Fv(A), Nat.sub(Fv(B), 1n))
    case C.Term.Tup{_, a, b}:
      Nat.max(Fv(a), Fv(b))
    case C.Term.Prj{h}:
      Fv(h)
    case C.Term.Enu{_}:
      0n
    case C.Term.Lab{_}:
      0n
    case C.Term.Mat{_, h, m}:
      Nat.max(Fv(h), Fv(m))
    case C.Term.Efq{}:
      0n
    case C.Term.Eql{a, b, T}:
      Nat.max(Fv(a), Nat.max(Fv(b), Fv(T)))
    case C.Term.Rfl{}:
      0n
    case C.Term.Rwt{e, P, f}:
      Nat.max(Fv(e), Nat.max(Nat.sub(Fv(P), 2n), Fv(f)))

# the nodes of t
def Sz(t: C.Term) -> Nat:
  match t:
    case C.Term.Var{_}:
      1n
    case C.Term.Ref{_}:
      1n
    case C.Term.Ann{x, T}:
      1n+Nat.add(Sz(x), Sz(T))
    case C.Term.Let{_, v, f}:
      1n+Nat.add(Sz(v), Sz(f))
    case C.Term.Typ{q}:
      1n+Sz(q)
    case C.Term.Min{a, b}:
      1n+Nat.add(Sz(a), Sz(b))
    case C.Term.All{_, A, B}:
      1n+Nat.add(Sz(A), Sz(B))
    case C.Term.Lam{_, f}:
      1n+Sz(f)
    case C.Term.App{_, f, x}:
      1n+Nat.add(Sz(f), Sz(x))
    case C.Term.Sig{_, A, B}:
      1n+Nat.add(Sz(A), Sz(B))
    case C.Term.Tup{_, a, b}:
      1n+Nat.add(Sz(a), Sz(b))
    case C.Term.Prj{h}:
      1n+Sz(h)
    case C.Term.Enu{_}:
      1n
    case C.Term.Lab{_}:
      1n
    case C.Term.Mat{_, h, m}:
      1n+Nat.add(Sz(h), Sz(m))
    case C.Term.Efq{}:
      1n
    case C.Term.Eql{a, b, T}:
      1n+Nat.add(Sz(a), Nat.add(Sz(b), Sz(T)))
    case C.Term.Rfl{}:
      1n
    case C.Term.Rwt{e, P, f}:
      1n+Nat.add(Sz(e), Nat.add(Sz(P), Sz(f)))

# the most nodes of the terms es
def Sz.max(es: List<&2, C.Term>) -> Nat:
  match es:
    case Nil{}:
      0n
    case Con{e, rest}:
      Nat.max(Sz(e), Sz.max(rest))

# each variable i of t: i + a does not wrap as a U32
def Fit(t: C.Term, +a: U32) -> Bool:
  match t:
    case C.Term.Var{+i}:
      U32.is_ge(U32.add(U32.from_nat(i), a), U32.from_nat(i))
    case C.Term.Ref{_}:
      True{}
    case C.Term.Ann{x, T}:
      Bool.and(Fit(x, a), Fit(T, a))
    case C.Term.Let{_, v, f}:
      Bool.and(Fit(v, a), Fit(f, a))
    case C.Term.Typ{q}:
      Fit(q, a)
    case C.Term.Min{x, y}:
      Bool.and(Fit(x, a), Fit(y, a))
    case C.Term.All{_, A, B}:
      Bool.and(Fit(A, a), Fit(B, a))
    case C.Term.Lam{_, f}:
      Fit(f, a)
    case C.Term.App{_, f, x}:
      Bool.and(Fit(f, a), Fit(x, a))
    case C.Term.Sig{_, A, B}:
      Bool.and(Fit(A, a), Fit(B, a))
    case C.Term.Tup{_, x, y}:
      Bool.and(Fit(x, a), Fit(y, a))
    case C.Term.Prj{h}:
      Fit(h, a)
    case C.Term.Enu{_}:
      True{}
    case C.Term.Lab{_}:
      True{}
    case C.Term.Mat{_, h, m}:
      Bool.and(Fit(h, a), Fit(m, a))
    case C.Term.Efq{}:
      True{}
    case C.Term.Eql{x, y, T}:
      Bool.and(Fit(x, a), Bool.and(Fit(y, a), Fit(T, a)))
    case C.Term.Rfl{}:
      True{}
    case C.Term.Rwt{e, P, f}:
      Bool.and(Fit(e, a), Bool.and(Fit(P, a), Fit(f, a)))

# each of es fits the shift by a
def Fits(es: List<&2, C.Term>, +a: U32) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, rest}:
      Bool.and(Fit(e, a), Fits(rest, a))

# what a walk computes, under d binders: a shift by a, or a substitution of e
type Mo is Data:
  Mo.shift{a: Nat}
  Mo.subst{e: List<&2, C.Term>}

def Mo.F(+mo: Mo, t: C.Term, +d: Nat) -> C.Term:
  match mo:
    case Mo.shift{a}:
      C.Term.shift(t, a, d)
    case Mo.subst{e}:
      C.Term.subst(t, e, d)

# Checked terms
# -------------

# x is one of the table's cells (I.table)
def Tbc(+x: U32) -> Bool:
  Bool.and(U32.is_le(345, x), U32.is_le(x, 363))

# the run may read the cell x: one of the state's (image K, first F, next N),
# not one of X, nor one of the table's
def Al(+K: U32, +F: U32, +X: List<&2, U32>, +N: U32, +x: U32) -> Bool:
  Bool.and(C.Cir.is_cell(x, K, F, N), Bool.and(Bool.not(Has(X, x)), Bool.not(Tbc(x))))

# the fv fvf of a cell of the tag tag says what the copy needs of its term t:
# a Ref or an Enu has 0, which shares it; another bounds t's free variables,
# unless it is fv_max
def FvOK(tag: Nat, +fvf: U32, t: C.Term) -> Bool:
  match tag:
    case 1n:
      U32.is_zero(fvf)
    case 12n:
      U32.is_zero(fvf)
    case _:
      Bool.or(U32.is_eq(fvf, 524287), Nat.is_le(Fv(t), U32.to_nat(fvf)))

def Tm.ok(b: Bool, t: C.Term) -> Maybe<&2, C.Term>:
  match b:
    case True{}:
      Some{t}
    case False{}:
      None{}

def Tm.chk(+tag: Nat, +fvf: U32, r: Maybe<&2, C.Term>) -> Maybe<&2, C.Term>:
  match r:
    case None{}:
      None{}
    case Some{+t}:
      Tm.ok(FvOK(tag, fvf, t), t)

def Tm.if(ok: Bool, r: Unit -> Maybe<&2, C.Term>) -> Maybe<&2, C.Term>:
  match ok:
    case True{}:
      r(Unit{})
    case False{}:
      None{}

# the checked term of the cell c: T.tm.of's, when every cell that it reads may
# be read (Al) and has a right fv (FvOK)
def Tm(fuel: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32) -> Maybe<&2, C.Term>:
  match fuel:
    case 0n:
      None{}
    case 1n+(+f):
      +cell = C.Cir.Cells.get(m, c)
      +f0 = C.Cir.Cell.get(0n, cell)
      +tag = U32.to_nat(U32.and(f0, 63))
      Tm.if(Al(K, F, X, N, c), u => Tm.chk(tag, U32.shrn(f0, 13n),
        T.tm.cell(tag, T.tm.quan(U32.and(U32.shrn(f0, 6n), 3)), c, C.Cir.Cell.get(2n, cell), ks, img,
          u => Tm(f, m, ks, img, K, F, X, N, C.Cir.Cell.get(2n, cell)),
          u => Tm(f, m, ks, img, K, F, X, N, C.Cir.Cell.get(3n, cell)),
          u => Tm(f, m, ks, img, K, F, X, N, C.Cir.Cell.get(4n, cell)))))

# the cells that may be read grow from (X, N) to (X2, N2): N2 is at least N,
# and each of X2 is one of X or from N on
def Incl.go(X2: List<&2, U32>, +X: List<&2, U32>, +N: U32) -> Bool:
  match X2:
    case Nil{}:
      True{}
    case Con{+y, rest}:
      Bool.and(Bool.or(Has(X, y), U32.is_le(N, y)), Incl.go(rest, X, N))

def Incl(+X: List<&2, U32>, +N: U32, X2: List<&2, U32>, +N2: U32) -> Bool:
  Bool.and(U32.is_le(N, N2), Incl.go(X2, X, N))

# a term that the run keeps: its fuel, cell and term
type Rt is Data:
  Rt{f: Nat, c: U32, t: C.Term}

# the roots rs keep their checked terms
def Rts(+m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, rs: List<&2, Rt>) -> Data:
  match rs:
    case Nil{}:
      Unit
    case Con{Rt{+f, +c, +t}, rest}:
      P2({Tm(f, m, ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, C.Term>}, Rts(m, ks, img, K, F, X, N, rest))

# a cell that the run keeps, field for field: the cell x holds cl
type Kc is Data:
  Kc{x: U32, cl: C.Cir.Cell}

# a kept cell: one that may be read and is no term's (a tag of the machine's
# own cells, 19 or more), so the copy never counts it; or one of the cells E
# that the run may not read, a machine cell before N
def Kc.ok(+K: U32, +F: U32, +X: List<&2, U32>, +N: U32, +E: List<&2, U32>, +x: U32, +cl: C.Cir.Cell) -> Bool:
  Bool.or(Bool.and(Al(K, F, X, N, x), Nat.is_le(19n, U32.to_nat(U32.and(C.Cir.Cell.get(0n, cl), 63)))),
    Bool.and(Has(E, x), Bool.and(U32.is_le(F, x), U32.is_lt(x, N))))

# each cell of kc holds its cell, and is kept
def Kcs(+m: C.Cir.Cells, +K: U32, +F: U32, +X: List<&2, U32>, +N: U32, +E: List<&2, U32>, kc: List<&2, Kc>) -> Data:
  match kc:
    case Nil{}:
      Unit
    case Con{Kc{+x, +cl}, rest}:
      P2({C.Cir.Cells.get(m, x) == cl : C.Cir.Cell},
      P2({Kc.ok(K, F, X, N, E, x, cl) == True{} : Bool},
        Kcs(m, K, F, X, N, E, rest)))

# the table by tag (Img.table) is at cell 345
def Tb.go(+m: C.Cir.Cells, +i: U32, cs: List<&2, C.Cir.Cell>) -> Data:
  match cs:
    case Nil{}:
      Unit
    case Con{+c, rest}:
      P2({C.Cir.Cells.get(m, i) == c : C.Cir.Cell}, Tb.go(m, U32.inc(i), rest))

def Tb(+m: C.Cir.Cells) -> Data:
  Tb.go(m, 345, C.Img.table([]))

# The allocation
# --------------

# the mask of the parts of the cell o that its reuse drops, as M.alloc reads
# it: its table entry's field 2, for a tag below 32
def Am(+m: C.Cir.Cells, +o: U32) -> U32:
  +t = U32.and(Fd(0n, m, o), 63)
  Bool.pick(U32, U32.is_lt(t, 32), Fd(2n, m, U32.add(345, t)), 0)

# the pointers of the cell o to c
def Ow(+m: C.Cir.Cells, +o: U32, +c: U32) -> Nat:
  +a = Am(m, o)
  Nat.add(Nat.of(Bool.and(U32.is_ne(U32.and(a, 1), 0), U32.is_eq(Fd(2n, m, o), c))),
    Nat.add(Nat.of(Bool.and(U32.is_ne(U32.and(a, 2), 0), U32.is_eq(Fd(3n, m, o), c))),
      Nat.of(Bool.and(U32.is_ne(U32.and(a, 4), 0), U32.is_eq(Fd(4n, m, o), c)))))

# the pointers of the cells P to c
def Pp(P: List<&2, U32>, +m: C.Cir.Cells, +c: U32) -> Nat:
  match P:
    case Nil{}:
      0n
    case Con{+o, rest}:
      Nat.add(Ow(m, o, c), Pp(rest, m, c))

# the cell c is STATIC
def Stc(+m: C.Cir.Cells, +c: U32) -> Bool:
  U32.is_ne(U32.and(Fd(0n, m, c), 1024), 0)

# the pend list from p: the cells Q, linked by field 1, then 0
def Chain(Q: List<&2, U32>, +m: C.Cir.Cells, +p: U32) -> Bool:
  match Q:
    case Nil{}:
      U32.is_zero(p)
    case Con{+q, rest}:
      Bool.and(U32.is_eq(p, q), Bool.and(Bool.not(U32.is_zero(q)), Chain(rest, m, Fd(1n, m, q))))

# the part p of a garbage cell, in its mask am at bit: none, a cell that is
# STATIC or garbage, or a live one, which counts more than the garbage's
# pointers to it and less than Bu
def AL.part(+m: C.Cir.Cells, +P: List<&2, U32>, +am: U32, +bit: U32, +p: U32, +K: U32, +F: U32, +N: U32,
  +Bu: U32) -> Bool:
  Bool.or(U32.is_zero(U32.and(am, bit)), Bool.or(U32.is_zero(p), Bool.and(C.Cir.is_cell(p, K, F, N),
    Bool.or(Stc(m, p), Bool.or(Has(P, p),
      Bool.and(Nat.is_lt(Pp(P, m, p), U32.to_nat(Fd(1n, m, p))), U32.is_lt(Fd(1n, m, p), Bu)))))))

# each garbage cell of os: one of the machine's own, not STATIC, of a term's
# tag or of one of the machine's own (so its mask is the table's), its parts
# as above; one of the pend list has no pointer of the garbage, another
# counts at least them
def AL.cells(os: List<&2, U32>, +m: C.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +K: U32, +F: U32,
  +N: U32, +Bu: U32) -> Bool:
  match os:
    case Nil{}:
      True{}
    case Con{+o, rest}:
      +am = Am(m, o)
      +tg = U32.and(Fd(0n, m, o), 63)
      Bool.and(Bool.and(Bool.and(Bool.and(U32.is_le(F, o), U32.is_lt(o, N)), Bool.not(Stc(m, o))),
        Bool.or(U32.is_le(tg, 18), U32.is_le(32, tg))),
      Bool.and(Bool.and(AL.part(m, P, am, 1, Fd(2n, m, o), K, F, N, Bu),
        Bool.and(AL.part(m, P, am, 2, Fd(3n, m, o), K, F, N, Bu), AL.part(m, P, am, 4, Fd(4n, m, o), K, F, N, Bu))),
      Bool.and(Bool.pick(Bool, Has(Q, o), Nat.is_eq(Pp(P, m, o), 0n), Nat.is_le(Pp(P, m, o), U32.to_nat(Fd(1n, m, o)))),
        AL.cells(rest, m, P, Q, K, F, N, Bu))))

# the allocation's invariant, with the pend list from pend
def AL(+m: C.Cir.Cells, +pend: U32, +P: List<&2, U32>, +Q: List<&2, U32>, +K: U32, +F: U32, +N: U32,
  +Bu: U32) -> Bool:
  Bool.and(Bool.and(Chain(Q, m, pend), Nodup(Q)), Bool.and(Bool.and(Sub(Q, P), Nodup(P)),
    AL.cells(P, m, P, Q, K, F, N, Bu)))

# The registers
# -------------

# the n registers of regs from the i-th, each made explicit: the run's own
# code then reads and writes them by computation
def Rg.ex(n: Nat, +regs: List<&2, U32>, +i: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{T.tm.reg(regs, i), Rg.ex(p, regs, 1n+i)}

# a register write
type Up is Data:
  Up{i: Nat, v: U32}

# the registers xs after the writes ups, in order
def Ups(ups: List<&2, Up>, xs: List<&2, U32>) -> List<&2, U32>:
  match ups:
    case Nil{}:
      xs
    case Con{Up{i, v}, rest}:
      Ups(rest, List.set(&2, U32, xs, i, v))

# i is one of rs
def Has.nat(rs: List<&2, Nat>, +i: Nat) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Con{j, rest}:
      Bool.or(Nat.is_eq(j, i), Has.nat(rest, i))

# each write of ups is to a register of rs
def Ups.in(ups: List<&2, Up>, +rs: List<&2, Nat>) -> Bool:
  match ups:
    case Nil{}:
      True{}
    case Con{Up{+i, _}, rest}:
      Bool.and(Has.nat(rs, i), Ups.in(rest, rs))

# the registers that M.shift may write: the alloc's (pend, dx, dr, aq, am),
# sdep, sres, cm, the walk's (ss to snew), t1, t2
def Sh.scratch() -> List<&2, Nat>:
  [3n, 4n, 5n, 6n, 7n, 33n, 40n, 41n, 55n, 56n, 57n, 58n, 59n, 60n, 62n, 63n]

# the registers that M.copy may write: M.shift's, the copy's (cs to croot),
# samt and the result register r
def Cp.scratch(+r: Nat) -> List<&2, Nat>:
  Con{r, List.append(&2, Nat, [30n, 31n, 32n, 34n, 35n, 38n, 39n, 61n], Sh.scratch())}

# The states
# ----------

# a state of the run: the image K, the first cell F, the limit L and the input
# I stay; there is no output
def S(regs: List<&2, U32>, m: C.Cir.Cells, next: U32, F: U32, K: U32, pg: U32, L: U32, I: List<&2, U32>) ->
  C.Cir.State:
  C.Cir.State{regs, m, next, F, K, pg, L, I, Nil{}, 0}

# st is such a state, and Q holds of its registers, cells, next and pages
def At(st: C.Cir.State, +F: U32, +K: U32, +L: U32, +I: List<&2, U32>,
  Q: List<&2, U32> -> C.Cir.Cells -> U32 -> U32 -> Type) -> Type:
  match st:
    case C.Cir.State{+rg, +ms, +nx, fi, im, +pg, li, inp, out, outn}:
      Sigma<&1, &1, {S(rg, ms, nx, F, K, pg, L, I) == C.Cir.State{rg, ms, nx, fi, im, pg, li, inp, out, outn} : C.Cir.State},
        _ => Q(rg, ms, nx, pg)>

# the outcome o: next, with a state of which Q holds, or out of memory
def Ok(o: C.Cir.Out, +F: U32, +K: U32, +L: U32, +I: List<&2, U32>,
  Q: List<&2, U32> -> C.Cir.Cells -> U32 -> U32 -> Type) -> Type:
  match o:
    case C.Cir.Out.next{st}:
      At(st, F, K, L, I, Q)
    case C.Cir.Out.halt{_, _}:
      Empty
    case C.Cir.Out.out_of_memory{}:
      Unit
    case C.Cir.Out.trap{}:
      Empty
    case C.Cir.Out.not_done{}:
      Empty

# The claims
# ----------

# what a copy (of the mode mo, from the cell of the term t) leaves: the
# registers of regs but for the writes ups, to the registers rs; in register
# rr the cell r of Mo.F(mo, t, 0), with any fuel g, of the cells that may be
# read once the new garbage Pn and the new next may be returned; the
# allocation's invariant again, of Pn, its pend list Qn and the bound Bu + Wu; the cells that may be read
# only grow; the table, the roots rs and the kept cells kc stay
type Wt is Data:
  Wt{ups: List<&2, Up>, r: U32, g: Nat, Pn: List<&2, U32>, Qn: List<&2, U32>}

def Post(+mo: Mo, +t: C.Term, +regs: List<&2, U32>, +scr: List<&2, Nat>, +rr: Nat, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +K: U32, +F: U32, +P: List<&2, U32>, +E: List<&2, U32>, +N: U32, +Bu: U32, +Wu: U32,
  +rs: List<&2, Rt>, +kc: List<&2, Kc>, w: Wt, +rg: List<&2, U32>, +ms: C.Cir.Cells, +nx: U32) -> Data:
  match w:
    case Wt{+ups, +r, +g, +Pn, +Qn}:
      P2({rg == Ups(ups, Rg.ex(64n, regs, 0n)) : List<&2, U32>},
      P2({Ups.in(ups, scr) == True{} : Bool},
      P2({T.tm.reg(rg, rr) == r : U32},
      P2({Tm(g, ms, ks, img, K, F, List.append(&2, U32, Pn, E), nx, r) == Some{Mo.F(mo, t, 0n)} : Maybe<&2, C.Term>},
      P2({AL(ms, T.tm.reg(rg, 3n), Pn, Qn, K, F, nx, U32.add(Bu, Wu)) == True{} : Bool},
      P2({Incl(P, N, Pn, nx) == True{} : Bool},
      P2(Tb(ms),
      P2(Rts(ms, ks, img, K, F, List.append(&2, U32, P, E), N, rs),
        Kcs(ms, K, F, List.append(&2, U32, P, E), N, E, kc)))))))))

# the cells E that the run may not read: machine cells before nx, none garbage
def Ex.ok(xs: List<&2, U32>, +P: List<&2, U32>, +F: U32, +nx: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Bool.and(Bool.not(Has(P, x)), Bool.and(U32.is_le(F, x), U32.is_lt(x, nx))), Ex.ok(rest, P, F, nx))

# what the state of a run should be at the start: the image's cells, the
# table, the pend list, the bound, the cells E that it may not read, and the
# cells and terms that stay
def Pre(+regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +F: U32, +K: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +P: List<&2, U32>, +Q: List<&2, U32>, +E: List<&2, U32>, +Bu: U32, +Wu: U32,
  +rs: List<&2, Rt>, +kc: List<&2, Kc>) -> Data:
  P2({List.length(&2, U32, regs) == 64n : Nat},
  P2({U32.is_le(363, K) == True{} : Bool},
  P2({U32.is_lt(K, F) == True{} : Bool},
  P2({U32.is_le(F, nx) == True{} : Bool},
  P2(Tb(m),
  P2({AL(m, T.tm.reg(regs, 3n), P, Q, K, F, nx, Bu) == True{} : Bool},
  P2({U32.is_le(Bu, U32.add(Bu, Wu)) == True{} : Bool},
  P2({Ex.ok(E, P, F, nx) == True{} : Bool},
  P2(Rts(m, ks, img, K, F, List.append(&2, U32, P, E), nx, rs), Kcs(m, K, F, List.append(&2, U32, P, E), nx, E, kc))))))))))

# LAW: M.shift(sres, t2): from a state whose register t2 holds a cell of the
# term t (by Tm, with any fuel g, reading neither the garbage P nor the cells
# E), and samt the amount a, of whose variables t allows the shift, with the
# start's facts (Pre) and a count bound Wu of at least 2 + 2 × Sz(t), some fuel
# gives sres a cell of Term.shift(t, a, 0), with Post's facts, or runs out of
# memory. E is [] for the machine; M.copy passes its frames' cells
law Sh.ok:
  for +regs: List<&2, U32>
  for +m: C.Cir.Cells
  for +nx: U32
  for +F: U32
  for +K: U32
  for +pg: U32
  for +L: U32
  for +I: List<&2, U32>
  for +ks: List<&2, List<&2, U32>>
  for +img: List<&2, C.Term>
  for +P: List<&2, U32>
  for +Q: List<&2, U32>
  for +Bu: U32
  for +Wu: U32
  for +E: List<&2, U32>
  for +rs: List<&2, Rt>
  for +kc: List<&2, Kc>
  for +t: C.Term
  for +g: Nat
  for +a: U32
  for pre: Pre(regs, m, nx, F, K, ks, img, P, Q, E, Bu, Wu, rs, kc)
  for ht: {Tm(g, m, ks, img, K, F, List.append(&2, U32, P, E), nx, T.tm.reg(regs, 63n)) == Some{t} : Maybe<&2, C.Term>}
  for ha: {T.tm.reg(regs, 61n) == a : U32}
  for hf: {Fit(t, a) == True{} : Bool}
  for hw: {Nat.is_le(2n+Nat.double(Sz(t)), U32.to_nat(Wu)) == True{} : Bool}
  exs n: Nat
  Ok(C.Cir.exec(n, C.M.shift(C.R.sres(), C.R.t2()), S(regs, m, nx, F, K, pg, L, I)), F, K, L, I,
    rg => ms => nx2 => pg2 => Ex(Wt, w => Post(Mo.shift{U32.to_nat(a)}, t, regs, Sh.scratch(), C.R.sres(), ks, img, K, F,
      P, E, nx, Bu, Wu, rs, kc, w, rg, ms, nx2)))

# the list of locals from the cell l: a cell of each of es, which may be read,
# no term's (tag 19 or more), its field 2 a cell of its term (by Tm, with any
# fuel), its field 1 the next
def Env(+m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +l: U32, es: List<&2, C.Term>) -> Data:
  match es:
    case Nil{}:
      Unit
    case Con{+e, rest}:
      P2({Al(K, F, X, N, l) == True{} : Bool},
      P2({Nat.is_le(19n, U32.to_nat(U32.and(Fd(0n, m, l), 63))) == True{} : Bool},
      P2(Ex(Nat, g => {Tm(g, m, ks, img, K, F, X, N, Fd(2n, m, l)) == Some{e} : Maybe<&2, C.Term>}),
        Env(m, ks, img, K, F, X, N, Fd(1n, m, l), rest))))

# the most counts that a copy of t with the locals es adds: a round of its
# walk adds at most one, and shifts a local at most once
def Cp.W(t: C.Term, es: List<&2, C.Term>) -> Nat:
  Nat.mul(1n+Nat.double(Sz(t)), 2n+Nat.double(Sz.max(es)))

# the register of the source of M.copy: wt (a call's leaf) or z (a λ's or a
# let's body), the machine's two calls; the copy goes to n
def Cp.src(wt: Bool) -> Nat:
  match wt:
    case True{}:
      C.R.wt()
    case False{}:
      C.R.z()

# LAW: M.copy(n, src), src wt or z (Cp.src): from a state whose register src
# holds a cell of the term t (by Tm, reading neither the garbage P nor the
# cells E), cenv the list of the locals es (Env) and clen their number, with
# the start's facts (Pre), every local fitting a shift by any depth of t
# (below 2 × Sz(t)), and a count bound Wu of at least Cp.W(t, es), some fuel
# gives n a cell of Term.subst(t, es, 0), with Post's facts, or runs out of
# memory
law Cp.ok:
  for +wt: Bool
  for +regs: List<&2, U32>
  for +m: C.Cir.Cells
  for +nx: U32
  for +F: U32
  for +K: U32
  for +pg: U32
  for +L: U32
  for +I: List<&2, U32>
  for +ks: List<&2, List<&2, U32>>
  for +img: List<&2, C.Term>
  for +P: List<&2, U32>
  for +Q: List<&2, U32>
  for +Bu: U32
  for +Wu: U32
  for +E: List<&2, U32>
  for +rs: List<&2, Rt>
  for +kc: List<&2, Kc>
  for +t: C.Term
  for +g: Nat
  for +es: List<&2, C.Term>
  for pre: Pre(regs, m, nx, F, K, ks, img, P, Q, E, Bu, Wu, rs, kc)
  for ht: {Tm(g, m, ks, img, K, F, List.append(&2, U32, P, E), nx, T.tm.reg(regs, Cp.src(wt))) == Some{t} : Maybe<&2, C.Term>}
  for he: Env(m, ks, img, K, F, List.append(&2, U32, P, E), nx, T.tm.reg(regs, 36n), es)
  for hl: {U32.to_nat(T.tm.reg(regs, 37n)) == List.length(&2, C.Term, es) : Nat}
  for hf: {Fits(es, U32.from_nat(Nat.double(Sz(t)))) == True{} : Bool}
  for hw: {Nat.is_le(Cp.W(t, es), U32.to_nat(Wu)) == True{} : Bool}
  exs n: Nat
  Ok(C.Cir.exec(n, C.M.copy(C.R.n(), Cp.src(wt)), S(regs, m, nx, F, K, pg, L, I)), F, K, L, I,
    rg => ms => nx2 => pg2 => Ex(Wt, w => Post(Mo.subst{es}, t, regs, Cp.scratch(C.R.n()), C.R.n(), ks, img, K, F,
      P, E, nx, Bu, Wu, rs, kc, w, rg, ms, nx2)))
