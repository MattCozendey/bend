# compiler: layer B, the machine
# ==============================
#
# The shared definitions (the invariant, the heap, Post, the premises' named
# types, the store and cell kit) live in proof_mach_defs.bend (D); the
# execution equations of the machine's statements in proof_mach_exec.bend (X).
# This file keeps the premises (open until the phases' lemmas exist), the
# moves, the loop and the assembly.
#
# mach.safe, mach.sound and mach.complete of proof.bend, with exactly their
# types (mach.safe.proof, mach.sound.proof, mach.complete.proof, at the end
# of "The run"), from the invariant of the machine (Inv) and one lemma per
# move. The Lean machine (bootstrap/lean, Machine.lean, Machine/*.lean) is
# the template: a move is an admin move that keeps the term, or one step of
# Eval, and keeps what the state knows.
#
# Kit (Post): what a statement's outcome may be, for any fuel (dn False) or
# for a fuel that ends it (dn True); more fuel keeps an outcome that ends
# (mono).
#
# Terms of states (A.*): a focus, to evaluate (mode 0) or a value (mode 1),
# and its frames (AF), the innermost first; their term (A.plugs) and the
# measure of the admin moves (A.w), which every admin move makes smaller.
#
# Inv(ds, ks, img, st, t, w): between two rounds, the state st holds an
# abstract state (Wit) of the term t and the measure w: the registers RG
# (focus, mode, sp, pend, then R60); the focus' cell and the frames' parts
# stand for their terms (Is, by recursion on the term, in the machine's own
# U32 forms, with VALUE, DATA and fv true of them); the frames (Frs); the
# counts and the pend list (Heap: a term cell counts at least its pointers,
# the pend list's cells have none, a pointer is below next); the image (ImgOK:
# the table, the defs' bodies, the labels of Q0 to Q2, the names); no output.
#
# Moves (MV, mv.*): one round of the main loop (B.body) from a state that Inv
# finds is, for any fuel, an admin move (Inv of the same term, a smaller
# measure), a step (Inv of u with Eval.step(ds, t) == Some{u}), a halt as HR
# says (0: t's bytes; 2: no step and no result), or out of memory; and it
# ends with some fuel. round.mv picks the move by the abstract state; the
# premises on M.copy, M.data, M.walk, M.out and M.input are open defs
# (copy.post, data.post, walk.post, out.post, input.post and their .done).
#
# The loop: loop.post (by induction on the fuel) gives only what Eval gives;
# loop.done (by induction on Eval's steps, then on the measure) finds a fuel
# that gives it, or runs out of memory.
#
# Proven: the kit, mono, the loop, the run from Cir.result's start, the
# three lemmas; the choice of the moves (round.post, round.done); the moves
# mv.ev.val, mv.ev.former, mv.ev.var and mv.out. Open (?TODO): the other
# moves, the premises above, the frame conditions of allocation (is.pend,
# is.fresh), Eval's ev.stops and ev.stuck, and mach.memory with what it
# needs (round.peak, round.room).

import Base
import ./impl.bend as C
import ./proof_term.bend as T
import ./proof_need.bend as N
import ./proof_mach_defs.bend as D
import ./proof_mach_exec.bend as X
import ./proof_mach_ev.bend as EV
import ./proof_is.bend as PI
import ./proof_out_is.bend as OI

# Open: the premises (the phases' lemmas)
# ---------------------------------------
#
# Each is a lemma of a phase file, with exactly this type: its conclusion is
# the named type of proof_mach_defs.bend.


def copy.post(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, +src: Nat,
  +keep: List<&2, Nat>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +c: U32, +t: C.Term, +ce: U32, +es: List<&2, C.Arg>,
  hs: D.HS(ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, t}, bs}, fs, sp, pend, ps),
  hl: {List.length(&2, U32, regs) == 64n : Nat},
  hc: {List.get(&2, U32, regs, src) == Some{c} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  he: {List.get(&2, U32, regs, 36n) == Some{ce} : Maybe<&2, U32>},
  hn: {List.get(&2, U32, regs, 37n) == Some{U32.from_nat(List.length(&2, C.Arg, es))} : Maybe<&2, U32>},
  env: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, ce, es),
  hr: {Bool.and(Nat.is_lt(r, 64n), Bool.not(D.Nat.mem([3n, 39n], r))) == True{} : Bool},
  hsrc: {D.Nat.mem([4n, 5n, 6n, 7n, 39n], src) == False{} : Bool},
  ho: N.Le(List.length(&2, D.Rt, os), 64n),
  hv: {D.Terms.below(D.Arg.terms(es), U32.to_nat(2147483648)) == True{} : Bool},
  hk: {D.Disj(keep, D.Copy.scr(r)) == True{} : Bool}) ->
  D.CopyPost(f, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, src, keep, os, bs, fs, sp, pend, ps, c, t, ce, es, hs, hl, hc, hp, he, hn, env, hr, hsrc, ho, hv, hk):
  ?TODO


def copy.done(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, +src: Nat,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +c: U32, +t: C.Term, +ce: U32, +es: List<&2, C.Arg>,
  hs: D.HS(ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, t}, bs}, fs, sp, pend, ps),
  hl: {List.length(&2, U32, regs) == 64n : Nat},
  hc: {List.get(&2, U32, regs, src) == Some{c} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  he: {List.get(&2, U32, regs, 36n) == Some{ce} : Maybe<&2, U32>},
  hn: {List.get(&2, U32, regs, 37n) == Some{U32.from_nat(List.length(&2, C.Arg, es))} : Maybe<&2, U32>},
  env: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, ce, es),
  hr: {Bool.and(Nat.is_lt(r, 64n), Bool.not(D.Nat.mem([3n, 39n], r))) == True{} : Bool},
  hsrc: {D.Nat.mem([4n, 5n, 6n, 7n, 39n], src) == False{} : Bool},
  ho: N.Le(List.length(&2, D.Rt, os), 64n)) ->
  D.CopyDone(ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, src, os, bs, fs, sp, pend, ps, c, t, ce, es, hs, hl, hc, hp, he, hn, env, hr, hsrc, ho):
  ?TODO


def data.post(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat,
  +keep: List<&2, Nat>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +c: U32, +v: C.Term,
  hs: D.HS(ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, v}, bs}, fs, sp, pend, ps),
  hl: {List.length(&2, U32, regs) == 64n : Nat},
  hc: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  hr: {D.Nat.mem(D.Data.scr(), r) == False{} : Bool},
  hk: {D.Disj(keep, D.Data.scr()) == True{} : Bool}) ->
  D.DataPost(f, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, keep, os, bs, fs, sp, pend, ps, c, v, hs, hl, hc, hp, hr, hk):
  ?TODO


def data.done(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +c: U32, +v: C.Term,
  hs: D.HS(ds, ks, img, m, nx, fi, im, os, Con{D.Rt{c, v}, bs}, fs, sp, pend, ps),
  hl: {List.length(&2, U32, regs) == 64n : Nat},
  hc: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  hr: {D.Nat.mem(D.Data.scr(), r) == False{} : Bool}) ->
  D.DataDone(ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, r, os, bs, fs, sp, pend, ps, c, v, hs, hl, hc, hp, hr):
  ?TODO


def walk.post(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>,
  +keep: List<&2, Nat>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +tc: U32, +tt: C.Term, +a: U32, +xs: List<&2, C.Arg>,
  hs: D.HS(ds, ks, img, m, nx, fi, im, os, Con{D.Rt{tc, tt}, bs}, fs, sp, pend, ps),
  hst: {D.Fl(m, tc, 1024) == True{} : Bool},
  hl: {List.length(&2, U32, regs) == 64n : Nat},
  ht: {List.get(&2, U32, regs, 19n) == Some{tc} : Maybe<&2, U32>},
  ha: {List.get(&2, U32, regs, 21n) == Some{a} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  args: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, a, xs),
  hk: {D.Disj(keep, D.Walk.scr()) == True{} : Bool}) ->
  D.WalkPost(f, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, keep, os, bs, fs, sp, pend, ps, tc, tt, a, xs, hs, hst, hl, ht, ha, hp, args, hk):
  ?TODO


def walk.done(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>,
  +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +tc: U32, +tt: C.Term, +a: U32, +xs: List<&2, C.Arg>,
  hs: D.HS(ds, ks, img, m, nx, fi, im, os, Con{D.Rt{tc, tt}, bs}, fs, sp, pend, ps),
  hst: {D.Fl(m, tc, 1024) == True{} : Bool},
  hl: {List.length(&2, U32, regs) == 64n : Nat},
  ht: {List.get(&2, U32, regs, 19n) == Some{tc} : Maybe<&2, U32>},
  ha: {List.get(&2, U32, regs, 21n) == Some{a} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  args: D.Ag(ds, m, im, fi, nx, ks, img, ps, os, a, xs)) ->
  D.WalkDone(ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, os, bs, fs, sp, pend, ps, tc, tt, a, xs, hs, hst, hl, ht, ha, hp, args):
  ?TODO


def out.post(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32,
  +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>,
  +v: C.Term, +ks2: List<&2, List<&2, U32>>,
  +hv: D.Is(ds, m, im, fi, nx, ks, img, foc, v),
  +hk: {ks == C.Img.known(ks2) : List<&2, List<&2, U32>>}) ->
  D.OutPost(f, ds, ks, img, foc, pend, rest, m, nx, fi, im, pg, lim, inp, v, ks2, hv, hk):
  OI.out.post(f, ds, ks, img, foc, pend, rest, m, nx, fi, im, pg, lim, inp, v, ks2, hv, hk,
    PI.is.tm(ds, m, im, fi, nx, ks, img, foc, v, hv))


def out.done(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32,
  +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>,
  +v: C.Term, +ks2: List<&2, List<&2, U32>>,
  +hv: D.Is(ds, m, im, fi, nx, ks, img, foc, v),
  +hk: {ks == C.Img.known(ks2) : List<&2, List<&2, U32>>}) ->
  D.OutDone(ds, ks, img, foc, pend, rest, m, nx, fi, im, pg, lim, inp, v, ks2, hv, hk):
  OI.out.done(ds, ks, img, foc, pend, rest, m, nx, fi, im, pg, lim, inp, v, ks2, hv, hk,
    PI.is.tm(ds, m, im, fi, nx, ks, img, foc, v, hv))


# Open: the start (proof_in.bend). From St0, with the image of a book that
# Book.read reads, M.input ends with InvIn, or runs out of memory, for any
# fuel; and with some fuel it ends.
def input.post(+f: Nat, +p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +k: U32, +len: U32,
  +pg: U32, +lim: U32, +first: U32,
  rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  small: {C.Img.small(p, 0) == True{} : Bool},
  s: D.Start(C.Img.cells(ds), i, m, k, len, pg, lim, first)) ->
  D.InputPost(f, p, ds, i, m, k, len, pg, lim, first, rd, small, s):
  ?TODO


def input.done(+p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +k: U32, +len: U32,
  +pg: U32, +lim: U32, +first: U32,
  rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  small: {C.Img.small(p, 0) == True{} : Bool},
  s: D.Start(C.Img.cells(ds), i, m, k, len, pg, lim, first)) ->
  D.InputDone(p, ds, i, m, k, len, pg, lim, first, rd, small, s):
  ?TODO



# Open lemmas
# -----------
#
# Each is a premise of the proofs below, in the shape that they use; a body
# ?TODO is still open.

# Eval: a value has no step (Lean's eval_value)
def ev.stops(+ds: List<&2, C.Def>, +t: C.Term, h: {C.Eval.vals(ds, t, False{}) == True{} : Bool}) ->
  {C.Eval.step(ds, t) == None{} : Maybe<C.Term>}:
  EV.ev.stops(ds, t, h)

# a term with a step is no value
def vals.of(b: Bool, +ds: List<&2, C.Def>, +t: C.Term, -u: C.Term, eb: {C.Eval.vals(ds, t, False{}) == b : Bool},
  es: {C.Eval.step(ds, t) == Some{u} : Maybe<C.Term>}) -> {C.Eval.vals(ds, t, False{}) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      Empty.absurd({C.Eval.vals(ds, t, False{}) == False{} : Bool},
        D.st.ne(u, Equal.trans(Maybe<C.Term>, None{}, C.Eval.step(ds, t), Some{u},
          Equal.sym(Maybe<C.Term>, C.Eval.step(ds, t), None{}, ev.stops(ds, t, eb)), es)))

# Inv's facts of that state, with the abstract state of ret, focus and fs
def IV(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +t: C.Term, +w: Nat, +ret: Bool, +focus: C.Term,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>) -> Data:
  D.InvOf(ds, ks, img, D.RG(foc, Bool.to_u32(ret), sp, pend, D.R60.list(rest)), m, nx, fi, im, Nil{}, 0, t, w, ret, focus, fs, foc, sp,
    pend, ps, rest)

# a move from st: for any fuel, a round that goes on (Rnd) or halts as HR
# says; and a fuel with which it ends
def MV(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +st: C.Cir.State, +t: C.Term, +w: Nat) ->
  Type:
  (@f: Nat -> D.Post(False{}, C.Cir.exec(f, D.B.body(), st), s => D.Rnd(ds, ks, img, t, w, s), s => st2 => D.HR(ds, t, s, st2))) &
    D.Ex(Nat, f => D.Ends(C.Cir.exec(f, D.B.body(), st)))

def mv.post(+f: Nat, -ds: List<&2, C.Def>, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, -st: C.Cir.State,
  -t: C.Term, -w: Nat, h: MV(ds, ks, img, st, t, w)) ->
  D.Post(False{}, C.Cir.exec(f, D.B.body(), st), s => D.Rnd(ds, ks, img, t, w, s), s => st2 => D.HR(ds, t, s, st2)):
  match h:
    case Tuple{p, _}:
      p(f)

def mv.done(-ds: List<&2, C.Def>, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, -st: C.Cir.State, -t: C.Term,
  -w: Nat, h: MV(ds, ks, img, st, t, w)) -> D.Ex(Nat, f => D.Ends(C.Cir.exec(f, D.B.body(), st))):
  match h:
    case Tuple{_, d}:
      d

# a frame of App q □ x: app_arg or app_val
def FK.isapp(k: D.FK) -> Bool:
  match k:
    case D.FK.arg{}:
      True{}
    case D.FK.val{}:
      True{}
    case _:
      False{}

# a value by its form, as the table says (I.table's field 4): every former but
# Tup
def A.tbl(t: C.Term) -> Bool:
  match t:
    case C.Term.Typ{_}:
      True{}
    case C.Term.All{_, _, _}:
      True{}
    case C.Term.Lam{_, _}:
      True{}
    case C.Term.Sig{_, _, _}:
      True{}
    case C.Term.Prj{_}:
      True{}
    case C.Term.Enu{_}:
      True{}
    case C.Term.Lab{_}:
      True{}
    case C.Term.Mat{_, _, _}:
      True{}
    case C.Term.Efq{}:
      True{}
    case C.Term.Eql{_, _, _}:
      True{}
    case C.Term.Rfl{}:
      True{}
    case _:
      False{}

# a λ, a λ-match of pairs or of labels: the redexes of M.redex's first cases
def A.node(t: C.Term) -> Bool:
  match t:
    case C.Term.Lam{_, _}:
      True{}
    case C.Term.Prj{_}:
      True{}
    case C.Term.Mat{_, _, _}:
      True{}
    case _:
      False{}

# the table's cell of the tag of a term's cell is a cell
def vt.of(-m: C.Cir.Cells, -im: U32, -fi: U32, -nx: U32, -f0: U32, +focus: C.Term, etag: {D.TgW(f0) == D.A.tag(focus) : U32},
  tb: D.Tbl(m, im, fi, nx)) -> {C.Cir.is_cell(U32.add(345, U32.and(f0, 63)), im, fi, nx) == True{} : Bool}:
  %Equal.sym(U32, D.TgW(f0), D.A.tag(focus), etag) : {C.Cir.is_cell(U32.add(345, _), im, fi, nx) == True{} : Bool}
  D.tbl.at(m, im, fi, nx, focus, tb)

# the test of M.ev on a cell flagged VALUE is not 0
def nz.of(-f0: U32, +e4: U32, hv: {U32.is_ne(U32.and(f0, 256), 0) == True{} : Bool}) ->
  {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)), Bool.to_u32(U32.is_ne(e4, 0)))) == False{} : Bool}:
  %Equal.sym(Bool, U32.is_ne(U32.and(f0, 256), 0), True{}, hv) :
    {U32.is_zero(U32.or(Bool.to_u32(_), Bool.to_u32(U32.is_ne(e4, 0)))) == False{} : Bool}
  D.or1(U32.is_ne(e4, 0))

# field 4 of the table's cell of a tag: 1 for a value by its form
def A.f4(t: C.Term) -> U32:
  match t:
    case C.Term.Var{_}:
      0
    case C.Term.Ref{_}:
      0
    case C.Term.Ann{_, _}:
      0
    case C.Term.Let{_, _, _}:
      0
    case C.Term.Typ{_}:
      1
    case C.Term.Min{_, _}:
      0
    case C.Term.All{_, _, _}:
      1
    case C.Term.Lam{_, _}:
      1
    case C.Term.App{_, _, _}:
      0
    case C.Term.Sig{_, _, _}:
      1
    case C.Term.Tup{_, _, _}:
      0
    case C.Term.Prj{_}:
      1
    case C.Term.Enu{_}:
      1
    case C.Term.Lab{_}:
      1
    case C.Term.Mat{_, _, _}:
      1
    case C.Term.Efq{}:
      1
    case C.Term.Eql{_, _, _}:
      1
    case C.Term.Rfl{}:
      1
    case C.Term.Rwt{_, _, _}:
      0

def tbl.f4(-m: C.Cir.Cells, -im: U32, -fi: U32, -nx: U32, t: C.Term, h: D.Tbl(m, im, fi, nx)) ->
  {D.Fd(4n, m, U32.add(345, D.A.tag(t))) == A.f4(t) : U32}:
  match t:
    case C.Term.Var{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}:
          e
    case C.Term.Ref{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}:
          e
    case C.Term.Ann{_, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}:
          e
    case C.Term.Let{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}:
          e
    case C.Term.Typ{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Min{_, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.All{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Lam{_, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.App{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Sig{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Tup{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Prj{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Enu{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Lab{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Mat{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Efq{}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Eql{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Rfl{}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Rwt{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e


# a value by its form, as the table says, has field 4 set
def f4.one(t: C.Term, hf: {A.tbl(t) == True{} : Bool}) -> {A.f4(t) == 1 : U32}:
  match t:
    case C.Term.Var{+x0}:
      D.bool.ft({A.f4(C.Term.Var{x0}) == 1 : U32}, hf)
    case C.Term.Ref{+x0}:
      D.bool.ft({A.f4(C.Term.Ref{x0}) == 1 : U32}, hf)
    case C.Term.Ann{+x0, +x1}:
      D.bool.ft({A.f4(C.Term.Ann{x0, x1}) == 1 : U32}, hf)
    case C.Term.Let{+x0, +x1, +x2}:
      D.bool.ft({A.f4(C.Term.Let{x0, x1, x2}) == 1 : U32}, hf)
    case C.Term.Typ{+x0}:
      {==}
    case C.Term.Min{+x0, +x1}:
      D.bool.ft({A.f4(C.Term.Min{x0, x1}) == 1 : U32}, hf)
    case C.Term.All{+x0, +x1, +x2}:
      {==}
    case C.Term.Lam{+x0, +x1}:
      {==}
    case C.Term.App{+x0, +x1, +x2}:
      D.bool.ft({A.f4(C.Term.App{x0, x1, x2}) == 1 : U32}, hf)
    case C.Term.Sig{+x0, +x1, +x2}:
      {==}
    case C.Term.Tup{+x0, +x1, +x2}:
      D.bool.ft({A.f4(C.Term.Tup{x0, x1, x2}) == 1 : U32}, hf)
    case C.Term.Prj{+x0}:
      {==}
    case C.Term.Enu{+x0}:
      {==}
    case C.Term.Lab{+x0}:
      {==}
    case C.Term.Mat{+x0, +x1, +x2}:
      {==}
    case C.Term.Efq{}:
      {==}
    case C.Term.Eql{+x0, +x1, +x2}:
      {==}
    case C.Term.Rfl{}:
      {==}
    case C.Term.Rwt{+x0, +x1, +x2}:
      D.bool.ft({A.f4(C.Term.Rwt{x0, x1, x2}) == 1 : U32}, hf)

# a value by its form, as the table says, is a value
def tbl.vals(+ds: List<&2, C.Def>, t: C.Term, hf: {A.tbl(t) == True{} : Bool}) ->
  {Bool.or(Bool.not(True{}), C.Eval.vals(ds, t, False{})) == True{} : Bool}:
  match t:
    case C.Term.Var{+x0}:
      D.bool.ft({Bool.or(Bool.not(True{}), C.Eval.vals(ds, C.Term.Var{x0}, False{})) == True{} : Bool}, hf)
    case C.Term.Ref{+x0}:
      D.bool.ft({Bool.or(Bool.not(True{}), C.Eval.vals(ds, C.Term.Ref{x0}, False{})) == True{} : Bool}, hf)
    case C.Term.Ann{+x0, +x1}:
      D.bool.ft({Bool.or(Bool.not(True{}), C.Eval.vals(ds, C.Term.Ann{x0, x1}, False{})) == True{} : Bool}, hf)
    case C.Term.Let{+x0, +x1, +x2}:
      D.bool.ft({Bool.or(Bool.not(True{}), C.Eval.vals(ds, C.Term.Let{x0, x1, x2}, False{})) == True{} : Bool}, hf)
    case C.Term.Typ{+x0}:
      {==}
    case C.Term.Min{+x0, +x1}:
      D.bool.ft({Bool.or(Bool.not(True{}), C.Eval.vals(ds, C.Term.Min{x0, x1}, False{})) == True{} : Bool}, hf)
    case C.Term.All{+x0, +x1, +x2}:
      {==}
    case C.Term.Lam{+x0, +x1}:
      {==}
    case C.Term.App{+x0, +x1, +x2}:
      D.bool.ft({Bool.or(Bool.not(True{}), C.Eval.vals(ds, C.Term.App{x0, x1, x2}, False{})) == True{} : Bool}, hf)
    case C.Term.Sig{+x0, +x1, +x2}:
      {==}
    case C.Term.Tup{+x0, +x1, +x2}:
      D.bool.ft({Bool.or(Bool.not(True{}), C.Eval.vals(ds, C.Term.Tup{x0, x1, x2}, False{})) == True{} : Bool}, hf)
    case C.Term.Prj{+x0}:
      {==}
    case C.Term.Enu{+x0}:
      {==}
    case C.Term.Lab{+x0}:
      {==}
    case C.Term.Mat{+x0, +x1, +x2}:
      {==}
    case C.Term.Efq{}:
      {==}
    case C.Term.Eql{+x0, +x1, +x2}:
      {==}
    case C.Term.Rfl{}:
      {==}
    case C.Term.Rwt{+x0, +x1, +x2}:
      D.bool.ft({Bool.or(Bool.not(True{}), C.Eval.vals(ds, C.Term.Rwt{x0, x1, x2}, False{})) == True{} : Bool}, hf)

def or1r(b: Bool) -> {U32.is_zero(U32.or(Bool.to_u32(b), 1)) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the test of M.ev on a value by its form is not 0
def nzf.of(-m: C.Cir.Cells, -im: U32, -fi: U32, -nx: U32, +f0: U32, +focus: C.Term, etag: {D.TgW(f0) == D.A.tag(focus) : U32},
  tb: D.Tbl(m, im, fi, nx), hf: {A.tbl(focus) == True{} : Bool}) ->
  {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)),
    Bool.to_u32(U32.is_ne(C.Cir.Cell.get(4n, C.Cir.Cells.get(m, U32.add(345, U32.and(f0, 63)))), 0)))) == False{} : Bool}:
  %Equal.sym(U32, D.TgW(f0), D.A.tag(focus), etag) :
    {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)),
      Bool.to_u32(U32.is_ne(C.Cir.Cell.get(4n, C.Cir.Cells.get(m, U32.add(345, _))), 0)))) == False{} : Bool}
  %Equal.sym(U32, D.Fd(4n, m, U32.add(345, D.A.tag(focus))), A.f4(focus), tbl.f4(m, im, fi, nx, focus, tb)) :
    {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)), Bool.to_u32(U32.is_ne(_, 0)))) == False{} : Bool}
  %Equal.sym(U32, A.f4(focus), 1, f4.one(focus, hf)) :
    {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)), Bool.to_u32(U32.is_ne(_, 0)))) == False{} : Bool}
  or1r(U32.is_ne(U32.and(f0, 256), 0))

# the test of M.ev on a value by its form, from the facts of its cell
def nzf.go(-ds: List<&2, C.Def>, -im: U32, -fi: U32, -nx: U32, +foc: U32, +m: C.Cir.Cells, +focus: C.Term,
  nd: D.Nd(ds, im, fi, nx, foc, C.Cir.Cells.get(m, foc), focus, D.A.tag(focus)), tb: D.Tbl(m, im, fi, nx),
  hf: {A.tbl(focus) == True{} : Bool}) ->
  {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(D.Fd(0n, m, foc), 256), 0)), Bool.to_u32(U32.is_ne(C.Cir.Cell.get(4n, C.Cir.Cells.get(m, U32.add(345, U32.and(D.Fd(0n, m, foc), 63)))), 0)))) == False{} : Bool}:
  match nd:
    case Tuple{_, Tuple{_, Tuple{etag, _}}}:
      nzf.of(m, im, fi, nx, D.Fd(0n, m, foc), focus, etag, tb, hf)

# M.ev, past its first statement, and past its second
def B.cond2() -> C.Cir.Expr:
  C.M.or(C.M.flag(C.M.g(C.R.c()), C.F.value()), C.M.ne(C.M.entry(4n, C.M.g(C.R.c())), C.M.c(0)))

# a halt
def eq.halt(+f: Nat, +x: U32, +st: C.Cir.State) -> {C.Cir.exec(f, C.Cir.Stmt.halt{x}, st) == C.Cir.Out.halt{x, st} : C.Cir.Out}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

# a then b, when a halts
def eq.seq.h(+f: Nat, a: C.Cir.Stmt, +b: C.Cir.Stmt, +st: C.Cir.State, +x: U32, +st1: C.Cir.State,
  e1: {C.Cir.exec(f, a, st) == C.Cir.Out.halt{x, st1} : C.Cir.Out}) ->
  {C.Cir.exec(f, C.Cir.Stmt.seq{a, b}, st) == C.Cir.Out.halt{x, st1} : C.Cir.Out}:
  match f:
    case 0n:
      %Equal.sym(C.Cir.Out, C.Cir.exec(0n, a, st), C.Cir.Out.halt{x, st1}, e1) :
        {C.Cir.exec.then(_, u => C.Cir.exec(0n, b, u)) == C.Cir.Out.halt{x, st1} : C.Cir.Out}
      {==}
    case 1n+g:
      %Equal.sym(C.Cir.Out, C.Cir.exec(1n+g, a, st), C.Cir.Out.halt{x, st1}, e1) :
        {C.Cir.exec.then(_, u => C.Cir.exec(1n+g, b, u)) == C.Cir.Out.halt{x, st1} : C.Cir.Out}
      {==}

# a test of the tag of a cell whose tag is another
def tag.ne(+f0: U32, +tag: U32, +x: U32, etag: {D.TgW(f0) == tag : U32}, e: {U32.is_eq(tag, x) == False{} : Bool}) ->
  {U32.is_zero(C.Wasm.op(C.Wasm.Op.eq{}, D.TgW(f0), x)) == True{} : Bool}:
  %Equal.sym(U32, D.TgW(f0), tag, etag) : {U32.is_zero(C.Wasm.op(C.Wasm.Op.eq{}, _, x)) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(tag, x), False{}, e) : {U32.is_zero(Bool.to_u32(_)) == True{} : Bool}
  {==}

# the test of M.ev on a cell not flagged VALUE, whose tag's table field 4 is 0, is 0
def z.of(-m: C.Cir.Cells, -im: U32, -fi: U32, -nx: U32, +f0: U32, +focus: C.Term, etag: {D.TgW(f0) == D.A.tag(focus) : U32},
  tb: D.Tbl(m, im, fi, nx), hv: {U32.is_ne(U32.and(f0, 256), 0) == False{} : Bool}, h0: {A.f4(focus) == 0 : U32}) ->
  {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)),
    Bool.to_u32(U32.is_ne(C.Cir.Cell.get(4n, C.Cir.Cells.get(m, U32.add(345, U32.and(f0, 63)))), 0)))) == True{} : Bool}:
  %Equal.sym(U32, D.TgW(f0), D.A.tag(focus), etag) :
    {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)),
      Bool.to_u32(U32.is_ne(C.Cir.Cell.get(4n, C.Cir.Cells.get(m, U32.add(345, _))), 0)))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(4n, m, U32.add(345, D.A.tag(focus))), A.f4(focus), tbl.f4(m, im, fi, nx, focus, tb)) :
    {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)), Bool.to_u32(U32.is_ne(_, 0)))) == True{} : Bool}
  %Equal.sym(U32, A.f4(focus), 0, h0) :
    {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)), Bool.to_u32(U32.is_ne(_, 0)))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_ne(U32.and(f0, 256), 0), False{}, hv) :
    {U32.is_zero(U32.or(Bool.to_u32(_), Bool.to_u32(U32.is_ne(0, 0)))) == True{} : Bool}
  {==}

# Eval: a focus with no step that is no value makes its frames' term so
def ev.stuck(+ds: List<&2, C.Def>, fs: List<&2, D.AF>, +u: C.Term, hfs: D.AFs.ok(ds, fs),
  hs: {C.Eval.step(ds, u) == None{} : Maybe<C.Term>}, hv: {C.Eval.vals(ds, u, False{}) == False{} : Bool}) ->
  D.P2({C.Eval.step(ds, D.A.plugs(fs, u)) == None{} : Maybe<C.Term>}, {C.Eval.vals(ds, D.A.plugs(fs, u), False{}) == False{} : Bool}):
  EV.ev.stuck(ds, fs, u, hfs, hs, hv)

# a halt of a round, from a term equal to t
def hr.eq(+ds: List<&2, C.Def>, -u: C.Term, -t: C.Term, -s: U32, -st: C.Cir.State, e: {u == t : C.Term},
  h: D.HR(ds, u, s, st)) -> D.HR(ds, t, s, st):
  %e : D.HR(ds, _, s, st)
  h

# a halt with 2 from a term that is stuck
def hr.stuck(+ds: List<&2, C.Def>, +t: C.Term, -st: C.Cir.State,
  h: D.P2({C.Eval.step(ds, t) == None{} : Maybe<C.Term>}, {C.Eval.vals(ds, t, False{}) == False{} : Bool})) -> D.HR(ds, t, 2, st):
  match h:
    case Tuple{es, ev}:
      Inr{({==}, (es, D.res.nv(ds, t, ev)))}

# M.ev's tests of the tag, from the last
def B.e6() -> C.Cir.Stmt:
  C.M.if(C.M.eq(C.M.g(C.R.tag()), C.M.c(C.T.min())), C.M.ev.min(), C.M.halt(2))

def B.e5() -> C.Cir.Stmt:
  C.M.if(C.M.eq(C.M.g(C.R.tag()), C.M.c(C.T.rwt())), C.M.ev.rwt(), B.e6())

def B.e4() -> C.Cir.Stmt:
  C.M.if(C.M.eq(C.M.g(C.R.tag()), C.M.c(C.T.tup())), C.M.ev.tup(), B.e5())

def B.e3() -> C.Cir.Stmt:
  C.M.if(C.M.eq(C.M.g(C.R.tag()), C.M.c(C.T.let())), C.M.ev.let(), B.e4())

def B.e2() -> C.Cir.Stmt:
  C.M.if(C.M.eq(C.M.g(C.R.tag()), C.M.c(C.T.ann())), C.M.ev.ann(), B.e3())

def B.e1() -> C.Cir.Stmt:
  C.M.if(C.M.eq(C.M.g(C.R.tag()), C.M.c(C.T.ref())), C.M.ev.ref(), B.e2())

def B.else() -> C.Cir.Stmt:
  C.M.if(C.M.eq(C.M.g(C.R.tag()), C.M.c(C.T.app())), C.M.ev.app(), B.e1())

def B.ev2() -> C.Cir.Stmt:
  C.M.do([C.M.set(C.R.tag(), C.M.tag(C.M.g(C.R.c()))), C.M.if(B.cond2(), C.M.set(C.R.mode(), C.M.c(1)), B.else())])

def B.ev3() -> C.Cir.Stmt:
  C.M.do([C.M.if(B.cond2(), C.M.set(C.R.mode(), C.M.c(1)), B.else())])

# M.ev's first two statements, from a state of mode 0: c and tag get the
# focus' cell and its tag
def ev.st1(+foc: U32, +sp: U32, +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +r63: U32, +m: C.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>) -> C.Cir.State:
  D.St.set(D.S(foc, 0, sp, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp), 8n, foc)

def ev.st2(+foc: U32, +sp: U32, +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +r63: U32, +m: C.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>) -> C.Cir.State:
  D.St.set(ev.st1(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp), 10n, D.TgW(D.Fd(0n, m, foc)))

# a round from mode 0 whose focus' cell c is flagged VALUE: c and tag are
# set, then the mode is 1
def ev.val.E(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32,
  +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +r63: U32, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, U32>, +focus: C.Term,
  +nd: D.Nd(ds, im, fi, nx, foc, C.Cir.Cells.get(m, foc), focus, D.A.tag(focus)),
  +tb: D.Tbl(m, im, fi, nx), +nz2: {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(D.Fd(0n, m, foc), 256), 0)), Bool.to_u32(U32.is_ne(C.Cir.Cell.get(4n, C.Cir.Cells.get(m, U32.add(345, U32.and(D.Fd(0n, m, foc), 63)))), 0)))) == False{} : Bool}) ->
  {C.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.Out.next{D.St.set(ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp), 1n, 1)} : C.Cir.Out}:
  match nd:
    case Tuple{+valid, Tuple{_, Tuple{+etag, _}}}:
      +st1 = ev.st1(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp)
      +st2 = ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp)
      +st3 = D.St.set(st2, 1n, 1)
      +f0 = D.Fd(0n, m, foc)
      +ef1 = D.ev.fld(0n, C.M.g(C.R.c()), D.St.regs(st1), m, nx, fi, im, pg, lim, inp, Nil{}, 0, foc, {==}, valid)
      +ef2 = D.ev.fld(0n, C.M.g(C.R.c()), D.St.regs(st2), m, nx, fi, im, pg, lim, inp, Nil{}, 0, foc, {==}, valid)
      +etg = D.ev.op(C.Wasm.Op.and{}, C.M.f(0n, C.M.g(C.R.c())), C.M.c(63), st1, f0, 63, ef1, {==})
      +etg2 = D.ev.op(C.Wasm.Op.and{}, C.M.f(0n, C.M.g(C.R.c())), C.M.c(63), st2, f0, 63, ef2, {==})
      +efl = D.ev.op(C.Wasm.Op.ne{}, C.M.and(C.M.f(0n, C.M.g(C.R.c())), C.M.c(256)), C.M.c(0), st2, C.Wasm.op(C.Wasm.Op.and{}, f0, 256), 0,
        D.ev.op(C.Wasm.Op.and{}, C.M.f(0n, C.M.g(C.R.c())), C.M.c(256), st2, f0, 256, ef2, {==}), {==})
      +addr = C.Wasm.op(C.Wasm.Op.add{}, 345, C.Wasm.op(C.Wasm.Op.and{}, f0, 63))
      +eadr = D.ev.op(C.Wasm.Op.add{}, C.M.c(345), C.M.tag(C.M.g(C.R.c())), st2, 345, C.Wasm.op(C.Wasm.Op.and{}, f0, 63), {==}, etg2)
      +vt = vt.of(m, im, fi, nx, f0, focus, etag, tb)
      +e4 = C.Cir.Cell.get(4n, C.Cir.Cells.get(m, addr))
      +ee4 = D.ev.fld(4n, C.M.add(C.M.c(345), C.M.tag(C.M.g(C.R.c()))), D.St.regs(st2), m, nx, fi, im, pg, lim, inp, Nil{}, 0, addr, eadr, vt)
      +ene = D.ev.op(C.Wasm.Op.ne{}, C.M.entry(4n, C.M.g(C.R.c())), C.M.c(0), st2, e4, 0, ee4, {==})
      +flv = C.Wasm.op(C.Wasm.Op.ne{}, C.Wasm.op(C.Wasm.Op.and{}, f0, 256), 0)
      +nev = C.Wasm.op(C.Wasm.Op.ne{}, e4, 0)
      +ec2 = D.ev.op(C.Wasm.Op.or{}, C.M.flag(C.M.g(C.R.c()), C.F.value()), C.M.ne(C.M.entry(4n, C.M.g(C.R.c())), C.M.c(0)), st2, flv, nev, efl, ene)
      +e3a = Equal.trans(C.Cir.Out, C.Cir.exec(f, C.Cir.Stmt.if{B.cond2(), C.M.set(C.R.mode(), C.M.c(1)), B.else()}, st2),
        C.Cir.exec(f, C.M.set(C.R.mode(), C.M.c(1)), st2), C.Cir.Out.next{st3},
        D.eq.if.t(f, B.cond2(), C.M.set(C.R.mode(), C.M.c(1)), B.else(), st2, C.Wasm.op(C.Wasm.Op.or{}, flv, nev), ec2, nz2),
        D.eq.set(f, 1n, C.M.c(1), st2, 1, {==}, {==}))
      %Equal.sym(C.Cir.Out, C.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)), C.Cir.exec(f, C.M.ev(), D.S(foc, 0, sp, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)),
        D.eq.if.t(f, C.M.eq(C.M.g(C.R.mode()), C.M.c(0)), C.M.ev(), C.M.ret(), D.S(foc, 0, sp, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp), 1, {==}, {==})) :
        {_ == C.Cir.Out.next{st3} : C.Cir.Out}
      %D.rw.seq(f, C.M.set(C.R.c(), C.M.g(C.R.focus())), B.ev2(), D.S(foc, 0, sp, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp), st1,
        D.eq.set(f, 8n, C.M.g(C.R.focus()), D.S(foc, 0, sp, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp), foc, {==}, {==})) : {_ == C.Cir.Out.next{st3} : C.Cir.Out}
      %D.rw.seq(f, C.M.set(C.R.tag(), C.M.tag(C.M.g(C.R.c()))), B.ev3(), st1, st2,
        D.eq.set(f, 10n, C.M.tag(C.M.g(C.R.c())), st1, D.TgW(f0), etg, {==})) : {_ == C.Cir.Out.next{st3} : C.Cir.Out}
      %D.rw.seq(f, C.Cir.Stmt.if{B.cond2(), C.M.set(C.R.mode(), C.M.c(1)), B.else()}, C.Cir.Stmt.nop{}, st2, st3, e3a) :
        {_ == C.Cir.Out.next{st3} : C.Cir.Out}
      %Equal.sym(C.Cir.Out, C.Cir.exec(f, C.Cir.Stmt.nop{}, st3), C.Cir.Out.next{st3}, D.eq.nop(f, st3)) :
        {_ == C.Cir.Out.next{st3} : C.Cir.Out}
      {==}

# the table of the image
def img.tbl(-ds: List<&2, C.Def>, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, -m: C.Cir.Cells, -im: U32,
  -fi: U32, -nx: U32, io: D.ImgOK(ds, ks, img, m, im, fi, nx)) -> D.Tbl(m, im, fi, nx):
  match io:
    case Tuple{tb, _}:
      tb

# a cell flagged VALUE stands for a value
def nd.val(-ds: List<&2, C.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, -x: C.Cir.Cell, -t: C.Term, -tag: U32,
  nd: D.Nd(ds, im, fi, nx, c, x, t, tag), hv: {D.FlW(C.Cir.Cell.get(0n, x), 256) == True{} : Bool}) ->
  {Bool.or(Bool.not(True{}), C.Eval.vals(ds, t, False{})) == True{} : Bool}:
  match nd:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{nv, _}}}}:
      %hv : {Bool.or(Bool.not(_), C.Eval.vals(ds, t, False{})) == True{} : Bool}
      nv

# mode 1 costs less than mode 0 by the focus' measure
def ret.lt(+focus: C.Term, +fs: List<&2, D.AF>, -w: Nat, ew: {D.A.w(False{}, focus, fs) == w : Nat}) ->
  N.Le(1n+D.A.w(True{}, focus, fs), w):
  %ew : N.Le(1n+D.A.w(True{}, focus, fs), _)
  N.add_mono(1n, D.A.w3(focus), D.A.w.frames(fs), D.A.w.frames(fs), D.A.w3.pos(focus), N.le_refl(D.A.w.frames(fs)))

def ev.val.mv(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32,
  +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +r63: U32, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: C.Term,
  +et: {D.A.plugs(fs, focus) == t : C.Term}, ew: {D.A.w(False{}, focus, fs) == w : Nat}, +afs: D.AFs.ok(ds, fs),
  +isf: D.Is(ds, m, im, fi, nx, ks, img, foc, focus), +frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, fs),
  +hp: D.Heap(m, nx, fi, im, [foc], pend, ps), +io: D.ImgOK(ds, ks, img, m, im, fi, nx),
  +nz2: {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(D.Fd(0n, m, foc), 256), 0)), Bool.to_u32(U32.is_ne(C.Cir.Cell.get(4n, C.Cir.Cells.get(m, U32.add(345, U32.and(D.Fd(0n, m, foc), 63)))), 0)))) == False{} : Bool},
  +evv: {Bool.or(Bool.not(True{}), C.Eval.vals(ds, focus, False{})) == True{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp), t, w):
  +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, focus, isf)
  +tb = img.tbl(ds, ks, img, m, im, fi, nx, io)
  +w2 = D.A.w(True{}, focus, fs)
  +inv3 = {(D.Wit{True{}, focus, fs, foc, sp, pend, ps, D.R60.of(D.St.regs(D.St.set(ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp), 1n, 1)))},
    (et, ({==}, (evv,
    (afs, ({==}, (isf, (frs, (hp, (io, ({==}, {==}))))))))))) : D.Inv(ds, ks, img, D.St.set(ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp), 1n, 1), t, w2)}
  +lt = ret.lt(focus, fs, w, ew)
  (f => (%Equal.sym(C.Cir.Out, C.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)), C.Cir.Out.next{D.St.set(ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp), 1n, 1)},
      ev.val.E(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp, focus, nd, tb, nz2)) :
      D.Post(False{}, _, s => D.Rnd(ds, ks, img, t, w, s), s => st2 => D.HR(ds, t, s, st2));
      Inl{(w2, (inv3, lt))}),
   (0n, (%Equal.sym(C.Cir.Out, C.Cir.exec(0n, D.B.body(), D.S(foc, 0, sp, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)), C.Cir.Out.next{D.St.set(ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp), 1n, 1)},
      ev.val.E(0n, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp, focus, nd, tb, nz2)) : D.Ends(_);
      Unit{})))

# the tests of M.ev on a cell of the tag 0: none takes it, a halt with 2
def B.chain0(+f: Nat, +st: C.Cir.State, +f0: U32,
  +etag: {D.TgW(f0) == 0 : U32}, +er: {C.Cir.eval(C.M.g(C.R.tag()), st) == Some{D.TgW(f0)} : Maybe<&2, U32>}) ->
  {C.Cir.exec(f, B.else(), st) == C.Cir.Out.halt{2, st} : C.Cir.Out}:
  %Equal.sym(C.Cir.Out, C.Cir.exec(f, B.else(), st), C.Cir.exec(f, B.e1(), st),
    D.eq.if.e(f, C.M.eq(C.M.g(C.R.tag()), C.M.c(8)), C.M.ev.app(), B.e1(), st, C.Wasm.op(C.Wasm.Op.eq{}, D.TgW(f0), 8),
      D.ev.op(C.Wasm.Op.eq{}, C.M.g(C.R.tag()), C.M.c(8), st, D.TgW(f0), 8, er, {==}), tag.ne(f0, 0, 8, etag, {==}))) :
    {_ == C.Cir.Out.halt{2, st} : C.Cir.Out}
  %Equal.sym(C.Cir.Out, C.Cir.exec(f, B.e1(), st), C.Cir.exec(f, B.e2(), st),
    D.eq.if.e(f, C.M.eq(C.M.g(C.R.tag()), C.M.c(1)), C.M.ev.ref(), B.e2(), st, C.Wasm.op(C.Wasm.Op.eq{}, D.TgW(f0), 1),
      D.ev.op(C.Wasm.Op.eq{}, C.M.g(C.R.tag()), C.M.c(1), st, D.TgW(f0), 1, er, {==}), tag.ne(f0, 0, 1, etag, {==}))) :
    {_ == C.Cir.Out.halt{2, st} : C.Cir.Out}
  %Equal.sym(C.Cir.Out, C.Cir.exec(f, B.e2(), st), C.Cir.exec(f, B.e3(), st),
    D.eq.if.e(f, C.M.eq(C.M.g(C.R.tag()), C.M.c(2)), C.M.ev.ann(), B.e3(), st, C.Wasm.op(C.Wasm.Op.eq{}, D.TgW(f0), 2),
      D.ev.op(C.Wasm.Op.eq{}, C.M.g(C.R.tag()), C.M.c(2), st, D.TgW(f0), 2, er, {==}), tag.ne(f0, 0, 2, etag, {==}))) :
    {_ == C.Cir.Out.halt{2, st} : C.Cir.Out}
  %Equal.sym(C.Cir.Out, C.Cir.exec(f, B.e3(), st), C.Cir.exec(f, B.e4(), st),
    D.eq.if.e(f, C.M.eq(C.M.g(C.R.tag()), C.M.c(3)), C.M.ev.let(), B.e4(), st, C.Wasm.op(C.Wasm.Op.eq{}, D.TgW(f0), 3),
      D.ev.op(C.Wasm.Op.eq{}, C.M.g(C.R.tag()), C.M.c(3), st, D.TgW(f0), 3, er, {==}), tag.ne(f0, 0, 3, etag, {==}))) :
    {_ == C.Cir.Out.halt{2, st} : C.Cir.Out}
  %Equal.sym(C.Cir.Out, C.Cir.exec(f, B.e4(), st), C.Cir.exec(f, B.e5(), st),
    D.eq.if.e(f, C.M.eq(C.M.g(C.R.tag()), C.M.c(10)), C.M.ev.tup(), B.e5(), st, C.Wasm.op(C.Wasm.Op.eq{}, D.TgW(f0), 10),
      D.ev.op(C.Wasm.Op.eq{}, C.M.g(C.R.tag()), C.M.c(10), st, D.TgW(f0), 10, er, {==}), tag.ne(f0, 0, 10, etag, {==}))) :
    {_ == C.Cir.Out.halt{2, st} : C.Cir.Out}
  %Equal.sym(C.Cir.Out, C.Cir.exec(f, B.e5(), st), C.Cir.exec(f, B.e6(), st),
    D.eq.if.e(f, C.M.eq(C.M.g(C.R.tag()), C.M.c(18)), C.M.ev.rwt(), B.e6(), st, C.Wasm.op(C.Wasm.Op.eq{}, D.TgW(f0), 18),
      D.ev.op(C.Wasm.Op.eq{}, C.M.g(C.R.tag()), C.M.c(18), st, D.TgW(f0), 18, er, {==}), tag.ne(f0, 0, 18, etag, {==}))) :
    {_ == C.Cir.Out.halt{2, st} : C.Cir.Out}
  %Equal.sym(C.Cir.Out, C.Cir.exec(f, B.e6(), st), C.Cir.exec(f, C.M.halt(2), st),
    D.eq.if.e(f, C.M.eq(C.M.g(C.R.tag()), C.M.c(5)), C.M.ev.min(), C.M.halt(2), st, C.Wasm.op(C.Wasm.Op.eq{}, D.TgW(f0), 5),
      D.ev.op(C.Wasm.Op.eq{}, C.M.g(C.R.tag()), C.M.c(5), st, D.TgW(f0), 5, er, {==}), tag.ne(f0, 0, 5, etag, {==}))) :
    {_ == C.Cir.Out.halt{2, st} : C.Cir.Out}
  eq.halt(f, 2, st)

# a round from mode 0 whose focus' cell is a variable: no case of M.ev takes
# it, a halt with 2
def ev.var.E(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32,
  +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +r63: U32, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, U32>, +i: Nat,
  +nd: D.Nd(ds, im, fi, nx, foc, C.Cir.Cells.get(m, foc), C.Term.Var{i}, 0),
  +tb: D.Tbl(m, im, fi, nx), +hv: {D.Fl(m, foc, 256) == False{} : Bool}) ->
  {C.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)) == C.Cir.Out.halt{2, ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  match nd:
    case Tuple{+valid, Tuple{_, Tuple{+etag, _}}}:
      +st1 = ev.st1(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp)
      +st2 = ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp)
      +f0 = D.Fd(0n, m, foc)
      +ef1 = D.ev.fld(0n, C.M.g(C.R.c()), D.St.regs(st1), m, nx, fi, im, pg, lim, inp, Nil{}, 0, foc, {==}, valid)
      +ef2 = D.ev.fld(0n, C.M.g(C.R.c()), D.St.regs(st2), m, nx, fi, im, pg, lim, inp, Nil{}, 0, foc, {==}, valid)
      +etg = D.ev.op(C.Wasm.Op.and{}, C.M.f(0n, C.M.g(C.R.c())), C.M.c(63), st1, f0, 63, ef1, {==})
      +etg2 = D.ev.op(C.Wasm.Op.and{}, C.M.f(0n, C.M.g(C.R.c())), C.M.c(63), st2, f0, 63, ef2, {==})
      +efl = D.ev.op(C.Wasm.Op.ne{}, C.M.and(C.M.f(0n, C.M.g(C.R.c())), C.M.c(256)), C.M.c(0), st2, C.Wasm.op(C.Wasm.Op.and{}, f0, 256), 0,
        D.ev.op(C.Wasm.Op.and{}, C.M.f(0n, C.M.g(C.R.c())), C.M.c(256), st2, f0, 256, ef2, {==}), {==})
      +addr = C.Wasm.op(C.Wasm.Op.add{}, 345, C.Wasm.op(C.Wasm.Op.and{}, f0, 63))
      +eadr = D.ev.op(C.Wasm.Op.add{}, C.M.c(345), C.M.tag(C.M.g(C.R.c())), st2, 345, C.Wasm.op(C.Wasm.Op.and{}, f0, 63), {==}, etg2)
      +vt = vt.of(m, im, fi, nx, f0, C.Term.Var{i}, etag, tb)
      +e4 = C.Cir.Cell.get(4n, C.Cir.Cells.get(m, addr))
      +ee4 = D.ev.fld(4n, C.M.add(C.M.c(345), C.M.tag(C.M.g(C.R.c()))), D.St.regs(st2), m, nx, fi, im, pg, lim, inp, Nil{}, 0, addr, eadr, vt)
      +ene = D.ev.op(C.Wasm.Op.ne{}, C.M.entry(4n, C.M.g(C.R.c())), C.M.c(0), st2, e4, 0, ee4, {==})
      +flv = C.Wasm.op(C.Wasm.Op.ne{}, C.Wasm.op(C.Wasm.Op.and{}, f0, 256), 0)
      +nev = C.Wasm.op(C.Wasm.Op.ne{}, e4, 0)
      +ec2 = D.ev.op(C.Wasm.Op.or{}, C.M.flag(C.M.g(C.R.c()), C.F.value()), C.M.ne(C.M.entry(4n, C.M.g(C.R.c())), C.M.c(0)), st2, flv, nev, efl, ene)
      +z2 = z.of(m, im, fi, nx, f0, C.Term.Var{i}, etag, tb, hv, {==})
      +e3a = Equal.trans(C.Cir.Out, C.Cir.exec(f, C.Cir.Stmt.if{B.cond2(), C.M.set(C.R.mode(), C.M.c(1)), B.else()}, st2),
        C.Cir.exec(f, B.else(), st2), C.Cir.Out.halt{2, st2},
        D.eq.if.e(f, B.cond2(), C.M.set(C.R.mode(), C.M.c(1)), B.else(), st2, C.Wasm.op(C.Wasm.Op.or{}, flv, nev), ec2, z2),
        B.chain0(f, st2, f0, etag, {==}))
      %Equal.sym(C.Cir.Out, C.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)), C.Cir.exec(f, C.M.ev(), D.S(foc, 0, sp, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)),
        D.eq.if.t(f, C.M.eq(C.M.g(C.R.mode()), C.M.c(0)), C.M.ev(), C.M.ret(), D.S(foc, 0, sp, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp), 1, {==}, {==})) :
        {_ == C.Cir.Out.halt{2, st2} : C.Cir.Out}
      %D.rw.seq(f, C.M.set(C.R.c(), C.M.g(C.R.focus())), B.ev2(), D.S(foc, 0, sp, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp), st1,
        D.eq.set(f, 8n, C.M.g(C.R.focus()), D.S(foc, 0, sp, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp), foc, {==}, {==})) : {_ == C.Cir.Out.halt{2, st2} : C.Cir.Out}
      %D.rw.seq(f, C.M.set(C.R.tag(), C.M.tag(C.M.g(C.R.c()))), B.ev3(), st1, st2,
        D.eq.set(f, 10n, C.M.tag(C.M.g(C.R.c())), st1, D.TgW(f0), etg, {==})) : {_ == C.Cir.Out.halt{2, st2} : C.Cir.Out}
      eq.seq.h(f, C.Cir.Stmt.if{B.cond2(), C.M.set(C.R.mode(), C.M.c(1)), B.else()}, C.Cir.Stmt.nop{}, st2, 2, st2, e3a)

# the parts of an if, to name the parts of a statement of impl.bend without
# copying them
def stmt.cond(x: C.Cir.Stmt) -> C.Cir.Expr:
  match x:
    case C.Cir.Stmt.if{c, _, _}:
      c
    case _:
      C.Cir.Expr.const{0}

def stmt.then(x: C.Cir.Stmt) -> C.Cir.Stmt:
  match x:
    case C.Cir.Stmt.if{_, t, _}:
      t
    case _:
      C.Cir.Stmt.nop{}

def stmt.else(x: C.Cir.Stmt) -> C.Cir.Stmt:
  match x:
    case C.Cir.Stmt.if{_, _, e}:
      e
    case _:
      C.Cir.Stmt.nop{}

# a weaker outcome
def post.map(dn: Bool, o: C.Cir.Out, -Q1: C.Cir.State -> Type, -Q2: C.Cir.State -> Type, -H1: U32 -> C.Cir.State -> Type,
  -H2: U32 -> C.Cir.State -> Type, h: D.Post(dn, o, Q1, H1), q: @st: C.Cir.State -> Q1(st) -> Q2(st),
  hh: @s: U32 -> @st: C.Cir.State -> H1(s, st) -> H2(s, st)) -> D.Post(dn, o, Q2, H2):
  match o:
    case C.Cir.Out.next{st}:
      q(st, h)
    case C.Cir.Out.halt{s, st}:
      hh(s, st, h)
    case C.Cir.Out.out_of_memory{}:
      Unit{}
    case C.Cir.Out.trap{}:
      h
    case C.Cir.Out.not_done{}:
      h

# the result of a value is its bytes
def res.val(+ds: List<&2, C.Def>, +v: C.Term, -x: Maybe<&2, List<&2, U32>>, ev: {C.Eval.vals(ds, v, False{}) == True{} : Bool},
  eu: {C.Program.unbytes(v) == x : Maybe<&2, List<&2, U32>>}) -> {C.Program.result(ds, Some{v}) == x : Maybe<&2, List<&2, U32>>}:
  %Equal.sym(Bool, C.Eval.vals(ds, v, False{}), True{}, ev) : {C.Program.result.if(_, v) == x : Maybe<&2, List<&2, U32>>}
  eu

# M.out's halts are a round's, from its value v
def out.hr(+ds: List<&2, C.Def>, +v: C.Term, +ev: {C.Eval.vals(ds, v, False{}) == True{} : Bool}, -s: U32, -st2: C.Cir.State,
  h: D.OutH(v, s, st2)) -> D.HR(ds, v, s, st2):
  match h:
    case Inl{x}:
      (e0, eu) = x
      Inl{(e0, (ev.stops(ds, v, ev), res.val(ds, v, Some{List.reverse(&2, U32, D.St.out(st2))}, ev, eu)))}
    case Inr{x}:
      (e2, eu) = x
      Inr{(e2, (ev.stops(ds, v, ev), res.val(ds, v, None{}, ev, eu)))}

# a round from mode 1 with no frame is M.out
def out.E(+f: Nat, +foc: U32, +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +r63: U32, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, U32>) -> {C.Cir.exec(f, D.B.body(), D.S(foc, 1, 0, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)) == C.Cir.exec(f, C.M.out(), D.S(foc, 1, 0, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  Equal.trans(C.Cir.Out, C.Cir.exec(f, D.B.body(), D.S(foc, 1, 0, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)), C.Cir.exec(f, C.M.ret(), D.S(foc, 1, 0, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)), C.Cir.exec(f, C.M.out(), D.S(foc, 1, 0, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)),
    D.eq.if.e(f, C.M.eq(C.M.g(C.R.mode()), C.M.c(0)), C.M.ev(), C.M.ret(), D.S(foc, 1, 0, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp), 0, {==}, {==}),
    D.eq.if.t(f, stmt.cond(C.M.ret()), stmt.then(C.M.ret()), stmt.else(C.M.ret()), D.S(foc, 1, 0, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp), 1, {==}, {==}))

def out.mv(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +pend: U32,
  +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +r63: U32, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>,
  +t: C.Term, +w: Nat, +focus: C.Term, +et: {focus == t : C.Term},
  +ev: {C.Eval.vals(ds, focus, False{}) == True{} : Bool}, +isf: D.Is(ds, m, im, fi, nx, ks, img, foc, focus),
  +ks2: List<&2, List<&2, U32>>, +hk: {ks == C.Img.known(ks2) : List<&2, List<&2, U32>>}) ->
  MV(ds, ks, img, D.S(foc, 1, 0, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp), t, w):
  +od = out.done(ds, ks, img, foc, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp, focus, ks2, isf, hk)
  +f1 = D.Ex.fst(Nat, f => D.Ends(C.Cir.exec(f, C.M.out(), D.S(foc, 1, 0, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp))), od)
  (+f => (%Equal.sym(C.Cir.Out, C.Cir.exec(f, D.B.body(), D.S(foc, 1, 0, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)), C.Cir.exec(f, C.M.out(), D.S(foc, 1, 0, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)),
      out.E(f, foc, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp)) :
      D.Post(False{}, _, s => D.Rnd(ds, ks, img, t, w, s), s => st2 => D.HR(ds, t, s, st2));
      post.map(False{}, C.Cir.exec(f, C.M.out(), D.S(foc, 1, 0, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)), st => Empty, s => D.Rnd(ds, ks, img, t, w, s),
        s => st2 => D.OutH(focus, s, st2), s => st2 => D.HR(ds, t, s, st2),
        out.post(f, ds, ks, img, foc, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp, focus, ks2, isf, hk),
        st => h => Empty.absurd(D.Rnd(ds, ks, img, t, w, st), h),
        s => st2 => h => hr.eq(ds, focus, t, s, st2, et, out.hr(ds, focus, ev, s, st2, h)))),
   (f1, (%Equal.sym(C.Cir.Out, C.Cir.exec(f1, D.B.body(), D.S(foc, 1, 0, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)), C.Cir.exec(f1, C.M.out(), D.S(foc, 1, 0, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)),
      out.E(f1, foc, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp)) : D.Ends(_);
      D.Ex.snd(Nat, f => D.Ends(C.Cir.exec(f, C.M.out(), D.S(foc, 1, 0, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp))), od))))

# the image's names, the machine's first
def img.ks(-ds: List<&2, C.Def>, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, -m: C.Cir.Cells, -im: U32,
  -fi: U32, -nx: U32, io: D.ImgOK(ds, ks, img, m, im, fi, nx)) -> D.Ex(List<&2, List<&2, U32>>, ks2 => {ks == C.Img.known(ks2) : List<&2, List<&2, U32>>}):
  match io:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{k, _}}}}}}:
      k

# The moves, one lemma each (open where the body is ?TODO)

# mode 0, a focus flagged VALUE: a value, mode 1; an admin move
def mv.ev.val(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, focus, fs, ps), +hv: {D.Fl(m, foc, 256) == True{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match rest:
    case D.R60{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62, +r63}:
      match iv:
        case Tuple{+et, Tuple{+ew, Tuple{_, Tuple{+afs, Tuple{_, Tuple{+isf, Tuple{+frs, Tuple{+hp, Tuple{+io, Tuple{_, _}}}}}}}}}}:
          +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, focus, isf)
          ev.val.mv(ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, et, ew, afs, isf, frs, hp,
            io, nz.of(D.Fd(0n, m, foc), C.Cir.Cell.get(4n, C.Cir.Cells.get(m, U32.add(345, U32.and(D.Fd(0n, m, foc), 63)))), hv),
            nd.val(ds, im, fi, nx, foc, C.Cir.Cells.get(m, foc), focus, D.A.tag(focus), nd, hv))

# mode 0, a focus that is a value by its form, as the table says (A.tbl): mode 1; an admin move
def mv.ev.former(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, focus, fs, ps), +hf: {A.tbl(focus) == True{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match rest:
    case D.R60{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62, +r63}:
      match iv:
        case Tuple{+et, Tuple{+ew, Tuple{_, Tuple{+afs, Tuple{_, Tuple{+isf, Tuple{+frs, Tuple{+hp, Tuple{+io, Tuple{_, _}}}}}}}}}}:
          +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, focus, isf)
          ev.val.mv(ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, et, ew, afs, isf, frs, hp,
            io, nzf.go(ds, im, fi, nx, foc, m, focus, nd, img.tbl(ds, ks, img, m, im, fi, nx, io), hf), tbl.vals(ds, focus, hf))

# mode 0, a variable: free in the whole term, which has no step and is no value; halt 2
def mv.ev.var(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +i: Nat,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, C.Term.Var{i}, fs, ps), +hv: {D.Fl(m, foc, 256) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match rest:
    case D.R60{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62, +r63}:
      match iv:
        case Tuple{+et, Tuple{_, Tuple{_, Tuple{+afs, Tuple{_, Tuple{+isf, Tuple{_, Tuple{_, Tuple{+io, Tuple{_, _}}}}}}}}}}:
          +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, C.Term.Var{i}, isf)
          +tb = img.tbl(ds, ks, img, m, im, fi, nx, io)
          hr = hr.eq(ds, D.A.plugs(fs, C.Term.Var{i}), t, 2, ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp), et,
            hr.stuck(ds, D.A.plugs(fs, C.Term.Var{i}), ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp), ev.stuck(ds, fs, C.Term.Var{i}, afs, {==}, {==})))
          (f => (%Equal.sym(C.Cir.Out, C.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)), C.Cir.Out.halt{2, ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp)},
              ev.var.E(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp, i, nd, tb, hv)) :
              D.Post(False{}, _, s => D.Rnd(ds, ks, img, t, w, s), s => st2 => D.HR(ds, t, s, st2));
              hr),
           (0n, (%Equal.sym(C.Cir.Out, C.Cir.exec(0n, D.B.body(), D.S(foc, 0, sp, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)), C.Cir.Out.halt{2, ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp)},
              ev.var.E(0n, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp, i, nd, tb, hv)) : D.Ends(_);
              Unit{})))

# mode 0, Ref k: the call of k on no arguments (M.call, with M.walk and M.copy): a step to the copy of its leaf; or, when its case tree takes an argument, mode 1, an admin move; halt 2 when no walk exists
def mv.ev.ref(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +k: List<&2, U32>,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, C.Term.Ref{k}, fs, ps), +hv: {D.Fl(m, foc, 256) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 0, Ann x y: x, a step
def mv.ev.ann(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +x: C.Term, +y: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, C.Term.Ann{x, y}, fs, ps), +hv: {D.Fl(m, foc, 256) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 0, Let q v b with q live: v in the frame Let q □ b; an admin move
def mv.ev.let(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: C.Quan, +v: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, C.Term.Let{q, v, b}, fs, ps), +hv: {D.Fl(m, foc, 256) == False{} : Bool}, +hq: {C.Quan.live(q) == True{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 0, Let q v b with q dead: b with v put in (M.copy), a step
def mv.ev.unlet(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: C.Quan, +v: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, C.Term.Let{q, v, b}, fs, ps), +hv: {D.Fl(m, foc, 256) == False{} : Bool}, +hq: {C.Quan.live(q) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 0, App q g x: g in the frame App q □ x; an admin move
def mv.ev.app(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: C.Quan, +g: C.Term, +x: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, C.Term.App{q, g, x}, fs, ps), +hv: {D.Fl(m, foc, 256) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 0, Tup q a b with q live, not flagged VALUE: a in the frame Tup q □ b; an admin move
def mv.ev.tup(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: C.Quan, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, C.Term.Tup{q, a, b}, fs, ps), +hv: {D.Fl(m, foc, 256) == False{} : Bool}, +hq: {C.Quan.live(q) == True{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 0, Tup q a b with q dead, not flagged VALUE: b in the frame Tup q a □; an admin move
def mv.ev.tup0(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: C.Quan, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, C.Term.Tup{q, a, b}, fs, ps), +hv: {D.Fl(m, foc, 256) == False{} : Bool}, +hq: {C.Quan.live(q) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 0, Rwt e p b: e in the frame Rwt □ p b; an admin move
def mv.ev.rwt(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +e: C.Term, +p: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, C.Term.Rwt{e, p, b}, fs, ps), +hv: {D.Fl(m, foc, 256) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 0, Min a b: a in the frame Min □ b; an admin move
def mv.ev.min(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, C.Term.Min{a, b}, fs, ps), +hv: {D.Fl(m, foc, 256) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, no frame: M.out halts with 0 and the bytes of the value (Program.unbytes), or with 2 when it is no list of bytes
def mv.out(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Nil{}, ps)) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match rest:
    case D.R60{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62, +r63}:
      match iv:
        case Tuple{+et, Tuple{_, Tuple{+evv, Tuple{_, Tuple{_, Tuple{+isf, Tuple{+frs, Tuple{_, Tuple{+io, Tuple{_, _}}}}}}}}}}:
          +k = img.ks(ds, ks, img, m, im, fi, nx, io)
          %Equal.sym(U32, sp, 0, frs) : MV(ds, ks, img, D.S(foc, 1, _, pend, D.R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp), t, w)
          out.mv(ds, ks, img, foc, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp, t, w, focus, et, evv, isf,
            D.Ex.fst(List<&2, List<&2, U32>>, ks2 => {ks == C.Img.known(ks2) : List<&2, List<&2, U32>>}, k),
            D.Ex.snd(List<&2, List<&2, U32>>, ks2 => {ks == C.Img.known(ks2) : List<&2, List<&2, U32>>}, k))

# mode 1, App q □ a (app_arg, app_val) with q live and a not known: a to evaluate, in the frame App q v □; an admin move
def mv.ret.swap(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: C.Term, +kind: D.FK, +q: C.Quan, +k: Bool, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{kind, q, k, a, b}, fs}, ps), +hk: {FK.isapp(kind) == True{} : Bool}, +hs: {Bool.and(C.Quan.live(q), Bool.not(k)) == True{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, App q v □ a (app_arg, app_val), when q is dead or a known: the redex of a λ (Eval.redex): its body with the argument put in (M.data, M.copy), a step; halt 2 when the λ does not bind it
def mv.ret.app.lam(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +r: C.Quan, +h: C.Term, +kind: D.FK, +q: C.Quan, +k: Bool, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, C.Term.Lam{r, h}, Con{D.AF{kind, q, k, a, b}, fs}, ps), +hk: {FK.isapp(kind) == True{} : Bool}, +hs: {Bool.and(C.Quan.live(q), Bool.not(k)) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, App q g □ (app_fun), with the value v: the redex of a λ (Eval.redex): its body with the argument put in (M.data, M.copy), a step; halt 2 when the λ does not bind it
def mv.ret.fun.lam(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +r: C.Quan, +h: C.Term, +focus: C.Term, +q: C.Quan, +k: Bool, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.fun{}, q, k, C.Term.Lam{r, h}, b}, fs}, ps)) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, App q v □ a (app_arg, app_val), when q is dead or a known: the redex of a λ-match of pairs: its case on the pair's fields, a step; halt 2 when the argument is no live pair
def mv.ret.app.prj(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +h: C.Term, +kind: D.FK, +q: C.Quan, +k: Bool, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, C.Term.Prj{h}, Con{D.AF{kind, q, k, a, b}, fs}, ps), +hk: {FK.isapp(kind) == True{} : Bool}, +hs: {Bool.and(C.Quan.live(q), Bool.not(k)) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, App q g □ (app_fun), with the value v: the redex of a λ-match of pairs: its case on the pair's fields, a step; halt 2 when the argument is no live pair
def mv.ret.fun.prj(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +h: C.Term, +focus: C.Term, +q: C.Quan, +k: Bool, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.fun{}, q, k, C.Term.Prj{h}, b}, fs}, ps)) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, App q v □ a (app_arg, app_val), when q is dead or a known: the redex of a λ-match of labels: the case of the label, a step; halt 2 when the argument is no live label
def mv.ret.app.mat(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +j: List<&2, U32>, +h: C.Term, +n: C.Term, +kind: D.FK, +q: C.Quan, +k: Bool, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, C.Term.Mat{j, h, n}, Con{D.AF{kind, q, k, a, b}, fs}, ps), +hk: {FK.isapp(kind) == True{} : Bool}, +hs: {Bool.and(C.Quan.live(q), Bool.not(k)) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, App q g □ (app_fun), with the value v: the redex of a λ-match of labels: the case of the label, a step; halt 2 when the argument is no live label
def mv.ret.fun.mat(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +j: List<&2, U32>, +h: C.Term, +n: C.Term, +focus: C.Term, +q: C.Quan, +k: Bool, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.fun{}, q, k, C.Term.Mat{j, h, n}, b}, fs}, ps)) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, App q v □ a (app_arg, app_val), when q is dead or a known: the redex of any other value: a call (M.call, with M.walk and M.copy) of the def at the head of its spine: a step to the copy of its leaf, or a value that waits for more arguments (an admin move); halt 2 when no walk exists
def mv.ret.app.call(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: C.Term, +kind: D.FK, +q: C.Quan, +k: Bool, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{kind, q, k, a, b}, fs}, ps), +hk: {FK.isapp(kind) == True{} : Bool}, +hs: {Bool.and(C.Quan.live(q), Bool.not(k)) == False{} : Bool}, +hn: {A.node(focus) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, App q g □ (app_fun), with the value v: the redex of any other value: a call (M.call, with M.walk and M.copy) of the def at the head of its spine: a step to the copy of its leaf, or a value that waits for more arguments (an admin move); halt 2 when no walk exists
def mv.ret.fun.call(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +g: C.Term, +focus: C.Term, +q: C.Quan, +k: Bool, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.fun{}, q, k, g, b}, fs}, ps), +hn: {A.node(g) == False{} : Bool}) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, Let q □ a, with the value v: a with v put in (M.data, M.copy), a step; halt 2 when q is 2 and v is no Data
def mv.ret.let(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: C.Term, +q: C.Quan, +k: Bool, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.let{}, q, k, a, b}, fs}, ps)) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, Tup q □ a, with the value v: a to evaluate, in the frame Tup q v □; an admin move
def mv.ret.tupb(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: C.Term, +q: C.Quan, +k: Bool, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.tupb{}, q, k, a, b}, fs}, ps)) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, Tup q a □, with the value v: the value Tup q a v; an admin move
def mv.ret.tupa(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: C.Term, +q: C.Quan, +k: Bool, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.tupa{}, q, k, a, b}, fs}, ps)) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, Rwt □ a b, with the value v: b when v is Rfl, a step; else halt 2
def mv.ret.rwt(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: C.Term, +q: C.Quan, +k: Bool, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.rwt{}, q, k, a, b}, fs}, ps)) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, Min □ a, with the value v: a to evaluate, in the frame Min v □; an admin move
def mv.ret.minb(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: C.Term, +q: C.Quan, +k: Bool, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.minb{}, q, k, a, b}, fs}, ps)) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, Min a □, with the value v: the meet of a and v, a step, when both are labels of quantities; else halt 2
def mv.ret.mina(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: C.Term, +q: C.Quan, +k: Bool, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.mina{}, q, k, a, b}, fs}, ps)) ->
  MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# The choice of the move
# ----------------------

# mode 0: by the flag VALUE of the focus' cell, then by its term
def round.ev(b: Bool, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: C.Term, eb: {D.Fl(m, foc, 256) == b : Bool},
  iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, focus, fs, ps)) -> MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match b:
    case True{}:
      mv.ev.val(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, iv, eb)
    case False{}:
      match focus:
        case C.Term.Var{+i}:
          mv.ev.var(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, i, iv, eb)
        case C.Term.Ref{+k}:
          mv.ev.ref(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, k, iv, eb)
        case C.Term.Ann{+x, +y}:
          mv.ev.ann(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, x, y, iv, eb)
        case C.Term.Let{+q, +v, +b2}:
          match q:
            case C.Quan.Q0{}:
              mv.ev.unlet(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Quan.Q0{}, v, b2, iv, eb, {==})
            case C.Quan.Q1{}:
              mv.ev.let(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Quan.Q1{}, v, b2, iv, eb, {==})
            case C.Quan.Q2{}:
              mv.ev.let(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Quan.Q2{}, v, b2, iv, eb, {==})
        case C.Term.Typ{+x}:
          mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Typ{x}, iv, {==})
        case C.Term.Min{+a, +b2}:
          mv.ev.min(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, a, b2, iv, eb)
        case C.Term.All{+q, +a, +b2}:
          mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.All{q, a, b2}, iv, {==})
        case C.Term.Lam{+q, +b2}:
          mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Lam{q, b2}, iv, {==})
        case C.Term.App{+q, +g, +x}:
          mv.ev.app(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, g, x, iv, eb)
        case C.Term.Sig{+q, +a, +b2}:
          mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Sig{q, a, b2}, iv, {==})
        case C.Term.Tup{+q, +a, +b2}:
          match q:
            case C.Quan.Q0{}:
              mv.ev.tup0(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Quan.Q0{}, a, b2, iv, eb, {==})
            case C.Quan.Q1{}:
              mv.ev.tup(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Quan.Q1{}, a, b2, iv, eb, {==})
            case C.Quan.Q2{}:
              mv.ev.tup(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Quan.Q2{}, a, b2, iv, eb, {==})
        case C.Term.Prj{+h}:
          mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Prj{h}, iv, {==})
        case C.Term.Enu{+e}:
          mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Enu{e}, iv, {==})
        case C.Term.Lab{+k}:
          mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Lab{k}, iv, {==})
        case C.Term.Mat{+k, +h, +n}:
          mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Mat{k, h, n}, iv, {==})
        case C.Term.Efq{}:
          mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Efq{}, iv, {==})
        case C.Term.Eql{+a, +b2, +y}:
          mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Eql{a, b2, y}, iv, {==})
        case C.Term.Rfl{}:
          mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Rfl{}, iv, {==})
        case C.Term.Rwt{+e, +p2, +b2}:
          mv.ev.rwt(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, e, p2, b2, iv, eb)

# mode 1, App q □ a: swap when q is live and a is not known; else the redex, by
# the value's term
def round.app(b: Bool, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: C.Term, +kind: D.FK, +q: C.Quan, +k: Bool, +a: C.Term, +bb: C.Term,
  eb: {Bool.and(C.Quan.live(q), Bool.not(k)) == b : Bool}, hk: {FK.isapp(kind) == True{} : Bool},
  iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{kind, q, k, a, bb}, fs}, ps)) -> MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match b:
    case True{}:
      mv.ret.swap(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, kind, q, k, a, bb, iv, hk, eb)
    case False{}:
      match focus:
        case C.Term.Var{+i}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Var{i}, kind, q, k, a, bb, iv, hk, eb, {==})
        case C.Term.Ref{+kk}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Ref{kk}, kind, q, k, a, bb, iv, hk, eb, {==})
        case C.Term.Ann{+x, +y}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Ann{x, y}, kind, q, k, a, bb, iv, hk, eb, {==})
        case C.Term.Let{+qq, +v, +b2}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Let{qq, v, b2}, kind, q, k, a, bb, iv, hk, eb, {==})
        case C.Term.Typ{+x}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Typ{x}, kind, q, k, a, bb, iv, hk, eb, {==})
        case C.Term.Min{+aa, +b2}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Min{aa, b2}, kind, q, k, a, bb, iv, hk, eb, {==})
        case C.Term.All{+qq, +aa, +b2}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.All{qq, aa, b2}, kind, q, k, a, bb, iv, hk, eb, {==})
        case C.Term.Lam{+r, +b2}:
          mv.ret.app.lam(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, r, b2, kind, q, k, a, bb, iv, hk, eb)
        case C.Term.App{+qq, +g, +x}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.App{qq, g, x}, kind, q, k, a, bb, iv, hk, eb, {==})
        case C.Term.Sig{+qq, +aa, +b2}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Sig{qq, aa, b2}, kind, q, k, a, bb, iv, hk, eb, {==})
        case C.Term.Tup{+qq, +aa, +b2}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Tup{qq, aa, b2}, kind, q, k, a, bb, iv, hk, eb, {==})
        case C.Term.Prj{+h}:
          mv.ret.app.prj(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, h, kind, q, k, a, bb, iv, hk, eb)
        case C.Term.Enu{+e}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Enu{e}, kind, q, k, a, bb, iv, hk, eb, {==})
        case C.Term.Lab{+kk}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Lab{kk}, kind, q, k, a, bb, iv, hk, eb, {==})
        case C.Term.Mat{+kk, +h, +n}:
          mv.ret.app.mat(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, kk, h, n, kind, q, k, a, bb, iv, hk, eb)
        case C.Term.Efq{}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Efq{}, kind, q, k, a, bb, iv, hk, eb, {==})
        case C.Term.Eql{+aa, +b2, +y}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Eql{aa, b2, y}, kind, q, k, a, bb, iv, hk, eb, {==})
        case C.Term.Rfl{}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Rfl{}, kind, q, k, a, bb, iv, hk, eb, {==})
        case C.Term.Rwt{+e, +p2, +b2}:
          mv.ret.app.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Rwt{e, p2, b2}, kind, q, k, a, bb, iv, hk, eb, {==})

# mode 1, App q g □: the redex, by the function's term
def round.fun(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: C.Term, +q: C.Quan, +k: Bool, +g: C.Term, +bb: C.Term,
  iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{D.AF{D.FK.fun{}, q, k, g, bb}, fs}, ps)) -> MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match g:
    case C.Term.Var{+i}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Var{i}, focus, q, k, bb, iv, {==})
    case C.Term.Ref{+kk}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Ref{kk}, focus, q, k, bb, iv, {==})
    case C.Term.Ann{+x, +y}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Ann{x, y}, focus, q, k, bb, iv, {==})
    case C.Term.Let{+r, +v, +b2}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Let{r, v, b2}, focus, q, k, bb, iv, {==})
    case C.Term.Typ{+x}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Typ{x}, focus, q, k, bb, iv, {==})
    case C.Term.Min{+a, +b2}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Min{a, b2}, focus, q, k, bb, iv, {==})
    case C.Term.All{+r, +a, +b2}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.All{r, a, b2}, focus, q, k, bb, iv, {==})
    case C.Term.Lam{+r, +b2}:
      mv.ret.fun.lam(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, r, b2, focus, q, k, bb, iv)
    case C.Term.App{+r, +g, +x}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.App{r, g, x}, focus, q, k, bb, iv, {==})
    case C.Term.Sig{+r, +a, +b2}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Sig{r, a, b2}, focus, q, k, bb, iv, {==})
    case C.Term.Tup{+r, +a, +b2}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Tup{r, a, b2}, focus, q, k, bb, iv, {==})
    case C.Term.Prj{+h}:
      mv.ret.fun.prj(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, h, focus, q, k, bb, iv)
    case C.Term.Enu{+e}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Enu{e}, focus, q, k, bb, iv, {==})
    case C.Term.Lab{+kk}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Lab{kk}, focus, q, k, bb, iv, {==})
    case C.Term.Mat{+kk, +h, +n}:
      mv.ret.fun.mat(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, kk, h, n, focus, q, k, bb, iv)
    case C.Term.Efq{}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Efq{}, focus, q, k, bb, iv, {==})
    case C.Term.Eql{+a, +b2, +y}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Eql{a, b2, y}, focus, q, k, bb, iv, {==})
    case C.Term.Rfl{}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Rfl{}, focus, q, k, bb, iv, {==})
    case C.Term.Rwt{+e, +p2, +b2}:
      mv.ret.fun.call(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, C.Term.Rwt{e, p2, b2}, focus, q, k, bb, iv, {==})

# the move of a state that Inv finds: by the mode, then by the focus or the
# top frame
def round.go(+ret: Bool, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: C.Term,
  iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, ret, focus, fs, ps)) -> MV(ds, ks, img, D.S(foc, Bool.to_u32(ret), sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match ret:
    case False{}:
      round.ev(D.Fl(m, foc, 256), ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, {==}, iv)
    case True{}:
      match fs:
        case Nil{}:
          mv.out(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, iv)
        case Con{D.AF{+kind, +q, +k, +a, +bb}, +fs2}:
          match kind:
            case D.FK.arg{}:
              round.app(Bool.and(C.Quan.live(q), Bool.not(k)), ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, D.FK.arg{}, q, k, a, bb, {==}, {==}, iv)
            case D.FK.val{}:
              round.app(Bool.and(C.Quan.live(q), Bool.not(k)), ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, D.FK.val{}, q, k, a, bb, {==}, {==}, iv)
            case D.FK.fun{}:
              round.fun(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)
            case D.FK.let{}:
              mv.ret.let(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)
            case D.FK.tupb{}:
              mv.ret.tupb(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)
            case D.FK.tupa{}:
              mv.ret.tupa(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)
            case D.FK.rwt{}:
              mv.ret.rwt(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)
            case D.FK.minb{}:
              mv.ret.minb(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)
            case D.FK.mina{}:
              mv.ret.mina(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)

# the registers, the output and its length that Inv finds
def inv.regs(-ds: List<&2, C.Def>, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, -regs: List<&2, U32>, -m: C.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -out: List<&2, U32>, -outn: U32, -t: C.Term, -w: Nat, -ret: Bool, -focus: C.Term, -fs: List<&2, D.AF>, -foc: U32, -sp: U32, -pend: U32, -ps: List<&2, U32>, -rest: D.R60, iw: D.InvOf(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest)) ->
  {regs == D.RG(foc, Bool.to_u32(ret), sp, pend, D.R60.list(rest)) : List<&2, U32>}:
  match iw:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}:
      e

def inv.out(-ds: List<&2, C.Def>, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, -regs: List<&2, U32>, -m: C.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -out: List<&2, U32>, -outn: U32, -t: C.Term, -w: Nat, -ret: Bool, -focus: C.Term, -fs: List<&2, D.AF>, -foc: U32, -sp: U32, -pend: U32, -ps: List<&2, U32>, -rest: D.R60, iw: D.InvOf(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest)) -> {out == Nil{} : List<&2, U32>}:
  match iw:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}:
      e

def inv.outn(-ds: List<&2, C.Def>, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, -regs: List<&2, U32>, -m: C.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -out: List<&2, U32>, -outn: U32, -t: C.Term, -w: Nat, -ret: Bool, -focus: C.Term, -fs: List<&2, D.AF>, -foc: U32, -sp: U32, -pend: U32, -ps: List<&2, U32>, -rest: D.R60, iw: D.InvOf(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest)) -> {outn == 0 : U32}:
  match iw:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, e}}}}}}}}}}:
      e

# Inv's facts, in the state that it finds
def iv.of(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +out: List<&2, U32>, +outn: U32, +t: C.Term, +w: Nat, +ret: Bool, +focus: C.Term, +fs: List<&2, D.AF>, +foc: U32, +sp: U32, +pend: U32, +ps: List<&2, U32>, +rest: D.R60,
  er: {regs == D.RG(foc, Bool.to_u32(ret), sp, pend, D.R60.list(rest)) : List<&2, U32>}, eo: {out == Nil{} : List<&2, U32>},
  en: {outn == 0 : U32}, iw: D.InvOf(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest)) ->
  IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, ret, focus, fs, ps):
  %er : D.InvOf(ds, ks, img, _, m, nx, fi, im, Nil{}, 0, t, w, ret, focus, fs, foc, sp, pend, ps, rest)
  %eo : D.InvOf(ds, ks, img, regs, m, nx, fi, im, _, 0, t, w, ret, focus, fs, foc, sp, pend, ps, rest)
  %en : D.InvOf(ds, ks, img, regs, m, nx, fi, im, out, _, t, w, ret, focus, fs, foc, sp, pend, ps, rest)
  iw

def round.iw(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +out: List<&2, U32>, +outn: U32, +t: C.Term, +w: Nat, +ret: Bool, +focus: C.Term, +fs: List<&2, D.AF>, +foc: U32, +sp: U32, +pend: U32, +ps: List<&2, U32>, +rest: D.R60, +pg: U32, +lim: U32, +inp: List<&2, U32>, +iw: D.InvOf(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest)) ->
  MV(ds, ks, img, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}, t, w):
  +er = inv.regs(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest, iw)
  +eo = inv.out(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest, iw)
  +en = inv.outn(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest, iw)
  %Equal.sym(List<&2, U32>, regs, D.RG(foc, Bool.to_u32(ret), sp, pend, D.R60.list(rest)), er) :
    MV(ds, ks, img, C.Cir.State{_, m, nx, fi, im, pg, lim, inp, out, outn}, t, w)
  %Equal.sym(List<&2, U32>, out, Nil{}, eo) :
    MV(ds, ks, img, C.Cir.State{D.RG(foc, Bool.to_u32(ret), sp, pend, D.R60.list(rest)), m, nx, fi, im, pg, lim, inp, _, outn}, t, w)
  %Equal.sym(U32, outn, 0, en) :
    MV(ds, ks, img, C.Cir.State{D.RG(foc, Bool.to_u32(ret), sp, pend, D.R60.list(rest)), m, nx, fi, im, pg, lim, inp, Nil{}, _}, t, w)
  round.go(ret, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus,
    iv.of(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest, er, eo, en, iw))

def round.wit(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +out: List<&2, U32>, +outn: U32,
  +t: C.Term, +w: Nat, inv: D.Inv(ds, ks, img, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}, t, w)) ->
  MV(ds, ks, img, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}, t, w):
  (x, iw) = inv
  match x:
    case D.Wit{+ret, +focus, +fs, +foc, +sp, +pend, +ps, +rest}:
      round.iw(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest, pg, lim, inp, iw)

# the move of a state of the invariant
def round.mv(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, st: C.Cir.State, +t: C.Term,
  +w: Nat, inv: D.Inv(ds, ks, img, st, t, w)) -> MV(ds, ks, img, st, t, w):
  match st:
    case C.Cir.State{+regs, +m, +nx, +fi, +im, +pg, +lim, +inp, +out, +outn}:
      round.wit(ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, out, outn, t, w, inv)

# a round of the main loop, for any fuel: an admin move, a step, a halt that
# says what Eval gives, or out of memory
def round.post(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +st: C.Cir.State, +t: C.Term, +w: Nat, inv: D.Inv(ds, ks, img, st, t, w)) ->
  D.Post(False{}, C.Cir.exec(f, D.B.body(), st), s => D.Rnd(ds, ks, img, t, w, s), s => st2 => D.HR(ds, t, s, st2)):
  mv.post(f, ds, ks, img, st, t, w, round.mv(ds, ks, img, st, t, w, inv))

# a round of the main loop ends, with some fuel
def round.done(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +st: C.Cir.State,
  +t: C.Term, +w: Nat, inv: D.Inv(ds, ks, img, st, t, w)) -> D.Ex(Nat, f => D.Ends(C.Cir.exec(f, D.B.body(), st))):
  mv.done(ds, ks, img, st, t, w, round.mv(ds, ks, img, st, t, w, inv))

# The loop gives what Eval gives
# ------------------------------

# a weaker halt
def post.wk(dn: Bool, o: C.Cir.Out, -Q: C.Cir.State -> Type, -H1: U32 -> C.Cir.State -> Type,
  -H2: U32 -> C.Cir.State -> Type, h: D.Post(dn, o, Q, H1), hh: @s: U32 -> @st: C.Cir.State -> H1(s, st) -> H2(s, st)) ->
  D.Post(dn, o, Q, H2):
  match o:
    case C.Cir.Out.next{st}:
      h
    case C.Cir.Out.halt{s, st}:
      hh(s, st, h)
    case C.Cir.Out.out_of_memory{}:
      Unit{}
    case C.Cir.Out.trap{}:
      h
    case C.Cir.Out.not_done{}:
      h

# no result after a term with no step
def none.after(+j: Nat, +ds: List<&2, C.Def>, +t: C.Term, es: {C.Eval.step(ds, t) == None{} : Maybe<C.Term>}) ->
  {C.Program.result(ds, C.Eval.steps(1n+j, ds, t)) == None{} : Maybe<&2, List<&2, U32>>}:
  %Equal.sym(Maybe<C.Term>, C.Eval.step(ds, t), None{}, es) : {C.Program.result(ds, C.Eval.run(j, ds, _)) == None{} : Maybe<&2, List<&2, U32>>}
  %Equal.sym(Maybe<C.Term>, C.Eval.run(j, ds, None{}), None{}, D.run.none(j, ds)) : {C.Program.result(ds, _) == None{} : Maybe<&2, List<&2, U32>>}
  {==}

# no result ever, from a term with no step and no result
def he.none(k: Nat, +ds: List<&2, C.Def>, +t: C.Term, +es: {C.Eval.step(ds, t) == None{} : Maybe<C.Term>},
  er: {C.Program.result(ds, Some{t}) == None{} : Maybe<&2, List<&2, U32>>}) ->
  {C.Program.result(ds, C.Eval.steps(k, ds, t)) == None{} : Maybe<&2, List<&2, U32>>}:
  match k:
    case 0n:
      er
    case 1n+(+j):
      none.after(j, ds, t, es)

# a round's halt says what the loop's says
def he.of(+ds: List<&2, C.Def>, +t: C.Term, -s: U32, -st: C.Cir.State, h: D.HR(ds, t, s, st)) -> D.HE(ds, t, s, st):
  match h:
    case Inl{x}:
      (e0, r) = x
      (es, er) = r
      Inl{(e0, (0n, er))}
    case Inr{x}:
      (e2, r) = x
      (es, er) = r
      Inr{(e2, k => he.none(k, ds, t, es, er))}

# the result after a step, from the result of its term
def step.res(+j: Nat, +ds: List<&2, C.Def>, +t: C.Term, -u: C.Term, -x: Maybe<&2, List<&2, U32>>,
  es: {C.Eval.step(ds, t) == Some{u} : Maybe<C.Term>},
  e: {C.Program.result(ds, C.Eval.steps(j, ds, u)) == x : Maybe<&2, List<&2, U32>>}) ->
  {C.Program.result(ds, C.Eval.steps(1n+j, ds, t)) == x : Maybe<&2, List<&2, U32>>}:
  %Equal.sym(Maybe<C.Term>, C.Eval.step(ds, t), Some{u}, es) : {C.Program.result(ds, C.Eval.run(j, ds, _)) == x : Maybe<&2, List<&2, U32>>}
  e

# the result of a term from that of its step
def res.step(+j: Nat, +ds: List<&2, C.Def>, +t: C.Term, -u: C.Term, -x: Maybe<&2, List<&2, U32>>,
  es: {C.Eval.step(ds, t) == Some{u} : Maybe<C.Term>},
  e: {C.Program.result(ds, C.Eval.steps(1n+j, ds, t)) == x : Maybe<&2, List<&2, U32>>}) ->
  {C.Program.result(ds, C.Eval.steps(j, ds, u)) == x : Maybe<&2, List<&2, U32>>}:
  %es : {C.Program.result(ds, C.Eval.run(j, ds, _)) == x : Maybe<&2, List<&2, U32>>}
  e

def he.all(k: Nat, +ds: List<&2, C.Def>, +t: C.Term, +u: C.Term, +es: {C.Eval.step(ds, t) == Some{u} : Maybe<C.Term>},
  g: @k: Nat -> {C.Program.result(ds, C.Eval.steps(k, ds, u)) == None{} : Maybe<&2, List<&2, U32>>}) ->
  {C.Program.result(ds, C.Eval.steps(k, ds, t)) == None{} : Maybe<&2, List<&2, U32>>}:
  match k:
    case 0n:
      D.res.nv(ds, t, vals.of(C.Eval.vals(ds, t, False{}), ds, t, u, {==}, es))
    case 1n+(+j):
      step.res(j, ds, t, u, None{}, es, g(j))

# a halt of the loop after a step says what Eval gives before the step
def he.step(+ds: List<&2, C.Def>, +t: C.Term, +u: C.Term, +es: {C.Eval.step(ds, t) == Some{u} : Maybe<C.Term>},
  -s: U32, -st: C.Cir.State, h: D.HE(ds, u, s, st)) -> D.HE(ds, t, s, st):
  match h:
    case Inl{x}:
      (e0, r) = x
      (+k, ek) = r
      Inl{(e0, (1n+k, step.res(k, ds, t, u, Some{List.reverse(&2, U32, D.St.out(st))}, es, ek)))}
    case Inr{x}:
      (e2, g) = x
      Inr{(e2, k => he.all(k, ds, t, u, es, g))}

# after a round that goes on: the loop from the next state, by ia after an
# admin move and by ist after a step
def loop.next(+p: Nat, +ds: List<&2, C.Def>, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, +u: C.Cir.State,
  +t: C.Term, -w: Nat, r: D.Rnd(ds, ks, img, t, w, u),
  ia: @w2: Nat -> D.Inv(ds, ks, img, u, t, w2) ->
    D.Post(False{}, C.Cir.exec(p, D.B.loop(), u), s => Empty, s => st2 => D.HE(ds, t, s, st2)),
  ist: @v: C.Term -> @w2: Nat -> D.Inv(ds, ks, img, u, v, w2) ->
    D.Post(False{}, C.Cir.exec(p, D.B.loop(), u), s => Empty, s => st2 => D.HE(ds, v, s, st2))) ->
  D.Post(False{}, C.Cir.exec(p, D.B.loop(), u), s => Empty, s => st2 => D.HE(ds, t, s, st2)):
  match r:
    case Inl{a}:
      (w2, r2) = a
      (inv2, lt) = r2
      ia(w2, inv2)
    case Inr{b}:
      (+v, r2) = b
      (+es, r3) = r2
      (w2, inv2) = r3
      post.wk(False{}, C.Cir.exec(p, D.B.loop(), u), s => Empty, s => st2 => D.HE(ds, v, s, st2), s => st2 => D.HE(ds, t, s, st2),
        ist(v, w2, inv2), s => st2 => h => he.step(ds, t, v, es, s, st2, h))

# the main loop, from a state of the invariant of the term t, halts only as
# HE says, with any fuel: by induction on the fuel
def loop.post(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +st: C.Cir.State,
  +t: C.Term, +w: Nat, inv: D.Inv(ds, ks, img, st, t, w)) ->
  D.Post(False{}, C.Cir.exec(f, D.B.loop(), st), s => Empty, s => st2 => D.HE(ds, t, s, st2)):
  match f:
    case 0n:
      Unit{}
    case 1n+p:
      D.post.then(False{}, C.Cir.exec(p, D.B.body(), st), u => C.Cir.exec(p, D.B.loop(), u), s => D.Rnd(ds, ks, img, t, w, s),
        s => Empty, s => st2 => D.HR(ds, t, s, st2), s => st2 => D.HE(ds, t, s, st2),
        round.post(p, ds, ks, img, st, t, w, inv),
        s => st2 => h => he.of(ds, t, s, st2, h),
        +u => r => loop.next(p, ds, ks, img, u, t, w, r, w2 => i2 => loop.post(p, ds, ks, img, u, t, w2, i2),
          v => w2 => i2 => loop.post(p, ds, ks, img, u, v, w2, i2)))

# The loop reaches what Eval reaches
# ----------------------------------

def good.ends(-o: List<&2, U32>, r: C.Cir.Out, g: D.Good(o, r)) -> D.Ends(r):
  match r:
    case C.Cir.Out.next{_}:
      Unit{}
    case C.Cir.Out.halt{_, _}:
      Unit{}
    case C.Cir.Out.out_of_memory{}:
      Unit{}
    case C.Cir.Out.trap{}:
      Unit{}
    case C.Cir.Out.not_done{}:
      g

def good.then(-o: List<&2, U32>, r: C.Cir.Out, -k: C.Cir.State -> C.Cir.Out, g: D.Good(o, r)) ->
  D.Good(o, C.Cir.exec.then(r, k)):
  match r:
    case C.Cir.Out.next{st}:
      Empty.absurd(D.Good(o, k(st)), g)
    case C.Cir.Out.halt{s, st}:
      g
    case C.Cir.Out.out_of_memory{}:
      Unit{}
    case C.Cir.Out.trap{}:
      g
    case C.Cir.Out.not_done{}:
      g

def ends.eq(-a: C.Cir.Out, -b: C.Cir.Out, e: {a == b : C.Cir.Out}, d: D.Ends(b)) -> D.Ends(a):
  %Equal.sym(C.Cir.Out, a, b, e) : D.Ends(_)
  d

# a round that halts or runs out of memory with the fuel f0 ends the loop the
# same with 1 + f0
def out.fin(-o: List<&2, U32>, +f0: Nat, -st: C.Cir.State, r: C.Cir.Out, er: {C.Cir.exec(f0, D.B.body(), st) == r : C.Cir.Out},
  g: D.Good(o, r)) -> D.Good(o, C.Cir.exec(1n+f0, D.B.loop(), st)):
  %Equal.sym(C.Cir.Out, C.Cir.exec(f0, D.B.body(), st), r, er) : D.Good(o, C.Cir.exec.then(_, u => C.Cir.exec(f0, D.B.loop(), u)))
  good.then(o, r, u => C.Cir.exec(f0, D.B.loop(), u), g)

# a round that goes on with the fuel f0, then the loop with n1, are the loop
# with 1 + f0 + n1
def next.fin(+o: List<&2, U32>, +f0: Nat, +n1: Nat, +st: C.Cir.State, +u: C.Cir.State,
  +er: {C.Cir.exec(f0, D.B.body(), st) == C.Cir.Out.next{u} : C.Cir.Out},
  +g1: D.Good(o, C.Cir.exec(n1, D.B.loop(), u))) -> D.Good(o, C.Cir.exec(1n+Nat.add(f0, n1), D.B.loop(), st)):
  +n = Nat.add(f0, n1)
  +d0 = ends.eq(C.Cir.exec(f0, D.B.body(), st), C.Cir.Out.next{u}, er, Unit{})
  +e1 = Equal.trans(C.Cir.Out, C.Cir.Out.next{u}, C.Cir.exec(f0, D.B.body(), st), C.Cir.exec(n, D.B.body(), st),
    Equal.sym(C.Cir.Out, C.Cir.exec(f0, D.B.body(), st), C.Cir.Out.next{u}, er),
    D.mono(f0, n, D.B.body(), st, N.le_add_r(f0, n1), d0))
  +e2 = D.mono(n1, n, D.B.loop(), u, N.le_add_l(f0, n1), good.ends(o, C.Cir.exec(n1, D.B.loop(), u), g1))
  %e1 : D.Good(o, C.Cir.exec.then(_, v => C.Cir.exec(n, D.B.loop(), v)))
  %e2 : D.Good(o, _)
  g1

# a round that halts, from a term from which Eval reaches the bytes o: the
# loop gives them
def loop.halt(k: Nat, +ds: List<&2, C.Def>, +t: C.Term, -s: U32, +st2: C.Cir.State, +o: List<&2, U32>,
  e: {C.Program.result(ds, C.Eval.steps(k, ds, t)) == Some{o} : Maybe<&2, List<&2, U32>>},
  h: D.HR(ds, t, s, st2)) -> D.Good(o, C.Cir.Out.halt{s, st2}):
  match k:
    case 0n:
      match h:
        case Inl{x}:
          (e0, r) = x
          (es, er) = r
          (e0, D.mb.inj(List.reverse(&2, U32, D.St.out(st2)), o,
            Equal.trans(Maybe<&2, List<&2, U32>>, Some{List.reverse(&2, U32, D.St.out(st2))}, C.Program.result(ds, Some{t}), Some{o},
              Equal.sym(Maybe<&2, List<&2, U32>>, C.Program.result(ds, Some{t}), Some{List.reverse(&2, U32, D.St.out(st2))}, er), e)))
        case Inr{x}:
          (e2, r) = x
          (es, er) = r
          Empty.absurd(D.Good(o, C.Cir.Out.halt{s, st2}), D.mb.ne(o,
            Equal.trans(Maybe<&2, List<&2, U32>>, None{}, C.Program.result(ds, Some{t}), Some{o},
              Equal.sym(Maybe<&2, List<&2, U32>>, C.Program.result(ds, Some{t}), None{}, er), e)))
    case 1n+(+j):
      match h:
        case Inl{x}:
          (e0, r) = x
          (es, er) = r
          Empty.absurd(D.Good(o, C.Cir.Out.halt{s, st2}), D.mb.ne(o,
            Equal.trans(Maybe<&2, List<&2, U32>>, None{}, C.Program.result(ds, C.Eval.steps(1n+j, ds, t)), Some{o},
              Equal.sym(Maybe<&2, List<&2, U32>>, C.Program.result(ds, C.Eval.steps(1n+j, ds, t)), None{}, none.after(j, ds, t, es)), e)))
        case Inr{x}:
          (e2, r) = x
          (es, er) = r
          Empty.absurd(D.Good(o, C.Cir.Out.halt{s, st2}), D.mb.ne(o,
            Equal.trans(Maybe<&2, List<&2, U32>>, None{}, C.Program.result(ds, C.Eval.steps(1n+j, ds, t)), Some{o},
              Equal.sym(Maybe<&2, List<&2, U32>>, C.Program.result(ds, C.Eval.steps(1n+j, ds, t)), None{}, none.after(j, ds, t, es)), e)))

# a step from a term from which Eval reaches the bytes o at once: none
def loop.step0(+ds: List<&2, C.Def>, +t: C.Term, +u: C.Term, -o: List<&2, U32>,
  e: {C.Program.result(ds, Some{t}) == Some{o} : Maybe<&2, List<&2, U32>>},
  es: {C.Eval.step(ds, t) == Some{u} : Maybe<C.Term>}) -> Empty:
  D.mb.ne(o, Equal.trans(Maybe<&2, List<&2, U32>>, None{}, C.Program.result(ds, Some{t}), Some{o},
    Equal.sym(Maybe<&2, List<&2, U32>>, C.Program.result(ds, Some{t}), None{},
      D.res.nv(ds, t, vals.of(C.Eval.vals(ds, t, False{}), ds, t, u, {==}, es))), e))

# when Eval reaches the bytes o from t within k steps, the loop gives them or
# runs out of memory, with some fuel: by induction on k, and on b, above the
# measure of the admin moves; r0 is the round with the fuel f0, that ends
def loop.done(k: Nat, b: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +st: C.Cir.State, +t: C.Term, +w: Nat, +o: List<&2, U32>, +hw: N.Le(1n+w, b),
  +e: {C.Program.result(ds, C.Eval.steps(k, ds, t)) == Some{o} : Maybe<&2, List<&2, U32>>},
  +f0: Nat, r0: C.Cir.Out, +er: {C.Cir.exec(f0, D.B.body(), st) == r0 : C.Cir.Out}, d0: D.Ends(r0),
  p0: D.Post(False{}, r0, s => D.Rnd(ds, ks, img, t, w, s), s => st2 => D.HR(ds, t, s, st2))) ->
  D.Ex(Nat, n => D.Good(o, C.Cir.exec(n, D.B.loop(), st))):
  match k:
    case 0n:
      match b:
        case 0n:
          Empty.absurd(D.Ex(Nat, n => D.Good(o, C.Cir.exec(n, D.B.loop(), st))), hw)
        case 1n+(+c):
          match r0:
            case C.Cir.Out.next{+u}:
              match p0:
                case Inl{+a}:
                  +w2 = D.adm.w(ds, ks, img, u, t, w, a)
                  +inv2 = D.adm.inv(ds, ks, img, u, t, w, a)
                  +lt = D.adm.lt(ds, ks, img, u, t, w, a)
                  +rd = round.done(ds, ks, img, u, t, w2, inv2)
                  +f1 = D.Ex.fst(Nat, f => D.Ends(C.Cir.exec(f, D.B.body(), u)), rd)
                  +ld = loop.done(0n, c, ds, ks, img, u, t, w2, o, N.le_trans(1n+w2, w, c, lt, hw), e, f1,
                    C.Cir.exec(f1, D.B.body(), u), {==}, D.Ex.snd(Nat, f => D.Ends(C.Cir.exec(f, D.B.body(), u)), rd),
                    round.post(f1, ds, ks, img, u, t, w2, inv2))
                  +n1 = D.Ex.fst(Nat, n => D.Good(o, C.Cir.exec(n, D.B.loop(), u)), ld)
                  (1n+Nat.add(f0, n1), next.fin(o, f0, n1, st, u, er, D.Ex.snd(Nat, n => D.Good(o, C.Cir.exec(n, D.B.loop(), u)), ld)))
                case Inr{+x}:
                  +v = D.stp.u(ds, ks, img, u, t, x)
                  +es = D.stp.es(ds, ks, img, u, t, x)
                  +w2 = D.stp.w(ds, ks, img, u, t, x)
                  +inv2 = D.stp.inv(ds, ks, img, u, t, x)
                  Empty.absurd(D.Ex(Nat, n => D.Good(o, C.Cir.exec(n, D.B.loop(), st))), loop.step0(ds, t, v, o, e, es))
            case C.Cir.Out.halt{+s, +st2}:
              (1n+f0, out.fin(o, f0, st, C.Cir.Out.halt{s, st2}, er, loop.halt(0n, ds, t, s, st2, o, e, p0)))
            case C.Cir.Out.out_of_memory{}:
              (1n+f0, out.fin(o, f0, st, C.Cir.Out.out_of_memory{}, er, Unit{}))
            case C.Cir.Out.trap{}:
              Empty.absurd(D.Ex(Nat, n => D.Good(o, C.Cir.exec(n, D.B.loop(), st))), p0)
            case C.Cir.Out.not_done{}:
              Empty.absurd(D.Ex(Nat, n => D.Good(o, C.Cir.exec(n, D.B.loop(), st))), d0)
    case 1n+(+j):
      match b:
        case 0n:
          Empty.absurd(D.Ex(Nat, n => D.Good(o, C.Cir.exec(n, D.B.loop(), st))), hw)
        case 1n+(+c):
          match r0:
            case C.Cir.Out.next{+u}:
              match p0:
                case Inl{+a}:
                  +w2 = D.adm.w(ds, ks, img, u, t, w, a)
                  +inv2 = D.adm.inv(ds, ks, img, u, t, w, a)
                  +lt = D.adm.lt(ds, ks, img, u, t, w, a)
                  +rd = round.done(ds, ks, img, u, t, w2, inv2)
                  +f1 = D.Ex.fst(Nat, f => D.Ends(C.Cir.exec(f, D.B.body(), u)), rd)
                  +ld = loop.done(1n+j, c, ds, ks, img, u, t, w2, o, N.le_trans(1n+w2, w, c, lt, hw), e, f1,
                    C.Cir.exec(f1, D.B.body(), u), {==}, D.Ex.snd(Nat, f => D.Ends(C.Cir.exec(f, D.B.body(), u)), rd),
                    round.post(f1, ds, ks, img, u, t, w2, inv2))
                  +n1 = D.Ex.fst(Nat, n => D.Good(o, C.Cir.exec(n, D.B.loop(), u)), ld)
                  (1n+Nat.add(f0, n1), next.fin(o, f0, n1, st, u, er, D.Ex.snd(Nat, n => D.Good(o, C.Cir.exec(n, D.B.loop(), u)), ld)))
                case Inr{+x}:
                  +v = D.stp.u(ds, ks, img, u, t, x)
                  +es = D.stp.es(ds, ks, img, u, t, x)
                  +w2 = D.stp.w(ds, ks, img, u, t, x)
                  +inv2 = D.stp.inv(ds, ks, img, u, t, x)
                  +rd = round.done(ds, ks, img, u, v, w2, inv2)
                  +f1 = D.Ex.fst(Nat, f => D.Ends(C.Cir.exec(f, D.B.body(), u)), rd)
                  +ld = loop.done(j, 1n+w2, ds, ks, img, u, v, w2, o, N.le_refl(1n+w2), res.step(j, ds, t, v, Some{o}, es, e), f1,
                    C.Cir.exec(f1, D.B.body(), u), {==}, D.Ex.snd(Nat, f => D.Ends(C.Cir.exec(f, D.B.body(), u)), rd),
                    round.post(f1, ds, ks, img, u, v, w2, inv2))
                  +n1 = D.Ex.fst(Nat, n => D.Good(o, C.Cir.exec(n, D.B.loop(), u)), ld)
                  (1n+Nat.add(f0, n1), next.fin(o, f0, n1, st, u, er, D.Ex.snd(Nat, n => D.Good(o, C.Cir.exec(n, D.B.loop(), u)), ld)))
            case C.Cir.Out.halt{+s, +st2}:
              (1n+f0, out.fin(o, f0, st, C.Cir.Out.halt{s, st2}, er, loop.halt(1n+j, ds, t, s, st2, o, e, p0)))
            case C.Cir.Out.out_of_memory{}:
              (1n+f0, out.fin(o, f0, st, C.Cir.Out.out_of_memory{}, er, Unit{}))
            case C.Cir.Out.trap{}:
              Empty.absurd(D.Ex(Nat, n => D.Good(o, C.Cir.exec(n, D.B.loop(), st))), p0)
            case C.Cir.Out.not_done{}:
              Empty.absurd(D.Ex(Nat, n => D.Good(o, C.Cir.exec(n, D.B.loop(), st))), d0)

# the loop, from a state of the invariant
def loop.start(k: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +st: C.Cir.State, +t: C.Term, +w: Nat, +o: List<&2, U32>, +inv: D.Inv(ds, ks, img, st, t, w),
  +e: {C.Program.result(ds, C.Eval.steps(k, ds, t)) == Some{o} : Maybe<&2, List<&2, U32>>}) ->
  D.Ex(Nat, n => D.Good(o, C.Cir.exec(n, D.B.loop(), st))):
  +rd = round.done(ds, ks, img, st, t, w, inv)
  +f0 = D.Ex.fst(Nat, f => D.Ends(C.Cir.exec(f, D.B.body(), st)), rd)
  loop.done(k, 1n+w, ds, ks, img, st, t, w, o, N.le_refl(1n+w), e, f0, C.Cir.exec(f0, D.B.body(), st), {==},
    D.Ex.snd(Nat, f => D.Ends(C.Cir.exec(f, D.B.body(), st)), rd), round.post(f0, ds, ks, img, st, t, w, inv))

def res.alloced(r: Maybe<&2, U32>, fuel: Nat, prog: C.Cir.Stmt, +regs: Nat, +cells: List<&2, C.Cir.Cell>, +k: U32,
  +len: U32, +lim: U32, +i: List<&2, U32>, +m: U32, -P: C.Wasm.Outcome -> Type, po: P(C.Wasm.Outcome.out_of_memory{}),
  ek: {k == C.Wasm.encode.len(C.Cir.Cell, cells) : U32},
  em: {U32.is_le(C.Cir.pages(C.Cir.input.at(k)), m) == True{} : Bool},
  elim: {lim == C.Wasm.min(m, 65536) : U32},
  el: {C.Wasm.length32(i) == Some{len} : Maybe<&2, U32>},
  er: {C.Cir.alloc.pages(k, len, C.Cir.pages(C.Cir.input.at(k)), lim) == r : Maybe<&2, U32>},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> D.Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    P(C.Cir.ended(C.Cir.exec(fuel, prog, D.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  P(C.Cir.result.alloced(r, fuel, prog, regs, cells, k, U32.add(C.Cir.input.at(k), len), lim, i)):
  match r:
    case None{}:
      po
    case Some{+p}:
      g(k, len, p, lim, C.Cir.first(k, U32.add(C.Cir.input.at(k), len)), (ek, (em, (elim, (el, (er, {==}))))))

def res.sized(nl: Maybe<&2, U32>, fuel: Nat, prog: C.Cir.Stmt, +regs: Nat, +cells: List<&2, C.Cir.Cell>, +k: U32,
  +lim: U32, +i: List<&2, U32>, +m: U32, -P: C.Wasm.Outcome -> Type, po: P(C.Wasm.Outcome.out_of_memory{}),
  ek: {k == C.Wasm.encode.len(C.Cir.Cell, cells) : U32},
  em: {U32.is_le(C.Cir.pages(C.Cir.input.at(k)), m) == True{} : Bool},
  elim: {lim == C.Wasm.min(m, 65536) : U32},
  el: {C.Wasm.length32(i) == nl : Maybe<&2, U32>},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> D.Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    P(C.Cir.ended(C.Cir.exec(fuel, prog, D.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  P(C.Cir.result.sized(nl, fuel, prog, regs, cells, k, C.Cir.pages(C.Cir.input.at(k)), lim, i)):
  match nl:
    case None{}:
      po
    case Some{+len}:
      res.alloced(C.Cir.alloc.pages(k, len, C.Cir.pages(C.Cir.input.at(k)), lim), fuel, prog, regs, cells, k, len, lim, i, m,
        P, po, ek, em, elim, el, {==}, g)

def res.memory(ok: Bool, fuel: Nat, prog: C.Cir.Stmt, +regs: Nat, +cells: List<&2, C.Cir.Cell>, +k: U32,
  +lim: U32, +i: List<&2, U32>, +m: U32, -P: C.Wasm.Outcome -> Type, po: P(C.Wasm.Outcome.out_of_memory{}),
  ek: {k == C.Wasm.encode.len(C.Cir.Cell, cells) : U32},
  em: {U32.is_le(C.Cir.pages(C.Cir.input.at(k)), m) == ok : Bool},
  elim: {lim == C.Wasm.min(m, 65536) : U32},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> D.Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    P(C.Cir.ended(C.Cir.exec(fuel, prog, D.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  P(C.Cir.result.memory(ok, fuel, prog, regs, cells, k, C.Cir.pages(C.Cir.input.at(k)), lim, i)):
  match ok:
    case False{}:
      po
    case True{}:
      res.sized(C.Wasm.length32(i), fuel, prog, regs, cells, k, lim, i, m, P, po, ek, em, elim, {==}, g)

# what holds of every run from the start, and of out of memory, holds of
# Cir.result
def res.on(fuel: Nat, prog: C.Cir.Stmt, +regs: Nat, +cells: List<&2, C.Cir.Cell>, +i: List<&2, U32>, +m: U32,
  -P: C.Wasm.Outcome -> Type, po: P(C.Wasm.Outcome.out_of_memory{}),
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> D.Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    P(C.Cir.ended(C.Cir.exec(fuel, prog, D.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  P(C.Cir.result(fuel, prog, regs, cells, i, m)):
  res.memory(U32.is_le(C.Cir.pages(C.Cir.input.at(C.Wasm.encode.len(C.Cir.Cell, cells))), m), fuel, prog, regs, cells,
    C.Wasm.encode.len(C.Cir.Cell, cells), C.Wasm.min(m, 65536), i, m, P, po, {==}, {==}, {==}, g)

def rex.alloced(r: Maybe<&2, U32>, prog: C.Cir.Stmt, +regs: Nat, +cells: List<&2, C.Cir.Cell>, +k: U32,
  +len: U32, +lim: U32, +i: List<&2, U32>, +m: U32, -P: C.Wasm.Outcome -> Type, po: P(C.Wasm.Outcome.out_of_memory{}),
  ek: {k == C.Wasm.encode.len(C.Cir.Cell, cells) : U32},
  em: {U32.is_le(C.Cir.pages(C.Cir.input.at(k)), m) == True{} : Bool},
  elim: {lim == C.Wasm.min(m, 65536) : U32},
  el: {C.Wasm.length32(i) == Some{len} : Maybe<&2, U32>},
  er: {C.Cir.alloc.pages(k, len, C.Cir.pages(C.Cir.input.at(k)), lim) == r : Maybe<&2, U32>},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> D.Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    &n: Nat -> P(C.Cir.ended(C.Cir.exec(n, prog, D.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  &n: Nat -> P(C.Cir.result.alloced(r, n, prog, regs, cells, k, U32.add(C.Cir.input.at(k), len), lim, i)):
  match r:
    case None{}:
      (0n, po)
    case Some{+p}:
      g(k, len, p, lim, C.Cir.first(k, U32.add(C.Cir.input.at(k), len)), (ek, (em, (elim, (el, (er, {==}))))))

def rex.sized(nl: Maybe<&2, U32>, prog: C.Cir.Stmt, +regs: Nat, +cells: List<&2, C.Cir.Cell>, +k: U32,
  +lim: U32, +i: List<&2, U32>, +m: U32, -P: C.Wasm.Outcome -> Type, po: P(C.Wasm.Outcome.out_of_memory{}),
  ek: {k == C.Wasm.encode.len(C.Cir.Cell, cells) : U32},
  em: {U32.is_le(C.Cir.pages(C.Cir.input.at(k)), m) == True{} : Bool},
  elim: {lim == C.Wasm.min(m, 65536) : U32},
  el: {C.Wasm.length32(i) == nl : Maybe<&2, U32>},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> D.Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    &n: Nat -> P(C.Cir.ended(C.Cir.exec(n, prog, D.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  &n: Nat -> P(C.Cir.result.sized(nl, n, prog, regs, cells, k, C.Cir.pages(C.Cir.input.at(k)), lim, i)):
  match nl:
    case None{}:
      (0n, po)
    case Some{+len}:
      rex.alloced(C.Cir.alloc.pages(k, len, C.Cir.pages(C.Cir.input.at(k)), lim), prog, regs, cells, k, len, lim, i, m,
        P, po, ek, em, elim, el, {==}, g)

def rex.memory(ok: Bool, prog: C.Cir.Stmt, +regs: Nat, +cells: List<&2, C.Cir.Cell>, +k: U32,
  +lim: U32, +i: List<&2, U32>, +m: U32, -P: C.Wasm.Outcome -> Type, po: P(C.Wasm.Outcome.out_of_memory{}),
  ek: {k == C.Wasm.encode.len(C.Cir.Cell, cells) : U32},
  em: {U32.is_le(C.Cir.pages(C.Cir.input.at(k)), m) == ok : Bool},
  elim: {lim == C.Wasm.min(m, 65536) : U32},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> D.Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    &n: Nat -> P(C.Cir.ended(C.Cir.exec(n, prog, D.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  &n: Nat -> P(C.Cir.result.memory(ok, n, prog, regs, cells, k, C.Cir.pages(C.Cir.input.at(k)), lim, i)):
  match ok:
    case False{}:
      (0n, po)
    case True{}:
      rex.sized(C.Wasm.length32(i), prog, regs, cells, k, lim, i, m, P, po, ek, em, elim, {==}, g)

# a fuel for each run from the start gives one for Cir.result, which runs out
# of memory or runs from the same start with any fuel
def res.ex(prog: C.Cir.Stmt, +regs: Nat, +cells: List<&2, C.Cir.Cell>, +i: List<&2, U32>, +m: U32,
  -P: C.Wasm.Outcome -> Type, po: P(C.Wasm.Outcome.out_of_memory{}),
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> D.Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    &n: Nat -> P(C.Cir.ended(C.Cir.exec(n, prog, D.St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  &n: Nat -> P(C.Cir.result(n, prog, regs, cells, i, m)):
  rex.memory(U32.is_le(C.Cir.pages(C.Cir.input.at(C.Wasm.encode.len(C.Cir.Cell, cells))), m), prog, regs, cells,
    C.Wasm.encode.len(C.Cir.Cell, cells), C.Wasm.min(m, 65536), i, m, P, po, {==}, {==}, {==}, g)

# The machine gives what Eval gives
# ---------------------------------

def run.loop(+n: Nat, +ds: List<&2, C.Def>, +i: List<&2, U32>, +st2: C.Cir.State,
  q: D.Ex(Nat, w => D.Inv(ds, T.tm.names(ds), T.tm.img(ds), st2, C.Program.start(i), w))) ->
  D.Post(False{}, C.Cir.exec(n, C.Cir.Stmt.seq{D.B.loop(), C.Cir.Stmt.nop{}}, st2), st => Unit,
    s2 => st3 => D.HE(ds, C.Program.start(i), s2, st3)):
  (w, inv) = q
  D.post.seq(n, False{}, D.B.loop(), C.Cir.Stmt.nop{}, st2, s => Empty, s => Unit, s2 => st3 => D.HE(ds, C.Program.start(i), s2, st3),
    s2 => st3 => D.HE(ds, C.Program.start(i), s2, st3),
    loop.post(n, ds, T.tm.names(ds), T.tm.img(ds), st2, C.Program.start(i), w, inv),
    s2 => st3 => h => h, st3 => h => Empty.absurd(D.Post(False{}, C.Cir.exec(n, C.Cir.Stmt.nop{}, st3), s => Unit,
      s2 => st4 => D.HE(ds, C.Program.start(i), s2, st4)), h))

def run.rest(+n: Nat, +ds: List<&2, C.Def>, +i: List<&2, U32>, +st1: C.Cir.State, q1: D.InvIn(ds, i, st1)) ->
  D.Post(False{}, C.Cir.exec(n, D.B.rest(), st1), st => Unit, s2 => st2 => D.HE(ds, C.Program.start(i), s2, st2)):
  (len, ex) = q1
  D.post.seq(n, False{}, C.M.set(C.R.mode(), C.M.c(0)), C.Cir.Stmt.seq{D.B.loop(), C.Cir.Stmt.nop{}}, st1,
    st2 => D.Ex(Nat, w => D.Inv(ds, T.tm.names(ds), T.tm.img(ds), st2, C.Program.start(i), w)), st => Unit,
    s2 => st2 => Empty, s2 => st2 => D.HE(ds, C.Program.start(i), s2, st2),
    (%Equal.sym(C.Cir.Out, C.Cir.exec(n, C.M.set(C.R.mode(), C.M.c(0)), st1), C.Cir.Out.next{D.Mode0(st1)}, D.setmode(n, st1, len)) :
      D.Post(False{}, _, st2 => D.Ex(Nat, w => D.Inv(ds, T.tm.names(ds), T.tm.img(ds), st2, C.Program.start(i), w)), s2 => st2 => Empty);
     ex),
    s2 => st2 => h => Empty.absurd(D.HE(ds, C.Program.start(i), s2, st2), h),
    st2 => q2 => run.loop(n, ds, i, st2, q2))

# a run of Mach.code from the start halts only as HE says, from Program.start
def run.post(+n: Nat, +p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +k: U32, +len: U32,
  +pg: U32, +lim: U32, +first: U32,
  rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  small: {C.Img.small(p, 0) == True{} : Bool},
  s: D.Start(C.Img.cells(ds), i, m, k, len, pg, lim, first)) ->
  D.Post(False{}, C.Cir.exec(n, C.Mach.code(), D.St0(C.Mach.regs(), C.Img.cells(ds), first, k, pg, lim, i)), st => Unit,
    s2 => st2 => D.HE(ds, C.Program.start(i), s2, st2)):
  D.post.seq(n, False{}, C.M.input(), D.B.rest(), D.St0(C.Mach.regs(), C.Img.cells(ds), first, k, pg, lim, i),
    st => D.InvIn(ds, i, st), st => Unit, s2 => st2 => Empty, s2 => st2 => D.HE(ds, C.Program.start(i), s2, st2),
    input.post(n, p, ds, i, m, k, len, pg, lim, first, rd, small, s),
    s2 => st2 => h => Empty.absurd(D.HE(ds, C.Program.start(i), s2, st2), h),
    st1 => q1 => run.rest(n, ds, i, st1, q1))

# the outcomes that are no trap
def oc.nt(x: C.Wasm.Outcome) -> Type:
  match x:
    case C.Wasm.Outcome.result{_}:
      Unit
    case C.Wasm.Outcome.out_of_memory{}:
      Unit
    case C.Wasm.Outcome.no_result{}:
      Unit
    case C.Wasm.Outcome.unsupported{}:
      Unit
    case C.Wasm.Outcome.trap{}:
      Empty
    case C.Wasm.Outcome.not_done{}:
      Unit

# the outcomes that are no result
def oc.nr(x: C.Wasm.Outcome) -> Type:
  match x:
    case C.Wasm.Outcome.result{_}:
      Empty
    case C.Wasm.Outcome.out_of_memory{}:
      Unit
    case C.Wasm.Outcome.no_result{}:
      Unit
    case C.Wasm.Outcome.unsupported{}:
      Unit
    case C.Wasm.Outcome.trap{}:
      Unit
    case C.Wasm.Outcome.not_done{}:
      Unit

def oc.get(x: C.Wasm.Outcome, d: List<&2, U32>) -> List<&2, U32>:
  match x:
    case C.Wasm.Outcome.result{y}:
      y
    case _:
      d

# result is one to one
def oc.inj(+a: List<&2, U32>, -b: List<&2, U32>, e: {C.Wasm.Outcome.result{a} == C.Wasm.Outcome.result{b} : C.Wasm.Outcome}) ->
  {a == b : List<&2, U32>}:
  Equal.cong(C.Wasm.Outcome, List<&2, U32>, x => oc.get(x, a), C.Wasm.Outcome.result{a}, C.Wasm.Outcome.result{b}, e)

# a run that halts with 0 gives its output's bytes
def ended0(-s: U32, +out: List<&2, U32>, e0: {s == 0 : U32}) ->
  {C.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), out) == C.Wasm.Outcome.result{List.reverse(&2, U32, out)} : C.Wasm.Outcome}:
  %Equal.sym(U32, s, 0, e0) : {C.Cir.ended.halt(U32.is_eq(_, 0), U32.is_eq(_, 1), U32.is_eq(_, 2), out) == C.Wasm.Outcome.result{List.reverse(&2, U32, out)} : C.Wasm.Outcome}
  {==}

# a run that halts with 2 gives no result
def ended2(-s: U32, +out: List<&2, U32>, e2: {s == 2 : U32}) ->
  {C.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), out) == C.Wasm.Outcome.no_result{} : C.Wasm.Outcome}:
  %Equal.sym(U32, s, 2, e2) : {C.Cir.ended.halt(U32.is_eq(_, 0), U32.is_eq(_, 1), U32.is_eq(_, 2), out) == C.Wasm.Outcome.no_result{} : C.Wasm.Outcome}
  {==}

# a run that halts only as HE says never traps
def safe.end(o: C.Cir.Out, -ds: List<&2, C.Def>, -t: C.Term,
  h: D.Post(False{}, o, st => Unit, s => st2 => D.HE(ds, t, s, st2))) ->
  {C.Cir.ended(o) != C.Wasm.Outcome.trap{} : C.Wasm.Outcome}:
  match o:
    case C.Cir.Out.next{st}:
      e => (%e : oc.nt(_); Unit{})
    case C.Cir.Out.halt{s, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, +out, outn}}:
      match h:
        case Inl{x}:
          (e0, r) = x
          %Equal.sym(C.Wasm.Outcome, C.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), out),
            C.Wasm.Outcome.result{List.reverse(&2, U32, out)}, ended0(s, out, e0)) : {_ != C.Wasm.Outcome.trap{} : C.Wasm.Outcome}
          e => (%e : oc.nt(_); Unit{})
        case Inr{x}:
          (e2, r) = x
          %Equal.sym(C.Wasm.Outcome, C.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), out),
            C.Wasm.Outcome.no_result{}, ended2(s, out, e2)) : {_ != C.Wasm.Outcome.trap{} : C.Wasm.Outcome}
          e => (%e : oc.nt(_); Unit{})
    case C.Cir.Out.out_of_memory{}:
      e => (%e : oc.nt(_); Unit{})
    case C.Cir.Out.trap{}:
      Empty.absurd({C.Wasm.Outcome.trap{} != C.Wasm.Outcome.trap{} : C.Wasm.Outcome}, h)
    case C.Cir.Out.not_done{}:
      e => (%e : oc.nt(_); Unit{})

# a result of a run that halts only as HE says is one that Eval reaches
def sound.end(o: C.Cir.Out, +ds: List<&2, C.Def>, +t: C.Term, +x: List<&2, U32>,
  h: D.Post(False{}, o, st => Unit, s => st2 => D.HE(ds, t, s, st2)),
  e: {C.Cir.ended(o) == C.Wasm.Outcome.result{x} : C.Wasm.Outcome}) ->
  &k: Nat -> {C.Program.result(ds, C.Eval.steps(k, ds, t)) == Some{x} : Maybe<&2, List<&2, U32>>}:
  match o:
    case C.Cir.Out.next{st}:
      Empty.absurd(&k: Nat -> {C.Program.result(ds, C.Eval.steps(k, ds, t)) == Some{x} : Maybe<&2, List<&2, U32>>},
        (%e : oc.nr(_); Unit{}))
    case C.Cir.Out.halt{s, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, +out, outn}}:
      match h:
        case Inl{y}:
          (e0, r) = y
          (+k, ek) = r
          +rx = oc.inj(List.reverse(&2, U32, out), x,
            Equal.trans(C.Wasm.Outcome, C.Wasm.Outcome.result{List.reverse(&2, U32, out)},
              C.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), out), C.Wasm.Outcome.result{x},
              Equal.sym(C.Wasm.Outcome, C.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), out),
                C.Wasm.Outcome.result{List.reverse(&2, U32, out)}, ended0(s, out, e0)), e))
          (k, (%rx :
            {C.Program.result(ds, C.Eval.steps(k, ds, t)) == Some{_} : Maybe<&2, List<&2, U32>>}; ek))
        case Inr{y}:
          (e2, g) = y
          Empty.absurd(&k: Nat -> {C.Program.result(ds, C.Eval.steps(k, ds, t)) == Some{x} : Maybe<&2, List<&2, U32>>},
            (%Equal.trans(C.Wasm.Outcome, C.Wasm.Outcome.no_result{},
              C.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), out), C.Wasm.Outcome.result{x},
              Equal.sym(C.Wasm.Outcome, C.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), out),
                C.Wasm.Outcome.no_result{}, ended2(s, out, e2)), e) : oc.nr(_); Unit{}))
    case C.Cir.Out.out_of_memory{}:
      Empty.absurd(&k: Nat -> {C.Program.result(ds, C.Eval.steps(k, ds, t)) == Some{x} : Maybe<&2, List<&2, U32>>},
        (%e : oc.nr(_); Unit{}))
    case C.Cir.Out.trap{}:
      Empty.absurd(&k: Nat -> {C.Program.result(ds, C.Eval.steps(k, ds, t)) == Some{x} : Maybe<&2, List<&2, U32>>}, h)
    case C.Cir.Out.not_done{}:
      Empty.absurd(&k: Nat -> {C.Program.result(ds, C.Eval.steps(k, ds, t)) == Some{x} : Maybe<&2, List<&2, U32>>},
        (%e : oc.nr(_); Unit{}))

# a run that gives the bytes o, or runs out of memory, ends so
def good.end(+o: List<&2, U32>, r: C.Cir.Out, g: D.Good(o, r)) ->
  Or({C.Cir.ended(r) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome}, {C.Cir.ended(r) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}):
  match r:
    case C.Cir.Out.next{st}:
      Empty.absurd(Or({C.Wasm.Outcome.no_result{} == C.Wasm.Outcome.result{o} : C.Wasm.Outcome},
        {C.Wasm.Outcome.no_result{} == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}), g)
    case C.Cir.Out.halt{s, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, +out, outn}}:
      (e0, eo) = g
      Inl{Equal.trans(C.Wasm.Outcome, C.Cir.ended.halt(U32.is_eq(s, 0), U32.is_eq(s, 1), U32.is_eq(s, 2), out),
        C.Wasm.Outcome.result{List.reverse(&2, U32, out)}, C.Wasm.Outcome.result{o}, ended0(s, out, e0),
        Equal.cong(List<&2, U32>, C.Wasm.Outcome, y => C.Wasm.Outcome.result{y}, List.reverse(&2, U32, out), o, eo))}
    case C.Cir.Out.out_of_memory{}:
      Inr{{==}}
    case C.Cir.Out.trap{}:
      Empty.absurd(Or({C.Wasm.Outcome.trap{} == C.Wasm.Outcome.result{o} : C.Wasm.Outcome},
        {C.Wasm.Outcome.trap{} == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}), g)
    case C.Cir.Out.not_done{}:
      Empty.absurd(Or({C.Wasm.Outcome.not_done{} == C.Wasm.Outcome.result{o} : C.Wasm.Outcome},
        {C.Wasm.Outcome.not_done{} == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}), g)

# M.input with the fuel f1, then the loop with n2, are Mach.code with
# 1 + f1 + n2
def run.fin(+o: List<&2, U32>, +f1: Nat, +n2: Nat, +st0: C.Cir.State, +st1: C.Cir.State,
  +er1: {C.Cir.exec(f1, C.M.input(), st0) == C.Cir.Out.next{st1} : C.Cir.Out},
  +len: {List.length(&2, U32, D.St.regs(st1)) == 64n : Nat},
  +g2: D.Good(o, C.Cir.exec(n2, D.B.loop(), D.Mode0(st1)))) -> D.Good(o, C.Cir.exec(1n+Nat.add(f1, n2), C.Mach.code(), st0)):
  +n = {1n+Nat.add(f1, n2) : Nat}
  +d1 = ends.eq(C.Cir.exec(f1, C.M.input(), st0), C.Cir.Out.next{st1}, er1, Unit{})
  +e1 = Equal.trans(C.Cir.Out, C.Cir.Out.next{st1}, C.Cir.exec(f1, C.M.input(), st0), C.Cir.exec(n, C.M.input(), st0),
    Equal.sym(C.Cir.Out, C.Cir.exec(f1, C.M.input(), st0), C.Cir.Out.next{st1}, er1),
    D.mono(f1, n, C.M.input(), st0, N.le_succ(f1, Nat.add(f1, n2), N.le_add_r(f1, n2)), d1))
  +e2 = Equal.sym(C.Cir.Out, C.Cir.exec(n, C.M.set(C.R.mode(), C.M.c(0)), st1), C.Cir.Out.next{D.Mode0(st1)}, D.setmode(n, st1, len))
  +e3 = D.mono(n2, n, D.B.loop(), D.Mode0(st1), N.le_succ(n2, Nat.add(f1, n2), N.le_add_l(f1, n2)),
    good.ends(o, C.Cir.exec(n2, D.B.loop(), D.Mode0(st1)), g2))
  %e1 : D.Good(o, C.Cir.exec.then(_, s1 => C.Cir.exec(n, D.B.rest(), s1)))
  %e2 : D.Good(o, C.Cir.exec.then(_, s2 => C.Cir.exec(n, C.Cir.Stmt.seq{D.B.loop(), C.Cir.Stmt.nop{}}, s2)))
  %e3 : D.Good(o, C.Cir.exec.then(_, s3 => C.Cir.exec(n, C.Cir.Stmt.nop{}, s3)))
  good.then(o, C.Cir.exec(n2, D.B.loop(), D.Mode0(st1)), s3 => C.Cir.exec(n, C.Cir.Stmt.nop{}, s3), g2)

# M.input that runs out of memory with the fuel f1 ends Mach.code so with 1 + f1
def oom.fin(-o: List<&2, U32>, +f1: Nat, +st0: C.Cir.State,
  er1: {C.Cir.exec(f1, C.M.input(), st0) == C.Cir.Out.out_of_memory{} : C.Cir.Out}) ->
  D.Good(o, C.Cir.exec(1n+f1, C.Mach.code(), st0)):
  +n = {1n+f1 : Nat}
  +er = er1
  +e1 = Equal.trans(C.Cir.Out, C.Cir.Out.out_of_memory{}, C.Cir.exec(f1, C.M.input(), st0), C.Cir.exec(n, C.M.input(), st0),
    Equal.sym(C.Cir.Out, C.Cir.exec(f1, C.M.input(), st0), C.Cir.Out.out_of_memory{}, er),
    D.mono(f1, n, C.M.input(), st0, N.le_succ(f1, f1, N.le_refl(f1)), ends.eq(C.Cir.exec(f1, C.M.input(), st0), C.Cir.Out.out_of_memory{}, er, Unit{})))
  %e1 : D.Good(o, C.Cir.exec.then(_, s1 => C.Cir.exec(n, D.B.rest(), s1)))
  Unit{}

def run.next(k: Nat, +ds: List<&2, C.Def>, +i: List<&2, U32>, +o: List<&2, U32>, +f1: Nat, +st0: C.Cir.State,
  +st1: C.Cir.State, +er1: {C.Cir.exec(f1, C.M.input(), st0) == C.Cir.Out.next{st1} : C.Cir.Out},
  +len: {List.length(&2, U32, D.St.regs(st1)) == 64n : Nat}, +w: Nat,
  +inv: D.Inv(ds, T.tm.names(ds), T.tm.img(ds), D.Mode0(st1), C.Program.start(i), w),
  +e: {C.Program.result(ds, C.Eval.steps(k, ds, C.Program.start(i))) == Some{o} : Maybe<&2, List<&2, U32>>}) ->
  D.Ex(Nat, n => D.Good(o, C.Cir.exec(n, C.Mach.code(), st0))):
  +ls = loop.start(k, ds, T.tm.names(ds), T.tm.img(ds), D.Mode0(st1), C.Program.start(i), w, o, inv, e)
  +n2 = D.Ex.fst(Nat, n => D.Good(o, C.Cir.exec(n, D.B.loop(), D.Mode0(st1))), ls)
  (1n+Nat.add(f1, n2), run.fin(o, f1, n2, st0, st1, er1, len, D.Ex.snd(Nat, n => D.Good(o, C.Cir.exec(n, D.B.loop(), D.Mode0(st1))), ls)))

def run.done.r(k: Nat, +ds: List<&2, C.Def>, +i: List<&2, U32>, +o: List<&2, U32>, +f1: Nat, +st0: C.Cir.State,
  r1: C.Cir.Out, +er1: {C.Cir.exec(f1, C.M.input(), st0) == r1 : C.Cir.Out}, d1: D.Ends(r1),
  p1: D.Post(False{}, r1, st => D.InvIn(ds, i, st), s2 => st2 => Empty),
  +e: {C.Program.result(ds, C.Eval.steps(k, ds, C.Program.start(i))) == Some{o} : Maybe<&2, List<&2, U32>>}) ->
  D.Ex(Nat, n => D.Good(o, C.Cir.exec(n, C.Mach.code(), st0))):
  match r1:
    case C.Cir.Out.next{+st1}:
      (len, q) = p1
      (w, inv) = q
      run.next(k, ds, i, o, f1, st0, st1, er1, len, w, inv, e)
    case C.Cir.Out.halt{s, st}:
      Empty.absurd(D.Ex(Nat, n => D.Good(o, C.Cir.exec(n, C.Mach.code(), st0))), p1)
    case C.Cir.Out.out_of_memory{}:
      (1n+f1, oom.fin(o, f1, st0, er1))
    case C.Cir.Out.trap{}:
      Empty.absurd(D.Ex(Nat, n => D.Good(o, C.Cir.exec(n, C.Mach.code(), st0))), p1)
    case C.Cir.Out.not_done{}:
      Empty.absurd(D.Ex(Nat, n => D.Good(o, C.Cir.exec(n, C.Mach.code(), st0))), d1)

# when Eval reaches the bytes o from Program.start(i), a run of Mach.code from
# the start gives them, or runs out of memory, with some fuel
def run.done(k: Nat, +p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +o: List<&2, U32>, +kk: U32,
  +len: U32, +pg: U32, +lim: U32, +first: U32,
  +rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  +small: {C.Img.small(p, 0) == True{} : Bool},
  +s: D.Start(C.Img.cells(ds), i, m, kk, len, pg, lim, first),
  +e: {C.Program.result(ds, C.Eval.steps(k, ds, C.Program.start(i))) == Some{o} : Maybe<&2, List<&2, U32>>}) ->
  D.Ex(Nat, n => D.Good(o, C.Cir.exec(n, C.Mach.code(), D.St0(C.Mach.regs(), C.Img.cells(ds), first, kk, pg, lim, i)))):
  +st0 = D.St0(C.Mach.regs(), C.Img.cells(ds), first, kk, pg, lim, i)
  +id = input.done(p, ds, i, m, kk, len, pg, lim, first, rd, small, s)
  +f1 = D.Ex.fst(Nat, f => D.Ends(C.Cir.exec(f, C.M.input(), st0)), id)
  run.done.r(k, ds, i, o, f1, st0, C.Cir.exec(f1, C.M.input(), st0), {==}, D.Ex.snd(Nat, f => D.Ends(C.Cir.exec(f, C.M.input(), st0)), id),
    input.post(f1, p, ds, i, m, kk, len, pg, lim, first, rd, small, s), e)

def comp.of(k: Nat, +p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +o: List<&2, U32>, +kk: U32,
  +len: U32, +pg: U32, +lim: U32, +first: U32,
  +rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  +small: {C.Img.small(p, 0) == True{} : Bool},
  +s: D.Start(C.Img.cells(ds), i, m, kk, len, pg, lim, first),
  +e: {C.Program.result(ds, C.Eval.steps(k, ds, C.Program.start(i))) == Some{o} : Maybe<&2, List<&2, U32>>}) ->
  &n: Nat -> Or({C.Cir.ended(C.Cir.exec(n, C.Mach.code(), D.St0(C.Mach.regs(), C.Img.cells(ds), first, kk, pg, lim, i))) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome},
    {C.Cir.ended(C.Cir.exec(n, C.Mach.code(), D.St0(C.Mach.regs(), C.Img.cells(ds), first, kk, pg, lim, i))) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}):
  +st0 = D.St0(C.Mach.regs(), C.Img.cells(ds), first, kk, pg, lim, i)
  +rn = run.done(k, p, ds, i, m, o, kk, len, pg, lim, first, rd, small, s, e)
  +n = D.Ex.fst(Nat, n => D.Good(o, C.Cir.exec(n, C.Mach.code(), st0)), rn)
  (n, good.end(o, C.Cir.exec(n, C.Mach.code(), st0), D.Ex.snd(Nat, n => D.Good(o, C.Cir.exec(n, C.Mach.code(), st0)), rn)))

# Layer B
# -------
#
# The lemmas of proof.bend, with exactly their types.

# B: the machine never makes an access that its module could not make the
# same way
def mach.safe.proof(
  +p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +n: Nat,
  rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  small: {C.Img.small(p, 0) == True{} : Bool}
) -> {C.Cir.result(n, C.Mach.code(), C.Mach.regs(), C.Img.cells(ds), i, m) != C.Wasm.Outcome.trap{} : C.Wasm.Outcome}:
  res.on(n, C.Mach.code(), C.Mach.regs(), C.Img.cells(ds), i, m, x => {x != C.Wasm.Outcome.trap{} : C.Wasm.Outcome},
    e => (%e : oc.nt(_); Unit{}),
    +kk => +len => +pg => +lim => +first => s =>
      safe.end(C.Cir.exec(n, C.Mach.code(), D.St0(C.Mach.regs(), C.Img.cells(ds), first, kk, pg, lim, i)), ds, C.Program.start(i),
        run.post(n, p, ds, i, m, kk, len, pg, lim, first, rd, small, s)))

# B: a result of the machine is the list of bytes of a value that Eval reaches
def mach.sound.proof(
  +p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +n: Nat, +o: List<&2, U32>,
  rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  small: {C.Img.small(p, 0) == True{} : Bool},
  e: {C.Cir.result(n, C.Mach.code(), C.Mach.regs(), C.Img.cells(ds), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome}
) -> &k:Nat -> {C.Program.result(ds, C.Eval.steps(k, ds, C.Program.start(i))) == Some{o} : Maybe<&2, List<&2, U32>>}:
  res.on(n, C.Mach.code(), C.Mach.regs(), C.Img.cells(ds), i, m,
    x => {x == C.Wasm.Outcome.result{o} : C.Wasm.Outcome} ->
      &k:Nat -> {C.Program.result(ds, C.Eval.steps(k, ds, C.Program.start(i))) == Some{o} : Maybe<&2, List<&2, U32>>},
    e2 => Empty.absurd(&k:Nat -> {C.Program.result(ds, C.Eval.steps(k, ds, C.Program.start(i))) == Some{o} : Maybe<&2, List<&2, U32>>},
      (%e2 : oc.nr(_); Unit{})),
    +kk => +len => +pg => +lim => +first => s => e2 =>
      sound.end(C.Cir.exec(n, C.Mach.code(), D.St0(C.Mach.regs(), C.Img.cells(ds), first, kk, pg, lim, i)), ds, C.Program.start(i), o,
        run.post(n, p, ds, i, m, kk, len, pg, lim, first, rd, small, s), e2), e)

# B: when Eval reaches a list of bytes, the machine gives it, or runs out of
# memory
def mach.complete.proof(
  +p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +k: Nat, +o: List<&2, U32>,
  rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  small: {C.Img.small(p, 0) == True{} : Bool},
  e: {C.Program.result(ds, C.Eval.steps(k, ds, C.Program.start(i))) == Some{o} : Maybe<&2, List<&2, U32>>}
) -> &n:Nat -> Or({C.Cir.result(n, C.Mach.code(), C.Mach.regs(), C.Img.cells(ds), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome},
  {C.Cir.result(n, C.Mach.code(), C.Mach.regs(), C.Img.cells(ds), i, m) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}):
  res.ex(C.Mach.code(), C.Mach.regs(), C.Img.cells(ds), i, m,
    x => Or({x == C.Wasm.Outcome.result{o} : C.Wasm.Outcome}, {x == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}),
    Inr{{==}},
    +kk => +len => +pg => +lim => +first => s => comp.of(k, p, ds, i, m, o, kk, len, pg, lim, first, rd, small, s, e))

# Open: a round keeps the machine's cells within the peak of its term
def round.peak(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +st: C.Cir.State, +t: C.Term, +w: Nat, inv: D.Inv(ds, ks, img, st, t, w)) ->
  D.Post(False{}, C.Cir.exec(f, D.B.body(), st), s => N.Le(D.Mem.cells(s), Nat.max(D.Mem.cells(st), D.Peak(t))), s => st2 => Unit):
  ?TODO

# Open: a round whose memory has room for the peak of its term, and for the
# output, does not run out of memory
def round.room(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +st: C.Cir.State, +t: C.Term, +w: Nat, inv: D.Inv(ds, ks, img, st, t, w),
  room: N.Le(Nat.add(Nat.mul(20n, Nat.add(U32.to_nat(D.St.first(st)), Nat.max(D.Mem.cells(st), D.Peak(t)))), C.Term.size(t)),
    U32.to_nat(U32.shln(C.Wasm.min(D.St.lim(st), 65536), 16n)))) ->
  D.NoOom(C.Cir.exec(f, D.B.body(), st)):
  ?TODO

# B: with the memory of INVARIANTS #4, the machine gives the list of bytes
# (open: from round.peak and round.room as above)
def mach.memory.proof(
  +p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +k: Nat, +o: List<&2, U32>,
  rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  small: {C.Img.small(p, 0) == True{} : Bool},
  e: {C.Program.result(ds, C.Eval.steps(k, ds, C.Program.start(i))) == Some{o} : Maybe<&2, List<&2, U32>>},
  big: {Nat.is_le(C.Program.need(p, i, k), C.Program.memory(m)) == True{} : Bool}
) -> &n:Nat -> {C.Cir.result(n, C.Mach.code(), C.Mach.regs(), C.Img.cells(ds), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome}:
  ?TODO
