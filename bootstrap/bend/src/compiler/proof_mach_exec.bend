# compiler: layer B, the run of the machine's statements
# ======================================================
#
# Equations of Cir.exec for the parts of the machine's code that the moves of
# proof_mach.bend run (open: a body ?TODO is to prove). Each holds for any
# fuel: a while is not run on these paths. A state is X.st of its registers
# (a list of 64, read by List.get) and its cells, with no output; X.set sets
# a register, X.store a field of a cell. This file imports only Base and
# impl.bend; proof_mach.bend imports it.

import Base
import ./impl.bend as C

# Kit
# ---

def X.st(regs: List<&2, U32>, m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, inp: List<&2, U32>) ->
  C.Cir.State:
  C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}

def X.set(regs: List<&2, U32>, +r: Nat, +v: U32) -> List<&2, U32>:
  List.set(&2, U32, regs, r, v)

# the cells with field k of the cell i set to v
def X.put(+m: C.Cir.Cells, +k: Nat, +i: U32, +v: U32) -> C.Cir.Cells:
  C.Cir.Cells.set(m, i, C.Cir.Cell.set(k, C.Cir.Cells.get(m, i), v))

def X.store(st: C.Cir.State, +k: Nat, +i: U32, +v: U32) -> C.Cir.State:
  match st:
    case C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}:
      C.Cir.State{regs, X.put(m, k, i, v), nx, fi, im, pg, lim, inp, out, outn}

def X.cells(st: C.Cir.State) -> C.Cir.Cells:
  match st:
    case C.Cir.State{_, m, _, _, _, _, _, _, _, _}:
      m

def X.setst(st: C.Cir.State, +r: Nat, +v: U32) -> C.Cir.State:
  match st:
    case C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}:
      C.Cir.State{List.set(&2, U32, regs, r, v), m, nx, fi, im, pg, lim, inp, out, outn}

def X.regs(st: C.Cir.State) -> List<&2, U32>:
  match st:
    case C.Cir.State{regs, _, _, _, _, _, _, _, _, _}:
      regs

# the body of the main loop
def X.body() -> C.Cir.Stmt:
  C.M.if(C.M.eq(C.M.g(C.R.mode()), C.M.c(0)), C.M.ev(), C.M.ret())

# the parts of a statement of impl.bend, to name them without copying them
def sel.t(x: C.Cir.Stmt) -> C.Cir.Stmt:
  match x:
    case C.Cir.Stmt.if{_, t, _}:
      t
    case _:
      C.Cir.Stmt.nop{}

def sel.e(x: C.Cir.Stmt) -> C.Cir.Stmt:
  match x:
    case C.Cir.Stmt.if{_, _, e}:
      e
    case _:
      C.Cir.Stmt.nop{}

def sel.a(x: C.Cir.Stmt) -> C.Cir.Stmt:
  match x:
    case C.Cir.Stmt.seq{a, _}:
      a
    case _:
      C.Cir.Stmt.nop{}

def sel.b(x: C.Cir.Stmt) -> C.Cir.Stmt:
  match x:
    case C.Cir.Stmt.seq{_, b}:
      b
    case _:
      C.Cir.Stmt.nop{}

# M.ret's tests of the frame's tag, past the i first: the test of app_arg or
# app_val (0), app_fun (1), let_in (2), tup_b (3), tup_a (4), rwt (5), min_b (6)
def X.chain(i: Nat) -> C.Cir.Stmt:
  match i:
    case 0n:
      sel.a(sel.b(sel.b(sel.b(sel.e(C.M.ret())))))
    case 1n+j:
      sel.e(X.chain(j))

# a single store
def eq.store(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +k: Nat, c: C.Cir.Expr, v: C.Cir.Expr, +i: U32, +x: U32,
  ec: {C.Cir.eval(c, X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{i} : Maybe<&2, U32>},
  ev: {C.Cir.eval(v, X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{x} : Maybe<&2, U32>},
  hc: {C.Cir.is_cell(i, im, fi, nx) == True{} : Bool}) ->
  {C.Cir.exec(f, C.Cir.Stmt.store{k, c, v}, X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.Out.next{X.st(regs, X.put(m, k, i, x), nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  ?TODO

# M.ret's dispatch
# ----------------
#
# A round from mode 1 whose top frame h (register sp) has the tag of a kind:
# registers h, tag and q get the frame, its tag and its quantity, and the
# round runs that kind's branch (for app_arg and app_val, the test of K
# comes next; for min_a, the last else).

def ret.disp.app(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +h: U32, hl: {List.length(&2, U32, regs) == 64n : Nat},
  h1: {List.get(&2, U32, regs, 1n) == Some{1} : Maybe<&2, U32>}, h2: {List.get(&2, U32, regs, 2n) == Some{h} : Maybe<&2, U32>},
  hz: {U32.is_eq(h, 0) == False{} : Bool}, hc: {C.Cir.is_cell(h, im, fi, nx) == True{} : Bool},
  ht: {U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 63) == 32 : U32}) ->
  {C.Cir.exec(f, X.body(), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.exec(f, sel.t(X.chain(0n)), X.st(X.set(X.set(X.set(regs, 9n, h), 10n, 32), 14n, U32.and(U32.shrn(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 6n), 3)), m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  ?TODO

def ret.disp.val(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +h: U32, hl: {List.length(&2, U32, regs) == 64n : Nat},
  h1: {List.get(&2, U32, regs, 1n) == Some{1} : Maybe<&2, U32>}, h2: {List.get(&2, U32, regs, 2n) == Some{h} : Maybe<&2, U32>},
  hz: {U32.is_eq(h, 0) == False{} : Bool}, hc: {C.Cir.is_cell(h, im, fi, nx) == True{} : Bool},
  ht: {U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 63) == 33 : U32}) ->
  {C.Cir.exec(f, X.body(), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.exec(f, sel.t(X.chain(0n)), X.st(X.set(X.set(X.set(regs, 9n, h), 10n, 33), 14n, U32.and(U32.shrn(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 6n), 3)), m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  ?TODO

def ret.disp.fun(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +h: U32, hl: {List.length(&2, U32, regs) == 64n : Nat},
  h1: {List.get(&2, U32, regs, 1n) == Some{1} : Maybe<&2, U32>}, h2: {List.get(&2, U32, regs, 2n) == Some{h} : Maybe<&2, U32>},
  hz: {U32.is_eq(h, 0) == False{} : Bool}, hc: {C.Cir.is_cell(h, im, fi, nx) == True{} : Bool},
  ht: {U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 63) == 34 : U32}) ->
  {C.Cir.exec(f, X.body(), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.exec(f, sel.t(X.chain(1n)), X.st(X.set(X.set(X.set(regs, 9n, h), 10n, 34), 14n, U32.and(U32.shrn(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 6n), 3)), m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  ?TODO

def ret.disp.let(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +h: U32, hl: {List.length(&2, U32, regs) == 64n : Nat},
  h1: {List.get(&2, U32, regs, 1n) == Some{1} : Maybe<&2, U32>}, h2: {List.get(&2, U32, regs, 2n) == Some{h} : Maybe<&2, U32>},
  hz: {U32.is_eq(h, 0) == False{} : Bool}, hc: {C.Cir.is_cell(h, im, fi, nx) == True{} : Bool},
  ht: {U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 63) == 35 : U32}) ->
  {C.Cir.exec(f, X.body(), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.exec(f, sel.t(X.chain(2n)), X.st(X.set(X.set(X.set(regs, 9n, h), 10n, 35), 14n, U32.and(U32.shrn(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 6n), 3)), m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  ?TODO

def ret.disp.tupb(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +h: U32, hl: {List.length(&2, U32, regs) == 64n : Nat},
  h1: {List.get(&2, U32, regs, 1n) == Some{1} : Maybe<&2, U32>}, h2: {List.get(&2, U32, regs, 2n) == Some{h} : Maybe<&2, U32>},
  hz: {U32.is_eq(h, 0) == False{} : Bool}, hc: {C.Cir.is_cell(h, im, fi, nx) == True{} : Bool},
  ht: {U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 63) == 36 : U32}) ->
  {C.Cir.exec(f, X.body(), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.exec(f, sel.t(X.chain(3n)), X.st(X.set(X.set(X.set(regs, 9n, h), 10n, 36), 14n, U32.and(U32.shrn(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 6n), 3)), m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  ?TODO

def ret.disp.tupa(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +h: U32, hl: {List.length(&2, U32, regs) == 64n : Nat},
  h1: {List.get(&2, U32, regs, 1n) == Some{1} : Maybe<&2, U32>}, h2: {List.get(&2, U32, regs, 2n) == Some{h} : Maybe<&2, U32>},
  hz: {U32.is_eq(h, 0) == False{} : Bool}, hc: {C.Cir.is_cell(h, im, fi, nx) == True{} : Bool},
  ht: {U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 63) == 37 : U32}) ->
  {C.Cir.exec(f, X.body(), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.exec(f, sel.t(X.chain(4n)), X.st(X.set(X.set(X.set(regs, 9n, h), 10n, 37), 14n, U32.and(U32.shrn(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 6n), 3)), m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  ?TODO

def ret.disp.rwt(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +h: U32, hl: {List.length(&2, U32, regs) == 64n : Nat},
  h1: {List.get(&2, U32, regs, 1n) == Some{1} : Maybe<&2, U32>}, h2: {List.get(&2, U32, regs, 2n) == Some{h} : Maybe<&2, U32>},
  hz: {U32.is_eq(h, 0) == False{} : Bool}, hc: {C.Cir.is_cell(h, im, fi, nx) == True{} : Bool},
  ht: {U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 63) == 38 : U32}) ->
  {C.Cir.exec(f, X.body(), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.exec(f, sel.t(X.chain(5n)), X.st(X.set(X.set(X.set(regs, 9n, h), 10n, 38), 14n, U32.and(U32.shrn(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 6n), 3)), m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  ?TODO

def ret.disp.minb(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +h: U32, hl: {List.length(&2, U32, regs) == 64n : Nat},
  h1: {List.get(&2, U32, regs, 1n) == Some{1} : Maybe<&2, U32>}, h2: {List.get(&2, U32, regs, 2n) == Some{h} : Maybe<&2, U32>},
  hz: {U32.is_eq(h, 0) == False{} : Bool}, hc: {C.Cir.is_cell(h, im, fi, nx) == True{} : Bool},
  ht: {U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 63) == 39 : U32}) ->
  {C.Cir.exec(f, X.body(), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.exec(f, sel.t(X.chain(6n)), X.st(X.set(X.set(X.set(regs, 9n, h), 10n, 39), 14n, U32.and(U32.shrn(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 6n), 3)), m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  ?TODO

def ret.disp.mina(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +h: U32, hl: {List.length(&2, U32, regs) == 64n : Nat},
  h1: {List.get(&2, U32, regs, 1n) == Some{1} : Maybe<&2, U32>}, h2: {List.get(&2, U32, regs, 2n) == Some{h} : Maybe<&2, U32>},
  hz: {U32.is_eq(h, 0) == False{} : Bool}, hc: {C.Cir.is_cell(h, im, fi, nx) == True{} : Bool},
  ht: {U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 63) == 40 : U32}) ->
  {C.Cir.exec(f, X.body(), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.exec(f, sel.e(X.chain(6n)), X.st(X.set(X.set(X.set(regs, 9n, h), 10n, 40), 14n, U32.and(U32.shrn(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 6n), 3)), m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  ?TODO

# The frames
# ----------

# M.swap(hdx), with the frame h in register h: register n and the focus get
# the frame's term, the frame gets the header hd (hdx's value) and the old
# focus foc, and the mode is 0
def swap.eq(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +h: U32, +foc: U32, hdx: C.Cir.Expr, +hd: U32, hl: {List.length(&2, U32, regs) == 64n : Nat},
  h0: {List.get(&2, U32, regs, 0n) == Some{foc} : Maybe<&2, U32>}, h9: {List.get(&2, U32, regs, 9n) == Some{h} : Maybe<&2, U32>}, hc: {C.Cir.is_cell(h, im, fi, nx) == True{} : Bool},
  ehd: {C.Cir.eval(hdx, X.st(X.set(regs, 15n, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, h))), m, nx, fi, im, pg, lim, inp)) == Some{hd} : Maybe<&2, U32>}) ->
  {C.Cir.exec(f, C.M.swap(hdx), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.Out.next{X.st(X.set(X.set(X.set(regs, 15n, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, h))), 0n, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, h))), 1n, 0), X.put(X.put(m, 0n, h, hd), 2n, h, foc), nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  ?TODO

# M.pop: register fr gets the top frame sp, sp the next frame (its field 1),
# and the frame goes to the pend list (its field 1 gets pend, pend gets it)
def pop.eq(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +sp: U32, +pend: U32, hl: {List.length(&2, U32, regs) == 64n : Nat},
  h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}, hc: {C.Cir.is_cell(sp, im, fi, nx) == True{} : Bool}) ->
  {C.Cir.exec(f, C.M.pop(), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.Out.next{X.st(X.set(X.set(X.set(regs, 16n, sp), 2n, C.Cir.Cell.get(1n, C.Cir.Cells.get(m, sp))), 3n, sp), X.put(m, 1n, sp, pend), nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  ?TODO

# Counts
# ------

# M.inc(r) of the cell c: nothing for 0 or a STATIC cell; else its count
# gains 1
def inc.eq.z(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, hr: {List.get(&2, U32, regs, r) == Some{0} : Maybe<&2, U32>}) ->
  {C.Cir.exec(f, C.M.inc(r), X.st(regs, m, nx, fi, im, pg, lim, inp)) == C.Cir.Out.next{X.st(regs, m, nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  ?TODO

def inc.eq.s(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, +c: U32, hr: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>}, hz: {U32.is_eq(c, 0) == False{} : Bool},
  hc: {C.Cir.is_cell(c, im, fi, nx) == True{} : Bool}, hs: {U32.is_ne(U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), 1024), 0) == True{} : Bool}) ->
  {C.Cir.exec(f, C.M.inc(r), X.st(regs, m, nx, fi, im, pg, lim, inp)) == C.Cir.Out.next{X.st(regs, m, nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  ?TODO

def inc.eq.n(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, +c: U32, hr: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>}, hz: {U32.is_eq(c, 0) == False{} : Bool},
  hc: {C.Cir.is_cell(c, im, fi, nx) == True{} : Bool}, hs: {U32.is_ne(U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), 1024), 0) == False{} : Bool}) ->
  {C.Cir.exec(f, C.M.inc(r), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.Out.next{X.st(regs, X.put(m, 1n, c, U32.add(C.Cir.Cell.get(1n, C.Cir.Cells.get(m, c)), 1)), nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  ?TODO

# M.dec(r) of the cell c: nothing for 0 or a STATIC cell; else register dr and
# its count get d, its count less 1; at 0 its field 1 gets pend and pend gets c
def dec.eq.z(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, hr: {List.get(&2, U32, regs, r) == Some{0} : Maybe<&2, U32>}) ->
  {C.Cir.exec(f, C.M.dec(r), X.st(regs, m, nx, fi, im, pg, lim, inp)) == C.Cir.Out.next{X.st(regs, m, nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  ?TODO

def dec.eq.s(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, +c: U32, hr: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>}, hz: {U32.is_eq(c, 0) == False{} : Bool},
  hc: {C.Cir.is_cell(c, im, fi, nx) == True{} : Bool}, hs: {U32.is_ne(U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), 1024), 0) == True{} : Bool}) ->
  {C.Cir.exec(f, C.M.dec(r), X.st(regs, m, nx, fi, im, pg, lim, inp)) == C.Cir.Out.next{X.st(regs, m, nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  ?TODO

def dec.eq.n(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, +c: U32, hl: {List.length(&2, U32, regs) == 64n : Nat}, hr: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>}, hz: {U32.is_eq(c, 0) == False{} : Bool},
  hc: {C.Cir.is_cell(c, im, fi, nx) == True{} : Bool}, hs: {U32.is_ne(U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), 1024), 0) == False{} : Bool},
  hd: {U32.is_eq(U32.sub(C.Cir.Cell.get(1n, C.Cir.Cells.get(m, c)), 1), 0) == False{} : Bool}, h5: {Nat.is_eq(5n, r) == False{} : Bool}) ->
  {C.Cir.exec(f, C.M.dec(r), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.Out.next{X.st(X.set(regs, 5n, U32.sub(C.Cir.Cell.get(1n, C.Cir.Cells.get(m, c)), 1)), X.put(m, 1n, c, U32.sub(C.Cir.Cell.get(1n, C.Cir.Cells.get(m, c)), 1)), nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  ?TODO

def dec.eq.p(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, +c: U32, +pend: U32, hl: {List.length(&2, U32, regs) == 64n : Nat}, hr: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>}, h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  hz: {U32.is_eq(c, 0) == False{} : Bool}, hc: {C.Cir.is_cell(c, im, fi, nx) == True{} : Bool},
  hs: {U32.is_ne(U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), 1024), 0) == False{} : Bool},
  hd: {U32.is_eq(U32.sub(C.Cir.Cell.get(1n, C.Cir.Cells.get(m, c)), 1), 0) == True{} : Bool}, h5: {Nat.is_eq(5n, r) == False{} : Bool}) ->
  {C.Cir.exec(f, C.M.dec(r), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.Out.next{X.st(X.set(X.set(regs, 5n, U32.sub(C.Cir.Cell.get(1n, C.Cir.Cells.get(m, c)), 1)), 3n, c), X.put(X.put(m, 1n, c, U32.sub(C.Cir.Cell.get(1n, C.Cir.Cells.get(m, c)), 1)), 1n, c, pend), nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  ?TODO

# Allocation
# ----------

# M.alloc(r) with an empty pend list: Cir's alloc
def alloc.eq.fresh(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, h3: {List.get(&2, U32, regs, 3n) == Some{0} : Maybe<&2, U32>}) ->
  {C.Cir.exec(f, C.M.alloc(r), X.st(regs, m, nx, fi, im, pg, lim, inp)) == C.Cir.exec.alloc(r, X.st(regs, m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  ?TODO

# M.alloc(r) from the pend list's first cell p: aq gets p, pend its field 1,
# am its tag's mask (a term cell, by the table's cell 345 + tag) or 0 (a cell
# of the machine's own kinds); then the rest of M.alloc (its parts lose a
# pointer, it is set to zeros, r gets it)
def alloc.eq.term(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, +p: U32, hl: {List.length(&2, U32, regs) == 64n : Nat}, h3: {List.get(&2, U32, regs, 3n) == Some{p} : Maybe<&2, U32>}, hz: {U32.is_eq(p, 0) == False{} : Bool},
  hc: {C.Cir.is_cell(p, im, fi, nx) == True{} : Bool}, ht: {U32.is_lt(U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, p)), 63), 32) == True{} : Bool},
  hm: {C.Cir.is_cell(U32.add(345, U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, p)), 63)), im, fi, nx) == True{} : Bool}) ->
  {C.Cir.exec(f, C.M.alloc(r), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.exec(f, sel.b(sel.b(sel.b(sel.t(C.M.alloc(r))))), X.st(X.set(X.set(X.set(regs, 6n, p), 3n, C.Cir.Cell.get(1n, C.Cir.Cells.get(m, p))), 7n, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, U32.add(345, U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, p)), 63))))), m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  ?TODO

def alloc.eq.own(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, +p: U32, hl: {List.length(&2, U32, regs) == 64n : Nat}, h3: {List.get(&2, U32, regs, 3n) == Some{p} : Maybe<&2, U32>}, hz: {U32.is_eq(p, 0) == False{} : Bool},
  hc: {C.Cir.is_cell(p, im, fi, nx) == True{} : Bool}, ht: {U32.is_lt(U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, p)), 63), 32) == False{} : Bool}) ->
  {C.Cir.exec(f, C.M.alloc(r), X.st(regs, m, nx, fi, im, pg, lim, inp)) == C.Cir.exec(f, sel.b(sel.b(sel.b(sel.t(C.M.alloc(r))))), X.st(X.set(X.set(X.set(regs, 6n, p), 3n, C.Cir.Cell.get(1n, C.Cir.Cells.get(m, p))), 7n, 0), m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  ?TODO

# a part of the cell aq loses a pointer (M.dec.part), when the mask am names
# it: register dx gets it, then M.dec(dx); else nothing
def dec.part.off(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +k: Nat, +bit: U32, +am: U32, h7: {List.get(&2, U32, regs, 7n) == Some{am} : Maybe<&2, U32>},
  hb: {U32.is_eq(U32.and(am, bit), 0) == True{} : Bool}) ->
  {C.Cir.exec(f, C.M.dec.part(k, bit), X.st(regs, m, nx, fi, im, pg, lim, inp)) == C.Cir.Out.next{X.st(regs, m, nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  ?TODO

def dec.part.on(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +k: Nat, +bit: U32, +am: U32, +aq: U32, hl: {List.length(&2, U32, regs) == 64n : Nat}, h6: {List.get(&2, U32, regs, 6n) == Some{aq} : Maybe<&2, U32>}, h7: {List.get(&2, U32, regs, 7n) == Some{am} : Maybe<&2, U32>},
  hb: {U32.is_eq(U32.and(am, bit), 0) == False{} : Bool}, hc: {C.Cir.is_cell(aq, im, fi, nx) == True{} : Bool}) ->
  {C.Cir.exec(f, C.M.dec.part(k, bit), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.exec(f, C.M.dec(C.R.dx()), X.st(X.set(regs, 4n, C.Cir.Cell.get(k, C.Cir.Cells.get(m, aq))), m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  ?TODO

# M.alloc's end: the cell aq is set to zeros and r gets it
def alloc.eq.end(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, +aq: U32, hl: {List.length(&2, U32, regs) == 64n : Nat}, h6: {List.get(&2, U32, regs, 6n) == Some{aq} : Maybe<&2, U32>}, hc: {C.Cir.is_cell(aq, im, fi, nx) == True{} : Bool},
  hr: {Nat.is_lt(r, 64n) == True{} : Bool}) ->
  {C.Cir.exec(f, sel.b(sel.b(sel.b(sel.b(sel.b(sel.b(sel.t(C.M.alloc(r)))))))), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.Out.next{X.st(X.set(regs, r, aq), C.Cir.Cells.set(m, aq, C.Cir.Cell.zero()), nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  ?TODO

# a new cell, after its M.alloc gives the state st1 with the cell z in r:
# M.make stores the header h, the count 1 and the fields a, b, c, each
# expression's value in the state where it runs
def make.eq(+f: Nat, st: C.Cir.State, +st1: C.Cir.State, +r: Nat, h: C.Cir.Expr, a: C.Cir.Expr, b: C.Cir.Expr,
  c: C.Cir.Expr, +z: U32, +hv: U32, +av: U32, +bv: U32, +cv: U32,
  e1: {C.Cir.exec(f, C.M.alloc(r), st) == C.Cir.Out.next{st1} : C.Cir.Out},
  ez: {List.get(&2, U32, X.regs(st1), r) == Some{z} : Maybe<&2, U32>},
  hz: {C.Cir.eval(C.M.f(0n, C.M.g(r)), st1) == Some{C.Cir.Cell.get(0n, C.Cir.Cells.get(X.cells(st1), z))} : Maybe<&2, U32>},
  eh: {C.Cir.eval(h, st1) == Some{hv} : Maybe<&2, U32>},
  ea: {C.Cir.eval(a, X.store(X.store(st1, 0n, z, hv), 1n, z, 1)) == Some{av} : Maybe<&2, U32>},
  eb: {C.Cir.eval(b, X.store(X.store(X.store(st1, 0n, z, hv), 1n, z, 1), 2n, z, av)) == Some{bv} : Maybe<&2, U32>},
  ec: {C.Cir.eval(c, X.store(X.store(X.store(X.store(st1, 0n, z, hv), 1n, z, 1), 2n, z, av), 3n, z, bv)) == Some{cv} : Maybe<&2, U32>}) ->
  {C.Cir.exec(f, C.M.make(r, h, a, b, c), st) ==
    C.Cir.Out.next{X.store(X.store(X.store(X.store(X.store(st1, 0n, z, hv), 1n, z, 1), 2n, z, av), 3n, z, bv), 4n, z, cv)} : C.Cir.Out}:
  ?TODO

# a new frame, after its M.alloc gives the state st1 with the cell z in fr:
# M.push stores the header h, the link sp and the fields a, b; sp gets z
def push.eq(+f: Nat, st: C.Cir.State, +st1: C.Cir.State, h: C.Cir.Expr, a: C.Cir.Expr, b: C.Cir.Expr, +z: U32, +sp: U32,
  +hv: U32, +av: U32, +bv: U32,
  e1: {C.Cir.exec(f, C.M.alloc(C.R.fr()), st) == C.Cir.Out.next{st1} : C.Cir.Out},
  ez: {List.get(&2, U32, X.regs(st1), 16n) == Some{z} : Maybe<&2, U32>},
  esp: {List.get(&2, U32, X.regs(st1), 2n) == Some{sp} : Maybe<&2, U32>},
  hz: {C.Cir.eval(C.M.f(0n, C.M.g(C.R.fr())), st1) == Some{C.Cir.Cell.get(0n, C.Cir.Cells.get(X.cells(st1), z))} : Maybe<&2, U32>},
  eh: {C.Cir.eval(h, st1) == Some{hv} : Maybe<&2, U32>},
  ea: {C.Cir.eval(a, X.store(X.store(st1, 0n, z, hv), 1n, z, sp)) == Some{av} : Maybe<&2, U32>},
  eb: {C.Cir.eval(b, X.store(X.store(X.store(st1, 0n, z, hv), 1n, z, sp), 2n, z, av)) == Some{bv} : Maybe<&2, U32>},
  hl: {List.length(&2, U32, X.regs(st1)) == 64n : Nat}) ->
  {C.Cir.exec(f, C.M.push(h, a, b), st) ==
    C.Cir.Out.next{X.setst(X.store(X.store(X.store(X.store(st1, 0n, z, hv), 1n, z, sp), 2n, z, av), 3n, z, bv), 2n, z)} : C.Cir.Out}:
  ?TODO
