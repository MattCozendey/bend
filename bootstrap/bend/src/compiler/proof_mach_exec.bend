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

# Proof kit
# ---------
#
# Bools (k.*), lists of registers (L.*: a set is there, keeps the others and
# the length), the values of expressions (ev.*) and the runs of statements
# (run.* as equations of their outcome; rw.* in the orientation that a
# rewrite of the goal takes, the new statement first), for any fuel.

def k.bt(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def k.bf(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def k.ft.e(h: {True{} == False{} : Bool}) -> Empty:
  %h : k.bt(_)
  Unit{}

def k.tf.e(h: {False{} == True{} : Bool}) -> Empty:
  %h : k.bf(_)
  Unit{}

def k.ft(-G: Type, h: {True{} == False{} : Bool}) -> G:
  Empty.absurd(G, k.ft.e(h))

def k.tf(-G: Type, h: {False{} == True{} : Bool}) -> G:
  Empty.absurd(G, k.tf.e(h))

# the register r set to v holds v
def L.gs(xs: List<&2, U32>, r: Nat, +v: U32, h: {Nat.is_lt(r, List.length(&2, U32, xs)) == True{} : Bool}) ->
  {List.get(&2, U32, List.set(&2, U32, xs, r, v), r) == Some{v} : Maybe<&2, U32>}:
  match xs r:
    case Nil{} 0n:
      k.tf({None{} == Some{v} : Maybe<&2, U32>}, h)
    case Nil{} 1n+p:
      k.tf({None{} == Some{v} : Maybe<&2, U32>}, h)
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      L.gs(t, p, v, h)

# a set of r keeps the register j
def L.go(xs: List<&2, U32>, r: Nat, j: Nat, +v: U32, -w: U32, ne: {Nat.is_eq(r, j) == False{} : Bool},
  h: {List.get(&2, U32, xs, j) == Some{w} : Maybe<&2, U32>}) ->
  {List.get(&2, U32, List.set(&2, U32, xs, r, v), j) == Some{w} : Maybe<&2, U32>}:
  match xs r j:
    case Nil{} _ _:
      h
    case Con{x, t} 0n 0n:
      k.ft({Some{v} == Some{w} : Maybe<&2, U32>}, ne)
    case Con{x, t} 0n 1n+q:
      h
    case Con{x, t} 1n+p 0n:
      h
    case Con{x, t} 1n+p 1n+q:
      L.go(t, p, q, v, w, ne, h)

# a set keeps the length
def L.len(xs: List<&2, U32>, r: Nat, +v: U32, -n: Nat, h: {List.length(&2, U32, xs) == n : Nat}) ->
  {List.length(&2, U32, List.set(&2, U32, xs, r, v)) == n : Nat}:
  match xs r:
    case Nil{} _:
      h
    case Con{x, t} 0n:
      h
    case Con{x, t} 1n+p:
      %Equal.sym(Nat, List.length(&2, U32, List.set(&2, U32, t, p, v)), List.length(&2, U32, t), L.len(t, p, v, List.length(&2, U32, t), {==})) :
        {1n+_ == n : Nat}
      h

# a register below 64 is one of 64
def L.lt(+xs: List<&2, U32>, +r: Nat, hl: {List.length(&2, U32, xs) == 64n : Nat}, hr: {Nat.is_lt(r, 64n) == True{} : Bool}) ->
  {Nat.is_lt(r, List.length(&2, U32, xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, U32, xs), 64n, hl) : {Nat.is_lt(r, _) == True{} : Bool}
  hr

# the cell i is one that st may access
def X.cell(st: C.Cir.State, +i: U32) -> Bool:
  match st:
    case C.Cir.State{_, _, +nx, +fi, +im, _, _, _, _, _}:
      C.Cir.is_cell(i, im, fi, nx)

# the value of an operation, from its operands'
def ev.op(o: C.Wasm.Op, a: C.Cir.Expr, b: C.Cir.Expr, +st: C.Cir.State, -x: U32, -y: U32,
  ea: {C.Cir.eval(a, st) == Some{x} : Maybe<&2, U32>}, eb: {C.Cir.eval(b, st) == Some{y} : Maybe<&2, U32>}) ->
  {C.Cir.eval(C.Cir.Expr.op{o, a, b}, st) == Some{C.Wasm.op(o, x, y)} : Maybe<&2, U32>}:
  %Equal.sym(Maybe<&2, U32>, C.Cir.eval(a, st), Some{x}, ea) :
    {C.Cir.eval.op(o, _, C.Cir.eval(b, st)) == Some{C.Wasm.op(o, x, y)} : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, C.Cir.eval(b, st), Some{y}, eb) :
    {C.Cir.eval.op(o, Some{x}, _) == Some{C.Wasm.op(o, x, y)} : Maybe<&2, U32>}
  {==}

# the same, with the operation's value w
def ev.opw(+o: C.Wasm.Op, +a: C.Cir.Expr, +b: C.Cir.Expr, +st: C.Cir.State, +x: U32, +y: U32, +w: U32,
  ea: {C.Cir.eval(a, st) == Some{x} : Maybe<&2, U32>}, eb: {C.Cir.eval(b, st) == Some{y} : Maybe<&2, U32>},
  hw: {C.Wasm.op(o, x, y) == w : U32}) ->
  {C.Cir.eval(C.Cir.Expr.op{o, a, b}, st) == Some{w} : Maybe<&2, U32>}:
  %Equal.sym(U32, C.Wasm.op(o, x, y), w, hw) : {C.Cir.eval(C.Cir.Expr.op{o, a, b}, st) == Some{_} : Maybe<&2, U32>}
  ev.op(o, a, b, st, x, y, ea, eb)

def ev.fld.of(+k: Nat, st: C.Cir.State, +i: U32, hv: {X.cell(st, i) == True{} : Bool}) ->
  {C.Cir.eval.field(k, Some{i}, st) == Some{C.Cir.Cell.get(k, C.Cir.Cells.get(X.cells(st), i))} : Maybe<&2, U32>}:
  match st:
    case C.Cir.State{regs, +m, +nx, +fi, +im, pg, lim, inp, out, outn}:
      %Equal.sym(Bool, C.Cir.is_cell(i, im, fi, nx), True{}, hv) :
        {C.Cir.eval.field.if(_, k, m, i) == Some{C.Cir.Cell.get(k, C.Cir.Cells.get(m, i))} : Maybe<&2, U32>}
      {==}

# the value of a field of a cell
def ev.fld(+k: Nat, c: C.Cir.Expr, +st: C.Cir.State, +i: U32, ec: {C.Cir.eval(c, st) == Some{i} : Maybe<&2, U32>},
  hv: {X.cell(st, i) == True{} : Bool}) ->
  {C.Cir.eval(C.Cir.Expr.field{k, c}, st) == Some{C.Cir.Cell.get(k, C.Cir.Cells.get(X.cells(st), i))} : Maybe<&2, U32>}:
  %Equal.sym(Maybe<&2, U32>, C.Cir.eval(c, st), Some{i}, ec) :
    {C.Cir.eval.field(k, _, st) == Some{C.Cir.Cell.get(k, C.Cir.Cells.get(X.cells(st), i))} : Maybe<&2, U32>}
  ev.fld.of(k, st, i, hv)

def run.set.of(+r: Nat, +e: C.Cir.Expr, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32,
  +lim: U32, +inp: List<&2, U32>, +out: List<&2, U32>, +outn: U32, +v: U32,
  ev: {C.Cir.eval(e, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}) == Some{v} : Maybe<&2, U32>},
  hl: {List.length(&2, U32, regs) == 64n : Nat}, hr: {Nat.is_lt(r, 64n) == True{} : Bool}) ->
  {C.Cir.exec.set(r, C.Cir.eval(e, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}), C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}) ==
    C.Cir.Out.next{C.Cir.State{List.set(&2, U32, regs, r, v), m, nx, fi, im, pg, lim, inp, out, outn}} : C.Cir.Out}:
  +st = C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}
  +o = {C.Cir.Out.next{C.Cir.State{List.set(&2, U32, regs, r, v), m, nx, fi, im, pg, lim, inp, out, outn}} : C.Cir.Out}
  %Equal.sym(Maybe<&2, U32>, C.Cir.eval(e, st), Some{v}, ev) : {C.Cir.exec.set(r, _, st) == o : C.Cir.Out}
  %Equal.sym(Bool, Nat.is_lt(r, List.length(&2, U32, regs)), True{}, L.lt(regs, r, hl, hr)) :
    {C.Cir.exec.set.of(C.Cir.regs.set.if(_, regs, r, v), st) == o : C.Cir.Out}
  {==}

# a set of the register r (below 64) to the value v of e
def run.set(+f: Nat, +r: Nat, +e: C.Cir.Expr, +st: C.Cir.State, +v: U32, ev: {C.Cir.eval(e, st) == Some{v} : Maybe<&2, U32>},
  hl: {List.length(&2, U32, X.regs(st)) == 64n : Nat}, hr: {Nat.is_lt(r, 64n) == True{} : Bool}) ->
  {C.Cir.exec(f, C.Cir.Stmt.set{r, e}, st) == C.Cir.Out.next{X.setst(st, r, v)} : C.Cir.Out}:
  match f st:
    case 0n C.Cir.State{+regs, +m, +nx, +fi, +im, +pg, +lim, +inp, +out, +outn}:
      run.set.of(r, e, regs, m, nx, fi, im, pg, lim, inp, out, outn, v, ev, hl, hr)
    case 1n+g C.Cir.State{+regs, +m, +nx, +fi, +im, +pg, +lim, +inp, +out, +outn}:
      run.set.of(r, e, regs, m, nx, fi, im, pg, lim, inp, out, outn, v, ev, hl, hr)

def run.store.of(+k: Nat, +c: C.Cir.Expr, +v: C.Cir.Expr, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, U32>, +out: List<&2, U32>, +outn: U32, +i: U32, +x: U32,
  ec: {C.Cir.eval(c, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}) == Some{i} : Maybe<&2, U32>},
  ev: {C.Cir.eval(v, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}) == Some{x} : Maybe<&2, U32>},
  hc: {C.Cir.is_cell(i, im, fi, nx) == True{} : Bool}) ->
  {C.Cir.exec.store(k, C.Cir.eval(c, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}),
    C.Cir.eval(v, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}), C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}) ==
    C.Cir.Out.next{C.Cir.State{regs, X.put(m, k, i, x), nx, fi, im, pg, lim, inp, out, outn}} : C.Cir.Out}:
  +st = C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}
  +o = {C.Cir.Out.next{C.Cir.State{regs, X.put(m, k, i, x), nx, fi, im, pg, lim, inp, out, outn}} : C.Cir.Out}
  %Equal.sym(Maybe<&2, U32>, C.Cir.eval(c, st), Some{i}, ec) : {C.Cir.exec.store(k, _, C.Cir.eval(v, st), st) == o : C.Cir.Out}
  %Equal.sym(Maybe<&2, U32>, C.Cir.eval(v, st), Some{x}, ev) : {C.Cir.exec.store(k, Some{i}, _, st) == o : C.Cir.Out}
  %Equal.sym(Bool, C.Cir.is_cell(i, im, fi, nx), True{}, hc) : {C.Cir.exec.store.if(_, k, i, x, st) == o : C.Cir.Out}
  {==}

# a store of the value x of v in field k of the cell i, the value of c
def run.store(+f: Nat, +k: Nat, +c: C.Cir.Expr, +v: C.Cir.Expr, +st: C.Cir.State, +i: U32, +x: U32,
  ec: {C.Cir.eval(c, st) == Some{i} : Maybe<&2, U32>}, ev: {C.Cir.eval(v, st) == Some{x} : Maybe<&2, U32>},
  hc: {X.cell(st, i) == True{} : Bool}) ->
  {C.Cir.exec(f, C.Cir.Stmt.store{k, c, v}, st) == C.Cir.Out.next{X.store(st, k, i, x)} : C.Cir.Out}:
  match f st:
    case 0n C.Cir.State{+regs, +m, +nx, +fi, +im, +pg, +lim, +inp, +out, +outn}:
      run.store.of(k, c, v, regs, m, nx, fi, im, pg, lim, inp, out, outn, i, x, ec, ev, hc)
    case 1n+g C.Cir.State{+regs, +m, +nx, +fi, +im, +pg, +lim, +inp, +out, +outn}:
      run.store.of(k, c, v, regs, m, nx, fi, im, pg, lim, inp, out, outn, i, x, ec, ev, hc)

def run.nop(+f: Nat, +st: C.Cir.State) -> {C.Cir.exec(f, C.Cir.Stmt.nop{}, st) == C.Cir.Out.next{st} : C.Cir.Out}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

# a then b, after a ends with st1
def rw.seq(+f: Nat, a: C.Cir.Stmt, +b: C.Cir.Stmt, +st: C.Cir.State, +st1: C.Cir.State,
  e1: {C.Cir.exec(f, a, st) == C.Cir.Out.next{st1} : C.Cir.Out}) ->
  {C.Cir.exec(f, b, st1) == C.Cir.exec(f, C.Cir.Stmt.seq{a, b}, st) : C.Cir.Out}:
  match f:
    case 0n:
      %Equal.sym(C.Cir.Out, C.Cir.exec(0n, a, st), C.Cir.Out.next{st1}, e1) :
        {C.Cir.exec(0n, b, st1) == C.Cir.exec.then(_, u => C.Cir.exec(0n, b, u)) : C.Cir.Out}
      {==}
    case 1n+g:
      %Equal.sym(C.Cir.Out, C.Cir.exec(1n+g, a, st), C.Cir.Out.next{st1}, e1) :
        {C.Cir.exec(1n+g, b, st1) == C.Cir.exec.then(_, u => C.Cir.exec(1n+g, b, u)) : C.Cir.Out}
      {==}

def k.then_nop(o: C.Cir.Out, +f: Nat) -> {o == C.Cir.exec.then(o, t => C.Cir.exec(f, C.Cir.Stmt.nop{}, t)) : C.Cir.Out}:
  match o:
    case C.Cir.Out.next{st}:
      Equal.sym(C.Cir.Out, C.Cir.exec(f, C.Cir.Stmt.nop{}, st), C.Cir.Out.next{st}, run.nop(f, st))
    case C.Cir.Out.halt{s, st}:
      {==}
    case C.Cir.Out.out_of_memory{}:
      {==}
    case C.Cir.Out.trap{}:
      {==}
    case C.Cir.Out.not_done{}:
      {==}

# a, then nothing
def rw.seq_nop(+f: Nat, +a: C.Cir.Stmt, +st: C.Cir.State) ->
  {C.Cir.exec(f, a, st) == C.Cir.exec(f, C.Cir.Stmt.seq{a, C.Cir.Stmt.nop{}}, st) : C.Cir.Out}:
  match f:
    case 0n:
      k.then_nop(C.Cir.exec(0n, a, st), 0n)
    case 1n+g:
      k.then_nop(C.Cir.exec(1n+g, a, st), 1n+g)

# an if whose condition is not 0, and one whose condition is 0
def rw.if.t(+f: Nat, c: C.Cir.Expr, +t: C.Cir.Stmt, +e: C.Cir.Stmt, +st: C.Cir.State, -v: U32,
  ev: {C.Cir.eval(c, st) == Some{v} : Maybe<&2, U32>}, nz: {U32.is_zero(v) == False{} : Bool}) ->
  {C.Cir.exec(f, t, st) == C.Cir.exec(f, C.Cir.Stmt.if{c, t, e}, st) : C.Cir.Out}:
  match f:
    case 0n:
      %Equal.sym(Maybe<&2, U32>, C.Cir.eval(c, st), Some{v}, ev) :
        {C.Cir.exec(0n, t, st) == C.Cir.exec.if(_, u => C.Cir.exec(0n, t, st), u => C.Cir.exec(0n, e, st)) : C.Cir.Out}
      %Equal.sym(Bool, U32.is_zero(v), False{}, nz) :
        {C.Cir.exec(0n, t, st) == C.Cir.exec.if.of(_, u => C.Cir.exec(0n, t, st), u => C.Cir.exec(0n, e, st)) : C.Cir.Out}
      {==}
    case 1n+g:
      %Equal.sym(Maybe<&2, U32>, C.Cir.eval(c, st), Some{v}, ev) :
        {C.Cir.exec(1n+g, t, st) == C.Cir.exec.if(_, u => C.Cir.exec(1n+g, t, st), u => C.Cir.exec(1n+g, e, st)) : C.Cir.Out}
      %Equal.sym(Bool, U32.is_zero(v), False{}, nz) :
        {C.Cir.exec(1n+g, t, st) == C.Cir.exec.if.of(_, u => C.Cir.exec(1n+g, t, st), u => C.Cir.exec(1n+g, e, st)) : C.Cir.Out}
      {==}

def rw.if.e(+f: Nat, c: C.Cir.Expr, +t: C.Cir.Stmt, +e: C.Cir.Stmt, +st: C.Cir.State,
  ev: {C.Cir.eval(c, st) == Some{0} : Maybe<&2, U32>}) ->
  {C.Cir.exec(f, e, st) == C.Cir.exec(f, C.Cir.Stmt.if{c, t, e}, st) : C.Cir.Out}:
  match f:
    case 0n:
      %Equal.sym(Maybe<&2, U32>, C.Cir.eval(c, st), Some{0}, ev) :
        {C.Cir.exec(0n, e, st) == C.Cir.exec.if(_, u => C.Cir.exec(0n, t, st), u => C.Cir.exec(0n, e, st)) : C.Cir.Out}
      {==}
    case 1n+g:
      %Equal.sym(Maybe<&2, U32>, C.Cir.eval(c, st), Some{0}, ev) :
        {C.Cir.exec(1n+g, e, st) == C.Cir.exec.if(_, u => C.Cir.exec(1n+g, t, st), u => C.Cir.exec(1n+g, e, st)) : C.Cir.Out}
      {==}

# the test of the register r against 0, for the cell c in it: 0 for ==, 1 for !=
def ev.eq0(+r: Nat, +st: C.Cir.State, +c: U32, h: {C.Cir.eval(C.M.g(r), st) == Some{c} : Maybe<&2, U32>},
  hz: {U32.is_eq(c, 0) == False{} : Bool}) -> {C.Cir.eval(C.M.eq(C.M.g(r), C.M.c(0)), st) == Some{0} : Maybe<&2, U32>}:
  ev.opw(C.Wasm.Op.eq{}, C.M.g(r), C.M.c(0), st, c, 0, 0, h, {==}, Equal.cong(Bool, U32, b => Bool.to_u32(b), U32.is_eq(c, 0), False{}, hz))

def ev.ne0(+r: Nat, +st: C.Cir.State, +c: U32, h: {C.Cir.eval(C.M.g(r), st) == Some{c} : Maybe<&2, U32>},
  hz: {U32.is_eq(c, 0) == False{} : Bool}) -> {C.Cir.eval(C.M.ne(C.M.g(r), C.M.c(0)), st) == Some{1} : Maybe<&2, U32>}:
  ev.opw(C.Wasm.Op.ne{}, C.M.g(r), C.M.c(0), st, c, 0, 1, h, {==}, Equal.cong(Bool, U32, b => Bool.to_u32(Bool.not(b)), U32.is_eq(c, 0), False{}, hz))

# a single store
def eq.store(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +k: Nat, c: C.Cir.Expr, v: C.Cir.Expr, +i: U32, +x: U32,
  ec: {C.Cir.eval(c, X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{i} : Maybe<&2, U32>},
  ev: {C.Cir.eval(v, X.st(regs, m, nx, fi, im, pg, lim, inp)) == Some{x} : Maybe<&2, U32>},
  hc: {C.Cir.is_cell(i, im, fi, nx) == True{} : Bool}) ->
  {C.Cir.exec(f, C.Cir.Stmt.store{k, c, v}, X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.Out.next{X.st(regs, X.put(m, k, i, x), nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  run.store(f, k, c, v, X.st(regs, m, nx, fi, im, pg, lim, inp), i, x, ec, ev, hc)

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
