# compiler: layer B, the run of the machine's statements
# ======================================================
#
# Equations of Cir.exec for the parts of the machine's code that the moves of
# proof_mach.bend run, all proven. Each holds for any
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
  %hw : {C.Cir.eval(C.Cir.Expr.op{o, a, b}, st) == Some{_} : Maybe<&2, U32>}
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
  +st = {C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn} : C.Cir.State}
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
  +st = {C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn} : C.Cir.State}
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

# not the value of a
def ev.eqz(+a: C.Cir.Expr, +st: C.Cir.State, -x: U32, ea: {C.Cir.eval(a, st) == Some{x} : Maybe<&2, U32>}) ->
  {C.Cir.eval(C.Cir.Expr.eqz{a}, st) == Some{Bool.to_u32(U32.is_zero(x))} : Maybe<&2, U32>}:
  %Equal.sym(Maybe<&2, U32>, C.Cir.eval(a, st), Some{x}, ea) :
    {C.Cir.eval.eqz(_) == Some{Bool.to_u32(U32.is_zero(x))} : Maybe<&2, U32>}
  {==}

# M.not(M.flag) of the cell c in register r, when the flag's test is b
def ev.notflag(+r: Nat, +st: C.Cir.State, +c: U32, +fl: U32, +b: Bool, +hr: {C.Cir.eval(C.M.g(r), st) == Some{c} : Maybe<&2, U32>},
  hc: {X.cell(st, c) == True{} : Bool}, hs: {U32.is_ne(U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(X.cells(st), c)), fl), 0) == b : Bool}) ->
  {C.Cir.eval(C.M.not(C.M.flag(C.M.g(r), fl)), st) == Some{Bool.to_u32(U32.is_zero(Bool.to_u32(b)))} : Maybe<&2, U32>}:
  +f0 = C.Cir.Cell.get(0n, C.Cir.Cells.get(X.cells(st), c))
  ev.eqz(C.M.flag(C.M.g(r), fl), st, Bool.to_u32(b),
    ev.opw(C.Wasm.Op.ne{}, C.M.and(C.M.f(0n, C.M.g(r)), C.M.c(fl)), C.M.c(0), st, U32.and(f0, fl), 0, Bool.to_u32(b),
      ev.op(C.Wasm.Op.and{}, C.M.f(0n, C.M.g(r)), C.M.c(fl), st, f0, fl, ev.fld(0n, C.M.g(r), st, c, hr, hc), {==}), {==},
      Equal.cong(Bool, U32, x => Bool.to_u32(x), U32.is_ne(U32.and(f0, fl), 0), b, hs)))

def run.alloc(+f: Nat, +r: Nat, +st: C.Cir.State) -> {C.Cir.exec(f, C.Cir.Stmt.alloc{r}, st) == C.Cir.exec.alloc(r, st) : C.Cir.Out}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

# an if whose condition is not 0, or is 0, that ends as its branch does
def run.if.t(+f: Nat, +c: C.Cir.Expr, +t: C.Cir.Stmt, +e: C.Cir.Stmt, +st: C.Cir.State, -v: U32,
  ev: {C.Cir.eval(c, st) == Some{v} : Maybe<&2, U32>}, nz: {U32.is_zero(v) == False{} : Bool}, -o: C.Cir.Out,
  h: {C.Cir.exec(f, t, st) == o : C.Cir.Out}) -> {C.Cir.exec(f, C.Cir.Stmt.if{c, t, e}, st) == o : C.Cir.Out}:
  %rw.if.t(f, c, t, e, st, v, ev, nz) : {_ == o : C.Cir.Out}
  h

def run.if.e(+f: Nat, +c: C.Cir.Expr, +t: C.Cir.Stmt, +e: C.Cir.Stmt, +st: C.Cir.State,
  ev: {C.Cir.eval(c, st) == Some{0} : Maybe<&2, U32>}, -o: C.Cir.Out,
  h: {C.Cir.exec(f, e, st) == o : C.Cir.Out}) -> {C.Cir.exec(f, C.Cir.Stmt.if{c, t, e}, st) == o : C.Cir.Out}:
  %rw.if.e(f, c, t, e, st, ev) : {_ == o : C.Cir.Out}
  h

# a cell set at w is there
def Ce.get_set.at(n: Nat, +w: Word(n), +m: C.Cir.Cells, +c: C.Cir.Cell) ->
  {C.Cir.Cells.get.at(n, w, C.Cir.Cells.set.at(n, w, m, c)) == c : C.Cir.Cell}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          match m:
            case C.Cir.Cells.node{+lo, +hi}:
              Ce.get_set.at(p, t, lo, c)
            case C.Cir.Cells.none{}:
              Ce.get_set.at(p, t, C.Cir.Cells.none{}, c)
            case C.Cir.Cells.one{+d}:
              Ce.get_set.at(p, t, C.Cir.Cells.none{}, c)
        case WCon{True{}, +t}:
          match m:
            case C.Cir.Cells.node{+lo, +hi}:
              Ce.get_set.at(p, t, hi, c)
            case C.Cir.Cells.none{}:
              Ce.get_set.at(p, t, C.Cir.Cells.none{}, c)
            case C.Cir.Cells.one{+d}:
              Ce.get_set.at(p, t, C.Cir.Cells.none{}, c)

def Ce.get_set(+m: C.Cir.Cells, +i: U32, +c: C.Cir.Cell) -> {C.Cir.Cells.get(C.Cir.Cells.set(m, i, c), i) == c : C.Cir.Cell}:
  match i:
    case U32{+w}:
      Ce.get_set.at(32n, w, m, c)

# a cell set twice at w holds the second
def Ce.set_set.at(n: Nat, +w: Word(n), +m: C.Cir.Cells, +c: C.Cir.Cell, +d: C.Cir.Cell) ->
  {C.Cir.Cells.set.at(n, w, m, d) == C.Cir.Cells.set.at(n, w, C.Cir.Cells.set.at(n, w, m, c), d) : C.Cir.Cells}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          match m:
            case C.Cir.Cells.node{+lo, +hi}:
              %Ce.set_set.at(p, t, lo, c, d) : {C.Cir.Cells.node{C.Cir.Cells.set.at(p, t, lo, d), hi} == C.Cir.Cells.node{_, hi} : C.Cir.Cells}
              {==}
            case C.Cir.Cells.none{}:
              %Ce.set_set.at(p, t, C.Cir.Cells.none{}, c, d) :
                {C.Cir.Cells.node{C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, d), C.Cir.Cells.none{}} == C.Cir.Cells.node{_, C.Cir.Cells.none{}} : C.Cir.Cells}
              {==}
            case C.Cir.Cells.one{+e}:
              %Ce.set_set.at(p, t, C.Cir.Cells.none{}, c, d) :
                {C.Cir.Cells.node{C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, d), C.Cir.Cells.none{}} == C.Cir.Cells.node{_, C.Cir.Cells.none{}} : C.Cir.Cells}
              {==}
        case WCon{True{}, +t}:
          match m:
            case C.Cir.Cells.node{+lo, +hi}:
              %Ce.set_set.at(p, t, hi, c, d) : {C.Cir.Cells.node{lo, C.Cir.Cells.set.at(p, t, hi, d)} == C.Cir.Cells.node{lo, _} : C.Cir.Cells}
              {==}
            case C.Cir.Cells.none{}:
              %Ce.set_set.at(p, t, C.Cir.Cells.none{}, c, d) :
                {C.Cir.Cells.node{C.Cir.Cells.none{}, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, d)} == C.Cir.Cells.node{C.Cir.Cells.none{}, _} : C.Cir.Cells}
              {==}
            case C.Cir.Cells.one{+e}:
              %Ce.set_set.at(p, t, C.Cir.Cells.none{}, c, d) :
                {C.Cir.Cells.node{C.Cir.Cells.none{}, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, d)} == C.Cir.Cells.node{C.Cir.Cells.none{}, _} : C.Cir.Cells}
              {==}

def Ce.set_set(+m: C.Cir.Cells, +i: U32, +c: C.Cir.Cell, +d: C.Cir.Cell) ->
  {C.Cir.Cells.set(m, i, d) == C.Cir.Cells.set(C.Cir.Cells.set(m, i, c), i, d) : C.Cir.Cells}:
  match i:
    case U32{+w}:
      Ce.set_set.at(32n, w, m, c, d)

# a store to the cell i, just set to c: i set once
def Ce.put_set(+m: C.Cir.Cells, +i: U32, +c: C.Cir.Cell, +k: Nat, +v: U32) ->
  {C.Cir.Cells.set(m, i, C.Cir.Cell.set(k, c, v)) == X.put(C.Cir.Cells.set(m, i, c), k, i, v) : C.Cir.Cells}:
  %Equal.sym(C.Cir.Cell, C.Cir.Cells.get(C.Cir.Cells.set(m, i, c), i), c, Ce.get_set(m, i, c)) :
    {C.Cir.Cells.set(m, i, C.Cir.Cell.set(k, c, v)) == C.Cir.Cells.set(C.Cir.Cells.set(m, i, c), i, C.Cir.Cell.set(k, _, v)) : C.Cir.Cells}
  Ce.set_set(m, i, c, C.Cir.Cell.set(k, c, v))

def Ce.zero5(c: C.Cir.Cell) ->
  {C.Cir.Cell.set(4n, C.Cir.Cell.set(3n, C.Cir.Cell.set(2n, C.Cir.Cell.set(1n, C.Cir.Cell.set(0n, c, 0), 0), 0), 0), 0) == C.Cir.Cell.zero() : C.Cir.Cell}:
  match c:
    case C.Cir.Cell{a, b, x, y, z}:
      {==}

# the five fields of the cell i set to 0: the cell is all zeros
def Ce.put5(+m: C.Cir.Cells, +i: U32) ->
  {C.Cir.Cells.set(m, i, C.Cir.Cell.zero()) == X.put(X.put(X.put(X.put(X.put(m, 0n, i, 0), 1n, i, 0), 2n, i, 0), 3n, i, 0), 4n, i, 0) : C.Cir.Cells}:
  +z = {C.Cir.Cells.set(m, i, C.Cir.Cell.zero()) : C.Cir.Cells}
  +c1 = C.Cir.Cell.set(0n, C.Cir.Cells.get(m, i), 0)
  +c2 = C.Cir.Cell.set(1n, c1, 0)
  +c3 = C.Cir.Cell.set(2n, c2, 0)
  +c4 = C.Cir.Cell.set(3n, c3, 0)
  %Ce.put_set(m, i, c1, 1n, 0) : {z == X.put(X.put(X.put(_, 2n, i, 0), 3n, i, 0), 4n, i, 0) : C.Cir.Cells}
  %Ce.put_set(m, i, c2, 2n, 0) : {z == X.put(X.put(_, 3n, i, 0), 4n, i, 0) : C.Cir.Cells}
  %Ce.put_set(m, i, c3, 3n, 0) : {z == X.put(_, 4n, i, 0) : C.Cir.Cells}
  %Ce.put_set(m, i, c4, 4n, 0) : {z == _ : C.Cir.Cells}
  Equal.cong(C.Cir.Cell, C.Cir.Cells, x => C.Cir.Cells.set(m, i, x), C.Cir.Cell.zero(), C.Cir.Cell.set(4n, c4, 0),
    Equal.sym(C.Cir.Cell, C.Cir.Cell.set(4n, c4, 0), C.Cir.Cell.zero(), Ce.zero5(C.Cir.Cells.get(m, i))))

def k.ms(x: Maybe<&2, U32>) -> Type:
  match x:
    case None{}:
      Unit
    case Some{_}:
      Empty

def k.none_some(-y: U32, h: {None{} == Some{y} : Maybe<&2, U32>}) -> Empty:
  %h : k.ms(_)
  Unit{}

def k.fi_ok(b: Bool, +k: Nat, +m: C.Cir.Cells, +i: U32, -y: U32, h: {C.Cir.eval.field.if(b, k, m, i) == Some{y} : Maybe<&2, U32>}) ->
  {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, k.none_some(y, h))

# the cell i in register r, whose field 0 Cir reads, is a cell
def k.cell_of(+r: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, U32>, +out: List<&2, U32>, +outn: U32, +i: U32, -y: U32, hr: {List.get(&2, U32, regs, r) == Some{i} : Maybe<&2, U32>},
  h: {C.Cir.eval(C.M.f(0n, C.M.g(r)), C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}) == Some{y} : Maybe<&2, U32>}) ->
  {C.Cir.is_cell(i, im, fi, nx) == True{} : Bool}:
  +st = {C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn} : C.Cir.State}
  k.fi_ok(C.Cir.is_cell(i, im, fi, nx), 0n, m, i, y,
    Equal.trans(Maybe<&2, U32>, C.Cir.eval.field(0n, Some{i}, st), C.Cir.eval(C.M.f(0n, C.M.g(r)), st), Some{y},
      Equal.cong(Maybe<&2, U32>, Maybe<&2, U32>, x => C.Cir.eval.field(0n, x, st), Some{i}, List.get(&2, U32, regs, r),
        Equal.sym(Maybe<&2, U32>, List.get(&2, U32, regs, r), Some{i}, hr)), h))

# the condition of an if
def sel.c(x: C.Cir.Stmt) -> C.Cir.Expr:
  match x:
    case C.Cir.Stmt.if{c, _, _}:
      c
    case _:
      C.Cir.Expr.const{0}

# a round of M.ret once registers h, tag and q hold the frame h, its tag T and
# its quantity
def ret.st(+regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +h: U32,
  +T: U32) -> C.Cir.State:
  X.st(X.set(X.set(X.set(regs, 9n, h), 10n, T), 14n, U32.and(U32.shrn(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 6n), 3)), m, nx, fi, im, pg,
    lim, inp)

# from B.body in mode 1, with the top frame h, to the tests of its tag
def ret.pre(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>,
  +h: U32, +T: U32, +hl: {List.length(&2, U32, regs) == 64n : Nat},
  h1: {List.get(&2, U32, regs, 1n) == Some{1} : Maybe<&2, U32>}, +h2: {List.get(&2, U32, regs, 2n) == Some{h} : Maybe<&2, U32>},
  hz: {U32.is_eq(h, 0) == False{} : Bool}, +hc: {C.Cir.is_cell(h, im, fi, nx) == True{} : Bool},
  ht: {U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 63) == T : U32}) ->
  {C.Cir.exec(f, X.chain(0n), ret.st(regs, m, nx, fi, im, pg, lim, inp, h, T)) == C.Cir.exec(f, X.body(), X.st(regs, m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  +F0 = C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h))
  +r1 = X.set(regs, 9n, h)
  +r2 = X.set(r1, 10n, T)
  +s0 = X.st(regs, m, nx, fi, im, pg, lim, inp)
  +s1 = X.st(r1, m, nx, fi, im, pg, lim, inp)
  +s2 = X.st(r2, m, nx, fi, im, pg, lim, inp)
  +s3 = ret.st(regs, m, nx, fi, im, pg, lim, inp, h, T)
  +lhs = {C.Cir.exec(f, X.chain(0n), s3) : C.Cir.Out}
  %rw.if.e(f, C.M.eq(C.M.g(1n), C.M.c(0)), C.M.ev(), C.M.ret(), s0, ev.op(C.Wasm.Op.eq{}, C.M.g(1n), C.M.c(0), s0, 1, 0, h1, {==})) :
    {lhs == _ : C.Cir.Out}
  %rw.if.e(f, C.M.eq(C.M.g(2n), C.M.c(0)), C.M.out(), sel.e(C.M.ret()), s0, ev.eq0(2n, s0, h, h2, hz)) : {lhs == _ : C.Cir.Out}
  %rw.seq(f, C.M.set(9n, C.M.g(2n)), sel.b(sel.e(C.M.ret())), s0, s1, run.set(f, 9n, C.M.g(2n), s0, h, h2, hl, {==})) : {lhs == _ : C.Cir.Out}
  %rw.seq(f, C.M.set(10n, C.M.tag(C.M.g(9n))), sel.b(sel.b(sel.e(C.M.ret()))), s1, s2,
    run.set(f, 10n, C.M.tag(C.M.g(9n)), s1, T,
      ev.opw(C.Wasm.Op.and{}, C.M.f(0n, C.M.g(9n)), C.M.c(63), s1, F0, 63, T,
        ev.fld(0n, C.M.g(9n), s1, h, L.gs(regs, 9n, h, L.lt(regs, 9n, hl, {==})), hc), {==}, ht),
      L.len(regs, 9n, h, 64n, hl), {==})) : {lhs == _ : C.Cir.Out}
  %rw.seq(f, C.M.set(14n, C.M.q(C.M.g(9n))), sel.b(sel.b(sel.b(sel.e(C.M.ret())))), s2, s3,
    run.set(f, 14n, C.M.q(C.M.g(9n)), s2, U32.and(U32.shrn(F0, 6n), 3),
      ev.op(C.Wasm.Op.and{}, C.M.shr(C.M.f(0n, C.M.g(9n)), C.M.c(6)), C.M.c(3), s2, U32.shrn(F0, 6n), 3,
        ev.op(C.Wasm.Op.shr_u{}, C.M.f(0n, C.M.g(9n)), C.M.c(6), s2, F0, 6,
          ev.fld(0n, C.M.g(9n), s2, h, L.go(r1, 10n, 9n, T, h, {==}, L.gs(regs, 9n, h, L.lt(regs, 9n, hl, {==}))), hc), {==}), {==}),
      L.len(r1, 10n, T, 64n, L.len(regs, 9n, h, 64n, hl)), {==})) : {lhs == _ : C.Cir.Out}
  rw.seq_nop(f, X.chain(0n), s3)

# the test of the tag against K
def ret.ev(+K: U32, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>,
  +h: U32, +T: U32, hl: {List.length(&2, U32, regs) == 64n : Nat}) ->
  {C.Cir.eval(C.M.eq(C.M.g(10n), C.M.c(K)), ret.st(regs, m, nx, fi, im, pg, lim, inp, h, T)) == Some{C.Wasm.op(C.Wasm.Op.eq{}, T, K)} : Maybe<&2, U32>}:
  ev.op(C.Wasm.Op.eq{}, C.M.g(10n), C.M.c(K), ret.st(regs, m, nx, fi, im, pg, lim, inp, h, T), T, K,
    L.go(X.set(X.set(regs, 9n, h), 10n, T), 14n, 10n, U32.and(U32.shrn(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 6n), 3), T, {==},
      L.gs(X.set(regs, 9n, h), 10n, T, L.lt(X.set(regs, 9n, h), 10n, L.len(regs, 9n, h, 64n, hl), {==}))), {==})

# the first test: app_arg or app_val
def ret.ev0(+regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>,
  +h: U32, +T: U32, +hl: {List.length(&2, U32, regs) == 64n : Nat}) ->
  {C.Cir.eval(sel.c(X.chain(0n)), ret.st(regs, m, nx, fi, im, pg, lim, inp, h, T)) ==
    Some{C.Wasm.op(C.Wasm.Op.or{}, C.Wasm.op(C.Wasm.Op.eq{}, T, 32), C.Wasm.op(C.Wasm.Op.eq{}, T, 33))} : Maybe<&2, U32>}:
  ev.op(C.Wasm.Op.or{}, C.M.eq(C.M.g(10n), C.M.c(32)), C.M.eq(C.M.g(10n), C.M.c(33)), ret.st(regs, m, nx, fi, im, pg, lim, inp, h, T),
    C.Wasm.op(C.Wasm.Op.eq{}, T, 32), C.Wasm.op(C.Wasm.Op.eq{}, T, 33),
    ret.ev(32, regs, m, nx, fi, im, pg, lim, inp, h, T, hl), ret.ev(33, regs, m, nx, fi, im, pg, lim, inp, h, T, hl))


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
  +l = hl
  +s3 = ret.st(regs, m, nx, fi, im, pg, lim, inp, h, 32)
  +rhs = {C.Cir.exec(f, sel.t(X.chain(0n)), s3) : C.Cir.Out}
  %ret.pre(f, regs, m, nx, fi, im, pg, lim, inp, h, 32, l, h1, h2, hz, hc, ht) : {_ == rhs : C.Cir.Out}
  %rw.if.t(f, sel.c(X.chain(0n)), sel.t(X.chain(0n)), sel.e(X.chain(0n)), s3, 1, ret.ev0(regs, m, nx, fi, im, pg, lim, inp, h, 32, l), {==}) : {_ == rhs : C.Cir.Out}
  {==}

def ret.disp.val(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +h: U32, hl: {List.length(&2, U32, regs) == 64n : Nat},
  h1: {List.get(&2, U32, regs, 1n) == Some{1} : Maybe<&2, U32>}, h2: {List.get(&2, U32, regs, 2n) == Some{h} : Maybe<&2, U32>},
  hz: {U32.is_eq(h, 0) == False{} : Bool}, hc: {C.Cir.is_cell(h, im, fi, nx) == True{} : Bool},
  ht: {U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 63) == 33 : U32}) ->
  {C.Cir.exec(f, X.body(), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.exec(f, sel.t(X.chain(0n)), X.st(X.set(X.set(X.set(regs, 9n, h), 10n, 33), 14n, U32.and(U32.shrn(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 6n), 3)), m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  +l = hl
  +s3 = ret.st(regs, m, nx, fi, im, pg, lim, inp, h, 33)
  +rhs = {C.Cir.exec(f, sel.t(X.chain(0n)), s3) : C.Cir.Out}
  %ret.pre(f, regs, m, nx, fi, im, pg, lim, inp, h, 33, l, h1, h2, hz, hc, ht) : {_ == rhs : C.Cir.Out}
  %rw.if.t(f, sel.c(X.chain(0n)), sel.t(X.chain(0n)), sel.e(X.chain(0n)), s3, 1, ret.ev0(regs, m, nx, fi, im, pg, lim, inp, h, 33, l), {==}) : {_ == rhs : C.Cir.Out}
  {==}

def ret.disp.fun(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +h: U32, hl: {List.length(&2, U32, regs) == 64n : Nat},
  h1: {List.get(&2, U32, regs, 1n) == Some{1} : Maybe<&2, U32>}, h2: {List.get(&2, U32, regs, 2n) == Some{h} : Maybe<&2, U32>},
  hz: {U32.is_eq(h, 0) == False{} : Bool}, hc: {C.Cir.is_cell(h, im, fi, nx) == True{} : Bool},
  ht: {U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 63) == 34 : U32}) ->
  {C.Cir.exec(f, X.body(), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.exec(f, sel.t(X.chain(1n)), X.st(X.set(X.set(X.set(regs, 9n, h), 10n, 34), 14n, U32.and(U32.shrn(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 6n), 3)), m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  +l = hl
  +s3 = ret.st(regs, m, nx, fi, im, pg, lim, inp, h, 34)
  +rhs = {C.Cir.exec(f, sel.t(X.chain(1n)), s3) : C.Cir.Out}
  %ret.pre(f, regs, m, nx, fi, im, pg, lim, inp, h, 34, l, h1, h2, hz, hc, ht) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(0n)), sel.t(X.chain(0n)), sel.e(X.chain(0n)), s3, ret.ev0(regs, m, nx, fi, im, pg, lim, inp, h, 34, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.t(f, sel.c(X.chain(1n)), sel.t(X.chain(1n)), sel.e(X.chain(1n)), s3, 1, ret.ev(34, regs, m, nx, fi, im, pg, lim, inp, h, 34, l), {==}) : {_ == rhs : C.Cir.Out}
  {==}

def ret.disp.let(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +h: U32, hl: {List.length(&2, U32, regs) == 64n : Nat},
  h1: {List.get(&2, U32, regs, 1n) == Some{1} : Maybe<&2, U32>}, h2: {List.get(&2, U32, regs, 2n) == Some{h} : Maybe<&2, U32>},
  hz: {U32.is_eq(h, 0) == False{} : Bool}, hc: {C.Cir.is_cell(h, im, fi, nx) == True{} : Bool},
  ht: {U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 63) == 35 : U32}) ->
  {C.Cir.exec(f, X.body(), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.exec(f, sel.t(X.chain(2n)), X.st(X.set(X.set(X.set(regs, 9n, h), 10n, 35), 14n, U32.and(U32.shrn(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 6n), 3)), m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  +l = hl
  +s3 = ret.st(regs, m, nx, fi, im, pg, lim, inp, h, 35)
  +rhs = {C.Cir.exec(f, sel.t(X.chain(2n)), s3) : C.Cir.Out}
  %ret.pre(f, regs, m, nx, fi, im, pg, lim, inp, h, 35, l, h1, h2, hz, hc, ht) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(0n)), sel.t(X.chain(0n)), sel.e(X.chain(0n)), s3, ret.ev0(regs, m, nx, fi, im, pg, lim, inp, h, 35, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(1n)), sel.t(X.chain(1n)), sel.e(X.chain(1n)), s3, ret.ev(34, regs, m, nx, fi, im, pg, lim, inp, h, 35, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.t(f, sel.c(X.chain(2n)), sel.t(X.chain(2n)), sel.e(X.chain(2n)), s3, 1, ret.ev(35, regs, m, nx, fi, im, pg, lim, inp, h, 35, l), {==}) : {_ == rhs : C.Cir.Out}
  {==}

def ret.disp.tupb(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +h: U32, hl: {List.length(&2, U32, regs) == 64n : Nat},
  h1: {List.get(&2, U32, regs, 1n) == Some{1} : Maybe<&2, U32>}, h2: {List.get(&2, U32, regs, 2n) == Some{h} : Maybe<&2, U32>},
  hz: {U32.is_eq(h, 0) == False{} : Bool}, hc: {C.Cir.is_cell(h, im, fi, nx) == True{} : Bool},
  ht: {U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 63) == 36 : U32}) ->
  {C.Cir.exec(f, X.body(), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.exec(f, sel.t(X.chain(3n)), X.st(X.set(X.set(X.set(regs, 9n, h), 10n, 36), 14n, U32.and(U32.shrn(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 6n), 3)), m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  +l = hl
  +s3 = ret.st(regs, m, nx, fi, im, pg, lim, inp, h, 36)
  +rhs = {C.Cir.exec(f, sel.t(X.chain(3n)), s3) : C.Cir.Out}
  %ret.pre(f, regs, m, nx, fi, im, pg, lim, inp, h, 36, l, h1, h2, hz, hc, ht) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(0n)), sel.t(X.chain(0n)), sel.e(X.chain(0n)), s3, ret.ev0(regs, m, nx, fi, im, pg, lim, inp, h, 36, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(1n)), sel.t(X.chain(1n)), sel.e(X.chain(1n)), s3, ret.ev(34, regs, m, nx, fi, im, pg, lim, inp, h, 36, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(2n)), sel.t(X.chain(2n)), sel.e(X.chain(2n)), s3, ret.ev(35, regs, m, nx, fi, im, pg, lim, inp, h, 36, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.t(f, sel.c(X.chain(3n)), sel.t(X.chain(3n)), sel.e(X.chain(3n)), s3, 1, ret.ev(36, regs, m, nx, fi, im, pg, lim, inp, h, 36, l), {==}) : {_ == rhs : C.Cir.Out}
  {==}

def ret.disp.tupa(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +h: U32, hl: {List.length(&2, U32, regs) == 64n : Nat},
  h1: {List.get(&2, U32, regs, 1n) == Some{1} : Maybe<&2, U32>}, h2: {List.get(&2, U32, regs, 2n) == Some{h} : Maybe<&2, U32>},
  hz: {U32.is_eq(h, 0) == False{} : Bool}, hc: {C.Cir.is_cell(h, im, fi, nx) == True{} : Bool},
  ht: {U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 63) == 37 : U32}) ->
  {C.Cir.exec(f, X.body(), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.exec(f, sel.t(X.chain(4n)), X.st(X.set(X.set(X.set(regs, 9n, h), 10n, 37), 14n, U32.and(U32.shrn(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 6n), 3)), m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  +l = hl
  +s3 = ret.st(regs, m, nx, fi, im, pg, lim, inp, h, 37)
  +rhs = {C.Cir.exec(f, sel.t(X.chain(4n)), s3) : C.Cir.Out}
  %ret.pre(f, regs, m, nx, fi, im, pg, lim, inp, h, 37, l, h1, h2, hz, hc, ht) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(0n)), sel.t(X.chain(0n)), sel.e(X.chain(0n)), s3, ret.ev0(regs, m, nx, fi, im, pg, lim, inp, h, 37, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(1n)), sel.t(X.chain(1n)), sel.e(X.chain(1n)), s3, ret.ev(34, regs, m, nx, fi, im, pg, lim, inp, h, 37, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(2n)), sel.t(X.chain(2n)), sel.e(X.chain(2n)), s3, ret.ev(35, regs, m, nx, fi, im, pg, lim, inp, h, 37, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(3n)), sel.t(X.chain(3n)), sel.e(X.chain(3n)), s3, ret.ev(36, regs, m, nx, fi, im, pg, lim, inp, h, 37, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.t(f, sel.c(X.chain(4n)), sel.t(X.chain(4n)), sel.e(X.chain(4n)), s3, 1, ret.ev(37, regs, m, nx, fi, im, pg, lim, inp, h, 37, l), {==}) : {_ == rhs : C.Cir.Out}
  {==}

def ret.disp.rwt(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +h: U32, hl: {List.length(&2, U32, regs) == 64n : Nat},
  h1: {List.get(&2, U32, regs, 1n) == Some{1} : Maybe<&2, U32>}, h2: {List.get(&2, U32, regs, 2n) == Some{h} : Maybe<&2, U32>},
  hz: {U32.is_eq(h, 0) == False{} : Bool}, hc: {C.Cir.is_cell(h, im, fi, nx) == True{} : Bool},
  ht: {U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 63) == 38 : U32}) ->
  {C.Cir.exec(f, X.body(), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.exec(f, sel.t(X.chain(5n)), X.st(X.set(X.set(X.set(regs, 9n, h), 10n, 38), 14n, U32.and(U32.shrn(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 6n), 3)), m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  +l = hl
  +s3 = ret.st(regs, m, nx, fi, im, pg, lim, inp, h, 38)
  +rhs = {C.Cir.exec(f, sel.t(X.chain(5n)), s3) : C.Cir.Out}
  %ret.pre(f, regs, m, nx, fi, im, pg, lim, inp, h, 38, l, h1, h2, hz, hc, ht) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(0n)), sel.t(X.chain(0n)), sel.e(X.chain(0n)), s3, ret.ev0(regs, m, nx, fi, im, pg, lim, inp, h, 38, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(1n)), sel.t(X.chain(1n)), sel.e(X.chain(1n)), s3, ret.ev(34, regs, m, nx, fi, im, pg, lim, inp, h, 38, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(2n)), sel.t(X.chain(2n)), sel.e(X.chain(2n)), s3, ret.ev(35, regs, m, nx, fi, im, pg, lim, inp, h, 38, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(3n)), sel.t(X.chain(3n)), sel.e(X.chain(3n)), s3, ret.ev(36, regs, m, nx, fi, im, pg, lim, inp, h, 38, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(4n)), sel.t(X.chain(4n)), sel.e(X.chain(4n)), s3, ret.ev(37, regs, m, nx, fi, im, pg, lim, inp, h, 38, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.t(f, sel.c(X.chain(5n)), sel.t(X.chain(5n)), sel.e(X.chain(5n)), s3, 1, ret.ev(38, regs, m, nx, fi, im, pg, lim, inp, h, 38, l), {==}) : {_ == rhs : C.Cir.Out}
  {==}

def ret.disp.minb(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +h: U32, hl: {List.length(&2, U32, regs) == 64n : Nat},
  h1: {List.get(&2, U32, regs, 1n) == Some{1} : Maybe<&2, U32>}, h2: {List.get(&2, U32, regs, 2n) == Some{h} : Maybe<&2, U32>},
  hz: {U32.is_eq(h, 0) == False{} : Bool}, hc: {C.Cir.is_cell(h, im, fi, nx) == True{} : Bool},
  ht: {U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 63) == 39 : U32}) ->
  {C.Cir.exec(f, X.body(), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.exec(f, sel.t(X.chain(6n)), X.st(X.set(X.set(X.set(regs, 9n, h), 10n, 39), 14n, U32.and(U32.shrn(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 6n), 3)), m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  +l = hl
  +s3 = ret.st(regs, m, nx, fi, im, pg, lim, inp, h, 39)
  +rhs = {C.Cir.exec(f, sel.t(X.chain(6n)), s3) : C.Cir.Out}
  %ret.pre(f, regs, m, nx, fi, im, pg, lim, inp, h, 39, l, h1, h2, hz, hc, ht) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(0n)), sel.t(X.chain(0n)), sel.e(X.chain(0n)), s3, ret.ev0(regs, m, nx, fi, im, pg, lim, inp, h, 39, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(1n)), sel.t(X.chain(1n)), sel.e(X.chain(1n)), s3, ret.ev(34, regs, m, nx, fi, im, pg, lim, inp, h, 39, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(2n)), sel.t(X.chain(2n)), sel.e(X.chain(2n)), s3, ret.ev(35, regs, m, nx, fi, im, pg, lim, inp, h, 39, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(3n)), sel.t(X.chain(3n)), sel.e(X.chain(3n)), s3, ret.ev(36, regs, m, nx, fi, im, pg, lim, inp, h, 39, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(4n)), sel.t(X.chain(4n)), sel.e(X.chain(4n)), s3, ret.ev(37, regs, m, nx, fi, im, pg, lim, inp, h, 39, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(5n)), sel.t(X.chain(5n)), sel.e(X.chain(5n)), s3, ret.ev(38, regs, m, nx, fi, im, pg, lim, inp, h, 39, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.t(f, sel.c(X.chain(6n)), sel.t(X.chain(6n)), sel.e(X.chain(6n)), s3, 1, ret.ev(39, regs, m, nx, fi, im, pg, lim, inp, h, 39, l), {==}) : {_ == rhs : C.Cir.Out}
  {==}

def ret.disp.mina(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +h: U32, hl: {List.length(&2, U32, regs) == 64n : Nat},
  h1: {List.get(&2, U32, regs, 1n) == Some{1} : Maybe<&2, U32>}, h2: {List.get(&2, U32, regs, 2n) == Some{h} : Maybe<&2, U32>},
  hz: {U32.is_eq(h, 0) == False{} : Bool}, hc: {C.Cir.is_cell(h, im, fi, nx) == True{} : Bool},
  ht: {U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 63) == 40 : U32}) ->
  {C.Cir.exec(f, X.body(), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.exec(f, sel.e(X.chain(6n)), X.st(X.set(X.set(X.set(regs, 9n, h), 10n, 40), 14n, U32.and(U32.shrn(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, h)), 6n), 3)), m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  +l = hl
  +s3 = ret.st(regs, m, nx, fi, im, pg, lim, inp, h, 40)
  +rhs = {C.Cir.exec(f, sel.e(X.chain(6n)), s3) : C.Cir.Out}
  %ret.pre(f, regs, m, nx, fi, im, pg, lim, inp, h, 40, l, h1, h2, hz, hc, ht) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(0n)), sel.t(X.chain(0n)), sel.e(X.chain(0n)), s3, ret.ev0(regs, m, nx, fi, im, pg, lim, inp, h, 40, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(1n)), sel.t(X.chain(1n)), sel.e(X.chain(1n)), s3, ret.ev(34, regs, m, nx, fi, im, pg, lim, inp, h, 40, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(2n)), sel.t(X.chain(2n)), sel.e(X.chain(2n)), s3, ret.ev(35, regs, m, nx, fi, im, pg, lim, inp, h, 40, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(3n)), sel.t(X.chain(3n)), sel.e(X.chain(3n)), s3, ret.ev(36, regs, m, nx, fi, im, pg, lim, inp, h, 40, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(4n)), sel.t(X.chain(4n)), sel.e(X.chain(4n)), s3, ret.ev(37, regs, m, nx, fi, im, pg, lim, inp, h, 40, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(5n)), sel.t(X.chain(5n)), sel.e(X.chain(5n)), s3, ret.ev(38, regs, m, nx, fi, im, pg, lim, inp, h, 40, l)) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(X.chain(6n)), sel.t(X.chain(6n)), sel.e(X.chain(6n)), s3, ret.ev(39, regs, m, nx, fi, im, pg, lim, inp, h, 40, l)) : {_ == rhs : C.Cir.Out}
  {==}

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
  +hx = hdx
  +g9 = h9
  +l = hl
  +c = hc
  +n = C.Cir.Cell.get(2n, C.Cir.Cells.get(m, h))
  +r1 = X.set(regs, 15n, n)
  +r2 = X.set(r1, 0n, n)
  +m1 = X.put(m, 0n, h, hd)
  +m2 = X.put(m1, 2n, h, foc)
  +s0 = X.st(regs, m, nx, fi, im, pg, lim, inp)
  +s1 = X.st(r1, m, nx, fi, im, pg, lim, inp)
  +s2 = X.st(r1, m1, nx, fi, im, pg, lim, inp)
  +s3 = X.st(r1, m2, nx, fi, im, pg, lim, inp)
  +s4 = X.st(r2, m2, nx, fi, im, pg, lim, inp)
  +s5 = X.st(X.set(r2, 1n, 0), m2, nx, fi, im, pg, lim, inp)
  +b0 = C.M.swap(hx)
  +b1 = sel.b(b0)
  +b2 = sel.b(b1)
  +b3 = sel.b(b2)
  +b4 = sel.b(b3)
  +rhs = {C.Cir.Out.next{s5} : C.Cir.Out}
  %rw.seq(f, sel.a(b0), b1, s0, s1, run.set(f, 15n, C.M.f(2n, C.M.g(9n)), s0, n, ev.fld(2n, C.M.g(9n), s0, h, g9, c), l, {==})) :
    {_ == rhs : C.Cir.Out}
  %rw.seq(f, sel.a(b1), b2, s1, s2, run.store(f, 0n, C.M.g(9n), hx, s1, h, hd, L.go(regs, 15n, 9n, n, h, {==}, g9), ehd, c)) :
    {_ == rhs : C.Cir.Out}
  %rw.seq(f, sel.a(b2), b3, s2, s3,
    run.store(f, 2n, C.M.g(9n), C.M.g(0n), s2, h, foc, L.go(regs, 15n, 9n, n, h, {==}, g9), L.go(regs, 15n, 0n, n, foc, {==}, h0), c)) :
    {_ == rhs : C.Cir.Out}
  %rw.seq(f, sel.a(b3), b4, s3, s4,
    run.set(f, 0n, C.M.g(15n), s3, n, L.gs(regs, 15n, n, L.lt(regs, 15n, l, {==})), L.len(regs, 15n, n, 64n, l), {==})) :
    {_ == rhs : C.Cir.Out}
  %rw.seq(f, sel.a(b4), sel.b(b4), s4, s5,
    run.set(f, 1n, C.M.c(0), s4, 0, {==}, L.len(r1, 0n, n, 64n, L.len(regs, 15n, n, 64n, l)), {==})) :
    {_ == rhs : C.Cir.Out}
  run.nop(f, s5)

# M.pop: register fr gets the top frame sp, sp the next frame (its field 1),
# and the frame goes to the pend list (its field 1 gets pend, pend gets it)
def pop.eq(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +sp: U32, +pend: U32, hl: {List.length(&2, U32, regs) == 64n : Nat},
  h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}, hc: {C.Cir.is_cell(sp, im, fi, nx) == True{} : Bool}) ->
  {C.Cir.exec(f, C.M.pop(), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.Out.next{X.st(X.set(X.set(X.set(regs, 16n, sp), 2n, C.Cir.Cell.get(1n, C.Cir.Cells.get(m, sp))), 3n, sp), X.put(m, 1n, sp, pend), nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  +l = hl
  +c = hc
  +w = C.Cir.Cell.get(1n, C.Cir.Cells.get(m, sp))
  +r1 = X.set(regs, 16n, sp)
  +r2 = X.set(r1, 2n, w)
  +m1 = X.put(m, 1n, sp, pend)
  +s0 = X.st(regs, m, nx, fi, im, pg, lim, inp)
  +s1 = X.st(r1, m, nx, fi, im, pg, lim, inp)
  +s2 = X.st(r2, m, nx, fi, im, pg, lim, inp)
  +s3 = X.st(r2, m1, nx, fi, im, pg, lim, inp)
  +s4 = X.st(X.set(r2, 3n, sp), m1, nx, fi, im, pg, lim, inp)
  +b0 = C.M.pop()
  +b1 = sel.b(b0)
  +rl = C.M.release(16n)
  +rhs = {C.Cir.Out.next{s4} : C.Cir.Out}
  %rw.seq(f, sel.a(b0), b1, s0, s1, run.set(f, 16n, C.M.g(2n), s0, sp, h2, l, {==})) : {_ == rhs : C.Cir.Out}
  %rw.seq(f, sel.a(b1), sel.b(b1), s1, s2,
    run.set(f, 2n, C.M.f(1n, C.M.g(16n)), s1, w, ev.fld(1n, C.M.g(16n), s1, sp, L.gs(regs, 16n, sp, L.lt(regs, 16n, l, {==})), c),
      L.len(regs, 16n, sp, 64n, l), {==})) : {_ == rhs : C.Cir.Out}
  %rw.seq_nop(f, rl, s2) : {_ == rhs : C.Cir.Out}
  %rw.seq(f, sel.a(rl), sel.b(rl), s2, s3,
    run.store(f, 1n, C.M.g(16n), C.M.g(3n), s2, sp, pend, L.go(r1, 2n, 16n, w, sp, {==}, L.gs(regs, 16n, sp, L.lt(regs, 16n, l, {==}))),
      L.go(r1, 2n, 3n, w, pend, {==}, L.go(regs, 16n, 3n, sp, pend, {==}, h3)), c)) : {_ == rhs : C.Cir.Out}
  %rw.seq(f, sel.a(sel.b(rl)), sel.b(sel.b(rl)), s3, s4,
    run.set(f, 3n, C.M.g(16n), s3, sp, L.go(r1, 2n, 16n, w, sp, {==}, L.gs(regs, 16n, sp, L.lt(regs, 16n, l, {==}))),
      L.len(r1, 2n, w, 64n, L.len(regs, 16n, sp, 64n, l)), {==})) : {_ == rhs : C.Cir.Out}
  run.nop(f, s4)

# Counts
# ------

# M.inc(r) of the cell c: nothing for 0 or a STATIC cell; else its count
# gains 1
def inc.eq.z(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, hr: {List.get(&2, U32, regs, r) == Some{0} : Maybe<&2, U32>}) ->
  {C.Cir.exec(f, C.M.inc(r), X.st(regs, m, nx, fi, im, pg, lim, inp)) == C.Cir.Out.next{X.st(regs, m, nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  +s0 = X.st(regs, m, nx, fi, im, pg, lim, inp)

  +i = C.M.inc(r)
  +rhs = {C.Cir.Out.next{s0} : C.Cir.Out}
  %rw.if.e(f, sel.c(i), sel.t(i), sel.e(i), s0, ev.op(C.Wasm.Op.ne{}, C.M.g(r), C.M.c(0), s0, 0, 0, hr, {==})) : {_ == rhs : C.Cir.Out}
  run.nop(f, s0)

def inc.eq.s(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, +c: U32, hr: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>}, hz: {U32.is_eq(c, 0) == False{} : Bool},
  hc: {C.Cir.is_cell(c, im, fi, nx) == True{} : Bool}, hs: {U32.is_ne(U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), 1024), 0) == True{} : Bool}) ->
  {C.Cir.exec(f, C.M.inc(r), X.st(regs, m, nx, fi, im, pg, lim, inp)) == C.Cir.Out.next{X.st(regs, m, nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  +s0 = X.st(regs, m, nx, fi, im, pg, lim, inp)

  +g = hr
  +i = C.M.inc(r)
  +j = sel.t(i)
  +rhs = {C.Cir.Out.next{s0} : C.Cir.Out}
  %rw.if.t(f, sel.c(i), j, sel.e(i), s0, 1, ev.ne0(r, s0, c, g, hz), {==}) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(j), sel.t(j), sel.e(j), s0, ev.notflag(r, s0, c, 1024, True{}, g, hc, hs)) : {_ == rhs : C.Cir.Out}
  run.nop(f, s0)

def inc.eq.n(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, +c: U32, hr: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>}, hz: {U32.is_eq(c, 0) == False{} : Bool},
  hc: {C.Cir.is_cell(c, im, fi, nx) == True{} : Bool}, hs: {U32.is_ne(U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), 1024), 0) == False{} : Bool}) ->
  {C.Cir.exec(f, C.M.inc(r), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.Out.next{X.st(regs, X.put(m, 1n, c, U32.add(C.Cir.Cell.get(1n, C.Cir.Cells.get(m, c)), 1)), nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  +s0 = X.st(regs, m, nx, fi, im, pg, lim, inp)

  +g = hr
  +cc = hc
  +i = C.M.inc(r)
  +j = sel.t(i)
  +f1 = C.Cir.Cell.get(1n, C.Cir.Cells.get(m, c))
  +rhs = {C.Cir.Out.next{X.st(regs, X.put(m, 1n, c, U32.add(f1, 1)), nx, fi, im, pg, lim, inp)} : C.Cir.Out}
  %rw.if.t(f, sel.c(i), j, sel.e(i), s0, 1, ev.ne0(r, s0, c, g, hz), {==}) : {_ == rhs : C.Cir.Out}
  %rw.if.t(f, sel.c(j), sel.t(j), sel.e(j), s0, 1, ev.notflag(r, s0, c, 1024, False{}, g, cc, hs), {==}) : {_ == rhs : C.Cir.Out}
  run.store(f, 1n, C.M.g(r), C.M.add(C.M.f(1n, C.M.g(r)), C.M.c(1)), s0, c, U32.add(f1, 1), g,
    ev.op(C.Wasm.Op.add{}, C.M.f(1n, C.M.g(r)), C.M.c(1), s0, f1, 1, ev.fld(1n, C.M.g(r), s0, c, g, cc), {==}), cc)

# M.dec(r) of the cell c: nothing for 0 or a STATIC cell; else register dr and
# its count get d, its count less 1; at 0 its field 1 gets pend and pend gets c
def dec.eq.z(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, hr: {List.get(&2, U32, regs, r) == Some{0} : Maybe<&2, U32>}) ->
  {C.Cir.exec(f, C.M.dec(r), X.st(regs, m, nx, fi, im, pg, lim, inp)) == C.Cir.Out.next{X.st(regs, m, nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  +s0 = X.st(regs, m, nx, fi, im, pg, lim, inp)

  +i = C.M.dec(r)
  +rhs = {C.Cir.Out.next{s0} : C.Cir.Out}
  %rw.if.e(f, sel.c(i), sel.t(i), sel.e(i), s0, ev.op(C.Wasm.Op.ne{}, C.M.g(r), C.M.c(0), s0, 0, 0, hr, {==})) : {_ == rhs : C.Cir.Out}
  run.nop(f, s0)

def dec.eq.s(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, +c: U32, hr: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>}, hz: {U32.is_eq(c, 0) == False{} : Bool},
  hc: {C.Cir.is_cell(c, im, fi, nx) == True{} : Bool}, hs: {U32.is_ne(U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), 1024), 0) == True{} : Bool}) ->
  {C.Cir.exec(f, C.M.dec(r), X.st(regs, m, nx, fi, im, pg, lim, inp)) == C.Cir.Out.next{X.st(regs, m, nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  +s0 = X.st(regs, m, nx, fi, im, pg, lim, inp)

  +g = hr
  +i = C.M.dec(r)
  +j = sel.t(i)
  +rhs = {C.Cir.Out.next{s0} : C.Cir.Out}
  %rw.if.t(f, sel.c(i), j, sel.e(i), s0, 1, ev.ne0(r, s0, c, g, hz), {==}) : {_ == rhs : C.Cir.Out}
  %rw.if.e(f, sel.c(j), sel.t(j), sel.e(j), s0, ev.notflag(r, s0, c, 1024, True{}, g, hc, hs)) : {_ == rhs : C.Cir.Out}
  run.nop(f, s0)

def dec.eq.n(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, +c: U32, hl: {List.length(&2, U32, regs) == 64n : Nat}, hr: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>}, hz: {U32.is_eq(c, 0) == False{} : Bool},
  hc: {C.Cir.is_cell(c, im, fi, nx) == True{} : Bool}, hs: {U32.is_ne(U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), 1024), 0) == False{} : Bool},
  hd: {U32.is_eq(U32.sub(C.Cir.Cell.get(1n, C.Cir.Cells.get(m, c)), 1), 0) == False{} : Bool}, h5: {Nat.is_eq(5n, r) == False{} : Bool}) ->
  {C.Cir.exec(f, C.M.dec(r), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.Out.next{X.st(X.set(regs, 5n, U32.sub(C.Cir.Cell.get(1n, C.Cir.Cells.get(m, c)), 1)), X.put(m, 1n, c, U32.sub(C.Cir.Cell.get(1n, C.Cir.Cells.get(m, c)), 1)), nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  +s0 = X.st(regs, m, nx, fi, im, pg, lim, inp)

  +g = hr
  +cc = hc
  +l = hl
  +n5 = h5
  +i = C.M.dec(r)
  +j = sel.t(i)
  +b0 = sel.t(j)
  +w = sel.a(sel.b(sel.b(b0)))
  +f1 = C.Cir.Cell.get(1n, C.Cir.Cells.get(m, c))
  +d = U32.sub(f1, 1)
  +r1 = X.set(regs, 5n, d)
  +m1 = X.put(m, 1n, c, d)
  +s1 = X.st(r1, m, nx, fi, im, pg, lim, inp)
  +s2 = X.st(r1, m1, nx, fi, im, pg, lim, inp)
  +rhs = {C.Cir.Out.next{s2} : C.Cir.Out}
  %rw.if.t(f, sel.c(i), j, sel.e(i), s0, 1, ev.ne0(r, s0, c, g, hz), {==}) : {_ == rhs : C.Cir.Out}
  %rw.if.t(f, sel.c(j), b0, sel.e(j), s0, 1, ev.notflag(r, s0, c, 1024, False{}, g, cc, hs), {==}) : {_ == rhs : C.Cir.Out}
  %rw.seq(f, sel.a(b0), sel.b(b0), s0, s1,
    run.set(f, 5n, C.M.sub(C.M.f(1n, C.M.g(r)), C.M.c(1)), s0, d,
      ev.op(C.Wasm.Op.sub{}, C.M.f(1n, C.M.g(r)), C.M.c(1), s0, f1, 1, ev.fld(1n, C.M.g(r), s0, c, g, cc), {==}), l, {==})) :
    {_ == rhs : C.Cir.Out}
  %rw.seq(f, sel.a(sel.b(b0)), sel.b(sel.b(b0)), s1, s2,
    run.store(f, 1n, C.M.g(r), C.M.g(5n), s1, c, d, L.go(regs, 5n, r, d, c, n5, g), L.gs(regs, 5n, d, L.lt(regs, 5n, l, {==})), cc)) :
    {_ == rhs : C.Cir.Out}
  %rw.seq_nop(f, w, s2) : {_ == rhs : C.Cir.Out}

  %rw.if.e(f, sel.c(w), sel.t(w), sel.e(w), s2, ev.eq0(5n, s2, d, L.gs(regs, 5n, d, L.lt(regs, 5n, l, {==})), hd)) : {_ == rhs : C.Cir.Out}
  run.nop(f, s2)

def dec.eq.p(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, +c: U32, +pend: U32, hl: {List.length(&2, U32, regs) == 64n : Nat}, hr: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>}, h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  hz: {U32.is_eq(c, 0) == False{} : Bool}, hc: {C.Cir.is_cell(c, im, fi, nx) == True{} : Bool},
  hs: {U32.is_ne(U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), 1024), 0) == False{} : Bool},
  hd: {U32.is_eq(U32.sub(C.Cir.Cell.get(1n, C.Cir.Cells.get(m, c)), 1), 0) == True{} : Bool}, h5: {Nat.is_eq(5n, r) == False{} : Bool}) ->
  {C.Cir.exec(f, C.M.dec(r), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.Out.next{X.st(X.set(X.set(regs, 5n, U32.sub(C.Cir.Cell.get(1n, C.Cir.Cells.get(m, c)), 1)), 3n, c), X.put(X.put(m, 1n, c, U32.sub(C.Cir.Cell.get(1n, C.Cir.Cells.get(m, c)), 1)), 1n, c, pend), nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  +s0 = X.st(regs, m, nx, fi, im, pg, lim, inp)

  +g = hr
  +cc = hc
  +l = hl
  +n5 = h5
  +i = C.M.dec(r)
  +j = sel.t(i)
  +b0 = sel.t(j)
  +w = sel.a(sel.b(sel.b(b0)))
  +f1 = C.Cir.Cell.get(1n, C.Cir.Cells.get(m, c))
  +d = U32.sub(f1, 1)
  +r1 = X.set(regs, 5n, d)
  +m1 = X.put(m, 1n, c, d)
  +s1 = X.st(r1, m, nx, fi, im, pg, lim, inp)
  +s2 = X.st(r1, m1, nx, fi, im, pg, lim, inp)
  +m2 = X.put(m1, 1n, c, pend)
  +s3 = X.st(r1, m2, nx, fi, im, pg, lim, inp)
  +s4 = X.st(X.set(r1, 3n, c), m2, nx, fi, im, pg, lim, inp)
  +t = sel.t(w)
  +rhs = {C.Cir.Out.next{s4} : C.Cir.Out}
  %rw.if.t(f, sel.c(i), j, sel.e(i), s0, 1, ev.ne0(r, s0, c, g, hz), {==}) : {_ == rhs : C.Cir.Out}
  %rw.if.t(f, sel.c(j), b0, sel.e(j), s0, 1, ev.notflag(r, s0, c, 1024, False{}, g, cc, hs), {==}) : {_ == rhs : C.Cir.Out}
  %rw.seq(f, sel.a(b0), sel.b(b0), s0, s1,
    run.set(f, 5n, C.M.sub(C.M.f(1n, C.M.g(r)), C.M.c(1)), s0, d,
      ev.op(C.Wasm.Op.sub{}, C.M.f(1n, C.M.g(r)), C.M.c(1), s0, f1, 1, ev.fld(1n, C.M.g(r), s0, c, g, cc), {==}), l, {==})) :
    {_ == rhs : C.Cir.Out}
  %rw.seq(f, sel.a(sel.b(b0)), sel.b(sel.b(b0)), s1, s2,
    run.store(f, 1n, C.M.g(r), C.M.g(5n), s1, c, d, L.go(regs, 5n, r, d, c, n5, g), L.gs(regs, 5n, d, L.lt(regs, 5n, l, {==})), cc)) :
    {_ == rhs : C.Cir.Out}
  %rw.seq_nop(f, w, s2) : {_ == rhs : C.Cir.Out}

  %rw.if.t(f, sel.c(w), t, sel.e(w), s2, 1,
    ev.opw(C.Wasm.Op.eq{}, C.M.g(5n), C.M.c(0), s2, d, 0, 1, L.gs(regs, 5n, d, L.lt(regs, 5n, l, {==})), {==},
      Equal.cong(Bool, U32, x => Bool.to_u32(x), U32.is_eq(d, 0), True{}, hd)), {==}) : {_ == rhs : C.Cir.Out}
  %rw.seq(f, sel.a(t), sel.b(t), s2, s3,
    run.store(f, 1n, C.M.g(r), C.M.g(3n), s2, c, pend, L.go(regs, 5n, r, d, c, n5, g), L.go(regs, 5n, 3n, d, pend, {==}, h3), cc)) :
    {_ == rhs : C.Cir.Out}
  %rw.seq(f, sel.a(sel.b(t)), sel.b(sel.b(t)), s3, s4,
    run.set(f, 3n, C.M.g(r), s3, c, L.go(regs, 5n, r, d, c, n5, g), L.len(regs, 5n, d, 64n, l), {==})) : {_ == rhs : C.Cir.Out}
  run.nop(f, s4)

# Allocation
# ----------

# M.alloc(r) with an empty pend list: Cir's alloc
def alloc.eq.fresh(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, h3: {List.get(&2, U32, regs, 3n) == Some{0} : Maybe<&2, U32>}) ->
  {C.Cir.exec(f, C.M.alloc(r), X.st(regs, m, nx, fi, im, pg, lim, inp)) == C.Cir.exec.alloc(r, X.st(regs, m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  +s0 = X.st(regs, m, nx, fi, im, pg, lim, inp)

  +a = C.M.alloc(r)
  +rhs = {C.Cir.exec.alloc(r, s0) : C.Cir.Out}
  %rw.if.e(f, sel.c(a), sel.t(a), sel.e(a), s0, ev.op(C.Wasm.Op.ne{}, C.M.g(3n), C.M.c(0), s0, 0, 0, h3, {==})) : {_ == rhs : C.Cir.Out}
  run.alloc(f, r, s0)

# M.alloc(r) from the pend list's first cell p: aq gets p, pend its field 1,
# am its tag's mask (a term cell, by the table's cell 345 + tag) or 0 (a cell
# of the machine's own kinds); then the rest of M.alloc (its parts lose a
# pointer, it is set to zeros, r gets it)
def alloc.eq.term(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, +p: U32, hl: {List.length(&2, U32, regs) == 64n : Nat}, h3: {List.get(&2, U32, regs, 3n) == Some{p} : Maybe<&2, U32>}, hz: {U32.is_eq(p, 0) == False{} : Bool},
  hc: {C.Cir.is_cell(p, im, fi, nx) == True{} : Bool}, ht: {U32.is_lt(U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, p)), 63), 32) == True{} : Bool},
  hm: {C.Cir.is_cell(U32.add(345, U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, p)), 63)), im, fi, nx) == True{} : Bool}) ->
  {C.Cir.exec(f, C.M.alloc(r), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.exec(f, sel.b(sel.b(sel.b(sel.t(C.M.alloc(r))))), X.st(X.set(X.set(X.set(regs, 6n, p), 3n, C.Cir.Cell.get(1n, C.Cir.Cells.get(m, p))), 7n, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, U32.add(345, U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, p)), 63))))), m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  +s0 = X.st(regs, m, nx, fi, im, pg, lim, inp)

  +l = hl
  +g3 = h3
  +c = hc
  +f0 = C.Cir.Cell.get(0n, C.Cir.Cells.get(m, p))
  +f1 = C.Cir.Cell.get(1n, C.Cir.Cells.get(m, p))
  +tg = U32.and(f0, 63)
  +r1 = X.set(regs, 6n, p)
  +r2 = X.set(r1, 3n, f1)
  +s1 = X.st(r1, m, nx, fi, im, pg, lim, inp)
  +s2 = X.st(r2, m, nx, fi, im, pg, lim, inp)
  +a = C.M.alloc(r)
  +b0 = sel.t(a)
  +b2 = sel.b(sel.b(b0))
  +w = sel.a(b2)
  +am = C.Cir.Cell.get(2n, C.Cir.Cells.get(m, U32.add(345, tg)))
  +s3 = X.st(X.set(r2, 7n, am), m, nx, fi, im, pg, lim, inp)
  +rhs = {C.Cir.exec(f, sel.b(b2), s3) : C.Cir.Out}
  %rw.if.t(f, sel.c(a), b0, sel.e(a), s0, 1, ev.ne0(3n, s0, p, g3, hz), {==}) : {_ == rhs : C.Cir.Out}
  %rw.seq(f, sel.a(b0), sel.b(b0), s0, s1, run.set(f, 6n, C.M.g(3n), s0, p, g3, l, {==})) : {_ == rhs : C.Cir.Out}
  %rw.seq(f, sel.a(sel.b(b0)), b2, s1, s2,
    run.set(f, 3n, C.M.f(1n, C.M.g(6n)), s1, f1, ev.fld(1n, C.M.g(6n), s1, p, L.gs(regs, 6n, p, L.lt(regs, 6n, l, {==})), c),
      L.len(regs, 6n, p, 64n, l), {==})) : {_ == rhs : C.Cir.Out}

  +etg = ev.op(C.Wasm.Op.and{}, C.M.f(0n, C.M.g(6n)), C.M.c(63), s2, f0, 63,
        ev.fld(0n, C.M.g(6n), s2, p, L.go(r1, 3n, 6n, f1, p, {==}, L.gs(regs, 6n, p, L.lt(regs, 6n, l, {==}))), c), {==})
  %rw.seq(f, w, sel.b(b2), s2, s3,
    run.if.t(f, sel.c(w), sel.t(w), sel.e(w), s2, 1,
      ev.opw(C.Wasm.Op.lt_u{}, C.M.tag(C.M.g(6n)), C.M.c(32), s2, tg, 32, 1, etg, {==},
        Equal.cong(Bool, U32, x => Bool.to_u32(x), U32.is_lt(tg, 32), True{}, ht)), {==}, C.Cir.Out.next{s3},
      run.set(f, 7n, C.M.entry(2n, C.M.g(6n)), s2, am,
        ev.fld(2n, C.M.add(C.M.c(C.I.table()), C.M.tag(C.M.g(6n))), s2, U32.add(345, tg),
          ev.op(C.Wasm.Op.add{}, C.M.c(C.I.table()), C.M.tag(C.M.g(6n)), s2, 345, tg, {==}, etg), hm),
        L.len(r1, 3n, f1, 64n, L.len(regs, 6n, p, 64n, l)), {==}))) : {_ == rhs : C.Cir.Out}
  {==}

def alloc.eq.own(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, +p: U32, hl: {List.length(&2, U32, regs) == 64n : Nat}, h3: {List.get(&2, U32, regs, 3n) == Some{p} : Maybe<&2, U32>}, hz: {U32.is_eq(p, 0) == False{} : Bool},
  hc: {C.Cir.is_cell(p, im, fi, nx) == True{} : Bool}, ht: {U32.is_lt(U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, p)), 63), 32) == False{} : Bool}) ->
  {C.Cir.exec(f, C.M.alloc(r), X.st(regs, m, nx, fi, im, pg, lim, inp)) == C.Cir.exec(f, sel.b(sel.b(sel.b(sel.t(C.M.alloc(r))))), X.st(X.set(X.set(X.set(regs, 6n, p), 3n, C.Cir.Cell.get(1n, C.Cir.Cells.get(m, p))), 7n, 0), m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  +s0 = X.st(regs, m, nx, fi, im, pg, lim, inp)

  +l = hl
  +g3 = h3
  +c = hc
  +f0 = C.Cir.Cell.get(0n, C.Cir.Cells.get(m, p))
  +f1 = C.Cir.Cell.get(1n, C.Cir.Cells.get(m, p))
  +tg = U32.and(f0, 63)
  +r1 = X.set(regs, 6n, p)
  +r2 = X.set(r1, 3n, f1)
  +s1 = X.st(r1, m, nx, fi, im, pg, lim, inp)
  +s2 = X.st(r2, m, nx, fi, im, pg, lim, inp)
  +a = C.M.alloc(r)
  +b0 = sel.t(a)
  +b2 = sel.b(sel.b(b0))
  +w = sel.a(b2)
  +s3 = X.st(X.set(r2, 7n, 0), m, nx, fi, im, pg, lim, inp)
  +rhs = {C.Cir.exec(f, sel.b(b2), s3) : C.Cir.Out}
  %rw.if.t(f, sel.c(a), b0, sel.e(a), s0, 1, ev.ne0(3n, s0, p, g3, hz), {==}) : {_ == rhs : C.Cir.Out}
  %rw.seq(f, sel.a(b0), sel.b(b0), s0, s1, run.set(f, 6n, C.M.g(3n), s0, p, g3, l, {==})) : {_ == rhs : C.Cir.Out}
  %rw.seq(f, sel.a(sel.b(b0)), b2, s1, s2,
    run.set(f, 3n, C.M.f(1n, C.M.g(6n)), s1, f1, ev.fld(1n, C.M.g(6n), s1, p, L.gs(regs, 6n, p, L.lt(regs, 6n, l, {==})), c),
      L.len(regs, 6n, p, 64n, l), {==})) : {_ == rhs : C.Cir.Out}

  %rw.seq(f, w, sel.b(b2), s2, s3,
    run.if.e(f, sel.c(w), sel.t(w), sel.e(w), s2,
      ev.opw(C.Wasm.Op.lt_u{}, C.M.tag(C.M.g(6n)), C.M.c(32), s2, tg, 32, 0, ev.op(C.Wasm.Op.and{}, C.M.f(0n, C.M.g(6n)), C.M.c(63), s2, f0, 63,
        ev.fld(0n, C.M.g(6n), s2, p, L.go(r1, 3n, 6n, f1, p, {==}, L.gs(regs, 6n, p, L.lt(regs, 6n, l, {==}))), c), {==}), {==},
        Equal.cong(Bool, U32, x => Bool.to_u32(x), U32.is_lt(tg, 32), False{}, ht)), C.Cir.Out.next{s3},
      run.set(f, 7n, C.M.c(0), s2, 0, {==}, L.len(r1, 3n, f1, 64n, L.len(regs, 6n, p, 64n, l)), {==}))) : {_ == rhs : C.Cir.Out}
  {==}

# a part of the cell aq loses a pointer (M.dec.part), when the mask am names
# it: register dx gets it, then M.dec(dx); else nothing
def dec.part.off(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +k: Nat, +bit: U32, +am: U32, h7: {List.get(&2, U32, regs, 7n) == Some{am} : Maybe<&2, U32>},
  hb: {U32.is_eq(U32.and(am, bit), 0) == True{} : Bool}) ->
  {C.Cir.exec(f, C.M.dec.part(k, bit), X.st(regs, m, nx, fi, im, pg, lim, inp)) == C.Cir.Out.next{X.st(regs, m, nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  +s0 = X.st(regs, m, nx, fi, im, pg, lim, inp)

  +dp = C.M.dec.part(k, bit)
  +rhs = {C.Cir.Out.next{s0} : C.Cir.Out}
  %rw.if.e(f, sel.c(dp), sel.t(dp), sel.e(dp), s0,
    ev.opw(C.Wasm.Op.ne{}, C.M.and(C.M.g(7n), C.M.c(bit)), C.M.c(0), s0, U32.and(am, bit), 0, 0,
      ev.op(C.Wasm.Op.and{}, C.M.g(7n), C.M.c(bit), s0, am, bit, h7, {==}), {==},
      Equal.cong(Bool, U32, x => Bool.to_u32(Bool.not(x)), U32.is_eq(U32.and(am, bit), 0), True{}, hb))) : {_ == rhs : C.Cir.Out}
  run.nop(f, s0)

def dec.part.on(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +k: Nat, +bit: U32, +am: U32, +aq: U32, hl: {List.length(&2, U32, regs) == 64n : Nat}, h6: {List.get(&2, U32, regs, 6n) == Some{aq} : Maybe<&2, U32>}, h7: {List.get(&2, U32, regs, 7n) == Some{am} : Maybe<&2, U32>},
  hb: {U32.is_eq(U32.and(am, bit), 0) == False{} : Bool}, hc: {C.Cir.is_cell(aq, im, fi, nx) == True{} : Bool}) ->
  {C.Cir.exec(f, C.M.dec.part(k, bit), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.exec(f, C.M.dec(C.R.dx()), X.st(X.set(regs, 4n, C.Cir.Cell.get(k, C.Cir.Cells.get(m, aq))), m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  +s0 = X.st(regs, m, nx, fi, im, pg, lim, inp)

  +s1 = X.st(X.set(regs, 4n, C.Cir.Cell.get(k, C.Cir.Cells.get(m, aq))), m, nx, fi, im, pg, lim, inp)
  +dp = C.M.dec.part(k, bit)
  +t = sel.t(dp)
  +rhs = {C.Cir.exec(f, C.M.dec(C.R.dx()), s1) : C.Cir.Out}
  %rw.if.t(f, sel.c(dp), t, sel.e(dp), s0, 1,
    ev.opw(C.Wasm.Op.ne{}, C.M.and(C.M.g(7n), C.M.c(bit)), C.M.c(0), s0, U32.and(am, bit), 0, 1,
      ev.op(C.Wasm.Op.and{}, C.M.g(7n), C.M.c(bit), s0, am, bit, h7, {==}), {==},
      Equal.cong(Bool, U32, x => Bool.to_u32(Bool.not(x)), U32.is_eq(U32.and(am, bit), 0), False{}, hb)), {==}) : {_ == rhs : C.Cir.Out}
  %rw.seq(f, sel.a(t), sel.b(t), s0, s1,
    run.set(f, 4n, C.M.f(k, C.M.g(6n)), s0, C.Cir.Cell.get(k, C.Cir.Cells.get(m, aq)), ev.fld(k, C.M.g(6n), s0, aq, h6, hc), hl, {==})) :
    {_ == rhs : C.Cir.Out}
  %rw.seq_nop(f, C.M.dec(C.R.dx()), s1) : {_ == rhs : C.Cir.Out}
  {==}

# M.alloc's end: the cell aq is set to zeros and r gets it
def alloc.eq.end(+f: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, +aq: U32, hl: {List.length(&2, U32, regs) == 64n : Nat}, h6: {List.get(&2, U32, regs, 6n) == Some{aq} : Maybe<&2, U32>}, hc: {C.Cir.is_cell(aq, im, fi, nx) == True{} : Bool},
  hr: {Nat.is_lt(r, 64n) == True{} : Bool}) ->
  {C.Cir.exec(f, sel.b(sel.b(sel.b(sel.b(sel.b(sel.b(sel.t(C.M.alloc(r)))))))), X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.Out.next{X.st(X.set(regs, r, aq), C.Cir.Cells.set(m, aq, C.Cir.Cell.zero()), nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  +g6 = h6
  +c = hc
  +m1 = X.put(m, 0n, aq, 0)
  +m2 = X.put(m1, 1n, aq, 0)
  +m3 = X.put(m2, 2n, aq, 0)
  +m4 = X.put(m3, 3n, aq, 0)
  +m5 = X.put(m4, 4n, aq, 0)
  +s0 = X.st(regs, m, nx, fi, im, pg, lim, inp)
  +s1 = X.st(regs, m1, nx, fi, im, pg, lim, inp)
  +s2 = X.st(regs, m2, nx, fi, im, pg, lim, inp)
  +s3 = X.st(regs, m3, nx, fi, im, pg, lim, inp)
  +s4 = X.st(regs, m4, nx, fi, im, pg, lim, inp)
  +s5 = X.st(regs, m5, nx, fi, im, pg, lim, inp)
  +s6 = X.st(X.set(regs, r, aq), m5, nx, fi, im, pg, lim, inp)
  +b0 = sel.b(sel.b(sel.b(sel.b(sel.b(sel.b(sel.t(C.M.alloc(r))))))))
  +b1 = sel.b(b0)
  +b2 = sel.b(b1)
  +b3 = sel.b(b2)
  +b4 = sel.b(b3)
  +b5 = sel.b(b4)
  +rhs = {C.Cir.Out.next{s6} : C.Cir.Out}
  %Equal.sym(C.Cir.Cells, C.Cir.Cells.set(m, aq, C.Cir.Cell.zero()), m5, Ce.put5(m, aq)) :
    {C.Cir.exec(f, b0, s0) == C.Cir.Out.next{X.st(X.set(regs, r, aq), _, nx, fi, im, pg, lim, inp)} : C.Cir.Out}
  %rw.seq(f, sel.a(b0), b1, s0, s1, run.store(f, 0n, C.M.g(6n), C.M.c(0), s0, aq, 0, g6, {==}, c)) : {_ == rhs : C.Cir.Out}
  %rw.seq(f, sel.a(b1), b2, s1, s2, run.store(f, 1n, C.M.g(6n), C.M.c(0), s1, aq, 0, g6, {==}, c)) : {_ == rhs : C.Cir.Out}
  %rw.seq(f, sel.a(b2), b3, s2, s3, run.store(f, 2n, C.M.g(6n), C.M.c(0), s2, aq, 0, g6, {==}, c)) : {_ == rhs : C.Cir.Out}
  %rw.seq(f, sel.a(b3), b4, s3, s4, run.store(f, 3n, C.M.g(6n), C.M.c(0), s3, aq, 0, g6, {==}, c)) : {_ == rhs : C.Cir.Out}
  %rw.seq(f, sel.a(b4), b5, s4, s5, run.store(f, 4n, C.M.g(6n), C.M.c(0), s4, aq, 0, g6, {==}, c)) : {_ == rhs : C.Cir.Out}
  %rw.seq(f, sel.a(b5), sel.b(b5), s5, s6, run.set(f, r, C.M.g(6n), s5, aq, g6, hl, hr)) : {_ == rhs : C.Cir.Out}
  run.nop(f, s6)

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
  match st1:
    case C.Cir.State{+regs1, +m1, +nx1, +fi1, +im1, +pg1, +lim1, +inp1, +out1, +outn1}:
      +g = ez
      +hh = h
      +aa = a
      +bb = b
      +cx = c
      +t0 = {C.Cir.State{regs1, m1, nx1, fi1, im1, pg1, lim1, inp1, out1, outn1} : C.Cir.State}
      +hc = k.cell_of(r, regs1, m1, nx1, fi1, im1, pg1, lim1, inp1, out1, outn1, z, C.Cir.Cell.get(0n, C.Cir.Cells.get(m1, z)), g, hz)
      +t1 = X.store(t0, 0n, z, hv)
      +t2 = X.store(t1, 1n, z, 1)
      +t3 = X.store(t2, 2n, z, av)
      +t4 = X.store(t3, 3n, z, bv)
      +t5 = X.store(t4, 4n, z, cv)
      +q1 = sel.b(C.M.make(r, hh, aa, bb, cx))
      +q2 = sel.b(q1)
      +q3 = sel.b(q2)
      +q4 = sel.b(q3)
      +q5 = sel.b(q4)
      +rhs = {C.Cir.Out.next{t5} : C.Cir.Out}
      %rw.seq(f, C.M.alloc(r), q1, st, t0, e1) : {_ == rhs : C.Cir.Out}
      %rw.seq(f, sel.a(q1), q2, t0, t1, run.store(f, 0n, C.M.g(r), hh, t0, z, hv, g, eh, hc)) : {_ == rhs : C.Cir.Out}
      %rw.seq(f, sel.a(q2), q3, t1, t2, run.store(f, 1n, C.M.g(r), C.M.c(1), t1, z, 1, g, {==}, hc)) : {_ == rhs : C.Cir.Out}
      %rw.seq(f, sel.a(q3), q4, t2, t3, run.store(f, 2n, C.M.g(r), aa, t2, z, av, g, ea, hc)) : {_ == rhs : C.Cir.Out}
      %rw.seq(f, sel.a(q4), q5, t3, t4, run.store(f, 3n, C.M.g(r), bb, t3, z, bv, g, eb, hc)) : {_ == rhs : C.Cir.Out}
      %rw.seq(f, sel.a(q5), sel.b(q5), t4, t5, run.store(f, 4n, C.M.g(r), cx, t4, z, cv, g, ec, hc)) : {_ == rhs : C.Cir.Out}
      run.nop(f, t5)

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
  match st1:
    case C.Cir.State{+regs1, +m1, +nx1, +fi1, +im1, +pg1, +lim1, +inp1, +out1, +outn1}:
      +g = ez
      +hh = h
      +aa = a
      +bb = b
      +t0 = {C.Cir.State{regs1, m1, nx1, fi1, im1, pg1, lim1, inp1, out1, outn1} : C.Cir.State}
      +hc = k.cell_of(16n, regs1, m1, nx1, fi1, im1, pg1, lim1, inp1, out1, outn1, z, C.Cir.Cell.get(0n, C.Cir.Cells.get(m1, z)), g, hz)
      +t1 = X.store(t0, 0n, z, hv)
      +t2 = X.store(t1, 1n, z, sp)
      +t3 = X.store(t2, 2n, z, av)
      +t4 = X.store(t3, 3n, z, bv)
      +t5 = X.setst(t4, 2n, z)
      +q1 = sel.b(C.M.push(hh, aa, bb))
      +q2 = sel.b(q1)
      +q3 = sel.b(q2)
      +q4 = sel.b(q3)
      +q5 = sel.b(q4)
      +rhs = {C.Cir.Out.next{t5} : C.Cir.Out}
      %rw.seq(f, C.M.alloc(C.R.fr()), q1, st, t0, e1) : {_ == rhs : C.Cir.Out}
      %rw.seq(f, sel.a(q1), q2, t0, t1, run.store(f, 0n, C.M.g(16n), hh, t0, z, hv, g, eh, hc)) : {_ == rhs : C.Cir.Out}
      %rw.seq(f, sel.a(q2), q3, t1, t2, run.store(f, 1n, C.M.g(16n), C.M.g(2n), t1, z, sp, g, esp, hc)) : {_ == rhs : C.Cir.Out}
      %rw.seq(f, sel.a(q3), q4, t2, t3, run.store(f, 2n, C.M.g(16n), aa, t2, z, av, g, ea, hc)) : {_ == rhs : C.Cir.Out}
      %rw.seq(f, sel.a(q4), q5, t3, t4, run.store(f, 3n, C.M.g(16n), bb, t3, z, bv, g, eb, hc)) : {_ == rhs : C.Cir.Out}
      %rw.seq(f, sel.a(q5), sel.b(q5), t4, t5, run.set(f, 2n, C.M.g(16n), t4, z, g, hl, {==})) : {_ == rhs : C.Cir.Out}
      run.nop(f, t5)
