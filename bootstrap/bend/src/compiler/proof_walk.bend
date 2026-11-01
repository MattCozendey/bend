# compiler: the data check and the walk of the machine (layer B)
# ===============================================================
#
# Toward data.post/data.done and walk.post/walk.done of proof_mach.bend
# (M.data and M.walk of impl.bend's Machine). What is here, all checked:
#
#   WP(s, F, st, Q): a weakest precondition of Cir.exec that matches the
#     statement first (Cir.exec matches the fuel first, so it is stuck on a
#     fuel variable); straight code computes inside it, and a proof gives only
#     the accesses' checks (Ob, CellOk) and a case at each test. M.alloc (an if
#     whose else is Stmt.alloc) is left whole, as an Ok of Cir.exec.
#     Sim: WP gives Ok(Cir.exec(F, s, st), Q); Mono: a weaker end;
#     WP.post: WP gives PM.Post(False, Cir.exec(F, s, st), Q, no halt).
#   Frames of T.tm.of: TFag (a set that keeps a cell's tag, quantity and
#     parts), TF1 (field 1), TFl (a flag outside the tag and quantity bits),
#     TFo/RdF (a set outside the cells that the term reads, RdIn); a ghost
#     write log (Wr, Apply, WOk) and its frames W.tm, W.rd, W.link, W.ag.
#   Terms: TUniq (one term per cell, whatever the fuel), D.lab, D.rfl, D.tup,
#     D.oth (a cell's term by its tag, for the data check).
#   The data check's soundness at its end: NFD (once the stack is empty,
#     every cell the check flagged stands for Data), with its invariant
#     (Stk, NFOk, Setl, Cl) and the lemmas that a round keeps it (SetStep,
#     ClM, NFOkM, FlW).
#   An interface for allocation (CS, AH, CF, PH, Sup) that the runs of M.data
#     and M.walk would take.
#
# Not here yet: the rounds of M.data's loops through WP, and M.walk.

import Base
import ./impl.bend as C
import ./proof_term.bend as T
import ./proof_need.bend as N
import ./proof_mach_defs.bend as PM

# Kit
# ---

# the truth of b, as a type
def Tr(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def IsSome(x: Maybe<&2, U32>) -> Type:
  match x:
    case None{}:
      Empty
    case Some{_}:
      Unit

def IfV(z: Bool, A: Type, B: Type) -> Type:
  match z:
    case False{}:
      A
    case True{}:
      B

def ft(-G: Type, h: {True{} == False{} : Bool}) -> G:
  Empty.absurd(G, N.true_ne_false(h))

def tf(-G: Type, h: {False{} == True{} : Bool}) -> G:
  Empty.absurd(G, N.false_ne_true(h))

# WP
# --

# the value of e, read with no check
def Ev.field(k: Nat, i: U32, st: C.Cir.State) -> U32:
  match st:
    case C.Cir.State{_, cells, _, _, _, _, _, _, _, _}:
      C.Cir.Cell.get(k, C.Cir.Cells.get(cells, i))

def Ev(e: C.Cir.Expr, +st: C.Cir.State) -> U32:
  match e:
    case C.Cir.Expr.const{n}:
      n
    case C.Cir.Expr.get{r}:
      Maybe.default(&2, U32, C.Cir.eval.get(r, st), 0)
    case C.Cir.Expr.op{o, a, b}:
      C.Wasm.op(o, Ev(a, st), Ev(b, st))
    case C.Cir.Expr.eqz{a}:
      Bool.to_u32(U32.is_zero(Ev(a, st)))
    case C.Cir.Expr.field{k, c}:
      Ev.field(k, Ev(c, st), st)
    case C.Cir.Expr.byte{i}:
      Maybe.default(&2, U32, C.Cir.eval.byte(Some{Ev(i, st)}, C.Cir.eval.input(st)), 0)
    case C.Cir.Expr.size{}:
      Maybe.default(&2, U32, C.Cir.eval.size(st), 0)

# the cell i is one that Cir may access in st
def CellOk(i: U32, st: C.Cir.State) -> Type:
  match st:
    case C.Cir.State{_, _, next, first, image, _, _, _, _, _}:
      {True{} == C.Cir.is_cell(i, image, first, next) : Bool}

# every access of e is one that Cir allows
def Ob(e: C.Cir.Expr, +st: C.Cir.State) -> Type:
  match e:
    case C.Cir.Expr.const{_}:
      Unit
    case C.Cir.Expr.get{r}:
      IsSome(C.Cir.eval.get(r, st))
    case C.Cir.Expr.op{_, a, b}:
      Ob(a, st) & Ob(b, st)
    case C.Cir.Expr.eqz{a}:
      Ob(a, st)
    case C.Cir.Expr.field{_, c}:
      Ob(c, st) & CellOk(Ev(c, st), st)
    case C.Cir.Expr.byte{i}:
      Ob(i, st) & IsSome(C.Cir.eval.byte(Some{Ev(i, st)}, C.Cir.eval.input(st)))
    case C.Cir.Expr.size{}:
      Unit

def Ok(o: C.Cir.Out, Q: C.Cir.State -> Type) -> Type:
  match o:
    case C.Cir.Out.next{st}:
      Q(st)
    case C.Cir.Out.halt{_, _}:
      Empty
    case C.Cir.Out.out_of_memory{}:
      Unit
    case C.Cir.Out.trap{}:
      Empty
    case C.Cir.Out.not_done{}:
      Unit

# a register r is set to v
def Upd(+st: C.Cir.State, r: Nat, v: U32) -> C.Cir.State:
  match st:
    case C.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}:
      C.Cir.State{List.set(&2, U32, regs, r, v), cells, next, first, image, pages, limit, input, out, outn}

def WP.set(r: Nat, v: U32, +st: C.Cir.State, Q: C.Cir.State -> Type) -> Type:
  match st:
    case C.Cir.State{+regs, _, _, _, _, _, _, _, _, _}:
      Tr(Nat.is_lt(r, List.length(&2, U32, regs))) & Q(Upd(st, r, v))

# field k of the cell i is set to v
def Sto(+st: C.Cir.State, k: Nat, +i: U32, v: U32) -> C.Cir.State:
  match st:
    case C.Cir.State{regs, +cells, next, first, image, pages, limit, input, out, outn}:
      C.Cir.State{regs, C.Cir.Cells.set(cells, i, C.Cir.Cell.set(k, C.Cir.Cells.get(cells, i), v)), next, first, image, pages, limit, input, out, outn}

def WP.store(k: Nat, +i: U32, v: U32, +st: C.Cir.State, Q: C.Cir.State -> Type) -> Type:
  CellOk(i, st) & Q(Sto(st, k, i, v))

# a branch of an if, on z = U32.is_zero of its test: the yes when false
def IfQ(z: Bool, ka: (C.Cir.State -> Type) -> Type, kb: (C.Cir.State -> Type) -> Type, Q: C.Cir.State -> Type) -> Type:
  match z:
    case False{}:
      ka(Q)
    case True{}:
      kb(Q)

# an if; one whose else is an alloc is M.alloc, whose outcome is given whole
def WP.if(e: C.Cir.Stmt, F: Nat, c: C.Cir.Expr, t: C.Cir.Stmt, +st: C.Cir.State, Q: C.Cir.State -> Type,
  ka: (C.Cir.State -> Type) -> Type, kb: (C.Cir.State -> Type) -> Type) -> Type:
  match e:
    case C.Cir.Stmt.alloc{r}:
      Ok(C.Cir.exec(F, C.Cir.Stmt.if{c, t, C.Cir.Stmt.alloc{r}}, st), Q)
    case _:
      Ob(c, st) & IfQ(U32.is_zero(Ev(c, st)), ka, kb, Q)

# a round of a while, on z = U32.is_zero of its test: the body when false;
# else the end, at st
def WhQ(z: Bool, kb: (C.Cir.State -> Type) -> Type, Q: C.Cir.State -> Type, st: C.Cir.State) -> Type:
  match z:
    case False{}:
      kb(Q)
    case True{}:
      Q(st)

# the weakest precondition of s from st, for the end Q
def WP(+s: C.Cir.Stmt, +F: Nat, +st: C.Cir.State, Q: C.Cir.State -> Type) -> Type:
  match s:
    case C.Cir.Stmt.nop{}:
      Q(st)
    case C.Cir.Stmt.set{r, e}:
      Ob(e, st) & WP.set(r, Ev(e, st), st, Q)
    case C.Cir.Stmt.store{k, c, v}:
      Ob(c, st) & (Ob(v, st) & WP.store(k, Ev(c, st), Ev(v, st), st, Q))
    case C.Cir.Stmt.alloc{_}:
      Empty
    case C.Cir.Stmt.emit{_}:
      Empty
    case C.Cir.Stmt.seq{a, b}:
      WP(a, F, st, t => WP(b, F, t, Q))
    case C.Cir.Stmt.if{+c, +t, +e}:
      WP.if(e, F, c, t, st, Q, q => WP(t, F, st, q), q => WP(e, F, st, q))
    case C.Cir.Stmt.while{+c, +b}:
      match F:
        case 0n:
          Unit
        case 1n+(+g):
          Ob(c, st) & WhQ(U32.is_zero(Ev(c, st)), q => WP(b, g, st, t => WP(s, g, t, q)), Q, st)
    case C.Cir.Stmt.halt{_}:
      Empty

# WP is sound
# -----------

def EvS.get(x: Maybe<&2, U32>, ob: IsSome(x)) -> {Some{Maybe.default(&2, U32, x, 0)} == x : Maybe<&2, U32>}:
  match x:
    case None{}:
      match ob:
    case Some{y}:
      {==}

def EvS.byte(x: Maybe<&2, U32>, ob: IsSome(x)) -> {Some{Maybe.default(&2, U32, x, 0)} == x : Maybe<&2, U32>}:
  EvS.get(x, ob)

def EvS.size(st: C.Cir.State) -> {Some{Maybe.default(&2, U32, C.Cir.eval.size(st), 0)} == C.Cir.eval.size(st) : Maybe<&2, U32>}:
  match st:
    case C.Cir.State{_, _, _, _, _, _, _, input, _, _}:
      {==}

def EvS.field(+k: Nat, +i: U32, st: C.Cir.State, ok: CellOk(i, st)) ->
  {Some{Ev.field(k, i, st)} == C.Cir.eval.field(k, Some{i}, st) : Maybe<&2, U32>}:
  match st:
    case C.Cir.State{regs, +cells, +next, +first, +image, pages, limit, input, out, outn}:
      %ok : {Some{C.Cir.Cell.get(k, C.Cir.Cells.get(cells, i))} == C.Cir.eval.field.if(_, k, cells, i) : Maybe<&2, U32>}
      {==}

# an expression whose accesses Cir allows has the value Ev
def EvS(+e: C.Cir.Expr, +st: C.Cir.State, ob: Ob(e, st)) -> {Some{Ev(e, st)} == C.Cir.eval(e, st) : Maybe<&2, U32>}:
  match e:
    case C.Cir.Expr.const{n}:
      {==}
    case C.Cir.Expr.get{r}:
      EvS.get(C.Cir.eval.get(r, st), ob)
    case C.Cir.Expr.op{+o, +a, +b}:
      (oa, ob2) = ob
      %EvS(a, st, oa) : {Some{C.Wasm.op(o, Ev(a, st), Ev(b, st))} == C.Cir.eval.op(o, _, C.Cir.eval(b, st)) : Maybe<&2, U32>}
      %EvS(b, st, ob2) : {Some{C.Wasm.op(o, Ev(a, st), Ev(b, st))} == C.Cir.eval.op(o, Some{Ev(a, st)}, _) : Maybe<&2, U32>}
      {==}
    case C.Cir.Expr.eqz{+a}:
      %EvS(a, st, ob) : {Some{Bool.to_u32(U32.is_zero(Ev(a, st)))} == C.Cir.eval.eqz(_) : Maybe<&2, U32>}
      {==}
    case C.Cir.Expr.field{+k, +c}:
      (oc, ok) = ob
      %EvS(c, st, oc) : {Some{Ev.field(k, Ev(c, st), st)} == C.Cir.eval.field(k, _, st) : Maybe<&2, U32>}
      EvS.field(k, Ev(c, st), st, ok)
    case C.Cir.Expr.byte{+i}:
      (oi, ob2) = ob
      %EvS(i, st, oi) : {Some{Maybe.default(&2, U32, C.Cir.eval.byte(Some{Ev(i, st)}, C.Cir.eval.input(st)), 0)} == C.Cir.eval.byte(_, C.Cir.eval.input(st)) : Maybe<&2, U32>}
      EvS.byte(C.Cir.eval.byte(Some{Ev(i, st)}, C.Cir.eval.input(st)), ob2)
    case C.Cir.Expr.size{}:
      EvS.size(st)

# an outcome, then more
def Then(o: C.Cir.Out, -k: C.Cir.State -> C.Cir.Out, -P: C.Cir.State -> Type, -Q: C.Cir.State -> Type,
  h: Ok(o, P), g: @st: C.Cir.State -> P(st) -> Ok(k(st), Q)) -> Ok(C.Cir.exec.then(o, k), Q):
  match o:
    case C.Cir.Out.next{st}:
      g(st, h)
    case C.Cir.Out.halt{s, st}:
      match h:
    case C.Cir.Out.out_of_memory{}:
      Unit{}
    case C.Cir.Out.trap{}:
      match h:
    case C.Cir.Out.not_done{}:
      Unit{}

def Sim.set.if(b: Bool, +regs: List<&2, U32>, +r: Nat, +x: U32, +cells: C.Cir.Cells, +next: U32, +first: U32, +image: U32, +pages: U32, +limit: U32,
  +input: List<&2, U32>, +out: List<&2, U32>, +outn: U32, -Q: C.Cir.State -> Type, tr: Tr(b),
  q: Q(C.Cir.State{List.set(&2, U32, regs, r, x), cells, next, first, image, pages, limit, input, out, outn})) ->
  Ok(C.Cir.exec.set.of(C.Cir.regs.set.if(b, regs, r, x), C.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}), Q):
  match b:
    case True{}:
      q
    case False{}:
      match tr:

def Sim.set(+r: Nat, +e: C.Cir.Expr, +st: C.Cir.State, -Q: C.Cir.State -> Type, w: Ob(e, st) & WP.set(r, Ev(e, st), st, Q)) ->
  Ok(C.Cir.exec.set(r, C.Cir.eval(e, st), st), Q):
  match st:
    case C.Cir.State{+regs, +cells, +next, +first, +image, +pages, +limit, +input, +out, +outn}:
      (ob, ws) = w
      (tr, q) = ws
      +s0 = {C.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn} : C.Cir.State}
      %EvS(e, s0, ob) : Ok(C.Cir.exec.set(r, _, s0), Q)
      Sim.set.if(Nat.is_lt(r, List.length(&2, U32, regs)), regs, r, Ev(e, s0), cells, next, first, image, pages, limit, input, out, outn, Q, tr, q)

def Sim.store.go(+k: Nat, +i: U32, +x: U32, +st: C.Cir.State, -Q: C.Cir.State -> Type, w: WP.store(k, i, x, st, Q)) ->
  Ok(C.Cir.exec.store(k, Some{i}, Some{x}, st), Q):
  match st:
    case C.Cir.State{regs, +cells, +next, +first, +image, pages, limit, input, out, outn}:
      (ok, q) = w
      %ok : Ok(C.Cir.exec.store.if(_, k, i, x, C.Cir.State{regs, cells, next, first, image, pages, limit, input, out, outn}), Q)
      q

def Sim.store(+k: Nat, +c: C.Cir.Expr, +v: C.Cir.Expr, +st: C.Cir.State, -Q: C.Cir.State -> Type,
  w: Ob(c, st) & (Ob(v, st) & WP.store(k, Ev(c, st), Ev(v, st), st, Q))) ->
  Ok(C.Cir.exec.store(k, C.Cir.eval(c, st), C.Cir.eval(v, st), st), Q):
  (oc, w2) = w
  (ov, ws) = w2
  %EvS(c, st, oc) : Ok(C.Cir.exec.store(k, _, C.Cir.eval(v, st), st), Q)
  %EvS(v, st, ov) : Ok(C.Cir.exec.store(k, Some{Ev(c, st)}, _, st), Q)
  Sim.store.go(k, Ev(c, st), Ev(v, st), st, Q, ws)

def Sim.if.of(z: Bool, -ka: (C.Cir.State -> Type) -> Type, -kb: (C.Cir.State -> Type) -> Type, -Q: C.Cir.State -> Type,
  -yes: Unit -> C.Cir.Out, -no: Unit -> C.Cir.Out, h: IfQ(z, ka, kb, Q), hy: ka(Q) -> Ok(yes(Unit{}), Q), hn: kb(Q) -> Ok(no(Unit{}), Q)) ->
  Ok(C.Cir.exec.if.of(z, yes, no), Q):
  match z:
    case False{}:
      hy(h)
    case True{}:
      hn(h)

def Sim.if(+F: Nat, +c: C.Cir.Expr, -t: C.Cir.Stmt, -e: C.Cir.Stmt, +st: C.Cir.State, -Q: C.Cir.State -> Type,
  w: Ob(c, st) & IfQ(U32.is_zero(Ev(c, st)), q => WP(t, F, st, q), q => WP(e, F, st, q), Q),
  ht: WP(t, F, st, Q) -> Ok(C.Cir.exec(F, t, st), Q), he: WP(e, F, st, Q) -> Ok(C.Cir.exec(F, e, st), Q)) ->
  Ok(C.Cir.exec.if(C.Cir.eval(c, st), u => C.Cir.exec(F, t, st), u => C.Cir.exec(F, e, st)), Q):
  (oc, wz) = w
  %EvS(c, st, oc) : Ok(C.Cir.exec.if(_, u => C.Cir.exec(F, t, st), u => C.Cir.exec(F, e, st)), Q)
  Sim.if.of(U32.is_zero(Ev(c, st)), q => WP(t, F, st, q), q => WP(e, F, st, q), Q, u => C.Cir.exec(F, t, st), u => C.Cir.exec(F, e, st), wz, ht, he)

def Sim.wh.of(z: Bool, -kb: (C.Cir.State -> Type) -> Type, -Q: C.Cir.State -> Type, +st: C.Cir.State,
  -yes: Unit -> C.Cir.Out, h: WhQ(z, kb, Q, st), hy: kb(Q) -> Ok(yes(Unit{}), Q)) ->
  Ok(C.Cir.exec.if.of(z, yes, u => C.Cir.Out.next{st}), Q):
  match z:
    case False{}:
      hy(h)
    case True{}:
      h

def Sim.wh(+g: Nat, +c: C.Cir.Expr, -b: C.Cir.Stmt, +st: C.Cir.State, -Q: C.Cir.State -> Type,
  w: Ob(c, st) & WhQ(U32.is_zero(Ev(c, st)), q => WP(b, g, st, t => WP(C.Cir.Stmt.while{c, b}, g, t, q)), Q, st),
  hb: WP(b, g, st, t => WP(C.Cir.Stmt.while{c, b}, g, t, Q)) ->
    Ok(C.Cir.exec.then(C.Cir.exec(g, b, st), t => C.Cir.exec(g, C.Cir.Stmt.while{c, b}, t)), Q)) ->
  Ok(C.Cir.exec.if(C.Cir.eval(c, st), u => C.Cir.exec.then(C.Cir.exec(g, b, st), t => C.Cir.exec(g, C.Cir.Stmt.while{c, b}, t)),
    u => C.Cir.Out.next{st}), Q):
  (oc, wz) = w
  %EvS(c, st, oc) : Ok(C.Cir.exec.if(_, u => C.Cir.exec.then(C.Cir.exec(g, b, st), t => C.Cir.exec(g, C.Cir.Stmt.while{c, b}, t)),
    u => C.Cir.Out.next{st}), Q)
  Sim.wh.of(U32.is_zero(Ev(c, st)), q => WP(b, g, st, t => WP(C.Cir.Stmt.while{c, b}, g, t, q)), Q, st,
    u => C.Cir.exec.then(C.Cir.exec(g, b, st), t => C.Cir.exec(g, C.Cir.Stmt.while{c, b}, t)), wz, hb)

# an if, by its else: M.alloc's outcome is given whole
def Sim.if2(+F: Nat, +e: C.Cir.Stmt, +c: C.Cir.Expr, +t: C.Cir.Stmt, +st: C.Cir.State, -Q: C.Cir.State -> Type,
  w: WP.if(e, F, c, t, st, Q, q => WP(t, F, st, q), q => WP(e, F, st, q)),
  ht: WP(t, F, st, Q) -> Ok(C.Cir.exec(F, t, st), Q), he: WP(e, F, st, Q) -> Ok(C.Cir.exec(F, e, st), Q)) ->
  Ok(C.Cir.exec.if(C.Cir.eval(c, st), u => C.Cir.exec(F, t, st), u => C.Cir.exec(F, e, st)), Q):
  match F:
    case 0n:
      match e:
        case C.Cir.Stmt.alloc{r}:
          w
        case C.Cir.Stmt.nop{}:
          Sim.if(F, c, t, C.Cir.Stmt.nop{}, st, Q, w, ht, he)
        case C.Cir.Stmt.set{r2, e2}:
          Sim.if(F, c, t, C.Cir.Stmt.set{r2, e2}, st, Q, w, ht, he)
        case C.Cir.Stmt.store{k2, c2, v2}:
          Sim.if(F, c, t, C.Cir.Stmt.store{k2, c2, v2}, st, Q, w, ht, he)
        case C.Cir.Stmt.emit{v2}:
          Sim.if(F, c, t, C.Cir.Stmt.emit{v2}, st, Q, w, ht, he)
        case C.Cir.Stmt.seq{a2, b2}:
          Sim.if(F, c, t, C.Cir.Stmt.seq{a2, b2}, st, Q, w, ht, he)
        case C.Cir.Stmt.if{c2, t2, e2}:
          Sim.if(F, c, t, C.Cir.Stmt.if{c2, t2, e2}, st, Q, w, ht, he)
        case C.Cir.Stmt.while{c2, b2}:
          Sim.if(F, c, t, C.Cir.Stmt.while{c2, b2}, st, Q, w, ht, he)
        case C.Cir.Stmt.halt{s2}:
          Sim.if(F, c, t, C.Cir.Stmt.halt{s2}, st, Q, w, ht, he)
    case 1n+g:
      match e:
        case C.Cir.Stmt.alloc{r}:
          w
        case C.Cir.Stmt.nop{}:
          Sim.if(F, c, t, C.Cir.Stmt.nop{}, st, Q, w, ht, he)
        case C.Cir.Stmt.set{r2, e2}:
          Sim.if(F, c, t, C.Cir.Stmt.set{r2, e2}, st, Q, w, ht, he)
        case C.Cir.Stmt.store{k2, c2, v2}:
          Sim.if(F, c, t, C.Cir.Stmt.store{k2, c2, v2}, st, Q, w, ht, he)
        case C.Cir.Stmt.emit{v2}:
          Sim.if(F, c, t, C.Cir.Stmt.emit{v2}, st, Q, w, ht, he)
        case C.Cir.Stmt.seq{a2, b2}:
          Sim.if(F, c, t, C.Cir.Stmt.seq{a2, b2}, st, Q, w, ht, he)
        case C.Cir.Stmt.if{c2, t2, e2}:
          Sim.if(F, c, t, C.Cir.Stmt.if{c2, t2, e2}, st, Q, w, ht, he)
        case C.Cir.Stmt.while{c2, b2}:
          Sim.if(F, c, t, C.Cir.Stmt.while{c2, b2}, st, Q, w, ht, he)
        case C.Cir.Stmt.halt{s2}:
          Sim.if(F, c, t, C.Cir.Stmt.halt{s2}, st, Q, w, ht, he)

def Sim.seq(+F: Nat, +a: C.Cir.Stmt, +b: C.Cir.Stmt, +st: C.Cir.State, -Q: C.Cir.State -> Type,
  ha: Ok(C.Cir.exec(F, a, st), t => WP(b, F, t, Q)), hb: @t: C.Cir.State -> WP(b, F, t, Q) -> Ok(C.Cir.exec(F, b, t), Q)) ->
  Ok(C.Cir.exec.then(C.Cir.exec(F, a, st), t => C.Cir.exec(F, b, t)), Q):
  Then(C.Cir.exec(F, a, st), t => C.Cir.exec(F, b, t), t => WP(b, F, t, Q), Q, ha, hb)

# WP gives Cir.exec's outcome
def Sim(+F: Nat, +s: C.Cir.Stmt, +st: C.Cir.State, -Q: C.Cir.State -> Type, w: WP(s, F, st, Q)) -> Ok(C.Cir.exec(F, s, st), Q):
  match F:
    case 0n:
      match s:
        case C.Cir.Stmt.nop{}:
          w
        case C.Cir.Stmt.set{+r, +e}:
          Sim.set(r, e, st, Q, w)
        case C.Cir.Stmt.store{+k, +c, +v}:
          Sim.store(k, c, v, st, Q, w)
        case C.Cir.Stmt.alloc{_}:
          match w:
        case C.Cir.Stmt.emit{_}:
          match w:
        case C.Cir.Stmt.seq{+a, +b}:
          Sim.seq(F, a, b, st, Q, Sim(F, a, st, t => WP(b, F, t, Q), w), t => wt => Sim(F, b, t, Q, wt))
        case C.Cir.Stmt.if{+c, +t, +e}:
          Sim.if2(F, e, c, t, st, Q, w, wt => Sim(F, t, st, Q, wt), we => Sim(F, e, st, Q, we))
        case C.Cir.Stmt.while{_, _}:
          Unit{}
        case C.Cir.Stmt.halt{_}:
          match w:
    case 1n+(+g):
      match s:
        case C.Cir.Stmt.nop{}:
          w
        case C.Cir.Stmt.set{+r, +e}:
          Sim.set(r, e, st, Q, w)
        case C.Cir.Stmt.store{+k, +c, +v}:
          Sim.store(k, c, v, st, Q, w)
        case C.Cir.Stmt.alloc{_}:
          match w:
        case C.Cir.Stmt.emit{_}:
          match w:
        case C.Cir.Stmt.seq{+a, +b}:
          Sim.seq(F, a, b, st, Q, Sim(F, a, st, t => WP(b, F, t, Q), w), t => wt => Sim(F, b, t, Q, wt))
        case C.Cir.Stmt.if{+c, +t, +e}:
          Sim.if2(F, e, c, t, st, Q, w, wt => Sim(F, t, st, Q, wt), we => Sim(F, e, st, Q, we))
        case C.Cir.Stmt.while{+c, +b}:
          Sim.wh(g, c, b, st, Q, w, wb => Sim.seq(g, b, C.Cir.Stmt.while{c, b}, st, Q, Sim(g, b, st, t => WP(C.Cir.Stmt.while{c, b}, g, t, Q), wb),
            t => wt => Sim(g, C.Cir.Stmt.while{c, b}, t, Q, wt)))
        case C.Cir.Stmt.halt{_}:
          match w:

# A weaker end
# ------------

def OkMono(o: C.Cir.Out, -P: C.Cir.State -> Type, -Q: C.Cir.State -> Type, h: Ok(o, P), imp: @t: C.Cir.State -> P(t) -> Q(t)) -> Ok(o, Q):
  match o:
    case C.Cir.Out.next{st}:
      imp(st, h)
    case C.Cir.Out.halt{s, st}:
      match h:
    case C.Cir.Out.out_of_memory{}:
      Unit{}
    case C.Cir.Out.trap{}:
      match h:
    case C.Cir.Out.not_done{}:
      Unit{}

def Mono.set(+r: Nat, +v: U32, +st: C.Cir.State, -P: C.Cir.State -> Type, -Q: C.Cir.State -> Type, w: WP.set(r, v, st, P),
  imp: @t: C.Cir.State -> P(t) -> Q(t)) -> WP.set(r, v, st, Q):
  match st:
    case C.Cir.State{+regs, +cells, +next, +first, +image, +pages, +limit, +input, +out, +outn}:
      (tr, p) = w
      (tr, imp(C.Cir.State{List.set(&2, U32, regs, r, v), cells, next, first, image, pages, limit, input, out, outn}, p))

def Mono.ifq(z: Bool, -ka: (C.Cir.State -> Type) -> Type, -kb: (C.Cir.State -> Type) -> Type, -P: C.Cir.State -> Type, -Q: C.Cir.State -> Type,
  w: IfQ(z, ka, kb, P), imp: @t: C.Cir.State -> P(t) -> Q(t),
  ra: (@t: C.Cir.State -> P(t) -> Q(t)) -> ka(P) -> ka(Q), rb: (@t: C.Cir.State -> P(t) -> Q(t)) -> kb(P) -> kb(Q)) -> IfQ(z, ka, kb, Q):
  match z:
    case False{}:
      ra(imp, w)
    case True{}:
      rb(imp, w)

def Mono.if(+e: C.Cir.Stmt, +F: Nat, +c: C.Cir.Expr, +t: C.Cir.Stmt, +st: C.Cir.State, -P: C.Cir.State -> Type, -Q: C.Cir.State -> Type,
  w: WP.if(e, F, c, t, st, P, q => WP(t, F, st, q), q => WP(e, F, st, q)), imp: @t: C.Cir.State -> P(t) -> Q(t),
  ra: (@t: C.Cir.State -> P(t) -> Q(t)) -> WP(t, F, st, P) -> WP(t, F, st, Q),
  rb: (@t: C.Cir.State -> P(t) -> Q(t)) -> WP(e, F, st, P) -> WP(e, F, st, Q)) ->
  WP.if(e, F, c, t, st, Q, q => WP(t, F, st, q), q => WP(e, F, st, q)):
  match e:
    case C.Cir.Stmt.alloc{r}:
      OkMono(C.Cir.exec(F, C.Cir.Stmt.if{c, t, C.Cir.Stmt.alloc{r}}, st), P, Q, w, imp)
    case C.Cir.Stmt.nop{}:
      (oc, wz) = w
      (oc, Mono.ifq(U32.is_zero(Ev(c, st)), q => WP(t, F, st, q), q => WP(C.Cir.Stmt.nop{}, F, st, q), P, Q, wz, imp, ra, rb))
    case C.Cir.Stmt.set{r2, e2}:
      (oc, wz) = w
      (oc, Mono.ifq(U32.is_zero(Ev(c, st)), q => WP(t, F, st, q), q => WP(C.Cir.Stmt.set{r2, e2}, F, st, q), P, Q, wz, imp, ra, rb))
    case C.Cir.Stmt.store{k2, c2, v2}:
      (oc, wz) = w
      (oc, Mono.ifq(U32.is_zero(Ev(c, st)), q => WP(t, F, st, q), q => WP(C.Cir.Stmt.store{k2, c2, v2}, F, st, q), P, Q, wz, imp, ra, rb))
    case C.Cir.Stmt.emit{v2}:
      (oc, wz) = w
      (oc, Mono.ifq(U32.is_zero(Ev(c, st)), q => WP(t, F, st, q), q => WP(C.Cir.Stmt.emit{v2}, F, st, q), P, Q, wz, imp, ra, rb))
    case C.Cir.Stmt.seq{a2, b2}:
      (oc, wz) = w
      (oc, Mono.ifq(U32.is_zero(Ev(c, st)), q => WP(t, F, st, q), q => WP(C.Cir.Stmt.seq{a2, b2}, F, st, q), P, Q, wz, imp, ra, rb))
    case C.Cir.Stmt.if{c2, t2, e2}:
      (oc, wz) = w
      (oc, Mono.ifq(U32.is_zero(Ev(c, st)), q => WP(t, F, st, q), q => WP(C.Cir.Stmt.if{c2, t2, e2}, F, st, q), P, Q, wz, imp, ra, rb))
    case C.Cir.Stmt.while{c2, b2}:
      (oc, wz) = w
      (oc, Mono.ifq(U32.is_zero(Ev(c, st)), q => WP(t, F, st, q), q => WP(C.Cir.Stmt.while{c2, b2}, F, st, q), P, Q, wz, imp, ra, rb))
    case C.Cir.Stmt.halt{s2}:
      (oc, wz) = w
      (oc, Mono.ifq(U32.is_zero(Ev(c, st)), q => WP(t, F, st, q), q => WP(C.Cir.Stmt.halt{s2}, F, st, q), P, Q, wz, imp, ra, rb))

def Mono.wh(z: Bool, -kb: (C.Cir.State -> Type) -> Type, -P: C.Cir.State -> Type, -Q: C.Cir.State -> Type, +st: C.Cir.State,
  w: WhQ(z, kb, P, st), imp: @t: C.Cir.State -> P(t) -> Q(t), rb: (@t: C.Cir.State -> P(t) -> Q(t)) -> kb(P) -> kb(Q)) -> WhQ(z, kb, Q, st):
  match z:
    case False{}:
      rb(imp, w)
    case True{}:
      imp(st, w)

# WP for an end P gives WP for any weaker end Q
def Mono(+s: C.Cir.Stmt, +F: Nat, +st: C.Cir.State, -P: C.Cir.State -> Type, -Q: C.Cir.State -> Type, w: WP(s, F, st, P),
  imp: @t: C.Cir.State -> P(t) -> Q(t)) -> WP(s, F, st, Q):
  match s:
    case C.Cir.Stmt.nop{}:
      imp(st, w)
    case C.Cir.Stmt.set{+r, +e}:
      (oe, ws) = w
      (oe, Mono.set(r, Ev(e, st), st, P, Q, ws, imp))
    case C.Cir.Stmt.store{+k, +c, +v}:
      (oc, w2) = w
      (ov, w3) = w2
      (ok, p) = w3
      (oc, (ov, (ok, imp(Sto(st, k, Ev(c, st), Ev(v, st)), p))))
    case C.Cir.Stmt.alloc{_}:
      match w:
    case C.Cir.Stmt.emit{_}:
      match w:
    case C.Cir.Stmt.seq{+a, +b}:
      Mono(a, F, st, t => WP(b, F, t, P), t => WP(b, F, t, Q), w, t => wt => Mono(b, F, t, P, Q, wt, imp))
    case C.Cir.Stmt.if{+c, +t, +e}:
      Mono.if(e, F, c, t, st, P, Q, w, imp, i => wt => Mono(t, F, st, P, Q, wt, i), i => we => Mono(e, F, st, P, Q, we, i))
    case C.Cir.Stmt.while{+c, +b}:
      match F:
        case 0n:
          Unit{}
        case 1n+(+g):
          (oc, wz) = w
          (oc, Mono.wh(U32.is_zero(Ev(c, st)), q => WP(b, g, st, t => WP(s, g, t, q)), P, Q, st, wz, imp,
            i => wb => Mono(b, g, st, t => WP(s, g, t, P), t => WP(s, g, t, Q), wb, t => wt => Mono(s, g, t, P, Q, wt, i))))
    case C.Cir.Stmt.halt{_}:
      match w:


# Cells
# -----
#
# (as proof_in.bend proves them)

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
              %Ce.set_set.at(p, t, C.Cir.Cells.none{}, c, d) : {C.Cir.Cells.node{C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, d), C.Cir.Cells.none{}} == C.Cir.Cells.node{_, C.Cir.Cells.none{}} : C.Cir.Cells}
              {==}
            case C.Cir.Cells.one{+e}:
              %Ce.set_set.at(p, t, C.Cir.Cells.none{}, c, d) : {C.Cir.Cells.node{C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, d), C.Cir.Cells.none{}} == C.Cir.Cells.node{_, C.Cir.Cells.none{}} : C.Cir.Cells}
              {==}
        case WCon{True{}, +t}:
          match m:
            case C.Cir.Cells.node{+lo, +hi}:
              %Ce.set_set.at(p, t, hi, c, d) : {C.Cir.Cells.node{lo, C.Cir.Cells.set.at(p, t, hi, d)} == C.Cir.Cells.node{lo, _} : C.Cir.Cells}
              {==}
            case C.Cir.Cells.none{}:
              %Ce.set_set.at(p, t, C.Cir.Cells.none{}, c, d) : {C.Cir.Cells.node{C.Cir.Cells.none{}, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, d)} == C.Cir.Cells.node{C.Cir.Cells.none{}, _} : C.Cir.Cells}
              {==}
            case C.Cir.Cells.one{+e}:
              %Ce.set_set.at(p, t, C.Cir.Cells.none{}, c, d) : {C.Cir.Cells.node{C.Cir.Cells.none{}, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, d)} == C.Cir.Cells.node{C.Cir.Cells.none{}, _} : C.Cir.Cells}
              {==}

def Ce.set_set(+m: C.Cir.Cells, +i: U32, +c: C.Cir.Cell, +d: C.Cir.Cell) ->
  {C.Cir.Cells.set(m, i, d) == C.Cir.Cells.set(C.Cir.Cells.set(m, i, c), i, d) : C.Cir.Cells}:
  match i:
    case U32{+w}:
      Ce.set_set.at(32n, w, m, c, d)

# no cell is all zeros
def Ce.get_none(n: Nat, +v: Word(n)) -> {C.Cir.Cell.zero() == C.Cir.Cells.get.at(n, v, C.Cir.Cells.none{}) : C.Cir.Cell}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match v:
        case WCon{False{}, +s}:
          {==}
        case WCon{True{}, +s}:
          {==}

# a set at w keeps the cell at another address v
def Ce.get_other.at(n: Nat, +v: Word(n), +w: Word(n), +m: C.Cir.Cells, +c: C.Cir.Cell, ne: {v == w : Word(n)} -> Empty) ->
  {C.Cir.Cells.get.at(n, v, m) == C.Cir.Cells.get.at(n, v, C.Cir.Cells.set.at(n, w, m, c)) : C.Cir.Cell}:
  match n:
    case 0n:
      match v w:
        case WNil{} WNil{}:
          Empty.absurd({C.Cir.Cells.get.at(0n, WNil{}, m) == C.Cir.Cells.get.at(0n, WNil{}, C.Cir.Cells.set.at(0n, WNil{}, m, c)) : C.Cir.Cell}, ne({==}))
    case 1n+(+p):
      match v w:
        case WCon{False{}, +s} WCon{False{}, +t}:
          match m:
            case C.Cir.Cells.node{+lo, +hi}:
              Ce.get_other.at(p, s, t, lo, c, e => ne(Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x}, s, t, e)))
            case C.Cir.Cells.none{}:
              Equal.trans(C.Cir.Cell, C.Cir.Cell.zero(), C.Cir.Cells.get.at(p, s, C.Cir.Cells.none{}), C.Cir.Cells.get.at(p, s, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, c)),
                Ce.get_none(p, s), Ce.get_other.at(p, s, t, C.Cir.Cells.none{}, c, e => ne(Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x}, s, t, e))))
            case C.Cir.Cells.one{+d}:
              Equal.trans(C.Cir.Cell, C.Cir.Cell.zero(), C.Cir.Cells.get.at(p, s, C.Cir.Cells.none{}), C.Cir.Cells.get.at(p, s, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, c)),
                Ce.get_none(p, s), Ce.get_other.at(p, s, t, C.Cir.Cells.none{}, c, e => ne(Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x}, s, t, e))))
        case WCon{True{}, +s} WCon{True{}, +t}:
          match m:
            case C.Cir.Cells.node{+lo, +hi}:
              Ce.get_other.at(p, s, t, hi, c, e => ne(Equal.cong(Word(p), Word(1n+p), x => WCon{True{}, x}, s, t, e)))
            case C.Cir.Cells.none{}:
              Equal.trans(C.Cir.Cell, C.Cir.Cell.zero(), C.Cir.Cells.get.at(p, s, C.Cir.Cells.none{}), C.Cir.Cells.get.at(p, s, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, c)),
                Ce.get_none(p, s), Ce.get_other.at(p, s, t, C.Cir.Cells.none{}, c, e => ne(Equal.cong(Word(p), Word(1n+p), x => WCon{True{}, x}, s, t, e))))
            case C.Cir.Cells.one{+d}:
              Equal.trans(C.Cir.Cell, C.Cir.Cell.zero(), C.Cir.Cells.get.at(p, s, C.Cir.Cells.none{}), C.Cir.Cells.get.at(p, s, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, c)),
                Ce.get_none(p, s), Ce.get_other.at(p, s, t, C.Cir.Cells.none{}, c, e => ne(Equal.cong(Word(p), Word(1n+p), x => WCon{True{}, x}, s, t, e))))
        case WCon{False{}, +s} WCon{True{}, +t}:
          match m:
            case C.Cir.Cells.node{+lo, +hi}:
              {==}
            case C.Cir.Cells.none{}:
              Ce.get_none(p, s)
            case C.Cir.Cells.one{+d}:
              Ce.get_none(p, s)
        case WCon{True{}, +s} WCon{False{}, +t}:
          match m:
            case C.Cir.Cells.node{+lo, +hi}:
              {==}
            case C.Cir.Cells.none{}:
              Ce.get_none(p, s)
            case C.Cir.Cells.one{+d}:
              Ce.get_none(p, s)

def Ce.get_other(+m: C.Cir.Cells, +j: U32, +i: U32, +c: C.Cir.Cell, ne: {j == i : U32} -> Empty) ->
  {C.Cir.Cells.get(m, j) == C.Cir.Cells.get(C.Cir.Cells.set(m, i, c), j) : C.Cir.Cell}:
  match j i:
    case U32{+v} U32{+w}:
      Ce.get_other.at(32n, v, w, m, c, e => ne(Equal.cong(Word(32n), U32, x => U32{x}, v, w, e)))


# U32 equality
# ------------

def W.eq.fc(c: Cmp, ab: Bool, bb: Bool, h: {Cmp.is_eq(Word.cmp.fin(ab, bb, c)) == True{} : Bool}) -> {Cmp.is_eq(c) == True{} : Bool}:
  match c:
    case LT{}:
      h
    case EQ{}:
      {==}
    case GT{}:
      h

def W.eq.fb(c: Cmp, ab: Bool, bb: Bool, h: {Cmp.is_eq(Word.cmp.fin(ab, bb, c)) == True{} : Bool}) -> {ab == bb : Bool}:
  match c:
    case LT{}:
      tf({ab == bb : Bool}, h)
    case EQ{}:
      match ab bb:
        case False{} False{}:
          {==}
        case False{} True{}:
          tf({False{} == True{} : Bool}, h)
        case True{} False{}:
          tf({True{} == False{} : Bool}, h)
        case True{} True{}:
          {==}
    case GT{}:
      tf({ab == bb : Bool}, h)

# words that compare EQ are equal
def W.eq(n: Nat, a: Word(n), b: Word(n), +h: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          +eb = W.eq.fb(Word.cmp(p, at, bt), ab, bb, h)
          +et = W.eq(p, at, bt, W.eq.fc(Word.cmp(p, at, bt), ab, bb, h))
          %eb : {WCon{ab, at} == WCon{_, bt} : Word(1n+p)}
          %et : {WCon{ab, at} == WCon{ab, _} : Word(1n+p)}
          {==}

def W.refl.b(b: Bool) -> {EQ{} == Bool.cmp(b, b) : Cmp}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def W.refl(n: Nat, a: Word(n)) -> {EQ{} == Word.cmp(n, a, a) : Cmp}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+(+p):
      match a:
        case WCon{+ab, +at}:
          %W.refl(p, at) : {EQ{} == Word.cmp.fin(ab, ab, _) : Cmp}
          W.refl.b(ab)

# U32s that is_eq says equal are equal
def U.eq_t(a: U32, b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      +e = W.eq(32n, x, y, h)
      %e : {U32{x} == U32{_} : U32}
      {==}

def U.refl(a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  match a:
    case U32{+x}:
      %W.refl(32n, x) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# U32s that is_eq says differ differ
def U.eq_f(+a: U32, +b: U32, h: {U32.is_eq(a, b) == False{} : Bool}, e: {a == b : U32}) -> Empty:
  +r = U.refl(a)
  +c = Equal.cong(U32, Bool, z => U32.is_eq(a, z), a, b, e)
  N.true_ne_false(Equal.trans(Bool, True{}, U32.is_eq(a, b), False{},
    Equal.trans(Bool, True{}, U32.is_eq(a, a), U32.is_eq(a, b), Equal.sym(Bool, U32.is_eq(a, a), True{}, r), c), h))

# Terms of cells
# --------------

# the parts that a cell of the tag reads give the same terms
def TE(tag: Nat, a2: Maybe<&2, C.Term>, b2: Maybe<&2, C.Term>, a3: Maybe<&2, C.Term>, b3: Maybe<&2, C.Term>, a4: Maybe<&2, C.Term>, b4: Maybe<&2, C.Term>) -> Type:
  match tag:
    case 0n:
      Unit
    case 1n:
      Unit
    case 2n:
      {a2 == b2 : Maybe<&2, C.Term>} & {a3 == b3 : Maybe<&2, C.Term>}
    case 3n:
      {a2 == b2 : Maybe<&2, C.Term>} & {a3 == b3 : Maybe<&2, C.Term>}
    case 4n:
      {a2 == b2 : Maybe<&2, C.Term>}
    case 5n:
      {a2 == b2 : Maybe<&2, C.Term>} & {a3 == b3 : Maybe<&2, C.Term>}
    case 6n:
      {a2 == b2 : Maybe<&2, C.Term>} & {a3 == b3 : Maybe<&2, C.Term>}
    case 7n:
      {a2 == b2 : Maybe<&2, C.Term>}
    case 8n:
      {a2 == b2 : Maybe<&2, C.Term>} & {a3 == b3 : Maybe<&2, C.Term>}
    case 9n:
      {a2 == b2 : Maybe<&2, C.Term>} & {a3 == b3 : Maybe<&2, C.Term>}
    case 10n:
      {a2 == b2 : Maybe<&2, C.Term>} & {a3 == b3 : Maybe<&2, C.Term>}
    case 11n:
      {a2 == b2 : Maybe<&2, C.Term>}
    case 12n:
      Unit
    case 13n:
      Unit
    case 14n:
      {a3 == b3 : Maybe<&2, C.Term>} & {a4 == b4 : Maybe<&2, C.Term>}
    case 15n:
      Unit
    case 16n:
      {a2 == b2 : Maybe<&2, C.Term>} & ({a3 == b3 : Maybe<&2, C.Term>} & {a4 == b4 : Maybe<&2, C.Term>})
    case 17n:
      Unit
    case 18n:
      {a2 == b2 : Maybe<&2, C.Term>} & ({a3 == b3 : Maybe<&2, C.Term>} & {a4 == b4 : Maybe<&2, C.Term>})
    case _:
      Unit

# all three parts give the same terms
def TE.all(tag: Nat, -a2: Maybe<&2, C.Term>, -b2: Maybe<&2, C.Term>, -a3: Maybe<&2, C.Term>, -b3: Maybe<&2, C.Term>, -a4: Maybe<&2, C.Term>, -b4: Maybe<&2, C.Term>,
  +e2: {a2 == b2 : Maybe<&2, C.Term>}, +e3: {a3 == b3 : Maybe<&2, C.Term>}, +e4: {a4 == b4 : Maybe<&2, C.Term>}) -> TE(tag, a2, b2, a3, b3, a4, b4):
  match tag:
    case 0n:
      Unit{}
    case 1n:
      Unit{}
    case 2n:
      (e2, e3)
    case 3n:
      (e2, e3)
    case 4n:
      e2
    case 5n:
      (e2, e3)
    case 6n:
      (e2, e3)
    case 7n:
      e2
    case 8n:
      (e2, e3)
    case 9n:
      (e2, e3)
    case 10n:
      (e2, e3)
    case 11n:
      e2
    case 12n:
      Unit{}
    case 13n:
      Unit{}
    case 14n:
      (e3, e4)
    case 15n:
      Unit{}
    case 16n:
      (e2, (e3, e4))
    case 17n:
      Unit{}
    case 18n:
      (e2, (e3, e4))
    case 19n+k:
      Unit{}

# tm.cell with parts that give the same terms
def TCell(tag: Nat, +q: C.Quan, +c: U32, +f2: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  -p2: Unit -> Maybe<&2, C.Term>, -p3: Unit -> Maybe<&2, C.Term>, -p4: Unit -> Maybe<&2, C.Term>, -r2: Unit -> Maybe<&2, C.Term>, -r3: Unit -> Maybe<&2, C.Term>, -r4: Unit -> Maybe<&2, C.Term>,
  h: TE(tag, p2(Unit{}), r2(Unit{}), p3(Unit{}), r3(Unit{}), p4(Unit{}), r4(Unit{}))) ->
  {T.tm.cell(tag, q, c, f2, ks, img, p2, p3, p4) == T.tm.cell(tag, q, c, f2, ks, img, r2, r3, r4) : Maybe<&2, C.Term>}:
  match tag:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      (e2, e3) = h
      %e2 : {T.tm.two(a => b => C.Term.Ann{a, b}, p2(Unit{}), p3(Unit{})) == T.tm.two(a => b => C.Term.Ann{a, b}, _, r3(Unit{})) : Maybe<&2, C.Term>}
      %e3 : {T.tm.two(a => b => C.Term.Ann{a, b}, p2(Unit{}), p3(Unit{})) == T.tm.two(a => b => C.Term.Ann{a, b}, p2(Unit{}), _) : Maybe<&2, C.Term>}
      {==}
    case 3n:
      (e2, e3) = h
      %e2 : {T.tm.two(a => b => C.Term.Let{q, a, b}, p2(Unit{}), p3(Unit{})) == T.tm.two(a => b => C.Term.Let{q, a, b}, _, r3(Unit{})) : Maybe<&2, C.Term>}
      %e3 : {T.tm.two(a => b => C.Term.Let{q, a, b}, p2(Unit{}), p3(Unit{})) == T.tm.two(a => b => C.Term.Let{q, a, b}, p2(Unit{}), _) : Maybe<&2, C.Term>}
      {==}
    case 4n:
      %h : {T.tm.one(a => C.Term.Typ{a}, p2(Unit{})) == T.tm.one(a => C.Term.Typ{a}, _) : Maybe<&2, C.Term>}
      {==}
    case 5n:
      (e2, e3) = h
      %e2 : {T.tm.two(a => b => C.Term.Min{a, b}, p2(Unit{}), p3(Unit{})) == T.tm.two(a => b => C.Term.Min{a, b}, _, r3(Unit{})) : Maybe<&2, C.Term>}
      %e3 : {T.tm.two(a => b => C.Term.Min{a, b}, p2(Unit{}), p3(Unit{})) == T.tm.two(a => b => C.Term.Min{a, b}, p2(Unit{}), _) : Maybe<&2, C.Term>}
      {==}
    case 6n:
      (e2, e3) = h
      %e2 : {T.tm.two(a => b => C.Term.All{q, a, b}, p2(Unit{}), p3(Unit{})) == T.tm.two(a => b => C.Term.All{q, a, b}, _, r3(Unit{})) : Maybe<&2, C.Term>}
      %e3 : {T.tm.two(a => b => C.Term.All{q, a, b}, p2(Unit{}), p3(Unit{})) == T.tm.two(a => b => C.Term.All{q, a, b}, p2(Unit{}), _) : Maybe<&2, C.Term>}
      {==}
    case 7n:
      %h : {T.tm.one(a => C.Term.Lam{q, a}, p2(Unit{})) == T.tm.one(a => C.Term.Lam{q, a}, _) : Maybe<&2, C.Term>}
      {==}
    case 8n:
      (e2, e3) = h
      %e2 : {T.tm.two(a => b => C.Term.App{q, a, b}, p2(Unit{}), p3(Unit{})) == T.tm.two(a => b => C.Term.App{q, a, b}, _, r3(Unit{})) : Maybe<&2, C.Term>}
      %e3 : {T.tm.two(a => b => C.Term.App{q, a, b}, p2(Unit{}), p3(Unit{})) == T.tm.two(a => b => C.Term.App{q, a, b}, p2(Unit{}), _) : Maybe<&2, C.Term>}
      {==}
    case 9n:
      (e2, e3) = h
      %e2 : {T.tm.two(a => b => C.Term.Sig{q, a, b}, p2(Unit{}), p3(Unit{})) == T.tm.two(a => b => C.Term.Sig{q, a, b}, _, r3(Unit{})) : Maybe<&2, C.Term>}
      %e3 : {T.tm.two(a => b => C.Term.Sig{q, a, b}, p2(Unit{}), p3(Unit{})) == T.tm.two(a => b => C.Term.Sig{q, a, b}, p2(Unit{}), _) : Maybe<&2, C.Term>}
      {==}
    case 10n:
      (e2, e3) = h
      %e2 : {T.tm.two(a => b => C.Term.Tup{q, a, b}, p2(Unit{}), p3(Unit{})) == T.tm.two(a => b => C.Term.Tup{q, a, b}, _, r3(Unit{})) : Maybe<&2, C.Term>}
      %e3 : {T.tm.two(a => b => C.Term.Tup{q, a, b}, p2(Unit{}), p3(Unit{})) == T.tm.two(a => b => C.Term.Tup{q, a, b}, p2(Unit{}), _) : Maybe<&2, C.Term>}
      {==}
    case 11n:
      %h : {T.tm.one(a => C.Term.Prj{a}, p2(Unit{})) == T.tm.one(a => C.Term.Prj{a}, _) : Maybe<&2, C.Term>}
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n:
      (e3, e4) = h
      %e3 : {T.tm.mat(T.tm.name(ks, f2), p3(Unit{}), p4(Unit{})) == T.tm.mat(T.tm.name(ks, f2), _, r4(Unit{})) : Maybe<&2, C.Term>}
      %e4 : {T.tm.mat(T.tm.name(ks, f2), p3(Unit{}), p4(Unit{})) == T.tm.mat(T.tm.name(ks, f2), p3(Unit{}), _) : Maybe<&2, C.Term>}
      {==}
    case 15n:
      {==}
    case 16n:
      (e2, e34) = h
      (e3, e4) = e34
      %e2 : {T.tm.three(a => b => t => C.Term.Eql{a, b, t}, p2(Unit{}), p3(Unit{}), p4(Unit{})) == T.tm.three(a => b => t => C.Term.Eql{a, b, t}, _, r3(Unit{}), r4(Unit{})) : Maybe<&2, C.Term>}
      %e3 : {T.tm.three(a => b => t => C.Term.Eql{a, b, t}, p2(Unit{}), p3(Unit{}), p4(Unit{})) == T.tm.three(a => b => t => C.Term.Eql{a, b, t}, p2(Unit{}), _, r4(Unit{})) : Maybe<&2, C.Term>}
      %e4 : {T.tm.three(a => b => t => C.Term.Eql{a, b, t}, p2(Unit{}), p3(Unit{}), p4(Unit{})) == T.tm.three(a => b => t => C.Term.Eql{a, b, t}, p2(Unit{}), p3(Unit{}), _) : Maybe<&2, C.Term>}
      {==}
    case 17n:
      {==}
    case 18n:
      (e2, e34) = h
      (e3, e4) = e34
      %e2 : {T.tm.three(a => b => t => C.Term.Rwt{a, b, t}, p2(Unit{}), p3(Unit{}), p4(Unit{})) == T.tm.three(a => b => t => C.Term.Rwt{a, b, t}, _, r3(Unit{}), r4(Unit{})) : Maybe<&2, C.Term>}
      %e3 : {T.tm.three(a => b => t => C.Term.Rwt{a, b, t}, p2(Unit{}), p3(Unit{}), p4(Unit{})) == T.tm.three(a => b => t => C.Term.Rwt{a, b, t}, p2(Unit{}), _, r4(Unit{})) : Maybe<&2, C.Term>}
      %e4 : {T.tm.three(a => b => t => C.Term.Rwt{a, b, t}, p2(Unit{}), p3(Unit{}), p4(Unit{})) == T.tm.three(a => b => t => C.Term.Rwt{a, b, t}, p2(Unit{}), p3(Unit{}), _) : Maybe<&2, C.Term>}
      {==}
    case 19n+k:
      {==}

# one level of tm.of, on two cell maps whose cell c has the same tag,
# quantity and parts, and whose parts give the same terms
def TOF(+g: Nat, +m: C.Cir.Cells, +m2: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32,
  et: {U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), 63) == U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m2, c)), 63) : U32},
  eq: {U32.and(U32.shrn(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), 6n), 3) == U32.and(U32.shrn(C.Cir.Cell.get(0n, C.Cir.Cells.get(m2, c)), 6n), 3) : U32},
  e2: {C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)) == C.Cir.Cell.get(2n, C.Cir.Cells.get(m2, c)) : U32},
  e3: {C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)) == C.Cir.Cell.get(3n, C.Cir.Cells.get(m2, c)) : U32},
  e4: {C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c)) == C.Cir.Cell.get(4n, C.Cir.Cells.get(m2, c)) : U32},
  h: TE(U32.to_nat(U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), 63)),
    T.tm.of(g, m, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), T.tm.of(g, m2, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))),
    T.tm.of(g, m, ks, img, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))), T.tm.of(g, m2, ks, img, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))),
    T.tm.of(g, m, ks, img, C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c))), T.tm.of(g, m2, ks, img, C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c))))) ->
  {T.tm.of(1n+g, m, ks, img, c) == T.tm.of(1n+g, m2, ks, img, c) : Maybe<&2, C.Term>}:
  +x0 = C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c))
  +x2 = C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))
  +x3 = C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))
  +x4 = C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c))
  +y0 = C.Cir.Cell.get(0n, C.Cir.Cells.get(m2, c))
  +y2 = C.Cir.Cell.get(2n, C.Cir.Cells.get(m2, c))
  +y3 = C.Cir.Cell.get(3n, C.Cir.Cells.get(m2, c))
  +y4 = C.Cir.Cell.get(4n, C.Cir.Cells.get(m2, c))
  +lhs = T.tm.cell(U32.to_nat(U32.and(x0, 63)), T.tm.quan(U32.and(U32.shrn(x0, 6n), 3)), c, x2, ks, img,
    u => T.tm.of(g, m, ks, img, x2), u => T.tm.of(g, m, ks, img, x3), u => T.tm.of(g, m, ks, img, x4))
  %et : {lhs == T.tm.cell(U32.to_nat(_), T.tm.quan(U32.and(U32.shrn(y0, 6n), 3)), c, y2, ks, img,
    u => T.tm.of(g, m2, ks, img, y2), u => T.tm.of(g, m2, ks, img, y3), u => T.tm.of(g, m2, ks, img, y4)) : Maybe<&2, C.Term>}
  %eq : {lhs == T.tm.cell(U32.to_nat(U32.and(x0, 63)), T.tm.quan(_), c, y2, ks, img,
    u => T.tm.of(g, m2, ks, img, y2), u => T.tm.of(g, m2, ks, img, y3), u => T.tm.of(g, m2, ks, img, y4)) : Maybe<&2, C.Term>}
  %e2 : {lhs == T.tm.cell(U32.to_nat(U32.and(x0, 63)), T.tm.quan(U32.and(U32.shrn(x0, 6n), 3)), c, _, ks, img,
    u => T.tm.of(g, m2, ks, img, _), u => T.tm.of(g, m2, ks, img, y3), u => T.tm.of(g, m2, ks, img, y4)) : Maybe<&2, C.Term>}
  %e3 : {lhs == T.tm.cell(U32.to_nat(U32.and(x0, 63)), T.tm.quan(U32.and(U32.shrn(x0, 6n), 3)), c, x2, ks, img,
    u => T.tm.of(g, m2, ks, img, x2), u => T.tm.of(g, m2, ks, img, _), u => T.tm.of(g, m2, ks, img, y4)) : Maybe<&2, C.Term>}
  %e4 : {lhs == T.tm.cell(U32.to_nat(U32.and(x0, 63)), T.tm.quan(U32.and(U32.shrn(x0, 6n), 3)), c, x2, ks, img,
    u => T.tm.of(g, m2, ks, img, x2), u => T.tm.of(g, m2, ks, img, x3), u => T.tm.of(g, m2, ks, img, _)) : Maybe<&2, C.Term>}
  TCell(U32.to_nat(U32.and(x0, 63)), T.tm.quan(U32.and(U32.shrn(x0, 6n), 3)), c, x2, ks, img,
    u => T.tm.of(g, m, ks, img, x2), u => T.tm.of(g, m, ks, img, x3), u => T.tm.of(g, m, ks, img, x4),
    u => T.tm.of(g, m2, ks, img, x2), u => T.tm.of(g, m2, ks, img, x3), u => T.tm.of(g, m2, ks, img, x4), h)

# two cells with the same tag, quantity and parts
def AgC(+x: C.Cir.Cell, +y: C.Cir.Cell) -> Data:
  Sigma<&2, &2, {U32.and(C.Cir.Cell.get(0n, x), 63) == U32.and(C.Cir.Cell.get(0n, y), 63) : U32}, _ =>
  Sigma<&2, &2, {U32.and(U32.shrn(C.Cir.Cell.get(0n, x), 6n), 3) == U32.and(U32.shrn(C.Cir.Cell.get(0n, y), 6n), 3) : U32}, _ =>
  Sigma<&2, &2, {C.Cir.Cell.get(2n, x) == C.Cir.Cell.get(2n, y) : U32}, _ =>
  Sigma<&2, &2, {C.Cir.Cell.get(3n, x) == C.Cir.Cell.get(3n, y) : U32}, _ =>
  {C.Cir.Cell.get(4n, x) == C.Cir.Cell.get(4n, y) : U32}>>>>

def AgC.t(-x: C.Cir.Cell, -y: C.Cir.Cell, a: AgC(x, y)) -> {U32.and(C.Cir.Cell.get(0n, x), 63) == U32.and(C.Cir.Cell.get(0n, y), 63) : U32}:
  (e, r) = a
  e

def AgC.q(-x: C.Cir.Cell, -y: C.Cir.Cell, a: AgC(x, y)) -> {U32.and(U32.shrn(C.Cir.Cell.get(0n, x), 6n), 3) == U32.and(U32.shrn(C.Cir.Cell.get(0n, y), 6n), 3) : U32}:
  (e0, r0) = a
  (e, r) = r0
  e

def AgC.f2(-x: C.Cir.Cell, -y: C.Cir.Cell, a: AgC(x, y)) -> {C.Cir.Cell.get(2n, x) == C.Cir.Cell.get(2n, y) : U32}:
  (e0, r0) = a
  (e1, r1) = r0
  (e, r) = r1
  e

def AgC.f3(-x: C.Cir.Cell, -y: C.Cir.Cell, a: AgC(x, y)) -> {C.Cir.Cell.get(3n, x) == C.Cir.Cell.get(3n, y) : U32}:
  (e0, r0) = a
  (e1, r1) = r0
  (e2, r2) = r1
  (e, r) = r2
  e

def AgC.f4(-x: C.Cir.Cell, -y: C.Cir.Cell, a: AgC(x, y)) -> {C.Cir.Cell.get(4n, x) == C.Cir.Cell.get(4n, y) : U32}:
  (e0, r0) = a
  (e1, r1) = r0
  (e2, r2) = r1
  (e3, e) = r2
  e

def AgC.refl(+x: C.Cir.Cell) -> AgC(x, x):
  ({==}, ({==}, ({==}, ({==}, {==}))))

def AgC.cong(+x: C.Cir.Cell, -y: C.Cir.Cell, e: {x == y : C.Cir.Cell}) -> AgC(x, y):
  %e : AgC(x, _)
  AgC.refl(x)

# a cell set to x2, which has the tag, quantity and parts of the cell d,
# keeps the tag, quantity and parts of every cell
def Ag.at(b: Bool, +m: C.Cir.Cells, +d: U32, +x2: C.Cir.Cell, +ag: AgC(C.Cir.Cells.get(m, d), x2), +c: U32,
  eb: {U32.is_eq(c, d) == b : Bool}) -> AgC(C.Cir.Cells.get(m, c), C.Cir.Cells.get(C.Cir.Cells.set(m, d, x2), c)):
  match b:
    case True{}:
      +e = U.eq_t(c, d, eb)
      %Equal.sym(U32, c, d, e) : AgC(C.Cir.Cells.get(m, _), C.Cir.Cells.get(C.Cir.Cells.set(m, d, x2), _))
      %Equal.sym(C.Cir.Cell, C.Cir.Cells.get(C.Cir.Cells.set(m, d, x2), d), x2, Ce.get_set(m, d, x2)) : AgC(C.Cir.Cells.get(m, d), _)
      ag
    case False{}:
      AgC.cong(C.Cir.Cells.get(m, c), C.Cir.Cells.get(C.Cir.Cells.set(m, d, x2), c), Ce.get_other(m, c, d, x2, e => U.eq_f(c, d, eb, e)))

def Ag(+m: C.Cir.Cells, +d: U32, +x2: C.Cir.Cell, +ag: AgC(C.Cir.Cells.get(m, d), x2), +c: U32) ->
  AgC(C.Cir.Cells.get(m, c), C.Cir.Cells.get(C.Cir.Cells.set(m, d, x2), c)):
  Ag.at(U32.is_eq(c, d), m, d, x2, ag, c, {==})

# a set of a cell that keeps its tag, quantity and parts keeps every term
def TFag(f: Nat, +m: C.Cir.Cells, +d: U32, +x2: C.Cir.Cell, +ag: AgC(C.Cir.Cells.get(m, d), x2), +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +c: U32) -> {T.tm.of(f, m, ks, img, c) == T.tm.of(f, C.Cir.Cells.set(m, d, x2), ks, img, c) : Maybe<&2, C.Term>}:
  match f:
    case 0n:
      {==}
    case 1n+(+g):
      +m2 = C.Cir.Cells.set(m, d, x2)
      +x = C.Cir.Cells.get(m, c)
      +y = C.Cir.Cells.get(m2, c)
      +a = Ag(m, d, x2, ag, c)
      TOF(g, m, m2, ks, img, c, AgC.t(x, y, a), AgC.q(x, y, a), AgC.f2(x, y, a), AgC.f3(x, y, a), AgC.f4(x, y, a),
        TE.all(U32.to_nat(U32.and(C.Cir.Cell.get(0n, x), 63)),
          T.tm.of(g, m, ks, img, C.Cir.Cell.get(2n, x)), T.tm.of(g, m2, ks, img, C.Cir.Cell.get(2n, x)),
          T.tm.of(g, m, ks, img, C.Cir.Cell.get(3n, x)), T.tm.of(g, m2, ks, img, C.Cir.Cell.get(3n, x)),
          T.tm.of(g, m, ks, img, C.Cir.Cell.get(4n, x)), T.tm.of(g, m2, ks, img, C.Cir.Cell.get(4n, x)),
          TFag(g, m, d, x2, ag, ks, img, C.Cir.Cell.get(2n, x)), TFag(g, m, d, x2, ag, ks, img, C.Cir.Cell.get(3n, x)),
          TFag(g, m, d, x2, ag, ks, img, C.Cir.Cell.get(4n, x))))

# field 1 of the cell d set to v
def Set1(+m: C.Cir.Cells, +d: U32, v: U32) -> C.Cir.Cells:
  C.Cir.Cells.set(m, d, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, d), v))

def AgC.set1(+x: C.Cir.Cell, +v: U32) -> AgC(x, C.Cir.Cell.set(1n, x, v)):
  match x:
    case C.Cir.Cell{+a, +b, +p, +q, +r}:
      AgC.refl(C.Cir.Cell{a, b, p, q, r})

# a set of field 1 (a count or a link) keeps every term
def TF1(f: Nat, +m: C.Cir.Cells, +d: U32, +v: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32) ->
  {T.tm.of(f, m, ks, img, c) == T.tm.of(f, Set1(m, d, v), ks, img, c) : Maybe<&2, C.Term>}:
  TFag(f, m, d, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, d), v), AgC.set1(C.Cir.Cells.get(m, d), v), ks, img, c)

# Bits
# ----

def B.head(n: Nat, w: Word(1n+n)) -> Bool:
  match w:
    case WCon{b, _}:
      b

def B.tail(n: Nat, w: Word(1n+n)) -> Word(n):
  match w:
    case WCon{_, t}:
      t

def B.or_and(b: Bool, c: Bool, mk: Bool, h: {Bool.and(c, mk) == False{} : Bool}) -> {Bool.and(b, mk) == Bool.and(Bool.or(b, c), mk) : Bool}:
  match b:
    case False{}:
      Equal.sym(Bool, Bool.and(c, mk), False{}, h)
    case True{}:
      match mk:
        case False{}:
          {==}
        case True{}:
          {==}

# an or with bits outside the mask mw keeps the bits of the mask
def W.or_and(n: Nat, w: Word(n), cw: Word(n), mw: Word(n), h: {Word.and(n, cw, mw) == Word.zero(n) : Word(n)}) ->
  {Word.and(n, w, mw) == Word.and(n, Word.or(n, w, cw), mw) : Word(n)}:
  match n:
    case 0n:
      match w cw mw:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match w cw mw:
        case WCon{+b, +wt} WCon{+c, +ct} WCon{+mk, +mt}:
          +h2 = h
          +eh = Equal.cong(Word(1n+p), Bool, x => B.head(p, x), WCon{Bool.and(c, mk), Word.and(p, ct, mt)}, WCon{False{}, Word.zero(p)}, h2)
          +et = Equal.cong(Word(1n+p), Word(p), x => B.tail(p, x), WCon{Bool.and(c, mk), Word.and(p, ct, mt)}, WCon{False{}, Word.zero(p)}, h2)
          %B.or_and(b, c, mk, eh) : {WCon{Bool.and(b, mk), Word.and(p, wt, mt)} == WCon{_, Word.and(p, Word.or(p, wt, ct), mt)} : Word(1n+p)}
          %W.or_and(p, wt, ct, mt, et) : {WCon{Bool.and(b, mk), Word.and(p, wt, mt)} == WCon{Bool.and(b, mk), _} : Word(1n+p)}
          {==}

def U.w(u: U32) -> Word(32n):
  match u:
    case U32{w}:
      w

def U.or_and(+x: U32, +c: U32, +mk: U32, h: {U32.and(c, mk) == 0 : U32}) -> {U32.and(x, mk) == U32.and(U32.or(x, c), mk) : U32}:
  match x c mk:
    case U32{+w} U32{+cw} U32{+mw}:
      +h2 = Equal.cong(U32, Word(32n), u => U.w(u), U32{Word.and(32n, cw, mw)}, 0, h)
      %W.or_and(32n, w, cw, mw, h2) : {U32{Word.and(32n, w, mw)} == U32{_} : U32}
      {==}

def W.pad_or(p: Nat, a: Word(p), b: Word(p)) ->
  {Word.or(1n+p, Word.shr.pad(p, a), Word.shr.pad(p, b)) == Word.shr.pad(p, Word.or(p, a, b)) : Word(1n+p)}:
  match p:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+q):
      match a b:
        case WCon{+a1, +at} WCon{+b1, +bt}:
          %W.pad_or(q, at, bt) : {WCon{Bool.or(a1, b1), Word.or(1n+q, Word.shr.pad(q, at), Word.shr.pad(q, bt))} == WCon{Bool.or(a1, b1), _} : Word(2n+q)}
          {==}

def W.shr_or(n: Nat, x: Word(n), y: Word(n)) -> {Word.or(n, Word.shr(n, x), Word.shr(n, y)) == Word.shr(n, Word.or(n, x, y)) : Word(n)}:
  match n:
    case 0n:
      match x y:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match x y:
        case WCon{a, +xt} WCon{b, +yt}:
          W.pad_or(p, xt, yt)

def U.shr_or(a: U32, b: U32) -> {U32.or(U32.shr(a), U32.shr(b)) == U32.shr(U32.or(a, b)) : U32}:
  match a b:
    case U32{+x} U32{+y}:
      %W.shr_or(32n, x, y) : {U32{Word.or(32n, Word.shr(32n, x), Word.shr(32n, y))} == U32{_} : U32}
      {==}

def U.shrn_or(+a: U32, +b: U32, n: Nat) -> {U32.or(U32.shrn(a, n), U32.shrn(b, n)) == U32.shrn(U32.or(a, b), n) : U32}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      %U.shrn_or(a, b, k) : {U32.or(U32.shr(U32.shrn(a, k)), U32.shr(U32.shrn(b, k))) == U32.shr(_) : U32}
      U.shr_or(U32.shrn(a, k), U32.shrn(b, k))

# a flag fl outside the bits of the tag and the quantity keeps them
def AgC.flag(+x: C.Cir.Cell, +fl: U32, h1: {U32.and(fl, 63) == 0 : U32}, h2: {U32.and(U32.shrn(fl, 6n), 3) == 0 : U32}) ->
  AgC(x, C.Cir.Cell.set(0n, x, U32.or(C.Cir.Cell.get(0n, x), fl))):
  match x:
    case C.Cir.Cell{+a, +b, +p, +q, +r}:
      +e1 = U.or_and(U32.shrn(a, 6n), U32.shrn(fl, 6n), 3, h2)
      +o = U32.or(U32.shrn(a, 6n), U32.shrn(fl, 6n))
      +e2 = Equal.trans(U32, U32.and(U32.shrn(a, 6n), 3), U32.and(o, 3), U32.and(U32.shrn(U32.or(a, fl), 6n), 3), e1,
        Equal.cong(U32, U32, z => U32.and(z, 3), o, U32.shrn(U32.or(a, fl), 6n), U.shrn_or(a, fl, 6n)))
      (U.or_and(a, fl, 63, h1), (e2, ({==}, ({==}, {==}))))

# the flag fl set in field 0 of the cell d
def SetF(+m: C.Cir.Cells, +d: U32, +fl: U32) -> C.Cir.Cells:
  C.Cir.Cells.set(m, d, C.Cir.Cell.set(0n, C.Cir.Cells.get(m, d), U32.or(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, d)), fl)))

# a flag outside the tag and the quantity keeps every term
def TFl(f: Nat, +m: C.Cir.Cells, +d: U32, +fl: U32, h1: {U32.and(fl, 63) == 0 : U32}, h2: {U32.and(U32.shrn(fl, 6n), 3) == 0 : U32},
  +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32) ->
  {T.tm.of(f, m, ks, img, c) == T.tm.of(f, SetF(m, d, fl), ks, img, c) : Maybe<&2, C.Term>}:
  +x = C.Cir.Cells.get(m, d)
  TFag(f, m, d, C.Cir.Cell.set(0n, x, U32.or(C.Cir.Cell.get(0n, x), fl)), AgC.flag(x, fl, h1, h2), ks, img, c)

# Cells that a term reads
# -----------------------

# c is in the list L
def Mem(+c: U32, L: List<&2, U32>) -> Bool:
  match L:
    case Nil{}:
      False{}
    case Con{h, t}:
      U32.is_eq(c, h) || Mem(c, t)

def RdIn.cell(tag: Nat, r2: Bool, r3: Bool, r4: Bool) -> Bool:
  match tag:
    case 0n:
      True{}
    case 1n:
      True{}
    case 2n:
      r2 && r3
    case 3n:
      r2 && r3
    case 4n:
      r2
    case 5n:
      r2 && r3
    case 6n:
      r2 && r3
    case 7n:
      r2
    case 8n:
      r2 && r3
    case 9n:
      r2 && r3
    case 10n:
      r2 && r3
    case 11n:
      r2
    case 12n:
      True{}
    case 13n:
      True{}
    case 14n:
      r3 && r4
    case 15n:
      True{}
    case 16n:
      r2 && (r3 && r4)
    case 17n:
      True{}
    case 18n:
      r2 && (r3 && r4)
    case 19n+k:
      True{}

# every cell that tm.of reads from c, within f levels, is in L
def RdIn(f: Nat, +m: C.Cir.Cells, +c: U32, +L: List<&2, U32>) -> Bool:
  match f:
    case 0n:
      True{}
    case 1n+(+g):
      +x = C.Cir.Cells.get(m, c)
      Mem(c, L) && RdIn.cell(U32.to_nat(U32.and(C.Cir.Cell.get(0n, x), 63)), RdIn(g, m, C.Cir.Cell.get(2n, x), L),
        RdIn(g, m, C.Cir.Cell.get(3n, x), L), RdIn(g, m, C.Cir.Cell.get(4n, x), L))

def Bo.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def Bo.and_r(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      tf({b == True{} : Bool}, h)

# the parts that RdIn.cell asks give the same terms
def TE.rd(tag: Nat, +r2: Bool, +r3: Bool, +r4: Bool, -a2: Maybe<&2, C.Term>, -b2: Maybe<&2, C.Term>, -a3: Maybe<&2, C.Term>, -b3: Maybe<&2, C.Term>, -a4: Maybe<&2, C.Term>, -b4: Maybe<&2, C.Term>,
  h: {RdIn.cell(tag, r2, r3, r4) == True{} : Bool},
  i2: {r2 == True{} : Bool} -> {a2 == b2 : Maybe<&2, C.Term>}, i3: {r3 == True{} : Bool} -> {a3 == b3 : Maybe<&2, C.Term>},
  i4: {r4 == True{} : Bool} -> {a4 == b4 : Maybe<&2, C.Term>}) -> TE(tag, a2, b2, a3, b3, a4, b4):
  match tag:
    case 0n:
      Unit{}
    case 1n:
      Unit{}
    case 2n:
      +h2 = h
      (i2(Bo.and_l(r2, r3, h2)), i3(Bo.and_r(r2, r3, h2)))
    case 3n:
      +h2 = h
      (i2(Bo.and_l(r2, r3, h2)), i3(Bo.and_r(r2, r3, h2)))
    case 4n:
      i2(h)
    case 5n:
      +h2 = h
      (i2(Bo.and_l(r2, r3, h2)), i3(Bo.and_r(r2, r3, h2)))
    case 6n:
      +h2 = h
      (i2(Bo.and_l(r2, r3, h2)), i3(Bo.and_r(r2, r3, h2)))
    case 7n:
      i2(h)
    case 8n:
      +h2 = h
      (i2(Bo.and_l(r2, r3, h2)), i3(Bo.and_r(r2, r3, h2)))
    case 9n:
      +h2 = h
      (i2(Bo.and_l(r2, r3, h2)), i3(Bo.and_r(r2, r3, h2)))
    case 10n:
      +h2 = h
      (i2(Bo.and_l(r2, r3, h2)), i3(Bo.and_r(r2, r3, h2)))
    case 11n:
      i2(h)
    case 12n:
      Unit{}
    case 13n:
      Unit{}
    case 14n:
      +h2 = h
      (i3(Bo.and_l(r3, r4, h2)), i4(Bo.and_r(r3, r4, h2)))
    case 15n:
      Unit{}
    case 16n:
      +h2 = h
      +h3 = Bo.and_r(r2, Bool.and(r3, r4), h2)
      (i2(Bo.and_l(r2, Bool.and(r3, r4), h2)), (i3(Bo.and_l(r3, r4, h3)), i4(Bo.and_r(r3, r4, h3))))
    case 17n:
      Unit{}
    case 18n:
      +h2 = h
      +h3 = Bo.and_r(r2, Bool.and(r3, r4), h2)
      (i2(Bo.and_l(r2, Bool.and(r3, r4), h2)), (i3(Bo.and_l(r3, r4, h3)), i4(Bo.and_r(r3, r4, h3))))
    case 19n+k:
      Unit{}

def RdIn.cell.mono(tag: Nat, +r2: Bool, +r3: Bool, +r4: Bool, +s2: Bool, +s3: Bool, +s4: Bool,
  h: {RdIn.cell(tag, r2, r3, r4) == True{} : Bool},
  i2: {r2 == True{} : Bool} -> {s2 == True{} : Bool}, i3: {r3 == True{} : Bool} -> {s3 == True{} : Bool},
  i4: {r4 == True{} : Bool} -> {s4 == True{} : Bool}) -> {RdIn.cell(tag, s2, s3, s4) == True{} : Bool}:
  match tag:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      +h2 = h
      +e2 = i2(Bo.and_l(r2, r3, h2))
      +e3 = i3(Bo.and_r(r2, r3, h2))
      %Equal.sym(Bool, s2, True{}, e2) : {Bool.and(_, s3) == True{} : Bool}
      e3
    case 3n:
      +h2 = h
      +e2 = i2(Bo.and_l(r2, r3, h2))
      +e3 = i3(Bo.and_r(r2, r3, h2))
      %Equal.sym(Bool, s2, True{}, e2) : {Bool.and(_, s3) == True{} : Bool}
      e3
    case 4n:
      i2(h)
    case 5n:
      +h2 = h
      +e2 = i2(Bo.and_l(r2, r3, h2))
      +e3 = i3(Bo.and_r(r2, r3, h2))
      %Equal.sym(Bool, s2, True{}, e2) : {Bool.and(_, s3) == True{} : Bool}
      e3
    case 6n:
      +h2 = h
      +e2 = i2(Bo.and_l(r2, r3, h2))
      +e3 = i3(Bo.and_r(r2, r3, h2))
      %Equal.sym(Bool, s2, True{}, e2) : {Bool.and(_, s3) == True{} : Bool}
      e3
    case 7n:
      i2(h)
    case 8n:
      +h2 = h
      +e2 = i2(Bo.and_l(r2, r3, h2))
      +e3 = i3(Bo.and_r(r2, r3, h2))
      %Equal.sym(Bool, s2, True{}, e2) : {Bool.and(_, s3) == True{} : Bool}
      e3
    case 9n:
      +h2 = h
      +e2 = i2(Bo.and_l(r2, r3, h2))
      +e3 = i3(Bo.and_r(r2, r3, h2))
      %Equal.sym(Bool, s2, True{}, e2) : {Bool.and(_, s3) == True{} : Bool}
      e3
    case 10n:
      +h2 = h
      +e2 = i2(Bo.and_l(r2, r3, h2))
      +e3 = i3(Bo.and_r(r2, r3, h2))
      %Equal.sym(Bool, s2, True{}, e2) : {Bool.and(_, s3) == True{} : Bool}
      e3
    case 11n:
      i2(h)
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n:
      +h2 = h
      +e3 = i3(Bo.and_l(r3, r4, h2))
      +e4 = i4(Bo.and_r(r3, r4, h2))
      %Equal.sym(Bool, s3, True{}, e3) : {Bool.and(_, s4) == True{} : Bool}
      e4
    case 15n:
      {==}
    case 16n:
      +h2 = h
      +h3 = Bo.and_r(r2, Bool.and(r3, r4), h2)
      +e2 = i2(Bo.and_l(r2, Bool.and(r3, r4), h2))
      +e3 = i3(Bo.and_l(r3, r4, h3))
      +e4 = i4(Bo.and_r(r3, r4, h3))
      %Equal.sym(Bool, s2, True{}, e2) : {Bool.and(_, Bool.and(s3, s4)) == True{} : Bool}
      %Equal.sym(Bool, s3, True{}, e3) : {Bool.and(True{}, Bool.and(_, s4)) == True{} : Bool}
      e4
    case 17n:
      {==}
    case 18n:
      +h2 = h
      +h3 = Bo.and_r(r2, Bool.and(r3, r4), h2)
      +e2 = i2(Bo.and_l(r2, Bool.and(r3, r4), h2))
      +e3 = i3(Bo.and_l(r3, r4, h3))
      +e4 = i4(Bo.and_r(r3, r4, h3))
      %Equal.sym(Bool, s2, True{}, e2) : {Bool.and(_, Bool.and(s3, s4)) == True{} : Bool}
      %Equal.sym(Bool, s3, True{}, e3) : {Bool.and(True{}, Bool.and(_, s4)) == True{} : Bool}
      e4
    case 19n+k:
      {==}

# a cell in L is not the cell s, which is not
def Mem.ne(+c: U32, +s: U32, +L: List<&2, U32>, +hm: {Mem(c, L) == True{} : Bool}, +hs: {Mem(s, L) == False{} : Bool},
  e: {c == s : U32}) -> Empty:
  +ec = Equal.cong(U32, Bool, z => Mem(z, L), c, s, e)
  N.true_ne_false(Equal.trans(Bool, True{}, Mem(s, L), False{},
    Equal.trans(Bool, True{}, Mem(c, L), Mem(s, L), Equal.sym(Bool, Mem(c, L), True{}, hm), ec), hs))

# a set of a cell outside L keeps the term of a cell that reads only cells of L
def TFo(f: Nat, +m: C.Cir.Cells, +s: U32, +x2: C.Cir.Cell, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +L: List<&2, U32>, +c: U32, h: {RdIn(f, m, c, L) == True{} : Bool}, +hs: {Mem(s, L) == False{} : Bool}) ->
  {T.tm.of(f, m, ks, img, c) == T.tm.of(f, C.Cir.Cells.set(m, s, x2), ks, img, c) : Maybe<&2, C.Term>}:
  match f:
    case 0n:
      {==}
    case 1n+(+g):
      +m2 = C.Cir.Cells.set(m, s, x2)
      +x = C.Cir.Cells.get(m, c)
      +y = C.Cir.Cells.get(m2, c)
      +x2p = C.Cir.Cell.get(2n, x)
      +x3p = C.Cir.Cell.get(3n, x)
      +x4p = C.Cir.Cell.get(4n, x)
      +tag = U32.to_nat(U32.and(C.Cir.Cell.get(0n, x), 63))
      +h2 = h
      +hm = Bo.and_l(Mem(c, L), RdIn.cell(tag, RdIn(g, m, x2p, L), RdIn(g, m, x3p, L), RdIn(g, m, x4p, L)), h2)
      +hr = Bo.and_r(Mem(c, L), RdIn.cell(tag, RdIn(g, m, x2p, L), RdIn(g, m, x3p, L), RdIn(g, m, x4p, L)), h2)
      +a = AgC.cong(x, y, Ce.get_other(m, c, s, x2, e => Mem.ne(c, s, L, hm, hs, e)))
      TOF(g, m, m2, ks, img, c, AgC.t(x, y, a), AgC.q(x, y, a), AgC.f2(x, y, a), AgC.f3(x, y, a), AgC.f4(x, y, a),
        TE.rd(tag, RdIn(g, m, x2p, L), RdIn(g, m, x3p, L), RdIn(g, m, x4p, L),
          T.tm.of(g, m, ks, img, x2p), T.tm.of(g, m2, ks, img, x2p), T.tm.of(g, m, ks, img, x3p), T.tm.of(g, m2, ks, img, x3p),
          T.tm.of(g, m, ks, img, x4p), T.tm.of(g, m2, ks, img, x4p), hr,
          e2 => TFo(g, m, s, x2, ks, img, L, x2p, e2, hs), e3 => TFo(g, m, s, x2, ks, img, L, x3p, e3, hs),
          e4 => TFo(g, m, s, x2, ks, img, L, x4p, e4, hs)))

# and the cells it reads are still those of L
def RdF(f: Nat, +m: C.Cir.Cells, +s: U32, +x2: C.Cir.Cell, +L: List<&2, U32>, +c: U32, h: {RdIn(f, m, c, L) == True{} : Bool},
  +hs: {Mem(s, L) == False{} : Bool}) -> {RdIn(f, C.Cir.Cells.set(m, s, x2), c, L) == True{} : Bool}:
  match f:
    case 0n:
      {==}
    case 1n+(+g):
      +m2 = C.Cir.Cells.set(m, s, x2)
      +x = C.Cir.Cells.get(m, c)
      +x2p = C.Cir.Cell.get(2n, x)
      +x3p = C.Cir.Cell.get(3n, x)
      +x4p = C.Cir.Cell.get(4n, x)
      +tag = U32.to_nat(U32.and(C.Cir.Cell.get(0n, x), 63))
      +h2 = h
      +hm = Bo.and_l(Mem(c, L), RdIn.cell(tag, RdIn(g, m, x2p, L), RdIn(g, m, x3p, L), RdIn(g, m, x4p, L)), h2)
      +hr = Bo.and_r(Mem(c, L), RdIn.cell(tag, RdIn(g, m, x2p, L), RdIn(g, m, x3p, L), RdIn(g, m, x4p, L)), h2)
      %Ce.get_other(m, c, s, x2, e => Mem.ne(c, s, L, hm, hs, e)) :
        {Bool.and(Mem(c, L), RdIn.cell(U32.to_nat(U32.and(C.Cir.Cell.get(0n, _), 63)), RdIn(g, m2, C.Cir.Cell.get(2n, _), L),
          RdIn(g, m2, C.Cir.Cell.get(3n, _), L), RdIn(g, m2, C.Cir.Cell.get(4n, _), L))) == True{} : Bool}
      %Equal.sym(Bool, Mem(c, L), True{}, hm) :
        {Bool.and(_, RdIn.cell(tag, RdIn(g, m2, x2p, L), RdIn(g, m2, x3p, L), RdIn(g, m2, x4p, L))) == True{} : Bool}
      RdIn.cell.mono(tag, RdIn(g, m, x2p, L), RdIn(g, m, x3p, L), RdIn(g, m, x4p, L), RdIn(g, m2, x2p, L), RdIn(g, m2, x3p, L),
        RdIn(g, m2, x4p, L), hr, e2 => RdF(g, m, s, x2, L, x2p, e2, hs), e3 => RdF(g, m, s, x2, L, x3p, e3, hs),
        e4 => RdF(g, m, s, x2, L, x4p, e4, hs))

# and so does a set that keeps the tag, quantity and parts of its cell
def RdAg(f: Nat, +m: C.Cir.Cells, +d: U32, +x2: C.Cir.Cell, +ag: AgC(C.Cir.Cells.get(m, d), x2), +L: List<&2, U32>, +c: U32,
  h: {RdIn(f, m, c, L) == True{} : Bool}) -> {RdIn(f, C.Cir.Cells.set(m, d, x2), c, L) == True{} : Bool}:
  match f:
    case 0n:
      {==}
    case 1n+(+g):
      +m2 = C.Cir.Cells.set(m, d, x2)
      +x = C.Cir.Cells.get(m, c)
      +y = C.Cir.Cells.get(m2, c)
      +x2p = C.Cir.Cell.get(2n, x)
      +x3p = C.Cir.Cell.get(3n, x)
      +x4p = C.Cir.Cell.get(4n, x)
      +tag = U32.to_nat(U32.and(C.Cir.Cell.get(0n, x), 63))
      +h2 = h
      +hm = Bo.and_l(Mem(c, L), RdIn.cell(tag, RdIn(g, m, x2p, L), RdIn(g, m, x3p, L), RdIn(g, m, x4p, L)), h2)
      +hr = Bo.and_r(Mem(c, L), RdIn.cell(tag, RdIn(g, m, x2p, L), RdIn(g, m, x3p, L), RdIn(g, m, x4p, L)), h2)
      +a = Ag(m, d, x2, ag, c)
      %AgC.t(x, y, a) : {Bool.and(Mem(c, L), RdIn.cell(U32.to_nat(_), RdIn(g, m2, C.Cir.Cell.get(2n, y), L),
          RdIn(g, m2, C.Cir.Cell.get(3n, y), L), RdIn(g, m2, C.Cir.Cell.get(4n, y), L))) == True{} : Bool}
      %AgC.f2(x, y, a) : {Bool.and(Mem(c, L), RdIn.cell(tag, RdIn(g, m2, _, L),
          RdIn(g, m2, C.Cir.Cell.get(3n, y), L), RdIn(g, m2, C.Cir.Cell.get(4n, y), L))) == True{} : Bool}
      %AgC.f3(x, y, a) : {Bool.and(Mem(c, L), RdIn.cell(tag, RdIn(g, m2, x2p, L), RdIn(g, m2, _, L), RdIn(g, m2, C.Cir.Cell.get(4n, y), L))) == True{} : Bool}
      %AgC.f4(x, y, a) : {Bool.and(Mem(c, L), RdIn.cell(tag, RdIn(g, m2, x2p, L), RdIn(g, m2, x3p, L), RdIn(g, m2, _, L))) == True{} : Bool}
      %Equal.sym(Bool, Mem(c, L), True{}, hm) :
        {Bool.and(_, RdIn.cell(tag, RdIn(g, m2, x2p, L), RdIn(g, m2, x3p, L), RdIn(g, m2, x4p, L))) == True{} : Bool}
      RdIn.cell.mono(tag, RdIn(g, m, x2p, L), RdIn(g, m, x3p, L), RdIn(g, m, x4p, L), RdIn(g, m2, x2p, L), RdIn(g, m2, x3p, L),
        RdIn(g, m2, x4p, L), hr, e2 => RdAg(g, m, d, x2, ag, L, x2p, e2), e3 => RdAg(g, m, d, x2, ag, L, x3p, e3),
        e4 => RdAg(g, m, d, x2, ag, L, x4p, e4))

# Writes
# ------
#
# A ghost log of the writes that a run makes, so that a frame is a fact of
# data: field 1 of a cell set (a count or a link), a flag set in field 0, or
# a whole cell set.

type Wr is Data:
  Wr.one{c: U32, v: U32}
  Wr.flag{c: U32, fl: U32}
  Wr.any{c: U32, x: C.Cir.Cell}

def Do(+m: C.Cir.Cells, w: Wr) -> C.Cir.Cells:
  match w:
    case Wr.one{c, v}:
      Set1(m, c, v)
    case Wr.flag{c, fl}:
      SetF(m, c, fl)
    case Wr.any{c, x}:
      C.Cir.Cells.set(m, c, x)

# the writes, the last first
def Apply(ws: List<&2, Wr>, +m: C.Cir.Cells) -> C.Cir.Cells:
  match ws:
    case Nil{}:
      m
    case Con{w, rest}:
      Do(Apply(rest, m), w)

# a write that keeps the terms of the cells of L, and every cell of K (the
# links): a count of a cell outside K, a flag outside the tag and the quantity
# on a cell outside K, or a cell outside L and K
def WOk1(w: Wr, +L: List<&2, U32>, +K: List<&2, U32>) -> Bool:
  match w:
    case Wr.one{+c, _}:
      Bool.not(Mem(c, K))
    case Wr.flag{+c, +fl}:
      Bool.not(Mem(c, K)) && (U32.is_eq(U32.and(fl, 63), 0) && U32.is_eq(U32.and(U32.shrn(fl, 6n), 3), 0))
    case Wr.any{+c, _}:
      Bool.not(Mem(c, L)) && Bool.not(Mem(c, K))

def WOk(ws: List<&2, Wr>, +L: List<&2, U32>, +K: List<&2, U32>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{w, rest}:
      WOk1(w, L, K) && WOk(rest, L, K)

def Bo.not_t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      tf({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def AgC.trans(+x: C.Cir.Cell, +y: C.Cir.Cell, +z: C.Cir.Cell, a: AgC(x, y), b: AgC(y, z)) -> AgC(x, z):
  +a2 = a
  +b2 = b
  (Equal.trans(U32, U32.and(C.Cir.Cell.get(0n, x), 63), U32.and(C.Cir.Cell.get(0n, y), 63), U32.and(C.Cir.Cell.get(0n, z), 63), AgC.t(x, y, a2), AgC.t(y, z, b2)),
  (Equal.trans(U32, U32.and(U32.shrn(C.Cir.Cell.get(0n, x), 6n), 3), U32.and(U32.shrn(C.Cir.Cell.get(0n, y), 6n), 3), U32.and(U32.shrn(C.Cir.Cell.get(0n, z), 6n), 3), AgC.q(x, y, a2), AgC.q(y, z, b2)),
  (Equal.trans(U32, C.Cir.Cell.get(2n, x), C.Cir.Cell.get(2n, y), C.Cir.Cell.get(2n, z), AgC.f2(x, y, a2), AgC.f2(y, z, b2)),
  (Equal.trans(U32, C.Cir.Cell.get(3n, x), C.Cir.Cell.get(3n, y), C.Cir.Cell.get(3n, z), AgC.f3(x, y, a2), AgC.f3(y, z, b2)),
  Equal.trans(U32, C.Cir.Cell.get(4n, x), C.Cir.Cell.get(4n, y), C.Cir.Cell.get(4n, z), AgC.f4(x, y, a2), AgC.f4(y, z, b2))))))

def WOk1.fl1(+fl: U32, +k: Bool, h: {Bool.and(k, Bool.and(U32.is_eq(U32.and(fl, 63), 0), U32.is_eq(U32.and(U32.shrn(fl, 6n), 3), 0))) == True{} : Bool}) ->
  {U32.and(fl, 63) == 0 : U32}:
  +h2 = Bo.and_r(k, Bool.and(U32.is_eq(U32.and(fl, 63), 0), U32.is_eq(U32.and(U32.shrn(fl, 6n), 3), 0)), h)
  U.eq_t(U32.and(fl, 63), 0, Bo.and_l(U32.is_eq(U32.and(fl, 63), 0), U32.is_eq(U32.and(U32.shrn(fl, 6n), 3), 0), h2))

def WOk1.fl2(+fl: U32, +k: Bool, h: {Bool.and(k, Bool.and(U32.is_eq(U32.and(fl, 63), 0), U32.is_eq(U32.and(U32.shrn(fl, 6n), 3), 0))) == True{} : Bool}) ->
  {U32.and(U32.shrn(fl, 6n), 3) == 0 : U32}:
  +h2 = Bo.and_r(k, Bool.and(U32.is_eq(U32.and(fl, 63), 0), U32.is_eq(U32.and(U32.shrn(fl, 6n), 3), 0)), h)
  U.eq_t(U32.and(U32.shrn(fl, 6n), 3), 0, Bo.and_r(U32.is_eq(U32.and(fl, 63), 0), U32.is_eq(U32.and(U32.shrn(fl, 6n), 3), 0), h2))

def WOk1.nk(+k: Bool, -r: Bool, h: {Bool.and(Bool.not(k), r) == True{} : Bool}) -> {k == False{} : Bool}:
  Bo.not_t(k, Bo.and_l(Bool.not(k), r, h))

# one write keeps the term of a cell that reads only cells of L
def Do1.tm(w: Wr, +f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +L: List<&2, U32>, +K: List<&2, U32>,
  +c: U32, o: {WOk1(w, L, K) == True{} : Bool}, h: {RdIn(f, m, c, L) == True{} : Bool}) ->
  {T.tm.of(f, m, ks, img, c) == T.tm.of(f, Do(m, w), ks, img, c) : Maybe<&2, C.Term>}:
  match w:
    case Wr.one{+d, +v}:
      TF1(f, m, d, v, ks, img, c)
    case Wr.flag{+d, +fl}:
      +o2 = o
      TFl(f, m, d, fl, WOk1.fl1(fl, Bool.not(Mem(d, K)), o2), WOk1.fl2(fl, Bool.not(Mem(d, K)), o2), ks, img, c)
    case Wr.any{+d, +x}:
      TFo(f, m, d, x, ks, img, L, c, h, WOk1.nk(Mem(d, L), Bool.not(Mem(d, K)), o))

def Do1.rd(w: Wr, +f: Nat, +m: C.Cir.Cells, +L: List<&2, U32>, +K: List<&2, U32>, +c: U32, o: {WOk1(w, L, K) == True{} : Bool},
  h: {RdIn(f, m, c, L) == True{} : Bool}) -> {RdIn(f, Do(m, w), c, L) == True{} : Bool}:
  match w:
    case Wr.one{+d, +v}:
      RdAg(f, m, d, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, d), v), AgC.set1(C.Cir.Cells.get(m, d), v), L, c, h)
    case Wr.flag{+d, +fl}:
      +o2 = o
      +x = C.Cir.Cells.get(m, d)
      RdAg(f, m, d, C.Cir.Cell.set(0n, x, U32.or(C.Cir.Cell.get(0n, x), fl)),
        AgC.flag(x, fl, WOk1.fl1(fl, Bool.not(Mem(d, K)), o2), WOk1.fl2(fl, Bool.not(Mem(d, K)), o2)), L, c, h)
    case Wr.any{+d, +x}:
      RdF(f, m, d, x, L, c, h, WOk1.nk(Mem(d, L), Bool.not(Mem(d, K)), o))

# writes that WOk allows keep the term of a cell that reads only cells of L
def W.rd(ws: List<&2, Wr>, +f: Nat, +m: C.Cir.Cells, +L: List<&2, U32>, +K: List<&2, U32>, +c: U32,
  ok: {WOk(ws, L, K) == True{} : Bool}, h: {RdIn(f, m, c, L) == True{} : Bool}) -> {RdIn(f, Apply(ws, m), c, L) == True{} : Bool}:
  match ws:
    case Nil{}:
      h
    case Con{+w, +rest}:
      +ok2 = ok
      Do1.rd(w, f, Apply(rest, m), L, K, c, Bo.and_l(WOk1(w, L, K), WOk(rest, L, K), ok2),
        W.rd(rest, f, m, L, K, c, Bo.and_r(WOk1(w, L, K), WOk(rest, L, K), ok2), h))

def W.tm(ws: List<&2, Wr>, +f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +L: List<&2, U32>,
  +K: List<&2, U32>, +c: U32, ok: {WOk(ws, L, K) == True{} : Bool}, +h: {RdIn(f, m, c, L) == True{} : Bool}) ->
  {T.tm.of(f, m, ks, img, c) == T.tm.of(f, Apply(ws, m), ks, img, c) : Maybe<&2, C.Term>}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +rest}:
      +ok2 = ok
      +ok1 = Bo.and_l(WOk1(w, L, K), WOk(rest, L, K), ok2)
      +okr = Bo.and_r(WOk1(w, L, K), WOk(rest, L, K), ok2)
      Equal.trans(Maybe<&2, C.Term>, T.tm.of(f, m, ks, img, c), T.tm.of(f, Apply(rest, m), ks, img, c), T.tm.of(f, Do(Apply(rest, m), w), ks, img, c),
        W.tm(rest, f, m, ks, img, L, K, c, okr, h),
        Do1.tm(w, f, Apply(rest, m), ks, img, L, K, c, ok1, W.rd(rest, f, m, L, K, c, okr, h)))

# one write keeps every cell of K
def Do1.link(w: Wr, +m: C.Cir.Cells, +L: List<&2, U32>, +K: List<&2, U32>, +d: U32, o: {WOk1(w, L, K) == True{} : Bool},
  +hd: {Mem(d, K) == True{} : Bool}) -> {C.Cir.Cells.get(m, d) == C.Cir.Cells.get(Do(m, w), d) : C.Cir.Cell}:
  match w:
    case Wr.one{+c, +v}:
      +hc = Bo.not_t(Mem(c, K), o)
      Ce.get_other(m, d, c, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, c), v), e => Mem.ne(d, c, K, hd, hc, e))
    case Wr.flag{+c, +fl}:
      +hc = WOk1.nk(Mem(c, K), Bool.and(U32.is_eq(U32.and(fl, 63), 0), U32.is_eq(U32.and(U32.shrn(fl, 6n), 3), 0)), o)
      +x = C.Cir.Cells.get(m, c)
      Ce.get_other(m, d, c, C.Cir.Cell.set(0n, x, U32.or(C.Cir.Cell.get(0n, x), fl)), e => Mem.ne(d, c, K, hd, hc, e))
    case Wr.any{+c, +x}:
      +o2 = o
      +hc = Bo.not_t(Mem(c, K), Bo.and_r(Bool.not(Mem(c, L)), Bool.not(Mem(c, K)), o2))
      Ce.get_other(m, d, c, x, e => Mem.ne(d, c, K, hd, hc, e))

def W.link(ws: List<&2, Wr>, +m: C.Cir.Cells, +L: List<&2, U32>, +K: List<&2, U32>, +d: U32, ok: {WOk(ws, L, K) == True{} : Bool},
  +hd: {Mem(d, K) == True{} : Bool}) -> {C.Cir.Cells.get(m, d) == C.Cir.Cells.get(Apply(ws, m), d) : C.Cir.Cell}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +rest}:
      +ok2 = ok
      Equal.trans(C.Cir.Cell, C.Cir.Cells.get(m, d), C.Cir.Cells.get(Apply(rest, m), d), C.Cir.Cells.get(Do(Apply(rest, m), w), d),
        W.link(rest, m, L, K, d, Bo.and_r(WOk1(w, L, K), WOk(rest, L, K), ok2), hd),
        Do1.link(w, Apply(rest, m), L, K, d, Bo.and_l(WOk1(w, L, K), WOk(rest, L, K), ok2), hd))

# one write keeps the tag, quantity and parts of every cell of L
def Do1.ag(w: Wr, +m: C.Cir.Cells, +L: List<&2, U32>, +K: List<&2, U32>, +d: U32, o: {WOk1(w, L, K) == True{} : Bool},
  +hd: {Mem(d, L) == True{} : Bool}) -> AgC(C.Cir.Cells.get(m, d), C.Cir.Cells.get(Do(m, w), d)):
  match w:
    case Wr.one{+c, +v}:
      Ag(m, c, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, c), v), AgC.set1(C.Cir.Cells.get(m, c), v), d)
    case Wr.flag{+c, +fl}:
      +o2 = o
      +x = C.Cir.Cells.get(m, c)
      Ag(m, c, C.Cir.Cell.set(0n, x, U32.or(C.Cir.Cell.get(0n, x), fl)),
        AgC.flag(x, fl, WOk1.fl1(fl, Bool.not(Mem(c, K)), o2), WOk1.fl2(fl, Bool.not(Mem(c, K)), o2)), d)
    case Wr.any{+c, +x}:
      +hc = WOk1.nk(Mem(c, L), Bool.not(Mem(c, K)), o)
      AgC.cong(C.Cir.Cells.get(m, d), C.Cir.Cells.get(C.Cir.Cells.set(m, c, x), d), Ce.get_other(m, d, c, x, e => Mem.ne(d, c, L, hd, hc, e)))

def W.ag(ws: List<&2, Wr>, +m: C.Cir.Cells, +L: List<&2, U32>, +K: List<&2, U32>, +d: U32, ok: {WOk(ws, L, K) == True{} : Bool},
  +hd: {Mem(d, L) == True{} : Bool}) -> AgC(C.Cir.Cells.get(m, d), C.Cir.Cells.get(Apply(ws, m), d)):
  match ws:
    case Nil{}:
      AgC.refl(C.Cir.Cells.get(m, d))
    case Con{+w, +rest}:
      +ok2 = ok
      AgC.trans(C.Cir.Cells.get(m, d), C.Cir.Cells.get(Apply(rest, m), d), C.Cir.Cells.get(Do(Apply(rest, m), w), d),
        W.ag(rest, m, L, K, d, Bo.and_r(WOk1(w, L, K), WOk(rest, L, K), ok2), hd),
        Do1.ag(w, Apply(rest, m), L, K, d, Bo.and_l(WOk1(w, L, K), WOk(rest, L, K), ok2), hd))

# The pend list
# -------------
#
# M.alloc takes the first cell of the pend list, whose parts then lose a
# pointer, or a new cell. That the cell it takes is none of the live ones is
# what the machine's counts guarantee; the proofs here take it, through CS,
# an invariant of the pend list p of the cells m that the caller chooses, of
# the live term cells L and the live link cells K (the machine's own: lists of
# arguments and locals, the stack of a check):
#
#   AH: from CS, M.alloc gives a cell c of neither L nor K, all zeros, after
#       writes that keep L's terms and K (counts, and the cells it takes),
#       and set no flag, and CS again with c in K;
#   CF: writes to cells of K, and flags on cells of L, keep CS;
#   PH: a cell of K that is no term cell (tag 32 or more), once on the pend
#       list, keeps CS, with the cell out of K.
#
# Each use takes one proof, so a run takes a supply of them, Sup(k), with k
# at least the rounds of its loops.

# every cell of L is one that Cir may access
def AllCell(L: List<&2, U32>, +im: U32, +fs: U32, +nx: U32) -> Bool:
  match L:
    case Nil{}:
      True{}
    case Con{c, rest}:
      C.Cir.is_cell(c, im, fs, nx) && AllCell(rest, im, fs, nx)

# K without c
def Remove.if(b: Bool, h: U32, r: List<&2, U32>) -> List<&2, U32>:
  match b:
    case True{}:
      r
    case False{}:
      Con{h, r}

def Remove(+c: U32, K: List<&2, U32>) -> List<&2, U32>:
  match K:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Remove.if(U32.is_eq(c, h), h, Remove(c, t))

# the registers after M.alloc(r): r holds c; pend, dx, dr, aq and am what it left
def AlRegs(+rg: List<&2, U32>, r: Nat, c: U32, p: U32, aq: U32, am: U32, dx: U32, dr: U32) -> List<&2, U32>:
  List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, rg, 3n, p), 4n, dx), 5n, dr), 6n, aq), 7n, am), r, c)

def Pend(+rg: List<&2, U32>) -> U32:
  Maybe.default(&2, U32, List.get(&2, U32, rg, 3n), 0)

# what M.alloc leaves: c, the registers, the writes and the new next and pages
type AW is Data:
  AW{c: U32, p: U32, aq: U32, am: U32, dx: U32, dr: U32, ws: List<&2, Wr>, nx: U32, pg: U32}

def AlPost.of(w: AW, +rg: List<&2, U32>, +r: Nat, +m: C.Cir.Cells, +fs: U32, +im: U32, +lim: U32, +inp: List<&2, U32>,
  +L: List<&2, U32>, +K: List<&2, U32>, -CS: C.Cir.Cells -> U32 -> List<&2, U32> -> List<&2, U32> -> Type, st2: C.Cir.State) -> Type:
  match w:
    case AW{+c, +p, +aq, +am, +dx, +dr, +ws, +nx2, +pg2}:
      Sigma<&1, &1, {st2 == C.Cir.State{AlRegs(rg, r, c, p, aq, am, dx, dr), Apply(ws, m), nx2, fs, im, pg2, lim, inp, [], 0} : C.Cir.State}, _ =>
      Sigma<&1, &1, {Mem(c, L) == False{} : Bool}, _ =>
      Sigma<&1, &1, {Mem(c, K) == False{} : Bool}, _ =>
      Sigma<&1, &1, {U32.is_zero(c) == False{} : Bool}, _ =>
      Sigma<&1, &1, {WOk(ws, L, K) == True{} : Bool}, _ =>
      Sigma<&1, &1, {WFl(ws, Nil{}) == True{} : Bool}, _ =>
      Sigma<&1, &1, {C.Cir.Cells.get(Apply(ws, m), c) == C.Cir.Cell.zero() : C.Cir.Cell}, _ =>
      Sigma<&1, &1, {AllCell(L, im, fs, nx2) == True{} : Bool}, _ =>
      Sigma<&1, &1, {AllCell(Con{c, K}, im, fs, nx2) == True{} : Bool}, _ =>
      CS(Apply(ws, m), p, L, Con{c, K})>>>>>>>>>

def AlPost(+rg: List<&2, U32>, +r: Nat, +m: C.Cir.Cells, +fs: U32, +im: U32, +lim: U32, +inp: List<&2, U32>,
  +L: List<&2, U32>, +K: List<&2, U32>, -CS: C.Cir.Cells -> U32 -> List<&2, U32> -> List<&2, U32> -> Type, st2: C.Cir.State) -> Type:
  &w: AW -> AlPost.of(w, rg, r, m, fs, im, lim, inp, L, K, CS, st2)

# AH: an alloc from a state of which CS holds
def AH(-CS: C.Cir.Cells -> U32 -> List<&2, U32> -> List<&2, U32> -> Type) -> Type:
  @F: Nat -> @r: Nat -> @rg: List<&2, U32> -> @m: C.Cir.Cells -> @nx: U32 -> @fs: U32 -> @im: U32 -> @pg: U32 -> @lim: U32 ->
  @inp: List<&2, U32> -> @L: List<&2, U32> -> @K: List<&2, U32> ->
  CS(m, Pend(rg), L, K) -> {AllCell(L, im, fs, nx) == True{} : Bool} -> {AllCell(K, im, fs, nx) == True{} : Bool} ->
  Ok(C.Cir.exec(F, C.M.alloc(r), C.Cir.State{rg, m, nx, fs, im, pg, lim, inp, [], 0}), st2 => AlPost(rg, r, m, fs, im, lim, inp, L, K, CS, st2))

# the writes of the machine's own code: links and whole cells of K, flags on L
def MyOk1(w: Wr, +L: List<&2, U32>, +K: List<&2, U32>) -> Bool:
  match w:
    case Wr.one{+c, _}:
      Mem(c, K)
    case Wr.flag{+c, +fl}:
      (Mem(c, L) || Mem(c, K)) && (U32.is_eq(U32.and(fl, 63), 0) && U32.is_eq(U32.and(U32.shrn(fl, 6n), 3), 0))
    case Wr.any{+c, _}:
      Mem(c, K)

def MyOk(ws: List<&2, Wr>, +L: List<&2, U32>, +K: List<&2, U32>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{w, rest}:
      MyOk1(w, L, K) && MyOk(rest, L, K)

# CF: the machine's own writes keep CS
def CF(-CS: C.Cir.Cells -> U32 -> List<&2, U32> -> List<&2, U32> -> Type) -> Type:
  @m: C.Cir.Cells -> @p: U32 -> @L: List<&2, U32> -> @K: List<&2, U32> -> @ws: List<&2, Wr> ->
  CS(m, p, L, K) -> {MyOk(ws, L, K) == True{} : Bool} -> CS(Apply(ws, m), p, L, K)

# PH: a cell of K, no term cell, goes to the pend list
def PH(-CS: C.Cir.Cells -> U32 -> List<&2, U32> -> List<&2, U32> -> Type) -> Type:
  @m: C.Cir.Cells -> @p: U32 -> @L: List<&2, U32> -> @K: List<&2, U32> -> @s: U32 ->
  CS(m, p, L, K) -> {Mem(s, K) == True{} : Bool} -> {Mem(s, L) == False{} : Bool} ->
  {U32.is_lt(U32.and(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, s)), 63), 32) == False{} : Bool} ->
  CS(Set1(m, s, p), s, L, Remove(s, K))

# the proofs that a round of a loop may use
def Unit6(-CS: C.Cir.Cells -> U32 -> List<&2, U32> -> List<&2, U32> -> Type) -> Type:
  AH(CS) & (AH(CS) & (PH(CS) & (CF(CS) & (CF(CS) & CF(CS)))))

def Sup(k: Nat, -CS: C.Cir.Cells -> U32 -> List<&2, U32> -> List<&2, U32> -> Type) -> Type:
  match k:
    case 0n:
      Unit
    case 1n+j:
      Unit6(CS) & Sup(j, CS)

def Sup.split.cons(j: Nat, b: Nat, -CS: C.Cir.Cells -> U32 -> List<&2, U32> -> List<&2, U32> -> Type, u: Unit6(CS), r: Sup(j, CS) & Sup(b, CS)) ->
  Sup(1n+j, CS) & Sup(b, CS):
  (x, y) = r
  ((u, x), y)

# a supply of a + b rounds is two
def Sup.split(a: Nat, +b: Nat, -CS: C.Cir.Cells -> U32 -> List<&2, U32> -> List<&2, U32> -> Type, s: Sup(Nat.add(a, b), CS)) ->
  Sup(a, CS) & Sup(b, CS):
  match a:
    case 0n:
      (Unit{}, s)
    case 1n+(+j):
      (u, r) = s
      Sup.split.cons(j, b, CS, u, Sup.split(j, b, CS, r))


# The registers
# -------------

# the 64 registers, as one value
type R64 is Data:
  R64{r0: U32, r1: U32, r2: U32, r3: U32, r4: U32, r5: U32, r6: U32, r7: U32, r8: U32, r9: U32, r10: U32, r11: U32, r12: U32, r13: U32, r14: U32, r15: U32, r16: U32, r17: U32, r18: U32, r19: U32, r20: U32, r21: U32, r22: U32, r23: U32, r24: U32, r25: U32, r26: U32, r27: U32, r28: U32, r29: U32, r30: U32, r31: U32, r32: U32, r33: U32, r34: U32, r35: U32, r36: U32, r37: U32, r38: U32, r39: U32, r40: U32, r41: U32, r42: U32, r43: U32, r44: U32, r45: U32, r46: U32, r47: U32, r48: U32, r49: U32, r50: U32, r51: U32, r52: U32, r53: U32, r54: U32, r55: U32, r56: U32, r57: U32, r58: U32, r59: U32, r60: U32, r61: U32, r62: U32, r63: U32}

def R64.list(r: R64) -> List<&2, U32>:
  match r:
    case R64{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47, a48, a49, a50, a51, a52, a53, a54, a55, a56, a57, a58, a59, a60, a61, a62, a63}:
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47, a48, a49, a50, a51, a52, a53, a54, a55, a56, a57, a58, a59, a60, a61, a62, a63]

# a state of a run: no output yet
def St(rg: List<&2, U32>, m: C.Cir.Cells, nx: U32, fs: U32, im: U32, pg: U32, lim: U32, inp: List<&2, U32>) -> C.Cir.State:
  C.Cir.State{rg, m, nx, fs, im, pg, lim, inp, [], 0}

# The data check
# --------------

# field k of the cell c, its tag and its quantity
def Fd(k: Nat, +m: C.Cir.Cells, +c: U32) -> U32:
  C.Cir.Cell.get(k, C.Cir.Cells.get(m, c))

def Tg(+m: C.Cir.Cells, +c: U32) -> U32:
  U32.and(Fd(0n, m, c), 63)

def Qb(+m: C.Cir.Cells, +c: U32) -> U32:
  U32.and(U32.shrn(Fd(0n, m, c), 6n), 3)

# the cell c is flagged DATA
def FlB(+m: C.Cir.Cells, +c: U32) -> Bool:
  U32.is_ne(U32.and(Fd(0n, m, c), 512), 0)

def DataB.isNone(r: Maybe<&2, C.Term>) -> Type:
  match r:
    case None{}:
      Unit
    case Some{_}:
      Empty

def DataB.of(r: Maybe<&2, C.Term>) -> Bool:
  match r:
    case None{}:
      False{}
    case Some{t}:
      C.Term.is_data(t)

# the term of c, within f levels, is Data
def DataB(f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32) -> Bool:
  DataB.of(T.tm.of(f, m, ks, img, c))

def DOk.tup(b: Bool, x: Bool, y: Bool) -> Bool:
  match b:
    case True{}:
      x && y
    case False{}:
      True{}

# what the check needs of the cells it reaches from c: a flagged cell is
# Data, a Ref's or an Enu's term is not, and so on in the parts of a pair
def DOk(f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32) -> Bool:
  match f:
    case 0n:
      True{}
    case 1n+(+g):
      +d = DataB(1n+g, m, ks, img, c)
      +t = Tg(m, c)
      (Bool.not(FlB(m, c)) || d) && ((Bool.not(U32.is_eq(t, 1) || U32.is_eq(t, 12)) || Bool.not(d)) &&
        DOk.tup(U32.is_eq(t, 10), DOk(g, m, ks, img, Fd(2n, m, c)), DOk(g, m, ks, img, Fd(3n, m, c))))

# Terms at a known tag
# --------------------

def U.nat_eq.c(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), +e: {x == y : Nat}) -> {Cmp.is_eq(c) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({Cmp.is_eq(LT{}) == True{} : Bool}, N.not_succ_le(x, N.le_rw_r(1n+x, y, x, Equal.sym(Nat, x, y, e), r)))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({Cmp.is_eq(GT{}) == True{} : Bool}, N.not_succ_le(y, N.le_rw_r(1n+y, x, y, e, r)))

# U32s of the same number are equal, as is_eq says
def U.nat_eq(+a: U32, +b: U32, e: {U32.to_nat(a) == U32.to_nat(b) : Nat}) -> {U32.is_eq(a, b) == True{} : Bool}:
  U.nat_eq.c(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), e)

# tm.of one level down, at the cell's tag n
def TAn(+g: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +y: U32, +n: Nat,
  e: {U32.to_nat(Tg(m, y)) == n : Nat}) ->
  {T.tm.cell(n, T.tm.quan(Qb(m, y)), y, Fd(2n, m, y), ks, img, u => T.tm.of(g, m, ks, img, Fd(2n, m, y)), u => T.tm.of(g, m, ks, img, Fd(3n, m, y)), u => T.tm.of(g, m, ks, img, Fd(4n, m, y))) == T.tm.of(1n+g, m, ks, img, y) : Maybe<&2, C.Term>}:
  %Equal.sym(Nat, U32.to_nat(Tg(m, y)), n, e) : {T.tm.cell(n, T.tm.quan(Qb(m, y)), y, Fd(2n, m, y), ks, img, u => T.tm.of(g, m, ks, img, Fd(2n, m, y)), u => T.tm.of(g, m, ks, img, Fd(3n, m, y)), u => T.tm.of(g, m, ks, img, Fd(4n, m, y))) == T.tm.cell(_, T.tm.quan(Qb(m, y)), y, Fd(2n, m, y), ks, img, u => T.tm.of(g, m, ks, img, Fd(2n, m, y)), u => T.tm.of(g, m, ks, img, Fd(3n, m, y)), u => T.tm.of(g, m, ks, img, Fd(4n, m, y))) : Maybe<&2, C.Term>}
  {==}

def Some.inj(-x: C.Term, -y: C.Term, e: {Some{x} == Some{y} : Maybe<&2, C.Term>}) -> {x == y : C.Term}:
  Equal.cong(Maybe<&2, C.Term>, C.Term, z => Maybe.default(&2, C.Term, z, C.Term.Efq{}), Some{x}, Some{y}, e)

def none_some(-t: C.Term, e: {None{} == Some{t} : Maybe<&2, C.Term>}) -> Empty:
  %e : DataB.isNone(_)
  Unit{}

def U.nat(+a: U32, +lit: U32, e: {a == lit : U32}) -> {U32.to_nat(a) == U32.to_nat(lit) : Nat}:
  Equal.cong(U32, Nat, z => U32.to_nat(z), a, lit, e)

def D.lab.n(n: Maybe<&2, List<&2, U32>>, -t: C.Term, h: {T.tm.named(n, k => C.Term.Lab{k}) == Some{t} : Maybe<&2, C.Term>}) -> {C.Term.is_data(t) == True{} : Bool}:
  match n:
    case None{}:
      Empty.absurd({C.Term.is_data(t) == True{} : Bool}, none_some(t, h))
    case Some{k}:
      %Some.inj(C.Term.Lab{k}, t, h) : {C.Term.is_data(_) == True{} : Bool}
      {==}

# a cell of the tag of a label stands for Data
def D.lab(+g: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +y: U32, e: {Tg(m, y) == 13 : U32},
  -t: C.Term, h: {T.tm.of(1n+g, m, ks, img, y) == Some{t} : Maybe<&2, C.Term>}) -> {C.Term.is_data(t) == True{} : Bool}:
  D.lab.n(T.tm.name(ks, Fd(2n, m, y)), t, Equal.trans(Maybe<&2, C.Term>, T.tm.cell(13n, T.tm.quan(Qb(m, y)), y, Fd(2n, m, y), ks, img, u => T.tm.of(g, m, ks, img, Fd(2n, m, y)), u => T.tm.of(g, m, ks, img, Fd(3n, m, y)), u => T.tm.of(g, m, ks, img, Fd(4n, m, y))), T.tm.of(1n+g, m, ks, img, y), Some{t},
    TAn(g, m, ks, img, y, 13n, U.nat(Tg(m, y), 13, e)), h))

# and so does one of the tag of Rfl
def D.rfl(+g: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +y: U32, e: {Tg(m, y) == 17 : U32},
  -t: C.Term, h: {T.tm.of(1n+g, m, ks, img, y) == Some{t} : Maybe<&2, C.Term>}) -> {C.Term.is_data(t) == True{} : Bool}:
  +e2 = Some.inj(C.Term.Rfl{}, t, Equal.trans(Maybe<&2, C.Term>, T.tm.cell(17n, T.tm.quan(Qb(m, y)), y, Fd(2n, m, y), ks, img, u => T.tm.of(g, m, ks, img, Fd(2n, m, y)), u => T.tm.of(g, m, ks, img, Fd(3n, m, y)), u => T.tm.of(g, m, ks, img, Fd(4n, m, y))), T.tm.of(1n+g, m, ks, img, y), Some{t},
    TAn(g, m, ks, img, y, 17n, U.nat(Tg(m, y), 17, e)), h))
  %e2 : {C.Term.is_data(_) == True{} : Bool}
  {==}

# the parts of a pair, and the pair
def TupR(+g: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +y: U32, t: C.Term) -> Data:
  Sigma<&2, &2, C.Term, a => Sigma<&2, &2, C.Term, b =>
  Sigma<&2, &2, {T.tm.of(g, m, ks, img, Fd(2n, m, y)) == Some{a} : Maybe<&2, C.Term>}, _ =>
  Sigma<&2, &2, {T.tm.of(g, m, ks, img, Fd(3n, m, y)) == Some{b} : Maybe<&2, C.Term>}, _ =>
  {C.Term.Tup{T.tm.quan(Qb(m, y)), a, b} == t : C.Term}>>>>

def D.tup.two(r: Maybe<&2, C.Term>, s: Maybe<&2, C.Term>, +q: C.Quan, -t: C.Term, h: {T.tm.two(a => b => C.Term.Tup{q, a, b}, r, s) == Some{t} : Maybe<&2, C.Term>}) ->
  Sigma<&2, &2, C.Term, a => Sigma<&2, &2, C.Term, b => Sigma<&2, &2, {r == Some{a} : Maybe<&2, C.Term>}, _ =>
  Sigma<&2, &2, {s == Some{b} : Maybe<&2, C.Term>}, _ => {C.Term.Tup{q, a, b} == t : C.Term}>>>>:
  match r s:
    case Some{+a} Some{+b}:
      (a, (b, ({==}, ({==}, Some.inj(C.Term.Tup{q, a, b}, t, h)))))
    case Some{a} None{}:
      Empty.absurd(Sigma<&2, &2, C.Term, a2 => Sigma<&2, &2, C.Term, b => Sigma<&2, &2, {Some{a} == Some{a2} : Maybe<&2, C.Term>}, _ =>
        Sigma<&2, &2, {None{} == Some{b} : Maybe<&2, C.Term>}, _ => {C.Term.Tup{q, a2, b} == t : C.Term}>>>>, none_some(t, h))
    case None{} s2:
      Empty.absurd(Sigma<&2, &2, C.Term, a => Sigma<&2, &2, C.Term, b => Sigma<&2, &2, {None{} == Some{a} : Maybe<&2, C.Term>}, _ =>
        Sigma<&2, &2, {s2 == Some{b} : Maybe<&2, C.Term>}, _ => {C.Term.Tup{q, a, b} == t : C.Term}>>>>, none_some(t, h))

# a cell of the tag of a pair stands for the pair of its parts' terms
def D.tup(+g: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +y: U32, e: {Tg(m, y) == 10 : U32},
  -t: C.Term, h: {T.tm.of(1n+g, m, ks, img, y) == Some{t} : Maybe<&2, C.Term>}) -> TupR(g, m, ks, img, y, t):
  D.tup.two(T.tm.of(g, m, ks, img, Fd(2n, m, y)), T.tm.of(g, m, ks, img, Fd(3n, m, y)), T.tm.quan(Qb(m, y)), t,
    Equal.trans(Maybe<&2, C.Term>, T.tm.cell(10n, T.tm.quan(Qb(m, y)), y, Fd(2n, m, y), ks, img, u => T.tm.of(g, m, ks, img, Fd(2n, m, y)), u => T.tm.of(g, m, ks, img, Fd(3n, m, y)), u => T.tm.of(g, m, ks, img, Fd(4n, m, y))), T.tm.of(1n+g, m, ks, img, y), Some{t},
      TAn(g, m, ks, img, y, 10n, U.nat(Tg(m, y), 10, e)), h))

def ND.one(-k: C.Term -> C.Term, r: Maybe<&2, C.Term>, hk: @a: C.Term -> {C.Term.is_data(k(a)) == False{} : Bool}) ->
  {DataB.of(T.tm.one(k, r)) == False{} : Bool}:
  match r:
    case None{}:
      {==}
    case Some{a}:
      hk(a)

def ND.two(-k: C.Term -> C.Term -> C.Term, r: Maybe<&2, C.Term>, s: Maybe<&2, C.Term>, hk: @a: C.Term -> @b: C.Term -> {C.Term.is_data(k(a, b)) == False{} : Bool}) ->
  {DataB.of(T.tm.two(k, r, s)) == False{} : Bool}:
  match r s:
    case Some{a} Some{b}:
      hk(a, b)
    case Some{a} None{}:
      {==}
    case None{} s2:
      {==}

def ND.three(-k: C.Term -> C.Term -> C.Term -> C.Term, r: Maybe<&2, C.Term>, s: Maybe<&2, C.Term>, u: Maybe<&2, C.Term>,
  hk: @a: C.Term -> @b: C.Term -> @c: C.Term -> {C.Term.is_data(k(a, b, c)) == False{} : Bool}) ->
  {DataB.of(T.tm.three(k, r, s, u)) == False{} : Bool}:
  match r s u:
    case Some{a} Some{b} Some{c}:
      hk(a, b, c)
    case Some{a} Some{b} None{}:
      {==}
    case Some{a} None{} u2:
      {==}
    case None{} s2 u2:
      {==}

def ND.mat(n: Maybe<&2, List<&2, U32>>, r: Maybe<&2, C.Term>, s: Maybe<&2, C.Term>) -> {DataB.of(T.tm.mat(n, r, s)) == False{} : Bool}:
  match n r s:
    case Some{k} Some{h} Some{c}:
      {==}
    case Some{k} Some{h} None{}:
      {==}
    case Some{k} None{} s2:
      {==}
    case None{} r2 s2:
      {==}

def ND.img.b(b: Bool, x: Bool, d: Bool, eb: {b == True{} : Bool}, im: {Bool.or(Bool.not(Bool.or(b, x)), Bool.not(d)) == True{} : Bool}) -> {d == False{} : Bool}:
  match b:
    case True{}:
      Bo.not_t(d, im)
    case False{}:
      tf({d == False{} : Bool}, eb)

def ND.img.n(x: Bool, d: Bool, ex: {x == True{} : Bool}, im: {Bool.or(Bool.not(x), Bool.not(d)) == True{} : Bool}) -> {d == False{} : Bool}:
  match x:
    case True{}:
      Bo.not_t(d, im)
    case False{}:
      tf({d == False{} : Bool}, ex)

def ND.img12.b(b: Bool, x: Bool, d: Bool, ex: {x == True{} : Bool}, im: {Bool.or(Bool.not(Bool.or(b, x)), Bool.not(d)) == True{} : Bool}) -> {d == False{} : Bool}:
  match b:
    case True{}:
      Bo.not_t(d, im)
    case False{}:
      ND.img.n(x, d, ex, im)

# a cell of any other tag stands for no Data: the image's term of a Ref or an
# Enu is none, as im says
def DO.cell(n: Nat, +q: C.Quan, +y: U32, +f2: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +p2: Maybe<&2, C.Term>, +p3: Maybe<&2, C.Term>, +p4: Maybe<&2, C.Term>, +T2: U32, d: Bool, +en: {U32.to_nat(T2) == n : Nat},
  n13: {U32.is_eq(T2, 13) == False{} : Bool}, n17: {U32.is_eq(T2, 17) == False{} : Bool}, n10: {U32.is_eq(T2, 10) == False{} : Bool},
  ed: {DataB.of(T.tm.cell(n, q, y, f2, ks, img, u => p2, u => p3, u => p4)) == d : Bool},
  im: {Bool.or(Bool.not(Bool.or(U32.is_eq(T2, 1), U32.is_eq(T2, 12))), Bool.not(d)) == True{} : Bool}) -> {d == False{} : Bool}:
  match n:
    case 0n:
      Equal.sym(Bool, False{}, d, ed)
    case 1n:
      ND.img.b(U32.is_eq(T2, 1), U32.is_eq(T2, 12), d, U.nat_eq(T2, 1, en), im)
    case 2n:
      Equal.trans(Bool, d, DataB.of(T.tm.two(a => b => C.Term.Ann{a, b}, p2, p3)), False{}, Equal.sym(Bool, DataB.of(T.tm.two(a => b => C.Term.Ann{a, b}, p2, p3)), d, ed), ND.two(a => b => C.Term.Ann{a, b}, p2, p3, a => b => {==}))
    case 3n:
      Equal.trans(Bool, d, DataB.of(T.tm.two(a => b => C.Term.Let{q, a, b}, p2, p3)), False{}, Equal.sym(Bool, DataB.of(T.tm.two(a => b => C.Term.Let{q, a, b}, p2, p3)), d, ed), ND.two(a => b => C.Term.Let{q, a, b}, p2, p3, a => b => {==}))
    case 4n:
      Equal.trans(Bool, d, DataB.of(T.tm.one(a => C.Term.Typ{a}, p2)), False{}, Equal.sym(Bool, DataB.of(T.tm.one(a => C.Term.Typ{a}, p2)), d, ed), ND.one(a => C.Term.Typ{a}, p2, a => {==}))
    case 5n:
      Equal.trans(Bool, d, DataB.of(T.tm.two(a => b => C.Term.Min{a, b}, p2, p3)), False{}, Equal.sym(Bool, DataB.of(T.tm.two(a => b => C.Term.Min{a, b}, p2, p3)), d, ed), ND.two(a => b => C.Term.Min{a, b}, p2, p3, a => b => {==}))
    case 6n:
      Equal.trans(Bool, d, DataB.of(T.tm.two(a => b => C.Term.All{q, a, b}, p2, p3)), False{}, Equal.sym(Bool, DataB.of(T.tm.two(a => b => C.Term.All{q, a, b}, p2, p3)), d, ed), ND.two(a => b => C.Term.All{q, a, b}, p2, p3, a => b => {==}))
    case 7n:
      Equal.trans(Bool, d, DataB.of(T.tm.one(a => C.Term.Lam{q, a}, p2)), False{}, Equal.sym(Bool, DataB.of(T.tm.one(a => C.Term.Lam{q, a}, p2)), d, ed), ND.one(a => C.Term.Lam{q, a}, p2, a => {==}))
    case 8n:
      Equal.trans(Bool, d, DataB.of(T.tm.two(a => b => C.Term.App{q, a, b}, p2, p3)), False{}, Equal.sym(Bool, DataB.of(T.tm.two(a => b => C.Term.App{q, a, b}, p2, p3)), d, ed), ND.two(a => b => C.Term.App{q, a, b}, p2, p3, a => b => {==}))
    case 9n:
      Equal.trans(Bool, d, DataB.of(T.tm.two(a => b => C.Term.Sig{q, a, b}, p2, p3)), False{}, Equal.sym(Bool, DataB.of(T.tm.two(a => b => C.Term.Sig{q, a, b}, p2, p3)), d, ed), ND.two(a => b => C.Term.Sig{q, a, b}, p2, p3, a => b => {==}))
    case 10n:
      Empty.absurd({d == False{} : Bool}, N.true_ne_false(Equal.trans(Bool, True{}, U32.is_eq(T2, 10), False{}, Equal.sym(Bool, U32.is_eq(T2, 10), True{}, U.nat_eq(T2, 10, en)), n10)))
    case 11n:
      Equal.trans(Bool, d, DataB.of(T.tm.one(a => C.Term.Prj{a}, p2)), False{}, Equal.sym(Bool, DataB.of(T.tm.one(a => C.Term.Prj{a}, p2)), d, ed), ND.one(a => C.Term.Prj{a}, p2, a => {==}))
    case 12n:
      ND.img12.b(U32.is_eq(T2, 1), U32.is_eq(T2, 12), d, U.nat_eq(T2, 12, en), im)
    case 13n:
      Empty.absurd({d == False{} : Bool}, N.true_ne_false(Equal.trans(Bool, True{}, U32.is_eq(T2, 13), False{}, Equal.sym(Bool, U32.is_eq(T2, 13), True{}, U.nat_eq(T2, 13, en)), n13)))
    case 14n:
      Equal.trans(Bool, d, DataB.of(T.tm.mat(T.tm.name(ks, f2), p3, p4)), False{}, Equal.sym(Bool, DataB.of(T.tm.mat(T.tm.name(ks, f2), p3, p4)), d, ed), ND.mat(T.tm.name(ks, f2), p3, p4))
    case 15n:
      Equal.sym(Bool, False{}, d, ed)
    case 16n:
      Equal.trans(Bool, d, DataB.of(T.tm.three(a => b => t => C.Term.Eql{a, b, t}, p2, p3, p4)), False{}, Equal.sym(Bool, DataB.of(T.tm.three(a => b => t => C.Term.Eql{a, b, t}, p2, p3, p4)), d, ed), ND.three(a => b => t => C.Term.Eql{a, b, t}, p2, p3, p4, a => b => c => {==}))
    case 17n:
      Empty.absurd({d == False{} : Bool}, N.true_ne_false(Equal.trans(Bool, True{}, U32.is_eq(T2, 17), False{}, Equal.sym(Bool, U32.is_eq(T2, 17), True{}, U.nat_eq(T2, 17, en)), n17)))
    case 18n:
      Equal.trans(Bool, d, DataB.of(T.tm.three(a => b => t => C.Term.Rwt{a, b, t}, p2, p3, p4)), False{}, Equal.sym(Bool, DataB.of(T.tm.three(a => b => t => C.Term.Rwt{a, b, t}, p2, p3, p4)), d, ed), ND.three(a => b => t => C.Term.Rwt{a, b, t}, p2, p3, p4, a => b => c => {==}))
    case 19n+k:
      Equal.sym(Bool, False{}, d, ed)

# a cell that the check finds no label, Rfl or pair stands for no Data
def D.oth(+g: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +y: U32,
  n13: {U32.is_eq(Tg(m, y), 13) == False{} : Bool}, n17: {U32.is_eq(Tg(m, y), 17) == False{} : Bool}, n10: {U32.is_eq(Tg(m, y), 10) == False{} : Bool},
  im: {Bool.or(Bool.not(Bool.or(U32.is_eq(Tg(m, y), 1), U32.is_eq(Tg(m, y), 12))), Bool.not(DataB(1n+g, m, ks, img, y))) == True{} : Bool}) ->
  {DataB(1n+g, m, ks, img, y) == False{} : Bool}:
  DO.cell(U32.to_nat(Tg(m, y)), T.tm.quan(Qb(m, y)), y, Fd(2n, m, y), ks, img, T.tm.of(g, m, ks, img, Fd(2n, m, y)), T.tm.of(g, m, ks, img, Fd(3n, m, y)), T.tm.of(g, m, ks, img, Fd(4n, m, y)), Tg(m, y), DataB(1n+g, m, ks, img, y), {==}, n13, n17, n10,
    Equal.cong(Maybe<&2, C.Term>, Bool, r => DataB.of(r), T.tm.cell(U32.to_nat(Tg(m, y)), T.tm.quan(Qb(m, y)), y, Fd(2n, m, y), ks, img, u => T.tm.of(g, m, ks, img, Fd(2n, m, y)), u => T.tm.of(g, m, ks, img, Fd(3n, m, y)), u => T.tm.of(g, m, ks, img, Fd(4n, m, y))), T.tm.of(1n+g, m, ks, img, y),
      TAn(g, m, ks, img, y, U32.to_nat(Tg(m, y)), {==})), im)

# Terms across fuel
# -----------------

def SameU(x: Maybe<&2, C.Term>, -t1: C.Term, -t2: C.Term, h1: {x == Some{t1} : Maybe<&2, C.Term>}, h2: {x == Some{t2} : Maybe<&2, C.Term>}) -> {t1 == t2 : C.Term}:
  Some.inj(t1, t2, Equal.trans(Maybe<&2, C.Term>, Some{t1}, x, Some{t2}, Equal.sym(Maybe<&2, C.Term>, x, Some{t1}, h1), h2))

def Cong2(-k: C.Term -> C.Term -> C.Term, +a: C.Term, -b: C.Term, +a2: C.Term, -b2: C.Term, e: {a == b : C.Term}, e2: {a2 == b2 : C.Term}) -> {k(a, a2) == k(b, b2) : C.Term}:
  %e : {k(a, a2) == k(_, b2) : C.Term}
  %e2 : {k(a, a2) == k(a, _) : C.Term}
  {==}

def Cong3(-k: C.Term -> C.Term -> C.Term -> C.Term, +a: C.Term, -b: C.Term, +a2: C.Term, -b2: C.Term, +a3: C.Term, -b3: C.Term, e: {a == b : C.Term}, e2: {a2 == b2 : C.Term},
  e3: {a3 == b3 : C.Term}) -> {k(a, a2, a3) == k(b, b2, b3) : C.Term}:
  %e : {k(a, a2, a3) == k(_, b2, b3) : C.Term}
  %e2 : {k(a, a2, a3) == k(a, _, b3) : C.Term}
  %e3 : {k(a, a2, a3) == k(a, a2, _) : C.Term}
  {==}

def U.one(-k: C.Term -> C.Term, r: Maybe<&2, C.Term>, s: Maybe<&2, C.Term>, -t1: C.Term, -t2: C.Term, h1: {T.tm.one(k, r) == Some{t1} : Maybe<&2, C.Term>}, h2: {T.tm.one(k, s) == Some{t2} : Maybe<&2, C.Term>},
  i: @a: C.Term -> @b: C.Term -> {r == Some{a} : Maybe<&2, C.Term>} -> {s == Some{b} : Maybe<&2, C.Term>} -> {a == b : C.Term}) -> {t1 == t2 : C.Term}:
  match r s:
    case Some{+a} Some{+b}:
      Equal.trans(C.Term, t1, k(a), t2, Equal.sym(C.Term, k(a), t1, Some.inj(k(a), t1, h1)),
        Equal.trans(C.Term, k(a), k(b), t2, Equal.cong(C.Term, C.Term, k, a, b, i(a, b, {==}, {==})), Some.inj(k(b), t2, h2)))
    case Some{a} None{}:
      Empty.absurd({t1 == t2 : C.Term}, none_some(t2, h2))
    case None{} s2:
      Empty.absurd({t1 == t2 : C.Term}, none_some(t1, h1))

def U.two(-k: C.Term -> C.Term -> C.Term, r: Maybe<&2, C.Term>, r2: Maybe<&2, C.Term>, s: Maybe<&2, C.Term>, s2: Maybe<&2, C.Term>, -t1: C.Term, -t2: C.Term,
  h1: {T.tm.two(k, r, r2) == Some{t1} : Maybe<&2, C.Term>}, h2: {T.tm.two(k, s, s2) == Some{t2} : Maybe<&2, C.Term>},
  i: @a: C.Term -> @b: C.Term -> {r == Some{a} : Maybe<&2, C.Term>} -> {s == Some{b} : Maybe<&2, C.Term>} -> {a == b : C.Term}, j: @a: C.Term -> @b: C.Term -> {r2 == Some{a} : Maybe<&2, C.Term>} -> {s2 == Some{b} : Maybe<&2, C.Term>} -> {a == b : C.Term}) -> {t1 == t2 : C.Term}:
  match r r2 s s2:
    case Some{+a} Some{+a2} Some{+b} Some{+b2}:
      Equal.trans(C.Term, t1, k(a, a2), t2, Equal.sym(C.Term, k(a, a2), t1, Some.inj(k(a, a2), t1, h1)),
        Equal.trans(C.Term, k(a, a2), k(b, b2), t2, Cong2(k, a, b, a2, b2, i(a, b, {==}, {==}), j(a2, b2, {==}, {==})), Some.inj(k(b, b2), t2, h2)))
    case Some{a} Some{a2} Some{b} None{}:
      Empty.absurd({t1 == t2 : C.Term}, none_some(t2, h2))
    case Some{a} Some{a2} None{} s3:
      Empty.absurd({t1 == t2 : C.Term}, none_some(t2, h2))
    case Some{a} None{} s4 s3:
      Empty.absurd({t1 == t2 : C.Term}, none_some(t1, h1))
    case None{} r3 s4 s3:
      Empty.absurd({t1 == t2 : C.Term}, none_some(t1, h1))

def U.three(-k: C.Term -> C.Term -> C.Term -> C.Term, r: Maybe<&2, C.Term>, r2: Maybe<&2, C.Term>, r3: Maybe<&2, C.Term>, s: Maybe<&2, C.Term>, s2: Maybe<&2, C.Term>, s3: Maybe<&2, C.Term>, -t1: C.Term, -t2: C.Term,
  h1: {T.tm.three(k, r, r2, r3) == Some{t1} : Maybe<&2, C.Term>}, h2: {T.tm.three(k, s, s2, s3) == Some{t2} : Maybe<&2, C.Term>},
  i: @a: C.Term -> @b: C.Term -> {r == Some{a} : Maybe<&2, C.Term>} -> {s == Some{b} : Maybe<&2, C.Term>} -> {a == b : C.Term}, j: @a: C.Term -> @b: C.Term -> {r2 == Some{a} : Maybe<&2, C.Term>} -> {s2 == Some{b} : Maybe<&2, C.Term>} -> {a == b : C.Term}, l: @a: C.Term -> @b: C.Term -> {r3 == Some{a} : Maybe<&2, C.Term>} -> {s3 == Some{b} : Maybe<&2, C.Term>} -> {a == b : C.Term}) -> {t1 == t2 : C.Term}:
  match r r2 r3 s s2 s3:
    case Some{+a} Some{+a2} Some{+a3} Some{+b} Some{+b2} Some{+b3}:
      Equal.trans(C.Term, t1, k(a, a2, a3), t2, Equal.sym(C.Term, k(a, a2, a3), t1, Some.inj(k(a, a2, a3), t1, h1)),
        Equal.trans(C.Term, k(a, a2, a3), k(b, b2, b3), t2, Cong3(k, a, b, a2, b2, a3, b3, i(a, b, {==}, {==}), j(a2, b2, {==}, {==}), l(a3, b3, {==}, {==})),
          Some.inj(k(b, b2, b3), t2, h2)))
    case Some{a} Some{a2} Some{a3} Some{b} Some{b2} None{}:
      Empty.absurd({t1 == t2 : C.Term}, none_some(t2, h2))
    case Some{a} Some{a2} Some{a3} Some{b} None{} x:
      Empty.absurd({t1 == t2 : C.Term}, none_some(t2, h2))
    case Some{a} Some{a2} Some{a3} None{} x y:
      Empty.absurd({t1 == t2 : C.Term}, none_some(t2, h2))
    case Some{a} Some{a2} None{} x y z:
      Empty.absurd({t1 == t2 : C.Term}, none_some(t1, h1))
    case Some{a} None{} w x y z:
      Empty.absurd({t1 == t2 : C.Term}, none_some(t1, h1))
    case None{} v w x y z:
      Empty.absurd({t1 == t2 : C.Term}, none_some(t1, h1))

def U.mat(n: Maybe<&2, List<&2, U32>>, r: Maybe<&2, C.Term>, r2: Maybe<&2, C.Term>, s: Maybe<&2, C.Term>, s2: Maybe<&2, C.Term>, -t1: C.Term, -t2: C.Term,
  h1: {T.tm.mat(n, r, r2) == Some{t1} : Maybe<&2, C.Term>}, h2: {T.tm.mat(n, s, s2) == Some{t2} : Maybe<&2, C.Term>},
  i: @a: C.Term -> @b: C.Term -> {r == Some{a} : Maybe<&2, C.Term>} -> {s == Some{b} : Maybe<&2, C.Term>} -> {a == b : C.Term}, j: @a: C.Term -> @b: C.Term -> {r2 == Some{a} : Maybe<&2, C.Term>} -> {s2 == Some{b} : Maybe<&2, C.Term>} -> {a == b : C.Term}) -> {t1 == t2 : C.Term}:
  match n r r2 s s2:
    case Some{+k} Some{+a} Some{+a2} Some{+b} Some{+b2}:
      Equal.trans(C.Term, t1, C.Term.Mat{k, a, a2}, t2, Equal.sym(C.Term, C.Term.Mat{k, a, a2}, t1, Some.inj(C.Term.Mat{k, a, a2}, t1, h1)),
        Equal.trans(C.Term, C.Term.Mat{k, a, a2}, C.Term.Mat{k, b, b2}, t2,
          Cong2(x => y => C.Term.Mat{k, x, y}, a, b, a2, b2, i(a, b, {==}, {==}), j(a2, b2, {==}, {==})), Some.inj(C.Term.Mat{k, b, b2}, t2, h2)))
    case Some{k} Some{a} Some{a2} Some{b} None{}:
      Empty.absurd({t1 == t2 : C.Term}, none_some(t2, h2))
    case Some{k} Some{a} Some{a2} None{} x:
      Empty.absurd({t1 == t2 : C.Term}, none_some(t2, h2))
    case Some{k} Some{a} None{} x y:
      Empty.absurd({t1 == t2 : C.Term}, none_some(t1, h1))
    case Some{k} None{} w x y:
      Empty.absurd({t1 == t2 : C.Term}, none_some(t1, h1))
    case None{} v w x y:
      Empty.absurd({t1 == t2 : C.Term}, none_some(t1, h1))

# a cell's two terms, at two fuels, are one, when its parts' are
def UCell(n: Nat, +q: C.Quan, +y: U32, +f2: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +r2: Maybe<&2, C.Term>, +r3: Maybe<&2, C.Term>, +r4: Maybe<&2, C.Term>, +s2: Maybe<&2, C.Term>, +s3: Maybe<&2, C.Term>, +s4: Maybe<&2, C.Term>, -t1: C.Term, -t2: C.Term,
  h1: {T.tm.cell(n, q, y, f2, ks, img, u => r2, u => r3, u => r4) == Some{t1} : Maybe<&2, C.Term>},
  h2: {T.tm.cell(n, q, y, f2, ks, img, u => s2, u => s3, u => s4) == Some{t2} : Maybe<&2, C.Term>},
  i2: @a: C.Term -> @b: C.Term -> {r2 == Some{a} : Maybe<&2, C.Term>} -> {s2 == Some{b} : Maybe<&2, C.Term>} -> {a == b : C.Term}, i3: @a: C.Term -> @b: C.Term -> {r3 == Some{a} : Maybe<&2, C.Term>} -> {s3 == Some{b} : Maybe<&2, C.Term>} -> {a == b : C.Term}, i4: @a: C.Term -> @b: C.Term -> {r4 == Some{a} : Maybe<&2, C.Term>} -> {s4 == Some{b} : Maybe<&2, C.Term>} -> {a == b : C.Term}) -> {t1 == t2 : C.Term}:
  match n:
    case 0n:
      SameU(T.tm.cell(0n, q, y, f2, ks, img, u => r2, u => r3, u => r4), t1, t2, h1, h2)
    case 1n:
      SameU(T.tm.cell(1n, q, y, f2, ks, img, u => r2, u => r3, u => r4), t1, t2, h1, h2)
    case 2n:
      U.two(a => b => C.Term.Ann{a, b}, r2, r3, s2, s3, t1, t2, h1, h2, i2, i3)
    case 3n:
      U.two(a => b => C.Term.Let{q, a, b}, r2, r3, s2, s3, t1, t2, h1, h2, i2, i3)
    case 4n:
      U.one(a => C.Term.Typ{a}, r2, s2, t1, t2, h1, h2, i2)
    case 5n:
      U.two(a => b => C.Term.Min{a, b}, r2, r3, s2, s3, t1, t2, h1, h2, i2, i3)
    case 6n:
      U.two(a => b => C.Term.All{q, a, b}, r2, r3, s2, s3, t1, t2, h1, h2, i2, i3)
    case 7n:
      U.one(a => C.Term.Lam{q, a}, r2, s2, t1, t2, h1, h2, i2)
    case 8n:
      U.two(a => b => C.Term.App{q, a, b}, r2, r3, s2, s3, t1, t2, h1, h2, i2, i3)
    case 9n:
      U.two(a => b => C.Term.Sig{q, a, b}, r2, r3, s2, s3, t1, t2, h1, h2, i2, i3)
    case 10n:
      U.two(a => b => C.Term.Tup{q, a, b}, r2, r3, s2, s3, t1, t2, h1, h2, i2, i3)
    case 11n:
      U.one(a => C.Term.Prj{a}, r2, s2, t1, t2, h1, h2, i2)
    case 12n:
      SameU(T.tm.cell(12n, q, y, f2, ks, img, u => r2, u => r3, u => r4), t1, t2, h1, h2)
    case 13n:
      SameU(T.tm.cell(13n, q, y, f2, ks, img, u => r2, u => r3, u => r4), t1, t2, h1, h2)
    case 14n:
      U.mat(T.tm.name(ks, f2), r3, r4, s3, s4, t1, t2, h1, h2, i3, i4)
    case 15n:
      SameU(T.tm.cell(15n, q, y, f2, ks, img, u => r2, u => r3, u => r4), t1, t2, h1, h2)
    case 16n:
      U.three(a => b => t => C.Term.Eql{a, b, t}, r2, r3, r4, s2, s3, s4, t1, t2, h1, h2, i2, i3, i4)
    case 17n:
      SameU(T.tm.cell(17n, q, y, f2, ks, img, u => r2, u => r3, u => r4), t1, t2, h1, h2)
    case 18n:
      U.three(a => b => t => C.Term.Rwt{a, b, t}, r2, r3, r4, s2, s3, s4, t1, t2, h1, h2, i2, i3, i4)
    case 19n+k:
      Empty.absurd({t1 == t2 : C.Term}, none_some(t1, h1))

# a cell stands for one term, whatever the fuel
def TUniq(f1: Nat, f2: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, -t1: C.Term, -t2: C.Term,
  h1: {T.tm.of(f1, m, ks, img, c) == Some{t1} : Maybe<&2, C.Term>}, h2: {T.tm.of(f2, m, ks, img, c) == Some{t2} : Maybe<&2, C.Term>}) -> {t1 == t2 : C.Term}:
  match f1 f2:
    case 0n _:
      Empty.absurd({t1 == t2 : C.Term}, none_some(t1, h1))
    case 1n+g1 0n:
      Empty.absurd({t1 == t2 : C.Term}, none_some(t2, h2))
    case 1n+(+g1) 1n+(+g2):
      +x = C.Cir.Cells.get(m, c)
      +p2 = C.Cir.Cell.get(2n, x)
      +p3 = C.Cir.Cell.get(3n, x)
      +p4 = C.Cir.Cell.get(4n, x)
      UCell(U32.to_nat(U32.and(C.Cir.Cell.get(0n, x), 63)), T.tm.quan(U32.and(U32.shrn(C.Cir.Cell.get(0n, x), 6n), 3)), c, p2, ks, img,
        T.tm.of(g1, m, ks, img, p2), T.tm.of(g1, m, ks, img, p3), T.tm.of(g1, m, ks, img, p4),
        T.tm.of(g2, m, ks, img, p2), T.tm.of(g2, m, ks, img, p3), T.tm.of(g2, m, ks, img, p4), t1, t2, h1, h2,
        a => b => e1 => e2 => TUniq(g1, g2, m, ks, img, p2, a, b, e1, e2), a => b => e1 => e2 => TUniq(g1, g2, m, ks, img, p3, a, b, e1, e2),
        a => b => e1 => e2 => TUniq(g1, g2, m, ks, img, p4, a, b, e1, e2))

# The check's stack and flags
# ---------------------------

# a check cell s on the stack, for the term cell y, whose term, within f
# levels, is t
type SE is Data:
  SE{s: U32, y: U32, f: Nat, t: C.Term}

# a cell that the check flagged, whose term within f levels is t
type NE is Data:
  NE{y: U32, f: Nat, t: C.Term}

def Top(S: List<&2, SE>) -> U32:
  match S:
    case Nil{}:
      0
    case Con{SE{s, _, _, _}, _}:
      s

def SCs(S: List<&2, SE>) -> List<&2, U32>:
  match S:
    case Nil{}:
      Nil{}
    case Con{SE{s, _, _, _}, rest}:
      Con{s, SCs(rest)}

def SYs(S: List<&2, SE>) -> List<&2, U32>:
  match S:
    case Nil{}:
      Nil{}
    case Con{SE{_, y, _, _}, rest}:
      Con{y, SYs(rest)}

def NCs(N: List<&2, NE>) -> List<&2, U32>:
  match N:
    case Nil{}:
      Nil{}
    case Con{NE{y, _, _}, rest}:
      Con{y, NCs(rest)}

# every term on the stack is Data
def AllD(S: List<&2, SE>) -> Bool:
  match S:
    case Nil{}:
      True{}
    case Con{SE{_, _, _, t}, rest}:
      C.Term.is_data(t) && AllD(rest)

def AllND(N: List<&2, NE>) -> Bool:
  match N:
    case Nil{}:
      True{}
    case Con{NE{_, _, t}, rest}:
      C.Term.is_data(t) && AllND(rest)

# a stack entry: its check cell, of header 44, holds y in field 2 and the
# next entry's cell in field 1; y's term within f levels is t
def EF(+m: C.Cir.Cells, +m0: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +L: List<&2, U32>, +K0: List<&2, U32>,
  e: SE, +nxt: U32, +rest: List<&2, SE>) -> Data:
  match e:
    case SE{+s, +y, +f, +t}:
      Sigma<&2, &2, {U32.is_zero(s) == False{} : Bool}, _ =>
      Sigma<&2, &2, {Mem(s, L) == False{} : Bool}, _ =>
      Sigma<&2, &2, {Mem(s, K0) == False{} : Bool}, _ =>
      Sigma<&2, &2, {Mem(s, SCs(rest)) == False{} : Bool}, _ =>
      Sigma<&2, &2, {Fd(0n, m, s) == 44 : U32}, _ =>
      Sigma<&2, &2, {Fd(1n, m, s) == nxt : U32}, _ =>
      Sigma<&2, &2, {Fd(2n, m, s) == y : U32}, _ =>
      Sigma<&2, &2, {T.tm.of(f, m0, ks, img, y) == Some{t} : Maybe<&2, C.Term>}, _ =>
      Sigma<&2, &2, {RdIn(f, m0, y, L) == True{} : Bool}, _ =>
      {DOk(f, m0, ks, img, y) == True{} : Bool}>>>>>>>>>

def Stk(+m: C.Cir.Cells, +m0: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +L: List<&2, U32>, +K0: List<&2, U32>,
  S: List<&2, SE>) -> Data:
  match S:
    case Nil{}:
      Unit
    case Con{e, +rest}:
      Sigma<&2, &2, EF(m, m0, ks, img, L, K0, e, Top(rest), rest), _ => Stk(m, m0, ks, img, L, K0, rest)>

# a flagged cell's facts
def NFF(+m0: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, N: List<&2, NE>) -> Data:
  match N:
    case Nil{}:
      Unit
    case Con{NE{+y, +f, +t}, rest}:
      Sigma<&2, &2, {T.tm.of(f, m0, ks, img, y) == Some{t} : Maybe<&2, C.Term>}, _ =>
      Sigma<&2, &2, {DOk(f, m0, ks, img, y) == True{} : Bool}, _ => NFF(m0, ks, img, rest)>>

# c is settled: on the stack, flagged by the check, or flagged before it
def Setl(+m0: C.Cir.Cells, +c: U32, +S: List<&2, SE>, +NC: List<&2, U32>) -> Bool:
  Mem(c, SYs(S)) || (Mem(c, NC) || FlB(m0, c))

# a flagged cell is a label, Rfl, or a pair whose parts that the check
# reaches are settled
def Cl(+m0: C.Cir.Cells, +y: U32, +S: List<&2, SE>, +NC: List<&2, U32>) -> Bool:
  +t = Tg(m0, y)
  U32.is_eq(t, 13) || (U32.is_eq(t, 17) || (U32.is_eq(t, 10) &&
    (Setl(m0, Fd(3n, m0, y), S, NC) && (U32.is_eq(Qb(m0, y), 0) || Setl(m0, Fd(2n, m0, y), S, NC)))))

def NFOk(+m0: C.Cir.Cells, N: List<&2, U32>, +S: List<&2, SE>, +NC: List<&2, U32>) -> Bool:
  match N:
    case Nil{}:
      True{}
    case Con{+y, rest}:
      Cl(m0, y, S, NC) && NFOk(m0, rest, S, NC)

def WFl1(w: Wr, +NC: List<&2, U32>) -> Bool:
  match w:
    case Wr.one{_, _}:
      True{}
    case Wr.flag{+c, +fl}:
      Mem(c, NC) && U32.is_eq(fl, 512)
    case Wr.any{_, _}:
      True{}

# every flag that the writes set is DATA, on a cell of NC
def WFl(ws: List<&2, Wr>, +NC: List<&2, U32>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{w, rest}:
      WFl1(w, NC) && WFl(rest, NC)

# no cell is in both lists
def Disj(A: List<&2, U32>, +B: List<&2, U32>) -> Bool:
  match A:
    case Nil{}:
      True{}
    case Con{+c, rest}:
      Bool.not(Mem(c, B)) && Disj(rest, B)

# Lists of cells
# --------------

def Cat(A: List<&2, U32>, B: List<&2, U32>) -> List<&2, U32>:
  match A:
    case Nil{}:
      B
    case Con{h, t}:
      Con{h, Cat(t, B)}

def Bo.or_l(a: Bool, -b: Bool, h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, h) : {Bool.or(_, b) == True{} : Bool}
  {==}

def Bo.or_r(a: Bool, b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def Bo.f_t(-b: Bool, h: {b == False{} : Bool}, e: {b == True{} : Bool}) -> Empty:
  N.true_ne_false(Equal.trans(Bool, True{}, b, False{}, Equal.sym(Bool, b, True{}, e), h))

def Mem.head(+c: U32, -t: List<&2, U32>) -> {Mem(c, Con{c, t}) == True{} : Bool}:
  Bo.or_l(U32.is_eq(c, c), Mem(c, t), U.refl(c))

def Mem.tail(+c: U32, +h: U32, t: List<&2, U32>, e: {Mem(c, t) == True{} : Bool}) -> {Mem(c, Con{h, t}) == True{} : Bool}:
  Bo.or_r(U32.is_eq(c, h), Mem(c, t), e)

def Mem.cat_r(+c: U32, A: List<&2, U32>, +B: List<&2, U32>, e: {Mem(c, B) == True{} : Bool}) -> {Mem(c, Cat(A, B)) == True{} : Bool}:
  match A:
    case Nil{}:
      e
    case Con{+h, +t}:
      Mem.tail(c, h, Cat(t, B), Mem.cat_r(c, t, B, e))

def Mem.cat_l.if(b: Bool, +c: U32, +t: List<&2, U32>, +B: List<&2, U32>, e: {Bool.or(b, Mem(c, t)) == True{} : Bool},
  r: {Mem(c, t) == True{} : Bool} -> {Mem(c, Cat(t, B)) == True{} : Bool}) -> {Bool.or(b, Mem(c, Cat(t, B))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      r(e)

def Mem.cat_l(+c: U32, A: List<&2, U32>, +B: List<&2, U32>, e: {Mem(c, A) == True{} : Bool}) -> {Mem(c, Cat(A, B)) == True{} : Bool}:
  match A:
    case Nil{}:
      tf({Mem(c, B) == True{} : Bool}, e)
    case Con{+h, +t}:
      Mem.cat_l.if(U32.is_eq(c, h), c, t, B, e, x => Mem.cat_l(c, t, B, x))

def AllCell.mem.if(b: Bool, +c: U32, +h2: U32, +t: List<&2, U32>, +im: U32, +fs: U32, +nx: U32, eb: {U32.is_eq(c, h2) == b : Bool},
  h: {Bool.and(C.Cir.is_cell(h2, im, fs, nx), AllCell(t, im, fs, nx)) == True{} : Bool}, e: {Bool.or(b, Mem(c, t)) == True{} : Bool},
  r: {AllCell(t, im, fs, nx) == True{} : Bool} -> {Mem(c, t) == True{} : Bool} -> {True{} == C.Cir.is_cell(c, im, fs, nx) : Bool}) ->
  {True{} == C.Cir.is_cell(c, im, fs, nx) : Bool}:
  match b:
    case True{}:
      +h3 = h
      %Equal.sym(U32, c, h2, U.eq_t(c, h2, eb)) : {True{} == C.Cir.is_cell(_, im, fs, nx) : Bool}
      Equal.sym(Bool, C.Cir.is_cell(h2, im, fs, nx), True{}, Bo.and_l(C.Cir.is_cell(h2, im, fs, nx), AllCell(t, im, fs, nx), h3))
    case False{}:
      +h3 = h
      r(Bo.and_r(C.Cir.is_cell(h2, im, fs, nx), AllCell(t, im, fs, nx), h3), e)

# a cell of L is one that Cir may access
def AllCell.mem(L: List<&2, U32>, +c: U32, +im: U32, +fs: U32, +nx: U32, h: {AllCell(L, im, fs, nx) == True{} : Bool},
  e: {Mem(c, L) == True{} : Bool}) -> {True{} == C.Cir.is_cell(c, im, fs, nx) : Bool}:
  match L:
    case Nil{}:
      tf({True{} == C.Cir.is_cell(c, im, fs, nx) : Bool}, e)
    case Con{+h2, +t}:
      AllCell.mem.if(U32.is_eq(c, h2), c, h2, t, im, fs, nx, {==}, h, e, ht => et => AllCell.mem(t, c, im, fs, nx, ht, et))

def Sub(A: List<&2, U32>, +B: List<&2, U32>) -> Bool:
  match A:
    case Nil{}:
      True{}
    case Con{+c, rest}:
      Mem(c, B) && Sub(rest, B)

def Sub.mem.if(b: Bool, +c: U32, +a: U32, +rest: List<&2, U32>, +B: List<&2, U32>, eb: {U32.is_eq(c, a) == b : Bool},
  ha: {Mem(a, B) == True{} : Bool}, e: {Bool.or(b, Mem(c, rest)) == True{} : Bool}, r: {Mem(c, rest) == True{} : Bool} -> {Mem(c, B) == True{} : Bool}) ->
  {Mem(c, B) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(U32, c, a, U.eq_t(c, a, eb)) : {Mem(_, B) == True{} : Bool}
      ha
    case False{}:
      r(e)

def Sub.mem(A: List<&2, U32>, +B: List<&2, U32>, +c: U32, h: {Sub(A, B) == True{} : Bool}, e: {Mem(c, A) == True{} : Bool}) -> {Mem(c, B) == True{} : Bool}:
  match A:
    case Nil{}:
      tf({Mem(c, B) == True{} : Bool}, e)
    case Con{+a, +rest}:
      +h2 = h
      Sub.mem.if(U32.is_eq(c, a), c, a, rest, B, {==}, Bo.and_l(Mem(a, B), Sub(rest, B), h2), e, x => Sub.mem(rest, B, c, Bo.and_r(Mem(a, B), Sub(rest, B), h2), x))


def Bo.and_i(a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

# Settled, as the check goes on
# -----------------------------

def SetStep.b(b1: Bool, b2: Bool, b3: Bool, b4: Bool, -G: Type, h: {Bool.or(Bool.or(b1, b2), Bool.or(b3, b4)) == True{} : Bool},
  k1: {b1 == True{} : Bool} -> G, k2: {b2 == True{} : Bool} -> G, k3: {b3 == True{} : Bool} -> G, k4: {b4 == True{} : Bool} -> G) -> G:
  match b1:
    case True{}:
      k1({==})
    case False{}:
      match b2:
        case True{}:
          k2({==})
        case False{}:
          match b3:
            case True{}:
              k3({==})
            case False{}:
              k4(h)

def SetStep.k1(+m0: C.Cir.Cells, +c: U32, +y: U32, +Sb: List<&2, SE>, +NCb: List<&2, U32>, hyb: {Setl(m0, y, Sb, NCb) == True{} : Bool},
  e: {U32.is_eq(c, y) == True{} : Bool}) -> {Setl(m0, c, Sb, NCb) == True{} : Bool}:
  %Equal.sym(U32, c, y, U.eq_t(c, y, e)) : {Setl(m0, _, Sb, NCb) == True{} : Bool}
  hyb

# a cell settled before a round of the check, where the entry of y left the
# stack for Sb, and the flagged cells grew to NCb, is settled after it
def SetStep(+m0: C.Cir.Cells, +c: U32, +s: U32, +y: U32, +f: Nat, +t: C.Term, +S2: List<&2, SE>, +Sb: List<&2, SE>,
  +NCa: List<&2, U32>, +NCb: List<&2, U32>, +hyb: {Setl(m0, y, Sb, NCb) == True{} : Bool}, +hsub: {Sub(SYs(S2), SYs(Sb)) == True{} : Bool},
  +hnc: {Sub(NCa, NCb) == True{} : Bool}, h: {Setl(m0, c, Con{SE{s, y, f, t}, S2}, NCa) == True{} : Bool}) -> {Setl(m0, c, Sb, NCb) == True{} : Bool}:
  SetStep.b(U32.is_eq(c, y), Mem(c, SYs(S2)), Mem(c, NCa), FlB(m0, c), {Setl(m0, c, Sb, NCb) == True{} : Bool}, h,
    e => SetStep.k1(m0, c, y, Sb, NCb, hyb, e),
    e => Bo.or_l(Mem(c, SYs(Sb)), Bool.or(Mem(c, NCb), FlB(m0, c)), Sub.mem(SYs(S2), SYs(Sb), c, hsub, e)),
    e => Bo.or_r(Mem(c, SYs(Sb)), Bool.or(Mem(c, NCb), FlB(m0, c)), Bo.or_l(Mem(c, NCb), FlB(m0, c), Sub.mem(NCa, NCb, c, hnc, e))),
    e => Bo.or_r(Mem(c, SYs(Sb)), Bool.or(Mem(c, NCb), FlB(m0, c)), Bo.or_r(Mem(c, NCb), FlB(m0, c), e)))

def ClM.b3(bq: Bool, s2: Bool, s2b: Bool, h: {Bool.or(bq, s2) == True{} : Bool},
  i2: {s2 == True{} : Bool} -> {s2b == True{} : Bool}) -> {Bool.or(bq, s2b) == True{} : Bool}:
  match bq:
    case True{}:
      {==}
    case False{}:
      i2(h)

def ClM.b2(bq: Bool, s2: Bool, s2b: Bool, s3b: Bool, e3: {s3b == True{} : Bool}, h: {Bool.or(bq, s2) == True{} : Bool},
  i2: {s2 == True{} : Bool} -> {s2b == True{} : Bool}) -> {Bool.and(s3b, Bool.or(bq, s2b)) == True{} : Bool}:
  %Equal.sym(Bool, s3b, True{}, e3) : {Bool.and(_, Bool.or(bq, s2b)) == True{} : Bool}
  ClM.b3(bq, s2, s2b, h, i2)

def ClM.b(b13: Bool, b17: Bool, b10: Bool, s3: Bool, bq: Bool, s2: Bool, s3b: Bool, s2b: Bool,
  h: {Bool.or(b13, Bool.or(b17, Bool.and(b10, Bool.and(s3, Bool.or(bq, s2))))) == True{} : Bool},
  i3: {s3 == True{} : Bool} -> {s3b == True{} : Bool}, i2: {s2 == True{} : Bool} -> {s2b == True{} : Bool}) ->
  {Bool.or(b13, Bool.or(b17, Bool.and(b10, Bool.and(s3b, Bool.or(bq, s2b))))) == True{} : Bool}:
  match b13:
    case True{}:
      {==}
    case False{}:
      match b17:
        case True{}:
          {==}
        case False{}:
          match b10:
            case False{}:
              tf({False{} == True{} : Bool}, h)
            case True{}:
              match s3:
                case False{}:
                  tf({Bool.and(s3b, Bool.or(bq, s2b)) == True{} : Bool}, h)
                case True{}:
                  ClM.b2(bq, s2, s2b, s3b, i3({==}), h, i2)


def ClM(+m0: C.Cir.Cells, +z: U32, +Sa: List<&2, SE>, +NCa: List<&2, U32>, +Sb: List<&2, SE>, +NCb: List<&2, U32>,
  h3: {Setl(m0, Fd(3n, m0, z), Sa, NCa) == True{} : Bool} -> {Setl(m0, Fd(3n, m0, z), Sb, NCb) == True{} : Bool},
  h2: {Setl(m0, Fd(2n, m0, z), Sa, NCa) == True{} : Bool} -> {Setl(m0, Fd(2n, m0, z), Sb, NCb) == True{} : Bool},
  h: {Cl(m0, z, Sa, NCa) == True{} : Bool}) -> {Cl(m0, z, Sb, NCb) == True{} : Bool}:
  +t = Tg(m0, z)
  ClM.b(U32.is_eq(t, 13), U32.is_eq(t, 17), U32.is_eq(t, 10), Setl(m0, Fd(3n, m0, z), Sa, NCa), U32.is_eq(Qb(m0, z), 0),
    Setl(m0, Fd(2n, m0, z), Sa, NCa), Setl(m0, Fd(3n, m0, z), Sb, NCb), Setl(m0, Fd(2n, m0, z), Sb, NCb), h, h3, h2)

# the closures of the flagged cells, after a round of the check
def NFOkM(N: List<&2, U32>, +m0: C.Cir.Cells, +s: U32, +y: U32, +f: Nat, +t: C.Term, +S2: List<&2, SE>, +Sb: List<&2, SE>,
  +NCa: List<&2, U32>, +NCb: List<&2, U32>, +hyb: {Setl(m0, y, Sb, NCb) == True{} : Bool}, +hsub: {Sub(SYs(S2), SYs(Sb)) == True{} : Bool},
  +hnc: {Sub(NCa, NCb) == True{} : Bool}, h: {NFOk(m0, N, Con{SE{s, y, f, t}, S2}, NCa) == True{} : Bool}) -> {NFOk(m0, N, Sb, NCb) == True{} : Bool}:
  match N:
    case Nil{}:
      {==}
    case Con{+z, +rest}:
      +h2 = h
      +Sa = {Con{SE{s, y, f, t}, S2} : List<&2, SE>}
      Bo.and_i(Cl(m0, z, Sb, NCb), NFOk(m0, rest, Sb, NCb),
        ClM(m0, z, Sa, NCa, Sb, NCb, x => SetStep(m0, Fd(3n, m0, z), s, y, f, t, S2, Sb, NCa, NCb, hyb, hsub, hnc, x),
          x => SetStep(m0, Fd(2n, m0, z), s, y, f, t, S2, Sb, NCa, NCb, hyb, hsub, hnc, x), Bo.and_l(Cl(m0, z, Sa, NCa), NFOk(m0, rest, Sa, NCa), h2)),
        NFOkM(rest, m0, s, y, f, t, S2, Sb, NCa, NCb, hyb, hsub, hnc, Bo.and_r(Cl(m0, z, Sa, NCa), NFOk(m0, rest, Sa, NCa), h2)))

# Flags
# -----

def F0.cell1(x: C.Cir.Cell, +v: U32) -> {C.Cir.Cell.get(0n, x) == C.Cir.Cell.get(0n, C.Cir.Cell.set(1n, x, v)) : U32}:
  match x:
    case C.Cir.Cell{a, b, p, q, r}:
      {==}

def F0.set1.if(b: Bool, +m: C.Cir.Cells, +c: U32, +v: U32, +y: U32, eb: {U32.is_eq(y, c) == b : Bool}) ->
  {Fd(0n, m, y) == Fd(0n, Set1(m, c, v), y) : U32}:
  match b:
    case True{}:
      %Equal.sym(U32, y, c, U.eq_t(y, c, eb)) : {Fd(0n, m, _) == Fd(0n, Set1(m, c, v), _) : U32}
      +x = C.Cir.Cell.set(1n, C.Cir.Cells.get(m, c), v)
      %Equal.sym(C.Cir.Cell, C.Cir.Cells.get(C.Cir.Cells.set(m, c, x), c), x, Ce.get_set(m, c, x)) :
        {C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)) == C.Cir.Cell.get(0n, _) : U32}
      F0.cell1(C.Cir.Cells.get(m, c), v)
    case False{}:
      Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(m, y), C.Cir.Cells.get(Set1(m, c, v), y),
        Ce.get_other(m, y, c, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, c), v), e => U.eq_f(y, c, eb, e)))

# field 1 set keeps field 0
def F0.set1(+m: C.Cir.Cells, +c: U32, +v: U32, +y: U32) -> {Fd(0n, m, y) == Fd(0n, Set1(m, c, v), y) : U32}:
  F0.set1.if(U32.is_eq(y, c), m, c, v, y, {==})

def FlB.eq(+m: C.Cir.Cells, +m2: C.Cir.Cells, +y: U32, e: {Fd(0n, m, y) == Fd(0n, m2, y) : U32}) -> {FlB(m, y) == FlB(m2, y) : Bool}:
  Equal.cong(U32, Bool, z => U32.is_ne(U32.and(z, 512), 0), Fd(0n, m, y), Fd(0n, m2, y), e)

def FlB.other(+m: C.Cir.Cells, +c: U32, +x: C.Cir.Cell, +y: U32, ne: {y == c : U32} -> Empty) ->
  {FlB(m, y) == FlB(C.Cir.Cells.set(m, c, x), y) : Bool}:
  FlB.eq(m, C.Cir.Cells.set(m, c, x), y,
    Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(m, y), C.Cir.Cells.get(C.Cir.Cells.set(m, c, x), y), Ce.get_other(m, y, c, x, ne)))

def FlW1.flag(b: Bool, +m: C.Cir.Cells, +c: U32, +fl: U32, +y: U32, +NC: List<&2, U32>, eb: {U32.is_eq(y, c) == b : Bool},
  fo: {Bool.and(Mem(c, NC), U32.is_eq(fl, 512)) == True{} : Bool}, h: {FlB(SetF(m, c, fl), y) == True{} : Bool}) ->
  {Bool.or(Mem(y, NC), FlB(m, y)) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(U32, y, c, U.eq_t(y, c, eb)) : {Bool.or(Mem(_, NC), FlB(m, _)) == True{} : Bool}
      Bo.or_l(Mem(c, NC), FlB(m, c), Bo.and_l(Mem(c, NC), U32.is_eq(fl, 512), fo))
    case False{}:
      +x = C.Cir.Cells.get(m, c)
      Bo.or_r(Mem(y, NC), FlB(m, y), Equal.trans(Bool, FlB(m, y), FlB(SetF(m, c, fl), y), True{},
        FlB.other(m, c, C.Cir.Cell.set(0n, x, U32.or(C.Cir.Cell.get(0n, x), fl)), y, e => U.eq_f(y, c, eb, e)), h))

# a cell of L flagged after one write was flagged before it, or by the check
def FlW1(w: Wr, +m: C.Cir.Cells, +y: U32, +L: List<&2, U32>, +K0: List<&2, U32>, +NC: List<&2, U32>, o: {WOk1(w, L, K0) == True{} : Bool},
  fo: {WFl1(w, NC) == True{} : Bool}, +hy: {Mem(y, L) == True{} : Bool}, h: {FlB(Do(m, w), y) == True{} : Bool}) ->
  {Bool.or(Mem(y, NC), FlB(m, y)) == True{} : Bool}:
  match w:
    case Wr.one{+c, +v}:
      Bo.or_r(Mem(y, NC), FlB(m, y), Equal.trans(Bool, FlB(m, y), FlB(Set1(m, c, v), y), True{}, FlB.eq(m, Set1(m, c, v), y, F0.set1(m, c, v, y)), h))
    case Wr.flag{+c, +fl}:
      FlW1.flag(U32.is_eq(y, c), m, c, fl, y, NC, {==}, fo, h)
    case Wr.any{+c, +x}:
      +hc = WOk1.nk(Mem(c, L), Bool.not(Mem(c, K0)), o)
      Bo.or_r(Mem(y, NC), FlB(m, y), Equal.trans(Bool, FlB(m, y), FlB(C.Cir.Cells.set(m, c, x), y), True{},
        FlB.other(m, c, x, y, e => Mem.ne(y, c, L, hy, hc, e)), h))

def FlW.c(b: Bool, d: Bool, -e: Bool, r: {Bool.or(b, d) == True{} : Bool}, k: {d == True{} : Bool} -> {Bool.or(b, e) == True{} : Bool}) ->
  {Bool.or(b, e) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      k(r)

# a cell of L flagged after the writes was flagged before them, or by the check
def FlW(ws: List<&2, Wr>, +m: C.Cir.Cells, +y: U32, +L: List<&2, U32>, +K0: List<&2, U32>, +NC: List<&2, U32>,
  ok: {WOk(ws, L, K0) == True{} : Bool}, fo: {WFl(ws, NC) == True{} : Bool}, +hy: {Mem(y, L) == True{} : Bool},
  h: {FlB(Apply(ws, m), y) == True{} : Bool}) -> {Bool.or(Mem(y, NC), FlB(m, y)) == True{} : Bool}:
  match ws:
    case Nil{}:
      Bo.or_r(Mem(y, NC), FlB(m, y), h)
    case Con{+w, +rest}:
      +ok2 = ok
      +fo2 = fo
      FlW.c(Mem(y, NC), FlB(Apply(rest, m), y), FlB(m, y),
        FlW1(w, Apply(rest, m), y, L, K0, NC, Bo.and_l(WOk1(w, L, K0), WOk(rest, L, K0), ok2), Bo.and_l(WFl1(w, NC), WFl(rest, NC), fo2), hy, h),
        x => FlW(rest, m, y, L, K0, NC, Bo.and_r(WOk1(w, L, K0), WOk(rest, L, K0), ok2), Bo.and_r(WFl1(w, NC), WFl(rest, NC), fo2), hy, x))

# The flagged cells are Data
# --------------------------

def NFOk.get.if(b: Bool, +m0: C.Cir.Cells, +z: U32, +a: U32, +rest: List<&2, U32>, +S: List<&2, SE>, +NC: List<&2, U32>,
  eb: {U32.is_eq(z, a) == b : Bool}, ha: {Cl(m0, a, S, NC) == True{} : Bool}, e: {Bool.or(b, Mem(z, rest)) == True{} : Bool},
  r: {Mem(z, rest) == True{} : Bool} -> {Cl(m0, z, S, NC) == True{} : Bool}) -> {Cl(m0, z, S, NC) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(U32, z, a, U.eq_t(z, a, eb)) : {Cl(m0, _, S, NC) == True{} : Bool}
      ha
    case False{}:
      r(e)

def NFOk.get(N: List<&2, U32>, +m0: C.Cir.Cells, +S: List<&2, SE>, +NC: List<&2, U32>, +z: U32, h: {NFOk(m0, N, S, NC) == True{} : Bool},
  e: {Mem(z, N) == True{} : Bool}) -> {Cl(m0, z, S, NC) == True{} : Bool}:
  match N:
    case Nil{}:
      tf({Cl(m0, z, S, NC) == True{} : Bool}, e)
    case Con{+a, +rest}:
      +h2 = h
      NFOk.get.if(U32.is_eq(z, a), m0, z, a, rest, S, NC, {==}, Bo.and_l(Cl(m0, a, S, NC), NFOk(m0, rest, S, NC), h2), e,
        x => NFOk.get(rest, m0, S, NC, z, Bo.and_r(Cl(m0, a, S, NC), NFOk(m0, rest, S, NC), h2), x))

# a flagged cell's facts, by its cell
def NEx(+m0: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +z: U32) -> Data:
  Sigma<&2, &2, Nat, f => Sigma<&2, &2, C.Term, t => Sigma<&2, &2, {T.tm.of(f, m0, ks, img, z) == Some{t} : Maybe<&2, C.Term>}, _ =>
    {DOk(f, m0, ks, img, z) == True{} : Bool}>>>

def NFF.get.if(b: Bool, +m0: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +z: U32, +y: U32, +f: Nat, +t: C.Term,
  +rest: List<&2, NE>, eb: {U32.is_eq(z, y) == b : Bool}, h1: {T.tm.of(f, m0, ks, img, y) == Some{t} : Maybe<&2, C.Term>},
  h2: {DOk(f, m0, ks, img, y) == True{} : Bool}, e: {Bool.or(b, Mem(z, NCs(rest))) == True{} : Bool},
  r: {Mem(z, NCs(rest)) == True{} : Bool} -> NEx(m0, ks, img, z)) -> NEx(m0, ks, img, z):
  match b:
    case True{}:
      %Equal.sym(U32, z, y, U.eq_t(z, y, eb)) : NEx(m0, ks, img, _)
      (f, (t, (h1, h2)))
    case False{}:
      r(e)

def NFF.get(N: List<&2, NE>, +m0: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +z: U32, nff: NFF(m0, ks, img, N),
  e: {Mem(z, NCs(N)) == True{} : Bool}) -> NEx(m0, ks, img, z):
  match N:
    case Nil{}:
      tf(NEx(m0, ks, img, z), e)
    case Con{NE{+y, +f, +t}, +rest}:
      (h1, r1) = nff
      (h2, r2) = r1
      NFF.get.if(U32.is_eq(z, y), m0, ks, img, z, y, f, t, rest, {==}, h1, h2, e, x => NFF.get(rest, m0, ks, img, z, r2, x))

def Tup.b(x: C.Term) -> C.Term:
  match x:
    case C.Term.Tup{_, _, b}:
      b
    case _:
      C.Term.Efq{}

def Tup.a(x: C.Term) -> C.Term:
  match x:
    case C.Term.Tup{_, a, _}:
      a
    case _:
      C.Term.Efq{}

def Tup.q(x: C.Term) -> C.Quan:
  match x:
    case C.Term.Tup{q, _, _}:
      q
    case _:
      C.Quan.Q0{}

def NotTup(t: C.Term) -> Type:
  match t:
    case C.Term.Tup{_, _, _}:
      Empty
    case _:
      Unit

def LiveQ.b(b: Bool, c: Bool, eb: {b == False{} : Bool}) ->
  {C.Quan.live(Bool.pick(C.Quan, b, C.Quan.Q0{}, Bool.pick(C.Quan, c, C.Quan.Q1{}, C.Quan.Q2{}))) == True{} : Bool}:
  match b:
    case True{}:
      ft({C.Quan.live(C.Quan.Q0{}) == True{} : Bool}, eb)
    case False{}:
      match c:
        case True{}:
          {==}
        case False{}:
          {==}

# a quantity of bits other than 0 is live
def LiveQ(+qb: U32, h: {U32.is_eq(qb, 0) == False{} : Bool}) -> {C.Quan.live(T.tm.quan(qb)) == True{} : Bool}:
  LiveQ.b(U32.is_eq(qb, 0), U32.is_eq(qb, 1), h)

def DOk.tup.l(b: Bool, +x: Bool, +y: Bool, eb: {b == True{} : Bool}, h: {DOk.tup(b, x, y) == True{} : Bool}) -> {x == True{} : Bool}:
  match b:
    case True{}:
      Bo.and_l(x, y, h)
    case False{}:
      tf({x == True{} : Bool}, eb)

def DOk.tup.r(b: Bool, +x: Bool, +y: Bool, eb: {b == True{} : Bool}, h: {DOk.tup(b, x, y) == True{} : Bool}) -> {y == True{} : Bool}:
  match b:
    case True{}:
      Bo.and_r(x, y, h)
    case False{}:
      tf({y == True{} : Bool}, eb)

# DOk of a pair cell gives DOk of its parts
def DOk.p2(+hh: Nat, +m0: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +y: U32, +e10: {U32.is_eq(Tg(m0, y), 10) == True{} : Bool},
  h: {DOk(1n+hh, m0, ks, img, y) == True{} : Bool}) -> {DOk(hh, m0, ks, img, Fd(2n, m0, y)) == True{} : Bool}:
  +d = DataB(1n+hh, m0, ks, img, y)
  +t = Tg(m0, y)
  +A = Bool.or(Bool.not(FlB(m0, y)), d)
  +B = Bool.or(Bool.not(Bool.or(U32.is_eq(t, 1), U32.is_eq(t, 12))), Bool.not(d))
  +X = DOk(hh, m0, ks, img, Fd(2n, m0, y))
  +Y = DOk(hh, m0, ks, img, Fd(3n, m0, y))
  DOk.tup.l(U32.is_eq(t, 10), X, Y, e10, Bo.and_r(B, DOk.tup(U32.is_eq(t, 10), X, Y), Bo.and_r(A, Bool.and(B, DOk.tup(U32.is_eq(t, 10), X, Y)), h)))

def DOk.p3(+hh: Nat, +m0: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +y: U32, +e10: {U32.is_eq(Tg(m0, y), 10) == True{} : Bool},
  h: {DOk(1n+hh, m0, ks, img, y) == True{} : Bool}) -> {DOk(hh, m0, ks, img, Fd(3n, m0, y)) == True{} : Bool}:
  +d = DataB(1n+hh, m0, ks, img, y)
  +t = Tg(m0, y)
  +A = Bool.or(Bool.not(FlB(m0, y)), d)
  +B = Bool.or(Bool.not(Bool.or(U32.is_eq(t, 1), U32.is_eq(t, 12))), Bool.not(d))
  +X = DOk(hh, m0, ks, img, Fd(2n, m0, y))
  +Y = DOk(hh, m0, ks, img, Fd(3n, m0, y))
  DOk.tup.r(U32.is_eq(t, 10), X, Y, e10, Bo.and_r(B, DOk.tup(U32.is_eq(t, 10), X, Y), Bo.and_r(A, Bool.and(B, DOk.tup(U32.is_eq(t, 10), X, Y)), h)))

def Bo.or_nt(a: Bool, b: Bool, h: {Bool.or(Bool.not(a), b) == True{} : Bool}, e: {a == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      tf({b == True{} : Bool}, e)

def DataB.some(x: Maybe<&2, C.Term>, -b: C.Term, hb: {x == Some{b} : Maybe<&2, C.Term>}, ed: {DataB.of(x) == True{} : Bool}) ->
  {C.Term.is_data(b) == True{} : Bool}:
  Equal.trans(Bool, C.Term.is_data(b), DataB.of(x), True{},
    Equal.sym(Bool, DataB.of(x), C.Term.is_data(b), Equal.cong(Maybe<&2, C.Term>, Bool, z => DataB.of(z), x, Some{b}, hb)), ed)

# a flagged cell whose DOk holds stands for Data
def DOk.fl(f: Nat, +m0: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, -b: C.Term, +hd: {DOk(f, m0, ks, img, c) == True{} : Bool},
  +hf: {FlB(m0, c) == True{} : Bool}, hb: {T.tm.of(f, m0, ks, img, c) == Some{b} : Maybe<&2, C.Term>}) -> {C.Term.is_data(b) == True{} : Bool}:
  match f:
    case 0n:
      Empty.absurd({C.Term.is_data(b) == True{} : Bool}, none_some(b, hb))
    case 1n+(+k):
      +d = DataB(1n+k, m0, ks, img, c)
      +t = Tg(m0, c)
      +A = Bool.or(Bool.not(FlB(m0, c)), d)
      +B = Bool.and(Bool.or(Bool.not(Bool.or(U32.is_eq(t, 1), U32.is_eq(t, 12))), Bool.not(d)),
        DOk.tup(U32.is_eq(t, 10), DOk(k, m0, ks, img, Fd(2n, m0, c)), DOk(k, m0, ks, img, Fd(3n, m0, c))))
      +ed = Bo.or_nt(FlB(m0, c), d, Bo.and_l(A, B, hd), hf)
      DataB.some(T.tm.of(1n+k, m0, ks, img, c), b, hb, ed)

def NFD.cl(b13: Bool, b17: Bool, b10: Bool, s3: Bool, bq: Bool, s2: Bool, -G: Type,
  cl: {Bool.or(b13, Bool.or(b17, Bool.and(b10, Bool.and(s3, Bool.or(bq, s2))))) == True{} : Bool},
  k13: {b13 == True{} : Bool} -> G, k17: {b17 == True{} : Bool} -> G,
  k10: {b10 == True{} : Bool} -> {s3 == True{} : Bool} -> {Bool.or(bq, s2) == True{} : Bool} -> G) -> G:
  match b13:
    case True{}:
      k13({==})
    case False{}:
      match b17:
        case True{}:
          k17({==})
        case False{}:
          match b10:
            case False{}:
              tf(G, cl)
            case True{}:
              match s3:
                case False{}:
                  tf(G, cl)
                case True{}:
                  k10({==}, {==}, cl)

def Bo.or_case(a: Bool, b: Bool, -G: Type, h: {Bool.or(a, b) == True{} : Bool}, ka: {a == True{} : Bool} -> G, kb: {b == True{} : Bool} -> G) -> G:
  match a:
    case True{}:
      ka({==})
    case False{}:
      kb(h)

# a part of a flagged pair, settled, stands for Data
def NFD.part(+m0: C.Cir.Cells, +c: U32, +NC: List<&2, U32>, -b: C.Term, sc: {Setl(m0, c, Nil{}, NC) == True{} : Bool},
  rec: {Mem(c, NC) == True{} : Bool} -> {C.Term.is_data(b) == True{} : Bool},
  fl: {FlB(m0, c) == True{} : Bool} -> {C.Term.is_data(b) == True{} : Bool}) -> {C.Term.is_data(b) == True{} : Bool}:
  Bo.or_case(Mem(c, NC), FlB(m0, c), {C.Term.is_data(b) == True{} : Bool}, sc, rec, fl)

def NFD.fl3.tr(+hh: Nat, +g: Nat, +m0: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +y: U32,
  +dk: {DOk(hh, m0, ks, img, Fd(3n, m0, y)) == True{} : Bool}, +hf: {FlB(m0, Fd(3n, m0, y)) == True{} : Bool}, -ty: C.Term,
  tr: TupR(hh, m0, ks, img, y, ty), -b: C.Term, hb: {T.tm.of(g, m0, ks, img, Fd(3n, m0, y)) == Some{b} : Maybe<&2, C.Term>}) ->
  {C.Term.is_data(b) == True{} : Bool}:
  (a2, r1) = tr
  (b2, r2) = r1
  (ha, r3) = r2
  (hb2, et) = r3
  +hy = hb2
  +by = b2
  +e = TUniq(hh, g, m0, ks, img, Fd(3n, m0, y), by, b, hy, hb)
  %e : {C.Term.is_data(_) == True{} : Bool}
  DOk.fl(hh, m0, ks, img, Fd(3n, m0, y), by, dk, hf, hy)

def NFD.fl3.go(fy: Nat, +g: Nat, +m0: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +y: U32,
  +e10b: {U32.is_eq(Tg(m0, y), 10) == True{} : Bool}, -ty: C.Term, hty: {T.tm.of(fy, m0, ks, img, y) == Some{ty} : Maybe<&2, C.Term>},
  dky: {DOk(fy, m0, ks, img, y) == True{} : Bool}, +hf: {FlB(m0, Fd(3n, m0, y)) == True{} : Bool}, -b: C.Term,
  hb: {T.tm.of(g, m0, ks, img, Fd(3n, m0, y)) == Some{b} : Maybe<&2, C.Term>}) -> {C.Term.is_data(b) == True{} : Bool}:
  match fy:
    case 0n:
      Empty.absurd({C.Term.is_data(b) == True{} : Bool}, none_some(ty, hty))
    case 1n+(+hh):
      NFD.fl3.tr(hh, g, m0, ks, img, y, DOk.p3(hh, m0, ks, img, y, e10b, dky), hf, ty,
        D.tup(hh, m0, ks, img, y, U.eq_t(Tg(m0, y), 10, e10b), ty, hty), b, hb)

# a part, flagged before the check, of a flagged pair stands for Data
def NFD.fl3(+g: Nat, +m0: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +y: U32, +e10b: {U32.is_eq(Tg(m0, y), 10) == True{} : Bool},
  ex: NEx(m0, ks, img, y), +hf: {FlB(m0, Fd(3n, m0, y)) == True{} : Bool}, -b: C.Term,
  hb: {T.tm.of(g, m0, ks, img, Fd(3n, m0, y)) == Some{b} : Maybe<&2, C.Term>}) -> {C.Term.is_data(b) == True{} : Bool}:
  (fy, r1) = ex
  (ty, r2) = r1
  (hty, dky) = r2
  NFD.fl3.go(fy, g, m0, ks, img, y, e10b, ty, hty, dky, hf, b, hb)

def NFD.fl2.tr(+hh: Nat, +g: Nat, +m0: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +y: U32,
  +dk: {DOk(hh, m0, ks, img, Fd(2n, m0, y)) == True{} : Bool}, +hf: {FlB(m0, Fd(2n, m0, y)) == True{} : Bool}, -ty: C.Term,
  tr: TupR(hh, m0, ks, img, y, ty), -b: C.Term, hb: {T.tm.of(g, m0, ks, img, Fd(2n, m0, y)) == Some{b} : Maybe<&2, C.Term>}) ->
  {C.Term.is_data(b) == True{} : Bool}:
  (a2, r1) = tr
  (b2, r2) = r1
  (ha, r3) = r2
  (hb2, et) = r3
  +hy = ha
  +by = a2
  +e = TUniq(hh, g, m0, ks, img, Fd(2n, m0, y), by, b, hy, hb)
  %e : {C.Term.is_data(_) == True{} : Bool}
  DOk.fl(hh, m0, ks, img, Fd(2n, m0, y), by, dk, hf, hy)

def NFD.fl2.go(fy: Nat, +g: Nat, +m0: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +y: U32,
  +e10b: {U32.is_eq(Tg(m0, y), 10) == True{} : Bool}, -ty: C.Term, hty: {T.tm.of(fy, m0, ks, img, y) == Some{ty} : Maybe<&2, C.Term>},
  dky: {DOk(fy, m0, ks, img, y) == True{} : Bool}, +hf: {FlB(m0, Fd(2n, m0, y)) == True{} : Bool}, -b: C.Term,
  hb: {T.tm.of(g, m0, ks, img, Fd(2n, m0, y)) == Some{b} : Maybe<&2, C.Term>}) -> {C.Term.is_data(b) == True{} : Bool}:
  match fy:
    case 0n:
      Empty.absurd({C.Term.is_data(b) == True{} : Bool}, none_some(ty, hty))
    case 1n+(+hh):
      NFD.fl2.tr(hh, g, m0, ks, img, y, DOk.p2(hh, m0, ks, img, y, e10b, dky), hf, ty,
        D.tup(hh, m0, ks, img, y, U.eq_t(Tg(m0, y), 10, e10b), ty, hty), b, hb)

# a part, flagged before the check, of a flagged pair stands for Data
def NFD.fl2(+g: Nat, +m0: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +y: U32, +e10b: {U32.is_eq(Tg(m0, y), 10) == True{} : Bool},
  ex: NEx(m0, ks, img, y), +hf: {FlB(m0, Fd(2n, m0, y)) == True{} : Bool}, -b: C.Term,
  hb: {T.tm.of(g, m0, ks, img, Fd(2n, m0, y)) == Some{b} : Maybe<&2, C.Term>}) -> {C.Term.is_data(b) == True{} : Bool}:
  (fy, r1) = ex
  (ty, r2) = r1
  (hty, dky) = r2
  NFD.fl2.go(fy, g, m0, ks, img, y, e10b, ty, hty, dky, hf, b, hb)

def NFD.qa(bq: Bool, +qb: U32, eq: {U32.is_eq(qb, 0) == bq : Bool}, s2: Bool, s2o: {Bool.or(bq, s2) == True{} : Bool}, +a: C.Term,
  ka: {s2 == True{} : Bool} -> {C.Term.is_data(a) == True{} : Bool}) ->
  {Bool.or(Bool.not(C.Quan.live(T.tm.quan(qb))), C.Term.is_data(a)) == True{} : Bool}:
  match bq:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(qb, 0), True{}, eq) : {Bool.or(Bool.not(C.Quan.live(Bool.pick(C.Quan, _, C.Quan.Q0{},
        Bool.pick(C.Quan, U32.is_eq(qb, 1), C.Quan.Q1{}, C.Quan.Q2{})))), C.Term.is_data(a)) == True{} : Bool}
      {==}
    case False{}:
      Bo.or_r(Bool.not(C.Quan.live(T.tm.quan(qb))), C.Term.is_data(a), ka(s2o))

def NFD.tup2(+g: Nat, +m0: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +N: List<&2, NE>, +nff: NFF(m0, ks, img, N),
  +y: U32, -t: C.Term, +hm: {Mem(y, NCs(N)) == True{} : Bool}, +e10b: {U32.is_eq(Tg(m0, y), 10) == True{} : Bool},
  s3: {Setl(m0, Fd(3n, m0, y), Nil{}, NCs(N)) == True{} : Bool},
  s2o: {Bool.or(U32.is_eq(Qb(m0, y), 0), Setl(m0, Fd(2n, m0, y), Nil{}, NCs(N))) == True{} : Bool}, tr: TupR(g, m0, ks, img, y, t),
  rec3: @b: C.Term -> {Mem(Fd(3n, m0, y), NCs(N)) == True{} : Bool} -> {T.tm.of(g, m0, ks, img, Fd(3n, m0, y)) == Some{b} : Maybe<&2, C.Term>} ->
    {C.Term.is_data(b) == True{} : Bool},
  rec2: @b: C.Term -> {Mem(Fd(2n, m0, y), NCs(N)) == True{} : Bool} -> {T.tm.of(g, m0, ks, img, Fd(2n, m0, y)) == Some{b} : Maybe<&2, C.Term>} ->
    {C.Term.is_data(b) == True{} : Bool}) -> {C.Term.is_data(t) == True{} : Bool}:
  (+a, r1) = tr
  (+b, r2) = r1
  (ha, r3) = r2
  (hb, et) = r3
  +ha2 = ha
  +hb2 = hb
  +NC = NCs(N)
  %et : {C.Term.is_data(_) == True{} : Bool}
  Bo.and_i(Bool.or(Bool.not(C.Quan.live(T.tm.quan(Qb(m0, y)))), C.Term.is_data(a)), C.Term.is_data(b),
    NFD.qa(U32.is_eq(Qb(m0, y), 0), Qb(m0, y), {==}, Setl(m0, Fd(2n, m0, y), Nil{}, NC), s2o, a,
      x => NFD.part(m0, Fd(2n, m0, y), NC, a, x, z => rec2(a, z, ha2),
        z => NFD.fl2(g, m0, ks, img, y, e10b, NFF.get(N, m0, ks, img, y, nff, hm), z, a, ha2))),
    NFD.part(m0, Fd(3n, m0, y), NC, b, s3, z => rec3(b, z, hb2),
      z => NFD.fl3(g, m0, ks, img, y, e10b, NFF.get(N, m0, ks, img, y, nff, hm), z, b, hb2)))

# once the stack is empty, every cell that the check flagged stands for Data
def NFD(f: Nat, +m0: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +N: List<&2, NE>, +nff: NFF(m0, ks, img, N),
  +nok: {NFOk(m0, NCs(N), Nil{}, NCs(N)) == True{} : Bool}, +y: U32, -t: C.Term, +hm: {Mem(y, NCs(N)) == True{} : Bool},
  +h: {T.tm.of(f, m0, ks, img, y) == Some{t} : Maybe<&2, C.Term>}) -> {C.Term.is_data(t) == True{} : Bool}:
  match f:
    case 0n:
      Empty.absurd({C.Term.is_data(t) == True{} : Bool}, none_some(t, h))
    case 1n+(+g):
      +NC = NCs(N)
      +T0 = Tg(m0, y)
      NFD.cl(U32.is_eq(T0, 13), U32.is_eq(T0, 17), U32.is_eq(T0, 10), Setl(m0, Fd(3n, m0, y), Nil{}, NC), U32.is_eq(Qb(m0, y), 0),
        Setl(m0, Fd(2n, m0, y), Nil{}, NC), {C.Term.is_data(t) == True{} : Bool}, NFOk.get(NC, m0, Nil{}, NC, y, nok, hm),
        e => D.lab(g, m0, ks, img, y, U.eq_t(T0, 13, e), t, h),
        e => D.rfl(g, m0, ks, img, y, U.eq_t(T0, 17, e), t, h),
        +e => s3 => s2o => NFD.tup2(g, m0, ks, img, N, nff, y, t, hm, e, s3, s2o, D.tup(g, m0, ks, img, y, U.eq_t(T0, 10, e), t, h),
          b => x => hb => NFD(g, m0, ks, img, N, nff, nok, Fd(3n, m0, y), b, x, hb),
          b => x => hb => NFD(g, m0, ks, img, N, nff, nok, Fd(2n, m0, y), b, x, hb)))

# Algebra of the writes
# ---------------------

def Apply.cat(a: List<&2, Wr>, +b: List<&2, Wr>, +m: C.Cir.Cells) -> {Apply(a, Apply(b, m)) == Apply(List.append(&2, Wr, a, b), m) : C.Cir.Cells}:
  match a:
    case Nil{}:
      {==}
    case Con{+w, +rest}:
      %Apply.cat(rest, b, m) : {Do(Apply(rest, Apply(b, m)), w) == Do(_, w) : C.Cir.Cells}
      {==}

def WOk.app(a: List<&2, Wr>, +b: List<&2, Wr>, +L: List<&2, U32>, +K: List<&2, U32>, ha: {WOk(a, L, K) == True{} : Bool},
  hb: {WOk(b, L, K) == True{} : Bool}) -> {WOk(List.append(&2, Wr, a, b), L, K) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case Con{+w, +rest}:
      +ha2 = ha
      Bo.and_i(WOk1(w, L, K), WOk(List.append(&2, Wr, rest, b), L, K), Bo.and_l(WOk1(w, L, K), WOk(rest, L, K), ha2),
        WOk.app(rest, b, L, K, Bo.and_r(WOk1(w, L, K), WOk(rest, L, K), ha2), hb))

def WFl.app(a: List<&2, Wr>, +b: List<&2, Wr>, +NC: List<&2, U32>, ha: {WFl(a, NC) == True{} : Bool},
  hb: {WFl(b, NC) == True{} : Bool}) -> {WFl(List.append(&2, Wr, a, b), NC) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case Con{+w, +rest}:
      +ha2 = ha
      Bo.and_i(WFl1(w, NC), WFl(List.append(&2, Wr, rest, b), NC), Bo.and_l(WFl1(w, NC), WFl(rest, NC), ha2),
        WFl.app(rest, b, NC, Bo.and_r(WFl1(w, NC), WFl(rest, NC), ha2), hb))

def Mem.sub_f.b(b: Bool, +c: U32, +A: List<&2, U32>, +B: List<&2, U32>, eb: {Mem(c, A) == b : Bool}, hs: {Sub(A, B) == True{} : Bool},
  h: {Mem(c, B) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Bo.f_t(Mem(c, B), h, Sub.mem(A, B, c, hs, eb)))
    case False{}:
      {==}

def Mem.sub_f(+c: U32, +A: List<&2, U32>, +B: List<&2, U32>, hs: {Sub(A, B) == True{} : Bool}, h: {Mem(c, B) == False{} : Bool}) -> {Mem(c, A) == False{} : Bool}:
  Mem.sub_f.b(Mem(c, A), c, A, B, {==}, hs, h)


# Bridge to layer B (proof_mach.bend)
# -----------------------------------

# Ok is PM.Post for any fuel (dn False), with no halt
def Ok.post(o: C.Cir.Out, -Q: C.Cir.State -> Type, h: Ok(o, Q)) -> PM.Post(False{}, o, Q, s => st => Empty):
  match o:
    case C.Cir.Out.next{st}:
      h
    case C.Cir.Out.halt{s, st}:
      h
    case C.Cir.Out.out_of_memory{}:
      Unit{}
    case C.Cir.Out.trap{}:
      h
    case C.Cir.Out.not_done{}:
      Unit{}

# WP gives PM.Post(False) of Cir.exec, with no halt: the shape of data.post and
# walk.post
def WP.post(+F: Nat, +s: C.Cir.Stmt, +st: C.Cir.State, -Q: C.Cir.State -> Type, w: WP(s, F, st, Q)) ->
  PM.Post(False{}, C.Cir.exec(F, s, st), Q, s2 => st2 => Empty):
  Ok.post(C.Cir.exec(F, s, st), Q, Sim(F, s, st, Q, w))
