# compiler: the data check and the walk of the machine (layer B)
# ===============================================================
#
# M.data(r) computes Term.is_data of the term of the cell in register r, and
# M.walk() computes Eval.walk of the case tree in wt on the arguments in
# wargs (impl.bend, Machine). The proofs run the code through WP, a weakest
# precondition of Cir.exec: WP(F, s, st, Q) holds when every access that s
# makes from st is one that Cir allows, and its end satisfies Q; Sim turns
# it into Cir.exec's outcome. Straight code then computes inside WP, so a
# proof gives only the accesses' checks, and a case at each test on a value
# that the proof does not know.

import Base
import ./impl.bend as C
import ./proof_term.bend as T
import ./proof_need.bend as N

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

def Apply(ws: List<&2, Wr>, +m: C.Cir.Cells) -> C.Cir.Cells:
  match ws:
    case Nil{}:
      m
    case Con{w, rest}:
      Apply(rest, Do(m, w))

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
def W.tm(ws: List<&2, Wr>, +f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +L: List<&2, U32>,
  +K: List<&2, U32>, +c: U32, ok: {WOk(ws, L, K) == True{} : Bool}, h: {RdIn(f, m, c, L) == True{} : Bool}) ->
  {T.tm.of(f, m, ks, img, c) == T.tm.of(f, Apply(ws, m), ks, img, c) : Maybe<&2, C.Term>}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +rest}:
      +ok2 = ok
      +o1 = Bo.and_l(WOk1(w, L, K), WOk(rest, L, K), ok2)
      +h2 = h
      Equal.trans(Maybe<&2, C.Term>, T.tm.of(f, m, ks, img, c), T.tm.of(f, Do(m, w), ks, img, c), T.tm.of(f, Apply(rest, Do(m, w)), ks, img, c),
        Do1.tm(w, f, m, ks, img, L, K, c, o1, h2),
        W.tm(rest, f, Do(m, w), ks, img, L, K, c, Bo.and_r(WOk1(w, L, K), WOk(rest, L, K), ok2), Do1.rd(w, f, m, L, K, c, o1, h2)))

def W.rd(ws: List<&2, Wr>, +f: Nat, +m: C.Cir.Cells, +L: List<&2, U32>, +K: List<&2, U32>, +c: U32,
  ok: {WOk(ws, L, K) == True{} : Bool}, h: {RdIn(f, m, c, L) == True{} : Bool}) -> {RdIn(f, Apply(ws, m), c, L) == True{} : Bool}:
  match ws:
    case Nil{}:
      h
    case Con{+w, +rest}:
      +ok2 = ok
      W.rd(rest, f, Do(m, w), L, K, c, Bo.and_r(WOk1(w, L, K), WOk(rest, L, K), ok2),
        Do1.rd(w, f, m, L, K, c, Bo.and_l(WOk1(w, L, K), WOk(rest, L, K), ok2), h))

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
      Equal.trans(C.Cir.Cell, C.Cir.Cells.get(m, d), C.Cir.Cells.get(Do(m, w), d), C.Cir.Cells.get(Apply(rest, Do(m, w)), d),
        Do1.link(w, m, L, K, d, Bo.and_l(WOk1(w, L, K), WOk(rest, L, K), ok2), hd),
        W.link(rest, Do(m, w), L, K, d, Bo.and_r(WOk1(w, L, K), WOk(rest, L, K), ok2), hd))

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
      AgC.trans(C.Cir.Cells.get(m, d), C.Cir.Cells.get(Do(m, w), d), C.Cir.Cells.get(Apply(rest, Do(m, w)), d),
        Do1.ag(w, m, L, K, d, Bo.and_l(WOk1(w, L, K), WOk(rest, L, K), ok2), hd),
        W.ag(rest, Do(m, w), L, K, d, Bo.and_r(WOk1(w, L, K), WOk(rest, L, K), ok2), hd))

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
#       writes that keep L's terms and K (counts), and CS again with c in K;
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
      Sigma<&1, &1, {C.Cir.Cells.get(Apply(ws, m), c) == C.Cir.Cell.zero() : C.Cir.Cell}, _ =>
      Sigma<&1, &1, {AllCell(L, im, fs, nx2) == True{} : Bool}, _ =>
      Sigma<&1, &1, {AllCell(Con{c, K}, im, fs, nx2) == True{} : Bool}, _ =>
      CS(Apply(ws, m), p, L, Con{c, K})>>>>>>>>

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

