import Base
import ./impl.bend as C
import ./proof_term.bend as T
import ./proof_need.bend as N
import ./proof_module.bend as PM

# Cells
# -----

# a cell set at w is there
def Cl.get_set.at(n: Nat, +w: Word(n), +m: C.Cir.Cells, +c: C.Cir.Cell) ->
  {C.Cir.Cells.get.at(n, w, C.Cir.Cells.set.at(n, w, m, c)) == c : C.Cir.Cell}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          match m:
            case C.Cir.Cells.node{+lo, +hi}:
              Cl.get_set.at(p, t, lo, c)
            case C.Cir.Cells.none{}:
              Cl.get_set.at(p, t, C.Cir.Cells.none{}, c)
            case C.Cir.Cells.one{+d}:
              Cl.get_set.at(p, t, C.Cir.Cells.none{}, c)
        case WCon{True{}, +t}:
          match m:
            case C.Cir.Cells.node{+lo, +hi}:
              Cl.get_set.at(p, t, hi, c)
            case C.Cir.Cells.none{}:
              Cl.get_set.at(p, t, C.Cir.Cells.none{}, c)
            case C.Cir.Cells.one{+d}:
              Cl.get_set.at(p, t, C.Cir.Cells.none{}, c)

def Cl.get_set(+m: C.Cir.Cells, +i: U32, +c: C.Cir.Cell) -> {C.Cir.Cells.get(C.Cir.Cells.set(m, i, c), i) == c : C.Cir.Cell}:
  match i:
    case U32{+w}:
      Cl.get_set.at(32n, w, m, c)

# a cell set twice at w holds the second
def Cl.set_set.at(n: Nat, +w: Word(n), +m: C.Cir.Cells, +c: C.Cir.Cell, +d: C.Cir.Cell) ->
  {C.Cir.Cells.set.at(n, w, m, d) == C.Cir.Cells.set.at(n, w, C.Cir.Cells.set.at(n, w, m, c), d) : C.Cir.Cells}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          match m:
            case C.Cir.Cells.node{+lo, +hi}:
              %Cl.set_set.at(p, t, lo, c, d) : {C.Cir.Cells.node{C.Cir.Cells.set.at(p, t, lo, d), hi} == C.Cir.Cells.node{_, hi} : C.Cir.Cells}
              {==}
            case C.Cir.Cells.none{}:
              %Cl.set_set.at(p, t, C.Cir.Cells.none{}, c, d) : {C.Cir.Cells.node{C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, d), C.Cir.Cells.none{}} == C.Cir.Cells.node{_, C.Cir.Cells.none{}} : C.Cir.Cells}
              {==}
            case C.Cir.Cells.one{+e}:
              %Cl.set_set.at(p, t, C.Cir.Cells.none{}, c, d) : {C.Cir.Cells.node{C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, d), C.Cir.Cells.none{}} == C.Cir.Cells.node{_, C.Cir.Cells.none{}} : C.Cir.Cells}
              {==}
        case WCon{True{}, +t}:
          match m:
            case C.Cir.Cells.node{+lo, +hi}:
              %Cl.set_set.at(p, t, hi, c, d) : {C.Cir.Cells.node{lo, C.Cir.Cells.set.at(p, t, hi, d)} == C.Cir.Cells.node{lo, _} : C.Cir.Cells}
              {==}
            case C.Cir.Cells.none{}:
              %Cl.set_set.at(p, t, C.Cir.Cells.none{}, c, d) : {C.Cir.Cells.node{C.Cir.Cells.none{}, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, d)} == C.Cir.Cells.node{C.Cir.Cells.none{}, _} : C.Cir.Cells}
              {==}
            case C.Cir.Cells.one{+e}:
              %Cl.set_set.at(p, t, C.Cir.Cells.none{}, c, d) : {C.Cir.Cells.node{C.Cir.Cells.none{}, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, d)} == C.Cir.Cells.node{C.Cir.Cells.none{}, _} : C.Cir.Cells}
              {==}

def Cl.set_set(+m: C.Cir.Cells, +i: U32, +c: C.Cir.Cell, +d: C.Cir.Cell) ->
  {C.Cir.Cells.set(m, i, d) == C.Cir.Cells.set(C.Cir.Cells.set(m, i, c), i, d) : C.Cir.Cells}:
  match i:
    case U32{+w}:
      Cl.set_set.at(32n, w, m, c, d)

# no cell is all zeros
def Cl.get_none(n: Nat, +v: Word(n)) -> {C.Cir.Cell.zero() == C.Cir.Cells.get.at(n, v, C.Cir.Cells.none{}) : C.Cir.Cell}:
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
def Cl.get_other.at(n: Nat, +v: Word(n), +w: Word(n), +m: C.Cir.Cells, +c: C.Cir.Cell, ne: {v == w : Word(n)} -> Empty) ->
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
              Cl.get_other.at(p, s, t, lo, c, e => ne(Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x}, s, t, e)))
            case C.Cir.Cells.none{}:
              Equal.trans(C.Cir.Cell, C.Cir.Cell.zero(), C.Cir.Cells.get.at(p, s, C.Cir.Cells.none{}), C.Cir.Cells.get.at(p, s, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, c)),
                Cl.get_none(p, s), Cl.get_other.at(p, s, t, C.Cir.Cells.none{}, c, e => ne(Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x}, s, t, e))))
            case C.Cir.Cells.one{+d}:
              Equal.trans(C.Cir.Cell, C.Cir.Cell.zero(), C.Cir.Cells.get.at(p, s, C.Cir.Cells.none{}), C.Cir.Cells.get.at(p, s, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, c)),
                Cl.get_none(p, s), Cl.get_other.at(p, s, t, C.Cir.Cells.none{}, c, e => ne(Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x}, s, t, e))))
        case WCon{True{}, +s} WCon{True{}, +t}:
          match m:
            case C.Cir.Cells.node{+lo, +hi}:
              Cl.get_other.at(p, s, t, hi, c, e => ne(Equal.cong(Word(p), Word(1n+p), x => WCon{True{}, x}, s, t, e)))
            case C.Cir.Cells.none{}:
              Equal.trans(C.Cir.Cell, C.Cir.Cell.zero(), C.Cir.Cells.get.at(p, s, C.Cir.Cells.none{}), C.Cir.Cells.get.at(p, s, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, c)),
                Cl.get_none(p, s), Cl.get_other.at(p, s, t, C.Cir.Cells.none{}, c, e => ne(Equal.cong(Word(p), Word(1n+p), x => WCon{True{}, x}, s, t, e))))
            case C.Cir.Cells.one{+d}:
              Equal.trans(C.Cir.Cell, C.Cir.Cell.zero(), C.Cir.Cells.get.at(p, s, C.Cir.Cells.none{}), C.Cir.Cells.get.at(p, s, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, c)),
                Cl.get_none(p, s), Cl.get_other.at(p, s, t, C.Cir.Cells.none{}, c, e => ne(Equal.cong(Word(p), Word(1n+p), x => WCon{True{}, x}, s, t, e))))
        case WCon{False{}, +s} WCon{True{}, +t}:
          match m:
            case C.Cir.Cells.node{+lo, +hi}:
              {==}
            case C.Cir.Cells.none{}:
              Cl.get_none(p, s)
            case C.Cir.Cells.one{+d}:
              Cl.get_none(p, s)
        case WCon{True{}, +s} WCon{False{}, +t}:
          match m:
            case C.Cir.Cells.node{+lo, +hi}:
              {==}
            case C.Cir.Cells.none{}:
              Cl.get_none(p, s)
            case C.Cir.Cells.one{+d}:
              Cl.get_none(p, s)

def Cl.get_other(+m: C.Cir.Cells, +j: U32, +i: U32, +c: C.Cir.Cell, ne: {j == i : U32} -> Empty) ->
  {C.Cir.Cells.get(m, j) == C.Cir.Cells.get(C.Cir.Cells.set(m, i, c), j) : C.Cir.Cell}:
  match j i:
    case U32{+v} U32{+w}:
      Cl.get_other.at(32n, v, w, m, c, e => ne(Equal.cong(Word(32n), U32, x => U32{x}, v, w, e)))

# Runs
# ----

# a state of the run: the registers, the cells, the next cell and the pages
def In.S(regs: List<&2, U32>, m: C.Cir.Cells, next: U32, F: U32, K: U32, pg: U32, L: U32, I: List<&2, U32>) -> C.Cir.State:
  C.Cir.State{regs, m, next, F, K, pg, L, I, Nil{}, 0}

# o ends after the statement with a state of which Q holds, or out of memory
def In.Ok(o: C.Cir.Out, Q: C.Cir.State -> Type) -> Type:
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
      Empty

# st is the state of regs, m and next, with any pages, and X holds
def In.Is(st: C.Cir.State, regs: List<&2, U32>, m: C.Cir.Cells, next: U32, F: U32, K: U32, L: U32, I: List<&2, U32>, X: Type) -> Type:
  match st:
    case C.Cir.State{rg, ms, nx, fi, im, +pg, li, inp, out, outn}:
      {In.S(regs, m, next, F, K, pg, L, I) == C.Cir.State{rg, ms, nx, fi, im, pg, li, inp, out, outn} : C.Cir.State} & X

# a statement, then more
def In.then(o: C.Cir.Out, -k: C.Cir.State -> C.Cir.Out, -Q: C.Cir.State -> Type, -R: C.Cir.State -> Type,
  h: In.Ok(o, Q), g: @st: C.Cir.State -> Q(st) -> In.Ok(k(st), R)) -> In.Ok(C.Cir.exec.then(o, k), R):
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
      match h:

# a state of which Is holds, by its pages
def In.at(st: C.Cir.State, +regs: List<&2, U32>, +m: C.Cir.Cells, +next: U32, +F: U32, +K: U32, +L: U32, +I: List<&2, U32>, -X: Type,
  -R: C.Cir.State -> Type, -k: C.Cir.State -> C.Cir.Out, e: In.Is(st, regs, m, next, F, K, L, I, X),
  g: @pg: U32 -> X -> In.Ok(k(In.S(regs, m, next, F, K, pg, L, I)), R)) -> In.Ok(k(st), R):
  match st:
    case C.Cir.State{rg, ms, nx, fi, im, +pg, li, inp, out, outn}:
      (eq, x) = e
      %eq : In.Ok(k(_), R)
      g(pg, x)

# a then b, when a ends in the state of regs, m and next
def In.seq(+f: Nat, a: C.Cir.Stmt, +b: C.Cir.Stmt, st: C.Cir.State, +regs: List<&2, U32>, +m: C.Cir.Cells, +next: U32, +F: U32, +K: U32, +L: U32,
  +I: List<&2, U32>, -X: Type, -R: C.Cir.State -> Type,
  h: In.Ok(C.Cir.exec(1n+f, a, st), s => In.Is(s, regs, m, next, F, K, L, I, X)),
  g: @pg: U32 -> X -> In.Ok(C.Cir.exec(1n+f, b, In.S(regs, m, next, F, K, pg, L, I)), R)) ->
  In.Ok(C.Cir.exec(1n+f, C.Cir.Stmt.seq{a, b}, st), R):
  In.then(C.Cir.exec(1n+f, a, st), t => C.Cir.exec(1n+f, b, t), s => In.Is(s, regs, m, next, F, K, L, I, X), R, h,
    s => e => In.at(s, regs, m, next, F, K, L, I, X, R, t => C.Cir.exec(1n+f, b, t), e, g))

# Allocation
# ----------

# the cell made of zeros
def In.z() -> C.Cir.Cell:
  C.Cir.Cell{0, 0, 0, 0, 0}

def In.room(rm: Maybe<&2, U32>, +r: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +next: U32, +F: U32, +K: U32, +pg: U32, +L: U32,
  +I: List<&2, U32>, rl: {True{} == Nat.is_lt(r, List.length(&2, U32, regs)) : Bool}, -X: Type, x: X) ->
  In.Ok(C.Cir.exec.bump.of(r, next, In.S(regs, m, next, F, K, pg, L, I), rm),
    s => In.Is(s, List.set(&2, U32, regs, r, next), C.Cir.Cells.set(m, next, In.z()), U32.inc(next), F, K, L, I, X)):
  match rm:
    case None{}:
      Unit{}
    case Some{+p}:
      %rl : In.Ok(C.Cir.exec.set.of(C.Cir.regs.set.if(_, regs, r, next), C.Cir.State{regs, C.Cir.Cells.set(m, next, In.z()), U32.inc(next), F, K, p, L, I, [], 0}),
        s => In.Is(s, List.set(&2, U32, regs, r, next), C.Cir.Cells.set(m, next, In.z()), U32.inc(next), F, K, L, I, X))
      ({==}, x)

def In.bump(b: Bool, +r: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +next: U32, +F: U32, +K: U32, +pg: U32, +L: U32,
  +I: List<&2, U32>, eb: {U32.is_lt(next, 214748364) == b : Bool}, rl: {True{} == Nat.is_lt(r, List.length(&2, U32, regs)) : Bool}) ->
  In.Ok(C.Cir.exec.bump.if(b, r, next, pg, L, In.S(regs, m, next, F, K, pg, L, I)),
    s => In.Is(s, List.set(&2, U32, regs, r, next), C.Cir.Cells.set(m, next, In.z()), U32.inc(next), F, K, L, I,
      {U32.is_lt(next, 214748364) == True{} : Bool})):
  match b:
    case False{}:
      Unit{}
    case True{}:
      In.room(C.Cir.room(U32.add(C.Cir.at(next), 19), pg, L), r, regs, m, next, F, K, pg, L, I, rl, {U32.is_lt(next, 214748364) == True{} : Bool}, eb)

# the code of a statement if c then t else e, its t
def In.yes(s: C.Cir.Stmt) -> C.Cir.Stmt:
  match s:
    case C.Cir.Stmt.if{_, t, _}:
      t
    case _:
      s

# a new cell, all zeros, when the pend list is empty
def In.alloc(+f: Nat, +r: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +next: U32, +F: U32, +K: U32, +pg: U32, +L: U32,
  +I: List<&2, U32>, p0: {Some{0} == List.get(&2, U32, regs, 3n) : Maybe<&2, U32>}, rl: {True{} == Nat.is_lt(r, List.length(&2, U32, regs)) : Bool}) ->
  In.Ok(C.Cir.exec(1n+f, C.M.alloc(r), In.S(regs, m, next, F, K, pg, L, I)),
    s => In.Is(s, List.set(&2, U32, regs, r, next), C.Cir.Cells.set(m, next, In.z()), U32.inc(next), F, K, L, I,
      {U32.is_lt(next, 214748364) == True{} : Bool})):
  %p0 : In.Ok(C.Cir.exec.if(C.Cir.eval.op(C.Wasm.Op.ne{}, _, Some{0}), u => C.Cir.exec(1n+f, In.yes(C.M.alloc(r)), In.S(regs, m, next, F, K, pg, L, I)),
      u => C.Cir.exec(1n+f, C.Cir.Stmt.alloc{r}, In.S(regs, m, next, F, K, pg, L, I))),
    s => In.Is(s, List.set(&2, U32, regs, r, next), C.Cir.Cells.set(m, next, In.z()), U32.inc(next), F, K, L, I,
      {U32.is_lt(next, 214748364) == True{} : Bool}))
  In.bump(U32.is_lt(next, 214748364), r, regs, m, next, F, K, pg, L, I, {==}, rl)

# field k of the cell i, which register r holds, gets the value of v
def In.store(+f: Nat, +k: Nat, +r: Nat, +v: C.Cir.Expr, +regs: List<&2, U32>, +m: C.Cir.Cells, +i: U32, +c: C.Cir.Cell, +x: U32, +nx: U32,
  +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, U32>,
  er: {Some{i} == List.get(&2, U32, regs, r) : Maybe<&2, U32>},
  ev: {Some{x} == C.Cir.eval(v, In.S(regs, C.Cir.Cells.set(m, i, c), nx, F, K, pg, L, I)) : Maybe<&2, U32>},
  ec: {True{} == C.Cir.is_cell(i, K, F, nx) : Bool}, -X: Type, xx: X) ->
  In.Ok(C.Cir.exec(1n+f, C.Cir.Stmt.store{k, C.Cir.Expr.get{r}, v}, In.S(regs, C.Cir.Cells.set(m, i, c), nx, F, K, pg, L, I)),
    s => In.Is(s, regs, C.Cir.Cells.set(m, i, C.Cir.Cell.set(k, c, x)), nx, F, K, L, I, X)):
  +st = In.S(regs, C.Cir.Cells.set(m, i, c), nx, F, K, pg, L, I)
  %er : In.Ok(C.Cir.exec.store(k, _, C.Cir.eval(v, st), st), s => In.Is(s, regs, C.Cir.Cells.set(m, i, C.Cir.Cell.set(k, c, x)), nx, F, K, L, I, X))
  %ev : In.Ok(C.Cir.exec.store(k, Some{i}, _, st), s => In.Is(s, regs, C.Cir.Cells.set(m, i, C.Cir.Cell.set(k, c, x)), nx, F, K, L, I, X))
  %ec : In.Ok(C.Cir.exec.store.if(_, k, i, x, st), s => In.Is(s, regs, C.Cir.Cells.set(m, i, C.Cir.Cell.set(k, c, x)), nx, F, K, L, I, X))
  %Equal.sym(C.Cir.Cell, C.Cir.Cells.get(C.Cir.Cells.set(m, i, c), i), c, Cl.get_set(m, i, c)) :
    {In.S(regs, C.Cir.Cells.set(m, i, C.Cir.Cell.set(k, c, x)), nx, F, K, pg, L, I) == In.S(regs, C.Cir.Cells.set(C.Cir.Cells.set(m, i, c), i, C.Cir.Cell.set(k, _, x)), nx, F, K, pg, L, I) : C.Cir.State} & X
  %Cl.set_set(m, i, c, C.Cir.Cell.set(k, c, x)) :
    {In.S(regs, C.Cir.Cells.set(m, i, C.Cir.Cell.set(k, c, x)), nx, F, K, pg, L, I) == In.S(regs, _, nx, F, K, pg, L, I) : C.Cir.State} & X
  ({==}, xx)

# the facts of a run: the alloc's bound
def In.lt(+next: U32) -> Data:
  {U32.is_lt(next, 214748364) == True{} : Bool}

# the stores of M.make, after its alloc
def In.make.stores(+f: Nat, +r: Nat, +h: C.Cir.Expr, +a: C.Cir.Expr, +b: C.Cir.Expr, +c: C.Cir.Expr, +rg: List<&2, U32>, +m: C.Cir.Cells,
  +next: U32, +n1: U32, +F: U32, +K: U32, +pg1: U32, +L: U32, +I: List<&2, U32>, +vh: U32, +va: U32, +vb: U32, +vc: U32,
  +er: {Some{next} == List.get(&2, U32, rg, r) : Maybe<&2, U32>},
  +ok: {True{} == C.Cir.is_cell(next, K, F, n1) : Bool}, +lt: In.lt(next),
  eh: @m2: C.Cir.Cells -> @pg2: U32 -> {Some{vh} == C.Cir.eval(h, In.S(rg, m2, n1, F, K, pg2, L, I)) : Maybe<&2, U32>},
  ea: @m2: C.Cir.Cells -> @pg2: U32 -> {Some{va} == C.Cir.eval(a, In.S(rg, m2, n1, F, K, pg2, L, I)) : Maybe<&2, U32>},
  eb: @m2: C.Cir.Cells -> @pg2: U32 -> {Some{vb} == C.Cir.eval(b, In.S(rg, m2, n1, F, K, pg2, L, I)) : Maybe<&2, U32>},
  ef: @m2: C.Cir.Cells -> @pg2: U32 -> {Some{vc} == C.Cir.eval(c, In.S(rg, m2, n1, F, K, pg2, L, I)) : Maybe<&2, U32>}) ->
  In.Ok(C.Cir.exec(1n+f, C.M.do([C.M.st(0n, C.M.g(r), h), C.M.st(1n, C.M.g(r), C.M.c(1)), C.M.st(2n, C.M.g(r), a), C.M.st(3n, C.M.g(r), b), C.M.st(4n, C.M.g(r), c)]),
      In.S(rg, C.Cir.Cells.set(m, next, In.z()), n1, F, K, pg1, L, I)),
    s => In.Is(s, rg, C.Cir.Cells.set(m, next, C.Cir.Cell{vh, 1, va, vb, vc}), n1, F, K, L, I, In.lt(next))):
  In.seq(f, C.M.st(0n, C.M.g(r), h), C.M.do([C.M.st(1n, C.M.g(r), C.M.c(1)), C.M.st(2n, C.M.g(r), a), C.M.st(3n, C.M.g(r), b), C.M.st(4n, C.M.g(r), c)]),
      In.S(rg, C.Cir.Cells.set(m, next, In.z()), n1, F, K, pg1, L, I), rg, C.Cir.Cells.set(m, next, C.Cir.Cell{vh, 0, 0, 0, 0}), n1, F, K, L, I, In.lt(next),
      s => In.Is(s, rg, C.Cir.Cells.set(m, next, C.Cir.Cell{vh, 1, va, vb, vc}), n1, F, K, L, I, In.lt(next)),
      In.store(f, 0n, r, h, rg, m, next, In.z(), vh, n1, F, K, pg1, L, I, er, eh(C.Cir.Cells.set(m, next, In.z()), pg1), ok, In.lt(next), lt),
      +pg2 => +lt => In.seq(f, C.M.st(1n, C.M.g(r), C.M.c(1)), C.M.do([C.M.st(2n, C.M.g(r), a), C.M.st(3n, C.M.g(r), b), C.M.st(4n, C.M.g(r), c)]),
      In.S(rg, C.Cir.Cells.set(m, next, C.Cir.Cell{vh, 0, 0, 0, 0}), n1, F, K, pg2, L, I), rg, C.Cir.Cells.set(m, next, C.Cir.Cell{vh, 1, 0, 0, 0}), n1, F, K, L, I, In.lt(next),
      s => In.Is(s, rg, C.Cir.Cells.set(m, next, C.Cir.Cell{vh, 1, va, vb, vc}), n1, F, K, L, I, In.lt(next)),
      In.store(f, 1n, r, C.M.c(1), rg, m, next, C.Cir.Cell{vh, 0, 0, 0, 0}, 1, n1, F, K, pg2, L, I, er, {==}, ok, In.lt(next), lt),
      +pg3 => +lt => In.seq(f, C.M.st(2n, C.M.g(r), a), C.M.do([C.M.st(3n, C.M.g(r), b), C.M.st(4n, C.M.g(r), c)]),
      In.S(rg, C.Cir.Cells.set(m, next, C.Cir.Cell{vh, 1, 0, 0, 0}), n1, F, K, pg3, L, I), rg, C.Cir.Cells.set(m, next, C.Cir.Cell{vh, 1, va, 0, 0}), n1, F, K, L, I, In.lt(next),
      s => In.Is(s, rg, C.Cir.Cells.set(m, next, C.Cir.Cell{vh, 1, va, vb, vc}), n1, F, K, L, I, In.lt(next)),
      In.store(f, 2n, r, a, rg, m, next, C.Cir.Cell{vh, 1, 0, 0, 0}, va, n1, F, K, pg3, L, I, er, ea(C.Cir.Cells.set(m, next, C.Cir.Cell{vh, 1, 0, 0, 0}), pg3), ok, In.lt(next), lt),
      +pg4 => +lt => In.seq(f, C.M.st(3n, C.M.g(r), b), C.M.do([C.M.st(4n, C.M.g(r), c)]),
      In.S(rg, C.Cir.Cells.set(m, next, C.Cir.Cell{vh, 1, va, 0, 0}), n1, F, K, pg4, L, I), rg, C.Cir.Cells.set(m, next, C.Cir.Cell{vh, 1, va, vb, 0}), n1, F, K, L, I, In.lt(next),
      s => In.Is(s, rg, C.Cir.Cells.set(m, next, C.Cir.Cell{vh, 1, va, vb, vc}), n1, F, K, L, I, In.lt(next)),
      In.store(f, 3n, r, b, rg, m, next, C.Cir.Cell{vh, 1, va, 0, 0}, vb, n1, F, K, pg4, L, I, er, eb(C.Cir.Cells.set(m, next, C.Cir.Cell{vh, 1, va, 0, 0}), pg4), ok, In.lt(next), lt),
      +pg5 => +lt => In.seq(f, C.M.st(4n, C.M.g(r), c), C.M.do([]),
      In.S(rg, C.Cir.Cells.set(m, next, C.Cir.Cell{vh, 1, va, vb, 0}), n1, F, K, pg5, L, I), rg, C.Cir.Cells.set(m, next, C.Cir.Cell{vh, 1, va, vb, vc}), n1, F, K, L, I, In.lt(next),
      s => In.Is(s, rg, C.Cir.Cells.set(m, next, C.Cir.Cell{vh, 1, va, vb, vc}), n1, F, K, L, I, In.lt(next)),
      In.store(f, 4n, r, c, rg, m, next, C.Cir.Cell{vh, 1, va, vb, 0}, vc, n1, F, K, pg5, L, I, er, ef(C.Cir.Cells.set(m, next, C.Cir.Cell{vh, 1, va, vb, 0}), pg5), ok, In.lt(next), lt),
      +pg6 => +lt => ({==}, lt))))))

# M.make: register r gets a new cell, with the header h and the fields a, b, c
def In.make(+f: Nat, +r: Nat, +h: C.Cir.Expr, +a: C.Cir.Expr, +b: C.Cir.Expr, +c: C.Cir.Expr, +regs: List<&2, U32>, +m: C.Cir.Cells,
  +next: U32, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, U32>, +vh: U32, +va: U32, +vb: U32, +vc: U32,
  p0: {Some{0} == List.get(&2, U32, regs, 3n) : Maybe<&2, U32>}, rl: {True{} == Nat.is_lt(r, List.length(&2, U32, regs)) : Bool},
  +er: {Some{next} == List.get(&2, U32, List.set(&2, U32, regs, r, next), r) : Maybe<&2, U32>},
  ec: In.lt(next) -> {True{} == C.Cir.is_cell(next, K, F, U32.inc(next)) : Bool},
  eh: @m2: C.Cir.Cells -> @pg2: U32 -> {Some{vh} == C.Cir.eval(h, In.S(List.set(&2, U32, regs, r, next), m2, U32.inc(next), F, K, pg2, L, I)) : Maybe<&2, U32>},
  ea: @m2: C.Cir.Cells -> @pg2: U32 -> {Some{va} == C.Cir.eval(a, In.S(List.set(&2, U32, regs, r, next), m2, U32.inc(next), F, K, pg2, L, I)) : Maybe<&2, U32>},
  eb: @m2: C.Cir.Cells -> @pg2: U32 -> {Some{vb} == C.Cir.eval(b, In.S(List.set(&2, U32, regs, r, next), m2, U32.inc(next), F, K, pg2, L, I)) : Maybe<&2, U32>},
  ef: @m2: C.Cir.Cells -> @pg2: U32 -> {Some{vc} == C.Cir.eval(c, In.S(List.set(&2, U32, regs, r, next), m2, U32.inc(next), F, K, pg2, L, I)) : Maybe<&2, U32>}) ->
  In.Ok(C.Cir.exec(1n+f, C.M.make(r, h, a, b, c), In.S(regs, m, next, F, K, pg, L, I)),
    s => In.Is(s, List.set(&2, U32, regs, r, next), C.Cir.Cells.set(m, next, C.Cir.Cell{vh, 1, va, vb, vc}), U32.inc(next), F, K, L, I, In.lt(next))):
  +rg = List.set(&2, U32, regs, r, next)
  +n1 = U32.inc(next)
  In.seq(f, C.M.alloc(r), C.M.do([C.M.st(0n, C.M.g(r), h), C.M.st(1n, C.M.g(r), C.M.c(1)), C.M.st(2n, C.M.g(r), a), C.M.st(3n, C.M.g(r), b), C.M.st(4n, C.M.g(r), c)]),
    In.S(regs, m, next, F, K, pg, L, I), rg, C.Cir.Cells.set(m, next, In.z()), n1, F, K, L, I, In.lt(next),
    s => In.Is(s, rg, C.Cir.Cells.set(m, next, C.Cir.Cell{vh, 1, va, vb, vc}), n1, F, K, L, I, In.lt(next)),
    In.alloc(f, r, regs, m, next, F, K, pg, L, I, p0, rl),
    ++pg1 => +lt => In.make.stores(f, r, h, a, b, c, rg, m, next, n1, F, K, pg1, L, I, vh, va, vb, vc, er, ec(lt), lt, eh, ea, eb, ef))

# Booleans
# --------

def Bo.ft(-G: Type, h: {True{} == False{} : Bool}) -> G:
  Empty.absurd(G, N.true_ne_false(h))

def Bo.and_l(a: Bool, -b: Bool, h: {True{} == Bool.and(a, b) : Bool}) -> {True{} == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Bo.ft({True{} == False{} : Bool}, h)

def Bo.and_r(a: Bool, b: Bool, h: {True{} == Bool.and(a, b) : Bool}) -> {True{} == b : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Bo.ft({True{} == b : Bool}, h)

def Bo.and_i(-a: Bool, -b: Bool, ha: {True{} == a : Bool}, hb: {True{} == b : Bool}) -> {True{} == Bool.and(a, b) : Bool}:
  %ha : {True{} == Bool.and(_, b) : Bool}
  %hb : {True{} == Bool.and(True{}, _) : Bool}
  {==}

# The cells a term reads
# ----------------------

# the cell j may be read: one of the image's first 89, or one the machine took
# (from F, before N)
def In.rd(+j: U32, +F: U32, +N: Nat) -> Bool:
  Bool.or(Nat.is_lt(U32.to_nat(j), 89n), Bool.and(Nat.is_le(U32.to_nat(F), U32.to_nat(j)), Nat.is_lt(U32.to_nat(j), N)))

# the parts that a cell of the tag tag reads: only Ref, App, Tup and Lab
def In.rds.cell(tag: Nat, r2: Unit -> Bool, r3: Unit -> Bool) -> Bool:
  match tag:
    case 1n:
      True{}
    case 8n:
      Bool.and(r2(Unit{}), r3(Unit{}))
    case 10n:
      Bool.and(r2(Unit{}), r3(Unit{}))
    case 13n:
      True{}
    case _:
      False{}

# T.tm.of(fuel, m, ks, img, c) reads only cells that may be read, of Ref, App,
# Tup and Lab, and ends before its fuel
def In.rds(fuel: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +c: U32) -> Bool:
  match fuel:
    case 0n:
      False{}
    case 1n+(+f):
      +cell = C.Cir.Cells.get(m, c)
      Bool.and(In.rd(c, F, N), In.rds.cell(U32.to_nat(U32.and(C.Cir.Cell.get(0n, cell), 63)),
        u => In.rds(f, m, F, N, C.Cir.Cell.get(2n, cell)), u => In.rds(f, m, F, N, C.Cir.Cell.get(3n, cell))))

def In.fr.goal(tag: Nat, +q: C.Quan, +c: U32, +f2: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  a2: Maybe<&2, C.Term>, a3: Maybe<&2, C.Term>, a4: Maybe<&2, C.Term>, b2: Maybe<&2, C.Term>, b3: Maybe<&2, C.Term>, b4: Maybe<&2, C.Term>,
  s2: Bool, s3: Bool) -> Type:
  {T.tm.cell(tag, q, c, f2, ks, img, u => a2, u => a3, u => a4) == T.tm.cell(tag, q, c, f2, ks, img, u => b2, u => b3, u => b4) : Maybe<&2, C.Term>} &
  {True{} == In.rds.cell(tag, u => s2, u => s3) : Bool}

# a cell of the tag, whose parts that it reads give the same terms, gives the
# same term
def In.fr.cell(tag: Nat, +q: C.Quan, +c: U32, +f2: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +a2: Maybe<&2, C.Term>, +a3: Maybe<&2, C.Term>, +a4: Maybe<&2, C.Term>, +b2: Maybe<&2, C.Term>, +b3: Maybe<&2, C.Term>, +b4: Maybe<&2, C.Term>,
  +r2: Bool, +r3: Bool, +s2: Bool, +s3: Bool, +h: {True{} == In.rds.cell(tag, u => r2, u => r3) : Bool},
  e2: {True{} == r2 : Bool} -> {a2 == b2 : Maybe<&2, C.Term>}, k2: {True{} == r2 : Bool} -> {True{} == s2 : Bool},
  e3: {True{} == r3 : Bool} -> {a3 == b3 : Maybe<&2, C.Term>}, k3: {True{} == r3 : Bool} -> {True{} == s3 : Bool}) ->
  In.fr.goal(tag, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3):
  match tag:
    case 0n:
      Bo.ft(In.fr.goal(0n, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3), h)
    case 1n:
      ({==}, {==})
    case 2n:
      Bo.ft(In.fr.goal(2n, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3), h)
    case 3n:
      Bo.ft(In.fr.goal(3n, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3), h)
    case 4n:
      Bo.ft(In.fr.goal(4n, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3), h)
    case 5n:
      Bo.ft(In.fr.goal(5n, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3), h)
    case 6n:
      Bo.ft(In.fr.goal(6n, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3), h)
    case 7n:
      Bo.ft(In.fr.goal(7n, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3), h)
    case 8n:
      +ra = Bo.and_l(r2, r3, h)
      +rb = Bo.and_r(r2, r3, h)
      %e2(ra) : In.fr.goal(8n, q, c, f2, ks, img, a2, a3, a4, _, b3, b4, s2, s3)
      %e3(rb) : In.fr.goal(8n, q, c, f2, ks, img, a2, a3, a4, a2, _, b4, s2, s3)
      ({==}, Bo.and_i(s2, s3, k2(ra), k3(rb)))
    case 9n:
      Bo.ft(In.fr.goal(9n, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3), h)
    case 10n:
      +ra = Bo.and_l(r2, r3, h)
      +rb = Bo.and_r(r2, r3, h)
      %e2(ra) : In.fr.goal(10n, q, c, f2, ks, img, a2, a3, a4, _, b3, b4, s2, s3)
      %e3(rb) : In.fr.goal(10n, q, c, f2, ks, img, a2, a3, a4, a2, _, b4, s2, s3)
      ({==}, Bo.and_i(s2, s3, k2(ra), k3(rb)))
    case 11n:
      Bo.ft(In.fr.goal(11n, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3), h)
    case 12n:
      Bo.ft(In.fr.goal(12n, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3), h)
    case 13n:
      ({==}, {==})
    case 14n+p:
      Bo.ft(In.fr.goal(14n+p, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3), h)

# a pair of two Data types, itself Data
def In.P(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

def In.p1(-A: Data, -B: Data, p: In.P(A, B)) -> A:
  (a, b) = p
  a

def In.p2(-A: Data, -B: Data, p: In.P(A, B)) -> B:
  (a, b) = p
  b

# a cell that may be read is not one that may not
def In.ne(+c: U32, +i: U32, +F: U32, +N: Nat, hc: {True{} == In.rd(c, F, N) : Bool}, hi: {False{} == In.rd(i, F, N) : Bool},
  e: {c == i : U32}) -> Empty:
  N.true_ne_false(Equal.trans(Bool, True{}, In.rd(c, F, N), False{}, hc,
    Equal.trans(Bool, In.rd(c, F, N), In.rd(i, F, N), False{}, Equal.cong(U32, Bool, j => In.rd(j, F, N), c, i, e),
      Equal.sym(Bool, False{}, In.rd(i, F, N), hi))))

def In.fr.res(f: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +c: U32, +i: U32, +x: C.Cir.Cell, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>) -> Data:
  In.P({T.tm.of(f, m, ks, img, c) == T.tm.of(f, C.Cir.Cells.set(m, i, x), ks, img, c) : Maybe<&2, C.Term>},
    {True{} == In.rds(f, C.Cir.Cells.set(m, i, x), F, N, c) : Bool})

# a term that reads only cells that may be read keeps its term, and still
# reads only those, when a cell that may not be read is set
def In.fr(f: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +c: U32, +i: U32, +x: C.Cir.Cell, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +h: {True{} == In.rds(f, m, F, N, c) : Bool}, +hi: {False{} == In.rd(i, F, N) : Bool}) -> In.fr.res(f, m, F, N, c, i, x, ks, img):
  match f:
    case 0n:
      Bo.ft(In.fr.res(0n, m, F, N, c, i, x, ks, img), h)
    case 1n+(+p):
      ?g
