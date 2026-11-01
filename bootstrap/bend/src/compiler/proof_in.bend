import Base
import ./impl.bend as C
import ./proof_term.bend as T
import ./proof_need.bend as N
import ./proof_module.bend as PM
import ./proof_instrs.bend as PI
import ./proof_img.bend as PG

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

# a pair of two Data types, itself Data
def In.P(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

def In.fr.goal(tag: Nat, +q: C.Quan, +c: U32, +f2: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  a2: Maybe<&2, C.Term>, a3: Maybe<&2, C.Term>, a4: Maybe<&2, C.Term>, b2: Maybe<&2, C.Term>, b3: Maybe<&2, C.Term>, b4: Maybe<&2, C.Term>,
  s2: Bool, s3: Bool) -> Data:
  In.P({T.tm.cell(tag, q, c, f2, ks, img, u => a2, u => a3, u => a4) == T.tm.cell(tag, q, c, f2, ks, img, u => b2, u => b3, u => b4) : Maybe<&2, C.Term>},
    {True{} == In.rds.cell(tag, u => s2, u => s3) : Bool})

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

def In.p1(-A: Data, -B: Data, p: In.P(A, B)) -> A:
  (a, b) = p
  a

def In.p2(-A: Data, -B: Data, p: In.P(A, B)) -> B:
  (a, b) = p
  b

# fr.cell's claim, with the check of the cell itself in front
def In.fr.fin(tag: Nat, +q: C.Quan, +c: U32, +f2: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +a2: Maybe<&2, C.Term>, +a3: Maybe<&2, C.Term>, +a4: Maybe<&2, C.Term>, +b2: Maybe<&2, C.Term>, +b3: Maybe<&2, C.Term>, +b4: Maybe<&2, C.Term>,
  +s2: Bool, +s3: Bool, +rc: Bool, hc: {True{} == rc : Bool}, r: In.fr.goal(tag, q, c, f2, ks, img, a2, a3, a4, b2, b3, b4, s2, s3)) ->
  In.P({T.tm.cell(tag, q, c, f2, ks, img, u => a2, u => a3, u => a4) == T.tm.cell(tag, q, c, f2, ks, img, u => b2, u => b3, u => b4) : Maybe<&2, C.Term>},
    {True{} == Bool.and(rc, In.rds.cell(tag, u => s2, u => s3)) : Bool}):
  (e, k) = r
  (e, Bo.and_i(rc, In.rds.cell(tag, u => s2, u => s3), hc, k))

# a cell that may be read is not one that may not
def In.ne(+c: U32, +i: U32, +F: U32, +N: Nat, hc: {True{} == In.rd(c, F, N) : Bool}, hi: {False{} == In.rd(i, F, N) : Bool},
  e: {c == i : U32}) -> Empty:
  N.true_ne_false(Equal.trans(Bool, True{}, In.rd(c, F, N), False{}, hc,
    Equal.trans(Bool, In.rd(c, F, N), In.rd(i, F, N), False{}, Equal.cong(U32, Bool, j => In.rd(j, F, N), c, i, e),
      Equal.sym(Bool, False{}, In.rd(i, F, N), hi))))

# In.fr's claim, once its fuel's first unit is spent, with the cell cl at c in
# the cells ms
def In.fr.after(+p: Nat, +m: C.Cir.Cells, +ms: C.Cir.Cells, +F: U32, +N: Nat, +c: U32, +cl: C.Cir.Cell, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>) -> Data:
  +cm = C.Cir.Cells.get(m, c)
  In.P({T.tm.cell(U32.to_nat(U32.and(C.Cir.Cell.get(0n, cm), 63)), T.tm.quan(U32.and(U32.shrn(C.Cir.Cell.get(0n, cm), 6n), 3)), c,
      C.Cir.Cell.get(2n, cm), ks, img, u => T.tm.of(p, m, ks, img, C.Cir.Cell.get(2n, cm)), u => T.tm.of(p, m, ks, img, C.Cir.Cell.get(3n, cm)),
      u => T.tm.of(p, m, ks, img, C.Cir.Cell.get(4n, cm))) ==
    T.tm.cell(U32.to_nat(U32.and(C.Cir.Cell.get(0n, cl), 63)), T.tm.quan(U32.and(U32.shrn(C.Cir.Cell.get(0n, cl), 6n), 3)), c,
      C.Cir.Cell.get(2n, cl), ks, img, u => T.tm.of(p, ms, ks, img, C.Cir.Cell.get(2n, cl)), u => T.tm.of(p, ms, ks, img, C.Cir.Cell.get(3n, cl)),
      u => T.tm.of(p, ms, ks, img, C.Cir.Cell.get(4n, cl))) : Maybe<&2, C.Term>},
    {True{} == Bool.and(In.rd(c, F, N), In.rds.cell(U32.to_nat(U32.and(C.Cir.Cell.get(0n, cl), 63)),
      u => In.rds(p, ms, F, N, C.Cir.Cell.get(2n, cl)), u => In.rds(p, ms, F, N, C.Cir.Cell.get(3n, cl)))) : Bool})

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
      +ms = C.Cir.Cells.set(m, i, x)
      +cl = C.Cir.Cells.get(m, c)
      +tag = U32.to_nat(U32.and(C.Cir.Cell.get(0n, cl), 63))
      +f2 = C.Cir.Cell.get(2n, cl)
      +f3 = C.Cir.Cell.get(3n, cl)
      +f4 = C.Cir.Cell.get(4n, cl)
      +hc = Bo.and_l(In.rd(c, F, N), In.rds.cell(tag, u => In.rds(p, m, F, N, f2), u => In.rds(p, m, F, N, f3)), h)
      +hr = Bo.and_r(In.rd(c, F, N), In.rds.cell(tag, u => In.rds(p, m, F, N, f2), u => In.rds(p, m, F, N, f3)), h)
      %Cl.get_other(m, c, i, x, e => In.ne(c, i, F, N, hc, hi, e)) : In.fr.after(p, m, ms, F, N, c, _, ks, img)
      +r = In.fr.cell(tag, T.tm.quan(U32.and(U32.shrn(C.Cir.Cell.get(0n, cl), 6n), 3)), c, f2, ks, img,
        T.tm.of(p, m, ks, img, f2), T.tm.of(p, m, ks, img, f3), T.tm.of(p, m, ks, img, f4),
        T.tm.of(p, ms, ks, img, f2), T.tm.of(p, ms, ks, img, f3), T.tm.of(p, ms, ks, img, f4),
        In.rds(p, m, F, N, f2), In.rds(p, m, F, N, f3), In.rds(p, ms, F, N, f2), In.rds(p, ms, F, N, f3), hr,
        k => In.p1({T.tm.of(p, m, ks, img, f2) == T.tm.of(p, ms, ks, img, f2) : Maybe<&2, C.Term>}, {True{} == In.rds(p, ms, F, N, f2) : Bool},
          In.fr(p, m, F, N, f2, i, x, ks, img, k, hi)),
        k => In.p2({T.tm.of(p, m, ks, img, f2) == T.tm.of(p, ms, ks, img, f2) : Maybe<&2, C.Term>}, {True{} == In.rds(p, ms, F, N, f2) : Bool},
          In.fr(p, m, F, N, f2, i, x, ks, img, k, hi)),
        k => In.p1({T.tm.of(p, m, ks, img, f3) == T.tm.of(p, ms, ks, img, f3) : Maybe<&2, C.Term>}, {True{} == In.rds(p, ms, F, N, f3) : Bool},
          In.fr(p, m, F, N, f3, i, x, ks, img, k, hi)),
        k => In.p2({T.tm.of(p, m, ks, img, f3) == T.tm.of(p, ms, ks, img, f3) : Maybe<&2, C.Term>}, {True{} == In.rds(p, ms, F, N, f3) : Bool},
          In.fr(p, m, F, N, f3, i, x, ks, img, k, hi)))
      In.fr.fin(tag, T.tm.quan(U32.and(U32.shrn(C.Cir.Cell.get(0n, cl), 6n), 3)), c, f2, ks, img,
        T.tm.of(p, m, ks, img, f2), T.tm.of(p, m, ks, img, f3), T.tm.of(p, m, ks, img, f4),
        T.tm.of(p, ms, ks, img, f2), T.tm.of(p, ms, ks, img, f3), T.tm.of(p, ms, ks, img, f4),
        In.rds(p, ms, F, N, f2), In.rds(p, ms, F, N, f3), In.rd(c, F, N), hc, r)

# a term that reads only cells that may be read, with fuel to spare
def In.mono(f: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +c: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +h: {True{} == In.rds(f, m, F, N, c) : Bool}) ->
  In.P({T.tm.of(f, m, ks, img, c) == T.tm.of(1n+f, m, ks, img, c) : Maybe<&2, C.Term>}, {True{} == In.rds(1n+f, m, F, N, c) : Bool}):
  match f:
    case 0n:
      Bo.ft(In.P({T.tm.of(0n, m, ks, img, c) == T.tm.of(1n, m, ks, img, c) : Maybe<&2, C.Term>}, {True{} == In.rds(1n, m, F, N, c) : Bool}), h)
    case 1n+(+p):
      +cl = C.Cir.Cells.get(m, c)
      +tag = U32.to_nat(U32.and(C.Cir.Cell.get(0n, cl), 63))
      +f2 = C.Cir.Cell.get(2n, cl)
      +f3 = C.Cir.Cell.get(3n, cl)
      +f4 = C.Cir.Cell.get(4n, cl)
      +hc = Bo.and_l(In.rd(c, F, N), In.rds.cell(tag, u => In.rds(p, m, F, N, f2), u => In.rds(p, m, F, N, f3)), h)
      +hr = Bo.and_r(In.rd(c, F, N), In.rds.cell(tag, u => In.rds(p, m, F, N, f2), u => In.rds(p, m, F, N, f3)), h)
      +r = In.fr.cell(tag, T.tm.quan(U32.and(U32.shrn(C.Cir.Cell.get(0n, cl), 6n), 3)), c, f2, ks, img,
        T.tm.of(p, m, ks, img, f2), T.tm.of(p, m, ks, img, f3), T.tm.of(p, m, ks, img, f4),
        T.tm.of(1n+p, m, ks, img, f2), T.tm.of(1n+p, m, ks, img, f3), T.tm.of(1n+p, m, ks, img, f4),
        In.rds(p, m, F, N, f2), In.rds(p, m, F, N, f3), In.rds(1n+p, m, F, N, f2), In.rds(1n+p, m, F, N, f3), hr,
        k => In.p1({T.tm.of(p, m, ks, img, f2) == T.tm.of(1n+p, m, ks, img, f2) : Maybe<&2, C.Term>}, {True{} == In.rds(1n+p, m, F, N, f2) : Bool},
          In.mono(p, m, F, N, f2, ks, img, k)),
        k => In.p2({T.tm.of(p, m, ks, img, f2) == T.tm.of(1n+p, m, ks, img, f2) : Maybe<&2, C.Term>}, {True{} == In.rds(1n+p, m, F, N, f2) : Bool},
          In.mono(p, m, F, N, f2, ks, img, k)),
        k => In.p1({T.tm.of(p, m, ks, img, f3) == T.tm.of(1n+p, m, ks, img, f3) : Maybe<&2, C.Term>}, {True{} == In.rds(1n+p, m, F, N, f3) : Bool},
          In.mono(p, m, F, N, f3, ks, img, k)),
        k => In.p2({T.tm.of(p, m, ks, img, f3) == T.tm.of(1n+p, m, ks, img, f3) : Maybe<&2, C.Term>}, {True{} == In.rds(1n+p, m, F, N, f3) : Bool},
          In.mono(p, m, F, N, f3, ks, img, k)))
      In.fr.fin(tag, T.tm.quan(U32.and(U32.shrn(C.Cir.Cell.get(0n, cl), 6n), 3)), c, f2, ks, img,
        T.tm.of(p, m, ks, img, f2), T.tm.of(p, m, ks, img, f3), T.tm.of(p, m, ks, img, f4),
        T.tm.of(1n+p, m, ks, img, f2), T.tm.of(1n+p, m, ks, img, f3), T.tm.of(1n+p, m, ks, img, f4),
        In.rds(1n+p, m, F, N, f2), In.rds(1n+p, m, F, N, f3), In.rd(c, F, N), hc, r)

# Nat: a < n gives a < 1 + n
def Na.lt_up(a: Nat, n: Nat, h: {True{} == Nat.is_lt(a, n) : Bool}) -> {True{} == Nat.is_lt(a, 1n+n) : Bool}:
  match a n:
    case 0n _:
      {==}
    case 1n+x 0n:
      Bo.ft({True{} == Nat.is_lt(1n+x, 1n) : Bool}, h)
    case 1n+x 1n+y:
      Na.lt_up(x, y, h)

def Bo.or_mono(a: Bool, -b: Bool, -c: Bool, h: {True{} == Bool.or(a, b) : Bool}, k: {True{} == b : Bool} -> {True{} == c : Bool}) ->
  {True{} == Bool.or(a, c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      k(h)

def Bo.and_mono(a: Bool, -b: Bool, -c: Bool, h: {True{} == Bool.and(a, b) : Bool}, k: {True{} == b : Bool} -> {True{} == c : Bool}) ->
  {True{} == Bool.and(a, c) : Bool}:
  match a:
    case True{}:
      k(h)
    case False{}:
      h

# a cell that may be read still may, once one more is taken
def In.rd_up(+j: U32, +F: U32, +N: Nat, h: {True{} == In.rd(j, F, N) : Bool}) -> {True{} == In.rd(j, F, 1n+N) : Bool}:
  Bo.or_mono(Nat.is_lt(U32.to_nat(j), 89n), Bool.and(Nat.is_le(U32.to_nat(F), U32.to_nat(j)), Nat.is_lt(U32.to_nat(j), N)),
    Bool.and(Nat.is_le(U32.to_nat(F), U32.to_nat(j)), Nat.is_lt(U32.to_nat(j), 1n+N)), h,
    k => Bo.and_mono(Nat.is_le(U32.to_nat(F), U32.to_nat(j)), Nat.is_lt(U32.to_nat(j), N), Nat.is_lt(U32.to_nat(j), 1n+N), k,
      l => Na.lt_up(U32.to_nat(j), N, l)))

# a term that reads only cells that may be read still does, once one more
# cell is taken
def In.up(f: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +c: U32, +h: {True{} == In.rds(f, m, F, N, c) : Bool}) ->
  {True{} == In.rds(f, m, F, 1n+N, c) : Bool}:
  match f:
    case 0n:
      h
    case 1n+(+p):
      +cl = C.Cir.Cells.get(m, c)
      +tag = U32.to_nat(U32.and(C.Cir.Cell.get(0n, cl), 63))
      +f2 = C.Cir.Cell.get(2n, cl)
      +f3 = C.Cir.Cell.get(3n, cl)
      +hc = Bo.and_l(In.rd(c, F, N), In.rds.cell(tag, u => In.rds(p, m, F, N, f2), u => In.rds(p, m, F, N, f3)), h)
      +hr = Bo.and_r(In.rd(c, F, N), In.rds.cell(tag, u => In.rds(p, m, F, N, f2), u => In.rds(p, m, F, N, f3)), h)
      +r = In.fr.cell(tag, C.Quan.Q0{}, c, f2, [], [], None{}, None{}, None{}, None{}, None{}, None{},
        In.rds(p, m, F, N, f2), In.rds(p, m, F, N, f3), In.rds(p, m, F, 1n+N, f2), In.rds(p, m, F, 1n+N, f3), hr,
        k => {==}, k => In.up(p, m, F, N, f2, k), k => {==}, k => In.up(p, m, F, N, f3, k))
      Bo.and_i(In.rd(c, F, 1n+N), In.rds.cell(tag, u => In.rds(p, m, F, 1n+N, f2), u => In.rds(p, m, F, 1n+N, f3)),
        In.rd_up(c, F, N, hc),
        In.p2({T.tm.cell(tag, C.Quan.Q0{}, c, f2, [], [], u => None{}, u => None{}, u => None{}) ==
          T.tm.cell(tag, C.Quan.Q0{}, c, f2, [], [], u => None{}, u => None{}, u => None{}) : Maybe<&2, C.Term>},
          {True{} == In.rds.cell(tag, u => In.rds(p, m, F, 1n+N, f2), u => In.rds(p, m, F, 1n+N, f3)) : Bool}, r))

# Terms of cells
# --------------

# the cell c of the cells m stands for t with the fuel f, reading only cells
# that may be read (F and N bound the machine's own)
def In.St(f: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +c: U32, +t: C.Term, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>) -> Data:
  In.P({Some{t} == T.tm.of(f, m, ks, img, c) : Maybe<&2, C.Term>}, {True{} == In.rds(f, m, F, N, c) : Bool})

# a cell that may not be read is set
def St.fr(+f: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +c: U32, +t: C.Term, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +i: U32, +x: C.Cir.Cell, +hi: {False{} == In.rd(i, F, N) : Bool}, s: In.St(f, m, F, N, c, t, ks, img)) ->
  In.St(f, C.Cir.Cells.set(m, i, x), F, N, c, t, ks, img):
  (e, r) = s
  +q = In.fr(f, m, F, N, c, i, x, ks, img, r, hi)
  (Equal.trans(Maybe<&2, C.Term>, Some{t}, T.tm.of(f, m, ks, img, c), T.tm.of(f, C.Cir.Cells.set(m, i, x), ks, img, c), e,
    In.p1({T.tm.of(f, m, ks, img, c) == T.tm.of(f, C.Cir.Cells.set(m, i, x), ks, img, c) : Maybe<&2, C.Term>},
      {True{} == In.rds(f, C.Cir.Cells.set(m, i, x), F, N, c) : Bool}, q)),
   In.p2({T.tm.of(f, m, ks, img, c) == T.tm.of(f, C.Cir.Cells.set(m, i, x), ks, img, c) : Maybe<&2, C.Term>},
      {True{} == In.rds(f, C.Cir.Cells.set(m, i, x), F, N, c) : Bool}, q))

# one more cell is taken
def St.up(+f: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +c: U32, +t: C.Term, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  s: In.St(f, m, F, N, c, t, ks, img)) -> In.St(f, m, F, 1n+N, c, t, ks, img):
  (e, r) = s
  (e, In.up(f, m, F, N, c, r))

# one more unit of fuel
def St.mono(+f: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +c: U32, +t: C.Term, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  s: In.St(f, m, F, N, c, t, ks, img)) -> In.St(1n+f, m, F, N, c, t, ks, img):
  (e, r) = s
  +q = In.mono(f, m, F, N, c, ks, img, r)
  (Equal.trans(Maybe<&2, C.Term>, Some{t}, T.tm.of(f, m, ks, img, c), T.tm.of(1n+f, m, ks, img, c), e,
    In.p1({T.tm.of(f, m, ks, img, c) == T.tm.of(1n+f, m, ks, img, c) : Maybe<&2, C.Term>},
      {True{} == In.rds(1n+f, m, F, N, c) : Bool}, q)),
   In.p2({T.tm.of(f, m, ks, img, c) == T.tm.of(1n+f, m, ks, img, c) : Maybe<&2, C.Term>},
      {True{} == In.rds(1n+f, m, F, N, c) : Bool}, q))

# more fuel
def St.add(d: Nat, +f: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +c: U32, +t: C.Term, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  s: In.St(f, m, F, N, c, t, ks, img)) -> In.St(Nat.add(d, f), m, F, N, c, t, ks, img):
  match d:
    case 0n:
      s
    case 1n+(+p):
      St.mono(Nat.add(p, f), m, F, N, c, t, ks, img, St.add(p, f, m, F, N, c, t, ks, img, s))

# (g - f) + f = g, when f <= g
def Na.sub_add(g: Nat, f: Nat, h: N.Le(f, g)) -> {g == Nat.add(Nat.sub(g, f), f) : Nat}:
  match g f:
    case 0n 0n:
      {==}
    case 0n 1n+a:
      Empty.absurd({0n == Nat.add(Nat.sub(0n, 1n+a), 1n+a) : Nat}, h)
    case 1n+b 0n:
      Equal.sym(Nat, Nat.add(1n+b, 0n), 1n+b, N.add_zero(1n+b))
    case 1n+(+b) 1n+(+a):
      %Equal.sym(Nat, Nat.add(Nat.sub(b, a), 1n+a), 1n+Nat.add(Nat.sub(b, a), a), N.add_succ_r(Nat.sub(b, a), a)) : {1n+b == _ : Nat}
      Equal.cong(Nat, Nat, x => 1n+x, b, Nat.add(Nat.sub(b, a), a), Na.sub_add(b, a, h))

# any more fuel
def St.to(+f: Nat, +g: Nat, h: N.Le(f, g), +m: C.Cir.Cells, +F: U32, +N: Nat, +c: U32, +t: C.Term, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, s: In.St(f, m, F, N, c, t, ks, img)) -> In.St(g, m, F, N, c, t, ks, img):
  %Equal.sym(Nat, g, Nat.add(Nat.sub(g, f), f), Na.sub_add(g, f, h)) : In.St(_, m, F, N, c, t, ks, img)
  St.add(Nat.sub(g, f), f, m, F, N, c, t, ks, img, s)

# St's claim with the cell cl at c, once a unit of fuel is spent
def In.St.after(+f: Nat, +ms: C.Cir.Cells, +F: U32, +N: Nat, +c: U32, +cl: C.Cir.Cell, +t: C.Term, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>) -> Data:
  In.P({Some{t} == T.tm.cell(U32.to_nat(U32.and(C.Cir.Cell.get(0n, cl), 63)), T.tm.quan(U32.and(U32.shrn(C.Cir.Cell.get(0n, cl), 6n), 3)), c,
      C.Cir.Cell.get(2n, cl), ks, img, u => T.tm.of(f, ms, ks, img, C.Cir.Cell.get(2n, cl)), u => T.tm.of(f, ms, ks, img, C.Cir.Cell.get(3n, cl)),
      u => T.tm.of(f, ms, ks, img, C.Cir.Cell.get(4n, cl))) : Maybe<&2, C.Term>},
    {True{} == Bool.and(In.rd(c, F, N), In.rds.cell(U32.to_nat(U32.and(C.Cir.Cell.get(0n, cl), 63)),
      u => In.rds(f, ms, F, N, C.Cir.Cell.get(2n, cl)), u => In.rds(f, ms, F, N, C.Cir.Cell.get(3n, cl)))) : Bool})

# a cell of two parts, at the quantity 1 (Tup, App), with its parts' terms
def In.two.go(+hd: U32, +f: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +i: U32, +p: U32, +q: U32, +t: C.Term, +tp: C.Term, +tq: C.Term,
  +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  ep: {Some{tp} == T.tm.of(f, C.Cir.Cells.set(m, i, C.Cir.Cell{hd, 1, p, q, 0}), ks, img, p) : Maybe<&2, C.Term>},
  rp: {True{} == In.rds(f, C.Cir.Cells.set(m, i, C.Cir.Cell{hd, 1, p, q, 0}), F, 1n+N, p) : Bool},
  eq: {Some{tq} == T.tm.of(f, C.Cir.Cells.set(m, i, C.Cir.Cell{hd, 1, p, q, 0}), ks, img, q) : Maybe<&2, C.Term>},
  rq: {True{} == In.rds(f, C.Cir.Cells.set(m, i, C.Cir.Cell{hd, 1, p, q, 0}), F, 1n+N, q) : Bool},
  hr: {True{} == In.rd(i, F, 1n+N) : Bool},
  et: {Some{t} == T.tm.cell(U32.to_nat(U32.and(hd, 63)), T.tm.quan(U32.and(U32.shrn(hd, 6n), 3)), i, p, ks, img, u => Some{tp}, u => Some{tq},
    u => T.tm.of(f, C.Cir.Cells.set(m, i, C.Cir.Cell{hd, 1, p, q, 0}), ks, img, 0)) : Maybe<&2, C.Term>},
  er: {True{} == In.rds.cell(U32.to_nat(U32.and(hd, 63)), u => True{}, u => True{}) : Bool}) ->
  In.St(1n+f, C.Cir.Cells.set(m, i, C.Cir.Cell{hd, 1, p, q, 0}), F, 1n+N, i, t, ks, img):
  +ms = C.Cir.Cells.set(m, i, C.Cir.Cell{hd, 1, p, q, 0})
  %Equal.sym(C.Cir.Cell, C.Cir.Cells.get(ms, i), C.Cir.Cell{hd, 1, p, q, 0}, Cl.get_set(m, i, C.Cir.Cell{hd, 1, p, q, 0})) :
    In.St.after(f, ms, F, 1n+N, i, _, t, ks, img)
  %ep : In.P({Some{t} == T.tm.cell(U32.to_nat(U32.and(hd, 63)), T.tm.quan(U32.and(U32.shrn(hd, 6n), 3)), i, p, ks, img, u => _, u => T.tm.of(f, ms, ks, img, q), u => T.tm.of(f, ms, ks, img, 0)) : Maybe<&2, C.Term>},
      {True{} == Bool.and(In.rd(i, F, 1n+N), In.rds.cell(U32.to_nat(U32.and(hd, 63)), u => In.rds(f, ms, F, 1n+N, p), u => In.rds(f, ms, F, 1n+N, q))) : Bool})
  %eq : In.P({Some{t} == T.tm.cell(U32.to_nat(U32.and(hd, 63)), T.tm.quan(U32.and(U32.shrn(hd, 6n), 3)), i, p, ks, img, u => Some{tp}, u => _, u => T.tm.of(f, ms, ks, img, 0)) : Maybe<&2, C.Term>},
      {True{} == Bool.and(In.rd(i, F, 1n+N), In.rds.cell(U32.to_nat(U32.and(hd, 63)), u => In.rds(f, ms, F, 1n+N, p), u => In.rds(f, ms, F, 1n+N, q))) : Bool})
  %rp : In.P({Some{t} == T.tm.cell(U32.to_nat(U32.and(hd, 63)), T.tm.quan(U32.and(U32.shrn(hd, 6n), 3)), i, p, ks, img, u => Some{tp}, u => Some{tq}, u => T.tm.of(f, ms, ks, img, 0)) : Maybe<&2, C.Term>},
      {True{} == Bool.and(In.rd(i, F, 1n+N), In.rds.cell(U32.to_nat(U32.and(hd, 63)), u => _, u => In.rds(f, ms, F, 1n+N, q))) : Bool})
  %rq : In.P({Some{t} == T.tm.cell(U32.to_nat(U32.and(hd, 63)), T.tm.quan(U32.and(U32.shrn(hd, 6n), 3)), i, p, ks, img, u => Some{tp}, u => Some{tq}, u => T.tm.of(f, ms, ks, img, 0)) : Maybe<&2, C.Term>},
      {True{} == Bool.and(In.rd(i, F, 1n+N), In.rds.cell(U32.to_nat(U32.and(hd, 63)), u => True{}, u => _)) : Bool})
  %hr : In.P({Some{t} == T.tm.cell(U32.to_nat(U32.and(hd, 63)), T.tm.quan(U32.and(U32.shrn(hd, 6n), 3)), i, p, ks, img, u => Some{tp}, u => Some{tq}, u => T.tm.of(f, ms, ks, img, 0)) : Maybe<&2, C.Term>},
      {True{} == Bool.and(_, In.rds.cell(U32.to_nat(U32.and(hd, 63)), u => True{}, u => True{})) : Bool})
  (et, er)

def In.two.of(+hd: U32, +f: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +i: U32, +p: U32, +q: U32, +t: C.Term, +tp: C.Term, +tq: C.Term,
  +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  sp: In.St(f, C.Cir.Cells.set(m, i, C.Cir.Cell{hd, 1, p, q, 0}), F, 1n+N, p, tp, ks, img),
  sq: In.St(f, C.Cir.Cells.set(m, i, C.Cir.Cell{hd, 1, p, q, 0}), F, 1n+N, q, tq, ks, img),
  hr: {True{} == In.rd(i, F, 1n+N) : Bool},
  et: {Some{t} == T.tm.cell(U32.to_nat(U32.and(hd, 63)), T.tm.quan(U32.and(U32.shrn(hd, 6n), 3)), i, p, ks, img, u => Some{tp}, u => Some{tq},
    u => T.tm.of(f, C.Cir.Cells.set(m, i, C.Cir.Cell{hd, 1, p, q, 0}), ks, img, 0)) : Maybe<&2, C.Term>},
  er: {True{} == In.rds.cell(U32.to_nat(U32.and(hd, 63)), u => True{}, u => True{}) : Bool}) ->
  In.St(1n+f, C.Cir.Cells.set(m, i, C.Cir.Cell{hd, 1, p, q, 0}), F, 1n+N, i, t, ks, img):
  (ep, rp) = sp
  (eq, rq) = sq
  In.two.go(hd, f, m, F, N, i, p, q, t, tp, tq, ks, img, ep, rp, eq, rq, hr, et, er)

# a new cell i of two parts p and q (Tup or App at the quantity 1), which
# stand for tp and tq
def In.two(+hd: U32, +f: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +i: U32, +p: U32, +q: U32, +t: C.Term, +tp: C.Term, +tq: C.Term,
  +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  sp: In.St(f, m, F, N, p, tp, ks, img), sq: In.St(f, m, F, N, q, tq, ks, img),
  +hi: {False{} == In.rd(i, F, N) : Bool}, hr: {True{} == In.rd(i, F, 1n+N) : Bool},
  et: {Some{t} == T.tm.cell(U32.to_nat(U32.and(hd, 63)), T.tm.quan(U32.and(U32.shrn(hd, 6n), 3)), i, p, ks, img, u => Some{tp}, u => Some{tq},
    u => T.tm.of(f, C.Cir.Cells.set(m, i, C.Cir.Cell{hd, 1, p, q, 0}), ks, img, 0)) : Maybe<&2, C.Term>},
  er: {True{} == In.rds.cell(U32.to_nat(U32.and(hd, 63)), u => True{}, u => True{}) : Bool}) ->
  In.St(1n+f, C.Cir.Cells.set(m, i, C.Cir.Cell{hd, 1, p, q, 0}), F, 1n+N, i, t, ks, img):
  +x = {C.Cir.Cell{hd, 1, p, q, 0} : C.Cir.Cell}
  +ms = C.Cir.Cells.set(m, i, x)
  In.two.of(hd, f, m, F, N, i, p, q, t, tp, tq, ks, img,
    St.up(f, ms, F, N, p, tp, ks, img, St.fr(f, m, F, N, p, tp, ks, img, i, x, hi, sp)),
    St.up(f, ms, F, N, q, tq, ks, img, St.fr(f, m, F, N, q, tq, ks, img, i, x, hi, sq)), hr, et, er)

# the pairs that the machine makes: STATIC (1866) or not (842)
def In.hd(st: Bool) -> U32:
  match st:
    case True{}:
      1866
    case False{}:
      842

def In.tup(st: Bool, +f: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +i: U32, +p: U32, +q: U32, +tp: C.Term, +tq: C.Term,
  +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  sp: In.St(f, m, F, N, p, tp, ks, img), sq: In.St(f, m, F, N, q, tq, ks, img),
  +hi: {False{} == In.rd(i, F, N) : Bool}, hr: {True{} == In.rd(i, F, 1n+N) : Bool}) ->
  In.St(1n+f, C.Cir.Cells.set(m, i, C.Cir.Cell{In.hd(st), 1, p, q, 0}), F, 1n+N, i, C.Term.Tup{C.Quan.Q1{}, tp, tq}, ks, img):
  match st:
    case True{}:
      In.two(1866, f, m, F, N, i, p, q, C.Term.Tup{C.Quan.Q1{}, tp, tq}, tp, tq, ks, img, sp, sq, hi, hr, {==}, {==})
    case False{}:
      In.two(842, f, m, F, N, i, p, q, C.Term.Tup{C.Quan.Q1{}, tp, tq}, tp, tq, ks, img, sp, sq, hi, hr, {==}, {==})

def In.app(+f: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +i: U32, +p: U32, +q: U32, +tp: C.Term, +tq: C.Term,
  +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  sp: In.St(f, m, F, N, p, tp, ks, img), sq: In.St(f, m, F, N, q, tq, ks, img),
  +hi: {False{} == In.rd(i, F, N) : Bool}, hr: {True{} == In.rd(i, F, 1n+N) : Bool}) ->
  In.St(1n+f, C.Cir.Cells.set(m, i, C.Cir.Cell{72, 1, p, q, 0}), F, 1n+N, i, C.Term.App{C.Quan.Q1{}, tp, tq}, ks, img):
  In.two(72, f, m, F, N, i, p, q, C.Term.App{C.Quan.Q1{}, tp, tq}, tp, tq, ks, img, sp, sq, hi, hr, {==}, {==})

# The cache
# ---------

type In.Or<-A: Data, -B: Data> is Data:
  In.Or.l{a: A}
  In.Or.r{b: B}

# a byte of the bits w, the lowest first
def In.u8(w: Word(8n)) -> U32:
  match w:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}:
      U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}}

# the low 8 bits of x
def In.low8(x: U32) -> Word(8n):
  match x:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, _}}}}}}}}}:
      WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}

# the cache cell of the byte of the bits w
def In.J(+w: Word(8n)) -> U32:
  U32.add(89, In.u8(w))

# the cache's entry for the byte of the bits w: none yet, or the cell of its U32
def In.En(+fc: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +w: Word(8n), +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>) -> Data:
  +v = C.Cir.Cell.get(2n, C.Cir.Cells.get(m, In.J(w)))
  In.Or<{0 == v : U32}, In.St(fc, m, F, N, v, C.Program.cell.of(In.u8(w)), ks, img)>

# the bit at the head of bs, False after its end
def In.bh(bs: List<&2, Bool>) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Con{b, _}:
      b

def In.bt(bs: List<&2, Bool>) -> List<&2, Bool>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{_, r}:
      r

# the byte of the bits bs, the highest first
def In.wl(+bs: List<&2, Bool>) -> Word(8n):
  +b1 = In.bt(bs)
  +b2 = In.bt(b1)
  +b3 = In.bt(b2)
  +b4 = In.bt(b3)
  +b5 = In.bt(b4)
  +b6 = In.bt(b5)
  +b7 = In.bt(b6)
  WCon{In.bh(b7), WCon{In.bh(b6), WCon{In.bh(b5), WCon{In.bh(b4), WCon{In.bh(b3), WCon{In.bh(b2), WCon{In.bh(b1), WCon{In.bh(bs), WNil{}}}}}}}}}

# the bits of w, the lowest first, onto bs
def In.push(n: Nat, w: Word(n), bs: List<&2, Bool>) -> List<&2, Bool>:
  match n:
    case 0n:
      bs
    case 1n+(+p):
      match w:
        case WCon{b, t}:
          In.push(p, t, Con{b, bs})

def In.wl_push(w: Word(8n)) -> {w == In.wl(In.push(8n, w, [])) : Word(8n)}:
  match w:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}:
      {==}

# the entries of the bytes of the bits bs, after n more, for every n more
def In.CI(n: Nat, +bs: List<&2, Bool>, +fc: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>) -> Data:
  match n:
    case 0n:
      In.En(fc, m, F, N, In.wl(bs), ks, img)
    case 1n+p:
      In.P(In.CI(p, Con{False{}, bs}, fc, m, F, N, ks, img), In.CI(p, Con{True{}, bs}, fc, m, F, N, ks, img))

# the cache cell of a byte lies in 89 to 344, and gives the byte back
def In.Jb(w: Word(8n)) -> In.P(N.Le(89n, U32.to_nat(In.J(w))), In.P(N.Le(1n+U32.to_nat(In.J(w)), 345n),
  {In.u8(w) == U32.and(U32.sub(In.J(w), 89), 255) : U32})):
  match w:
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      (Unit{}, (Unit{}, {==}))

# the bits of a byte, back
def In.low8_u8(w: Word(8n)) -> {w == In.low8(In.u8(w)) : Word(8n)}:
  match w:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}:
      {==}

# the cache cells of two bytes are two
def In.J_inj(+w: Word(8n), +v: Word(8n), e: {In.J(w) == In.J(v) : U32}) -> {w == v : Word(8n)}:
  +a = In.p2(N.Le(1n+U32.to_nat(In.J(w)), 345n), {In.u8(w) == U32.and(U32.sub(In.J(w), 89), 255) : U32},
    In.p2(N.Le(89n, U32.to_nat(In.J(w))), In.P(N.Le(1n+U32.to_nat(In.J(w)), 345n), {In.u8(w) == U32.and(U32.sub(In.J(w), 89), 255) : U32}), In.Jb(w)))
  +b = In.p2(N.Le(1n+U32.to_nat(In.J(v)), 345n), {In.u8(v) == U32.and(U32.sub(In.J(v), 89), 255) : U32},
    In.p2(N.Le(89n, U32.to_nat(In.J(v))), In.P(N.Le(1n+U32.to_nat(In.J(v)), 345n), {In.u8(v) == U32.and(U32.sub(In.J(v), 89), 255) : U32}), In.Jb(v)))
  +uw = Equal.trans(U32, In.u8(w), U32.and(U32.sub(In.J(w), 89), 255), U32.and(U32.sub(In.J(v), 89), 255), a,
    Equal.cong(U32, U32, y => U32.and(U32.sub(y, 89), 255), In.J(w), In.J(v), e))
  +uv = Equal.trans(U32, In.u8(w), U32.and(U32.sub(In.J(v), 89), 255), In.u8(v), uw, Equal.sym(U32, In.u8(v), U32.and(U32.sub(In.J(v), 89), 255), b))
  Equal.trans(Word(8n), w, In.low8(In.u8(w)), v, In.low8_u8(w),
    Equal.trans(Word(8n), In.low8(In.u8(w)), In.low8(In.u8(v)), v, Equal.cong(U32, Word(8n), y => In.low8(y), In.u8(w), In.u8(v), uv),
      Equal.sym(Word(8n), v, In.low8(In.u8(v)), In.low8_u8(v))))

# bits and words, compared
def In.beq(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case _ _:
      False{}

def In.weq(n: Nat, a: Word(n), b: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match a b:
        case WCon{x, s} WCon{y, t}:
          Bool.and(In.beq(x, y), In.weq(p, s, t))

def In.weq_t(n: Nat, a: Word(n), b: Word(n), h: {True{} == In.weq(n, a, b) : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b:
        case WCon{True{}, +s} WCon{True{}, +t}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, s, t, In.weq_t(p, s, t, h))
        case WCon{False{}, +s} WCon{False{}, +t}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, s, t, In.weq_t(p, s, t, h))
        case WCon{True{}, +s} WCon{False{}, +t}:
          Bo.ft({WCon{True{}, s} == WCon{False{}, t} : Word(1n+p)}, h)
        case WCon{False{}, +s} WCon{True{}, +t}:
          Bo.ft({WCon{False{}, s} == WCon{True{}, t} : Word(1n+p)}, h)

def In.weq_refl(n: Nat, a: Word(n)) -> {True{} == In.weq(n, a, a) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      match a:
        case WCon{True{}, +s}:
          In.weq_refl(p, s)
        case WCon{False{}, +s}:
          In.weq_refl(p, s)

def In.weq_f(+n: Nat, +a: Word(n), +b: Word(n), h: {False{} == In.weq(n, a, b) : Bool}, e: {a == b : Word(n)}) -> Empty:
  +r = Equal.trans(Bool, True{}, In.weq(n, a, a), In.weq(n, a, b), In.weq_refl(n, a), Equal.cong(Word(n), Bool, z => In.weq(n, a, z), a, b, e))
  N.true_ne_false(Equal.trans(Bool, True{}, In.weq(n, a, b), False{}, r, Equal.sym(Bool, False{}, In.weq(n, a, b), h)))

# Numbers
# -------

def Na.le_t(a: Nat, b: Nat, h: N.Le(a, b)) -> {True{} == Nat.is_le(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+x 0n:
      Empty.absurd({True{} == Nat.is_le(1n+x, 0n) : Bool}, h)
    case 1n+x 1n+y:
      Na.le_t(x, y, h)

# b <= a gives a < b false
def Na.lt_f(a: Nat, b: Nat, h: N.Le(b, a)) -> {False{} == Nat.is_lt(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 1n+x 0n:
      {==}
    case 0n 1n+y:
      Empty.absurd({False{} == Nat.is_lt(0n, 1n+y) : Bool}, h)
    case 1n+x 1n+y:
      Na.lt_f(x, y, h)

# 1 + b <= a gives a <= b false
def Na.le_f(a: Nat, b: Nat, h: N.Le(1n+b, a)) -> {False{} == Nat.is_le(a, b) : Bool}:
  match a b:
    case 0n _:
      Empty.absurd({False{} == Nat.is_le(0n, b) : Bool}, h)
    case 1n+x 0n:
      {==}
    case 1n+x 1n+y:
      Na.le_f(x, y, h)

def Na.lt_succ(a: Nat) -> {True{} == Nat.is_lt(a, 1n+a) : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+x:
      Na.lt_succ(x)

def Bo.or_r(a: Bool, -b: Bool, h: {True{} == b : Bool}) -> {True{} == Bool.or(a, b) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

# a comparison LT gives x < y
def Cm.lt(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), e: {Cmp.is_lt(c) == True{} : Bool}) -> N.Le(1n+x, y):
  match c:
    case LT{}:
      r
    case EQ{}:
      Bo.ft(N.Le(1n+x, y), Equal.sym(Bool, False{}, True{}, e))
    case GT{}:
      Bo.ft(N.Le(1n+x, y), Equal.sym(Bool, False{}, True{}, e))

# x <= y makes the comparison at most EQ
def Cm.le(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(x, y)) -> {True{} == Cmp.is_le(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({True{} == False{} : Bool}, N.not_succ_le(y, N.le_trans(1n+y, x, y, r, h)))

# x < y makes the comparison LT
def Cm.lt_t(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(1n+x, y)) -> {True{} == Cmp.is_lt(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({True{} == False{} : Bool}, N.not_succ_le(x, N.le_rw_r(1n+x, y, x, Equal.sym(Nat, x, y, r), h)))
    case GT{}:
      Empty.absurd({True{} == False{} : Bool}, N.not_succ_le(y, N.le_trans(1n+y, x, y, r, N.weaken(x, y, h))))

# x > y makes the comparison not EQ
def Cm.ne(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(1n+y, x)) -> {False{} == Cmp.is_eq(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(y, N.le_rw_r(1n+y, x, y, r, h)))
    case GT{}:
      {==}

# below M, a U32 has a next one, one more
def U.inc(+a: U32, +M: U32, h: {U32.is_lt(a, M) == True{} : Bool}) -> {U32.to_nat(U32.inc(a)) == 1n+U32.to_nat(a) : Nat}:
  +l = Cm.lt(U32.cmp(a, M), U32.to_nat(a), U32.to_nat(M), N.U32.rel(a, M), h)
  PI.U32.inc_nat(a, Equal.sym(Bool, U32.is_zero(U32.inc(a)), False{}, PM.nz(a, M, l)))

# Cells that may be read
# ----------------------

def In.Jlo(+w: Word(8n)) -> N.Le(89n, U32.to_nat(In.J(w))):
  In.p1(N.Le(89n, U32.to_nat(In.J(w))), In.P(N.Le(1n+U32.to_nat(In.J(w)), 345n), {In.u8(w) == U32.and(U32.sub(In.J(w), 89), 255) : U32}), In.Jb(w))

def In.Jhi(+w: Word(8n)) -> N.Le(1n+U32.to_nat(In.J(w)), 345n):
  In.p1(N.Le(1n+U32.to_nat(In.J(w)), 345n), {In.u8(w) == U32.and(U32.sub(In.J(w), 89), 255) : U32},
    In.p2(N.Le(89n, U32.to_nat(In.J(w))), In.P(N.Le(1n+U32.to_nat(In.J(w)), 345n), {In.u8(w) == U32.and(U32.sub(In.J(w), 89), 255) : U32}), In.Jb(w)))

# a cache cell may not be read
def In.rdJ(+w: Word(8n), +F: U32, +N: Nat, hF: N.Le(345n, U32.to_nat(F))) -> {False{} == In.rd(In.J(w), F, N) : Bool}:
  +tJ = U32.to_nat(In.J(w))
  %Na.lt_f(tJ, 89n, In.Jlo(w)) : {False{} == Bool.or(_, Bool.and(Nat.is_le(U32.to_nat(F), tJ), Nat.is_lt(tJ, N))) : Bool}
  %Na.le_f(U32.to_nat(F), tJ, N.le_trans(1n+tJ, 345n, U32.to_nat(F), In.Jhi(w), hF)) : {False{} == Bool.or(False{}, Bool.and(_, Nat.is_lt(tJ, N))) : Bool}
  {==}

# a cache cell is none of the machine's own
def In.neJ(+w: Word(8n), +i: U32, hi: N.Le(345n, U32.to_nat(i)), e: {In.J(w) == i : U32}) -> Empty:
  +tJ = U32.to_nat(In.J(w))
  N.not_succ_le(tJ, N.le_rw_r(1n+tJ, U32.to_nat(i), tJ, Equal.sym(Nat, tJ, U32.to_nat(i), Equal.cong(U32, Nat, y => U32.to_nat(y), In.J(w), i, e)),
    N.le_trans(1n+tJ, 345n, U32.to_nat(i), In.Jhi(w), hi)))

# the new cell next (numbered N) may not be read yet, but may once taken
def In.rdNew(+i: U32, +F: U32, +N: Nat, eN: {U32.to_nat(i) == N : Nat}, hF: N.Le(89n, U32.to_nat(F)), +hFN: N.Le(U32.to_nat(F), N)) ->
  In.P({False{} == In.rd(i, F, N) : Bool}, {True{} == In.rd(i, F, 1n+N) : Bool}):
  %Equal.sym(Nat, U32.to_nat(i), N, eN) : In.P({False{} == Bool.or(Nat.is_lt(_, 89n), Bool.and(Nat.is_le(U32.to_nat(F), _), Nat.is_lt(_, N))) : Bool},
    {True{} == Bool.or(Nat.is_lt(_, 89n), Bool.and(Nat.is_le(U32.to_nat(F), _), Nat.is_lt(_, 1n+N))) : Bool})
  %Na.lt_f(N, 89n, N.le_trans(89n, U32.to_nat(F), N, hF, hFN)) : In.P({False{} == Bool.or(_, Bool.and(Nat.is_le(U32.to_nat(F), N), Nat.is_lt(N, N))) : Bool},
    {True{} == Bool.or(_, Bool.and(Nat.is_le(U32.to_nat(F), N), Nat.is_lt(N, 1n+N))) : Bool})
  %Na.le_t(U32.to_nat(F), N, hFN) : In.P({False{} == Bool.or(False{}, Bool.and(_, Nat.is_lt(N, N))) : Bool},
    {True{} == Bool.or(False{}, Bool.and(_, Nat.is_lt(N, 1n+N))) : Bool})
  %Na.lt_f(N, N, N.le_refl(N)) : In.P({False{} == Bool.or(False{}, Bool.and(True{}, _)) : Bool},
    {True{} == Bool.or(False{}, Bool.and(True{}, Nat.is_lt(N, 1n+N))) : Bool})
  ({==}, Na.lt_succ(N))

# the cache cell of a byte is one of the image's
def In.cellJ(+w: Word(8n), +K: U32, +F: U32, +nx: U32, hK: N.Le(344n, U32.to_nat(K))) -> {True{} == C.Cir.is_cell(In.J(w), K, F, nx) : Bool}:
  +j = In.J(w)
  +tJ = U32.to_nat(j)
  %Cm.ne(U32.cmp(j, 0), tJ, U32.to_nat(0), N.U32.rel(j, 0), N.le_trans(1n, 89n, tJ, Unit{}, In.Jlo(w))) :
    {True{} == Bool.or(Bool.and(Bool.not(_), U32.is_le(j, K)), Bool.and(U32.is_le(F, j), U32.is_lt(j, nx))) : Bool}
  %Cm.le(U32.cmp(j, K), tJ, U32.to_nat(K), N.U32.rel(j, K), N.le_trans(tJ, 344n, U32.to_nat(K), In.Jhi(w), hK)) :
    {True{} == Bool.or(Bool.and(True{}, _), Bool.and(U32.is_le(F, j), U32.is_lt(j, nx))) : Bool}
  {==}

# the new cell next is one the machine took
def In.cellNew(+next: U32, +K: U32, +F: U32, lt: In.lt(next), hFN: N.Le(U32.to_nat(F), U32.to_nat(next))) ->
  {True{} == C.Cir.is_cell(next, K, F, U32.inc(next)) : Bool}:
  +tN = U32.to_nat(next)
  Bo.or_r(Bool.and(Bool.not(U32.is_zero(next)), U32.is_le(next, K)), Bool.and(U32.is_le(F, next), U32.is_lt(next, U32.inc(next))),
    Bo.and_i(U32.is_le(F, next), U32.is_lt(next, U32.inc(next)),
      Cm.le(U32.cmp(F, next), U32.to_nat(F), tN, N.U32.rel(F, next), hFN),
      Cm.lt_t(U32.cmp(next, U32.inc(next)), tN, U32.to_nat(U32.inc(next)), N.U32.rel(next, U32.inc(next)),
        N.le_rw_r(1n+tN, 1n+tN, U32.to_nat(U32.inc(next)), Equal.sym(Nat, U32.to_nat(U32.inc(next)), 1n+tN, U.inc(next, 214748364, lt)), N.le_refl(1n+tN)))))

# The cache's entries
# -------------------

def En.fr.go(+fc: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +v: U32, +t: C.Term, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +i: U32, +x: C.Cir.Cell,
  +hi: {False{} == In.rd(i, F, N) : Bool}, e: In.Or<{0 == v : U32}, In.St(fc, m, F, N, v, t, ks, img)>) ->
  In.Or<{0 == v : U32}, In.St(fc, C.Cir.Cells.set(m, i, x), F, N, v, t, ks, img)>:
  match e:
    case In.Or.l{z}:
      In.Or.l{z}
    case In.Or.r{s}:
      In.Or.r{St.fr(fc, m, F, N, v, t, ks, img, i, x, hi, s)}

# a cell the machine takes keeps every entry
def En.fr(+fc: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +w: Word(8n), +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +i: U32, +x: C.Cir.Cell,
  +hi: {False{} == In.rd(i, F, N) : Bool}, hb: N.Le(345n, U32.to_nat(i)), e: In.En(fc, m, F, N, w, ks, img)) ->
  In.En(fc, C.Cir.Cells.set(m, i, x), F, N, w, ks, img):
  +ms = C.Cir.Cells.set(m, i, x)
  %Cl.get_other(m, In.J(w), i, x, k => In.neJ(w, i, hb, k)) :
    In.Or<{0 == C.Cir.Cell.get(2n, _) : U32}, In.St(fc, ms, F, N, C.Cir.Cell.get(2n, _), C.Program.cell.of(In.u8(w)), ks, img)>
  En.fr.go(fc, m, F, N, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, In.J(w))), C.Program.cell.of(In.u8(w)), ks, img, i, x, hi, e)

def En.up(+fc: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +w: Word(8n), +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, e: In.En(fc, m, F, N, w, ks, img)) ->
  In.En(fc, m, F, 1n+N, w, ks, img):
  match e:
    case In.Or.l{z}:
      In.Or.l{z}
    case In.Or.r{s}:
      In.Or.r{St.up(fc, m, F, N, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, In.J(w))), C.Program.cell.of(In.u8(w)), ks, img, s)}

def CI.fr(n: Nat, +bs: List<&2, Bool>, +fc: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +i: U32,
  +x: C.Cir.Cell, +hi: {False{} == In.rd(i, F, N) : Bool}, +hb: N.Le(345n, U32.to_nat(i)), ci: In.CI(n, bs, fc, m, F, N, ks, img)) ->
  In.CI(n, bs, fc, C.Cir.Cells.set(m, i, x), F, N, ks, img):
  match n:
    case 0n:
      En.fr(fc, m, F, N, In.wl(bs), ks, img, i, x, hi, hb, ci)
    case 1n+(+p):
      (a, b) = ci
      (CI.fr(p, Con{False{}, bs}, fc, m, F, N, ks, img, i, x, hi, hb, a), CI.fr(p, Con{True{}, bs}, fc, m, F, N, ks, img, i, x, hi, hb, b))

def CI.up(n: Nat, +bs: List<&2, Bool>, +fc: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  ci: In.CI(n, bs, fc, m, F, N, ks, img)) -> In.CI(n, bs, fc, m, F, 1n+N, ks, img):
  match n:
    case 0n:
      En.up(fc, m, F, N, In.wl(bs), ks, img, ci)
    case 1n+(+p):
      (a, b) = ci
      (CI.up(p, Con{False{}, bs}, fc, m, F, N, ks, img, a), CI.up(p, Con{True{}, bs}, fc, m, F, N, ks, img, b))

def CI.get(n: Nat, +bs: List<&2, Bool>, +fc: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  w: Word(n), ci: In.CI(n, bs, fc, m, F, N, ks, img)) -> In.En(fc, m, F, N, In.wl(In.push(n, w, bs)), ks, img):
  match n:
    case 0n:
      match w:
        case WNil{}:
          ci
    case 1n+(+p):
      match w:
        case WCon{False{}, t}:
          (a, b) = ci
          CI.get(p, Con{False{}, bs}, fc, m, F, N, ks, img, t, a)
        case WCon{True{}, t}:
          (a, b) = ci
          CI.get(p, Con{True{}, bs}, fc, m, F, N, ks, img, t, b)

# field 2 of a cell, once set
def Cl.f2(c: C.Cir.Cell, +v: U32) -> {v == C.Cir.Cell.get(2n, C.Cir.Cell.set(2n, c, v)) : U32}:
  match c:
    case C.Cir.Cell{a, b, x, y, z}:
      {==}

# the store of the cache: the entry of w8 gets the cell v
def En.st.go(b: Bool, +fc: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +w: Word(8n), +w8: Word(8n), +v: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +hF: N.Le(345n, U32.to_nat(F)), eb: {b == In.weq(8n, w, w8) : Bool},
  sv: In.St(fc, C.Cir.Cells.set(m, In.J(w8), C.Cir.Cell.set(2n, C.Cir.Cells.get(m, In.J(w8)), v)), F, N, v, C.Program.cell.of(In.u8(w8)), ks, img),
  e: In.En(fc, m, F, N, w, ks, img)) ->
  In.En(fc, C.Cir.Cells.set(m, In.J(w8), C.Cir.Cell.set(2n, C.Cir.Cells.get(m, In.J(w8)), v)), F, N, w, ks, img):
  match b:
    case True{}:
      %Equal.sym(Word(8n), w, w8, In.weq_t(8n, w, w8, eb)) : In.En(fc, C.Cir.Cells.set(m, In.J(w8), C.Cir.Cell.set(2n, C.Cir.Cells.get(m, In.J(w8)), v)), F, N, _, ks, img)
      %Equal.sym(C.Cir.Cell, C.Cir.Cells.get(C.Cir.Cells.set(m, In.J(w8), C.Cir.Cell.set(2n, C.Cir.Cells.get(m, In.J(w8)), v)), In.J(w8)), C.Cir.Cell.set(2n, C.Cir.Cells.get(m, In.J(w8)), v), Cl.get_set(m, In.J(w8), C.Cir.Cell.set(2n, C.Cir.Cells.get(m, In.J(w8)), v))) :
        In.Or<{0 == C.Cir.Cell.get(2n, _) : U32}, In.St(fc, C.Cir.Cells.set(m, In.J(w8), C.Cir.Cell.set(2n, C.Cir.Cells.get(m, In.J(w8)), v)), F, N, C.Cir.Cell.get(2n, _), C.Program.cell.of(In.u8(w8)), ks, img)>
      %Cl.f2(C.Cir.Cells.get(m, In.J(w8)), v) :
        In.Or<{0 == _ : U32}, In.St(fc, C.Cir.Cells.set(m, In.J(w8), C.Cir.Cell.set(2n, C.Cir.Cells.get(m, In.J(w8)), v)), F, N, _, C.Program.cell.of(In.u8(w8)), ks, img)>
      In.Or.r{sv}
    case False{}:
      %Cl.get_other(m, In.J(w), In.J(w8), C.Cir.Cell.set(2n, C.Cir.Cells.get(m, In.J(w8)), v), k => In.weq_f(8n, w, w8, eb, In.J_inj(w, w8, k))) :
        In.Or<{0 == C.Cir.Cell.get(2n, _) : U32}, In.St(fc, C.Cir.Cells.set(m, In.J(w8), C.Cir.Cell.set(2n, C.Cir.Cells.get(m, In.J(w8)), v)), F, N, C.Cir.Cell.get(2n, _), C.Program.cell.of(In.u8(w)), ks, img)>
      En.fr.go(fc, m, F, N, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, In.J(w))), C.Program.cell.of(In.u8(w)), ks, img, In.J(w8), C.Cir.Cell.set(2n, C.Cir.Cells.get(m, In.J(w8)), v),
        In.rdJ(w8, F, N, hF), e)

def CI.st(n: Nat, +bs: List<&2, Bool>, +fc: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +w8: Word(8n), +v: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +hF: N.Le(345n, U32.to_nat(F)),
  +sv: In.St(fc, C.Cir.Cells.set(m, In.J(w8), C.Cir.Cell.set(2n, C.Cir.Cells.get(m, In.J(w8)), v)), F, N, v, C.Program.cell.of(In.u8(w8)), ks, img),
  ci: In.CI(n, bs, fc, m, F, N, ks, img)) ->
  In.CI(n, bs, fc, C.Cir.Cells.set(m, In.J(w8), C.Cir.Cell.set(2n, C.Cir.Cells.get(m, In.J(w8)), v)), F, N, ks, img):
  match n:
    case 0n:
      En.st.go(In.weq(8n, In.wl(bs), w8), fc, m, F, N, In.wl(bs), w8, v, ks, img, hF, {==}, sv, ci)
    case 1n+(+p):
      (a, b) = ci
      (CI.st(p, Con{False{}, bs}, fc, m, F, N, w8, v, ks, img, hF, sv, a), CI.st(p, Con{True{}, bs}, fc, m, F, N, w8, v, ks, img, hF, sv, b))

# The image's cells that the machine points to
# ----------------------------------------------

# the labels (), Con, U32, WCon (cells 1, 3, 4, 6), Nil (12), True (13), False (14), the
# 24 False bits (16) and the Ref of main (88)
def In.Im(+f0: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>) -> Data:
  In.P(In.St(f0, m, F, N, 1, C.Term.Lab{C.Program.name.unit()}, ks, img), In.P(In.St(f0, m, F, N, 3, C.Term.Lab{C.Program.name.con()}, ks, img), In.P(In.St(f0, m, F, N, 4, C.Term.Lab{C.Program.name.u32()}, ks, img), In.P(In.St(f0, m, F, N, 6, C.Term.Lab{C.Program.name.wcon()}, ks, img), In.P(In.St(f0, m, F, N, 12, C.Program.bytes([]), ks, img), In.P(In.St(f0, m, F, N, 13, C.Program.bit(True{}), ks, img), In.P(In.St(f0, m, F, N, 14, C.Program.bit(False{}), ks, img), In.P(In.St(f0, m, F, N, 16, C.Program.word(24n, Word.zero(24n)), ks, img), In.St(f0, m, F, N, 88, C.Term.Ref{C.Program.name.main()}, ks, img)))))))))

def Im.fr(+f0: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +i: U32, +x: C.Cir.Cell,
  +hi: {False{} == In.rd(i, F, N) : Bool}, im: In.Im(f0, m, F, N, ks, img)) -> In.Im(f0, C.Cir.Cells.set(m, i, x), F, N, ks, img):
  (s0, r0) = im
  (s1, r1) = r0
  (s2, r2) = r1
  (s3, r3) = r2
  (s4, r4) = r3
  (s5, r5) = r4
  (s6, r6) = r5
  (s7, r7) = r6
  (St.fr(f0, m, F, N, 1, C.Term.Lab{C.Program.name.unit()}, ks, img, i, x, hi, s0), (St.fr(f0, m, F, N, 3, C.Term.Lab{C.Program.name.con()}, ks, img, i, x, hi, s1), (St.fr(f0, m, F, N, 4, C.Term.Lab{C.Program.name.u32()}, ks, img, i, x, hi, s2), (St.fr(f0, m, F, N, 6, C.Term.Lab{C.Program.name.wcon()}, ks, img, i, x, hi, s3), (St.fr(f0, m, F, N, 12, C.Program.bytes([]), ks, img, i, x, hi, s4), (St.fr(f0, m, F, N, 13, C.Program.bit(True{}), ks, img, i, x, hi, s5), (St.fr(f0, m, F, N, 14, C.Program.bit(False{}), ks, img, i, x, hi, s6), (St.fr(f0, m, F, N, 16, C.Program.word(24n, Word.zero(24n)), ks, img, i, x, hi, s7), St.fr(f0, m, F, N, 88, C.Term.Ref{C.Program.name.main()}, ks, img, i, x, hi, r7)))))))))

def Im.up(+f0: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  im: In.Im(f0, m, F, N, ks, img)) -> In.Im(f0, m, F, 1n+N, ks, img):
  (s0, r0) = im
  (s1, r1) = r0
  (s2, r2) = r1
  (s3, r3) = r2
  (s4, r4) = r3
  (s5, r5) = r4
  (s6, r6) = r5
  (s7, r7) = r6
  (St.up(f0, m, F, N, 1, C.Term.Lab{C.Program.name.unit()}, ks, img, s0), (St.up(f0, m, F, N, 3, C.Term.Lab{C.Program.name.con()}, ks, img, s1), (St.up(f0, m, F, N, 4, C.Term.Lab{C.Program.name.u32()}, ks, img, s2), (St.up(f0, m, F, N, 6, C.Term.Lab{C.Program.name.wcon()}, ks, img, s3), (St.up(f0, m, F, N, 12, C.Program.bytes([]), ks, img, s4), (St.up(f0, m, F, N, 13, C.Program.bit(True{}), ks, img, s5), (St.up(f0, m, F, N, 14, C.Program.bit(False{}), ks, img, s6), (St.up(f0, m, F, N, 16, C.Program.word(24n, Word.zero(24n)), ks, img, s7), St.up(f0, m, F, N, 88, C.Term.Ref{C.Program.name.main()}, ks, img, r7)))))))))

def Im.g1(+f0: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  im: In.Im(f0, m, F, N, ks, img)) -> In.St(f0, m, F, N, 1, C.Term.Lab{C.Program.name.unit()}, ks, img):
  (s0, r0) = im
  (s1, r1) = r0
  (s2, r2) = r1
  (s3, r3) = r2
  (s4, r4) = r3
  (s5, r5) = r4
  (s6, r6) = r5
  (s7, r7) = r6
  s0

def Im.g3(+f0: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  im: In.Im(f0, m, F, N, ks, img)) -> In.St(f0, m, F, N, 3, C.Term.Lab{C.Program.name.con()}, ks, img):
  (s0, r0) = im
  (s1, r1) = r0
  (s2, r2) = r1
  (s3, r3) = r2
  (s4, r4) = r3
  (s5, r5) = r4
  (s6, r6) = r5
  (s7, r7) = r6
  s1

def Im.g4(+f0: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  im: In.Im(f0, m, F, N, ks, img)) -> In.St(f0, m, F, N, 4, C.Term.Lab{C.Program.name.u32()}, ks, img):
  (s0, r0) = im
  (s1, r1) = r0
  (s2, r2) = r1
  (s3, r3) = r2
  (s4, r4) = r3
  (s5, r5) = r4
  (s6, r6) = r5
  (s7, r7) = r6
  s2

def Im.g6(+f0: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  im: In.Im(f0, m, F, N, ks, img)) -> In.St(f0, m, F, N, 6, C.Term.Lab{C.Program.name.wcon()}, ks, img):
  (s0, r0) = im
  (s1, r1) = r0
  (s2, r2) = r1
  (s3, r3) = r2
  (s4, r4) = r3
  (s5, r5) = r4
  (s6, r6) = r5
  (s7, r7) = r6
  s3

def Im.g12(+f0: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  im: In.Im(f0, m, F, N, ks, img)) -> In.St(f0, m, F, N, 12, C.Program.bytes([]), ks, img):
  (s0, r0) = im
  (s1, r1) = r0
  (s2, r2) = r1
  (s3, r3) = r2
  (s4, r4) = r3
  (s5, r5) = r4
  (s6, r6) = r5
  (s7, r7) = r6
  s4

def Im.g13(+f0: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  im: In.Im(f0, m, F, N, ks, img)) -> In.St(f0, m, F, N, 13, C.Program.bit(True{}), ks, img):
  (s0, r0) = im
  (s1, r1) = r0
  (s2, r2) = r1
  (s3, r3) = r2
  (s4, r4) = r3
  (s5, r5) = r4
  (s6, r6) = r5
  (s7, r7) = r6
  s5

def Im.g14(+f0: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  im: In.Im(f0, m, F, N, ks, img)) -> In.St(f0, m, F, N, 14, C.Program.bit(False{}), ks, img):
  (s0, r0) = im
  (s1, r1) = r0
  (s2, r2) = r1
  (s3, r3) = r2
  (s4, r4) = r3
  (s5, r5) = r4
  (s6, r6) = r5
  (s7, r7) = r6
  s6

def Im.g16(+f0: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  im: In.Im(f0, m, F, N, ks, img)) -> In.St(f0, m, F, N, 16, C.Program.word(24n, Word.zero(24n)), ks, img):
  (s0, r0) = im
  (s1, r1) = r0
  (s2, r2) = r1
  (s3, r3) = r2
  (s4, r4) = r3
  (s5, r5) = r4
  (s6, r6) = r5
  (s7, r7) = r6
  s7

def Im.g88(+f0: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  im: In.Im(f0, m, F, N, ks, img)) -> In.St(f0, m, F, N, 88, C.Term.Ref{C.Program.name.main()}, ks, img):
  (s0, r0) = im
  (s1, r1) = r0
  (s2, r2) = r1
  (s3, r3) = r2
  (s4, r4) = r3
  (s5, r5) = r4
  (s6, r6) = r5
  (s7, r7) = r6
  r7

# The facts of a state
# --------------------

# next is numbered N, from F, and the image's cells and the cache stand for
# their terms
def In.Fa(+m: C.Cir.Cells, +next: U32, +N: Nat, +F: U32, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>) -> Data:
  In.P({U32.to_nat(next) == N : Nat}, In.P(N.Le(U32.to_nat(F), N), In.P(In.Im(f0, m, F, N, ks, img), In.CI(8n, [], fc, m, F, N, ks, img))))

# the new cell may not be read yet
def Fa.hi(+m: C.Cir.Cells, +next: U32, +N: Nat, +F: U32, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  hF: N.Le(345n, U32.to_nat(F)), fa: In.Fa(m, next, N, F, f0, fc, ks, img)) -> {False{} == In.rd(next, F, N) : Bool}:
  (eN, r) = fa
  (hFN, r2) = r
  In.p1({False{} == In.rd(next, F, N) : Bool}, {True{} == In.rd(next, F, 1n+N) : Bool},
    In.rdNew(next, F, N, eN, N.le_trans(89n, 345n, U32.to_nat(F), Unit{}, hF), hFN))

# and may be once taken
def Fa.hr(+m: C.Cir.Cells, +next: U32, +N: Nat, +F: U32, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  hF: N.Le(345n, U32.to_nat(F)), fa: In.Fa(m, next, N, F, f0, fc, ks, img)) -> {True{} == In.rd(next, F, 1n+N) : Bool}:
  (eN, r) = fa
  (hFN, r2) = r
  In.p2({False{} == In.rd(next, F, N) : Bool}, {True{} == In.rd(next, F, 1n+N) : Bool},
    In.rdNew(next, F, N, eN, N.le_trans(89n, 345n, U32.to_nat(F), Unit{}, hF), hFN))

def Fa.lF(+m: C.Cir.Cells, +next: U32, +N: Nat, +F: U32, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  fa: In.Fa(m, next, N, F, f0, fc, ks, img)) -> N.Le(U32.to_nat(F), U32.to_nat(next)):
  (eN, r) = fa
  (hFN, r2) = r
  N.le_rw_r(U32.to_nat(F), N, U32.to_nat(next), Equal.sym(Nat, U32.to_nat(next), N, eN), hFN)

def Fa.im(+m: C.Cir.Cells, +next: U32, +N: Nat, +F: U32, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  fa: In.Fa(m, next, N, F, f0, fc, ks, img)) -> In.Im(f0, m, F, N, ks, img):
  (eN, r) = fa
  (hFN, r2) = r
  (im, ci) = r2
  im

def Fa.ci(+m: C.Cir.Cells, +next: U32, +N: Nat, +F: U32, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  fa: In.Fa(m, next, N, F, f0, fc, ks, img)) -> In.CI(8n, [], fc, m, F, N, ks, img):
  (eN, r) = fa
  (hFN, r2) = r
  (im, ci) = r2
  ci

def Fa.eN(+m: C.Cir.Cells, +next: U32, +N: Nat, +F: U32, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  fa: In.Fa(m, next, N, F, f0, fc, ks, img)) -> {U32.to_nat(next) == N : Nat}:
  (eN, r) = fa
  eN

def Fa.hFN(+m: C.Cir.Cells, +next: U32, +N: Nat, +F: U32, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  fa: In.Fa(m, next, N, F, f0, fc, ks, img)) -> N.Le(U32.to_nat(F), N):
  (eN, r) = fa
  (hFN, r2) = r
  hFN

# the facts once the cell next, set to x, is taken
def Fa.step(+m: C.Cir.Cells, +next: U32, +N: Nat, +F: U32, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +x: C.Cir.Cell, lt: In.lt(next), +hF: N.Le(345n, U32.to_nat(F)), +fa: In.Fa(m, next, N, F, f0, fc, ks, img)) ->
  In.Fa(C.Cir.Cells.set(m, next, x), U32.inc(next), 1n+N, F, f0, fc, ks, img):
  +hi = Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa)
  +lF = Fa.lF(m, next, N, F, f0, fc, ks, img, fa)
  +eN = Fa.eN(m, next, N, F, f0, fc, ks, img, fa)
  +hFN = Fa.hFN(m, next, N, F, f0, fc, ks, img, fa)
  +im = Fa.im(m, next, N, F, f0, fc, ks, img, fa)
  +ci = Fa.ci(m, next, N, F, f0, fc, ks, img, fa)
  (Equal.trans(Nat, U32.to_nat(U32.inc(next)), 1n+U32.to_nat(next), 1n+N, U.inc(next, 214748364, lt), Equal.cong(Nat, Nat, z => 1n+z, U32.to_nat(next), N, eN)),
   (N.le_succ(U32.to_nat(F), N, hFN),
    (Im.up(f0, C.Cir.Cells.set(m, next, x), F, N, ks, img, Im.fr(f0, m, F, N, ks, img, next, x, hi, im)),
     CI.up(8n, [], fc, C.Cir.Cells.set(m, next, x), F, N, ks, img,
       CI.fr(8n, [], fc, m, F, N, ks, img, next, x, hi, N.le_trans(345n, U32.to_nat(F), U32.to_nat(next), hF, lF), ci)))))

# a term framed over a new cell
def St.step(+f: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +c: U32, +t: C.Term, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +i: U32, +x: C.Cir.Cell, +hi: {False{} == In.rd(i, F, N) : Bool}, s: In.St(f, m, F, N, c, t, ks, img)) ->
  In.St(f, C.Cir.Cells.set(m, i, x), F, 1n+N, c, t, ks, img):
  St.up(f, C.Cir.Cells.set(m, i, x), F, N, c, t, ks, img, St.fr(f, m, F, N, c, t, ks, img, i, x, hi, s))

# the cells once the cache's entry of w8 gets v
def In.cs(+m: C.Cir.Cells, +w8: Word(8n), +v: U32) -> C.Cir.Cells:
  C.Cir.Cells.set(m, In.J(w8), C.Cir.Cell.set(2n, C.Cir.Cells.get(m, In.J(w8)), v))

# the facts once the cache's entry of w8 gets v, which stands for its U32
def Fa.cs(+m: C.Cir.Cells, +next: U32, +N: Nat, +F: U32, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +w8: Word(8n), +v: U32, +hF: N.Le(345n, U32.to_nat(F)), sv: In.St(fc, m, F, N, v, C.Program.cell.of(In.u8(w8)), ks, img),
  +fa: In.Fa(m, next, N, F, f0, fc, ks, img)) -> In.Fa(In.cs(m, w8, v), next, N, F, f0, fc, ks, img):
  +x = C.Cir.Cell.set(2n, C.Cir.Cells.get(m, In.J(w8)), v)
  +hi = In.rdJ(w8, F, N, hF)
  (Fa.eN(m, next, N, F, f0, fc, ks, img, fa),
   (Fa.hFN(m, next, N, F, f0, fc, ks, img, fa),
    (Im.fr(f0, m, F, N, ks, img, In.J(w8), x, hi, Fa.im(m, next, N, F, f0, fc, ks, img, fa)),
     CI.st(8n, [], fc, m, F, N, w8, v, ks, img, hF, St.fr(fc, m, F, N, v, C.Program.cell.of(In.u8(w8)), ks, img, In.J(w8), x, hi, sv),
       Fa.ci(m, next, N, F, f0, fc, ks, img, fa)))))

# The registers
# -------------

# the registers of M.input: focus, ii, ib, il, iu, iw, ij, t1 and t2, the
# others 0
def In.R(+fo: U32, +ii: U32, +ib: U32, +il: U32, +iu: U32, +iw: U32, +ij: U32, +t1: U32, +t2: U32) -> List<&2, U32>:
  Con{fo, List.append(&2, U32, List.replicate(U32, 48n, 0), [ii, ib, il, iu, iw, ij, 0, 0, 0, 0, 0, 0, 0, t1, t2])}

def In.R0() -> {List.replicate(U32, C.Mach.regs(), 0) == In.R(0, 0, 0, 0, 0, 0, 0, 0, 0) : List<&2, U32>}:
  {==}

# Bits
# ----

def In.b0(y: U32) -> Bool:
  match y:
    case U32{WCon{b, _}}:
      b

def Wd.and_zero(n: Nat, t: Word(n)) -> {Word.zero(n) == Word.and(n, t, Word.zero(n)) : Word(n)}:
  match n:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+(+p):
      match t:
        case WCon{True{}, +r}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.zero(p), Word.and(p, r, Word.zero(p)), Wd.and_zero(p, r))
        case WCon{False{}, +r}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.zero(p), Word.and(p, r, Word.zero(p)), Wd.and_zero(p, r))

# M.pick of the low bit of y: 13 (True) or 14 (False)
def In.pv(y: U32) -> {Bool.pick(U32, In.b0(y), 13, 14) == U32.or(U32.and(13, U32.sub(0, U32.and(y, 1))), U32.and(14, U32.sub(U32.and(y, 1), 1))) : U32}:
  match y:
    case U32{WCon{True{}, +t}}:
      %Wd.and_zero(31n, t) : {13 == U32.or(U32.and(13, U32.sub(0, U32{WCon{True{}, _}})), U32.and(14, U32.sub(U32{WCon{True{}, _}}, 1))) : U32}
      {==}
    case U32{WCon{False{}, +t}}:
      %Wd.and_zero(31n, t) : {14 == U32.or(U32.and(13, U32.sub(0, U32{WCon{False{}, _}})), U32.and(14, U32.sub(U32{WCon{False{}, _}}, 1))) : U32}
      {==}

# the cell of the bit b in the image
def Im.bit(b: Bool, +f0: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  im: In.Im(f0, m, F, N, ks, img)) -> In.St(f0, m, F, N, Bool.pick(U32, b, 13, 14), C.Program.bit(b), ks, img):
  match b:
    case True{}:
      Im.g13(f0, m, F, N, ks, img, im)
    case False{}:
      Im.g14(f0, m, F, N, ks, img, im)

# Loops
# -----

# a round of a while whose condition holds
def In.loop(+f: Nat, +c: C.Cir.Expr, +body: C.Cir.Stmt, +st: C.Cir.State, -Q: C.Cir.State -> Type, -R: C.Cir.State -> Type,
  ev: {Some{1} == C.Cir.eval(c, st) : Maybe<&2, U32>}, h: In.Ok(C.Cir.exec(f, body, st), Q),
  g: @s: C.Cir.State -> Q(s) -> In.Ok(C.Cir.exec(f, C.Cir.Stmt.while{c, body}, s), R)) ->
  In.Ok(C.Cir.exec(1n+f, C.Cir.Stmt.while{c, body}, st), R):
  %ev : In.Ok(C.Cir.exec.if(_, u => C.Cir.exec.then(C.Cir.exec(f, body, st), t => C.Cir.exec(f, C.Cir.Stmt.while{c, body}, t)), u => C.Cir.Out.next{st}), R)
  In.then(C.Cir.exec(f, body, st), t => C.Cir.exec(f, C.Cir.Stmt.while{c, body}, t), Q, R, h, g)

# the end of a while
def In.loop.end(+f: Nat, +c: C.Cir.Expr, +body: C.Cir.Stmt, +st: C.Cir.State, -R: C.Cir.State -> Type,
  ev: {Some{0} == C.Cir.eval(c, st) : Maybe<&2, U32>}, k: R(st)) -> In.Ok(C.Cir.exec(1n+f, C.Cir.Stmt.while{c, body}, st), R):
  %ev : In.Ok(C.Cir.exec.if(_, u => C.Cir.exec.then(C.Cir.exec(f, body, st), t => C.Cir.exec(f, C.Cir.Stmt.while{c, body}, t)), u => C.Cir.Out.next{st}), R)
  k

# Runs, then more
# ---------------

# s runs from st with the fuel f, then k: the run ends with a state of which
# R holds, or out of memory
def In.Go(f: Nat, s: C.Cir.Stmt, st: C.Cir.State, k: C.Cir.State -> C.Cir.Out, R: C.Cir.State -> Type) -> Type:
  In.Ok(C.Cir.exec.then(C.Cir.exec(f, s, st), k), R)

# a run, then k1, then k2, regrouped
def In.assoc(o: C.Cir.Out, -k1: C.Cir.State -> C.Cir.Out, -k2: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type,
  h: In.Ok(C.Cir.exec.then(o, t => C.Cir.exec.then(k1(t), k2)), R)) -> In.Ok(C.Cir.exec.then(C.Cir.exec.then(o, k1), k2), R):
  match o:
    case C.Cir.Out.next{st}:
      h
    case C.Cir.Out.halt{s, st}:
      h
    case C.Cir.Out.out_of_memory{}:
      h
    case C.Cir.Out.trap{}:
      h
    case C.Cir.Out.not_done{}:
      h

# a then b
def In.sq(+f: Nat, +a: C.Cir.Stmt, -b: C.Cir.Stmt, +st: C.Cir.State, -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type,
  h: In.Go(1n+f, a, st, t => C.Cir.exec.then(C.Cir.exec(1n+f, b, t), k), R)) -> In.Go(1n+f, C.Cir.Stmt.seq{a, b}, st, k, R):
  In.assoc(C.Cir.exec(1n+f, a, st), t => C.Cir.exec(1n+f, b, t), k, R, h)

# nothing
def In.nop(-f: Nat, -st: C.Cir.State, -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type, h: In.Ok(k(st), R)) ->
  In.Go(1n+f, C.Cir.Stmt.nop{}, st, k, R):
  h

# register r gets the value v of e
def In.set(+f: Nat, +r: Nat, -e: C.Cir.Expr, +regs: List<&2, U32>, +m: C.Cir.Cells, +next: U32, +F: U32, +K: U32, +pg: U32, +L: U32,
  +I: List<&2, U32>, +v: U32, ev: {Some{v} == C.Cir.eval(e, In.S(regs, m, next, F, K, pg, L, I)) : Maybe<&2, U32>},
  rl: {True{} == Nat.is_lt(r, List.length(&2, U32, regs)) : Bool}, -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type,
  h: In.Ok(k(In.S(List.set(&2, U32, regs, r, v), m, next, F, K, pg, L, I)), R)) ->
  In.Go(1n+f, C.Cir.Stmt.set{r, e}, In.S(regs, m, next, F, K, pg, L, I), k, R):
  +st = In.S(regs, m, next, F, K, pg, L, I)
  %ev : In.Ok(C.Cir.exec.then(C.Cir.exec.set(r, _, st), k), R)
  %rl : In.Ok(C.Cir.exec.then(C.Cir.exec.set.of(C.Cir.regs.set.if(_, regs, r, v), st), k), R)
  h

# field kf of the cell i, the value of c, gets the value x of v
def In.str(+f: Nat, +kf: Nat, -c: C.Cir.Expr, -v: C.Cir.Expr, +regs: List<&2, U32>, +m: C.Cir.Cells, +next: U32, +F: U32, +K: U32, +pg: U32,
  +L: U32, +I: List<&2, U32>, +i: U32, +x: U32,
  evc: {Some{i} == C.Cir.eval(c, In.S(regs, m, next, F, K, pg, L, I)) : Maybe<&2, U32>},
  evv: {Some{x} == C.Cir.eval(v, In.S(regs, m, next, F, K, pg, L, I)) : Maybe<&2, U32>},
  ec: {True{} == C.Cir.is_cell(i, K, F, next) : Bool}, -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type,
  h: In.Ok(k(In.S(regs, C.Cir.Cells.set(m, i, C.Cir.Cell.set(kf, C.Cir.Cells.get(m, i), x)), next, F, K, pg, L, I)), R)) ->
  In.Go(1n+f, C.Cir.Stmt.store{kf, c, v}, In.S(regs, m, next, F, K, pg, L, I), k, R):
  +st = In.S(regs, m, next, F, K, pg, L, I)
  %evc : In.Ok(C.Cir.exec.then(C.Cir.exec.store(kf, _, C.Cir.eval(v, st), st), k), R)
  %evv : In.Ok(C.Cir.exec.then(C.Cir.exec.store(kf, Some{i}, _, st), k), R)
  %ec : In.Ok(C.Cir.exec.then(C.Cir.exec.store.if(_, kf, i, x, st), k), R)
  h

# a round of a while whose condition holds
def In.wh(+f: Nat, +c: C.Cir.Expr, +body: C.Cir.Stmt, +st: C.Cir.State, -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type,
  ev: {Some{1} == C.Cir.eval(c, st) : Maybe<&2, U32>},
  h: In.Go(f, body, st, t => C.Cir.exec.then(C.Cir.exec(f, C.Cir.Stmt.while{c, body}, t), k), R)) ->
  In.Go(1n+f, C.Cir.Stmt.while{c, body}, st, k, R):
  %ev : In.Ok(C.Cir.exec.then(C.Cir.exec.if(_, u => C.Cir.exec.then(C.Cir.exec(f, body, st), t => C.Cir.exec(f, C.Cir.Stmt.while{c, body}, t)),
    u => C.Cir.Out.next{st}), k), R)
  In.assoc(C.Cir.exec(f, body, st), t => C.Cir.exec(f, C.Cir.Stmt.while{c, body}, t), k, R, h)

# the end of a while
def In.wh.end(+f: Nat, +c: C.Cir.Expr, +body: C.Cir.Stmt, +st: C.Cir.State, -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type,
  ev: {Some{0} == C.Cir.eval(c, st) : Maybe<&2, U32>}, h: In.Ok(k(st), R)) -> In.Go(1n+f, C.Cir.Stmt.while{c, body}, st, k, R):
  %ev : In.Ok(C.Cir.exec.then(C.Cir.exec.if(_, u => C.Cir.exec.then(C.Cir.exec(f, body, st), t => C.Cir.exec(f, C.Cir.Stmt.while{c, body}, t)),
    u => C.Cir.Out.next{st}), k), R)
  h

# if c then t else e, when c is not 0
def In.ifT(+f: Nat, +c: C.Cir.Expr, -t: C.Cir.Stmt, -e: C.Cir.Stmt, +st: C.Cir.State, +x: U32,
  ev: {Some{x} == C.Cir.eval(c, st) : Maybe<&2, U32>}, ez: {False{} == U32.is_zero(x) : Bool},
  -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type, h: In.Go(1n+f, t, st, k, R)) -> In.Go(1n+f, C.Cir.Stmt.if{c, t, e}, st, k, R):
  %ev : In.Ok(C.Cir.exec.then(C.Cir.exec.if(_, u => C.Cir.exec(1n+f, t, st), u => C.Cir.exec(1n+f, e, st)), k), R)
  %ez : In.Ok(C.Cir.exec.then(C.Cir.exec.if.of(_, u => C.Cir.exec(1n+f, t, st), u => C.Cir.exec(1n+f, e, st)), k), R)
  h

# if c then t else e, when c is 0
def In.ifF(+f: Nat, +c: C.Cir.Expr, -t: C.Cir.Stmt, -e: C.Cir.Stmt, +st: C.Cir.State, +x: U32,
  ev: {Some{x} == C.Cir.eval(c, st) : Maybe<&2, U32>}, ez: {True{} == U32.is_zero(x) : Bool},
  -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type, h: In.Go(1n+f, e, st, k, R)) -> In.Go(1n+f, C.Cir.Stmt.if{c, t, e}, st, k, R):
  %ev : In.Ok(C.Cir.exec.then(C.Cir.exec.if(_, u => C.Cir.exec(1n+f, t, st), u => C.Cir.exec(1n+f, e, st)), k), R)
  %ez : In.Ok(C.Cir.exec.then(C.Cir.exec.if.of(_, u => C.Cir.exec(1n+f, t, st), u => C.Cir.exec(1n+f, e, st)), k), R)
  h

# M.make, then k
def In.mk(+f: Nat, +r: Nat, +h: C.Cir.Expr, +a: C.Cir.Expr, +b: C.Cir.Expr, +c: C.Cir.Expr, +regs: List<&2, U32>, +m: C.Cir.Cells,
  +next: U32, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, U32>, +vh: U32, +va: U32, +vb: U32, +vc: U32,
  p0: {Some{0} == List.get(&2, U32, regs, 3n) : Maybe<&2, U32>}, rl: {True{} == Nat.is_lt(r, List.length(&2, U32, regs)) : Bool},
  +er: {Some{next} == List.get(&2, U32, List.set(&2, U32, regs, r, next), r) : Maybe<&2, U32>},
  ec: In.lt(next) -> {True{} == C.Cir.is_cell(next, K, F, U32.inc(next)) : Bool},
  eh: @m2: C.Cir.Cells -> @pg2: U32 -> {Some{vh} == C.Cir.eval(h, In.S(List.set(&2, U32, regs, r, next), m2, U32.inc(next), F, K, pg2, L, I)) : Maybe<&2, U32>},
  ea: @m2: C.Cir.Cells -> @pg2: U32 -> {Some{va} == C.Cir.eval(a, In.S(List.set(&2, U32, regs, r, next), m2, U32.inc(next), F, K, pg2, L, I)) : Maybe<&2, U32>},
  eb: @m2: C.Cir.Cells -> @pg2: U32 -> {Some{vb} == C.Cir.eval(b, In.S(List.set(&2, U32, regs, r, next), m2, U32.inc(next), F, K, pg2, L, I)) : Maybe<&2, U32>},
  ef: @m2: C.Cir.Cells -> @pg2: U32 -> {Some{vc} == C.Cir.eval(c, In.S(List.set(&2, U32, regs, r, next), m2, U32.inc(next), F, K, pg2, L, I)) : Maybe<&2, U32>},
  -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type,
  g: @pg2: U32 -> In.lt(next) -> In.Ok(k(In.S(List.set(&2, U32, regs, r, next), C.Cir.Cells.set(m, next, C.Cir.Cell{vh, 1, va, vb, vc}), U32.inc(next), F, K, pg2, L, I)), R)) ->
  In.Go(1n+f, C.M.make(r, h, a, b, c), In.S(regs, m, next, F, K, pg, L, I), k, R):
  +rg = List.set(&2, U32, regs, r, next)
  +ms = C.Cir.Cells.set(m, next, C.Cir.Cell{vh, 1, va, vb, vc})
  In.then(C.Cir.exec(1n+f, C.M.make(r, h, a, b, c), In.S(regs, m, next, F, K, pg, L, I)), k,
    s => In.Is(s, rg, ms, U32.inc(next), F, K, L, I, In.lt(next)), R,
    In.make(f, r, h, a, b, c, regs, m, next, F, K, pg, L, I, vh, va, vb, vc, p0, rl, er, ec, eh, ea, eb, ef),
    s => e => In.at(s, rg, ms, U32.inc(next), F, K, L, I, In.lt(next), R, k, e, g))

# The cells that the run keeps
# ----------------------------

# the cell j is one that the run keeps: one of the image's first 89, or one
# from the table on, before F
def In.kp(+j: U32, +F: U32) -> Bool:
  Bool.or(Nat.is_lt(U32.to_nat(j), 89n), Bool.and(Nat.is_le(345n, U32.to_nat(j)), Nat.is_lt(U32.to_nat(j), U32.to_nat(F))))

# m holds the cells of m0 that the run keeps
def In.Fr(m0: C.Cir.Cells, m: C.Cir.Cells, F: U32) -> Type:
  @j: U32 -> {True{} == In.kp(j, F) : Bool} -> {C.Cir.Cells.get(m0, j) == C.Cir.Cells.get(m, j) : C.Cir.Cell}

def Fr.refl(-m0: C.Cir.Cells, -F: U32) -> In.Fr(m0, m0, F):
  j => h => {==}

# a cell from F on is none that the run keeps
def In.kpNew(+i: U32, +F: U32, hF: N.Le(345n, U32.to_nat(F)), +hi: N.Le(U32.to_nat(F), U32.to_nat(i))) -> {False{} == In.kp(i, F) : Bool}:
  +ti = U32.to_nat(i)
  +tF = U32.to_nat(F)
  +h345 = N.le_trans(345n, tF, ti, hF, hi)
  %Na.lt_f(ti, 89n, N.le_trans(89n, 345n, ti, Unit{}, h345)) : {False{} == Bool.or(_, Bool.and(Nat.is_le(345n, ti), Nat.is_lt(ti, tF))) : Bool}
  %Na.le_t(345n, ti, h345) : {False{} == Bool.or(False{}, Bool.and(_, Nat.is_lt(ti, tF))) : Bool}
  %Na.lt_f(ti, tF, hi) : {False{} == Bool.or(False{}, Bool.and(True{}, _)) : Bool}
  {==}

# a cache cell is none that the run keeps
def In.kpJ(+w: Word(8n), +F: U32) -> {False{} == In.kp(In.J(w), F) : Bool}:
  +tJ = U32.to_nat(In.J(w))
  %Na.lt_f(tJ, 89n, In.Jlo(w)) : {False{} == Bool.or(_, Bool.and(Nat.is_le(345n, tJ), Nat.is_lt(tJ, U32.to_nat(F)))) : Bool}
  %Na.le_f(345n, tJ, In.Jhi(w)) : {False{} == Bool.or(False{}, Bool.and(_, Nat.is_lt(tJ, U32.to_nat(F)))) : Bool}
  {==}

def In.kpne(+j: U32, +i: U32, +F: U32, h: {True{} == In.kp(j, F) : Bool}, hi: {False{} == In.kp(i, F) : Bool}, e: {j == i : U32}) -> Empty:
  N.true_ne_false(Equal.trans(Bool, True{}, In.kp(j, F), False{}, h,
    Equal.trans(Bool, In.kp(j, F), In.kp(i, F), False{}, Equal.cong(U32, Bool, z => In.kp(z, F), j, i, e),
      Equal.sym(Bool, False{}, In.kp(i, F), hi))))

# a set of a cell that the run does not keep
def Fr.set(-m0: C.Cir.Cells, +m: C.Cir.Cells, +F: U32, +i: U32, +x: C.Cir.Cell, +hi: {False{} == In.kp(i, F) : Bool},
  fr: In.Fr(m0, m, F)) -> In.Fr(m0, C.Cir.Cells.set(m, i, x), F):
  +j => +h => Equal.trans(C.Cir.Cell, C.Cir.Cells.get(m0, j), C.Cir.Cells.get(m, j), C.Cir.Cells.get(C.Cir.Cells.set(m, i, x), j),
    fr(j, h), Cl.get_other(m, j, i, x, e => In.kpne(j, i, F, h, hi, e)))

# a new cell
def Fr.step(-m0: C.Cir.Cells, +m: C.Cir.Cells, +F: U32, +i: U32, +x: C.Cir.Cell, hF: N.Le(345n, U32.to_nat(F)),
  hi: N.Le(U32.to_nat(F), U32.to_nat(i)), fr: In.Fr(m0, m, F)) -> In.Fr(m0, C.Cir.Cells.set(m, i, x), F):
  Fr.set(m0, m, F, i, x, In.kpNew(i, F, hF, hi), fr)

# the cache's entry of w8
def Fr.cs(-m0: C.Cir.Cells, +m: C.Cir.Cells, +F: U32, +w8: Word(8n), +v: U32, fr: In.Fr(m0, m, F)) -> In.Fr(m0, In.cs(m, w8, v), F):
  Fr.set(m0, m, F, In.J(w8), C.Cir.Cell.set(2n, C.Cir.Cells.get(m, In.J(w8)), v), In.kpJ(w8, F), fr)

# The code of M.input
# -------------------

def In.c.i1() -> C.Cir.Stmt:
  C.M.set(C.R.ij(), C.M.sub(C.M.g(C.R.ij()), C.M.c(1)))

def In.c.i2() -> C.Cir.Stmt:
  C.M.make(C.R.t1(), C.M.c(C.M.h.static()), C.M.g(C.R.iw()), C.M.c(C.I.lab(C.N.unit())), C.M.c(0))

def In.c.pick() -> C.Cir.Expr:
  C.M.pick(C.M.and(C.M.shr(C.M.g(C.R.ib()), C.M.g(C.R.ij())), C.M.c(1)), C.M.c(C.I.true()), C.M.c(C.I.false()))

def In.c.i3() -> C.Cir.Stmt:
  C.M.make(C.R.t2(), C.M.c(C.M.h.static()), In.c.pick(), C.M.g(C.R.t1()), C.M.c(0))

def In.c.i4() -> C.Cir.Stmt:
  C.M.make(C.R.iw(), C.M.c(C.M.h.static()), C.M.c(C.I.lab(C.N.wcon())), C.M.g(C.R.t2()), C.M.c(0))

def In.c.inner() -> C.Cir.Stmt:
  C.M.do([In.c.i1(), In.c.i2(), In.c.i3(), In.c.i4()])

# the bit j of ib
def In.bit(+ib: U32, +j: U32) -> Bool:
  In.b0(U32.shrn(ib, U32.to_nat(U32.and(j, 31))))

# the pick of the bit: 13 or 14
def In.evpick(+fo: U32, +ii: U32, +ib: U32, +il: U32, +iu: U32, +iw: U32, +ij: U32, +t1: U32, +t2: U32, +m: C.Cir.Cells, +next: U32,
  +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, U32>) ->
  {Some{Bool.pick(U32, In.bit(ib, ij), 13, 14)} == C.Cir.eval(In.c.pick(), In.S(In.R(fo, ii, ib, il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I)) : Maybe<&2, U32>}:
  +y = U32.shrn(ib, U32.to_nat(U32.and(ij, 31)))
  %Equal.sym(U32, Bool.pick(U32, In.b0(y), 13, 14), U32.or(U32.and(13, U32.sub(0, U32.and(y, 1))), U32.and(14, U32.sub(U32.and(y, 1), 1))), In.pv(y)) :
    {Some{_} == C.Cir.eval(In.c.pick(), In.S(In.R(fo, ii, ib, il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I)) : Maybe<&2, U32>}
  {==}

# The bits' loop
# --------------

# what a round of the bits' loop gives: the word iw2 of 1 + n bits, the bit
# of ib at j in front of t, with the fuel fw and the count N
def In.ir.K(+fo: U32, +ii: U32, +ib: U32, +il: U32, +iu: U32, +j: U32, +N: Nat, +F: U32, +K: U32, +L: U32, +I: List<&2, U32>, +f0: Nat,
  +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, -m0: C.Cir.Cells, +fw: Nat, +n: Nat, +t: Word(n), +fl: Nat, +bl: C.Term,
  -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type) -> Type:
  @iw2: U32 -> @t12: U32 -> @t22: U32 -> @m2: C.Cir.Cells -> @nx2: U32 -> @pg2: U32 -> In.Fa(m2, nx2, N, F, f0, fc, ks, img) ->
    In.St(fw, m2, F, N, iw2, C.Program.word(1n+n, WCon{In.bit(ib, j), t}), ks, img) -> In.St(fl, m2, F, N, il, bl, ks, img) ->
    In.Fr(m0, m2, F) -> In.Ok(k(In.S(In.R(fo, ii, ib, il, iu, iw2, j, t12, t22), m2, nx2, F, K, pg2, L, I)), R)

# the third make of a round: iw gets WCon in front of the cell t2
def In.ir.c(+f: Nat, +fo: U32, +ii: U32, +ib: U32, +il: U32, +iu: U32, +iw: U32, +j: U32, +t1: U32, +t2: U32, +m: C.Cir.Cells, +next: U32,
  +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, U32>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  -m0: C.Cir.Cells, +fw: Nat, +n: Nat, +t: Word(n), +fl: Nat, +bl: C.Term,
  +hF: N.Le(345n, U32.to_nat(F)), +hw: N.Le(f0, fw), +fa: In.Fa(m, next, N, F, f0, fc, ks, img),
  +s2: In.St(fw, m, F, N, t2, C.Term.Tup{C.Quan.Q1{}, C.Program.bit(In.bit(ib, j)), C.Term.Tup{C.Quan.Q1{}, C.Program.word(n, t), C.Term.Lab{C.Program.name.unit()}}}, ks, img),
  +sl: In.St(fl, m, F, N, il, bl, ks, img), fr: In.Fr(m0, m, F),
  -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type,
  g: In.ir.K(fo, ii, ib, il, iu, j, 1n+N, F, K, L, I, f0, fc, ks, img, m0, 1n+fw, n, t, fl, bl, k, R)) ->
  In.Go(1n+f, C.M.do([In.c.i4()]), In.S(In.R(fo, ii, ib, il, iu, iw, j, t1, t2), m, next, F, K, pg, L, I), k, R):
  In.sq(f, In.c.i4(), C.M.do([]), In.S(In.R(fo, ii, ib, il, iu, iw, j, t1, t2), m, next, F, K, pg, L, I), k, R,
   In.mk(f, C.R.iw(), C.M.c(C.M.h.static()), C.M.c(C.I.lab(C.N.wcon())), C.M.g(C.R.t2()), C.M.c(0), In.R(fo, ii, ib, il, iu, iw, j, t1, t2), m, next,
    F, K, pg, L, I, In.hd(True{}), 6, t2, 0,
    {==}, {==}, {==}, lt => In.cellNew(next, K, F, lt, Fa.lF(m, next, N, F, f0, fc, ks, img, fa)),
    m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, t => C.Cir.exec.then(C.Cir.exec(1n+f, C.M.do([]), t), k), R,
    +pg3 => +lt3 =>
     In.nop(f, In.S(In.R(fo, ii, ib, il, iu, next, j, t1, t2), C.Cir.Cells.set(m, next, C.Cir.Cell{In.hd(True{}), 1, 6, t2, 0}), U32.inc(next), F, K, pg3, L, I), k, R,
       g(next, t1, t2, C.Cir.Cells.set(m, next, C.Cir.Cell{In.hd(True{}), 1, 6, t2, 0}), U32.inc(next), pg3,
         Fa.step(m, next, N, F, f0, fc, ks, img, C.Cir.Cell{In.hd(True{}), 1, 6, t2, 0}, lt3, hF, fa),
         In.tup(True{}, fw, m, F, N, next, 6, t2, C.Term.Lab{C.Program.name.wcon()},
           C.Term.Tup{C.Quan.Q1{}, C.Program.bit(In.bit(ib, j)), C.Term.Tup{C.Quan.Q1{}, C.Program.word(n, t), C.Term.Lab{C.Program.name.unit()}}}, ks, img,
           St.to(f0, fw, hw, m, F, N, 6, C.Term.Lab{C.Program.name.wcon()}, ks, img, Im.g6(f0, m, F, N, ks, img, Fa.im(m, next, N, F, f0, fc, ks, img, fa))),
           s2, Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa), Fa.hr(m, next, N, F, f0, fc, ks, img, hF, fa)),
         St.step(fl, m, F, N, il, bl, ks, img, next, C.Cir.Cell{In.hd(True{}), 1, 6, t2, 0}, Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa), sl),
         Fr.step(m0, m, F, next, C.Cir.Cell{In.hd(True{}), 1, 6, t2, 0}, hF, Fa.lF(m, next, N, F, f0, fc, ks, img, fa), fr)))))

# the second make of a round: t2 gets the bit in front of the cell t1
def In.ir.b(+f: Nat, +fo: U32, +ii: U32, +ib: U32, +il: U32, +iu: U32, +iw: U32, +j: U32, +t1: U32, +t2: U32, +m: C.Cir.Cells, +next: U32,
  +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, U32>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  -m0: C.Cir.Cells, +fw: Nat, +n: Nat, +t: Word(n), +fl: Nat, +bl: C.Term,
  +hF: N.Le(345n, U32.to_nat(F)), +hw: N.Le(f0, fw), +fa: In.Fa(m, next, N, F, f0, fc, ks, img),
  +s1: In.St(fw, m, F, N, t1, C.Term.Tup{C.Quan.Q1{}, C.Program.word(n, t), C.Term.Lab{C.Program.name.unit()}}, ks, img),
  +sl: In.St(fl, m, F, N, il, bl, ks, img), fr: In.Fr(m0, m, F),
  -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type,
  g: In.ir.K(fo, ii, ib, il, iu, j, 1n+(1n+N), F, K, L, I, f0, fc, ks, img, m0, 1n+(1n+fw), n, t, fl, bl, k, R)) ->
  In.Go(1n+f, C.M.do([In.c.i3(), In.c.i4()]), In.S(In.R(fo, ii, ib, il, iu, iw, j, t1, t2), m, next, F, K, pg, L, I), k, R):
  In.sq(f, In.c.i3(), C.M.do([In.c.i4()]), In.S(In.R(fo, ii, ib, il, iu, iw, j, t1, t2), m, next, F, K, pg, L, I), k, R,
   In.mk(f, C.R.t2(), C.M.c(C.M.h.static()), In.c.pick(), C.M.g(C.R.t1()), C.M.c(0), In.R(fo, ii, ib, il, iu, iw, j, t1, t2), m, next,
    F, K, pg, L, I, In.hd(True{}), Bool.pick(U32, In.bit(ib, j), 13, 14), t1, 0,
    {==}, {==}, {==}, lt => In.cellNew(next, K, F, lt, Fa.lF(m, next, N, F, f0, fc, ks, img, fa)),
    m4 => pg4 => {==}, m4 => pg4 => In.evpick(fo, ii, ib, il, iu, iw, j, t1, next, m4, U32.inc(next), F, K, pg4, L, I),
    m4 => pg4 => {==}, m4 => pg4 => {==}, t => C.Cir.exec.then(C.Cir.exec(1n+f, C.M.do([In.c.i4()]), t), k), R,
    +pg3 => +lt3 =>
     In.ir.c(f, fo, ii, ib, il, iu, iw, j, t1, next, C.Cir.Cells.set(m, next, C.Cir.Cell{In.hd(True{}), 1, Bool.pick(U32, In.bit(ib, j), 13, 14), t1, 0}),
       U32.inc(next), 1n+N, F, K, pg3, L, I, f0, fc, ks, img, m0, 1n+fw, n, t, fl, bl, hF, N.le_succ(f0, fw, hw),
       Fa.step(m, next, N, F, f0, fc, ks, img, C.Cir.Cell{In.hd(True{}), 1, Bool.pick(U32, In.bit(ib, j), 13, 14), t1, 0}, lt3, hF, fa),
       In.tup(True{}, fw, m, F, N, next, Bool.pick(U32, In.bit(ib, j), 13, 14), t1, C.Program.bit(In.bit(ib, j)),
         C.Term.Tup{C.Quan.Q1{}, C.Program.word(n, t), C.Term.Lab{C.Program.name.unit()}}, ks, img,
         St.to(f0, fw, hw, m, F, N, Bool.pick(U32, In.bit(ib, j), 13, 14), C.Program.bit(In.bit(ib, j)), ks, img,
           Im.bit(In.bit(ib, j), f0, m, F, N, ks, img, Fa.im(m, next, N, F, f0, fc, ks, img, fa))),
         s1, Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa), Fa.hr(m, next, N, F, f0, fc, ks, img, hF, fa)),
       St.step(fl, m, F, N, il, bl, ks, img, next, C.Cir.Cell{In.hd(True{}), 1, Bool.pick(U32, In.bit(ib, j), 13, 14), t1, 0},
         Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa), sl),
       Fr.step(m0, m, F, next, C.Cir.Cell{In.hd(True{}), 1, Bool.pick(U32, In.bit(ib, j), 13, 14), t1, 0}, hF, Fa.lF(m, next, N, F, f0, fc, ks, img, fa), fr),
       k, R, g)))

# a round of the bits' loop: ij goes down by one, and iw gets the bit of ib
# at ij in front
def In.ir(+f: Nat, +fo: U32, +ii: U32, +ib: U32, +il: U32, +iu: U32, +iw: U32, +jp: U32, +t1: U32, +t2: U32, +m: C.Cir.Cells, +next: U32,
  +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, U32>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  -m0: C.Cir.Cells, +fw: Nat, +n: Nat, +t: Word(n), +fl: Nat, +bl: C.Term,
  +hF: N.Le(345n, U32.to_nat(F)), +hw: N.Le(f0, fw), +fa: In.Fa(m, next, N, F, f0, fc, ks, img),
  +sw: In.St(fw, m, F, N, iw, C.Program.word(n, t), ks, img), +sl: In.St(fl, m, F, N, il, bl, ks, img), fr: In.Fr(m0, m, F),
  -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type,
  g: In.ir.K(fo, ii, ib, il, iu, U32.sub(jp, 1), 3n+N, F, K, L, I, f0, fc, ks, img, m0, 3n+fw, n, t, fl, bl, k, R)) ->
  In.Go(1n+f, In.c.inner(), In.S(In.R(fo, ii, ib, il, iu, iw, jp, t1, t2), m, next, F, K, pg, L, I), k, R):
  In.sq(f, In.c.i1(), C.M.do([In.c.i2(), In.c.i3(), In.c.i4()]), In.S(In.R(fo, ii, ib, il, iu, iw, jp, t1, t2), m, next, F, K, pg, L, I), k, R,
   In.set(f, C.R.ij(), C.M.sub(C.M.g(C.R.ij()), C.M.c(1)), In.R(fo, ii, ib, il, iu, iw, jp, t1, t2), m, next, F, K, pg, L, I, U32.sub(jp, 1), {==}, {==},
    t => C.Cir.exec.then(C.Cir.exec(1n+f, C.M.do([In.c.i2(), In.c.i3(), In.c.i4()]), t), k), R,
    In.sq(f, In.c.i2(), C.M.do([In.c.i3(), In.c.i4()]), In.S(In.R(fo, ii, ib, il, iu, iw, U32.sub(jp, 1), t1, t2), m, next, F, K, pg, L, I), k, R,
     In.mk(f, C.R.t1(), C.M.c(C.M.h.static()), C.M.g(C.R.iw()), C.M.c(C.I.lab(C.N.unit())), C.M.c(0), In.R(fo, ii, ib, il, iu, iw, U32.sub(jp, 1), t1, t2),
      m, next, F, K, pg, L, I, In.hd(True{}), iw, 1, 0,
      {==}, {==}, {==}, lt => In.cellNew(next, K, F, lt, Fa.lF(m, next, N, F, f0, fc, ks, img, fa)),
      m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, t => C.Cir.exec.then(C.Cir.exec(1n+f, C.M.do([In.c.i3(), In.c.i4()]), t), k), R,
      +pg3 => +lt3 =>
       In.ir.b(f, fo, ii, ib, il, iu, iw, U32.sub(jp, 1), next, t2, C.Cir.Cells.set(m, next, C.Cir.Cell{In.hd(True{}), 1, iw, 1, 0}),
         U32.inc(next), 1n+N, F, K, pg3, L, I, f0, fc, ks, img, m0, 1n+fw, n, t, fl, bl, hF, N.le_succ(f0, fw, hw),
         Fa.step(m, next, N, F, f0, fc, ks, img, C.Cir.Cell{In.hd(True{}), 1, iw, 1, 0}, lt3, hF, fa),
         In.tup(True{}, fw, m, F, N, next, iw, 1, C.Program.word(n, t), C.Term.Lab{C.Program.name.unit()}, ks, img, sw,
           St.to(f0, fw, hw, m, F, N, 1, C.Term.Lab{C.Program.name.unit()}, ks, img, Im.g1(f0, m, F, N, ks, img, Fa.im(m, next, N, F, f0, fc, ks, img, fa))),
           Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa), Fa.hr(m, next, N, F, f0, fc, ks, img, hF, fa)),
         St.step(fl, m, F, N, il, bl, ks, img, next, C.Cir.Cell{In.hd(True{}), 1, iw, 1, 0}, Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa), sl),
         Fr.step(m0, m, F, next, C.Cir.Cell{In.hd(True{}), 1, iw, 1, 0}, hF, Fa.lF(m, next, N, F, f0, fc, ks, img, fa), fr),
         k, R, g)))))

# the bits' loop
def In.c.W() -> C.Cir.Stmt:
  C.M.while(C.M.ne(C.M.g(C.R.ij()), C.M.c(0)), In.c.inner())

# the word of the low byte of ib, the lowest bit first, over 24 False bits
def In.wd(+ib: U32) -> Word(32n):
  WCon{In.bit(ib, 0), WCon{In.bit(ib, 1), WCon{In.bit(ib, 2), WCon{In.bit(ib, 3), WCon{In.bit(ib, 4), WCon{In.bit(ib, 5), WCon{In.bit(ib, 6),
    WCon{In.bit(ib, 7), Word.zero(24n)}}}}}}}}

# the word that the bits' loop builds
def In.wd.eq(+ib: U32) -> {C.Program.word(1n+(1n+(1n+(1n+(1n+(1n+(1n+(1n+24n))))))), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(8, 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(8, 1), 1)), WCon{In.bit(ib, U32.sub(8, 1)), Word.zero(24n)}}}}}}}}) == C.Program.word(32n, In.wd(ib)) : C.Term}:
  {==}

# a term, by an equation
def St.cast(-f: Nat, -m: C.Cir.Cells, -F: U32, -N: Nat, -c: U32, -t: C.Term, -u: C.Term, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>,
  e: {t == u : C.Term}, s: In.St(f, m, F, N, c, t, ks, img)) -> In.St(f, m, F, N, c, u, ks, img):
  %e : In.St(f, m, F, N, c, _, ks, img)
  s

# the bits' loop: iw gets the word of the low byte of ib, over the 24 False
# bits of the image, in 8 rounds of 3 new cells
def In.il(+Z: Nat, +fo: U32, +ii: U32, +ib: U32, +il: U32, +iu: U32, +t1: U32, +t2: U32, +m: C.Cir.Cells, +next: U32,
  +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, U32>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  -m0: C.Cir.Cells, +fl: Nat, +bl: C.Term, +hF: N.Le(345n, U32.to_nat(F)), +fa: In.Fa(m, next, N, F, f0, fc, ks, img),
  +sl: In.St(fl, m, F, N, il, bl, ks, img), fr: In.Fr(m0, m, F), -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type,
  g: @iw2: U32 -> @ij2: U32 -> @t12: U32 -> @t22: U32 -> @m2: C.Cir.Cells -> @nx2: U32 -> @pg2: U32 -> In.Fa(m2, nx2, 24n+N, F, f0, fc, ks, img) ->
    In.St(24n+f0, m2, F, 24n+N, iw2, C.Program.word(32n, In.wd(ib)), ks, img) -> In.St(fl, m2, F, 24n+N, il, bl, ks, img) -> In.Fr(m0, m2, F) ->
    In.Ok(k(In.S(In.R(fo, ii, ib, il, iu, iw2, ij2, t12, t22), m2, nx2, F, K, pg2, L, I)), R)) ->
  In.Go(9n+Z, In.c.W(), In.S(In.R(fo, ii, ib, il, iu, 16, 8, t1, t2), m, next, F, K, pg, L, I), k, R):
  In.wh(8n+Z, C.M.ne(C.M.g(C.R.ij()), C.M.c(0)), In.c.inner(), In.S(In.R(fo, ii, ib, il, iu, 16, 8, t1, t2), m, next, F, K, pg, L, I), k, R, {==},
   In.ir(7n+Z, fo, ii, ib, il, iu, 16, 8, t1, t2, m, next, N, F, K, pg, L, I, f0, fc, ks, img, m0, f0, 24n, Word.zero(24n), fl, bl, hF, N.le_refl(f0), fa, Im.g16(f0, m, F, N, ks, img, Fa.im(m, next, N, F, f0, fc, ks, img, fa)), sl, fr,
    t => C.Cir.exec.then(C.Cir.exec(8n+Z, In.c.W(), t), k), R,
    +iw1 => +ta1 => +tb1 => +m1 => +nx1 => +pg1 => +fa1 => +sw1 => +sl1 => fr1 =>
     In.wh(7n+Z, C.M.ne(C.M.g(C.R.ij()), C.M.c(0)), In.c.inner(), In.S(In.R(fo, ii, ib, il, iu, iw1, U32.sub(8, 1), ta1, tb1), m1, nx1, F, K, pg1, L, I), k, R, {==},
      In.ir(6n+Z, fo, ii, ib, il, iu, iw1, U32.sub(8, 1), ta1, tb1, m1, nx1, 3n+N, F, K, pg1, L, I, f0, fc, ks, img, m0, 3n+f0, 1n+24n, WCon{In.bit(ib, U32.sub(8, 1)), Word.zero(24n)}, fl, bl, hF, N.le_add_l(3n, f0), fa1, sw1, sl1, fr1,
       t => C.Cir.exec.then(C.Cir.exec(7n+Z, In.c.W(), t), k), R,
       +iw2 => +ta2 => +tb2 => +m2 => +nx2 => +pg2 => +fa2 => +sw2 => +sl2 => fr2 =>
        In.wh(6n+Z, C.M.ne(C.M.g(C.R.ij()), C.M.c(0)), In.c.inner(), In.S(In.R(fo, ii, ib, il, iu, iw2, U32.sub(U32.sub(8, 1), 1), ta2, tb2), m2, nx2, F, K, pg2, L, I), k, R, {==},
         In.ir(5n+Z, fo, ii, ib, il, iu, iw2, U32.sub(U32.sub(8, 1), 1), ta2, tb2, m2, nx2, 6n+N, F, K, pg2, L, I, f0, fc, ks, img, m0, 6n+f0, 1n+(1n+24n), WCon{In.bit(ib, U32.sub(U32.sub(8, 1), 1)), WCon{In.bit(ib, U32.sub(8, 1)), Word.zero(24n)}}, fl, bl, hF, N.le_add_l(6n, f0), fa2, sw2, sl2, fr2,
          t => C.Cir.exec.then(C.Cir.exec(6n+Z, In.c.W(), t), k), R,
          +iw3 => +ta3 => +tb3 => +m3 => +nx3 => +pg3 => +fa3 => +sw3 => +sl3 => fr3 =>
           In.wh(5n+Z, C.M.ne(C.M.g(C.R.ij()), C.M.c(0)), In.c.inner(), In.S(In.R(fo, ii, ib, il, iu, iw3, U32.sub(U32.sub(U32.sub(8, 1), 1), 1), ta3, tb3), m3, nx3, F, K, pg3, L, I), k, R, {==},
            In.ir(4n+Z, fo, ii, ib, il, iu, iw3, U32.sub(U32.sub(U32.sub(8, 1), 1), 1), ta3, tb3, m3, nx3, 9n+N, F, K, pg3, L, I, f0, fc, ks, img, m0, 9n+f0, 1n+(1n+(1n+24n)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(8, 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(8, 1), 1)), WCon{In.bit(ib, U32.sub(8, 1)), Word.zero(24n)}}}, fl, bl, hF, N.le_add_l(9n, f0), fa3, sw3, sl3, fr3,
             t => C.Cir.exec.then(C.Cir.exec(5n+Z, In.c.W(), t), k), R,
             +iw4 => +ta4 => +tb4 => +m4 => +nx4 => +pg4 => +fa4 => +sw4 => +sl4 => fr4 =>
              In.wh(4n+Z, C.M.ne(C.M.g(C.R.ij()), C.M.c(0)), In.c.inner(), In.S(In.R(fo, ii, ib, il, iu, iw4, U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), ta4, tb4), m4, nx4, F, K, pg4, L, I), k, R, {==},
               In.ir(3n+Z, fo, ii, ib, il, iu, iw4, U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), ta4, tb4, m4, nx4, 12n+N, F, K, pg4, L, I, f0, fc, ks, img, m0, 12n+f0, 1n+(1n+(1n+(1n+24n))), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(8, 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(8, 1), 1)), WCon{In.bit(ib, U32.sub(8, 1)), Word.zero(24n)}}}}, fl, bl, hF, N.le_add_l(12n, f0), fa4, sw4, sl4, fr4,
                t => C.Cir.exec.then(C.Cir.exec(4n+Z, In.c.W(), t), k), R,
                +iw5 => +ta5 => +tb5 => +m5 => +nx5 => +pg5 => +fa5 => +sw5 => +sl5 => fr5 =>
                 In.wh(3n+Z, C.M.ne(C.M.g(C.R.ij()), C.M.c(0)), In.c.inner(), In.S(In.R(fo, ii, ib, il, iu, iw5, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), ta5, tb5), m5, nx5, F, K, pg5, L, I), k, R, {==},
                  In.ir(2n+Z, fo, ii, ib, il, iu, iw5, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), ta5, tb5, m5, nx5, 15n+N, F, K, pg5, L, I, f0, fc, ks, img, m0, 15n+f0, 1n+(1n+(1n+(1n+(1n+24n)))), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(8, 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(8, 1), 1)), WCon{In.bit(ib, U32.sub(8, 1)), Word.zero(24n)}}}}}, fl, bl, hF, N.le_add_l(15n, f0), fa5, sw5, sl5, fr5,
                   t => C.Cir.exec.then(C.Cir.exec(3n+Z, In.c.W(), t), k), R,
                   +iw6 => +ta6 => +tb6 => +m6 => +nx6 => +pg6 => +fa6 => +sw6 => +sl6 => fr6 =>
                    In.wh(2n+Z, C.M.ne(C.M.g(C.R.ij()), C.M.c(0)), In.c.inner(), In.S(In.R(fo, ii, ib, il, iu, iw6, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1), ta6, tb6), m6, nx6, F, K, pg6, L, I), k, R, {==},
                     In.ir(1n+Z, fo, ii, ib, il, iu, iw6, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1), ta6, tb6, m6, nx6, 18n+N, F, K, pg6, L, I, f0, fc, ks, img, m0, 18n+f0, 1n+(1n+(1n+(1n+(1n+(1n+24n))))), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(8, 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(8, 1), 1)), WCon{In.bit(ib, U32.sub(8, 1)), Word.zero(24n)}}}}}}, fl, bl, hF, N.le_add_l(18n, f0), fa6, sw6, sl6, fr6,
                      t => C.Cir.exec.then(C.Cir.exec(2n+Z, In.c.W(), t), k), R,
                      +iw7 => +ta7 => +tb7 => +m7 => +nx7 => +pg7 => +fa7 => +sw7 => +sl7 => fr7 =>
                       In.wh(1n+Z, C.M.ne(C.M.g(C.R.ij()), C.M.c(0)), In.c.inner(), In.S(In.R(fo, ii, ib, il, iu, iw7, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1), 1), ta7, tb7), m7, nx7, F, K, pg7, L, I), k, R, {==},
                        In.ir(Z, fo, ii, ib, il, iu, iw7, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1), 1), ta7, tb7, m7, nx7, 21n+N, F, K, pg7, L, I, f0, fc, ks, img, m0, 21n+f0, 1n+(1n+(1n+(1n+(1n+(1n+(1n+24n)))))), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(8, 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(8, 1), 1)), WCon{In.bit(ib, U32.sub(8, 1)), Word.zero(24n)}}}}}}}, fl, bl, hF, N.le_add_l(21n, f0), fa7, sw7, sl7, fr7,
                         t => C.Cir.exec.then(C.Cir.exec(1n+Z, In.c.W(), t), k), R,
                         +iw8 => +ta8 => +tb8 => +m8 => +nx8 => +pg8 => +fa8 => +sw8 => +sl8 => fr8 =>
                          In.wh.end(Z, C.M.ne(C.M.g(C.R.ij()), C.M.c(0)), In.c.inner(), In.S(In.R(fo, ii, ib, il, iu, iw8, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1), 1), 1), ta8, tb8), m8, nx8, F, K, pg8, L, I), k, R, {==},
                           g(iw8, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1), 1), 1), ta8, tb8, m8, nx8, pg8, fa8, St.cast(24n+f0, m8, F, 24n+N, iw8, C.Program.word(1n+(1n+(1n+(1n+(1n+(1n+(1n+(1n+24n))))))), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(U32.sub(8, 1), 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(U32.sub(8, 1), 1), 1)), WCon{In.bit(ib, U32.sub(U32.sub(8, 1), 1)), WCon{In.bit(ib, U32.sub(8, 1)), Word.zero(24n)}}}}}}}}), C.Program.word(32n, In.wd(ib)), ks, img, In.wd.eq(ib), sw8), sl8, fr8))))))))))))))))))

# The cache's new entry
# ---------------------

def In.c.c1() -> C.Cir.Stmt:
  C.M.set(C.R.iw(), C.M.c(C.I.z24()))

def In.c.c2() -> C.Cir.Stmt:
  C.M.set(C.R.ij(), C.M.c(8))

def In.c.c5() -> C.Cir.Stmt:
  C.M.make(C.R.iu(), C.M.c(C.M.h.static()), C.M.c(C.I.lab(C.N.u32())), C.M.g(C.R.t1()), C.M.c(0))

def In.c.c6() -> C.Cir.Stmt:
  C.M.st(2n, C.M.add(C.M.c(C.I.cache()), C.M.g(C.R.ib())), C.M.g(C.R.iu()))

def In.c.cache() -> C.Cir.Stmt:
  C.M.do([In.c.c1(), In.c.c2(), In.c.W(), In.c.i2(), In.c.c5(), In.c.c6()])

# the U32 of a byte, as the cache's entry builds it
def In.wd_u8(w8: Word(8n)) ->
  {C.Term.Tup{C.Quan.Q1{}, C.Term.Lab{C.Program.name.u32()}, C.Term.Tup{C.Quan.Q1{}, C.Program.word(32n, In.wd(In.u8(w8))), C.Term.Lab{C.Program.name.unit()}}} ==
    C.Program.cell.of(In.u8(w8)) : C.Term}:
  match w8:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}:
      {==}

# what the cache's new entry gives: the cell iu2 of the U32 of the byte w8,
# in 26 new cells
def In.cch.K(+fo: U32, +ii: U32, +w8: Word(8n), +il: U32, +N: Nat, +F: U32, +K: U32, +L: U32, +I: List<&2, U32>, +f0: Nat, +fc: Nat,
  +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, -m0: C.Cir.Cells, +fl: Nat, +bl: C.Term, -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type) -> Type:
  @iu2: U32 -> @iw2: U32 -> @ij2: U32 -> @t12: U32 -> @t22: U32 -> @m2: C.Cir.Cells -> @nx2: U32 -> @pg2: U32 -> In.Fa(m2, nx2, N, F, f0, fc, ks, img) ->
    In.St(fc, m2, F, N, iu2, C.Program.cell.of(In.u8(w8)), ks, img) -> In.St(fl, m2, F, N, il, bl, ks, img) -> In.Fr(m0, m2, F) ->
    In.Ok(k(In.S(In.R(fo, ii, In.u8(w8), il, iu2, iw2, ij2, t12, t22), m2, nx2, F, K, pg2, L, I)), R)

# the store of the cache's new entry
def In.cch.c(+Z: Nat, +fo: U32, +ii: U32, +w8: Word(8n), +il: U32, +iu: U32, +iw: U32, +ij: U32, +t1: U32, +t2: U32, +m: C.Cir.Cells,
  +next: U32, +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, U32>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, -m0: C.Cir.Cells, +fl: Nat, +bl: C.Term, +hF: N.Le(345n, U32.to_nat(F)), +hK: N.Le(344n, U32.to_nat(K)),
  +fa: In.Fa(m, next, N, F, f0, fc, ks, img), +sv: In.St(fc, m, F, N, iu, C.Program.cell.of(In.u8(w8)), ks, img),
  +sl: In.St(fl, m, F, N, il, bl, ks, img), fr: In.Fr(m0, m, F), -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type,
  g: In.cch.K(fo, ii, w8, il, N, F, K, L, I, f0, fc, ks, img, m0, fl, bl, k, R)) ->
  In.Go(1n+(8n+Z), C.M.do([In.c.c6()]), In.S(In.R(fo, ii, In.u8(w8), il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I), k, R):
  In.sq(8n+Z, In.c.c6(), C.M.do([]), In.S(In.R(fo, ii, In.u8(w8), il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I), k, R,
   In.str(8n+Z, 2n, C.M.add(C.M.c(C.I.cache()), C.M.g(C.R.ib())), C.M.g(C.R.iu()), In.R(fo, ii, In.u8(w8), il, iu, iw, ij, t1, t2), m, next,
    F, K, pg, L, I, In.J(w8), iu, {==}, {==}, In.cellJ(w8, K, F, next, hK), t => C.Cir.exec.then(C.Cir.exec(1n+(8n+Z), C.M.do([]), t), k), R,
    In.nop(8n+Z, In.S(In.R(fo, ii, In.u8(w8), il, iu, iw, ij, t1, t2), In.cs(m, w8, iu), next, F, K, pg, L, I), k, R,
     g(iu, iw, ij, t1, t2, In.cs(m, w8, iu), next, pg, Fa.cs(m, next, N, F, f0, fc, ks, img, w8, iu, hF, sv, fa),
       St.fr(fc, m, F, N, iu, C.Program.cell.of(In.u8(w8)), ks, img, In.J(w8), C.Cir.Cell.set(2n, C.Cir.Cells.get(m, In.J(w8)), iu), In.rdJ(w8, F, N, hF), sv),
       St.fr(fl, m, F, N, il, bl, ks, img, In.J(w8), C.Cir.Cell.set(2n, C.Cir.Cells.get(m, In.J(w8)), iu), In.rdJ(w8, F, N, hF), sl),
       Fr.cs(m0, m, F, w8, iu, fr)))))

# the last make and the store of the cache's new entry
def In.cch.b(+Z: Nat, +fo: U32, +ii: U32, +w8: Word(8n), +il: U32, +iu: U32, +iw: U32, +ij: U32, +t1: U32, +t2: U32, +m: C.Cir.Cells,
  +next: U32, +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, U32>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, -m0: C.Cir.Cells, +fl: Nat, +bl: C.Term, +fs: Nat, +hF: N.Le(345n, U32.to_nat(F)), +hK: N.Le(344n, U32.to_nat(K)),
  +hs: N.Le(f0, fs), hc: N.Le(1n+fs, fc), +fa: In.Fa(m, next, N, F, f0, fc, ks, img),
  +s1: In.St(fs, m, F, N, t1, C.Term.Tup{C.Quan.Q1{}, C.Program.word(32n, In.wd(In.u8(w8))), C.Term.Lab{C.Program.name.unit()}}, ks, img),
  +sl: In.St(fl, m, F, N, il, bl, ks, img), fr: In.Fr(m0, m, F), -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type,
  g: In.cch.K(fo, ii, w8, il, 1n+N, F, K, L, I, f0, fc, ks, img, m0, fl, bl, k, R)) ->
  In.Go(1n+(8n+Z), C.M.do([In.c.c5(), In.c.c6()]), In.S(In.R(fo, ii, In.u8(w8), il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I), k, R):
  In.sq(8n+Z, In.c.c5(), C.M.do([In.c.c6()]), In.S(In.R(fo, ii, In.u8(w8), il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I), k, R,
   In.mk(8n+Z, C.R.iu(), C.M.c(C.M.h.static()), C.M.c(C.I.lab(C.N.u32())), C.M.g(C.R.t1()), C.M.c(0), In.R(fo, ii, In.u8(w8), il, iu, iw, ij, t1, t2),
    m, next, F, K, pg, L, I, In.hd(True{}), 4, t1, 0,
    {==}, {==}, {==}, lt => In.cellNew(next, K, F, lt, Fa.lF(m, next, N, F, f0, fc, ks, img, fa)),
    m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, t => C.Cir.exec.then(C.Cir.exec(1n+(8n+Z), C.M.do([In.c.c6()]), t), k), R,
    +pg3 => +lt3 =>
     +sv = St.to(1n+fs, fc, hc, C.Cir.Cells.set(m, next, C.Cir.Cell{In.hd(True{}), 1, 4, t1, 0}), F, 1n+N, next, C.Program.cell.of(In.u8(w8)), ks, img,
       St.cast(1n+fs, C.Cir.Cells.set(m, next, C.Cir.Cell{In.hd(True{}), 1, 4, t1, 0}), F, 1n+N, next,
         C.Term.Tup{C.Quan.Q1{}, C.Term.Lab{C.Program.name.u32()}, C.Term.Tup{C.Quan.Q1{}, C.Program.word(32n, In.wd(In.u8(w8))), C.Term.Lab{C.Program.name.unit()}}},
         C.Program.cell.of(In.u8(w8)), ks, img, In.wd_u8(w8),
         In.tup(True{}, fs, m, F, N, next, 4, t1, C.Term.Lab{C.Program.name.u32()},
           C.Term.Tup{C.Quan.Q1{}, C.Program.word(32n, In.wd(In.u8(w8))), C.Term.Lab{C.Program.name.unit()}}, ks, img,
           St.to(f0, fs, hs, m, F, N, 4, C.Term.Lab{C.Program.name.u32()}, ks, img, Im.g4(f0, m, F, N, ks, img, Fa.im(m, next, N, F, f0, fc, ks, img, fa))),
           s1, Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa), Fa.hr(m, next, N, F, f0, fc, ks, img, hF, fa))))
     +fa1 = Fa.step(m, next, N, F, f0, fc, ks, img, C.Cir.Cell{In.hd(True{}), 1, 4, t1, 0}, lt3, hF, fa)
     +sl1 = St.step(fl, m, F, N, il, bl, ks, img, next, C.Cir.Cell{In.hd(True{}), 1, 4, t1, 0}, Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa), sl)
     fr1 = Fr.step(m0, m, F, next, C.Cir.Cell{In.hd(True{}), 1, 4, t1, 0}, hF, Fa.lF(m, next, N, F, f0, fc, ks, img, fa), fr)
     In.cch.c(Z, fo, ii, w8, il, next, iw, ij, t1, t2, C.Cir.Cells.set(m, next, C.Cir.Cell{In.hd(True{}), 1, 4, t1, 0}), U32.inc(next), 1n+N,
       F, K, pg3, L, I, f0, fc, ks, img, m0, fl, bl, hF, hK, fa1, sv, sl1, fr1, k, R, g)))

# the cache's new entry: the U32 of the byte w8, as 8 bits over the image's 24
# False bits, stored in the cache
def In.cch(+Z: Nat, +fo: U32, +ii: U32, +w8: Word(8n), +il: U32, +iu: U32, +iw: U32, +ij: U32, +t1: U32, +t2: U32, +m: C.Cir.Cells,
  +next: U32, +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, U32>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, -m0: C.Cir.Cells, +fl: Nat, +bl: C.Term, +hF: N.Le(345n, U32.to_nat(F)), +hK: N.Le(344n, U32.to_nat(K)),
  hc: N.Le(26n+f0, fc), +fa: In.Fa(m, next, N, F, f0, fc, ks, img),
  +sl: In.St(fl, m, F, N, il, bl, ks, img), fr: In.Fr(m0, m, F), -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type,
  g: In.cch.K(fo, ii, w8, il, 26n+N, F, K, L, I, f0, fc, ks, img, m0, fl, bl, k, R)) ->
  In.Go(9n+Z, In.c.cache(), In.S(In.R(fo, ii, In.u8(w8), il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I), k, R):
  In.sq(8n+Z, In.c.c1(), C.M.do([In.c.c2(), In.c.W(), In.c.i2(), In.c.c5(), In.c.c6()]), In.S(In.R(fo, ii, In.u8(w8), il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I), k, R,
   In.set(8n+Z, C.R.iw(), C.M.c(C.I.z24()), In.R(fo, ii, In.u8(w8), il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I, 16, {==}, {==},
    t => C.Cir.exec.then(C.Cir.exec(1n+(8n+Z), C.M.do([In.c.c2(), In.c.W(), In.c.i2(), In.c.c5(), In.c.c6()]), t), k), R,
    In.sq(8n+Z, In.c.c2(), C.M.do([In.c.W(), In.c.i2(), In.c.c5(), In.c.c6()]), In.S(In.R(fo, ii, In.u8(w8), il, iu, 16, ij, t1, t2), m, next, F, K, pg, L, I), k, R,
     In.set(8n+Z, C.R.ij(), C.M.c(8), In.R(fo, ii, In.u8(w8), il, iu, 16, ij, t1, t2), m, next, F, K, pg, L, I, 8, {==}, {==},
      t => C.Cir.exec.then(C.Cir.exec(1n+(8n+Z), C.M.do([In.c.W(), In.c.i2(), In.c.c5(), In.c.c6()]), t), k), R,
      In.sq(8n+Z, In.c.W(), C.M.do([In.c.i2(), In.c.c5(), In.c.c6()]), In.S(In.R(fo, ii, In.u8(w8), il, iu, 16, 8, t1, t2), m, next, F, K, pg, L, I), k, R,
       In.il(Z, fo, ii, In.u8(w8), il, iu, t1, t2, m, next, N, F, K, pg, L, I, f0, fc, ks, img, m0, fl, bl, hF, fa, sl, fr,
        t => C.Cir.exec.then(C.Cir.exec(1n+(8n+Z), C.M.do([In.c.i2(), In.c.c5(), In.c.c6()]), t), k), R,
        +iw2 => +ij2 => +t12 => +t22 => +m2 => +nx2 => +pg2 => +fa2 => +sw2 => +sl2 => fr2 =>
         In.sq(8n+Z, In.c.i2(), C.M.do([In.c.c5(), In.c.c6()]), In.S(In.R(fo, ii, In.u8(w8), il, iu, iw2, ij2, t12, t22), m2, nx2, F, K, pg2, L, I), k, R,
          In.mk(8n+Z, C.R.t1(), C.M.c(C.M.h.static()), C.M.g(C.R.iw()), C.M.c(C.I.lab(C.N.unit())), C.M.c(0), In.R(fo, ii, In.u8(w8), il, iu, iw2, ij2, t12, t22),
           m2, nx2, F, K, pg2, L, I, In.hd(True{}), iw2, 1, 0,
           {==}, {==}, {==}, lt => In.cellNew(nx2, K, F, lt, Fa.lF(m2, nx2, 24n+N, F, f0, fc, ks, img, fa2)),
           m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==},
           t => C.Cir.exec.then(C.Cir.exec(1n+(8n+Z), C.M.do([In.c.c5(), In.c.c6()]), t), k), R,
           +pg3 => +lt3 =>
            In.cch.b(Z, fo, ii, w8, il, iu, iw2, ij2, nx2, t22, C.Cir.Cells.set(m2, nx2, C.Cir.Cell{In.hd(True{}), 1, iw2, 1, 0}), U32.inc(nx2), 1n+(24n+N),
              F, K, pg3, L, I, f0, fc, ks, img, m0, fl, bl, 1n+(24n+f0), hF, hK, N.le_add_l(25n, f0), hc,
              Fa.step(m2, nx2, 24n+N, F, f0, fc, ks, img, C.Cir.Cell{In.hd(True{}), 1, iw2, 1, 0}, lt3, hF, fa2),
              In.tup(True{}, 24n+f0, m2, F, 24n+N, nx2, iw2, 1, C.Program.word(32n, In.wd(In.u8(w8))), C.Term.Lab{C.Program.name.unit()}, ks, img, sw2,
                St.to(f0, 24n+f0, N.le_add_l(24n, f0), m2, F, 24n+N, 1, C.Term.Lab{C.Program.name.unit()}, ks, img,
                  Im.g1(f0, m2, F, 24n+N, ks, img, Fa.im(m2, nx2, 24n+N, F, f0, fc, ks, img, fa2))),
                Fa.hi(m2, nx2, 24n+N, F, f0, fc, ks, img, hF, fa2), Fa.hr(m2, nx2, 24n+N, F, f0, fc, ks, img, hF, fa2)),
              St.step(fl, m2, F, 24n+N, il, bl, ks, img, nx2, C.Cir.Cell{In.hd(True{}), 1, iw2, 1, 0}, Fa.hi(m2, nx2, 24n+N, F, f0, fc, ks, img, hF, fa2), sl2),
              Fr.step(m0, m2, F, nx2, C.Cir.Cell{In.hd(True{}), 1, iw2, 1, 0}, hF, Fa.lF(m2, nx2, 24n+N, F, f0, fc, ks, img, fa2), fr2),
              k, R, g)))))))))

# The list's new cell
# -------------------

def In.c.b5() -> C.Cir.Stmt:
  C.M.make(C.R.t1(), C.M.c(C.M.h.data()), C.M.g(C.R.il()), C.M.c(C.I.lab(C.N.unit())), C.M.c(0))

def In.c.b6() -> C.Cir.Stmt:
  C.M.make(C.R.t2(), C.M.c(C.M.h.data()), C.M.g(C.R.iu()), C.M.g(C.R.t1()), C.M.c(0))

def In.c.b7() -> C.Cir.Stmt:
  C.M.make(C.R.il(), C.M.c(C.M.h.data()), C.M.c(C.I.lab(C.N.con())), C.M.g(C.R.t2()), C.M.c(0))

# Con with the fields cu and bl
def In.con.eq(+cu: C.Term, +bl: C.Term) ->
  {C.Term.Tup{C.Quan.Q1{}, C.Term.Lab{C.Program.name.con()}, C.Term.Tup{C.Quan.Q1{}, cu, C.Term.Tup{C.Quan.Q1{}, bl, C.Term.Lab{C.Program.name.unit()}}}} ==
    C.Program.ctor(C.Program.name.con(), [cu, bl]) : C.Term}:
  {==}

# what the list's new cell gives: the cell il2 of Con with the fields cu and bl
def In.lst.K(+fo: U32, +ii: U32, +ib: U32, +iu: U32, +iw: U32, +ij: U32, +N: Nat, +F: U32, +K: U32, +L: U32, +I: List<&2, U32>, +f0: Nat,
  +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, -m0: C.Cir.Cells, +fs: Nat, +cu: C.Term, +bl: C.Term,
  -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type) -> Type:
  @il2: U32 -> @t12: U32 -> @t22: U32 -> @m2: C.Cir.Cells -> @nx2: U32 -> @pg2: U32 -> In.Fa(m2, nx2, N, F, f0, fc, ks, img) ->
    In.St(fs, m2, F, N, il2, C.Program.ctor(C.Program.name.con(), [cu, bl]), ks, img) -> In.Fr(m0, m2, F) ->
    In.Ok(k(In.S(In.R(fo, ii, ib, il2, iu, iw, ij, t12, t22), m2, nx2, F, K, pg2, L, I)), R)

# the list's last make: il gets Con in front of the cell t2
def In.lst.c(+f: Nat, +fo: U32, +ii: U32, +ib: U32, +il: U32, +iu: U32, +iw: U32, +ij: U32, +t1: U32, +t2: U32, +m: C.Cir.Cells, +next: U32,
  +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, U32>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  -m0: C.Cir.Cells, +fs: Nat, +cu: C.Term, +bl: C.Term, +hF: N.Le(345n, U32.to_nat(F)), +hs: N.Le(f0, fs), +fa: In.Fa(m, next, N, F, f0, fc, ks, img),
  +s2: In.St(fs, m, F, N, t2, C.Term.Tup{C.Quan.Q1{}, cu, C.Term.Tup{C.Quan.Q1{}, bl, C.Term.Lab{C.Program.name.unit()}}}, ks, img), fr: In.Fr(m0, m, F),
  -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type,
  g: In.lst.K(fo, ii, ib, iu, iw, ij, 1n+N, F, K, L, I, f0, fc, ks, img, m0, 1n+fs, cu, bl, k, R)) ->
  In.Go(1n+f, C.M.do([In.c.b7()]), In.S(In.R(fo, ii, ib, il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I), k, R):
  In.sq(f, In.c.b7(), C.M.do([]), In.S(In.R(fo, ii, ib, il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I), k, R,
   In.mk(f, C.R.il(), C.M.c(C.M.h.data()), C.M.c(C.I.lab(C.N.con())), C.M.g(C.R.t2()), C.M.c(0), In.R(fo, ii, ib, il, iu, iw, ij, t1, t2), m, next,
    F, K, pg, L, I, In.hd(False{}), 3, t2, 0,
    {==}, {==}, {==}, lt => In.cellNew(next, K, F, lt, Fa.lF(m, next, N, F, f0, fc, ks, img, fa)),
    m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, t => C.Cir.exec.then(C.Cir.exec(1n+f, C.M.do([]), t), k), R,
    +pg3 => +lt3 =>
     In.nop(f, In.S(In.R(fo, ii, ib, next, iu, iw, ij, t1, t2), C.Cir.Cells.set(m, next, C.Cir.Cell{In.hd(False{}), 1, 3, t2, 0}), U32.inc(next), F, K, pg3, L, I), k, R,
       g(next, t1, t2, C.Cir.Cells.set(m, next, C.Cir.Cell{In.hd(False{}), 1, 3, t2, 0}), U32.inc(next), pg3,
         Fa.step(m, next, N, F, f0, fc, ks, img, C.Cir.Cell{In.hd(False{}), 1, 3, t2, 0}, lt3, hF, fa),
         St.cast(1n+fs, C.Cir.Cells.set(m, next, C.Cir.Cell{In.hd(False{}), 1, 3, t2, 0}), F, 1n+N, next,
           C.Term.Tup{C.Quan.Q1{}, C.Term.Lab{C.Program.name.con()}, C.Term.Tup{C.Quan.Q1{}, cu, C.Term.Tup{C.Quan.Q1{}, bl, C.Term.Lab{C.Program.name.unit()}}}},
           C.Program.ctor(C.Program.name.con(), [cu, bl]), ks, img, In.con.eq(cu, bl),
           In.tup(False{}, fs, m, F, N, next, 3, t2, C.Term.Lab{C.Program.name.con()},
             C.Term.Tup{C.Quan.Q1{}, cu, C.Term.Tup{C.Quan.Q1{}, bl, C.Term.Lab{C.Program.name.unit()}}}, ks, img,
             St.to(f0, fs, hs, m, F, N, 3, C.Term.Lab{C.Program.name.con()}, ks, img, Im.g3(f0, m, F, N, ks, img, Fa.im(m, next, N, F, f0, fc, ks, img, fa))),
             s2, Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa), Fa.hr(m, next, N, F, f0, fc, ks, img, hF, fa))),
         Fr.step(m0, m, F, next, C.Cir.Cell{In.hd(False{}), 1, 3, t2, 0}, hF, Fa.lF(m, next, N, F, f0, fc, ks, img, fa), fr)))))

# the list's second make: t2 gets the cell iu in front of the cell t1
def In.lst.b(+f: Nat, +fo: U32, +ii: U32, +ib: U32, +il: U32, +iu: U32, +iw: U32, +ij: U32, +t1: U32, +t2: U32, +m: C.Cir.Cells, +next: U32,
  +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, U32>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  -m0: C.Cir.Cells, +fs: Nat, +cu: C.Term, +bl: C.Term, +hF: N.Le(345n, U32.to_nat(F)), +hs: N.Le(f0, fs), hcs: N.Le(fc, fs),
  +fa: In.Fa(m, next, N, F, f0, fc, ks, img), +su: In.St(fc, m, F, N, iu, cu, ks, img),
  +s1: In.St(fs, m, F, N, t1, C.Term.Tup{C.Quan.Q1{}, bl, C.Term.Lab{C.Program.name.unit()}}, ks, img), fr: In.Fr(m0, m, F),
  -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type,
  g: In.lst.K(fo, ii, ib, iu, iw, ij, 1n+(1n+N), F, K, L, I, f0, fc, ks, img, m0, 1n+(1n+fs), cu, bl, k, R)) ->
  In.Go(1n+f, C.M.do([In.c.b6(), In.c.b7()]), In.S(In.R(fo, ii, ib, il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I), k, R):
  In.sq(f, In.c.b6(), C.M.do([In.c.b7()]), In.S(In.R(fo, ii, ib, il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I), k, R,
   In.mk(f, C.R.t2(), C.M.c(C.M.h.data()), C.M.g(C.R.iu()), C.M.g(C.R.t1()), C.M.c(0), In.R(fo, ii, ib, il, iu, iw, ij, t1, t2), m, next,
    F, K, pg, L, I, In.hd(False{}), iu, t1, 0,
    {==}, {==}, {==}, lt => In.cellNew(next, K, F, lt, Fa.lF(m, next, N, F, f0, fc, ks, img, fa)),
    m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, t => C.Cir.exec.then(C.Cir.exec(1n+f, C.M.do([In.c.b7()]), t), k), R,
    +pg3 => +lt3 =>
     In.lst.c(f, fo, ii, ib, il, iu, iw, ij, t1, next, C.Cir.Cells.set(m, next, C.Cir.Cell{In.hd(False{}), 1, iu, t1, 0}), U32.inc(next), 1n+N,
       F, K, pg3, L, I, f0, fc, ks, img, m0, 1n+fs, cu, bl, hF, N.le_succ(f0, fs, hs),
       Fa.step(m, next, N, F, f0, fc, ks, img, C.Cir.Cell{In.hd(False{}), 1, iu, t1, 0}, lt3, hF, fa),
       In.tup(False{}, fs, m, F, N, next, iu, t1, cu, C.Term.Tup{C.Quan.Q1{}, bl, C.Term.Lab{C.Program.name.unit()}}, ks, img,
         St.to(fc, fs, hcs, m, F, N, iu, cu, ks, img, su), s1, Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa), Fa.hr(m, next, N, F, f0, fc, ks, img, hF, fa)),
       Fr.step(m0, m, F, next, C.Cir.Cell{In.hd(False{}), 1, iu, t1, 0}, hF, Fa.lF(m, next, N, F, f0, fc, ks, img, fa), fr), k, R, g)))

# the list's new cell: il gets Con of the cells iu and il
def In.lst(+f: Nat, +fo: U32, +ii: U32, +ib: U32, +il: U32, +iu: U32, +iw: U32, +ij: U32, +t1: U32, +t2: U32, +m: C.Cir.Cells, +next: U32,
  +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, U32>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  -m0: C.Cir.Cells, +fl: Nat, +cu: C.Term, +bl: C.Term, +hF: N.Le(345n, U32.to_nat(F)), +hl: N.Le(f0, fl), hcl: N.Le(fc, 1n+fl),
  +fa: In.Fa(m, next, N, F, f0, fc, ks, img), +su: In.St(fc, m, F, N, iu, cu, ks, img), +sl: In.St(fl, m, F, N, il, bl, ks, img), fr: In.Fr(m0, m, F),
  -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type,
  g: In.lst.K(fo, ii, ib, iu, iw, ij, 3n+N, F, K, L, I, f0, fc, ks, img, m0, 3n+fl, cu, bl, k, R)) ->
  In.Go(1n+f, C.M.do([In.c.b5(), In.c.b6(), In.c.b7()]), In.S(In.R(fo, ii, ib, il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I), k, R):
  In.sq(f, In.c.b5(), C.M.do([In.c.b6(), In.c.b7()]), In.S(In.R(fo, ii, ib, il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I), k, R,
   In.mk(f, C.R.t1(), C.M.c(C.M.h.data()), C.M.g(C.R.il()), C.M.c(C.I.lab(C.N.unit())), C.M.c(0), In.R(fo, ii, ib, il, iu, iw, ij, t1, t2), m, next,
    F, K, pg, L, I, In.hd(False{}), il, 1, 0,
    {==}, {==}, {==}, lt => In.cellNew(next, K, F, lt, Fa.lF(m, next, N, F, f0, fc, ks, img, fa)),
    m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, t => C.Cir.exec.then(C.Cir.exec(1n+f, C.M.do([In.c.b6(), In.c.b7()]), t), k), R,
    +pg3 => +lt3 =>
     In.lst.b(f, fo, ii, ib, il, iu, iw, ij, next, t2, C.Cir.Cells.set(m, next, C.Cir.Cell{In.hd(False{}), 1, il, 1, 0}), U32.inc(next), 1n+N,
       F, K, pg3, L, I, f0, fc, ks, img, m0, 1n+fl, cu, bl, hF, N.le_succ(f0, fl, hl), hcl,
       Fa.step(m, next, N, F, f0, fc, ks, img, C.Cir.Cell{In.hd(False{}), 1, il, 1, 0}, lt3, hF, fa),
       St.step(fc, m, F, N, iu, cu, ks, img, next, C.Cir.Cell{In.hd(False{}), 1, il, 1, 0}, Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa), su),
       In.tup(False{}, fl, m, F, N, next, il, 1, bl, C.Term.Lab{C.Program.name.unit()}, ks, img, sl,
         St.to(f0, fl, hl, m, F, N, 1, C.Term.Lab{C.Program.name.unit()}, ks, img, Im.g1(f0, m, F, N, ks, img, Fa.im(m, next, N, F, f0, fc, ks, img, fa))),
         Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa), Fa.hr(m, next, N, F, f0, fc, ks, img, hF, fa)),
       Fr.step(m0, m, F, next, C.Cir.Cell{In.hd(False{}), 1, il, 1, 0}, hF, Fa.lF(m, next, N, F, f0, fc, ks, img, fa), fr), k, R, g)))

# The input's bytes
# -----------------

def Bo.and_t(b: Bool) -> {b == Bool.and(b, True{}) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the byte of the low bits of x is x's low byte
def In.and255(x: U32) -> {In.u8(In.low8(x)) == U32.and(x, 255) : U32}:
  match x:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, WCon{+b6, WCon{+b7, +t}}}}}}}}}:
      %Bo.and_t(b0) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}} == U32{WCon{_, WCon{Bool.and(b1, True{}), WCon{Bool.and(b2, True{}), WCon{Bool.and(b3, True{}), WCon{Bool.and(b4, True{}), WCon{Bool.and(b5, True{}), WCon{Bool.and(b6, True{}), WCon{Bool.and(b7, True{}), Word.and(24n, t, Word.zero(24n))}}}}}}}}} : U32}
      %Bo.and_t(b1) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}} == U32{WCon{b0, WCon{_, WCon{Bool.and(b2, True{}), WCon{Bool.and(b3, True{}), WCon{Bool.and(b4, True{}), WCon{Bool.and(b5, True{}), WCon{Bool.and(b6, True{}), WCon{Bool.and(b7, True{}), Word.and(24n, t, Word.zero(24n))}}}}}}}}} : U32}
      %Bo.and_t(b2) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{_, WCon{Bool.and(b3, True{}), WCon{Bool.and(b4, True{}), WCon{Bool.and(b5, True{}), WCon{Bool.and(b6, True{}), WCon{Bool.and(b7, True{}), Word.and(24n, t, Word.zero(24n))}}}}}}}}} : U32}
      %Bo.and_t(b3) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{_, WCon{Bool.and(b4, True{}), WCon{Bool.and(b5, True{}), WCon{Bool.and(b6, True{}), WCon{Bool.and(b7, True{}), Word.and(24n, t, Word.zero(24n))}}}}}}}}} : U32}
      %Bo.and_t(b4) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{_, WCon{Bool.and(b5, True{}), WCon{Bool.and(b6, True{}), WCon{Bool.and(b7, True{}), Word.and(24n, t, Word.zero(24n))}}}}}}}}} : U32}
      %Bo.and_t(b5) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{_, WCon{Bool.and(b6, True{}), WCon{Bool.and(b7, True{}), Word.and(24n, t, Word.zero(24n))}}}}}}}}} : U32}
      %Bo.and_t(b6) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{_, WCon{Bool.and(b7, True{}), Word.and(24n, t, Word.zero(24n))}}}}}}}}} : U32}
      %Bo.and_t(b7) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{_, Word.and(24n, t, Word.zero(24n))}}}}}}}}} : U32}
      %Wd.and_zero(24n, t) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, _}}}}}}}}} : U32}
      {==}

# the element p of I, 0 past its end
def In.nth(I: List<&2, U32>, p: Nat) -> U32:
  Maybe.default(&2, U32, List.get(&2, U32, I, p), 0)

def In.get_at(I: List<&2, U32>, p: Nat, h: N.Le(1n+p, List.length(&2, U32, I))) -> {Some{In.nth(I, p)} == List.get(&2, U32, I, p) : Maybe<&2, U32>}:
  match I:
    case Nil{}:
      Empty.absurd({Some{In.nth([], p)} == List.get(&2, U32, [], p) : Maybe<&2, U32>}, h)
    case Con{x, r}:
      match p:
        case 0n:
          {==}
        case 1n+q:
          In.get_at(r, q, h)

def In.drop0(I: List<&2, U32>) -> {I == List.drop(&2, U32, I, 0n) : List<&2, U32>}:
  match I:
    case Nil{}:
      {==}
    case Con{x, r}:
      {==}

# the list from p on: its element p, then the list from 1 + p on
def In.drop_at(I: List<&2, U32>, p: Nat, h: N.Le(1n+p, List.length(&2, U32, I))) ->
  {Con{In.nth(I, p), List.drop(&2, U32, I, 1n+p)} == List.drop(&2, U32, I, p) : List<&2, U32>}:
  match I:
    case Nil{}:
      Empty.absurd({Con{In.nth([], p), List.drop(&2, U32, [], 1n+p)} == List.drop(&2, U32, [], p) : List<&2, U32>}, h)
    case Con{+x, +r}:
      match p:
        case 0n:
          Equal.cong(List<&2, U32>, List<&2, U32>, y => Con{x, y}, List.drop(&2, U32, r, 0n), r, Equal.sym(List<&2, U32>, r, List.drop(&2, U32, r, 0n), In.drop0(r)))
        case 1n+q:
          In.drop_at(r, q, h)

def In.drop_len(I: List<&2, U32>) -> {[] == List.drop(&2, U32, I, List.length(&2, U32, I)) : List<&2, U32>}:
  match I:
    case Nil{}:
      {==}
    case Con{x, r}:
      In.drop_len(r)

# the input's size
def In.enc_len(I: List<&2, U32>) -> {U32.from_nat(List.length(&2, U32, I)) == C.Wasm.encode.len(U32, I) : U32}:
  match I:
    case Nil{}:
      {==}
    case Con{x, r}:
      Equal.cong(U32, U32, y => U32.inc(y), U32.from_nat(List.length(&2, U32, r)), C.Wasm.encode.len(U32, r), In.enc_len(r))

# the bytes from p on: Con of the byte p and the bytes from 1 + p on
def In.bytes.step(+I: List<&2, U32>, +p: Nat, +x: U32, hd: {Con{x, List.drop(&2, U32, I, 1n+p)} == List.drop(&2, U32, I, p) : List<&2, U32>}) ->
  {C.Program.ctor(C.Program.name.con(), [C.Program.cell.of(In.u8(In.low8(x))), C.Program.bytes(List.drop(&2, U32, I, 1n+p))]) ==
    C.Program.bytes(List.drop(&2, U32, I, p)) : C.Term}:
  %hd : {C.Program.ctor(C.Program.name.con(), [C.Program.cell.of(In.u8(In.low8(x))), C.Program.bytes(List.drop(&2, U32, I, 1n+p))]) == C.Program.bytes(_) : C.Term}
  %In.and255(x) : {C.Program.ctor(C.Program.name.con(), [C.Program.cell.of(In.u8(In.low8(x))), C.Program.bytes(List.drop(&2, U32, I, 1n+p))]) ==
    C.Program.ctor(C.Program.name.con(), [C.Program.cell.of(_), C.Program.bytes(List.drop(&2, U32, I, 1n+p))]) : C.Term}
  {==}

# an entry, by an equation of its byte
def En.cast(-fc: Nat, -m: C.Cir.Cells, -F: U32, -N: Nat, -w: Word(8n), -v: Word(8n), -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>,
  e: {w == v : Word(8n)}, x: In.En(fc, m, F, N, w, ks, img)) -> In.En(fc, m, F, N, v, ks, img):
  %e : In.En(fc, m, F, N, _, ks, img)
  x

# the cache's entry of w8, when it is not 0, stands for its U32
def In.hit(+fc: Nat, +m: C.Cir.Cells, +F: U32, +N: Nat, +w8: Word(8n), +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  eb: {U32.is_eq(C.Cir.Cell.get(2n, C.Cir.Cells.get(m, In.J(w8))), 0) == False{} : Bool}, en: In.En(fc, m, F, N, w8, ks, img)) ->
  In.St(fc, m, F, N, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, In.J(w8))), C.Program.cell.of(In.u8(w8)), ks, img):
  match en:
    case In.Or.l{z}:
      +v = C.Cir.Cell.get(2n, C.Cir.Cells.get(m, In.J(w8)))
      Empty.absurd(In.St(fc, m, F, N, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, In.J(w8))), C.Program.cell.of(In.u8(w8)), ks, img),
        N.true_ne_false(Equal.trans(Bool, True{}, U32.is_eq(v, 0), False{}, Equal.cong(U32, Bool, y => U32.is_eq(y, 0), 0, v, z), eb)))
    case In.Or.r{s}:
      s

# A round of the input's loop
# ---------------------------

def In.c.b1() -> C.Cir.Stmt:
  C.M.set(C.R.ii(), C.M.sub(C.M.g(C.R.ii()), C.M.c(1)))

def In.c.b2() -> C.Cir.Stmt:
  C.M.set(C.R.ib(), C.Cir.Expr.byte{C.M.g(C.R.ii())})

def In.c.b3() -> C.Cir.Stmt:
  C.M.set(C.R.iu(), C.M.f(2n, C.M.add(C.M.c(C.I.cache()), C.M.g(C.R.ib()))))

def In.c.b4() -> C.Cir.Stmt:
  C.M.when(C.M.eq(C.M.g(C.R.iu()), C.M.c(0)), In.c.cache())

def In.c.body() -> C.Cir.Stmt:
  C.M.do([In.c.b1(), In.c.b2(), In.c.b3(), In.c.b4(), In.c.b5(), In.c.b6(), In.c.b7()])

# the byte that the round reads: the low byte of the input's element p
def In.evb(+I: List<&2, U32>, +p: Nat, +M: U32, +hpl: N.Le(1n+p, List.length(&2, U32, I)), +hLM: N.Le(List.length(&2, U32, I), U32.to_nat(M)),
  +fo: U32, +ib: U32, +il: U32, +iu: U32, +iw: U32, +ij: U32, +t1: U32, +t2: U32, +m: C.Cir.Cells, +next: U32, +F: U32, +K: U32, +pg: U32, +L: U32) ->
  {Some{In.u8(In.low8(In.nth(I, p)))} == C.Cir.eval(C.Cir.Expr.byte{C.M.g(C.R.ii())}, In.S(In.R(fo, U32.from_nat(p), ib, il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I)) : Maybe<&2, U32>}:
  +x = In.nth(I, p)
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(p)), p, PM.tofrom(p, M, N.le_trans(p, List.length(&2, U32, I), U32.to_nat(M), N.weaken(p, List.length(&2, U32, I), hpl), hLM))) :
    {Some{In.u8(In.low8(x))} == C.Cir.eval.byte.of(List.get(&2, U32, I, _)) : Maybe<&2, U32>}
  %In.get_at(I, p, hpl) : {Some{In.u8(In.low8(x))} == C.Cir.eval.byte.of(_) : Maybe<&2, U32>}
  %In.and255(x) : {Some{In.u8(In.low8(x))} == Some{_} : Maybe<&2, U32>}
  {==}

# the cache's entry of the byte
def In.evf(+w8: Word(8n), +fo: U32, +ii: U32, +il: U32, +iu: U32, +iw: U32, +ij: U32, +t1: U32, +t2: U32, +m: C.Cir.Cells, +next: U32,
  +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, U32>, hK: N.Le(344n, U32.to_nat(K))) ->
  {Some{C.Cir.Cell.get(2n, C.Cir.Cells.get(m, In.J(w8)))} ==
    C.Cir.eval(C.M.f(2n, C.M.add(C.M.c(C.I.cache()), C.M.g(C.R.ib()))), In.S(In.R(fo, ii, In.u8(w8), il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I)) : Maybe<&2, U32>}:
  %In.cellJ(w8, K, F, next, hK) : {Some{C.Cir.Cell.get(2n, C.Cir.Cells.get(m, In.J(w8)))} == C.Cir.eval.field.if(_, 2n, m, In.J(w8)) : Maybe<&2, U32>}
  {==}

# the test of the cache's entry v
def In.evc(+v: U32, -b: Bool, eb: {U32.is_eq(v, 0) == b : Bool}, +fo: U32, +ii: U32, +ib: U32, +il: U32, +iw: U32, +ij: U32, +t1: U32, +t2: U32,
  +m: C.Cir.Cells, +next: U32, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, U32>) ->
  {Some{Bool.to_u32(b)} == C.Cir.eval(C.M.eq(C.M.g(C.R.iu()), C.M.c(0)), In.S(In.R(fo, ii, ib, il, v, iw, ij, t1, t2), m, next, F, K, pg, L, I)) : Maybe<&2, U32>}:
  %eb : {Some{Bool.to_u32(_)} == C.Cir.eval(C.M.eq(C.M.g(C.R.iu()), C.M.c(0)), In.S(In.R(fo, ii, ib, il, v, iw, ij, t1, t2), m, next, F, K, pg, L, I)) : Maybe<&2, U32>}
  {==}

# what a round of the input's loop gives: the cell il2 of the bytes bp, with
# the fuel fs, in at most 29 new cells
def In.or.K(+fo: U32, +p: Nat, +N: Nat, +F: U32, +K: U32, +L: U32, +I: List<&2, U32>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, -m0: C.Cir.Cells, +fs: Nat, +bp: C.Term, -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type) -> Type:
  @ib2: U32 -> @il2: U32 -> @iu2: U32 -> @iw2: U32 -> @ij2: U32 -> @t12: U32 -> @t22: U32 -> @m2: C.Cir.Cells -> @nx2: U32 -> @N2: Nat -> @pg2: U32 ->
    N.Le(N2, 29n+N) -> In.Fa(m2, nx2, N2, F, f0, fc, ks, img) -> In.St(fs, m2, F, N2, il2, bp, ks, img) -> In.Fr(m0, m2, F) ->
    In.Ok(k(In.S(In.R(fo, U32.from_nat(p), ib2, il2, iu2, iw2, ij2, t12, t22), m2, nx2, F, K, pg2, L, I)), R)

# the round, from the test of the cache's entry on
def In.or.b4(b: Bool, +Z: Nat, +fo: U32, +p: Nat, +w8: Word(8n), +il: U32, +iw: U32, +ij: U32, +t1: U32, +t2: U32, +m: C.Cir.Cells, +next: U32,
  +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, U32>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  -m0: C.Cir.Cells, +fl: Nat, +bl: C.Term, +bp: C.Term, +hF: N.Le(345n, U32.to_nat(F)), +hK: N.Le(344n, U32.to_nat(K)), +hc: N.Le(26n+f0, fc),
  +hcl: N.Le(fc, fl), +fa: In.Fa(m, next, N, F, f0, fc, ks, img), +sl: In.St(fl, m, F, N, il, bl, ks, img), fr: In.Fr(m0, m, F),
  ebl: {C.Program.ctor(C.Program.name.con(), [C.Program.cell.of(In.u8(w8)), bl]) == bp : C.Term},
  +eb: {U32.is_eq(C.Cir.Cell.get(2n, C.Cir.Cells.get(m, In.J(w8))), 0) == b : Bool}, -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type,
  g: In.or.K(fo, p, N, F, K, L, I, f0, fc, ks, img, m0, 3n+fl, bp, k, R)) ->
  In.Go(1n+(8n+Z), C.M.do([In.c.b4(), In.c.b5(), In.c.b6(), In.c.b7()]),
    In.S(In.R(fo, U32.from_nat(p), In.u8(w8), il, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, In.J(w8))), iw, ij, t1, t2), m, next, F, K, pg, L, I), k, R):
  match b:
    case True{}:
      +hl = N.le_trans(f0, fc, fl, N.le_trans(f0, 26n+f0, fc, N.le_add_l(26n, f0), hc), hcl)
      +hcl1 = N.le_succ(fc, fl, hcl)
      In.sq(8n+Z, In.c.b4(), C.M.do([In.c.b5(), In.c.b6(), In.c.b7()]),
       In.S(In.R(fo, U32.from_nat(p), In.u8(w8), il, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, In.J(w8))), iw, ij, t1, t2), m, next, F, K, pg, L, I), k, R,
       In.ifT(8n+Z, C.M.eq(C.M.g(C.R.iu()), C.M.c(0)), In.c.cache(), C.Cir.Stmt.nop{},
        In.S(In.R(fo, U32.from_nat(p), In.u8(w8), il, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, In.J(w8))), iw, ij, t1, t2), m, next, F, K, pg, L, I), 1,
        In.evc(C.Cir.Cell.get(2n, C.Cir.Cells.get(m, In.J(w8))), True{}, eb, fo, U32.from_nat(p), In.u8(w8), il, iw, ij, t1, t2, m, next, F, K, pg, L, I), {==},
        t => C.Cir.exec.then(C.Cir.exec(1n+(8n+Z), C.M.do([In.c.b5(), In.c.b6(), In.c.b7()]), t), k), R,
        In.cch(Z, fo, U32.from_nat(p), w8, il, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, In.J(w8))), iw, ij, t1, t2, m, next, N, F, K, pg, L, I, f0, fc, ks, img,
         m0, fl, bl, hF, hK, hc, fa, sl, fr, t => C.Cir.exec.then(C.Cir.exec(1n+(8n+Z), C.M.do([In.c.b5(), In.c.b6(), In.c.b7()]), t), k), R,
         +iu2 => +iw2 => +ij2 => +t12 => +t22 => +m2 => +nx2 => +pg2 => +fa2 => +su2 => +sl2 => fr2 =>
          In.lst(8n+Z, fo, U32.from_nat(p), In.u8(w8), il, iu2, iw2, ij2, t12, t22, m2, nx2, 26n+N, F, K, pg2, L, I, f0, fc, ks, img, m0, fl,
           C.Program.cell.of(In.u8(w8)), bl, hF, hl, hcl1, fa2, su2, sl2, fr2, k, R,
           +il3 => +t13 => +t23 => +m3 => +nx3 => +pg3 => +fa3 => +sl3 => fr3 =>
            g(In.u8(w8), il3, iu2, iw2, ij2, t13, t23, m3, nx3, 3n+(26n+N), pg3, N.le_refl(29n+N), fa3,
              St.cast(3n+fl, m3, F, 3n+(26n+N), il3, C.Program.ctor(C.Program.name.con(), [C.Program.cell.of(In.u8(w8)), bl]), bp, ks, img, ebl, sl3), fr3)))))
    case False{}:
      +hl = N.le_trans(f0, fc, fl, N.le_trans(f0, 26n+f0, fc, N.le_add_l(26n, f0), hc), hcl)
      +hcl1 = N.le_succ(fc, fl, hcl)
      In.sq(8n+Z, In.c.b4(), C.M.do([In.c.b5(), In.c.b6(), In.c.b7()]),
       In.S(In.R(fo, U32.from_nat(p), In.u8(w8), il, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, In.J(w8))), iw, ij, t1, t2), m, next, F, K, pg, L, I), k, R,
       In.ifF(8n+Z, C.M.eq(C.M.g(C.R.iu()), C.M.c(0)), In.c.cache(), C.Cir.Stmt.nop{},
        In.S(In.R(fo, U32.from_nat(p), In.u8(w8), il, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, In.J(w8))), iw, ij, t1, t2), m, next, F, K, pg, L, I), 0,
        In.evc(C.Cir.Cell.get(2n, C.Cir.Cells.get(m, In.J(w8))), False{}, eb, fo, U32.from_nat(p), In.u8(w8), il, iw, ij, t1, t2, m, next, F, K, pg, L, I), {==},
        t => C.Cir.exec.then(C.Cir.exec(1n+(8n+Z), C.M.do([In.c.b5(), In.c.b6(), In.c.b7()]), t), k), R,
        In.nop(8n+Z, In.S(In.R(fo, U32.from_nat(p), In.u8(w8), il, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, In.J(w8))), iw, ij, t1, t2), m, next, F, K, pg, L, I),
         t => C.Cir.exec.then(C.Cir.exec(1n+(8n+Z), C.M.do([In.c.b5(), In.c.b6(), In.c.b7()]), t), k), R,
         In.lst(8n+Z, fo, U32.from_nat(p), In.u8(w8), il, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, In.J(w8))), iw, ij, t1, t2, m, next, N, F, K, pg, L, I,
          f0, fc, ks, img, m0, fl, C.Program.cell.of(In.u8(w8)), bl, hF, hl, hcl1, fa,
          In.hit(fc, m, F, N, w8, ks, img, eb, En.cast(fc, m, F, N, In.wl(In.push(8n, w8, [])), w8, ks, img,
            Equal.sym(Word(8n), w8, In.wl(In.push(8n, w8, [])), In.wl_push(w8)), CI.get(8n, [], fc, m, F, N, ks, img, w8, Fa.ci(m, next, N, F, f0, fc, ks, img, fa)))),
          sl, fr, k, R,
          +il3 => +t13 => +t23 => +m3 => +nx3 => +pg3 => +fa3 => +sl3 => fr3 =>
           g(In.u8(w8), il3, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, In.J(w8))), iw, ij, t13, t23, m3, nx3, 3n+N, pg3, N.le_add_l(26n, N), fa3,
             St.cast(3n+fl, m3, F, 3n+N, il3, C.Program.ctor(C.Program.name.con(), [C.Program.cell.of(In.u8(w8)), bl]), bp, ks, img, ebl, sl3), fr3)))))

# a round of the input's loop: ii goes down by one to p, and il gets Con of
# the byte p in front
def In.or(+Z: Nat, +fo: U32, +p: Nat, +ib: U32, +il: U32, +iu: U32, +iw: U32, +ij: U32, +t1: U32, +t2: U32, +m: C.Cir.Cells, +next: U32,
  +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, U32>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  -m0: C.Cir.Cells, +fl: Nat, +M: U32, +hF: N.Le(345n, U32.to_nat(F)), +hK: N.Le(344n, U32.to_nat(K)), +hc: N.Le(26n+f0, fc),
  +hcl: N.Le(fc, fl), +hpl: N.Le(1n+p, List.length(&2, U32, I)), +hLM: N.Le(List.length(&2, U32, I), U32.to_nat(M)),
  +fa: In.Fa(m, next, N, F, f0, fc, ks, img), +sl: In.St(fl, m, F, N, il, C.Program.bytes(List.drop(&2, U32, I, 1n+p)), ks, img), fr: In.Fr(m0, m, F),
  -k: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type,
  g: In.or.K(fo, p, N, F, K, L, I, f0, fc, ks, img, m0, 3n+fl, C.Program.bytes(List.drop(&2, U32, I, p)), k, R)) ->
  In.Go(9n+Z, In.c.body(), In.S(In.R(fo, U32.from_nat(1n+p), ib, il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I), k, R):
  In.sq(8n+Z, In.c.b1(), C.M.do([In.c.b2(), In.c.b3(), In.c.b4(), In.c.b5(), In.c.b6(), In.c.b7()]),
   In.S(In.R(fo, U32.from_nat(1n+p), ib, il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I), k, R,
   In.set(8n+Z, C.R.ii(), C.M.sub(C.M.g(C.R.ii()), C.M.c(1)), In.R(fo, U32.from_nat(1n+p), ib, il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I,
    U32.from_nat(p), Equal.cong(U32, Maybe<&2, U32>, z => Some{z}, U32.from_nat(p), U32.sub(U32.inc(U32.from_nat(p)), 1), PI.U32.inc_dec(U32.from_nat(p))), {==},
    t => C.Cir.exec.then(C.Cir.exec(1n+(8n+Z), C.M.do([In.c.b2(), In.c.b3(), In.c.b4(), In.c.b5(), In.c.b6(), In.c.b7()]), t), k), R,
    In.sq(8n+Z, In.c.b2(), C.M.do([In.c.b3(), In.c.b4(), In.c.b5(), In.c.b6(), In.c.b7()]),
     In.S(In.R(fo, U32.from_nat(p), ib, il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I), k, R,
     In.set(8n+Z, C.R.ib(), C.Cir.Expr.byte{C.M.g(C.R.ii())}, In.R(fo, U32.from_nat(p), ib, il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I,
      In.u8(In.low8(In.nth(I, p))), In.evb(I, p, M, hpl, hLM, fo, ib, il, iu, iw, ij, t1, t2, m, next, F, K, pg, L), {==},
      t => C.Cir.exec.then(C.Cir.exec(1n+(8n+Z), C.M.do([In.c.b3(), In.c.b4(), In.c.b5(), In.c.b6(), In.c.b7()]), t), k), R,
      In.sq(8n+Z, In.c.b3(), C.M.do([In.c.b4(), In.c.b5(), In.c.b6(), In.c.b7()]),
       In.S(In.R(fo, U32.from_nat(p), In.u8(In.low8(In.nth(I, p))), il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I), k, R,
       In.set(8n+Z, C.R.iu(), C.M.f(2n, C.M.add(C.M.c(C.I.cache()), C.M.g(C.R.ib()))), In.R(fo, U32.from_nat(p), In.u8(In.low8(In.nth(I, p))), il, iu, iw, ij, t1, t2),
        m, next, F, K, pg, L, I, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, In.J(In.low8(In.nth(I, p))))),
        In.evf(In.low8(In.nth(I, p)), fo, U32.from_nat(p), il, iu, iw, ij, t1, t2, m, next, F, K, pg, L, I, hK), {==},
        t => C.Cir.exec.then(C.Cir.exec(1n+(8n+Z), C.M.do([In.c.b4(), In.c.b5(), In.c.b6(), In.c.b7()]), t), k), R,
        In.or.b4(U32.is_eq(C.Cir.Cell.get(2n, C.Cir.Cells.get(m, In.J(In.low8(In.nth(I, p))))), 0), Z, fo, p, In.low8(In.nth(I, p)), il, iw, ij, t1, t2,
         m, next, N, F, K, pg, L, I, f0, fc, ks, img, m0, fl, C.Program.bytes(List.drop(&2, U32, I, 1n+p)), C.Program.bytes(List.drop(&2, U32, I, p)),
         hF, hK, hc, hcl, fa, sl, fr, In.bytes.step(I, p, In.nth(I, p), In.drop_at(I, p, hpl)), {==}, k, R, g)))))))

# The input's loop
# ----------------

def In.c.OW() -> C.Cir.Stmt:
  C.M.while(C.M.ne(C.M.g(C.R.ii()), C.M.c(0)), In.c.body())

# the fuel of the list after k more rounds, from fl
def In.f3(k: Nat, fl: Nat) -> Nat:
  match k:
    case 0n:
      fl
    case 1n+p:
      In.f3(p, 3n+fl)

def In.f3.ge(k: Nat, +fl: Nat) -> N.Le(fl, In.f3(k, fl)):
  match k:
    case 0n:
      N.le_refl(fl)
    case 1n+(+p):
      N.le_trans(fl, 3n+fl, In.f3(p, 3n+fl), N.le_add_l(3n, fl), In.f3.ge(p, 3n+fl))

# the most cells after k more rounds, from N: 29 a round
def In.cap(k: Nat, N: Nat) -> Nat:
  match k:
    case 0n:
      N
    case 1n+p:
      In.cap(p, 29n+N)

def In.cap.mono(k: Nat, +a: Nat, +b: Nat, h: N.Le(a, b)) -> N.Le(In.cap(k, a), In.cap(k, b)):
  match k:
    case 0n:
      h
    case 1n+(+p):
      In.cap.mono(p, 29n+a, 29n+b, h)

# the test of the input's loop, while ii is 1 + p
def In.evne(+p: Nat, +M: U32, +h: N.Le(1n+p, U32.to_nat(M)), +fo: U32, +ib: U32, +il: U32, +iu: U32, +iw: U32, +ij: U32, +t1: U32, +t2: U32,
  +m: C.Cir.Cells, +next: U32, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, U32>) ->
  {Some{1} == C.Cir.eval(C.M.ne(C.M.g(C.R.ii()), C.M.c(0)), In.S(In.R(fo, U32.from_nat(1n+p), ib, il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I)) : Maybe<&2, U32>}:
  +tf = PM.tofrom(p, M, N.weaken(p, U32.to_nat(M), h))
  +h2 = N.le_rw_l(1n+p, 1n+U32.to_nat(U32.from_nat(p)), U32.to_nat(M),
    Equal.cong(Nat, Nat, q => 1n+q, p, U32.to_nat(U32.from_nat(p)), Equal.sym(Nat, U32.to_nat(U32.from_nat(p)), p, tf)), h)
  %Equal.sym(Bool, U32.is_zero(U32.inc(U32.from_nat(p))), False{}, PM.nz(U32.from_nat(p), M, h2)) :
    {Some{1} == Some{Bool.to_u32(Bool.not(_))} : Maybe<&2, U32>}
  {==}

# what the input's loop gives: the cell il2 of the input's bytes
def In.ol.K(+fo: U32, +k: Nat, +N: Nat, +F: U32, +K: U32, +L: U32, +I: List<&2, U32>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, -m0: C.Cir.Cells, +fs: Nat, -k_: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type) -> Type:
  @ib2: U32 -> @il2: U32 -> @iu2: U32 -> @iw2: U32 -> @ij2: U32 -> @t12: U32 -> @t22: U32 -> @m2: C.Cir.Cells -> @nx2: U32 -> @N2: Nat -> @pg2: U32 ->
    N.Le(N2, In.cap(k, N)) -> In.Fa(m2, nx2, N2, F, f0, fc, ks, img) -> In.St(fs, m2, F, N2, il2, C.Program.bytes(List.drop(&2, U32, I, 0n)), ks, img) ->
    In.Fr(m0, m2, F) -> In.Ok(k_(In.S(In.R(fo, 0, ib2, il2, iu2, iw2, ij2, t12, t22), m2, nx2, F, K, pg2, L, I)), R)

# the input's loop, with k bytes still to read: il holds the bytes from k on
def In.ol(k: Nat, +d: Nat, +fo: U32, +ib: U32, +il: U32, +iu: U32, +iw: U32, +ij: U32, +t1: U32, +t2: U32, +m: C.Cir.Cells, +next: U32,
  +N: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, U32>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  -m0: C.Cir.Cells, +fl: Nat, +M: U32, +hF: N.Le(345n, U32.to_nat(F)), +hK: N.Le(344n, U32.to_nat(K)), +hc: N.Le(26n+f0, fc),
  +hcl: N.Le(fc, fl), +hkl: N.Le(k, List.length(&2, U32, I)), +hLM: N.Le(List.length(&2, U32, I), U32.to_nat(M)),
  +fa: In.Fa(m, next, N, F, f0, fc, ks, img), +sl: In.St(fl, m, F, N, il, C.Program.bytes(List.drop(&2, U32, I, k)), ks, img), fr: In.Fr(m0, m, F),
  -k_: C.Cir.State -> C.Cir.Out, -R: C.Cir.State -> Type,
  g: In.ol.K(fo, k, N, F, K, L, I, f0, fc, ks, img, m0, In.f3(k, fl), k_, R)) ->
  In.Go(10n+Nat.add(k, d), In.c.OW(), In.S(In.R(fo, U32.from_nat(k), ib, il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I), k_, R):
  match k:
    case 0n:
      In.wh.end(9n+d, C.M.ne(C.M.g(C.R.ii()), C.M.c(0)), In.c.body(), In.S(In.R(fo, U32.from_nat(0n), ib, il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I),
        k_, R, {==}, g(ib, il, iu, iw, ij, t1, t2, m, next, N, pg, N.le_refl(N), fa, sl, fr))
    case 1n+(+p):
      In.wh(9n+(1n+Nat.add(p, d)), C.M.ne(C.M.g(C.R.ii()), C.M.c(0)), In.c.body(), In.S(In.R(fo, U32.from_nat(1n+p), ib, il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I),
       k_, R, In.evne(p, M, N.le_trans(1n+p, List.length(&2, U32, I), U32.to_nat(M), hkl, hLM), fo, ib, il, iu, iw, ij, t1, t2, m, next, F, K, pg, L, I),
       In.or(1n+Nat.add(p, d), fo, p, ib, il, iu, iw, ij, t1, t2, m, next, N, F, K, pg, L, I, f0, fc, ks, img, m0, fl, M, hF, hK, hc, hcl, hkl, hLM, fa, sl, fr,
        t => C.Cir.exec.then(C.Cir.exec(9n+(1n+Nat.add(p, d)), In.c.OW(), t), k_), R,
        +ib2 => +il2 => +iu2 => +iw2 => +ij2 => +t12 => +t22 => +m2 => +nx2 => +N2 => +pg2 => +hN2 => +fa2 => +sl2 => fr2 =>
         In.ol(p, d, fo, ib2, il2, iu2, iw2, ij2, t12, t22, m2, nx2, N2, F, K, pg2, L, I, f0, fc, ks, img, m0, 3n+fl, M, hF, hK, hc,
          N.le_succ(fc, 2n+fl, N.le_succ(fc, 1n+fl, N.le_succ(fc, fl, hcl))), N.weaken(p, List.length(&2, U32, I), hkl), hLM, fa2, sl2, fr2, k_, R,
          +ib3 => +il3 => +iu3 => +iw3 => +ij3 => +t13 => +t23 => +m3 => +nx3 => +N3 => +pg3 => hN3 => +fa3 => +sl3 => fr3 =>
           g(ib3, il3, iu3, iw3, ij3, t13, t23, m3, nx3, N3, pg3,
             N.le_trans(N3, In.cap(p, N2), In.cap(p, 29n+N), hN3, In.cap.mono(p, N2, 29n+N, hN2)), fa3, sl3, fr3))))

# M.input
# -------

# a pair of types, and a value with a property
def In.T(-A: Type, -B: Type) -> Type:
  Sigma<&1, &1, A, _ => B>

def In.EU(-B: U32 -> Type) -> Type:
  Sigma<&2, &1, U32, x => B(x)>

def In.EN(-B: Nat -> Type) -> Type:
  Sigma<&2, &1, Nat, x => B(x)>

def In.EC(-B: C.Cir.Cells -> Type) -> Type:
  Sigma<&2, &1, C.Cir.Cells, x => B(x)>

# the end of a run, in a state of which R holds
def In.top(o: C.Cir.Out, -R: C.Cir.State -> Type, h: In.Ok(C.Cir.exec.then(o, t => C.Cir.Out.next{t}), R)) -> In.Ok(o, R):
  match o:
    case C.Cir.Out.next{st}:
      h
    case C.Cir.Out.halt{s, st}:
      h
    case C.Cir.Out.out_of_memory{}:
      h
    case C.Cir.Out.trap{}:
      h
    case C.Cir.Out.not_done{}:
      h

# the term of a state with no frame is its focus's
def In.state(+f: Nat, +fo: U32, +ib: U32, +il: U32, +iu: U32, +iw: U32, +ij: U32, +t1: U32, +t2: U32, +m1: C.Cir.Cells, +nx1: U32, +F: U32,
  +K: U32, +pg1: U32, +L: U32, +I: List<&2, U32>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +t: C.Term,
  e: {Some{t} == T.tm.of(1n+f, m1, ks, img, fo) : Maybe<&2, C.Term>}) ->
  {Some{t} == T.tm.state(1n+f, ks, img, In.S(In.R(fo, 0, ib, il, iu, iw, ij, t1, t2), m1, nx1, F, K, pg1, L, I)) : Maybe<&2, C.Term>}:
  %e : {Some{t} == T.tm.bind(_, u => T.tm.plugs(1n+f, m1, ks, img, 0, u)) : Maybe<&2, C.Term>}
  {==}

# what M.input leaves, by the values of the registers (focus fo; ii, sp, pend
# and mode 0), its cells m1 and its next cell nx1, numbered N1: the start's
# other parts; the term of the state and of the focus, with the fuel ff,
# reading only the image's first 89 cells and the cells from F before N1;
# the image's cells and the cache still stand for their terms; the cells that
# the run keeps (In.kp) are m0's; and N1 is at most ncap
def In.Fin(+fo: U32, +ib: U32, +il: U32, +iu: U32, +iw: U32, +ij: U32, +t1: U32, +t2: U32, +m1: C.Cir.Cells, +nx1: U32, +N1: Nat, +pg1: U32,
  -m0: C.Cir.Cells, +F: U32, +K: U32, +L: U32, +I: List<&2, U32>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +ff: Nat, +ncap: Nat, +st: C.Cir.State) -> Type:
  In.T({st == In.S(In.R(fo, 0, ib, il, iu, iw, ij, t1, t2), m1, nx1, F, K, pg1, L, I) : C.Cir.State},
   In.T({Some{C.Program.start(I)} == T.tm.state(ff, ks, img, st) : Maybe<&2, C.Term>},
    In.T(In.St(ff, m1, F, N1, fo, C.Program.start(I), ks, img),
     In.T(In.Fa(m1, nx1, N1, F, f0, fc, ks, img),
      In.T(In.Fr(m0, m1, F), N.Le(N1, ncap))))))

def In.Post(-m0: C.Cir.Cells, +F: U32, +K: U32, +L: U32, +I: List<&2, U32>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +ff: Nat, +ncap: Nat, +st: C.Cir.State) -> Type:
  In.EU(+fo => In.EU(+ib => In.EU(+il => In.EU(+iu => In.EU(+iw => In.EU(+ij => In.EU(+t1 => In.EU(+t2 =>
    In.EC(+m1 => In.EU(+nx1 => In.EN(+N1 => In.EU(+pg1 =>
      In.Fin(fo, ib, il, iu, iw, ij, t1, t2, m1, nx1, N1, pg1, m0, F, K, L, I, f0, fc, ks, img, ff, ncap, st)))))))))))))

def In.c.s1() -> C.Cir.Stmt:
  C.M.set(C.R.il(), C.M.c(C.I.nil()))

def In.c.s2() -> C.Cir.Stmt:
  C.M.set(C.R.ii(), C.Cir.Expr.size{})

def In.c.s4() -> C.Cir.Stmt:
  C.M.make(C.R.focus(), C.M.c(U32.or(C.T.app(), 64)), C.M.c(C.I.ref_main()), C.M.g(C.R.il()), C.M.c(0))

# the focus: main applied to the list
def In.inp.end(+f: Nat, +ib: U32, +il: U32, +iu: U32, +iw: U32, +ij: U32, +t1: U32, +t2: U32, +m: C.Cir.Cells, +next: U32, +N: Nat,
  +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, U32>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  -m0: C.Cir.Cells, +fl: Nat, +ncap: Nat, +hF: N.Le(345n, U32.to_nat(F)), +hl: N.Le(f0, fl), hN: N.Le(N, ncap),
  +fa: In.Fa(m, next, N, F, f0, fc, ks, img), +sl: In.St(fl, m, F, N, il, C.Program.bytes(List.drop(&2, U32, I, 0n)), ks, img), fr: In.Fr(m0, m, F)) ->
  In.Go(1n+f, C.M.do([In.c.s4()]), In.S(In.R(0, 0, ib, il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I), t => C.Cir.Out.next{t},
    s => In.Post(m0, F, K, L, I, f0, fc, ks, img, 1n+fl, 1n+ncap, s)):
  In.sq(f, In.c.s4(), C.M.do([]), In.S(In.R(0, 0, ib, il, iu, iw, ij, t1, t2), m, next, F, K, pg, L, I), t => C.Cir.Out.next{t},
   s => In.Post(m0, F, K, L, I, f0, fc, ks, img, 1n+fl, 1n+ncap, s),
   In.mk(f, C.R.focus(), C.M.c(U32.or(C.T.app(), 64)), C.M.c(C.I.ref_main()), C.M.g(C.R.il()), C.M.c(0), In.R(0, 0, ib, il, iu, iw, ij, t1, t2), m, next,
    F, K, pg, L, I, 72, 88, il, 0,
    {==}, {==}, {==}, lt => In.cellNew(next, K, F, lt, Fa.lF(m, next, N, F, f0, fc, ks, img, fa)),
    m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==}, m4 => pg4 => {==},
    t => C.Cir.exec.then(C.Cir.exec(1n+f, C.M.do([]), t), u => C.Cir.Out.next{u}), s => In.Post(m0, F, K, L, I, f0, fc, ks, img, 1n+fl, 1n+ncap, s),
    +pg3 => +lt3 =>
     +sf = St.cast(1n+fl, C.Cir.Cells.set(m, next, C.Cir.Cell{72, 1, 88, il, 0}), F, 1n+N, next,
       C.Term.App{C.Quan.Q1{}, C.Term.Ref{C.Program.name.main()}, C.Program.bytes(List.drop(&2, U32, I, 0n))}, C.Program.start(I), ks, img,
       Equal.cong(List<&2, U32>, C.Term, y => C.Term.App{C.Quan.Q1{}, C.Term.Ref{C.Program.name.main()}, C.Program.bytes(y)}, List.drop(&2, U32, I, 0n), I,
         Equal.sym(List<&2, U32>, I, List.drop(&2, U32, I, 0n), In.drop0(I))),
       In.app(fl, m, F, N, next, 88, il, C.Term.Ref{C.Program.name.main()}, C.Program.bytes(List.drop(&2, U32, I, 0n)), ks, img,
         St.to(f0, fl, hl, m, F, N, 88, C.Term.Ref{C.Program.name.main()}, ks, img, Im.g88(f0, m, F, N, ks, img, Fa.im(m, next, N, F, f0, fc, ks, img, fa))),
         sl, Fa.hi(m, next, N, F, f0, fc, ks, img, hF, fa), Fa.hr(m, next, N, F, f0, fc, ks, img, hF, fa)))
     In.nop(f, In.S(In.R(next, 0, ib, il, iu, iw, ij, t1, t2), C.Cir.Cells.set(m, next, C.Cir.Cell{72, 1, 88, il, 0}), U32.inc(next), F, K, pg3, L, I),
      t => C.Cir.Out.next{t}, s => In.Post(m0, F, K, L, I, f0, fc, ks, img, 1n+fl, 1n+ncap, s),
      (next, (ib, (il, (iu, (iw, (ij, (t1, (t2, (C.Cir.Cells.set(m, next, C.Cir.Cell{72, 1, 88, il, 0}), (U32.inc(next), (1n+N, (pg3,
        ({==}, (In.state(fl, next, ib, il, iu, iw, ij, t1, t2, C.Cir.Cells.set(m, next, C.Cir.Cell{72, 1, 88, il, 0}), U32.inc(next), F, K, pg3, L, I,
                 ks, img, C.Program.start(I), In.p1({Some{C.Program.start(I)} == T.tm.of(1n+fl, C.Cir.Cells.set(m, next, C.Cir.Cell{72, 1, 88, il, 0}), ks, img, next) : Maybe<&2, C.Term>},
                   {True{} == In.rds(1n+fl, C.Cir.Cells.set(m, next, C.Cir.Cell{72, 1, 88, il, 0}), F, 1n+N, next) : Bool}, sf)),
         (sf, (Fa.step(m, next, N, F, f0, fc, ks, img, C.Cir.Cell{72, 1, 88, il, 0}, lt3, hF, fa),
          (Fr.step(m0, m, F, next, C.Cir.Cell{72, 1, 88, il, 0}, hF, Fa.lF(m, next, N, F, f0, fc, ks, img, fa), fr), hN))))))))))))))))))))

# M.input, from a state whose cells m stand for the image's terms and whose
# cache is empty or stands for its bytes' U32s: the run makes the focus the
# cell of main applied to the list of the input's bytes, or runs out of memory
def In.inp(+d: Nat, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, U32>, +f0: Nat, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +M: U32, +m: C.Cir.Cells, +hF: N.Le(345n, U32.to_nat(F)), +hK: N.Le(344n, U32.to_nat(K)), +hc: N.Le(26n+f0, fc),
  +hLM: N.Le(List.length(&2, U32, I), U32.to_nat(M)), +fa: In.Fa(m, F, U32.to_nat(F), F, f0, fc, ks, img)) ->
  In.Ok(C.Cir.exec(10n+Nat.add(List.length(&2, U32, I), d), C.M.input(), In.S(In.R(0, 0, 0, 0, 0, 0, 0, 0, 0), m, F, F, K, pg, L, I)),
    s => In.Post(m, F, K, L, I, f0, fc, ks, img, 1n+In.f3(List.length(&2, U32, I), fc), 1n+In.cap(List.length(&2, U32, I), U32.to_nat(F)), s)):
  +len = List.length(&2, U32, I)
  +N0 = U32.to_nat(F)
  +hf = N.le_trans(f0, 26n+f0, fc, N.le_add_l(26n, f0), hc)
  In.top(C.Cir.exec(10n+Nat.add(List.length(&2, U32, I), d), C.M.input(), In.S(In.R(0, 0, 0, 0, 0, 0, 0, 0, 0), m, F, F, K, pg, L, I)),
   s => In.Post(m, F, K, L, I, f0, fc, ks, img, 1n+In.f3(List.length(&2, U32, I), fc), 1n+In.cap(List.length(&2, U32, I), U32.to_nat(F)), s),
   In.sq(9n+Nat.add(List.length(&2, U32, I), d), In.c.s1(), C.M.do([In.c.s2(), In.c.OW(), In.c.s4()]), In.S(In.R(0, 0, 0, 0, 0, 0, 0, 0, 0), m, F, F, K, pg, L, I),
    t => C.Cir.Out.next{t}, s => In.Post(m, F, K, L, I, f0, fc, ks, img, 1n+In.f3(List.length(&2, U32, I), fc), 1n+In.cap(List.length(&2, U32, I), U32.to_nat(F)), s),
    In.set(9n+Nat.add(List.length(&2, U32, I), d), C.R.il(), C.M.c(C.I.nil()), In.R(0, 0, 0, 0, 0, 0, 0, 0, 0), m, F, F, K, pg, L, I, 12, {==}, {==},
     t => C.Cir.exec.then(C.Cir.exec(1n+(9n+Nat.add(List.length(&2, U32, I), d)), C.M.do([In.c.s2(), In.c.OW(), In.c.s4()]), t), u => C.Cir.Out.next{u}),
     s => In.Post(m, F, K, L, I, f0, fc, ks, img, 1n+In.f3(List.length(&2, U32, I), fc), 1n+In.cap(List.length(&2, U32, I), U32.to_nat(F)), s),
     In.sq(9n+Nat.add(List.length(&2, U32, I), d), In.c.s2(), C.M.do([In.c.OW(), In.c.s4()]), In.S(In.R(0, 0, 0, 12, 0, 0, 0, 0, 0), m, F, F, K, pg, L, I),
      t => C.Cir.Out.next{t}, s => In.Post(m, F, K, L, I, f0, fc, ks, img, 1n+In.f3(List.length(&2, U32, I), fc), 1n+In.cap(List.length(&2, U32, I), U32.to_nat(F)), s),
      In.set(9n+Nat.add(List.length(&2, U32, I), d), C.R.ii(), C.Cir.Expr.size{}, In.R(0, 0, 0, 12, 0, 0, 0, 0, 0), m, F, F, K, pg, L, I,
       U32.from_nat(List.length(&2, U32, I)),
       Equal.cong(U32, Maybe<&2, U32>, z => Some{z}, U32.from_nat(List.length(&2, U32, I)), C.Wasm.encode.len(U32, I), In.enc_len(I)), {==},
       t => C.Cir.exec.then(C.Cir.exec(1n+(9n+Nat.add(List.length(&2, U32, I), d)), C.M.do([In.c.OW(), In.c.s4()]), t), u => C.Cir.Out.next{u}),
       s => In.Post(m, F, K, L, I, f0, fc, ks, img, 1n+In.f3(List.length(&2, U32, I), fc), 1n+In.cap(List.length(&2, U32, I), U32.to_nat(F)), s),
       In.sq(9n+Nat.add(List.length(&2, U32, I), d), In.c.OW(), C.M.do([In.c.s4()]),
        In.S(In.R(0, U32.from_nat(List.length(&2, U32, I)), 0, 12, 0, 0, 0, 0, 0), m, F, F, K, pg, L, I),
        t => C.Cir.Out.next{t}, s => In.Post(m, F, K, L, I, f0, fc, ks, img, 1n+In.f3(List.length(&2, U32, I), fc), 1n+In.cap(List.length(&2, U32, I), U32.to_nat(F)), s),
        In.ol(List.length(&2, U32, I), d, 0, 0, 12, 0, 0, 0, 0, 0, m, F, U32.to_nat(F), F, K, pg, L, I, f0, fc, ks, img, m, fc, M, hF, hK, hc,
         N.le_refl(fc), N.le_refl(List.length(&2, U32, I)), hLM, fa,
         St.cast(fc, m, F, U32.to_nat(F), 12, C.Program.bytes([]), C.Program.bytes(List.drop(&2, U32, I, List.length(&2, U32, I))), ks, img,
           Equal.cong(List<&2, U32>, C.Term, y => C.Program.bytes(y), [], List.drop(&2, U32, I, List.length(&2, U32, I)), In.drop_len(I)),
           St.to(f0, fc, hf, m, F, U32.to_nat(F), 12, C.Program.bytes([]), ks, img, Im.g12(f0, m, F, U32.to_nat(F), ks, img, Fa.im(m, F, U32.to_nat(F), F, f0, fc, ks, img, fa)))),
         Fr.refl(m, F),
         t => C.Cir.exec.then(C.Cir.exec(1n+(9n+Nat.add(List.length(&2, U32, I), d)), C.M.do([In.c.s4()]), t), u => C.Cir.Out.next{u}),
         s => In.Post(m, F, K, L, I, f0, fc, ks, img, 1n+In.f3(List.length(&2, U32, I), fc), 1n+In.cap(List.length(&2, U32, I), U32.to_nat(F)), s),
         +ib2 => +il2 => +iu2 => +iw2 => +ij2 => +t12 => +t22 => +m2 => +nx2 => +N2 => +pg2 => hN => +fa2 => +sl2 => fr2 =>
          In.inp.end(9n+Nat.add(List.length(&2, U32, I), d), ib2, il2, iu2, iw2, ij2, t12, t22, m2, nx2, N2, F, K, pg2, L, I, f0, fc, ks, img, m,
            In.f3(List.length(&2, U32, I), fc), In.cap(List.length(&2, U32, I), U32.to_nat(F)), hF,
            N.le_trans(f0, fc, In.f3(List.length(&2, U32, I), fc), hf, In.f3.ge(List.length(&2, U32, I), fc)), hN, fa2, sl2, fr2))))))))

# Numbers, once more
# ------------------

# 0 is no successor
def Na.dz(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

def Na.zs(-x: Nat, e: {0n == 1n+x : Nat}) -> Empty:
  %e : Na.dz(_)
  Unit{}

def Na.pr(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def Na.dbl_inj(a: Nat, b: Nat, e: {Nat.double(a) == Nat.double(b) : Nat}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      Empty.absurd({0n == 1n+y : Nat}, Na.zs(1n+Nat.double(y), e))
    case 1n+x 0n:
      Empty.absurd({1n+x == 0n : Nat}, Na.zs(1n+Nat.double(x), Equal.sym(Nat, 2n+Nat.double(x), 0n, e)))
    case 1n+(+x) 1n+(+y):
      Equal.cong(Nat, Nat, z => 1n+z, x, y, Na.dbl_inj(x, y, Equal.cong(Nat, Nat, z => Na.pr(Na.pr(z)), 2n+Nat.double(x), 2n+Nat.double(y), e)))

def Na.dbl_odd(a: Nat, b: Nat, e: {Nat.double(a) == 1n+Nat.double(b) : Nat}) -> Empty:
  match a b:
    case 0n _:
      Na.zs(Nat.double(b), e)
    case 1n+x 0n:
      Na.zs(Nat.double(x), Equal.sym(Nat, 1n+Nat.double(x), 0n, Equal.cong(Nat, Nat, z => Na.pr(z), 2n+Nat.double(x), 1n, e)))
    case 1n+(+x) 1n+(+y):
      Na.dbl_odd(x, y, Equal.cong(Nat, Nat, z => Na.pr(Na.pr(z)), 2n+Nat.double(x), 3n+Nat.double(y), e))

# two words of the same number are one
def Wd.inj(n: Nat, a: Word(n), b: Word(n), e: {Word.to_nat(n, a) == Word.to_nat(n, b) : Nat}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b:
        case WCon{False{}, +s} WCon{False{}, +t}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, s, t,
            Wd.inj(p, s, t, Na.dbl_inj(Word.to_nat(p, s), Word.to_nat(p, t), e)))
        case WCon{True{}, +s} WCon{True{}, +t}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, s, t,
            Wd.inj(p, s, t, Na.dbl_inj(Word.to_nat(p, s), Word.to_nat(p, t),
              Equal.cong(Nat, Nat, z => Na.pr(z), 1n+Nat.double(Word.to_nat(p, s)), 1n+Nat.double(Word.to_nat(p, t)), e))))
        case WCon{False{}, +s} WCon{True{}, +t}:
          Empty.absurd({WCon{False{}, s} == WCon{True{}, t} : Word(1n+p)}, Na.dbl_odd(Word.to_nat(p, s), Word.to_nat(p, t), e))
        case WCon{True{}, +s} WCon{False{}, +t}:
          Empty.absurd({WCon{True{}, s} == WCon{False{}, t} : Word(1n+p)},
            Na.dbl_odd(Word.to_nat(p, t), Word.to_nat(p, s), Equal.sym(Nat, 1n+Nat.double(Word.to_nat(p, s)), Nat.double(Word.to_nat(p, t)), e)))

def U.inj(a: U32, b: U32, e: {U32.to_nat(a) == U32.to_nat(b) : Nat}) -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      Equal.cong(Word(32n), U32, z => U32{z}, x, y, Wd.inj(32n, x, y, e))

def Na.le_split.of(+x: Nat, +y: Nat, r: In.Or<{x == y : Nat}, N.Le(1n+x, y)>) -> In.Or<{1n+x == 1n+y : Nat}, N.Le(2n+x, 1n+y)>:
  match r:
    case In.Or.l{e}:
      In.Or.l{Equal.cong(Nat, Nat, z => 1n+z, x, y, e)}
    case In.Or.r{h}:
      In.Or.r{h}

# a <= b: a is b, or below it
def Na.le_split(a: Nat, b: Nat, h: N.Le(a, b)) -> In.Or<{a == b : Nat}, N.Le(1n+a, b)>:
  match a b:
    case 0n 0n:
      In.Or.l{{==}}
    case 0n 1n+y:
      In.Or.r{N.le_zero(y)}
    case 1n+x 0n:
      Empty.absurd(In.Or<{1n+x == 0n : Nat}, N.Le(2n+x, 0n)>, h)
    case 1n+(+x) 1n+(+y):
      Na.le_split.of(x, y, Na.le_split(x, y, h))


# The start's cells
# -----------------

# the image's cells 1 to 88, with main's body at the cell main
def In.p88(+main: U32) -> List<&2, C.Cir.Cell>:
  C.Img.labels(11n, 0,
    C.Img.pair(C.I.lab(C.N.nil()), C.I.lab(C.N.unit()), C.Img.pair(C.I.lab(C.N.true()), C.I.lab(C.N.unit()),
    C.Img.pair(C.I.lab(C.N.false()), C.I.lab(C.N.unit()), C.Img.pair(C.I.lab(C.N.wnil()), C.I.lab(C.N.unit()),
    C.Img.zeros24(24n, 24, C.I.z24(), C.Img.cell(1025, main, C.N.main(), 0, [])))))))

# and to 344, the cache's
def In.p344(+main: U32) -> List<&2, C.Cir.Cell>:
  List.append(&2, C.Cir.Cell, In.p88(main), C.Img.blank(256n, []))

def In.m88(+main: U32) -> C.Cir.Cells:
  C.Cir.load(In.p88(main), 1, C.Cir.Cells.none{})

def In.m344(+main: U32) -> C.Cir.Cells:
  C.Cir.load(In.p344(main), 1, C.Cir.Cells.none{})


# the image's cells that the machine points to, with the fuel 80
def Im.m88(+main: U32, +F: U32, +N: Nat, +ds: List<&2, C.Def>) -> In.Im(80n, In.m88(main), F, N, T.tm.names(ds), T.tm.img(ds)):
  (({==}, {==}), (({==}, {==}), (({==}, {==}), (({==}, {==}), (({==}, {==}), (({==}, {==}), (({==}, {==}), (({==}, {==}), ({==}, {==})))))))))

# Loads
# -----

# the cell after i, when the cells from i on stay below M
def Ld.einc(+i: U32, +n: Nat, +M: U32, hov: N.Le(Nat.add(U32.to_nat(i), 1n+n), U32.to_nat(M))) -> {U32.to_nat(U32.inc(i)) == 1n+U32.to_nat(i) : Nat}:
  +ti = U32.to_nat(i)
  +h1 = N.le_rw_l(Nat.add(ti, 1n+n), 1n+Nat.add(ti, n), U32.to_nat(M), N.add_succ_r(ti, n), hov)
  +h2 = N.le_trans(1n+ti, 1n+Nat.add(ti, n), U32.to_nat(M), N.le_add_r(ti, n), h1)
  PI.U32.inc_nat(i, Equal.sym(Bool, U32.is_zero(U32.inc(i)), False{}, PM.nz(i, M, h2)))

def Ld.hov(+i: U32, +n: Nat, +M: U32, +hov: N.Le(Nat.add(U32.to_nat(i), 1n+n), U32.to_nat(M))) -> N.Le(Nat.add(U32.to_nat(U32.inc(i)), n), U32.to_nat(M)):
  +ti = U32.to_nat(i)
  %Equal.sym(Nat, U32.to_nat(U32.inc(i)), 1n+ti, Ld.einc(i, n, M, hov)) : N.Le(Nat.add(_, n), U32.to_nat(M))
  N.le_rw_l(Nat.add(ti, 1n+n), 1n+Nat.add(ti, n), U32.to_nat(M), N.add_succ_r(ti, n), hov)

# a load from i on keeps the cells below i
def Ld.keep(cs: List<&2, C.Cir.Cell>, +i: U32, +m: C.Cir.Cells, +j: U32, +M: U32, hj: N.Le(1n+U32.to_nat(j), U32.to_nat(i)),
  +hov: N.Le(Nat.add(U32.to_nat(i), List.length(&2, C.Cir.Cell, cs)), U32.to_nat(M))) ->
  {C.Cir.Cells.get(m, j) == C.Cir.Cells.get(C.Cir.load(cs, i, m), j) : C.Cir.Cell}:
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      +tj = U32.to_nat(j)
      +ti = U32.to_nat(i)
      +hj1 = hj
      +hj2 = N.le_rw_r(1n+tj, 1n+ti, U32.to_nat(U32.inc(i)), Equal.sym(Nat, U32.to_nat(U32.inc(i)), 1n+ti, Ld.einc(i, List.length(&2, C.Cir.Cell, rest), M, hov)),
        N.le_succ(1n+tj, ti, hj1))
      Equal.trans(C.Cir.Cell, C.Cir.Cells.get(m, j), C.Cir.Cells.get(C.Cir.Cells.set(m, i, c), j),
        C.Cir.Cells.get(C.Cir.load(rest, U32.inc(i), C.Cir.Cells.set(m, i, c)), j),
        Cl.get_other(m, j, i, c, e => N.not_succ_le(ti, N.le_rw_l(1n+tj, 1n+ti, ti, Equal.cong(U32, Nat, z => 1n+U32.to_nat(z), j, i, e), hj1))),
        Ld.keep(rest, U32.inc(i), C.Cir.Cells.set(m, i, c), j, M, hj2, Ld.hov(i, List.length(&2, C.Cir.Cell, rest), M, hov)))

def Ld.blen(q: Nat) -> {List.length(&2, C.Cir.Cell, C.Img.blank(q, [])) == q : Nat}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, C.Cir.Cell, C.Img.blank(p, [])), p, Ld.blen(p))

# field 2 of the zero cell set at i, read at j = i
def Ld.z.at(+m: C.Cir.Cells, +i: U32, +j: U32, eij: {i == j : U32}) ->
  {0 == C.Cir.Cell.get(2n, C.Cir.Cells.get(C.Cir.Cells.set(m, i, C.Cir.Cell{0, 0, 0, 0, 0}), j)) : U32}:
  %eij : {0 == C.Cir.Cell.get(2n, C.Cir.Cells.get(C.Cir.Cells.set(m, i, C.Cir.Cell{0, 0, 0, 0, 0}), _)) : U32}
  %Equal.sym(C.Cir.Cell, C.Cir.Cells.get(C.Cir.Cells.set(m, i, C.Cir.Cell{0, 0, 0, 0, 0}), i), C.Cir.Cell{0, 0, 0, 0, 0}, Cl.get_set(m, i, C.Cir.Cell{0, 0, 0, 0, 0})) :
    {0 == C.Cir.Cell.get(2n, _) : U32}
  {==}

def Ld.zero.go(+q: Nat, +i: U32, +m: C.Cir.Cells, +j: U32, +M: U32, r: In.Or<{U32.to_nat(i) == U32.to_nat(j) : Nat}, N.Le(1n+U32.to_nat(i), U32.to_nat(j))>,
  +hov: N.Le(Nat.add(U32.to_nat(i), 1n+q), U32.to_nat(M)),
  ih: N.Le(U32.to_nat(U32.inc(i)), U32.to_nat(j)) -> {0 == C.Cir.Cell.get(2n, C.Cir.Cells.get(C.Cir.load(C.Img.blank(q, []), U32.inc(i), C.Cir.Cells.set(m, i, C.Cir.Cell{0, 0, 0, 0, 0})), j)) : U32}) ->
  {0 == C.Cir.Cell.get(2n, C.Cir.Cells.get(C.Cir.load(C.Img.blank(q, []), U32.inc(i), C.Cir.Cells.set(m, i, C.Cir.Cell{0, 0, 0, 0, 0})), j)) : U32}:
  match r:
    case In.Or.l{+e}:
      +ei = Ld.einc(i, q, M, hov)
      +ms = C.Cir.Cells.set(m, i, C.Cir.Cell{0, 0, 0, 0, 0})
      +hj = N.le_rw_r(1n+U32.to_nat(j), 1n+U32.to_nat(i), U32.to_nat(U32.inc(i)), Equal.sym(Nat, U32.to_nat(U32.inc(i)), 1n+U32.to_nat(i), ei),
        N.le_rw_l(1n+U32.to_nat(i), 1n+U32.to_nat(j), 1n+U32.to_nat(i), Equal.cong(Nat, Nat, z => 1n+z, U32.to_nat(i), U32.to_nat(j), e), N.le_refl(1n+U32.to_nat(i))))
      +hv = N.le_rw_l(Nat.add(U32.to_nat(U32.inc(i)), q), Nat.add(U32.to_nat(U32.inc(i)), List.length(&2, C.Cir.Cell, C.Img.blank(q, []))), U32.to_nat(M),
        Equal.cong(Nat, Nat, z => Nat.add(U32.to_nat(U32.inc(i)), z), q, List.length(&2, C.Cir.Cell, C.Img.blank(q, [])),
          Equal.sym(Nat, List.length(&2, C.Cir.Cell, C.Img.blank(q, [])), q, Ld.blen(q))), Ld.hov(i, q, M, hov))
      Equal.trans(U32, 0, C.Cir.Cell.get(2n, C.Cir.Cells.get(C.Cir.Cells.set(m, i, C.Cir.Cell{0, 0, 0, 0, 0}), j)),
        C.Cir.Cell.get(2n, C.Cir.Cells.get(C.Cir.load(C.Img.blank(q, []), U32.inc(i), C.Cir.Cells.set(m, i, C.Cir.Cell{0, 0, 0, 0, 0})), j)),
        Ld.z.at(m, i, j, U.inj(i, j, e)),
        Equal.cong(C.Cir.Cell, U32, y => C.Cir.Cell.get(2n, y), C.Cir.Cells.get(C.Cir.Cells.set(m, i, C.Cir.Cell{0, 0, 0, 0, 0}), j),
          C.Cir.Cells.get(C.Cir.load(C.Img.blank(q, []), U32.inc(i), C.Cir.Cells.set(m, i, C.Cir.Cell{0, 0, 0, 0, 0})), j),
          Ld.keep(C.Img.blank(q, []), U32.inc(i), C.Cir.Cells.set(m, i, C.Cir.Cell{0, 0, 0, 0, 0}), j, M, hj, hv)))
    case In.Or.r{h}:
      +ei = Ld.einc(i, q, M, hov)
      ih(N.le_rw_l(1n+U32.to_nat(i), U32.to_nat(U32.inc(i)), U32.to_nat(j), Equal.sym(Nat, U32.to_nat(U32.inc(i)), 1n+U32.to_nat(i), ei), h))

# a load of n zero cells from i: field 2 of each of them is 0
def Ld.zero(n: Nat, +i: U32, +m: C.Cir.Cells, +j: U32, +M: U32, +h1: N.Le(U32.to_nat(i), U32.to_nat(j)),
  +h2: N.Le(1n+U32.to_nat(j), Nat.add(U32.to_nat(i), n)), +hov: N.Le(Nat.add(U32.to_nat(i), n), U32.to_nat(M))) ->
  {0 == C.Cir.Cell.get(2n, C.Cir.Cells.get(C.Cir.load(C.Img.blank(n, []), i, m), j)) : U32}:
  match n:
    case 0n:
      Empty.absurd({0 == C.Cir.Cell.get(2n, C.Cir.Cells.get(C.Cir.load(C.Img.blank(0n, []), i, m), j)) : U32},
        N.not_succ_le(U32.to_nat(j), N.le_trans(1n+U32.to_nat(j), U32.to_nat(i), U32.to_nat(j),
          N.le_rw_r(1n+U32.to_nat(j), Nat.add(U32.to_nat(i), 0n), U32.to_nat(i), N.add_zero(U32.to_nat(i)), h2), h1)))
    case 1n+(+q):
      +ei = Ld.einc(i, q, M, hov)
      Ld.zero.go(q, i, m, j, M, Na.le_split(U32.to_nat(i), U32.to_nat(j), h1), hov,
        h => Ld.zero(q, U32.inc(i), C.Cir.Cells.set(m, i, C.Cir.Cell{0, 0, 0, 0, 0}), j, M, h,
          N.le_rw_r(1n+U32.to_nat(j), 1n+Nat.add(U32.to_nat(i), q), Nat.add(U32.to_nat(U32.inc(i)), q),
            Equal.cong(Nat, Nat, z => Nat.add(z, q), 1n+U32.to_nat(i), U32.to_nat(U32.inc(i)), Equal.sym(Nat, U32.to_nat(U32.inc(i)), 1n+U32.to_nat(i), ei)),
            N.le_rw_r(1n+U32.to_nat(j), Nat.add(U32.to_nat(i), 1n+q), 1n+Nat.add(U32.to_nat(i), q), N.add_succ_r(U32.to_nat(i), q), h2)),
          Ld.hov(i, q, M, hov)))

# the cells xs then ys, loaded from i
def In.adv(xs: List<&2, C.Cir.Cell>, +i: U32) -> U32:
  match xs:
    case Nil{}:
      i
    case Con{_, r}:
      In.adv(r, U32.inc(i))

def Ld.app(xs: List<&2, C.Cir.Cell>, +ys: List<&2, C.Cir.Cell>, +i: U32, +m: C.Cir.Cells) ->
  {C.Cir.load(List.append(&2, C.Cir.Cell, xs, ys), i, m) == C.Cir.load(ys, In.adv(xs, i), C.Cir.load(xs, i, m)) : C.Cir.Cells}:
  match xs:
    case Nil{}:
      {==}
    case Con{+c, r}:
      Ld.app(r, ys, U32.inc(i), C.Cir.Cells.set(m, i, c))

# The start's facts
# -----------------

def Na.and_le_lt(a: Nat, b: Nat) -> {False{} == Bool.and(Nat.is_le(a, b), Nat.is_lt(b, a)) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+x 0n:
      {==}
    case 1n+x 1n+y:
      Na.and_le_lt(x, y)

# at the start (N is F), a cell from 89 on may not be read
def In.rd0(+j: U32, +F: U32, h89: N.Le(89n, U32.to_nat(j))) -> {False{} == In.rd(j, F, U32.to_nat(F)) : Bool}:
  +tj = U32.to_nat(j)
  +tF = U32.to_nat(F)
  %Na.lt_f(tj, 89n, h89) : {False{} == Bool.or(_, Bool.and(Nat.is_le(tF, tj), Nat.is_lt(tj, tF))) : Bool}
  Na.and_le_lt(tF, tj)

# a load from 89 on keeps what the image's cells that the machine points to
# stand for
def Im.load(cs: List<&2, C.Cir.Cell>, +i: U32, +m: C.Cir.Cells, +F: U32, +f0: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +M: U32,
  h89: N.Le(89n, U32.to_nat(i)), +hov: N.Le(Nat.add(U32.to_nat(i), List.length(&2, C.Cir.Cell, cs)), U32.to_nat(M)),
  im: In.Im(f0, m, F, U32.to_nat(F), ks, img)) -> In.Im(f0, C.Cir.load(cs, i, m), F, U32.to_nat(F), ks, img):
  match cs:
    case Nil{}:
      im
    case Con{+c, +rest}:
      +h89b = h89
      +ei = Ld.einc(i, List.length(&2, C.Cir.Cell, rest), M, hov)
      Im.load(rest, U32.inc(i), C.Cir.Cells.set(m, i, c), F, f0, ks, img, M,
        N.le_rw_r(89n, 1n+U32.to_nat(i), U32.to_nat(U32.inc(i)), Equal.sym(Nat, U32.to_nat(U32.inc(i)), 1n+U32.to_nat(i), ei), N.le_succ(89n, U32.to_nat(i), h89b)),
        Ld.hov(i, List.length(&2, C.Cir.Cell, rest), M, hov),
        Im.fr(f0, m, F, U32.to_nat(F), ks, img, i, c, In.rd0(i, F, h89b), im))

# a load from 345 on keeps the cache's entries
def CI.load(cs: List<&2, C.Cir.Cell>, +i: U32, +m: C.Cir.Cells, +F: U32, +fc: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +M: U32,
  h345: N.Le(345n, U32.to_nat(i)), +hov: N.Le(Nat.add(U32.to_nat(i), List.length(&2, C.Cir.Cell, cs)), U32.to_nat(M)),
  ci: In.CI(8n, [], fc, m, F, U32.to_nat(F), ks, img)) -> In.CI(8n, [], fc, C.Cir.load(cs, i, m), F, U32.to_nat(F), ks, img):
  match cs:
    case Nil{}:
      ci
    case Con{+c, +rest}:
      +hb = h345
      +ei = Ld.einc(i, List.length(&2, C.Cir.Cell, rest), M, hov)
      CI.load(rest, U32.inc(i), C.Cir.Cells.set(m, i, c), F, fc, ks, img, M,
        N.le_rw_r(345n, 1n+U32.to_nat(i), U32.to_nat(U32.inc(i)), Equal.sym(Nat, U32.to_nat(U32.inc(i)), 1n+U32.to_nat(i), ei), N.le_succ(345n, U32.to_nat(i), hb)),
        Ld.hov(i, List.length(&2, C.Cir.Cell, rest), M, hov),
        CI.fr(8n, [], fc, m, F, U32.to_nat(F), ks, img, i, c, In.rd0(i, F, N.le_trans(89n, 345n, U32.to_nat(i), Unit{}, hb)), hb, ci))

# the cache of the image is empty
def In.cz(+main: U32, +w: Word(8n)) -> {0 == C.Cir.Cell.get(2n, C.Cir.Cells.get(In.m344(main), In.J(w))) : U32}:
  %Equal.sym(C.Cir.Cells, C.Cir.load(In.p344(main), 1, C.Cir.Cells.none{}), C.Cir.load(C.Img.blank(256n, []), In.adv(In.p88(main), 1), In.m88(main)),
    Ld.app(In.p88(main), C.Img.blank(256n, []), 1, C.Cir.Cells.none{})) :
    {0 == C.Cir.Cell.get(2n, C.Cir.Cells.get(_, In.J(w))) : U32}
  Ld.zero(256n, In.adv(In.p88(main), 1), In.m88(main), In.J(w), 345, In.Jlo(w), In.Jhi(w), Unit{})

def CI.z(n: Nat, +bs: List<&2, Bool>, +fc: Nat, +main: U32, +F: U32, +N: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>) ->
  In.CI(n, bs, fc, In.m344(main), F, N, ks, img):
  match n:
    case 0n:
      In.Or.l{In.cz(main, In.wl(bs))}
    case 1n+(+p):
      (CI.z(p, Con{False{}, bs}, fc, main, F, N, ks, img), CI.z(p, Con{True{}, bs}, fc, main, F, N, ks, img))

# the image's cells, cut after cell 88 and after cell 344
def In.pre88.eq(+main: U32, +acc: List<&2, C.Cir.Cell>) ->
  {C.Img.prefix(main, acc) == List.append(&2, C.Cir.Cell, In.p88(main), C.Img.blank(256n, C.Img.table(acc))) : List<&2, C.Cir.Cell>}:
  {==}

def In.pre344.eq(+main: U32, +acc: List<&2, C.Cir.Cell>) ->
  {C.Img.prefix(main, acc) == List.append(&2, C.Cir.Cell, In.p344(main), C.Img.table(acc)) : List<&2, C.Cir.Cell>}:
  {==}

# the main def's body, and the cells of the book's bodies
def In.main(+ds: List<&2, C.Def>) -> U32:
  C.Img.ref(C.Img.defs(ds, C.I.book()), C.Program.name.main())

def In.bodies(+ds: List<&2, C.Def>) -> List<&2, C.Cir.Cell>:
  C.Img.bodies(ds, C.Img.known(C.Img.names.defs(ds)), C.Img.defs(ds, C.I.book()), C.I.book())

def In.cells.eq(+ds: List<&2, C.Def>) -> {C.Img.cells(ds) == C.Img.prefix(In.main(ds), In.bodies(ds)) : List<&2, C.Cir.Cell>}:
  {==}

# the start's cells, from cell 89 on and from cell 345 on
def In.e88(+ds: List<&2, C.Def>) ->
  {C.Cir.load(C.Img.blank(256n, C.Img.table(In.bodies(ds))), In.adv(In.p88(In.main(ds)), 1), In.m88(In.main(ds))) ==
    C.Cir.load(C.Img.cells(ds), 1, C.Cir.Cells.none{}) : C.Cir.Cells}:
  %Equal.sym(List<&2, C.Cir.Cell>, C.Img.cells(ds), C.Img.prefix(In.main(ds), In.bodies(ds)), In.cells.eq(ds)) :
    {C.Cir.load(C.Img.blank(256n, C.Img.table(In.bodies(ds))), In.adv(In.p88(In.main(ds)), 1), In.m88(In.main(ds))) == C.Cir.load(_, 1, C.Cir.Cells.none{}) : C.Cir.Cells}
  %Equal.sym(List<&2, C.Cir.Cell>, C.Img.prefix(In.main(ds), In.bodies(ds)),
    List.append(&2, C.Cir.Cell, In.p88(In.main(ds)), C.Img.blank(256n, C.Img.table(In.bodies(ds)))), In.pre88.eq(In.main(ds), In.bodies(ds))) :
    {C.Cir.load(C.Img.blank(256n, C.Img.table(In.bodies(ds))), In.adv(In.p88(In.main(ds)), 1), In.m88(In.main(ds))) == C.Cir.load(_, 1, C.Cir.Cells.none{}) : C.Cir.Cells}
  Equal.sym(C.Cir.Cells, C.Cir.load(List.append(&2, C.Cir.Cell, In.p88(In.main(ds)), C.Img.blank(256n, C.Img.table(In.bodies(ds)))), 1, C.Cir.Cells.none{}), C.Cir.load(C.Img.blank(256n, C.Img.table(In.bodies(ds))), In.adv(In.p88(In.main(ds)), 1), In.m88(In.main(ds))),
    Ld.app(In.p88(In.main(ds)), C.Img.blank(256n, C.Img.table(In.bodies(ds))), 1, C.Cir.Cells.none{}))

def In.e344(+ds: List<&2, C.Def>) ->
  {C.Cir.load(C.Img.table(In.bodies(ds)), In.adv(In.p344(In.main(ds)), 1), In.m344(In.main(ds))) ==
    C.Cir.load(C.Img.cells(ds), 1, C.Cir.Cells.none{}) : C.Cir.Cells}:
  %Equal.sym(List<&2, C.Cir.Cell>, C.Img.cells(ds), C.Img.prefix(In.main(ds), In.bodies(ds)), In.cells.eq(ds)) :
    {C.Cir.load(C.Img.table(In.bodies(ds)), In.adv(In.p344(In.main(ds)), 1), In.m344(In.main(ds))) == C.Cir.load(_, 1, C.Cir.Cells.none{}) : C.Cir.Cells}
  %Equal.sym(List<&2, C.Cir.Cell>, C.Img.prefix(In.main(ds), In.bodies(ds)),
    List.append(&2, C.Cir.Cell, In.p344(In.main(ds)), C.Img.table(In.bodies(ds))), In.pre344.eq(In.main(ds), In.bodies(ds))) :
    {C.Cir.load(C.Img.table(In.bodies(ds)), In.adv(In.p344(In.main(ds)), 1), In.m344(In.main(ds))) == C.Cir.load(_, 1, C.Cir.Cells.none{}) : C.Cir.Cells}
  Equal.sym(C.Cir.Cells, C.Cir.load(List.append(&2, C.Cir.Cell, In.p344(In.main(ds)), C.Img.table(In.bodies(ds))), 1, C.Cir.Cells.none{}), C.Cir.load(C.Img.table(In.bodies(ds)), In.adv(In.p344(In.main(ds)), 1), In.m344(In.main(ds))),
    Ld.app(In.p344(In.main(ds)), C.Img.table(In.bodies(ds)), 1, C.Cir.Cells.none{}))


# the facts of other cells, by an equation
def Im.cast(-f0: Nat, -m: C.Cir.Cells, -m2: C.Cir.Cells, -F: U32, -N: Nat, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>,
  e: {m == m2 : C.Cir.Cells}, im: In.Im(f0, m, F, N, ks, img)) -> In.Im(f0, m2, F, N, ks, img):
  %e : In.Im(f0, _, F, N, ks, img)
  im

def CI.cast(-fc: Nat, -m: C.Cir.Cells, -m2: C.Cir.Cells, -F: U32, -N: Nat, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>,
  e: {m == m2 : C.Cir.Cells}, ci: In.CI(8n, [], fc, m, F, N, ks, img)) -> In.CI(8n, [], fc, m2, F, N, ks, img):
  %e : In.CI(8n, [], fc, _, F, N, ks, img)
  ci

# the image's cells that the machine points to stand for their terms at the start
def In.start.im(+ds: List<&2, C.Def>, +F: U32, +M: U32, +hsm: N.Le(1n+List.length(&2, C.Cir.Cell, C.Img.cells(ds)), U32.to_nat(M))) ->
  In.Im(80n, C.Cir.load(C.Img.cells(ds), 1, C.Cir.Cells.none{}), F, U32.to_nat(F), T.tm.names(ds), T.tm.img(ds)):
  Im.cast(80n, C.Cir.load(C.Img.blank(256n, C.Img.table(In.bodies(ds))), In.adv(In.p88(In.main(ds)), 1), In.m88(In.main(ds))),
   C.Cir.load(C.Img.cells(ds), 1, C.Cir.Cells.none{}), F, U32.to_nat(F), T.tm.names(ds), T.tm.img(ds), In.e88(ds),
   Im.load(C.Img.blank(256n, C.Img.table(In.bodies(ds))), In.adv(In.p88(In.main(ds)), 1), In.m88(In.main(ds)), F, 80n, T.tm.names(ds), T.tm.img(ds), M,
    Unit{}, hsm, Im.m88(In.main(ds), F, U32.to_nat(F), ds)))

# the cache is empty at the start
def In.start.ci(+ds: List<&2, C.Def>, +F: U32, +M: U32, +fc: Nat, +hsm: N.Le(1n+List.length(&2, C.Cir.Cell, C.Img.cells(ds)), U32.to_nat(M))) ->
  In.CI(8n, [], fc, C.Cir.load(C.Img.cells(ds), 1, C.Cir.Cells.none{}), F, U32.to_nat(F), T.tm.names(ds), T.tm.img(ds)):
  CI.cast(fc, C.Cir.load(C.Img.table(In.bodies(ds)), In.adv(In.p344(In.main(ds)), 1), In.m344(In.main(ds))),
   C.Cir.load(C.Img.cells(ds), 1, C.Cir.Cells.none{}), F, U32.to_nat(F), T.tm.names(ds), T.tm.img(ds), In.e344(ds),
   CI.load(C.Img.table(In.bodies(ds)), In.adv(In.p344(In.main(ds)), 1), In.m344(In.main(ds)), F, fc, T.tm.names(ds), T.tm.img(ds), M,
    Unit{}, hsm, CI.z(8n, [], fc, In.main(ds), F, U32.to_nat(F), T.tm.names(ds), T.tm.img(ds))))

# the facts of the start state: next and first are F, numbered as F; the
# image's cells that the machine points to stand for their terms with the
# fuel 80; the cache is empty
def In.start(+ds: List<&2, C.Def>, +F: U32, +M: U32, +fc: Nat, +hsm: N.Le(1n+List.length(&2, C.Cir.Cell, C.Img.cells(ds)), U32.to_nat(M))) ->
  In.Fa(C.Cir.load(C.Img.cells(ds), 1, C.Cir.Cells.none{}), F, U32.to_nat(F), F, 80n, fc, T.tm.names(ds), T.tm.img(ds)):
  ({==}, (N.le_refl(U32.to_nat(F)), (In.start.im(ds, F, M, hsm), In.start.ci(ds, F, M, fc, hsm))))
