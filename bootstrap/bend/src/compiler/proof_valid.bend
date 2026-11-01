# compiler: the modules of Cir.module are valid
# =============================================
#
# Wasm.valid.module accepts the module of Cir.module (valid.module, at the
# end) when the program's registers and fields exist (ok.stmt) and run has at
# most 50000 locals. The proof splits Wasm.valid.go in two: locs says that
# every local index is below the locals' number, and free.go is the
# validation with no check of the locals (go.free shows that the two agree
# when locs holds). Over Cir.code, free.go computes: the code of an
# expression leaves one value (free.expr), and the code of a statement at d
# levels inside run's block, whose labels are lab(d), leaves the stack as it
# was (free.stmt); a branch out of run reaches lab(d) at 1 + d (lab.out).
# The memory's limit, (b - 1) >> 16 + 1 pages, is at most 65536 for every b
# (pages.le), so the cells need no premise.

import Base
import ./impl.bend as C
import ./proof_need.bend as N
import ./proof_instrs.bend as I
import ./proof_img.bend as G
import ./proof_module.bend as M

# The programs' bounds
# --------------------

# every register that e reads is below regs, and every field is at most 4
def ok.expr(e: C.Cir.Expr, +regs: Nat) -> Bool:
  match e:
    case C.Cir.Expr.const{_}:
      True{}
    case C.Cir.Expr.get{r}:
      Nat.is_lt(r, regs)
    case C.Cir.Expr.op{_, a, b}:
      ok.expr(a, regs) && ok.expr(b, regs)
    case C.Cir.Expr.eqz{a}:
      ok.expr(a, regs)
    case C.Cir.Expr.field{k, c}:
      Nat.is_le(k, 4n) && ok.expr(c, regs)
    case C.Cir.Expr.byte{i}:
      ok.expr(i, regs)
    case C.Cir.Expr.size{}:
      True{}

# every register that s reads or writes is below regs, and every field is at
# most 4
def ok.stmt(s: C.Cir.Stmt, +regs: Nat) -> Bool:
  match s:
    case C.Cir.Stmt.nop{}:
      True{}
    case C.Cir.Stmt.set{r, e}:
      Nat.is_lt(r, regs) && ok.expr(e, regs)
    case C.Cir.Stmt.store{k, c, v}:
      Nat.is_le(k, 4n) && ok.expr(c, regs) && ok.expr(v, regs)
    case C.Cir.Stmt.alloc{r}:
      Nat.is_lt(r, regs)
    case C.Cir.Stmt.emit{v}:
      ok.expr(v, regs)
    case C.Cir.Stmt.seq{a, b}:
      ok.stmt(a, regs) && ok.stmt(b, regs)
    case C.Cir.Stmt.if{c, t, e}:
      ok.expr(c, regs) && ok.stmt(t, regs) && ok.stmt(e, regs)
    case C.Cir.Stmt.while{c, body}:
      ok.expr(c, regs) && ok.stmt(body, regs)
    case C.Cir.Stmt.halt{_}:
      True{}

# Validation without the locals
# -----------------------------

# h >= k, by the steps of k
def ge(k: Nat, h: Nat) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+q:
      match h:
        case 0n:
          False{}
        case 1n+p:
          ge(q, p)

# h - k, by the steps of k
def sb(k: Nat, h: Nat) -> Nat:
  match k:
    case 0n:
      h
    case 1n+q:
      match h:
        case 0n:
          0n
        case 1n+p:
          sb(q, p)

# Nat.is_ge is ge
def ge.eq(k: Nat, h: Nat) -> {Nat.is_ge(h, k) == ge(k, h) : Bool}:
  match k:
    case 0n:
      match h:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case 1n+q:
      match h:
        case 0n:
          {==}
        case 1n+p:
          ge.eq(q, p)

# Nat.sub is sb
def sb.eq(k: Nat, h: Nat) -> {Nat.sub(h, k) == sb(k, h) : Nat}:
  match k:
    case 0n:
      match h:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case 1n+q:
      match h:
        case 0n:
          {==}
        case 1n+p:
          sb.eq(q, p)

# Wasm.valid.go with no check of the local indices
def free.go(xs: List<&2, C.Wasm.Instr>, +h: Nat, +labels: List<&2, Nat>, +mem: Bool) -> Maybe<&2, C.Wasm.Height>:
  match xs:
    case Nil{}:
      Some{C.Wasm.Height.at{h}}
    case Con{C.Wasm.Instr.const{_}, rest}:
      free.go(rest, 1n+h, labels, mem)
    case Con{C.Wasm.Instr.local_get{_}, rest}:
      free.go(rest, 1n+h, labels, mem)
    case Con{C.Wasm.Instr.local_set{_}, rest}:
      C.Wasm.valid.if(ge(1n, h), u => free.go(rest, sb(1n, h), labels, mem))
    case Con{C.Wasm.Instr.local_tee{_}, rest}:
      C.Wasm.valid.if(ge(1n, h), u => free.go(rest, h, labels, mem))
    case Con{C.Wasm.Instr.op{_}, rest}:
      C.Wasm.valid.if(ge(2n, h), u => free.go(rest, sb(1n, h), labels, mem))
    case Con{C.Wasm.Instr.eqz{}, rest}:
      C.Wasm.valid.if(ge(1n, h), u => free.go(rest, h, labels, mem))
    case Con{C.Wasm.Instr.load{_}, rest}:
      C.Wasm.valid.if(mem && ge(1n, h), u => free.go(rest, h, labels, mem))
    case Con{C.Wasm.Instr.load8_u{_}, rest}:
      C.Wasm.valid.if(mem && ge(1n, h), u => free.go(rest, h, labels, mem))
    case Con{C.Wasm.Instr.store{_}, rest}:
      C.Wasm.valid.if(mem && ge(2n, h), u => free.go(rest, sb(2n, h), labels, mem))
    case Con{C.Wasm.Instr.store8{_}, rest}:
      C.Wasm.valid.if(mem && ge(2n, h), u => free.go(rest, sb(2n, h), labels, mem))
    case Con{C.Wasm.Instr.memory_size{}, rest}:
      C.Wasm.valid.if(mem, u => free.go(rest, 1n+h, labels, mem))
    case Con{C.Wasm.Instr.memory_grow{}, rest}:
      C.Wasm.valid.if(mem && ge(1n, h), u => free.go(rest, h, labels, mem))
    case Con{C.Wasm.Instr.block{body}, rest}:
      C.Wasm.valid.if(C.Wasm.valid.is_empty(free.go(body, 0n, Con{0n, labels}, mem)),
        u => free.go(rest, h, labels, mem))
    case Con{C.Wasm.Instr.loop{body}, rest}:
      C.Wasm.valid.if(C.Wasm.valid.is_empty(free.go(body, 0n, Con{0n, labels}, mem)),
        u => free.go(rest, h, labels, mem))
    case Con{C.Wasm.Instr.br{l}, rest}:
      C.Wasm.valid.if(C.Wasm.valid.br(C.Wasm.valid.label(labels, l), h) && List.is_empty(&2, C.Wasm.Instr, rest),
        u => Some{C.Wasm.Height.any{}})
    case Con{C.Wasm.Instr.br_if{l}, rest}:
      C.Wasm.valid.if(C.Wasm.valid.br_if(C.Wasm.valid.label(labels, l), h),
        u => free.go(rest, sb(1n, h), labels, mem))
    case Con{C.Wasm.Instr.br_table{ls, l}, rest}:
      C.Wasm.valid.if(C.Wasm.valid.table(labels, ls, C.Wasm.valid.label(labels, l), h) && List.is_empty(&2, C.Wasm.Instr, rest),
        u => Some{C.Wasm.Height.any{}})

# the local i is below n
def chk(i: U32, n: Nat) -> Bool:
  Nat.is_lt(U32.to_nat(i), n)

# every local index of xs, also inside its blocks, is below n
def locs(xs: List<&2, C.Wasm.Instr>, +n: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{C.Wasm.Instr.local_get{i}, rest}:
      chk(i, n) && locs(rest, n)
    case Con{C.Wasm.Instr.local_set{i}, rest}:
      chk(i, n) && locs(rest, n)
    case Con{C.Wasm.Instr.local_tee{i}, rest}:
      chk(i, n) && locs(rest, n)
    case Con{C.Wasm.Instr.block{body}, rest}:
      locs(body, n) && locs(rest, n)
    case Con{C.Wasm.Instr.loop{body}, rest}:
      locs(body, n) && locs(rest, n)
    case Con{_, rest}:
      locs(rest, n)

# a local below n = |loc| passes the check of Wasm.valid.go
def chk.lt(+i: U32, +loc: U32, +n: Nat, en: {U32.to_nat(loc) == n : Nat}, c: {chk(i, n) == True{} : Bool}) ->
  {U32.is_lt(i, loc) == True{} : Bool}:
  G.lt_true(U32.cmp(i, loc), U32.to_nat(i), U32.to_nat(loc), N.U32.rel(i, loc),
    N.le_rw_r(1n+U32.to_nat(i), n, U32.to_nat(loc), Equal.sym(Nat, U32.to_nat(loc), n, en), M.lt_le(U32.to_nat(i), n, c)))

# equal conditions and equal results
def if.cong(-c1: Bool, -c2: Bool, -a: Maybe<&2, C.Wasm.Height>, -b: Maybe<&2, C.Wasm.Height>,
  ec: {c1 == c2 : Bool}, e: {a == b : Maybe<&2, C.Wasm.Height>}) ->
  {C.Wasm.valid.if(c1, u => a) == C.Wasm.valid.if(c2, u => b) : Maybe<&2, C.Wasm.Height>}:
  %ec : {C.Wasm.valid.if(c1, u => a) == C.Wasm.valid.if(_, u => b) : Maybe<&2, C.Wasm.Height>}
  %e : {C.Wasm.valid.if(c1, u => a) == C.Wasm.valid.if(c1, u => _) : Maybe<&2, C.Wasm.Height>}
  {==}

# equal conditions after the memory's
def mem.cong(+mem: Bool, -c1: Bool, -c2: Bool, ec: {c1 == c2 : Bool}) -> {Bool.and(mem, c1) == Bool.and(mem, c2) : Bool}:
  %ec : {Bool.and(mem, c1) == Bool.and(mem, _) : Bool}
  {==}

# go at the height k1 = k2
def go.at(+rest: List<&2, C.Wasm.Instr>, -k1: Nat, -k2: Nat, +labels: List<&2, Nat>, +loc: U32, +mem: Bool,
  ek: {k1 == k2 : Nat}, ih: {C.Wasm.valid.go(rest, k2, labels, loc, mem) == free.go(rest, k2, labels, mem) : Maybe<&2, C.Wasm.Height>}) ->
  {C.Wasm.valid.go(rest, k1, labels, loc, mem) == free.go(rest, k2, labels, mem) : Maybe<&2, C.Wasm.Height>}:
  %Equal.sym(Nat, k1, k2, ek) : {C.Wasm.valid.go(rest, _, labels, loc, mem) == free.go(rest, k2, labels, mem) : Maybe<&2, C.Wasm.Height>}
  ih

# with every local below the locals' number, Wasm.valid.go is free.go
def go.free(xs: List<&2, C.Wasm.Instr>, +h: Nat, +labels: List<&2, Nat>, +loc: U32, +n: Nat, +mem: Bool,
  +en: {U32.to_nat(loc) == n : Nat}, +ok: {locs(xs, n) == True{} : Bool}) ->
  {C.Wasm.valid.go(xs, h, labels, loc, mem) == free.go(xs, h, labels, mem) : Maybe<&2, C.Wasm.Height>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +rest}:
      match x:
        case C.Wasm.Instr.const{_}:
          go.free(rest, 1n+h, labels, loc, n, mem, en, ok)
        case C.Wasm.Instr.local_get{+i}:
          +c = chk.lt(i, loc, n, en, I.and.l(chk(i, n), locs(rest, n), ok))
          %Equal.sym(Bool, U32.is_lt(i, loc), True{}, c) :
            {C.Wasm.valid.if(_, u => C.Wasm.valid.go(rest, 1n+h, labels, loc, mem)) == free.go(rest, 1n+h, labels, mem) : Maybe<&2, C.Wasm.Height>}
          go.free(rest, 1n+h, labels, loc, n, mem, en, I.and.r(chk(i, n), locs(rest, n), ok))
        case C.Wasm.Instr.local_set{+i}:
          +c = chk.lt(i, loc, n, en, I.and.l(chk(i, n), locs(rest, n), ok))
          %Equal.sym(Bool, U32.is_lt(i, loc), True{}, c) :
            {C.Wasm.valid.if(Bool.and(_, Nat.is_ge(h, 1n)), u => C.Wasm.valid.go(rest, Nat.sub(h, 1n), labels, loc, mem)) ==
              C.Wasm.valid.if(ge(1n, h), u => free.go(rest, sb(1n, h), labels, mem)) : Maybe<&2, C.Wasm.Height>}
          if.cong(Nat.is_ge(h, 1n), ge(1n, h), C.Wasm.valid.go(rest, Nat.sub(h, 1n), labels, loc, mem), free.go(rest, sb(1n, h), labels, mem),
            ge.eq(1n, h), go.at(rest, Nat.sub(h, 1n), sb(1n, h), labels, loc, mem, sb.eq(1n, h),
              go.free(rest, sb(1n, h), labels, loc, n, mem, en, I.and.r(chk(i, n), locs(rest, n), ok))))
        case C.Wasm.Instr.local_tee{+i}:
          +c = chk.lt(i, loc, n, en, I.and.l(chk(i, n), locs(rest, n), ok))
          %Equal.sym(Bool, U32.is_lt(i, loc), True{}, c) :
            {C.Wasm.valid.if(Bool.and(_, Nat.is_ge(h, 1n)), u => C.Wasm.valid.go(rest, h, labels, loc, mem)) ==
              C.Wasm.valid.if(ge(1n, h), u => free.go(rest, h, labels, mem)) : Maybe<&2, C.Wasm.Height>}
          if.cong(Nat.is_ge(h, 1n), ge(1n, h), C.Wasm.valid.go(rest, h, labels, loc, mem), free.go(rest, h, labels, mem),
            ge.eq(1n, h), go.free(rest, h, labels, loc, n, mem, en, I.and.r(chk(i, n), locs(rest, n), ok)))
        case C.Wasm.Instr.op{_}:
          if.cong(Nat.is_ge(h, 2n), ge(2n, h), C.Wasm.valid.go(rest, Nat.sub(h, 1n), labels, loc, mem), free.go(rest, sb(1n, h), labels, mem),
            ge.eq(2n, h), go.at(rest, Nat.sub(h, 1n), sb(1n, h), labels, loc, mem, sb.eq(1n, h),
              go.free(rest, sb(1n, h), labels, loc, n, mem, en, ok)))
        case C.Wasm.Instr.eqz{}:
          if.cong(Nat.is_ge(h, 1n), ge(1n, h), C.Wasm.valid.go(rest, h, labels, loc, mem), free.go(rest, h, labels, mem),
            ge.eq(1n, h), go.free(rest, h, labels, loc, n, mem, en, ok))
        case C.Wasm.Instr.load{_}:
          if.cong(Bool.and(mem, Nat.is_ge(h, 1n)), Bool.and(mem, ge(1n, h)), C.Wasm.valid.go(rest, h, labels, loc, mem), free.go(rest, h, labels, mem),
            mem.cong(mem, Nat.is_ge(h, 1n), ge(1n, h), ge.eq(1n, h)), go.free(rest, h, labels, loc, n, mem, en, ok))
        case C.Wasm.Instr.load8_u{_}:
          if.cong(Bool.and(mem, Nat.is_ge(h, 1n)), Bool.and(mem, ge(1n, h)), C.Wasm.valid.go(rest, h, labels, loc, mem), free.go(rest, h, labels, mem),
            mem.cong(mem, Nat.is_ge(h, 1n), ge(1n, h), ge.eq(1n, h)), go.free(rest, h, labels, loc, n, mem, en, ok))
        case C.Wasm.Instr.store{_}:
          if.cong(Bool.and(mem, Nat.is_ge(h, 2n)), Bool.and(mem, ge(2n, h)), C.Wasm.valid.go(rest, Nat.sub(h, 2n), labels, loc, mem), free.go(rest, sb(2n, h), labels, mem),
            mem.cong(mem, Nat.is_ge(h, 2n), ge(2n, h), ge.eq(2n, h)), go.at(rest, Nat.sub(h, 2n), sb(2n, h), labels, loc, mem, sb.eq(2n, h),
              go.free(rest, sb(2n, h), labels, loc, n, mem, en, ok)))
        case C.Wasm.Instr.store8{_}:
          if.cong(Bool.and(mem, Nat.is_ge(h, 2n)), Bool.and(mem, ge(2n, h)), C.Wasm.valid.go(rest, Nat.sub(h, 2n), labels, loc, mem), free.go(rest, sb(2n, h), labels, mem),
            mem.cong(mem, Nat.is_ge(h, 2n), ge(2n, h), ge.eq(2n, h)), go.at(rest, Nat.sub(h, 2n), sb(2n, h), labels, loc, mem, sb.eq(2n, h),
              go.free(rest, sb(2n, h), labels, loc, n, mem, en, ok)))
        case C.Wasm.Instr.memory_size{}:
          Equal.cong(Maybe<&2, C.Wasm.Height>, Maybe<&2, C.Wasm.Height>, m => C.Wasm.valid.if(mem, u => m),
            C.Wasm.valid.go(rest, 1n+h, labels, loc, mem), free.go(rest, 1n+h, labels, mem),
            go.free(rest, 1n+h, labels, loc, n, mem, en, ok))
        case C.Wasm.Instr.memory_grow{}:
          if.cong(Bool.and(mem, Nat.is_ge(h, 1n)), Bool.and(mem, ge(1n, h)), C.Wasm.valid.go(rest, h, labels, loc, mem), free.go(rest, h, labels, mem),
            mem.cong(mem, Nat.is_ge(h, 1n), ge(1n, h), ge.eq(1n, h)), go.free(rest, h, labels, loc, n, mem, en, ok))
        case C.Wasm.Instr.block{+body}:
          +eb = go.free(body, 0n, Con{0n, labels}, loc, n, mem, en, I.and.l(locs(body, n), locs(rest, n), ok))
          %Equal.sym(Maybe<&2, C.Wasm.Height>, C.Wasm.valid.go(body, 0n, Con{0n, labels}, loc, mem), free.go(body, 0n, Con{0n, labels}, mem), eb) :
            {C.Wasm.valid.if(C.Wasm.valid.is_empty(_), u => C.Wasm.valid.go(rest, h, labels, loc, mem)) ==
              C.Wasm.valid.if(C.Wasm.valid.is_empty(free.go(body, 0n, Con{0n, labels}, mem)), u => free.go(rest, h, labels, mem)) : Maybe<&2, C.Wasm.Height>}
          Equal.cong(Maybe<&2, C.Wasm.Height>, Maybe<&2, C.Wasm.Height>,
            m => C.Wasm.valid.if(C.Wasm.valid.is_empty(free.go(body, 0n, Con{0n, labels}, mem)), u => m),
            C.Wasm.valid.go(rest, h, labels, loc, mem), free.go(rest, h, labels, mem),
            go.free(rest, h, labels, loc, n, mem, en, I.and.r(locs(body, n), locs(rest, n), ok)))
        case C.Wasm.Instr.loop{+body}:
          +eb = go.free(body, 0n, Con{0n, labels}, loc, n, mem, en, I.and.l(locs(body, n), locs(rest, n), ok))
          %Equal.sym(Maybe<&2, C.Wasm.Height>, C.Wasm.valid.go(body, 0n, Con{0n, labels}, loc, mem), free.go(body, 0n, Con{0n, labels}, mem), eb) :
            {C.Wasm.valid.if(C.Wasm.valid.is_empty(_), u => C.Wasm.valid.go(rest, h, labels, loc, mem)) ==
              C.Wasm.valid.if(C.Wasm.valid.is_empty(free.go(body, 0n, Con{0n, labels}, mem)), u => free.go(rest, h, labels, mem)) : Maybe<&2, C.Wasm.Height>}
          Equal.cong(Maybe<&2, C.Wasm.Height>, Maybe<&2, C.Wasm.Height>,
            m => C.Wasm.valid.if(C.Wasm.valid.is_empty(free.go(body, 0n, Con{0n, labels}, mem)), u => m),
            C.Wasm.valid.go(rest, h, labels, loc, mem), free.go(rest, h, labels, mem),
            go.free(rest, h, labels, loc, n, mem, en, I.and.r(locs(body, n), locs(rest, n), ok)))
        case C.Wasm.Instr.br{_}:
          {==}
        case C.Wasm.Instr.br_if{+l}:
          Equal.cong(Maybe<&2, C.Wasm.Height>, Maybe<&2, C.Wasm.Height>,
            m => C.Wasm.valid.if(C.Wasm.valid.br_if(C.Wasm.valid.label(labels, l), h), u => m),
            C.Wasm.valid.go(rest, Nat.sub(h, 1n), labels, loc, mem), free.go(rest, sb(1n, h), labels, mem),
            go.at(rest, Nat.sub(h, 1n), sb(1n, h), labels, loc, mem, sb.eq(1n, h),
              go.free(rest, sb(1n, h), labels, loc, n, mem, en, ok)))
        case C.Wasm.Instr.br_table{_, _}:
          {==}

# Labels
# ------

# the labels' types at d levels inside run's block, innermost first: d + 1
# blocks of no values, then run's own label, of one value
def lab(d: Nat) -> List<&2, Nat>:
  match d:
    case 0n:
      [0n, 1n]
    case 1n+p:
      Con{0n, lab(p)}

def lab.if(z: Bool, +p: Nat, ih: {C.Wasm.valid.label(lab(p), U32.from_nat(p)) == Some{0n} : Maybe<&2, Nat>}) ->
  {C.Wasm.valid.label.if(z, 0n, u => C.Wasm.valid.label(lab(p), U32.sub(U32.inc(U32.from_nat(p)), 1))) == Some{0n} : Maybe<&2, Nat>}:
  match z:
    case True{}:
      {==}
    case False{}:
      %I.U32.inc_dec(U32.from_nat(p)) : {C.Wasm.valid.label(lab(p), _) == Some{0n} : Maybe<&2, Nat>}
      ih

# the label d, from d levels inside run's block, is a block of no values: run's
# own block (also when d wraps around, as every label but the last has no
# values)
def lab.out(+d: Nat) -> {C.Wasm.valid.label(lab(d), U32.from_nat(d)) == Some{0n} : Maybe<&2, Nat>}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      lab.if(U32.is_zero(U32.inc(U32.from_nat(p))), p, lab.out(p))

# Expressions
# -----------

# the code of an expression leaves one value
def free.expr(e: C.Cir.Expr, +acc: List<&2, C.Wasm.Instr>, +h: Nat, +labels: List<&2, Nat>) ->
  {free.go(C.Cir.code.expr(e, acc), h, labels, True{}) == free.go(acc, 1n+h, labels, True{}) : Maybe<&2, C.Wasm.Height>}:
  match e:
    case C.Cir.Expr.const{_}:
      {==}
    case C.Cir.Expr.get{_}:
      {==}
    case C.Cir.Expr.op{+o, +a, +b}:
      +X = C.Cir.code.expr(b, Con{C.Cir.i.op(o), acc})
      Equal.trans(Maybe<&2, C.Wasm.Height>, free.go(C.Cir.code.expr(a, X), h, labels, True{}), free.go(X, 1n+h, labels, True{}),
        free.go(acc, 1n+h, labels, True{}), free.expr(a, X, h, labels), free.expr(b, Con{C.Cir.i.op(o), acc}, 1n+h, labels))
    case C.Cir.Expr.eqz{+a}:
      free.expr(a, Con{C.Wasm.Instr.eqz{}, acc}, h, labels)
    case C.Cir.Expr.field{+k, +c}:
      free.expr(c, C.Cir.code.at(Con{C.Wasm.Instr.load{U32.shln(U32.from_nat(k), 2n)}, acc}), h, labels)
    case C.Cir.Expr.byte{+i}:
      free.expr(i, Con{C.Cir.i.get(0), Con{C.Cir.i.op(C.Wasm.Op.add{}), Con{C.Wasm.Instr.load8_u{0},
        Con{C.Cir.i.const(255), Con{C.Cir.i.op(C.Wasm.Op.and{}), acc}}}}}, h, labels)
    case C.Cir.Expr.size{}:
      {==}

# Branches out of run
# -------------------

# a branch to a block of no values
def br.ok(+l: U32, +labels: List<&2, Nat>, e: {C.Wasm.valid.label(labels, l) == Some{0n} : Maybe<&2, Nat>}) ->
  {free.go([C.Wasm.Instr.br{l}], 0n, labels, True{}) == Some{C.Wasm.Height.any{}} : Maybe<&2, C.Wasm.Height>}:
  %Equal.sym(Maybe<&2, Nat>, C.Wasm.valid.label(labels, l), Some{0n}, e) :
    {C.Wasm.valid.if(Bool.and(C.Wasm.valid.br(_, 0n), List.is_empty(&2, C.Wasm.Instr, [])), u => Some{C.Wasm.Height.any{}}) ==
      Some{C.Wasm.Height.any{}} : Maybe<&2, C.Wasm.Height>}
  {==}

# the exit with the status s
def exit.ok(+s: U32, +d: Nat, +rest: List<&2, C.Wasm.Instr>, +h: Nat) ->
  {free.go(Con{C.Cir.code.exit(s, d), rest}, h, lab(d), True{}) == free.go(rest, h, lab(d), True{}) : Maybe<&2, C.Wasm.Height>}:
  %Equal.sym(Maybe<&2, C.Wasm.Height>, free.go([C.Wasm.Instr.br{U32.from_nat(1n+d)}], 0n, lab(1n+d), True{}), Some{C.Wasm.Height.any{}},
    br.ok(U32.from_nat(1n+d), lab(1n+d), lab.out(1n+d))) :
    {C.Wasm.valid.if(C.Wasm.valid.is_empty(_), u => free.go(rest, h, lab(d), True{})) == free.go(rest, h, lab(d), True{}) : Maybe<&2, C.Wasm.Height>}
  {==}

# out of memory unless cond, which leaves one value
def unless.ok(+cond: List<&2, C.Wasm.Instr>, +d: Nat, +acc: List<&2, C.Wasm.Instr>, +h: Nat,
  ec: {free.go(List.append(&2, C.Wasm.Instr, cond, [C.Wasm.Instr.br_if{0}, C.Cir.code.exit(1, 1n+d)]), 0n, lab(1n+d), True{}) ==
    free.go([C.Cir.code.exit(1, 1n+d)], 0n, lab(1n+d), True{}) : Maybe<&2, C.Wasm.Height>}) ->
  {free.go(C.Cir.code.unless(cond, d, acc), h, lab(d), True{}) == free.go(acc, h, lab(d), True{}) : Maybe<&2, C.Wasm.Height>}:
  +B = List.append(&2, C.Wasm.Instr, cond, [C.Wasm.Instr.br_if{0}, C.Cir.code.exit(1, 1n+d)])
  +e = Equal.trans(Maybe<&2, C.Wasm.Height>, free.go(B, 0n, lab(1n+d), True{}), free.go([C.Cir.code.exit(1, 1n+d)], 0n, lab(1n+d), True{}),
    free.go([], 0n, lab(1n+d), True{}), ec, exit.ok(1, 1n+d, [], 0n))
  %Equal.sym(Maybe<&2, C.Wasm.Height>, free.go(B, 0n, lab(1n+d), True{}), free.go([], 0n, lab(1n+d), True{}), e) :
    {C.Wasm.valid.if(C.Wasm.valid.is_empty(_), u => free.go(acc, h, lab(d), True{})) == free.go(acc, h, lab(d), True{}) : Maybe<&2, C.Wasm.Height>}
  {==}

# the check of memory.grow
def grow.cond() -> List<&2, C.Wasm.Instr>:
  [C.Cir.i.get(C.Cir.l.need()), C.Wasm.Instr.memory_size{}, C.Cir.i.op(C.Wasm.Op.sub{}),
    C.Wasm.Instr.memory_grow{}, C.Cir.i.const(4294967295), C.Cir.i.op(C.Wasm.Op.ne{})]

# the memory grows
def grow.ok(+d: Nat, +acc: List<&2, C.Wasm.Instr>, +h: Nat) ->
  {free.go(C.Cir.code.grow(d, acc), h, lab(d), True{}) == free.go(acc, h, lab(d), True{}) : Maybe<&2, C.Wasm.Height>}:
  %Equal.sym(Maybe<&2, C.Wasm.Height>, free.go(C.Cir.code.unless(grow.cond(), 1n+d, []), 0n, lab(1n+d), True{}), free.go([], 0n, lab(1n+d), True{}),
    unless.ok(grow.cond(), 1n+d, [], 0n, {==})) :
    {C.Wasm.valid.if(C.Wasm.valid.is_empty(_), u => free.go(acc, h, lab(d), True{})) == free.go(acc, h, lab(d), True{}) : Maybe<&2, C.Wasm.Height>}
  {==}

# the check of alloc that the cell's number fits
def alloc.cond() -> List<&2, C.Wasm.Instr>:
  [C.Cir.i.get(C.Cir.l.next()), C.Cir.i.const(214748364), C.Cir.i.op(C.Wasm.Op.lt_u{})]

# the code of alloc after its memory grows
def alloc.tail(+x: U32, acc: List<&2, C.Wasm.Instr>) -> List<&2, C.Wasm.Instr>:
  Con{C.Cir.i.get(C.Cir.l.next()), Con{C.Cir.i.set(x),
    Con{C.Cir.i.get(C.Cir.l.next()), Con{C.Cir.i.const(1), Con{C.Cir.i.op(C.Wasm.Op.add{}), Con{C.Cir.i.set(C.Cir.l.next()),
    Con{C.Cir.i.get(x), C.Cir.code.at(Con{C.Cir.i.set(C.Cir.l.addr()), C.Cir.code.zero(acc)})}}}}}}}

# the code of alloc after its check of the cell's number
def alloc.rest(+x: U32, +d: Nat, acc: List<&2, C.Wasm.Instr>) -> List<&2, C.Wasm.Instr>:
  Con{C.Cir.i.get(C.Cir.l.next()), C.Cir.code.at(Con{C.Cir.i.const(19), Con{C.Cir.i.op(C.Wasm.Op.add{}),
    C.Cir.code.need(C.Cir.code.grow(d, alloc.tail(x, acc)))}})}

# a new cell leaves the stack as it was
def alloc.ok(+x: U32, +d: Nat, +acc: List<&2, C.Wasm.Instr>, +h: Nat) ->
  {free.go(C.Cir.code.alloc(x, d, acc), h, lab(d), True{}) == free.go(acc, h, lab(d), True{}) : Maybe<&2, C.Wasm.Height>}:
  +R = alloc.rest(x, d, acc)
  +K = alloc.tail(x, acc)
  Equal.trans(Maybe<&2, C.Wasm.Height>, free.go(C.Cir.code.alloc(x, d, acc), h, lab(d), True{}), free.go(R, h, lab(d), True{}),
    free.go(acc, h, lab(d), True{}), unless.ok(alloc.cond(), d, R, h, {==}),
    Equal.trans(Maybe<&2, C.Wasm.Height>, free.go(R, h, lab(d), True{}), free.go(K, h, lab(d), True{}),
      free.go(acc, h, lab(d), True{}), grow.ok(d, K, h), {==}))

# the check of emit that the byte's place fits
def emit.cond() -> List<&2, C.Wasm.Instr>:
  [C.Cir.i.get(C.Cir.l.next()), C.Cir.i.const(214748365), C.Cir.i.op(C.Wasm.Op.lt_u{}),
    C.Cir.i.get(C.Cir.l.addr()), C.Cir.i.get(C.Cir.l.outn()), C.Cir.i.op(C.Wasm.Op.ge_u{}), C.Cir.i.op(C.Wasm.Op.and{})]

# the code of emit after its value
def emit.store(acc: List<&2, C.Wasm.Instr>) -> List<&2, C.Wasm.Instr>:
  Con{C.Wasm.Instr.store8{0}, Con{C.Cir.i.get(C.Cir.l.outn()), Con{C.Cir.i.const(1), Con{C.Cir.i.op(C.Wasm.Op.add{}),
    Con{C.Cir.i.set(C.Cir.l.outn()), acc}}}}}

# the code of emit after its memory grows
def emit.tail(+v: C.Cir.Expr, acc: List<&2, C.Wasm.Instr>) -> List<&2, C.Wasm.Instr>:
  Con{C.Cir.i.get(C.Cir.l.addr()), C.Cir.code.expr(v, emit.store(acc))}

# the code of emit after its check of the byte's place
def emit.rest(+v: C.Cir.Expr, +d: Nat, acc: List<&2, C.Wasm.Instr>) -> List<&2, C.Wasm.Instr>:
  Con{C.Cir.i.get(C.Cir.l.addr()), C.Cir.code.need(C.Cir.code.grow(d, emit.tail(v, acc)))}

# a byte of output leaves the stack as it was
def emit.ok(+v: C.Cir.Expr, +d: Nat, +acc: List<&2, C.Wasm.Instr>, +h: Nat) ->
  {free.go(C.Cir.code.emit(v, d, acc), h, lab(d), True{}) == free.go(acc, h, lab(d), True{}) : Maybe<&2, C.Wasm.Height>}:
  +R = emit.rest(v, d, acc)
  +K = emit.tail(v, acc)
  Equal.trans(Maybe<&2, C.Wasm.Height>, free.go(C.Cir.code.emit(v, d, acc), h, lab(d), True{}), free.go(R, h, lab(d), True{}),
    free.go(acc, h, lab(d), True{}), unless.ok(emit.cond(), d, R, h, {==}),
    Equal.trans(Maybe<&2, C.Wasm.Height>, free.go(R, h, lab(d), True{}), free.go(K, h, lab(d), True{}),
      free.go(acc, h, lab(d), True{}), grow.ok(d, K, h), free.expr(v, emit.store(acc), 1n+h, lab(d))))

# the result, if any, then the branch out of run
def result.ok(z: Bool, +l: U32, +labels: List<&2, Nat>, e: {C.Wasm.valid.label(labels, l) == Some{0n} : Maybe<&2, Nat>}) ->
  {free.go(List.append(&2, C.Wasm.Instr, C.Cir.code.result(z), [C.Wasm.Instr.br{l}]), 0n, labels, True{}) == Some{C.Wasm.Height.any{}} : Maybe<&2, C.Wasm.Height>}:
  match z:
    case True{}:
      br.ok(l, labels, e)
    case False{}:
      br.ok(l, labels, e)

# halt leaves the stack as it was (and branches out of run)
def halt.ok(+s: U32, +d: Nat, +acc: List<&2, C.Wasm.Instr>, +h: Nat) ->
  {free.go(Con{C.Cir.code.halt(s, d), acc}, h, lab(d), True{}) == free.go(acc, h, lab(d), True{}) : Maybe<&2, C.Wasm.Height>}:
  +A = List.append(&2, C.Wasm.Instr, C.Cir.code.result(U32.is_zero(s)), [C.Wasm.Instr.br{U32.from_nat(1n+d)}])
  %Equal.sym(Maybe<&2, C.Wasm.Height>, free.go(A, 0n, lab(1n+d), True{}), Some{C.Wasm.Height.any{}},
    result.ok(U32.is_zero(s), U32.from_nat(1n+d), lab(1n+d), lab.out(1n+d))) :
    {C.Wasm.valid.if(C.Wasm.valid.is_empty(_), u => free.go(acc, h, lab(d), True{})) == free.go(acc, h, lab(d), True{}) : Maybe<&2, C.Wasm.Height>}
  {==}

# Statements
# ----------

# the code of a statement at d levels inside run's block leaves the stack as
# it found it
def free.stmt(s: C.Cir.Stmt, +d: Nat, +acc: List<&2, C.Wasm.Instr>, +h: Nat) ->
  {free.go(C.Cir.code.stmt(s, d, acc), h, lab(d), True{}) == free.go(acc, h, lab(d), True{}) : Maybe<&2, C.Wasm.Height>}:
  match s:
    case C.Cir.Stmt.nop{}:
      {==}
    case C.Cir.Stmt.set{+r, +e}:
      free.expr(e, Con{C.Cir.i.set(C.Cir.l.reg(r)), acc}, h, lab(d))
    case C.Cir.Stmt.store{+k, +c, +v}:
      +X = C.Cir.code.expr(v, Con{C.Wasm.Instr.store{U32.shln(U32.from_nat(k), 2n)}, acc})
      Equal.trans(Maybe<&2, C.Wasm.Height>, free.go(C.Cir.code.expr(c, C.Cir.code.at(X)), h, lab(d), True{}),
        free.go(C.Cir.code.at(X), 1n+h, lab(d), True{}), free.go(acc, h, lab(d), True{}),
        free.expr(c, C.Cir.code.at(X), h, lab(d)), free.expr(v, Con{C.Wasm.Instr.store{U32.shln(U32.from_nat(k), 2n)}, acc}, 1n+h, lab(d)))
    case C.Cir.Stmt.alloc{+r}:
      alloc.ok(C.Cir.l.reg(r), d, acc, h)
    case C.Cir.Stmt.emit{+v}:
      emit.ok(v, d, acc, h)
    case C.Cir.Stmt.seq{+a, +b}:
      +X = C.Cir.code.stmt(b, d, acc)
      Equal.trans(Maybe<&2, C.Wasm.Height>, free.go(C.Cir.code.stmt(a, d, X), h, lab(d), True{}), free.go(X, h, lab(d), True{}),
        free.go(acc, h, lab(d), True{}), free.stmt(a, d, X, h), free.stmt(b, d, acc, h))
    case C.Cir.Stmt.if{+c, +t, +e}:
      +T = C.Cir.code.stmt(t, 2n+d, [C.Wasm.Instr.br{1}])
      +X = {Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{0}, T}} : List<&2, C.Wasm.Instr>}
      +E = C.Cir.code.stmt(e, 1n+d, [])
      +e1 = Equal.trans(Maybe<&2, C.Wasm.Height>, free.go(C.Cir.code.expr(c, X), 0n, lab(2n+d), True{}), free.go(T, 0n, lab(2n+d), True{}),
        free.go([C.Wasm.Instr.br{1}], 0n, lab(2n+d), True{}), free.expr(c, X, 0n, lab(2n+d)), free.stmt(t, 2n+d, [C.Wasm.Instr.br{1}], 0n))
      %Equal.sym(Maybe<&2, C.Wasm.Height>, free.go(C.Cir.code.expr(c, X), 0n, lab(2n+d), True{}), free.go([C.Wasm.Instr.br{1}], 0n, lab(2n+d), True{}), e1) :
        {C.Wasm.valid.if(C.Wasm.valid.is_empty(C.Wasm.valid.if(C.Wasm.valid.is_empty(_), u => free.go(E, 0n, lab(1n+d), True{}))),
          u => free.go(acc, h, lab(d), True{})) == free.go(acc, h, lab(d), True{}) : Maybe<&2, C.Wasm.Height>}
      %Equal.sym(Maybe<&2, C.Wasm.Height>, free.go(E, 0n, lab(1n+d), True{}), free.go([], 0n, lab(1n+d), True{}), free.stmt(e, 1n+d, [], 0n)) :
        {C.Wasm.valid.if(C.Wasm.valid.is_empty(_), u => free.go(acc, h, lab(d), True{})) == free.go(acc, h, lab(d), True{}) : Maybe<&2, C.Wasm.Height>}
      {==}
    case C.Cir.Stmt.while{+c, +body}:
      +T = C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])
      +X = {Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, T}} : List<&2, C.Wasm.Instr>}
      +e1 = Equal.trans(Maybe<&2, C.Wasm.Height>, free.go(C.Cir.code.expr(c, X), 0n, lab(2n+d), True{}), free.go(T, 0n, lab(2n+d), True{}),
        free.go([C.Wasm.Instr.br{0}], 0n, lab(2n+d), True{}), free.expr(c, X, 0n, lab(2n+d)), free.stmt(body, 2n+d, [C.Wasm.Instr.br{0}], 0n))
      %Equal.sym(Maybe<&2, C.Wasm.Height>, free.go(C.Cir.code.expr(c, X), 0n, lab(2n+d), True{}), free.go([C.Wasm.Instr.br{0}], 0n, lab(2n+d), True{}), e1) :
        {C.Wasm.valid.if(C.Wasm.valid.is_empty(C.Wasm.valid.if(C.Wasm.valid.is_empty(_), u => free.go([], 0n, lab(1n+d), True{}))),
          u => free.go(acc, h, lab(d), True{})) == free.go(acc, h, lab(d), True{}) : Maybe<&2, C.Wasm.Height>}
      {==}
    case C.Cir.Stmt.halt{+s}:
      halt.ok(s, d, acc, h)

# Register indices
# ----------------

# a carry in adds one
def adc.carry(+n: Nat, a: Word(n), b: Word(n)) ->
  {Word.adc(n, a, b, False{}, True{}) == Word.inc(n, Word.adc(n, a, b, False{}, False{})) : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{False{}, at} WCon{False{}, bt}:
          {==}
        case WCon{False{}, +at} WCon{True{}, +bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, at, bt, False{}, True{}),
            Word.inc(p, Word.adc(p, at, bt, False{}, False{})), adc.carry(p, at, bt))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, at, bt, False{}, True{}),
            Word.inc(p, Word.adc(p, at, bt, False{}, False{})), adc.carry(p, at, bt))
        case WCon{True{}, at} WCon{True{}, bt}:
          {==}

# a + (b + 1) = (a + b) + 1, with the carry c
def adc.inc(+n: Nat, a: Word(n), b: Word(n), c: Bool) ->
  {Word.adc(n, a, Word.inc(n, b), False{}, c) == Word.inc(n, Word.adc(n, a, b, False{}, c)) : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{False{}, at} WCon{False{}, bt} False{}:
          {==}
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, at, bt, False{}, True{}),
            Word.inc(p, Word.adc(p, at, bt, False{}, False{})), adc.carry(p, at, bt))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, at, bt, False{}, True{}),
            Word.inc(p, Word.adc(p, at, bt, False{}, False{})), adc.carry(p, at, bt))
        case WCon{True{}, at} WCon{False{}, bt} True{}:
          {==}
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, at, Word.inc(p, bt), False{}, False{}),
            Word.inc(p, Word.adc(p, at, bt, False{}, False{})), adc.inc(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, at, Word.inc(p, bt), False{}, False{}),
            Word.adc(p, at, bt, False{}, True{}),
            Equal.trans(Word(p), Word.adc(p, at, Word.inc(p, bt), False{}, False{}), Word.inc(p, Word.adc(p, at, bt, False{}, False{})),
              Word.adc(p, at, bt, False{}, True{}), adc.inc(p, at, bt, False{}),
              Equal.sym(Word(p), Word.adc(p, at, bt, False{}, True{}), Word.inc(p, Word.adc(p, at, bt, False{}, False{})), adc.carry(p, at, bt))))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, at, Word.inc(p, bt), False{}, False{}),
            Word.adc(p, at, bt, False{}, True{}),
            Equal.trans(Word(p), Word.adc(p, at, Word.inc(p, bt), False{}, False{}), Word.inc(p, Word.adc(p, at, bt, False{}, False{})),
              Word.adc(p, at, bt, False{}, True{}), adc.inc(p, at, bt, False{}),
              Equal.sym(Word(p), Word.adc(p, at, bt, False{}, True{}), Word.inc(p, Word.adc(p, at, bt, False{}, False{})), adc.carry(p, at, bt))))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, at, Word.inc(p, bt), False{}, True{}),
            Word.inc(p, Word.adc(p, at, bt, False{}, True{})), adc.inc(p, at, bt, True{}))

# a + (b + 1) = (a + b) + 1 on U32
def add.inc(a: U32, b: U32) -> {U32.add(a, U32.inc(b)) == U32.inc(U32.add(a, b)) : U32}:
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.adc(32n, x, Word.inc(32n, y), False{}, False{}),
        Word.inc(32n, Word.adc(32n, x, y, False{}, False{})), adc.inc(32n, x, y, False{}))

# register r is local 8 + r
def add8(+r: Nat) -> {C.Cir.l.reg(r) == U32.from_nat(8n+r) : U32}:
  match r:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(U32, U32.add(8, U32.inc(U32.from_nat(p))), U32.inc(U32.add(8, U32.from_nat(p))), U32.from_nat(9n+p),
        add.inc(8, U32.from_nat(p)), Equal.cong(U32, U32, x => U32.inc(x), U32.add(8, U32.from_nat(p)), U32.from_nat(8n+p), add8(p)))

# a register below regs is a local below 8 + regs, when 8 + regs <= M
def reg.chk(+r: Nat, +regs: Nat, +M: U32, +ok: {Nat.is_lt(r, regs) == True{} : Bool}, b: N.Le(8n+regs, U32.to_nat(M))) ->
  {chk(C.Cir.l.reg(r), 8n+regs) == True{} : Bool}:
  +le = N.le_trans(8n+r, 8n+regs, U32.to_nat(M), N.weaken(r, regs, M.lt_le(r, regs, ok)), b)
  +e2 = M.tofrom(8n+r, M, le)
  %Equal.sym(U32, C.Cir.l.reg(r), U32.from_nat(8n+r), add8(r)) : {Nat.is_lt(U32.to_nat(_), 8n+regs) == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(8n+r)), 8n+r, e2) : {Nat.is_lt(_, 8n+regs) == True{} : Bool}
  ok

# Local indices
# -------------

# True && x = x
def and.true(-c: Bool, -x: Bool, e: {c == True{} : Bool}) -> {Bool.and(c, x) == x : Bool}:
  %Equal.sym(Bool, c, True{}, e) : {Bool.and(_, x) == x : Bool}
  {==}

# the code of an expression uses locals below 8 + regs
def locs.expr(e: C.Cir.Expr, +acc: List<&2, C.Wasm.Instr>, +regs: Nat, +M: U32,
  +ok: {ok.expr(e, regs) == True{} : Bool}, +b: N.Le(8n+regs, U32.to_nat(M))) ->
  {locs(C.Cir.code.expr(e, acc), 8n+regs) == locs(acc, 8n+regs) : Bool}:
  match e:
    case C.Cir.Expr.const{_}:
      {==}
    case C.Cir.Expr.get{+r}:
      and.true(chk(C.Cir.l.reg(r), 8n+regs), locs(acc, 8n+regs), reg.chk(r, regs, M, ok, b))
    case C.Cir.Expr.op{+o, +a, +c}:
      +X = C.Cir.code.expr(c, Con{C.Cir.i.op(o), acc})
      Equal.trans(Bool, locs(C.Cir.code.expr(a, X), 8n+regs), locs(X, 8n+regs), locs(acc, 8n+regs),
        locs.expr(a, X, regs, M, I.and.l(ok.expr(a, regs), ok.expr(c, regs), ok), b),
        locs.expr(c, Con{C.Cir.i.op(o), acc}, regs, M, I.and.r(ok.expr(a, regs), ok.expr(c, regs), ok), b))
    case C.Cir.Expr.eqz{+a}:
      locs.expr(a, Con{C.Wasm.Instr.eqz{}, acc}, regs, M, ok, b)
    case C.Cir.Expr.field{+k, +c}:
      locs.expr(c, C.Cir.code.at(Con{C.Wasm.Instr.load{U32.shln(U32.from_nat(k), 2n)}, acc}), regs, M,
        I.and.r(Nat.is_le(k, 4n), ok.expr(c, regs), ok), b)
    case C.Cir.Expr.byte{+i}:
      locs.expr(i, Con{C.Cir.i.get(0), Con{C.Cir.i.op(C.Wasm.Op.add{}), Con{C.Wasm.Instr.load8_u{0},
        Con{C.Cir.i.const(255), Con{C.Cir.i.op(C.Wasm.Op.and{}), acc}}}}}, regs, M, ok, b)
    case C.Cir.Expr.size{}:
      {==}

# the result and the branch out of run use the runtime's locals only
def locs.result(z: Bool, +l: U32, +regs: Nat) ->
  {locs(List.append(&2, C.Wasm.Instr, C.Cir.code.result(z), [C.Wasm.Instr.br{l}]), 8n+regs) == True{} : Bool}:
  match z:
    case True{}:
      {==}
    case False{}:
      {==}

# the code of alloc, into the local x, uses locals below 8 + regs
def locs.alloc(+x: U32, +d: Nat, +acc: List<&2, C.Wasm.Instr>, +regs: Nat, hx: {chk(x, 8n+regs) == True{} : Bool}) ->
  {locs(C.Cir.code.alloc(x, d, acc), 8n+regs) == locs(acc, 8n+regs) : Bool}:
  %Equal.sym(Bool, chk(x, 8n+regs), True{}, hx) : {Bool.and(_, Bool.and(_, locs(acc, 8n+regs))) == locs(acc, 8n+regs) : Bool}
  {==}

# the code of a statement uses locals below 8 + regs
def locs.stmt(s: C.Cir.Stmt, +d: Nat, +acc: List<&2, C.Wasm.Instr>, +regs: Nat, +M: U32,
  +ok: {ok.stmt(s, regs) == True{} : Bool}, +b: N.Le(8n+regs, U32.to_nat(M))) ->
  {locs(C.Cir.code.stmt(s, d, acc), 8n+regs) == locs(acc, 8n+regs) : Bool}:
  match s:
    case C.Cir.Stmt.nop{}:
      {==}
    case C.Cir.Stmt.set{+r, +e}:
      Equal.trans(Bool, locs(C.Cir.code.expr(e, Con{C.Cir.i.set(C.Cir.l.reg(r)), acc}), 8n+regs), locs(Con{C.Cir.i.set(C.Cir.l.reg(r)), acc}, 8n+regs), locs(acc, 8n+regs),
        locs.expr(e, Con{C.Cir.i.set(C.Cir.l.reg(r)), acc}, regs, M, I.and.r(Nat.is_lt(r, regs), ok.expr(e, regs), ok), b),
        and.true(chk(C.Cir.l.reg(r), 8n+regs), locs(acc, 8n+regs), reg.chk(r, regs, M, I.and.l(Nat.is_lt(r, regs), ok.expr(e, regs), ok), b)))
    case C.Cir.Stmt.store{+k, +c, +v}:
      +X = C.Cir.code.expr(v, Con{C.Wasm.Instr.store{U32.shln(U32.from_nat(k), 2n)}, acc})
      +ab = I.and.l(Bool.and(Nat.is_le(k, 4n), ok.expr(c, regs)), ok.expr(v, regs), ok)
      Equal.trans(Bool, locs(C.Cir.code.expr(c, C.Cir.code.at(X)), 8n+regs), locs(C.Cir.code.at(X), 8n+regs), locs(acc, 8n+regs),
        locs.expr(c, C.Cir.code.at(X), regs, M, I.and.r(Nat.is_le(k, 4n), ok.expr(c, regs), ab), b),
        locs.expr(v, Con{C.Wasm.Instr.store{U32.shln(U32.from_nat(k), 2n)}, acc}, regs, M,
          I.and.r(Bool.and(Nat.is_le(k, 4n), ok.expr(c, regs)), ok.expr(v, regs), ok), b))
    case C.Cir.Stmt.alloc{+r}:
      locs.alloc(C.Cir.l.reg(r), d, acc, regs, reg.chk(r, regs, M, ok, b))
    case C.Cir.Stmt.emit{+v}:
      locs.expr(v, emit.store(acc), regs, M, ok, b)
    case C.Cir.Stmt.seq{+a, +c}:
      +X = C.Cir.code.stmt(c, d, acc)
      Equal.trans(Bool, locs(C.Cir.code.stmt(a, d, X), 8n+regs), locs(X, 8n+regs), locs(acc, 8n+regs),
        locs.stmt(a, d, X, regs, M, I.and.l(ok.stmt(a, regs), ok.stmt(c, regs), ok), b),
        locs.stmt(c, d, acc, regs, M, I.and.r(ok.stmt(a, regs), ok.stmt(c, regs), ok), b))
    case C.Cir.Stmt.if{+c, +t, +e}:
      +T = C.Cir.code.stmt(t, 2n+d, [C.Wasm.Instr.br{1}])
      +X = {Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{0}, T}} : List<&2, C.Wasm.Instr>}
      +E = C.Cir.code.stmt(e, 1n+d, [])
      +ct = I.and.l(Bool.and(ok.expr(c, regs), ok.stmt(t, regs)), ok.stmt(e, regs), ok)
      +e1 = Equal.trans(Bool, locs(C.Cir.code.expr(c, X), 8n+regs), locs(T, 8n+regs), True{},
        locs.expr(c, X, regs, M, I.and.l(ok.expr(c, regs), ok.stmt(t, regs), ct), b),
        locs.stmt(t, 2n+d, [C.Wasm.Instr.br{1}], regs, M, I.and.r(ok.expr(c, regs), ok.stmt(t, regs), ct), b))
      %Equal.sym(Bool, locs(C.Cir.code.expr(c, X), 8n+regs), True{}, e1) : {Bool.and(Bool.and(_, locs(E, 8n+regs)), locs(acc, 8n+regs)) == locs(acc, 8n+regs) : Bool}
      %Equal.sym(Bool, locs(E, 8n+regs), True{}, locs.stmt(e, 1n+d, [], regs, M, I.and.r(Bool.and(ok.expr(c, regs), ok.stmt(t, regs)), ok.stmt(e, regs), ok), b)) :
        {Bool.and(Bool.and(True{}, _), locs(acc, 8n+regs)) == locs(acc, 8n+regs) : Bool}
      {==}
    case C.Cir.Stmt.while{+c, +body}:
      +T = C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])
      +X = {Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, T}} : List<&2, C.Wasm.Instr>}
      +e1 = Equal.trans(Bool, locs(C.Cir.code.expr(c, X), 8n+regs), locs(T, 8n+regs), True{},
        locs.expr(c, X, regs, M, I.and.l(ok.expr(c, regs), ok.stmt(body, regs), ok), b),
        locs.stmt(body, 2n+d, [C.Wasm.Instr.br{0}], regs, M, I.and.r(ok.expr(c, regs), ok.stmt(body, regs), ok), b))
      %Equal.sym(Bool, locs(C.Cir.code.expr(c, X), 8n+regs), True{}, e1) : {Bool.and(Bool.and(_, True{}), locs(acc, 8n+regs)) == locs(acc, 8n+regs) : Bool}
      {==}
    case C.Cir.Stmt.halt{+s}:
      %Equal.sym(Bool, locs(List.append(&2, C.Wasm.Instr, C.Cir.code.result(U32.is_zero(s)), [C.Wasm.Instr.br{U32.from_nat(1n+d)}]), 8n+regs), True{},
        locs.result(U32.is_zero(s), U32.from_nat(1n+d), regs)) : {Bool.and(_, locs(acc, 8n+regs)) == locs(acc, 8n+regs) : Bool}
      {==}

# The memory
# ----------

# a word shifted right with a 0 on top keeps its number
def pad.val(+p: Nat, t: Word(p)) -> {Word.to_nat(1n+p, Word.shr.pad(p, t)) == Word.to_nat(p, t) : Nat}:
  match p:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+q:
      match t:
        case WCon{False{}, +r}:
          Equal.cong(Nat, Nat, v => Nat.double(v), Word.to_nat(1n+q, Word.shr.pad(q, r)), Word.to_nat(q, r), pad.val(q, r))
        case WCon{True{}, +r}:
          Equal.cong(Nat, Nat, v => 1n+Nat.double(v), Word.to_nat(1n+q, Word.shr.pad(q, r)), Word.to_nat(q, r), pad.val(q, r))

# 2 (x >> 1) <= x
def shr.le(x: U32) -> N.Le(Nat.double(U32.to_nat(U32.shr(x))), U32.to_nat(x)):
  match x:
    case U32{w}:
      match w:
        case WCon{False{}, +t}:
          +a = Nat.double(Word.to_nat(31n, t))
          N.le_rw_l(a, Nat.double(Word.to_nat(32n, Word.shr.pad(31n, t))), a,
            Equal.cong(Nat, Nat, v => Nat.double(v), Word.to_nat(31n, t), Word.to_nat(32n, Word.shr.pad(31n, t)),
              Equal.sym(Nat, Word.to_nat(32n, Word.shr.pad(31n, t)), Word.to_nat(31n, t), pad.val(31n, t))),
            N.le_refl(a))
        case WCon{True{}, +t}:
          +a = Nat.double(Word.to_nat(31n, t))
          N.le_rw_l(a, Nat.double(Word.to_nat(32n, Word.shr.pad(31n, t))), 1n+a,
            Equal.cong(Nat, Nat, v => Nat.double(v), Word.to_nat(31n, t), Word.to_nat(32n, Word.shr.pad(31n, t)),
              Equal.sym(Nat, Word.to_nat(32n, Word.shr.pad(31n, t)), Word.to_nat(31n, t), pad.val(31n, t))),
            N.le_succ(a, a, N.le_refl(a)))

# x >> (1 + q) = (x >> 1) >> q
def shrn.succ(+x: U32, q: Nat) -> {U32.shrn(x, 1n+q) == U32.shrn(U32.shr(x), q) : U32}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(U32, U32, y => U32.shr(y), U32.shrn(x, 1n+p), U32.shrn(U32.shr(x), p), shrn.succ(x, p))

# 2^k (x >> k) <= x
def shrn.le(+k: Nat, +x: U32) -> N.Le(N.D(k, U32.to_nat(U32.shrn(x, k))), U32.to_nat(x)):
  match k:
    case 0n:
      N.le_refl(U32.to_nat(x))
    case 1n+q:
      +y = U32.shr(x)
      +a = Nat.double(N.D(q, U32.to_nat(U32.shrn(y, q))))
      +h = N.le_trans(a, Nat.double(U32.to_nat(y)), U32.to_nat(x),
        N.double_mono(N.D(q, U32.to_nat(U32.shrn(y, q))), U32.to_nat(y), shrn.le(q, y)), shr.le(x))
      N.le_rw_l(a, Nat.double(N.D(q, U32.to_nat(U32.shrn(x, 1n+q)))), U32.to_nat(x),
        Equal.cong(U32, Nat, z => Nat.double(N.D(q, U32.to_nat(z))), U32.shrn(y, q), U32.shrn(x, 1n+q),
          Equal.sym(U32, U32.shrn(x, 1n+q), U32.shrn(y, q), shrn.succ(x, q))), h)

# a word of n bits is below 2^n
def word.lt(+n: Nat, w: Word(n)) -> N.Le(1n+Word.to_nat(n, w), N.D(n, 1n)):
  match n:
    case 0n:
      match w:
        case WNil{}:
          Unit{}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          N.lt_dd(Word.to_nat(p, t), N.D(p, 1n), word.lt(p, t))
        case WCon{True{}, +t}:
          N.double_mono(1n+Word.to_nat(p, t), N.D(p, 1n), word.lt(p, t))

# a U32 is below 2^32
def u32.lt(x: U32) -> N.Le(1n+U32.to_nat(x), N.D(32n, 1n)):
  match x:
    case U32{+w}:
      N.le_rw_l(1n+Word.to_nat(32n, w), 1n+U32.to_nat(U32{w}), N.D(32n, 1n),
        Equal.cong(Nat, Nat, v => 1n+v, Word.to_nat(32n, w), U32.to_nat(U32{w}), Equal.sym(Nat, U32.to_nat(U32{w}), Word.to_nat(32n, w), N.u32_to_nat(w))),
        word.lt(32n, w))

# 1 + 2^k a <= 2^k b gives 1 + a <= b
def dlt(+k: Nat, +a: Nat, +b: Nat, h: N.Le(1n+N.D(k, a), N.D(k, b))) -> N.Le(1n+a, b):
  match k:
    case 0n:
      h
    case 1n+q:
      dlt(q, a, b, G.half_lt(N.D(q, a), N.D(q, b), h))

# (x >> 16) + 1 <= 65536: a memory of Cir.pages(b) pages is never too big
def pages.le(+x: U32) -> {U32.is_le(U32.inc(U32.shrn(x, 16n)), 65536) == True{} : Bool}:
  +A = U32.inc(U32.shrn(x, 16n))
  +s = U32.to_nat(U32.shrn(x, 16n))
  +h3 = N.le_trans(1n+N.D(16n, s), 1n+U32.to_nat(x), N.D(32n, 1n), shrn.le(16n, x), u32.lt(x))
  +h4 = N.le_rw_r(1n+N.D(16n, s), N.D(32n, 1n), N.D(16n, N.D(16n, 1n)),
    Equal.sym(Nat, N.D(16n, N.D(16n, 1n)), N.D(32n, 1n), N.D_add(16n, 16n, 32n, 1n, {==})), h3)
  +h5 = dlt(16n, s, N.D(16n, 1n), h4)
  +h6 = N.le_trans(U32.to_nat(A), 1n+s, U32.to_nat(65536), N.U32.inc_le(U32.shrn(x, 16n)),
    N.le_rw_r(1n+s, N.D(16n, 1n), U32.to_nat(65536), Equal.sym(Nat, U32.to_nat(65536), N.D(16n, 1n), N.val_65536()), h5))
  M.le_true(U32.cmp(A, 65536), U32.to_nat(A), U32.to_nat(65536), N.U32.rel(A, 65536), h6)

# The module
# ----------

# run's body uses locals below 8 + regs
def run.locs(+prog: C.Cir.Stmt, +regs: Nat, +k: U32, +M: U32,
  ok: {ok.stmt(prog, regs) == True{} : Bool}, b: N.Le(8n+regs, U32.to_nat(M))) ->
  {locs(M.body(C.Cir.run(prog, regs, k)), 8n+regs) == True{} : Bool}:
  %Equal.sym(Bool, locs(C.Cir.code.stmt(prog, 0n, []), 8n+regs), True{}, locs.stmt(prog, 0n, [], regs, M, ok, b)) :
    {Bool.and(_, True{}) == True{} : Bool}
  {==}

# run is valid, with 8 + regs <= M locals
def run.ok(+prog: C.Cir.Stmt, +regs: Nat, +k: U32, +M: U32,
  ok: {ok.stmt(prog, regs) == True{} : Bool}, +b: N.Le(8n+regs, U32.to_nat(M))) ->
  {C.Wasm.valid.func(True{}, C.Cir.run(prog, regs, k)) == True{} : Bool}:
  +B = M.body(C.Cir.run(prog, regs, k))
  +loc = U32.from_nat(8n+regs)
  +eg = go.free(B, 0n, [1n], loc, 8n+regs, True{}, M.tofrom(8n+regs, M, b), run.locs(prog, regs, k, M, ok, b))
  %Equal.sym(Maybe<&2, C.Wasm.Height>, C.Wasm.valid.go(B, 0n, [1n], loc, True{}), free.go(B, 0n, [1n], True{}), eg) :
    {C.Wasm.valid.is_results(_, 1n) == True{} : Bool}
  %Equal.sym(Maybe<&2, C.Wasm.Height>, free.go(C.Cir.code.stmt(prog, 0n, []), 0n, lab(0n), True{}), free.go([], 0n, lab(0n), True{}),
    free.stmt(prog, 0n, [], 0n)) :
    {C.Wasm.valid.is_results(C.Wasm.valid.if(C.Wasm.valid.is_empty(_), u => Some{C.Wasm.Height.at{1n}}), 1n) == True{} : Bool}
  {==}

# the module is valid, with 8 + regs <= M locals in run
def module.sized(+prog: C.Cir.Stmt, +regs: Nat, +cells: List<&2, C.Cir.Cell>, +M: U32,
  ok: {ok.stmt(prog, regs) == True{} : Bool}, +b: N.Le(8n+regs, U32.to_nat(M))) ->
  {C.Wasm.valid.module(C.Cir.module(prog, regs, cells)) == True{} : Bool}:
  +k = C.Wasm.encode.len(C.Cir.Cell, cells)
  %Equal.sym(Bool, U32.is_le(C.Cir.pages(C.Cir.input.at(k)), 65536), True{}, pages.le(U32.sub(C.Cir.input.at(k), 1))) :
    {Bool.and(Bool.and(Bool.and(Bool.and(_, True{}), Bool.and(C.Wasm.valid.func(True{}, C.Cir.run(prog, regs, k)), True{})), True{}), True{}) == True{} : Bool}
  %Equal.sym(Bool, C.Wasm.valid.func(True{}, C.Cir.run(prog, regs, k)), True{}, run.ok(prog, regs, k, M, ok, b)) :
    {Bool.and(Bool.and(Bool.and(Bool.and(True{}, True{}), Bool.and(_, True{})), True{}), True{}) == True{} : Bool}
  {==}

# 6 + regs <= W gives 8 + regs <= W + 2, when W + 1 and W + 2 do not wrap
def regs.le(+regs: Nat, +W: U32, hr: N.Le(6n+regs, U32.to_nat(W)),
  z1: {False{} == U32.is_zero(U32.inc(W)) : Bool}, z2: {False{} == U32.is_zero(U32.inc(U32.inc(W))) : Bool}) ->
  N.Le(8n+regs, U32.to_nat(U32.inc(U32.inc(W)))):
  +W1 = U32.inc(W)
  +W2 = U32.inc(W1)
  +e = Equal.trans(Nat, U32.to_nat(W2), 1n+U32.to_nat(W1), 2n+U32.to_nat(W), I.U32.inc_nat(W1, z2),
    Equal.cong(Nat, Nat, v => 1n+v, U32.to_nat(W1), 1n+U32.to_nat(W), I.U32.inc_nat(W, z1)))
  N.le_rw_r(8n+regs, 2n+U32.to_nat(W), U32.to_nat(W2), Equal.sym(Nat, U32.to_nat(W2), 2n+U32.to_nat(W), e), hr)

# The validity of the modules
# ---------------------------

# Wasm.valid.module accepts the module of Cir.module when every register of
# the program is below regs, every field is at most 4 (ok.stmt), and run has
# at most 50000 locals (the premise of M.module.round, which also keeps the
# locals' indices, at most 8 + regs, below 2^32)
def valid.module(+prog: C.Cir.Stmt, +regs: Nat, +cells: List<&2, C.Cir.Cell>,
  ok: {ok.stmt(prog, regs) == True{} : Bool},
  hr: {Nat.is_le(6n+regs, U32.to_nat(50000)) == True{} : Bool}) ->
  {C.Wasm.valid.module(C.Cir.module(prog, regs, cells)) == True{} : Bool}:
  module.sized(prog, regs, cells, U32.inc(U32.inc(50000)), ok, regs.le(regs, 50000, N.toLe(6n+regs, U32.to_nat(50000), hr), {==}, {==}))

# The machine and halt
# --------------------

# the machine's program uses only its registers and fields 0 to 4
def mach.ok() -> {ok.stmt(C.Mach.code(), C.Mach.regs()) == True{} : Bool}:
  {==}

# halt uses no register
def halt.regs(+s: U32) -> {ok.stmt(C.Cir.Stmt.halt{s}, 0n) == True{} : Bool}:
  {==}

# the machine's module is valid, for every image
def valid.machine(+cells: List<&2, C.Cir.Cell>) -> {C.Wasm.valid.module(C.Cir.module(C.Mach.code(), C.Mach.regs(), cells)) == True{} : Bool}:
  valid.module(C.Mach.code(), C.Mach.regs(), cells, mach.ok(), {==})

# the module of halt is valid
def valid.halt(+s: U32) -> {C.Wasm.valid.module(C.Cir.module(C.Cir.Stmt.halt{s}, 0n, [])) == True{} : Bool}:
  valid.module(C.Cir.Stmt.halt{s}, 0n, [], halt.regs(s), {==})
