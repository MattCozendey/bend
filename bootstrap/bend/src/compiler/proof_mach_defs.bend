# compiler: layer B's shared definitions
# ======================================
#
# What the phases of the machine (M.input, M.copy, M.data, M.walk, M.out)
# and the moves of proof_mach.bend share: the kit (Post, Ends, mono), the
# terms of states (A.*), the invariant (Is, Frs, the heap Heap and HS,
# ImgOK, Inv), the shapes of a round (Rnd, HR) and of the start (St0,
# Start, InvIn), the conclusions of the phases' premises (CopyPost,
# CopyDone, DataPost, DataDone, WalkPost, WalkDone, OutPost, OutDone,
# InputPost, InputDone), the heap's operations (inc.post, dec.post,
# alloc.post, release.post, ptr.bound, is.pend, is.fresh: open), the stores
# that keep the terms (is.st, is.f1, frs.f1), the word and cell kit and the
# run of statements (eq.*, rw.*, ev.*). It imports no phase file.

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

def Ex.fst(-A: Data, -B: @-x: A -> Data, p: Ex(A, B)) -> A:
  match p:
    case Tuple{a, _}:
      a

def Ex.snd(-A: Data, -B: @-x: A -> Data, p: Ex(A, B)) -> B(Ex.fst(A, B, p)):
  match p:
    case Tuple{_, b}:
      b

# a run that must end may not run out of fuel
def ND(dn: Bool) -> Type:
  match dn:
    case True{}:
      Empty
    case False{}:
      Unit

# what the outcome o of a statement may be: next, with a state of which Q
# holds; a halt with the status s in the state st, of which H holds; out of
# memory; never a trap; out of fuel only when dn is False
def Post(dn: Bool, o: C.Cir.Out, Q: C.Cir.State -> Type, H: U32 -> C.Cir.State -> Type) -> Type:
  match o:
    case C.Cir.Out.next{st}:
      Q(st)
    case C.Cir.Out.halt{s, st}:
      H(s, st)
    case C.Cir.Out.out_of_memory{}:
      Unit
    case C.Cir.Out.trap{}:
      Empty
    case C.Cir.Out.not_done{}:
      ND(dn)

# the run ends: anything but out of fuel
def Ends(o: C.Cir.Out) -> Data:
  match o:
    case C.Cir.Out.next{_}:
      Unit
    case C.Cir.Out.halt{_, _}:
      Unit
    case C.Cir.Out.out_of_memory{}:
      Unit
    case C.Cir.Out.trap{}:
      Unit
    case C.Cir.Out.not_done{}:
      Empty

# a statement, then more: Q of the first gives what the rest may be
def post.then(dn: Bool, o: C.Cir.Out, -k: C.Cir.State -> C.Cir.Out, -Q: C.Cir.State -> Type, -R: C.Cir.State -> Type,
  -H1: U32 -> C.Cir.State -> Type, -H2: U32 -> C.Cir.State -> Type,
  h: Post(dn, o, Q, H1), hh: @s: U32 -> @st: C.Cir.State -> H1(s, st) -> H2(s, st),
  g: @st: C.Cir.State -> Q(st) -> Post(dn, k(st), R, H2)) -> Post(dn, C.Cir.exec.then(o, k), R, H2):
  match o:
    case C.Cir.Out.next{st}:
      g(st, h)
    case C.Cir.Out.halt{s, st}:
      hh(s, st, h)
    case C.Cir.Out.out_of_memory{}:
      Unit{}
    case C.Cir.Out.trap{}:
      h
    case C.Cir.Out.not_done{}:
      h

# a then b, for any fuel
def post.seq(+f: Nat, dn: Bool, a: C.Cir.Stmt, +b: C.Cir.Stmt, +st: C.Cir.State, -Q: C.Cir.State -> Type,
  -R: C.Cir.State -> Type, -H1: U32 -> C.Cir.State -> Type, -H2: U32 -> C.Cir.State -> Type,
  h: Post(dn, C.Cir.exec(f, a, st), Q, H1), hh: @s: U32 -> @st: C.Cir.State -> H1(s, st) -> H2(s, st),
  g: @st: C.Cir.State -> Q(st) -> Post(dn, C.Cir.exec(f, b, st), R, H2)) ->
  Post(dn, C.Cir.exec(f, C.Cir.Stmt.seq{a, b}, st), R, H2):
  match f:
    case 0n:
      post.then(dn, C.Cir.exec(0n, a, st), t => C.Cir.exec(0n, b, t), Q, R, H1, H2, h, hh, g)
    case 1n+p:
      post.then(dn, C.Cir.exec(1n+p, a, st), t => C.Cir.exec(1n+p, b, t), Q, R, H1, H2, h, hh, g)

# a run that ends, and holds what Post(False) says, holds what Post(True) says
def post.ends(o: C.Cir.Out, -Q: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type, h: Post(False{}, o, Q, H),
  d: Ends(o)) -> Post(True{}, o, Q, H):
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
      d

# Post(True) says the run ends
def post.end(o: C.Cir.Out, -Q: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type, h: Post(True{}, o, Q, H)) ->
  Ends(o):
  match o:
    case C.Cir.Out.next{st}:
      Unit{}
    case C.Cir.Out.halt{s, st}:
      Unit{}
    case C.Cir.Out.out_of_memory{}:
      Unit{}
    case C.Cir.Out.trap{}:
      Unit{}
    case C.Cir.Out.not_done{}:
      h

# More fuel
# ---------
#
# A run that ends with the fuel f ends the same with any fuel g >= f (mono),
# by induction on f, then on the statement.

def ends.then(o: C.Cir.Out, -k: C.Cir.State -> C.Cir.Out, d: Ends(C.Cir.exec.then(o, k))) -> Ends(o):
  match o:
    case C.Cir.Out.next{st}:
      Unit{}
    case C.Cir.Out.halt{s, st}:
      Unit{}
    case C.Cir.Out.out_of_memory{}:
      Unit{}
    case C.Cir.Out.trap{}:
      Unit{}
    case C.Cir.Out.not_done{}:
      d

# the rest of a seq, after the same outcome o
def mono.then(o: C.Cir.Out, -f: Nat, -g: Nat, -b: C.Cir.Stmt, d: Ends(C.Cir.exec.then(o, t => C.Cir.exec(f, b, t))),
  ih: @t: C.Cir.State -> Ends(C.Cir.exec(f, b, t)) -> {C.Cir.exec(f, b, t) == C.Cir.exec(g, b, t) : C.Cir.Out}) ->
  {C.Cir.exec.then(o, t => C.Cir.exec(f, b, t)) == C.Cir.exec.then(o, t => C.Cir.exec(g, b, t)) : C.Cir.Out}:
  match o:
    case C.Cir.Out.next{st}:
      ih(st, d)
    case C.Cir.Out.halt{s, st}:
      {==}
    case C.Cir.Out.out_of_memory{}:
      {==}
    case C.Cir.Out.trap{}:
      {==}
    case C.Cir.Out.not_done{}:
      {==}

# a seq: its first part by ha, then the rest by ih
def mono.seq(+f: Nat, -g: Nat, +a: C.Cir.Stmt, -b: C.Cir.Stmt, +st: C.Cir.State,
  +d: Ends(C.Cir.exec.then(C.Cir.exec(f, a, st), t => C.Cir.exec(f, b, t))),
  ha: Ends(C.Cir.exec(f, a, st)) -> {C.Cir.exec(f, a, st) == C.Cir.exec(g, a, st) : C.Cir.Out},
  ih: @t: C.Cir.State -> Ends(C.Cir.exec(f, b, t)) -> {C.Cir.exec(f, b, t) == C.Cir.exec(g, b, t) : C.Cir.Out}) ->
  {C.Cir.exec.then(C.Cir.exec(f, a, st), t => C.Cir.exec(f, b, t)) ==
    C.Cir.exec.then(C.Cir.exec(g, a, st), t => C.Cir.exec(g, b, t)) : C.Cir.Out}:
  +e = ha(ends.then(C.Cir.exec(f, a, st), t => C.Cir.exec(f, b, t), d))
  %e : {C.Cir.exec.then(C.Cir.exec(f, a, st), t => C.Cir.exec(f, b, t)) ==
    C.Cir.exec.then(_, t => C.Cir.exec(g, b, t)) : C.Cir.Out}
  mono.then(C.Cir.exec(f, a, st), f, g, b, d, ih)

def mono.if.of(z: Bool, -f: Nat, -g: Nat, -t: C.Cir.Stmt, -e: C.Cir.Stmt, -st: C.Cir.State,
  d: Ends(C.Cir.exec.if.of(z, u => C.Cir.exec(f, t, st), u => C.Cir.exec(f, e, st))),
  ht: Ends(C.Cir.exec(f, t, st)) -> {C.Cir.exec(f, t, st) == C.Cir.exec(g, t, st) : C.Cir.Out},
  he: Ends(C.Cir.exec(f, e, st)) -> {C.Cir.exec(f, e, st) == C.Cir.exec(g, e, st) : C.Cir.Out}) ->
  {C.Cir.exec.if.of(z, u => C.Cir.exec(f, t, st), u => C.Cir.exec(f, e, st)) ==
    C.Cir.exec.if.of(z, u => C.Cir.exec(g, t, st), u => C.Cir.exec(g, e, st)) : C.Cir.Out}:
  match z:
    case False{}:
      ht(d)
    case True{}:
      he(d)

# an if: the branch that its condition takes
def mono.if(c: Maybe<&2, U32>, -f: Nat, -g: Nat, -t: C.Cir.Stmt, -e: C.Cir.Stmt, -st: C.Cir.State,
  d: Ends(C.Cir.exec.if(c, u => C.Cir.exec(f, t, st), u => C.Cir.exec(f, e, st))),
  ht: Ends(C.Cir.exec(f, t, st)) -> {C.Cir.exec(f, t, st) == C.Cir.exec(g, t, st) : C.Cir.Out},
  he: Ends(C.Cir.exec(f, e, st)) -> {C.Cir.exec(f, e, st) == C.Cir.exec(g, e, st) : C.Cir.Out}) ->
  {C.Cir.exec.if(c, u => C.Cir.exec(f, t, st), u => C.Cir.exec(f, e, st)) ==
    C.Cir.exec.if(c, u => C.Cir.exec(g, t, st), u => C.Cir.exec(g, e, st)) : C.Cir.Out}:
  match c:
    case Some{x}:
      mono.if.of(U32.is_zero(x), f, g, t, e, st, d, ht, he)
    case None{}:
      {==}

def mono.wh.of(z: Bool, -f: Nat, -g: Nat, -c: C.Cir.Expr, -body: C.Cir.Stmt, -st: C.Cir.State,
  d: Ends(C.Cir.exec.if.of(z, u => C.Cir.exec.then(C.Cir.exec(f, body, st), t => C.Cir.exec(f, C.Cir.Stmt.while{c, body}, t)),
    u => C.Cir.Out.next{st})),
  h: Ends(C.Cir.exec.then(C.Cir.exec(f, body, st), t => C.Cir.exec(f, C.Cir.Stmt.while{c, body}, t))) ->
    {C.Cir.exec.then(C.Cir.exec(f, body, st), t => C.Cir.exec(f, C.Cir.Stmt.while{c, body}, t)) ==
      C.Cir.exec.then(C.Cir.exec(g, body, st), t => C.Cir.exec(g, C.Cir.Stmt.while{c, body}, t)) : C.Cir.Out}) ->
  {C.Cir.exec.if.of(z, u => C.Cir.exec.then(C.Cir.exec(f, body, st), t => C.Cir.exec(f, C.Cir.Stmt.while{c, body}, t)),
    u => C.Cir.Out.next{st}) ==
   C.Cir.exec.if.of(z, u => C.Cir.exec.then(C.Cir.exec(g, body, st), t => C.Cir.exec(g, C.Cir.Stmt.while{c, body}, t)),
    u => C.Cir.Out.next{st}) : C.Cir.Out}:
  match z:
    case False{}:
      h(d)
    case True{}:
      {==}

# a round of a while: its body, then the while again
def mono.wh(v: Maybe<&2, U32>, -f: Nat, -g: Nat, -c: C.Cir.Expr, -body: C.Cir.Stmt, -st: C.Cir.State,
  d: Ends(C.Cir.exec.if(v, u => C.Cir.exec.then(C.Cir.exec(f, body, st), t => C.Cir.exec(f, C.Cir.Stmt.while{c, body}, t)),
    u => C.Cir.Out.next{st})),
  h: Ends(C.Cir.exec.then(C.Cir.exec(f, body, st), t => C.Cir.exec(f, C.Cir.Stmt.while{c, body}, t))) ->
    {C.Cir.exec.then(C.Cir.exec(f, body, st), t => C.Cir.exec(f, C.Cir.Stmt.while{c, body}, t)) ==
      C.Cir.exec.then(C.Cir.exec(g, body, st), t => C.Cir.exec(g, C.Cir.Stmt.while{c, body}, t)) : C.Cir.Out}) ->
  {C.Cir.exec.if(v, u => C.Cir.exec.then(C.Cir.exec(f, body, st), t => C.Cir.exec(f, C.Cir.Stmt.while{c, body}, t)),
    u => C.Cir.Out.next{st}) ==
   C.Cir.exec.if(v, u => C.Cir.exec.then(C.Cir.exec(g, body, st), t => C.Cir.exec(g, C.Cir.Stmt.while{c, body}, t)),
    u => C.Cir.Out.next{st}) : C.Cir.Out}:
  match v:
    case Some{x}:
      mono.wh.of(U32.is_zero(x), f, g, c, body, st, d, h)
    case None{}:
      {==}

# more fuel keeps a run that ends
def mono(+f: Nat, +g: Nat, +s: C.Cir.Stmt, +st: C.Cir.State, +le: N.Le(f, g), +d: Ends(C.Cir.exec(f, s, st))) ->
  {C.Cir.exec(f, s, st) == C.Cir.exec(g, s, st) : C.Cir.Out}:
  match f g:
    case 0n 0n:
      {==}
    case 0n 1n+h:
      match s:
        case C.Cir.Stmt.nop{}:
          {==}
        case C.Cir.Stmt.set{r, e}:
          {==}
        case C.Cir.Stmt.store{k, c, v}:
          {==}
        case C.Cir.Stmt.alloc{r}:
          {==}
        case C.Cir.Stmt.emit{v}:
          {==}
        case C.Cir.Stmt.seq{+a, +b}:
          mono.seq(0n, 1n+h, a, b, st, d, x => mono(0n, 1n+h, a, st, le, x), t => x => mono(0n, 1n+h, b, t, le, x))
        case C.Cir.Stmt.if{c, +t, +e}:
          mono.if(C.Cir.eval(c, st), 0n, 1n+h, t, e, st, d, x => mono(0n, 1n+h, t, st, le, x),
            x => mono(0n, 1n+h, e, st, le, x))
        case C.Cir.Stmt.while{c, body}:
          Empty.absurd({C.Cir.exec(0n, C.Cir.Stmt.while{c, body}, st) == C.Cir.exec(1n+h, C.Cir.Stmt.while{c, body}, st) : C.Cir.Out}, d)
        case C.Cir.Stmt.halt{x}:
          {==}
    case 1n+p 0n:
      Empty.absurd({C.Cir.exec(1n+p, s, st) == C.Cir.exec(0n, s, st) : C.Cir.Out}, le)
    case 1n+p 1n+h:
      match s:
        case C.Cir.Stmt.nop{}:
          {==}
        case C.Cir.Stmt.set{r, e}:
          {==}
        case C.Cir.Stmt.store{k, c, v}:
          {==}
        case C.Cir.Stmt.alloc{r}:
          {==}
        case C.Cir.Stmt.emit{v}:
          {==}
        case C.Cir.Stmt.seq{+a, +b}:
          mono.seq(1n+p, 1n+h, a, b, st, d, x => mono(1n+p, 1n+h, a, st, le, x), t => x => mono(1n+p, 1n+h, b, t, le, x))
        case C.Cir.Stmt.if{c, +t, +e}:
          mono.if(C.Cir.eval(c, st), 1n+p, 1n+h, t, e, st, d, x => mono(1n+p, 1n+h, t, st, le, x),
            x => mono(1n+p, 1n+h, e, st, le, x))
        case C.Cir.Stmt.while{+c, +body}:
          mono.wh(C.Cir.eval(c, st), p, h, c, body, st, d,
            x => mono.seq(p, h, body, C.Cir.Stmt.while{c, body}, st, x, y => mono(p, h, body, st, le, y),
              t => y => mono(p, h, C.Cir.Stmt.while{c, body}, t, le, y)))
        case C.Cir.Stmt.halt{x}:
          {==}

# Terms of states
# ---------------
#
# A state as Lean's State (Machine.lean): a focus, to evaluate or a value,
# and its frames, the innermost first. A frame is a term with a hole, of a
# kind (the machine's K.app_arg to K.min_a), a quantity q, the flag K (k), and
# the terms a (in its field 2) and b (in its field 3, for Rwt).

type FK is Data:
  FK.arg{}
  FK.val{}
  FK.fun{}
  FK.let{}
  FK.tupb{}
  FK.tupa{}
  FK.rwt{}
  FK.minb{}
  FK.mina{}

# the tag of a frame's cell
def FK.tag(k: FK) -> U32:
  match k:
    case FK.arg{}:
      32
    case FK.val{}:
      33
    case FK.fun{}:
      34
    case FK.let{}:
      35
    case FK.tupb{}:
      36
    case FK.tupa{}:
      37
    case FK.rwt{}:
      38
    case FK.minb{}:
      39
    case FK.mina{}:
      40

type AF is Data:
  AF{kind: FK, q: C.Quan, k: Bool, a: C.Term, b: C.Term}

# the frame with t in its hole (Frame.plug)
def A.plug(fr: AF, t: C.Term) -> C.Term:
  match fr:
    case AF{FK.arg{}, q, _, a, _}:
      C.Term.App{q, t, a}
    case AF{FK.val{}, q, _, a, _}:
      C.Term.App{q, t, a}
    case AF{FK.fun{}, q, _, a, _}:
      C.Term.App{q, a, t}
    case AF{FK.let{}, q, _, a, _}:
      C.Term.Let{q, t, a}
    case AF{FK.tupb{}, q, _, a, _}:
      C.Term.Tup{q, t, a}
    case AF{FK.tupa{}, q, _, a, _}:
      C.Term.Tup{q, a, t}
    case AF{FK.rwt{}, _, _, a, b}:
      C.Term.Rwt{t, a, b}
    case AF{FK.minb{}, _, _, a, _}:
      C.Term.Min{t, a}
    case AF{FK.mina{}, _, _, a, _}:
      C.Term.Min{a, t}

# the frames fs around t, the innermost first (plugs)
def A.plugs(fs: List<&2, AF>, t: C.Term) -> C.Term:
  match fs:
    case Nil{}:
      t
    case Con{fr, rest}:
      A.plugs(rest, A.plug(fr, t))

def Nat.of(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# 3 × the nodes of t: the measure of a term to evaluate
def A.w3(t: C.Term) -> Nat:
  +s = C.Term.size(t)
  Nat.add(s, Nat.add(s, s))

# the measure of a frame: what its admin moves still cost, before a step
def A.w.frame(fr: AF) -> Nat:
  match fr:
    case AF{FK.arg{}, +q, +k, a, _}:
      Bool.pick(Nat, Bool.and(C.Quan.live(q), Bool.not(k)), 2n+A.w3(a), 1n)
    case AF{FK.val{}, +q, +k, a, _}:
      Bool.pick(Nat, Bool.and(C.Quan.live(q), Bool.not(k)), 2n+A.w3(a), 1n)
    case AF{FK.fun{}, _, _, _, _}:
      1n
    case AF{FK.let{}, _, _, _, _}:
      0n
    case AF{FK.tupb{}, _, _, a, _}:
      2n+A.w3(a)
    case AF{FK.tupa{}, _, _, _, _}:
      1n
    case AF{FK.rwt{}, _, _, _, _}:
      0n
    case AF{FK.minb{}, _, _, a, _}:
      1n+A.w3(a)
    case AF{FK.mina{}, _, _, _, _}:
      0n

def A.w.frames(fs: List<&2, AF>) -> Nat:
  match fs:
    case Nil{}:
      0n
    case Con{fr, rest}:
      Nat.add(A.w.frame(fr), A.w.frames(rest))

# the measure of a state: its frames', and its focus' when it is to evaluate
def A.w(ret: Bool, focus: C.Term, fs: List<&2, AF>) -> Nat:
  Nat.add(Bool.pick(Nat, ret, 0n, A.w3(focus)), A.w.frames(fs))

# what a frame knows (Frame.Ok): the function of App q f □ is a value, and q
# is live; a known argument is a value; Let and Tup □ b are live; the first
# field of Tup q a □ is a value when q is live; Min a □ holds a value
def AF.ok(+ds: List<&2, C.Def>, fr: AF) -> Data:
  match fr:
    case AF{FK.arg{}, _, k, a, _}:
      {Bool.or(Bool.not(k), C.Eval.vals(ds, a, False{})) == True{} : Bool}
    case AF{FK.val{}, _, k, a, _}:
      {Bool.or(Bool.not(k), C.Eval.vals(ds, a, False{})) == True{} : Bool}
    case AF{FK.fun{}, q, _, a, _}:
      {Bool.and(C.Quan.live(q), C.Eval.vals(ds, a, False{})) == True{} : Bool}
    case AF{FK.let{}, q, _, _, _}:
      {C.Quan.live(q) == True{} : Bool}
    case AF{FK.tupb{}, q, _, _, _}:
      {C.Quan.live(q) == True{} : Bool}
    case AF{FK.tupa{}, q, _, a, _}:
      {Bool.or(Bool.not(C.Quan.live(q)), C.Eval.vals(ds, a, False{})) == True{} : Bool}
    case AF{FK.rwt{}, _, _, _, _}:
      Unit
    case AF{FK.minb{}, _, _, _, _}:
      Unit
    case AF{FK.mina{}, _, _, a, _}:
      {C.Eval.vals(ds, a, False{}) == True{} : Bool}

def AFs.ok(+ds: List<&2, C.Def>, fs: List<&2, AF>) -> Data:
  match fs:
    case Nil{}:
      Unit
    case Con{fr, rest}:
      P2(AF.ok(ds, fr), AFs.ok(ds, rest))

# The invariant
# -------------

# field k of the cell c
def Fd(k: Nat, m: C.Cir.Cells, +c: U32) -> U32:
  C.Cir.Cell.get(k, C.Cir.Cells.get(m, c))

# the parts of field 0, as the machine reads them (M.tag, M.q, M.flag, M.fv)
def Tg(m: C.Cir.Cells, +c: U32) -> U32:
  U32.and(Fd(0n, m, c), 63)

def Qn(m: C.Cir.Cells, +c: U32) -> U32:
  U32.and(U32.shrn(Fd(0n, m, c), 6n), 3)

def Fl(m: C.Cir.Cells, +c: U32, fl: U32) -> Bool:
  U32.is_ne(U32.and(Fd(0n, m, c), fl), 0)

def Fv(m: C.Cir.Cells, +c: U32) -> U32:
  U32.shrn(Fd(0n, m, c), 13n)

# c is one of the machine's own cells, from fi, before nx
def Own(+fi: U32, +nx: U32, +c: U32) -> Bool:
  Bool.and(U32.is_le(fi, c), U32.is_lt(c, nx))

# every free variable of t is below n (Term.subst's binders)
def Term.below(t: C.Term, +n: Nat) -> Bool:
  match t:
    case C.Term.Var{i}:
      Nat.is_lt(i, n)
    case C.Term.Ref{_}:
      True{}
    case C.Term.Ann{x, T}:
      Bool.and(Term.below(x, n), Term.below(T, n))
    case C.Term.Let{_, v, f}:
      Bool.and(Term.below(v, n), Term.below(f, 1n+n))
    case C.Term.Typ{x}:
      Term.below(x, n)
    case C.Term.Min{a, b}:
      Bool.and(Term.below(a, n), Term.below(b, n))
    case C.Term.All{_, A, B}:
      Bool.and(Term.below(A, n), Term.below(B, 1n+n))
    case C.Term.Lam{_, f}:
      Term.below(f, 1n+n)
    case C.Term.App{_, f, x}:
      Bool.and(Term.below(f, n), Term.below(x, n))
    case C.Term.Sig{_, A, B}:
      Bool.and(Term.below(A, n), Term.below(B, 1n+n))
    case C.Term.Tup{_, a, b}:
      Bool.and(Term.below(a, n), Term.below(b, n))
    case C.Term.Prj{h}:
      Term.below(h, n)
    case C.Term.Enu{_}:
      True{}
    case C.Term.Lab{_}:
      True{}
    case C.Term.Mat{_, h, m}:
      Bool.and(Term.below(h, n), Term.below(m, n))
    case C.Term.Efq{}:
      True{}
    case C.Term.Eql{a, b, T}:
      Bool.and(Term.below(a, n), Bool.and(Term.below(b, n), Term.below(T, n)))
    case C.Term.Rfl{}:
      True{}
    case C.Term.Rwt{e, P, f}:
      Bool.and(Term.below(e, n), Bool.and(Term.below(P, 2n+n), Term.below(f, n)))

# the parts of field 0 of a cell, as the machine reads them
def TgW(+f0: U32) -> U32:
  U32.and(f0, 63)

def QnW(+f0: U32) -> U32:
  U32.and(U32.shrn(f0, 6n), 3)

def FlW(+f0: U32, fl: U32) -> Bool:
  U32.is_ne(U32.and(f0, fl), 0)

def FvW(+f0: U32) -> U32:
  U32.shrn(f0, 13n)

# what the flag DATA of the field 0 f0 says of the term t, when dk asks for
# it (Is, Inv): t is Data. Inside M.data the flag may be set ahead of the
# check that fails (the run then halts), so the heap's operations hold for
# either dk (HSK)
def DataK(dk: Bool, +f0: U32, t: C.Term) -> Data:
  match dk:
    case True{}:
      {Bool.or(Bool.not(FlW(f0, 512)), C.Term.is_data(t)) == True{} : Bool}
    case False{}:
      Unit

# what the cell c, of the value x, of the term t says of itself: it is a
# cell; one of the machine's own, or STATIC; its tag; VALUE says t is a value,
# DATA that it is Data (when dk); fv bounds its free variables, unless it is
# fv_max
def NdK(+dk: Bool, +ds: List<&2, C.Def>, +im: U32, +fi: U32, +nx: U32, +c: U32, +x: C.Cir.Cell, +t: C.Term, +tag: U32) -> Data:
  +f0 = C.Cir.Cell.get(0n, x)
  P2({C.Cir.is_cell(c, im, fi, nx) == True{} : Bool},
  P2({Bool.or(Own(fi, nx, c), FlW(f0, 1024)) == True{} : Bool},
  P2({TgW(f0) == tag : U32},
  P2({Bool.or(Bool.not(FlW(f0, 256)), C.Eval.vals(ds, t, False{})) == True{} : Bool},
  P2(DataK(dk, f0, t),
    {Bool.or(U32.is_eq(FvW(f0), 524287), Term.below(t, U32.to_nat(FvW(f0)))) == True{} : Bool})))))

def Nd(+ds: List<&2, C.Def>, +im: U32, +fi: U32, +nx: U32, +c: U32, +x: C.Cir.Cell, +t: C.Term, +tag: U32) -> Data:
  NdK(True{}, ds, im, fi, nx, c, x, t, tag)

# the quantity of the cell x is q
def Qs(+x: C.Cir.Cell, q: C.Quan) -> Data:
  {QnW(C.Cir.Cell.get(0n, x)) == C.Img.quan(q) : U32}

# the name of a label or a λ-match: its place in the image's names ks, the
# first of the name k
def Nm(+ks: List<&2, List<&2, U32>>, +x: C.Cir.Cell, +k: List<&2, U32>) -> Data:
  P2({T.tm.name(ks, C.Cir.Cell.get(2n, x)) == Some{k} : Maybe<&2, List<&2, U32>>},
    {C.Cir.Cell.get(2n, x) == C.Img.id(ks, k, 0) : U32})

# a part y of the cell c is STATIC, or c is one of the machine's own: no cell of
# the image points to one of the machine's
def Sp(+fi: U32, +nx: U32, +c: U32, +y: C.Cir.Cell) -> Data:
  {Bool.or(Own(fi, nx, c), FlW(C.Cir.Cell.get(0n, y), 1024)) == True{} : Bool}

# the cell c, of the value x in the cells m, stands for the term t: by the
# tag and the parts of each of its cells, as T.tm.of reads them; a Ref or an
# Enu is one of the image's, img its term, and a Ref holds the body of the
# first def of its name, where the image places it (Img.ref)
def IsCK(+dk: Bool, +ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +c: U32, +x: C.Cir.Cell, t: C.Term) -> Data:
  match t:
    case C.Term.Var{+i}:
      P2(NdK(dk, ds, im, fi, nx, c, x, C.Term.Var{i}, 0), {U32.to_nat(C.Cir.Cell.get(2n, x)) == i : Nat})
    case C.Term.Ref{+k}:
      P2(NdK(dk, ds, im, fi, nx, c, x, C.Term.Ref{k}, 1),
      P2({T.tm.image(img, c) == Some{C.Term.Ref{k}} : Maybe<&2, C.Term>},
      P2({FvW(C.Cir.Cell.get(0n, x)) == 0 : U32},
        {C.Cir.Cell.get(2n, x) == C.Img.ref(C.Img.defs(ds, C.I.book()), k) : U32})))
    case C.Term.Ann{+y, +z}:
      P2(NdK(dk, ds, im, fi, nx, c, x, C.Term.Ann{y, z}, 2),
      P2(P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x)), y)), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(3n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x)), z))))
    case C.Term.Let{+q, +v, +f}:
      P2(NdK(dk, ds, im, fi, nx, c, x, C.Term.Let{q, v, f}, 3), P2(Qs(x, q),
      P2(P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x)), v)), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(3n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x)), f)))))
    case C.Term.Typ{+y}:
      P2(NdK(dk, ds, im, fi, nx, c, x, C.Term.Typ{y}, 4), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x)), y)))
    case C.Term.Min{+a, +b}:
      P2(NdK(dk, ds, im, fi, nx, c, x, C.Term.Min{a, b}, 5),
      P2(P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x)), a)), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(3n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x)), b))))
    case C.Term.All{+q, +a, +b}:
      P2(NdK(dk, ds, im, fi, nx, c, x, C.Term.All{q, a, b}, 6), P2(Qs(x, q),
      P2(P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x)), a)), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(3n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x)), b)))))
    case C.Term.Lam{+q, +f}:
      P2(NdK(dk, ds, im, fi, nx, c, x, C.Term.Lam{q, f}, 7), P2(Qs(x, q), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x)), f))))
    case C.Term.App{+q, +f, +y}:
      P2(NdK(dk, ds, im, fi, nx, c, x, C.Term.App{q, f, y}, 8), P2(Qs(x, q),
      P2(P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x)), f)), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(3n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x)), y)))))
    case C.Term.Sig{+q, +a, +b}:
      P2(NdK(dk, ds, im, fi, nx, c, x, C.Term.Sig{q, a, b}, 9), P2(Qs(x, q),
      P2(P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x)), a)), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(3n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x)), b)))))
    case C.Term.Tup{+q, +a, +b}:
      P2(NdK(dk, ds, im, fi, nx, c, x, C.Term.Tup{q, a, b}, 10), P2(Qs(x, q),
      P2(P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x)), a)), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(3n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x)), b)))))
    case C.Term.Prj{+h}:
      P2(NdK(dk, ds, im, fi, nx, c, x, C.Term.Prj{h}, 11), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x)), h)))
    case C.Term.Enu{+e}:
      P2(NdK(dk, ds, im, fi, nx, c, x, C.Term.Enu{e}, 12),
      P2({T.tm.image(img, c) == Some{C.Term.Enu{e}} : Maybe<&2, C.Term>}, {FvW(C.Cir.Cell.get(0n, x)) == 0 : U32}))
    case C.Term.Lab{+k}:
      P2(NdK(dk, ds, im, fi, nx, c, x, C.Term.Lab{k}, 13), Nm(ks, x, k))
    case C.Term.Mat{+k, +h, +n}:
      P2(NdK(dk, ds, im, fi, nx, c, x, C.Term.Mat{k, h, n}, 14), P2(Nm(ks, x, k),
      P2(P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(3n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x)), h)), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(4n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(4n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(4n, x)), n)))))
    case C.Term.Efq{}:
      NdK(dk, ds, im, fi, nx, c, x, C.Term.Efq{}, 15)
    case C.Term.Eql{+a, +b, +y}:
      P2(NdK(dk, ds, im, fi, nx, c, x, C.Term.Eql{a, b, y}, 16),
      P2(P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x)), a)),
      P2(P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(3n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x)), b)), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(4n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(4n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(4n, x)), y)))))
    case C.Term.Rfl{}:
      NdK(dk, ds, im, fi, nx, c, x, C.Term.Rfl{}, 17)
    case C.Term.Rwt{+e, +p, +f}:
      P2(NdK(dk, ds, im, fi, nx, c, x, C.Term.Rwt{e, p, f}, 18),
      P2(P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x)), e)),
      P2(P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(3n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x)), p)), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(4n, x))), IsCK(dk, ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(4n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(4n, x)), f)))))

def IsC(+ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +c: U32, +x: C.Cir.Cell, t: C.Term) -> Data:
  IsCK(True{}, ds, m, im, fi, nx, ks, img, c, x, t)

# the cell c of the cells m stands for the term t (with DATA's meaning when dk)
def IsK(+dk: Bool, +ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +c: U32, t: C.Term) -> Data:
  IsCK(dk, ds, m, im, fi, nx, ks, img, c, C.Cir.Cells.get(m, c), t)

def Is(+ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +c: U32, t: C.Term) -> Data:
  IsK(True{}, ds, m, im, fi, nx, ks, img, c, t)

def Mem(xs: List<&2, U32>, +c: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, rest}:
      Bool.or(U32.is_eq(x, c), Mem(rest, c))

# the part b of a frame: in field 3, for Rwt only
def Frs.bK(+dk: Bool, +ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +c: U32, kind: FK, b: C.Term) -> Data:
  match kind:
    case FK.rwt{}:
      IsK(dk, ds, m, im, fi, nx, ks, img, c, b)
    case _:
      Unit

def Frs.b(+ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +c: U32, kind: FK, b: C.Term) -> Data:
  Frs.bK(True{}, ds, m, im, fi, nx, ks, img, c, kind, b)

# the frames from the cell fr on, linked by field 1, the innermost first: each
# one of the machine's own cells, not STATIC, not in the pend list ps, of its
# kind's tag, its quantity and its flag K, with its parts standing for a and,
# for Rwt, b; 0 after the last
def FrsK(+dk: Bool, +ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +ps: List<&2, U32>, +fr: U32, fs: List<&2, AF>) -> Data:
  match fs:
    case Nil{}:
      {fr == 0 : U32}
    case Con{AF{+kind, +q, +k, +a, +b}, rest}:
      P2({U32.is_eq(fr, 0) == False{} : Bool},
      P2({C.Cir.is_cell(fr, im, fi, nx) == True{} : Bool},
      P2({Own(fi, nx, fr) == True{} : Bool},
      P2({Fl(m, fr, 1024) == False{} : Bool},
      P2({Mem(ps, fr) == False{} : Bool},
      P2({Tg(m, fr) == FK.tag(kind) : U32},
      P2(Qs(C.Cir.Cells.get(m, fr), q),
      P2({Fl(m, fr, 2048) == k : Bool},
      P2(IsK(dk, ds, m, im, fi, nx, ks, img, Fd(2n, m, fr), a),
      P2(Frs.bK(dk, ds, m, im, fi, nx, ks, img, Fd(3n, m, fr), kind, b),
        FrsK(dk, ds, m, im, fi, nx, ks, img, ps, Fd(1n, m, fr), rest)))))))))))

def Frs(+ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +ps: List<&2, U32>, +fr: U32, fs: List<&2, AF>) -> Data:
  FrsK(True{}, ds, m, im, fi, nx, ks, img, ps, fr, fs)

# Counts and the pend list
# ------------------------
#
# The heap of the machine, shared by every phase (M.input, the moves,
# M.copy, M.data, M.walk, M.out). A cell holds pointers (Fs): a term cell (a
# tag below 19, one of the image's table) its parts, by its tag's mask, in or
# out of the pend list (a cell of the pend list drops them when it is
# reused); a frame (tags 32 to 40) its field 2, and field 3 for Rwt, and an
# argument that owns its term (K.arg, OWNED) its field 2, while out of the
# pend list. The roots rs are the registers that own a pointer. Counts are
# exact (Cnt): each term cell of the machine's, not STATIC and out of the
# pend list, counts its pointers, from the cells (Pc) and the roots. The pend
# list's cells count none (PendOK), and are term cells or of the machine's
# own kinds (32 and up). A count is at most 3 × the machine's cells + the
# roots (ptr.bound): with next <= 214748364 (Room) and at most 64 roots,
# M.inc never wraps. A pointer is below next, to a term cell (Pts), so a new
# cell has none.

# a pointer in the list, when b holds
def Fs.opt(b: Bool, +v: U32, +rest: List<&2, U32>) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, b, Con{v, rest}, rest)

# the parts of a term cell of the mask a
def Fs.term(+a: U32, +x2: U32, +x3: U32, +x4: U32) -> List<&2, U32>:
  Fs.opt(U32.is_ne(U32.and(a, 1), 0), x2, Fs.opt(U32.is_ne(U32.and(a, 2), 0), x3, Fs.opt(U32.is_ne(U32.and(a, 4), 0), x4, Nil{})))

# the pointers that the cell o holds
def Fs(+m: C.Cir.Cells, +ps: List<&2, U32>, +o: U32) -> List<&2, U32>:
  +f0 = Fd(0n, m, o)
  +tg = TgW(f0)
  Bool.pick(List<&2, U32>, U32.is_lt(tg, 19),
    Fs.term(Fd(2n, m, U32.add(345, tg)), Fd(2n, m, o), Fd(3n, m, o), Fd(4n, m, o)),
    Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, tg), U32.is_le(tg, 40)), Bool.not(Mem(ps, o))),
      Con{Fd(2n, m, o), Fs.opt(U32.is_eq(tg, 38), Fd(3n, m, o), Nil{})},
      Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(tg, 41), FlW(f0, 4096)), Bool.not(Mem(ps, o))),
        [Fd(2n, m, o)], Nil{})))

# the cells rs that are c
def RcL(rs: List<&2, U32>, +c: U32) -> Nat:
  match rs:
    case Nil{}:
      0n
    case Con{r, rest}:
      Nat.add(Nat.of(U32.is_eq(r, c)), RcL(rest, c))

# the pointers to c of the n cells from o
def Pc(n: Nat, +m: C.Cir.Cells, +ps: List<&2, U32>, +o: U32, +c: U32) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      Nat.add(RcL(Fs(m, ps, o), c), Pc(p, m, ps, U32.inc(o), c))

# the pointers to c: of the n cells of the machine, from fi, and of the roots
def Ptr(+n: Nat, +m: C.Cir.Cells, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +c: U32) -> Nat:
  Nat.add(Pc(n, m, ps, fi, c), RcL(rs, c))

# each of the n cells from c that is a term cell, not STATIC and out of ps,
# counts its pointers, exactly
def Cnt(n: Nat, +m: C.Cir.Cells, +c: U32, +N: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(
        Bool.or(Bool.not(U32.is_lt(Tg(m, c), 19)), Bool.or(Fl(m, c, 1024), Bool.or(Mem(ps, c),
          Nat.is_eq(U32.to_nat(Fd(1n, m, c)), Ptr(N, m, fi, ps, rs, c))))),
        Cnt(p, m, U32.inc(c), N, fi, ps, rs))

# each pointer of xs is below nx, to a term cell (a tag below 19)
def Lt.all(xs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Bool.and(U32.is_lt(x, nx), U32.is_lt(Tg(m, x), 19)), Lt.all(rest, m, nx))

# the pointers of each of the n cells from o are below nx, to term cells
def Pts(n: Nat, +m: C.Cir.Cells, +ps: List<&2, U32>, +o: U32, +nx: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(Lt.all(Fs(m, ps, o), m, nx), Pts(p, m, ps, U32.inc(o), nx))

# the pend list from the cell p: the cells ps, linked by field 1, then 0
def Chain(ps: List<&2, U32>, +m: C.Cir.Cells, +p: U32) -> Data:
  match ps:
    case Nil{}:
      {p == 0 : U32}
    case Con{+x, rest}:
      P2({p == x : U32}, P2({U32.is_eq(x, 0) == False{} : Bool}, Chain(rest, m, Fd(1n, m, x))))

# each cell of qs, of the pend list ps, is one of the machine's own, not
# STATIC, a term cell or one of the machine's own kinds, and nothing points
# to it
def PendOK(qs: List<&2, U32>, +ps: List<&2, U32>, +m: C.Cir.Cells, +fi: U32, +nx: U32, +rs: List<&2, U32>) -> Data:
  match qs:
    case Nil{}:
      Unit
    case Con{+p, rest}:
      P2({Own(fi, nx, p) == True{} : Bool},
      P2({Fl(m, p, 1024) == False{} : Bool},
      P2({Bool.or(U32.is_lt(Tg(m, p), 19), U32.is_le(32, Tg(m, p))) == True{} : Bool},
      P2({Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, p) == 0n : Nat},
        PendOK(rest, ps, m, fi, nx, rs)))))

# the heap of the cells m, the machine's from fi to nx, with the roots rs and
# the pend list ps from pend
def Heap(+m: C.Cir.Cells, +nx: U32, +fi: U32, +rs: List<&2, U32>, +pend: U32, +ps: List<&2, U32>) -> Data:
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  P2(Chain(ps, m, pend),
  P2(PendOK(ps, ps, m, fi, nx, rs),
  P2({Cnt(n, m, fi, n, fi, ps, rs) == True{} : Bool},
  P2({Pts(n, m, ps, fi, nx) == True{} : Bool},
    {U32.is_le(nx, 214748364) == True{} : Bool}))))

# The image
# ---------
#
# What the moves read of the image's cells, which no move changes but for the
# flag DATA: the table by tag (I.table), the bodies of the defs (where Img.ref
# finds them), the labels of Q0, Q1 and Q2 (M.ret.min's), and the image's
# names, the machine's (Img.known) first.

type Row is Data:
  Row{a: U32, b: U32, c: U32}

# fields 2, 3 and 4 of the table's cells, by tag (Img.table)
def Tbl.rows() -> List<&2, Row>:
  [Row{0, 0, 0}, Row{0, 0, 0}, Row{3, 0, 0}, Row{3, 4, 0}, Row{1, 0, 1}, Row{3, 0, 0}, Row{3, 4, 1}, Row{1, 1, 1},
   Row{3, 0, 0}, Row{3, 4, 1}, Row{3, 0, 0}, Row{1, 0, 1}, Row{0, 0, 1}, Row{0, 0, 1}, Row{6, 0, 1}, Row{0, 0, 1},
   Row{7, 0, 1}, Row{0, 0, 1}, Row{7, 8, 0}]

def Tbl.go(rs: List<&2, Row>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +at: U32) -> Data:
  match rs:
    case Nil{}:
      Unit
    case Con{Row{a, b, c}, rest}:
      P2({C.Cir.is_cell(at, im, fi, nx) == True{} : Bool},
      P2({Fd(2n, m, at) == a : U32}, P2({Fd(3n, m, at) == b : U32}, P2({Fd(4n, m, at) == c : U32},
        Tbl.go(rest, m, im, fi, nx, U32.inc(at))))))

# the table by tag, from cell 345: cells, with their fields
def Tbl(+m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32) -> Data:
  Tbl.go(Tbl.rows(), m, im, fi, nx, 345)

# the bodies of the defs dl, from the cell at on, as Img.defs places them:
# cells of the image
def DefsK(dl: List<&2, C.Def>, +dk: Bool, +ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +at: U32) -> Data:
  match dl:
    case Nil{}:
      Unit
    case Con{C.Def{_, _, +v, _}, rest}:
      P2({U32.is_eq(at, 0) == False{} : Bool},
      P2({U32.is_le(at, im) == True{} : Bool},
      P2(IsK(dk, ds, m, im, fi, nx, ks, img, at, v),
        DefsK(rest, dk, ds, m, im, fi, nx, ks, img, U32.add(at, C.Img.size(v))))))

def Defs(dl: List<&2, C.Def>, +ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +at: U32) -> Data:
  DefsK(dl, True{}, ds, m, im, fi, nx, ks, img, at)

def ImgOKK(+dk: Bool, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +m: C.Cir.Cells,
  +im: U32, +fi: U32, +nx: U32) -> Data:
  P2(Tbl(m, im, fi, nx),
  P2(DefsK(ds, dk, ds, m, im, fi, nx, ks, img, C.I.book()),
  P2(IsK(dk, ds, m, im, fi, nx, ks, img, 9, C.Term.Lab{C.Quan.name(C.Quan.Q0{})}),
  P2(IsK(dk, ds, m, im, fi, nx, ks, img, 10, C.Term.Lab{C.Quan.name(C.Quan.Q1{})}),
  P2(IsK(dk, ds, m, im, fi, nx, ks, img, 11, C.Term.Lab{C.Quan.name(C.Quan.Q2{})}),
  P2(Ex(List<&2, List<&2, U32>>, ks2 => {ks == C.Img.known(ks2) : List<&2, List<&2, U32>>}),
  P2({U32.is_le(363, im) == True{} : Bool}, {U32.is_lt(im, fi) == True{} : Bool})))))))

def ImgOK(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +m: C.Cir.Cells, +im: U32,
  +fi: U32, +nx: U32) -> Data:
  ImgOKK(True{}, ds, ks, img, m, im, fi, nx)

# The invariant
# -------------

# the registers past the first four, by name
type R60 is Data:
  R60{r4: U32, r5: U32, r6: U32, r7: U32, r8: U32, r9: U32, r10: U32, r11: U32, r12: U32, r13: U32, r14: U32, r15: U32, r16: U32, r17: U32, r18: U32, r19: U32, r20: U32, r21: U32, r22: U32, r23: U32, r24: U32, r25: U32, r26: U32, r27: U32, r28: U32, r29: U32, r30: U32, r31: U32, r32: U32, r33: U32, r34: U32, r35: U32, r36: U32, r37: U32, r38: U32, r39: U32, r40: U32, r41: U32, r42: U32, r43: U32, r44: U32, r45: U32, r46: U32, r47: U32, r48: U32, r49: U32, r50: U32, r51: U32, r52: U32, r53: U32, r54: U32, r55: U32, r56: U32, r57: U32, r58: U32, r59: U32, r60: U32, r61: U32, r62: U32, r63: U32}

def R60.list(x: R60) -> List<&2, U32>:
  match x:
    case R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}:
      [r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63]

# registers 4 to 63 of a list of registers
def R60.of(+xs: List<&2, U32>) -> R60:
  R60{Maybe.default(&2, U32, List.get(&2, U32, xs, 4n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 5n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 6n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 7n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 8n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 9n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 10n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 11n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 12n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 13n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 14n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 15n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 16n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 17n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 18n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 19n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 20n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 21n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 22n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 23n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 24n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 25n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 26n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 27n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 28n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 29n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 30n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 31n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 32n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 33n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 34n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 35n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 36n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 37n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 38n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 39n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 40n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 41n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 42n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 43n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 44n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 45n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 46n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 47n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 48n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 49n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 50n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 51n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 52n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 53n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 54n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 55n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 56n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 57n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 58n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 59n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 60n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 61n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 62n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 63n), 0)}

# the registers: focus, mode, sp, pend, then the 60 others
def RG(+foc: U32, +md: U32, +sp: U32, +pend: U32, rest: List<&2, U32>) -> List<&2, U32>:
  Con{foc, Con{md, Con{sp, Con{pend, rest}}}}

# Moves
# -----
#
# One round of the main loop (B.body) from a state that Inv finds (S, IV),
# by the abstract state: for any fuel, an admin move (the same term and a
# smaller measure), a step of Eval, a halt as HR says, or out of memory; and
# with some fuel it ends (MV). round.mv picks the move.

# the state of the registers RG, the cells m, and no output, as Inv finds it
def S(+foc: U32, +md: U32, +sp: U32, +pend: U32, rest: R60, m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +pg: U32, +lim: U32, inp: List<&2, U32>) -> C.Cir.State:
  C.Cir.State{RG(foc, md, sp, pend, R60.list(rest)), m, nx, fi, im, pg, lim, inp, Nil{}, 0}

# what the invariant finds in a state: the abstract state (ret: mode 1, the
# focus' term, the frames), the focus' cell, the top frame, the pend list
# and its cells, and the registers past the first four
type Wit is Data:
  Wit{ret: Bool, focus: C.Term, fs: List<&2, AF>, foc: U32, sp: U32, pend: U32, ps: List<&2, U32>, rest: R60}

def InvOf(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +out: List<&2, U32>, +outn: U32, +t: C.Term, +w: Nat, +ret: Bool,
  +focus: C.Term, +fs: List<&2, AF>, +foc: U32, +sp: U32, +pend: U32, +ps: List<&2, U32>, +rest: R60) -> Data:
  P2({A.plugs(fs, focus) == t : C.Term},
  P2({A.w(ret, focus, fs) == w : Nat},
  P2({Bool.or(Bool.not(ret), C.Eval.vals(ds, focus, False{})) == True{} : Bool},
  P2(AFs.ok(ds, fs),
  P2({regs == RG(foc, Bool.to_u32(ret), sp, pend, R60.list(rest)) : List<&2, U32>},
  P2(Is(ds, m, im, fi, nx, ks, img, foc, focus),
  P2(Frs(ds, m, im, fi, nx, ks, img, ps, sp, fs),
  P2(Heap(m, nx, fi, [foc], pend, ps),
  P2(ImgOK(ds, ks, img, m, im, fi, nx),
  P2({out == Nil{} : List<&2, U32>}, {outn == 0 : U32}))))))))))

# the state st holds the abstract state of x, of the term t and the measure w
def InvW(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, st: C.Cir.State, +t: C.Term,
  +w: Nat, x: Wit) -> Data:
  match st x:
    case C.Cir.State{regs, m, nx, fi, im, _, _, _, out, outn} Wit{ret, focus, fs, foc, sp, pend, ps, rest}:
      InvOf(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest)

# Inv: between two rounds of the main loop, the state st stands for the term
# t, with the measure w, in the book ds, with the image's names ks and terms
# img
def Inv(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +st: C.Cir.State, +t: C.Term,
  +w: Nat) -> Data:
  Ex(Wit, x => InvW(ds, ks, img, st, t, w, x))

# Heaps in a move
# ---------------
#
# Inside a move, the registers own or borrow cells. HS is Inv's heap there:
# the owned roots os (registers that own a pointer to their cells, counted
# by Ptr), the borrowed terms bs (each STATIC, or a node of an owned root's
# term: Held), the frames, the pend list and the image. A node of an owned
# term has a pointer from the root or from its parent node, so no M.alloc
# frees it, nor a cell below it; a pointer only from the pend list, or from
# a cell that only the pend list holds, would not do. The premises of the
# moves on M.copy, M.data, M.walk and M.out below are stated with it (HSK:
# with DATA's meaning when dk, as Inv has it).

type Rt is Data:
  Rt{c: U32, t: C.Term}

def Rt.cells(rs: List<&2, Rt>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{Rt{c, _}, rest}:
      Con{c, Rt.cells(rest)}

def Rt.terms(rs: List<&2, Rt>) -> List<&2, C.Term>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{Rt{_, u}, rest}:
      Con{u, Rt.terms(rest)}

# each cell of rs stands for its term
def RtsK(+dk: Bool, +ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, rs: List<&2, Rt>) -> Data:
  match rs:
    case Nil{}:
      Unit
    case Con{Rt{+c, +u}, rest}:
      P2(IsK(dk, ds, m, im, fi, nx, ks, img, c, u), RtsK(dk, ds, m, im, fi, nx, ks, img, rest))

def Rts(+ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, rs: List<&2, Rt>) -> Data:
  RtsK(True{}, ds, m, im, fi, nx, ks, img, rs)

# c is a node of the term t at the cell r: r, or a node of one of its parts,
# in the fields that IsC reads
def Node(t: C.Term, +m: C.Cir.Cells, +r: U32, +c: U32) -> Bool:
  match t:
    case C.Term.Var{_}:
      U32.is_eq(r, c)
    case C.Term.Ref{_}:
      U32.is_eq(r, c)
    case C.Term.Ann{y, z}:
      Bool.or(U32.is_eq(r, c), Bool.or(Node(y, m, Fd(2n, m, r), c), Node(z, m, Fd(3n, m, r), c)))
    case C.Term.Let{_, v, f}:
      Bool.or(U32.is_eq(r, c), Bool.or(Node(v, m, Fd(2n, m, r), c), Node(f, m, Fd(3n, m, r), c)))
    case C.Term.Typ{y}:
      Bool.or(U32.is_eq(r, c), Node(y, m, Fd(2n, m, r), c))
    case C.Term.Min{a, b}:
      Bool.or(U32.is_eq(r, c), Bool.or(Node(a, m, Fd(2n, m, r), c), Node(b, m, Fd(3n, m, r), c)))
    case C.Term.All{_, a, b}:
      Bool.or(U32.is_eq(r, c), Bool.or(Node(a, m, Fd(2n, m, r), c), Node(b, m, Fd(3n, m, r), c)))
    case C.Term.Lam{_, f}:
      Bool.or(U32.is_eq(r, c), Node(f, m, Fd(2n, m, r), c))
    case C.Term.App{_, f, y}:
      Bool.or(U32.is_eq(r, c), Bool.or(Node(f, m, Fd(2n, m, r), c), Node(y, m, Fd(3n, m, r), c)))
    case C.Term.Sig{_, a, b}:
      Bool.or(U32.is_eq(r, c), Bool.or(Node(a, m, Fd(2n, m, r), c), Node(b, m, Fd(3n, m, r), c)))
    case C.Term.Tup{_, a, b}:
      Bool.or(U32.is_eq(r, c), Bool.or(Node(a, m, Fd(2n, m, r), c), Node(b, m, Fd(3n, m, r), c)))
    case C.Term.Prj{h}:
      Bool.or(U32.is_eq(r, c), Node(h, m, Fd(2n, m, r), c))
    case C.Term.Enu{_}:
      U32.is_eq(r, c)
    case C.Term.Lab{_}:
      U32.is_eq(r, c)
    case C.Term.Mat{_, h, n}:
      Bool.or(U32.is_eq(r, c), Bool.or(Node(h, m, Fd(3n, m, r), c), Node(n, m, Fd(4n, m, r), c)))
    case C.Term.Efq{}:
      U32.is_eq(r, c)
    case C.Term.Eql{a, b, y}:
      Bool.or(U32.is_eq(r, c), Bool.or(Node(a, m, Fd(2n, m, r), c), Bool.or(Node(b, m, Fd(3n, m, r), c), Node(y, m, Fd(4n, m, r), c))))
    case C.Term.Rfl{}:
      U32.is_eq(r, c)
    case C.Term.Rwt{e, y, f}:
      Bool.or(U32.is_eq(r, c), Bool.or(Node(e, m, Fd(2n, m, r), c), Bool.or(Node(y, m, Fd(3n, m, r), c), Node(f, m, Fd(4n, m, r), c))))

# c is a node of the term of one of the roots os
def Nodes(os: List<&2, Rt>, +m: C.Cir.Cells, +c: U32) -> Bool:
  match os:
    case Nil{}:
      False{}
    case Con{Rt{+r, u}, rest}:
      Bool.or(Node(u, m, r, c), Nodes(rest, m, c))

# each cell of bs is STATIC or a node of an owned root's term (os)
def Held(+m: C.Cir.Cells, +os: List<&2, Rt>, bs: List<&2, Rt>) -> Data:
  match bs:
    case Nil{}:
      Unit
    case Con{Rt{+c, _}, rest}:
      P2({Bool.or(Fl(m, c, 1024), Nodes(os, m, c)) == True{} : Bool}, Held(m, os, rest))

def HSK(+dk: Bool, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +m: C.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +os: List<&2, Rt>, +bs: List<&2, Rt>, +fs: List<&2, AF>, +sp: U32, +pend: U32,
  +ps: List<&2, U32>) -> Data:
  P2(RtsK(dk, ds, m, im, fi, nx, ks, img, os),
  P2(RtsK(dk, ds, m, im, fi, nx, ks, img, bs),
  P2(Held(m, os, bs),
  P2(FrsK(dk, ds, m, im, fi, nx, ks, img, ps, sp, fs),
  P2(Heap(m, nx, fi, Rt.cells(os), pend, ps),
    ImgOKK(dk, ds, ks, img, m, im, fi, nx))))))

def HS(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +m: C.Cir.Cells, +nx: U32,
  +fi: U32, +im: U32, +os: List<&2, Rt>, +bs: List<&2, Rt>, +fs: List<&2, AF>, +sp: U32, +pend: U32,
  +ps: List<&2, U32>) -> Data:
  HSK(True{}, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps)

def Term.is_var(t: C.Term) -> Bool:
  match t:
    case C.Term.Var{_}:
      True{}
    case _:
      False{}

# the chain of K.arg cells from a, linked by field 1, that hold the terms of xs
# in field 2, at their quantities: the machine's own cells, not STATIC, out of
# the pend list; an OWNED one's term is a Var (counted by Fs), any other's is
# STATIC or a node of an owned root's term (os); each term's cell STATIC or
# out of the pend list too (M.walk's arguments and locals; M.copy's locals,
# with any quantity)
def Ag(+ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +ps: List<&2, U32>, +os: List<&2, Rt>, +a: U32, xs: List<&2, C.Arg>) -> Data:
  match xs:
    case Nil{}:
      {a == 0 : U32}
    case Con{C.Arg{+q, +x}, rest}:
      P2({U32.is_eq(a, 0) == False{} : Bool},
      P2({C.Cir.is_cell(a, im, fi, nx) == True{} : Bool},
      P2({Own(fi, nx, a) == True{} : Bool},
      P2({Fl(m, a, 1024) == False{} : Bool},
      P2({Mem(ps, a) == False{} : Bool},
      P2({Tg(m, a) == 41 : U32},
      P2(Qs(C.Cir.Cells.get(m, a), q),
      P2({Bool.or(Bool.not(Fl(m, a, 2048)), C.Eval.vals(ds, x, False{})) == True{} : Bool},
      P2({Bool.or(Bool.not(Fl(m, a, 4096)), Term.is_var(x)) == True{} : Bool},
      P2(Is(ds, m, im, fi, nx, ks, img, Fd(2n, m, a), x),
      P2({Bool.or(Fl(m, a, 4096), Bool.or(Fl(m, Fd(2n, m, a), 1024), Nodes(os, m, Fd(2n, m, a)))) == True{} : Bool},
      P2({Bool.or(Fl(m, Fd(2n, m, a), 1024), Bool.not(Mem(ps, Fd(2n, m, a)))) == True{} : Bool},
        Ag(ds, m, im, fi, nx, ks, img, ps, os, Fd(1n, m, a), rest)))))))))))))

def Arg.terms(xs: List<&2, C.Arg>) -> List<&2, C.Term>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{C.Arg{_, x}, rest}:
      Con{x, Arg.terms(rest)}

# the registers of keep have the same values in regs2 as in regs
def Kept(+regs: List<&2, U32>, +regs2: List<&2, U32>, keep: List<&2, Nat>) -> Data:
  match keep:
    case Nil{}:
      Unit
    case Con{+j, rest}:
      P2({List.get(&2, U32, regs2, j) == List.get(&2, U32, regs, j) : Maybe<&2, U32>}, Kept(regs, regs2, rest))

def Nat.mem(xs: List<&2, Nat>, +j: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, rest}:
      Bool.or(Nat.is_eq(x, j), Nat.mem(rest, j))

# no register of keep is one of scr
def Disj(keep: List<&2, Nat>, +scr: List<&2, Nat>) -> Bool:
  match keep:
    case Nil{}:
      True{}
    case Con{+j, rest}:
      Bool.and(Bool.not(Nat.mem(scr, j)), Disj(rest, scr))

# the registers that M.copy(r, _), M.data and M.walk may change (pend among
# them, which each premise names)
def Copy.scr(+r: Nat) -> List<&2, Nat>:
  [r, 3n, 4n, 5n, 6n, 7n, 30n, 31n, 32n, 33n, 34n, 35n, 38n, 39n, 40n, 41n, 55n, 56n, 57n, 58n, 59n, 60n, 61n, 62n, 63n]

def Data.scr() -> List<&2, Nat>:
  [3n, 4n, 5n, 6n, 7n, 42n, 43n, 44n, 62n]

def Walk.scr() -> List<&2, Nat>:
  [3n, 4n, 5n, 6n, 7n, 19n, 20n, 21n, 22n, 23n, 24n, 25n, 26n, 27n, 28n, 29n, 42n, 43n, 44n, 62n]

def St.cells(st: C.Cir.State) -> C.Cir.Cells:
  match st:
    case C.Cir.State{_, m, _, _, _, _, _, _, _, _}:
      m

def St.next(st: C.Cir.State) -> U32:
  match st:
    case C.Cir.State{_, _, nx, _, _, _, _, _, _, _}:
      nx

# a state after a statement of a move: the same first cell, image, limit and
# input, no output, and 64 registers, of which keep's are kept
def Same(+regs: List<&2, U32>, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, U32>, +keep: List<&2, Nat>,
  st: C.Cir.State) -> Data:
  match st:
    case C.Cir.State{+regs2, _, _, fi2, im2, _, lim2, inp2, out2, outn2}:
      P2({fi2 == fi : U32}, P2({im2 == im : U32}, P2({lim2 == lim : U32}, P2({inp2 == inp : List<&2, U32>},
      P2({out2 == Nil{} : List<&2, U32>}, P2({outn2 == 0 : U32},
      P2({List.length(&2, U32, regs2) == 64n : Nat}, Kept(regs, regs2, keep))))))))

# the register r of the state st holds v
def Reg(st: C.Cir.State, +r: Nat, +v: U32) -> Data:
  {List.get(&2, U32, St.regs(st), r) == Some{v} : Maybe<&2, U32>}

# Open: the heap's operations (this file)
# ---------------------------------------
#
# The statements that every phase uses for its cells, with the shared Heap:
# M.inc of a held cell makes it an owned root; M.dec of an owned root drops
# it (to the pend list at 0); M.alloc gives a cell, all zeros, that nothing
# points to, out of the pend list (its old parts lose a pointer); M.release
# of a cell of the machine's own kinds (tag 32 and up: a frame, an argument,
# a check, a root) puts it in the pend list. Each keeps HS's terms, and the
# registers but its own. A count never wraps (ptr.bound, with Room).

# a count is at most 3 × the machine's cells and the roots
def ptr.bound(+n: Nat, +m: C.Cir.Cells, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +c: U32) ->
  N.Le(Ptr(n, m, fi, ps, rs, c), Nat.add(Nat.mul(3n, n), List.length(&2, U32, rs))):
  ?TODO

# M.inc(r), with the held cell c of u in register r: c is an owned root too
def inc.post(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat,
  +os: List<&2, Rt>, +bs: List<&2, Rt>, +fs: List<&2, AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +c: U32, +u: C.Term,
  hs: HS(ds, ks, img, m, nx, fi, im, os, Con{Rt{c, u}, bs}, fs, sp, pend, ps),
  hc: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>}) ->
  Post(False{}, C.Cir.exec(f, C.M.inc(r), C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
    st2 => Ex(C.Cir.Cells, m2 => P2({st2 == C.Cir.State{regs, m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : C.Cir.State},
      HS(ds, ks, img, m2, nx, fi, im, Con{Rt{c, u}, os}, Con{Rt{c, u}, bs}, fs, sp, pend, ps))),
    s => st2 => Empty):
  ?TODO

# M.dec(r), with the owned root c of u in register r, when each borrowed term
# is held without that root: c is no root, and goes to the pend list at 0;
# only registers dr and pend change
def dec.post(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat,
  +os: List<&2, Rt>, +bs: List<&2, Rt>, +fs: List<&2, AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +c: U32, +u: C.Term,
  hs: HS(ds, ks, img, m, nx, fi, im, Con{Rt{c, u}, os}, bs, fs, sp, pend, ps),
  hb: Held(m, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, ps, Rt.cells(os), bs),
  hl: {List.length(&2, U32, regs) == 64n : Nat},
  hc: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  Post(False{}, C.Cir.exec(f, C.M.dec(r), C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
    st2 => Ex(C.Cir.Cells, m2 => Ex(U32, d => Ex(U32, pend2 => Ex(List<&2, U32>, ps2 =>
      P2({st2 == C.Cir.State{List.set(&2, U32, List.set(&2, U32, regs, 5n, d), 3n, pend2), m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : C.Cir.State},
        HS(ds, ks, img, m2, nx, fi, im, os, bs, fs, sp, pend2, ps2)))))),
    s => st2 => Empty):
  ?TODO

# M.alloc(r): register r gets a cell z, all zeros, out of the pend list, that
# nothing points to (a new cell, or the pend list's first, whose parts lose a
# pointer); HS holds with the same terms; only Copy.scr's alloc registers
# (aq, am, dx, dr), pend and r change. Out of memory only when it is new.
def alloc.post(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat,
  +keep: List<&2, Nat>, +os: List<&2, Rt>, +bs: List<&2, Rt>, +fs: List<&2, AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  hs: HS(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps),
  hl: {List.length(&2, U32, regs) == 64n : Nat},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  hk: {Disj(keep, [r, 3n, 4n, 5n, 6n, 7n]) == True{} : Bool}) ->
  Post(False{}, C.Cir.exec(f, C.M.alloc(r), C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
    st2 => P2(Same(regs, fi, im, lim, inp, keep, st2),
      Ex(U32, z => Ex(U32, pend2 => Ex(List<&2, U32>, ps2 =>
        P2(Reg(st2, r, z), P2(Reg(st2, 3n, pend2),
        P2({C.Cir.Cells.get(St.cells(st2), z) == C.Cir.Cell.zero() : C.Cir.Cell},
        P2({Own(fi, St.next(st2), z) == True{} : Bool}, P2({Mem(ps2, z) == False{} : Bool},
        P2({Ptr(Nat.sub(U32.to_nat(St.next(st2)), U32.to_nat(fi)), St.cells(st2), fi, ps2, Rt.cells(os), z) == 0n : Nat},
          HS(ds, ks, img, St.cells(st2), St.next(st2), fi, im, os, bs, fs, sp, pend2, ps2))))))))))),
    s => st2 => Empty):
  ?TODO

# M.release(r), of the cell z of the machine's own kinds (tag 32 or more) in
# register r, out of the pend list: z goes to the pend list
def release.post(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat,
  +os: List<&2, Rt>, +bs: List<&2, Rt>, +fs: List<&2, AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +z: U32,
  hs: HS(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps),
  hz: {Own(fi, nx, z) == True{} : Bool}, ht: {U32.is_lt(Tg(m, z), 32) == False{} : Bool},
  hf: {Fl(m, z, 1024) == False{} : Bool}, hm: {Mem(ps, z) == False{} : Bool},
  hl: {List.length(&2, U32, regs) == 64n : Nat},
  hc: {List.get(&2, U32, regs, r) == Some{z} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  Post(False{}, C.Cir.exec(f, C.M.release(r), C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
    st2 => Ex(C.Cir.Cells, m2 => P2({st2 == C.Cir.State{List.set(&2, U32, regs, 3n, z), m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : C.Cir.State},
      HS(ds, ks, img, m2, nx, fi, im, os, bs, fs, sp, z, Con{z, ps}))),
    s => st2 => Empty):
  ?TODO

# Open: M.copy (proof_copy.bend)
# ------------------------------
#
# From a state of HS, with the cell c of t borrowed (in register src) and the
# locals of the chain ce (register cenv) standing for the terms of es (clen,
# their number, in register clen), M.copy(r, src) gives register r a new cell
# n that stands for Term.subst(t, terms(es), 0n), owned (its count is 1);
# HS holds again with n among the owned roots, the locals' chain is kept, and
# only Copy.scr(r)'s registers change: pend to pend2, with the pend list ps2.
# Every cell that a copy takes is from the pend list or new (the frame
# condition on allocation, by which HS's terms stay). With some fuel it ends.

def CopyQ(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +fi: U32, +im: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, +keep: List<&2, Nat>, +os: List<&2, Rt>,
  +bs: List<&2, Rt>, +fs: List<&2, AF>, +sp: U32, +t: C.Term, +ce: U32, +es: List<&2, C.Arg>, +st2: C.Cir.State) -> Data:
  +m2 = St.cells(st2)
  +nx2 = St.next(st2)
  P2(Same(regs, fi, im, lim, inp, keep, st2),
  Ex(U32, n => Ex(U32, pend2 => Ex(List<&2, U32>, ps2 =>
    P2(Reg(st2, r, n), P2(Reg(st2, 3n, pend2),
    P2(HS(ds, ks, img, m2, nx2, fi, im, Con{Rt{n, C.Term.subst(t, Arg.terms(es), 0n)}, os}, bs, fs, sp, pend2, ps2),
      Ag(ds, m2, im, fi, nx2, ks, img, ps2, os, ce, es))))))))
# the conclusion of copy.post (proof_mach.bend), for the phase that proves it
def CopyPost(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, +src: Nat,
  +keep: List<&2, Nat>, +os: List<&2, Rt>, +bs: List<&2, Rt>, +fs: List<&2, AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +c: U32, +t: C.Term, +ce: U32, +es: List<&2, C.Arg>,
  hs: HS(ds, ks, img, m, nx, fi, im, os, Con{Rt{c, t}, bs}, fs, sp, pend, ps),
  hl: {List.length(&2, U32, regs) == 64n : Nat},
  hc: {List.get(&2, U32, regs, src) == Some{c} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  he: {List.get(&2, U32, regs, 36n) == Some{ce} : Maybe<&2, U32>},
  hn: {List.get(&2, U32, regs, 37n) == Some{U32.from_nat(List.length(&2, C.Arg, es))} : Maybe<&2, U32>},
  env: Ag(ds, m, im, fi, nx, ks, img, ps, os, ce, es),
  hr: {Bool.and(Nat.is_lt(r, 64n), Bool.not(Nat.mem([3n, 39n], r))) == True{} : Bool},
  hsrc: {Nat.mem([4n, 5n, 6n, 7n, 39n], src) == False{} : Bool},
  hk: {Disj(keep, Copy.scr(r)) == True{} : Bool}) ->
  Type:
  Post(False{}, C.Cir.exec(f, C.M.copy(r, src), C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
    st2 => CopyQ(ds, ks, img, regs, fi, im, lim, inp, r, keep, os, Con{Rt{c, t}, bs}, fs, sp, t, ce, es, st2),
    s => st2 => Empty)

# the conclusion of copy.done (proof_mach.bend), for the phase that proves it
def CopyDone(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, +src: Nat,
  +os: List<&2, Rt>, +bs: List<&2, Rt>, +fs: List<&2, AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +c: U32, +t: C.Term, +ce: U32, +es: List<&2, C.Arg>,
  hs: HS(ds, ks, img, m, nx, fi, im, os, Con{Rt{c, t}, bs}, fs, sp, pend, ps),
  hl: {List.length(&2, U32, regs) == 64n : Nat},
  hc: {List.get(&2, U32, regs, src) == Some{c} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  he: {List.get(&2, U32, regs, 36n) == Some{ce} : Maybe<&2, U32>},
  hn: {List.get(&2, U32, regs, 37n) == Some{U32.from_nat(List.length(&2, C.Arg, es))} : Maybe<&2, U32>},
  env: Ag(ds, m, im, fi, nx, ks, img, ps, os, ce, es),
  hr: {Bool.and(Nat.is_lt(r, 64n), Bool.not(Nat.mem([3n, 39n], r))) == True{} : Bool},
  hsrc: {Nat.mem([4n, 5n, 6n, 7n, 39n], src) == False{} : Bool}) ->
  Data:
  Ex(Nat, f => Ends(C.Cir.exec(f, C.M.copy(r, src), C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0})))


# Open: M.data (proof_walk.bend)
# ------------------------------
#
# From a state of HS, with the cell c of v (in register r, none of
# Data.scr(), which M.data sets before it reads r) among its terms, M.data(r)
# sets register dok to 1 when Term.is_data(v), else to 0; when it is 1, HS
# holds again (the flags DATA that it set are true); when it is 0 the run
# halts with 2, and nothing more is needed (on that path the flags it set
# may be false, so HSK(False{}) is what holds inside it). Only Data.scr()'s
# registers change. With some fuel it ends.

def DataH(b: Bool, X: Data) -> Data:
  match b:
    case True{}:
      X
    case False{}:
      Unit

def DataQ(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +fi: U32, +im: U32, +lim: U32, +inp: List<&2, U32>, +keep: List<&2, Nat>, +os: List<&2, Rt>, +bs: List<&2, Rt>,
  +fs: List<&2, AF>, +sp: U32, +v: C.Term, +st2: C.Cir.State) -> Data:
  P2(Same(regs, fi, im, lim, inp, keep, st2),
  P2(Reg(st2, 43n, Bool.to_u32(C.Term.is_data(v))),
  Ex(U32, pend2 => Ex(List<&2, U32>, ps2 =>
    P2(Reg(st2, 3n, pend2), DataH(C.Term.is_data(v), HS(ds, ks, img, St.cells(st2), St.next(st2), fi, im, os, bs, fs, sp, pend2, ps2)))))))
# the conclusion of data.post (proof_mach.bend), for the phase that proves it
def DataPost(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat,
  +keep: List<&2, Nat>, +os: List<&2, Rt>, +bs: List<&2, Rt>, +fs: List<&2, AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +c: U32, +v: C.Term,
  hs: HS(ds, ks, img, m, nx, fi, im, os, Con{Rt{c, v}, bs}, fs, sp, pend, ps),
  hl: {List.length(&2, U32, regs) == 64n : Nat},
  hc: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  hr: {Nat.mem(Data.scr(), r) == False{} : Bool},
  hk: {Disj(keep, Data.scr()) == True{} : Bool}) ->
  Type:
  Post(False{}, C.Cir.exec(f, C.M.data(r), C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
    st2 => DataQ(ds, ks, img, regs, fi, im, lim, inp, keep, os, Con{Rt{c, v}, bs}, fs, sp, v, st2), s => st2 => Empty)

# the conclusion of data.done (proof_mach.bend), for the phase that proves it
def DataDone(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat,
  +os: List<&2, Rt>, +bs: List<&2, Rt>, +fs: List<&2, AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +c: U32, +v: C.Term,
  hs: HS(ds, ks, img, m, nx, fi, im, os, Con{Rt{c, v}, bs}, fs, sp, pend, ps),
  hl: {List.length(&2, U32, regs) == 64n : Nat},
  hc: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  hr: {Nat.mem(Data.scr(), r) == False{} : Bool}) ->
  Data:
  Ex(Nat, f => Ends(C.Cir.exec(f, C.M.data(r), C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0})))


# Open: M.walk (proof_walk.bend)
# ------------------------------
#
# From a state of HS, with the case tree's cell tc of tt (register wt, an
# image cell) and the arguments of xs (the chain in register wargs), M.walk
# computes Eval.walk(tt, Nil{}, xs) (WalkR): wres is 1 at a leaf u, in
# register wt, with the walk's locals e in the chain of register wenv (wn of
# them) and the arguments left ys in wargs, so that the walk gives
# Term.spine(ys, Term.subst(u, e, 0n)); 2 when the walk needs more arguments,
# with wenv and wargs chains to release; 3 when no walk exists. HS holds
# again, except when wres is 3 (a check of M.data may have failed), and
# only Walk.scr()'s registers change. With some fuel it ends.

def WalkR(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +m2: C.Cir.Cells, +nx2: U32,
  +fi: U32, +im: U32, +ps2: List<&2, U32>, +os: List<&2, Rt>, +tt: C.Term, +xs: List<&2, C.Arg>, +res: U32, +wt2: U32, +env: U32,
  +wn: U32, +args: U32) -> Type:
  Or(P2({res == 1 : U32}, Ex(C.Term, u => Ex(List<&2, C.Arg>, e => Ex(List<&2, C.Arg>, ys =>
      P2({C.Eval.walk(tt, Nil{}, xs) == Some{Some{C.Term.spine(ys, C.Term.subst(u, Arg.terms(e), 0n))}} : Maybe<Maybe<C.Term>>},
      P2(Is(ds, m2, im, fi, nx2, ks, img, wt2, u),
      P2({Fl(m2, wt2, 1024) == True{} : Bool},
      P2({wn == U32.from_nat(List.length(&2, C.Arg, e))  : U32},
      P2(Ag(ds, m2, im, fi, nx2, ks, img, ps2, os, env, e), Ag(ds, m2, im, fi, nx2, ks, img, ps2, os, args, ys)))))))))),
  Or(P2({res == 2 : U32}, P2({C.Eval.walk(tt, Nil{}, xs) == Some{None{}} : Maybe<Maybe<C.Term>>},
      Ex(List<&2, C.Arg>, e => Ex(List<&2, C.Arg>, ys =>
        P2(Ag(ds, m2, im, fi, nx2, ks, img, ps2, os, env, e), Ag(ds, m2, im, fi, nx2, ks, img, ps2, os, args, ys)))))),
    P2({res == 3 : U32}, {C.Eval.walk(tt, Nil{}, xs) == None{} : Maybe<Maybe<C.Term>>})))

def WalkQ(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +fi: U32, +im: U32, +lim: U32, +inp: List<&2, U32>, +keep: List<&2, Nat>, +os: List<&2, Rt>, +bs: List<&2, Rt>,
  +fs: List<&2, AF>, +sp: U32, +tt: C.Term, +xs: List<&2, C.Arg>, +st2: C.Cir.State) -> Type:
  +m2 = St.cells(st2)
  +nx2 = St.next(st2)
  Same(regs, fi, im, lim, inp, keep, st2) &
  &res: U32 -> &wt2: U32 -> &env: U32 -> &wn: U32 -> &args: U32 -> &pend2: U32 -> &ps2: List<&2, U32> ->
    Reg(st2, 26n, res) & Reg(st2, 19n, wt2) & Reg(st2, 20n, env) & Reg(st2, 25n, wn) & Reg(st2, 21n, args) &
    Reg(st2, 3n, pend2) & DataH(U32.is_ne(res, 3), HS(ds, ks, img, m2, nx2, fi, im, os, bs, fs, sp, pend2, ps2)) &
    WalkR(ds, ks, img, m2, nx2, fi, im, ps2, os, tt, xs, res, wt2, env, wn, args)
# the conclusion of walk.post (proof_mach.bend), for the phase that proves it
def WalkPost(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>,
  +keep: List<&2, Nat>, +os: List<&2, Rt>, +bs: List<&2, Rt>, +fs: List<&2, AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +tc: U32, +tt: C.Term, +a: U32, +xs: List<&2, C.Arg>,
  hs: HS(ds, ks, img, m, nx, fi, im, os, Con{Rt{tc, tt}, bs}, fs, sp, pend, ps),
  hst: {Fl(m, tc, 1024) == True{} : Bool},
  hl: {List.length(&2, U32, regs) == 64n : Nat},
  ht: {List.get(&2, U32, regs, 19n) == Some{tc} : Maybe<&2, U32>},
  ha: {List.get(&2, U32, regs, 21n) == Some{a} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  args: Ag(ds, m, im, fi, nx, ks, img, ps, os, a, xs),
  hk: {Disj(keep, Walk.scr()) == True{} : Bool}) ->
  Type:
  Post(False{}, C.Cir.exec(f, C.M.walk(), C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
    st2 => WalkQ(ds, ks, img, regs, fi, im, lim, inp, keep, os, Con{Rt{tc, tt}, bs}, fs, sp, tt, xs, st2), s => st2 => Empty)

# the conclusion of walk.done (proof_mach.bend), for the phase that proves it
def WalkDone(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>,
  +os: List<&2, Rt>, +bs: List<&2, Rt>, +fs: List<&2, AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +tc: U32, +tt: C.Term, +a: U32, +xs: List<&2, C.Arg>,
  hs: HS(ds, ks, img, m, nx, fi, im, os, Con{Rt{tc, tt}, bs}, fs, sp, pend, ps),
  hst: {Fl(m, tc, 1024) == True{} : Bool},
  hl: {List.length(&2, U32, regs) == 64n : Nat},
  ht: {List.get(&2, U32, regs, 19n) == Some{tc} : Maybe<&2, U32>},
  ha: {List.get(&2, U32, regs, 21n) == Some{a} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  args: Ag(ds, m, im, fi, nx, ks, img, ps, os, a, xs)) ->
  Data:
  Ex(Nat, f => Ends(C.Cir.exec(f, C.M.walk(), C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0})))


# Open: M.out (proof_out.bend)
# ----------------------------
#
# In mode 1 with no frame, from the focus' cell of the value v, M.out halts
# with 0 and the bytes of Program.unbytes(v) (the output, the last first), or
# with 2 when it is none; it may run out of memory. With some fuel it ends.

def OutH(+v: C.Term, +s: U32, st2: C.Cir.State) -> Data:
  Either<&2, &2, P2({s == 0 : U32}, {C.Program.unbytes(v) == Some{List.reverse(&2, U32, St.out(st2))} : Maybe<&2, List<&2, U32>>}),
    P2({s == 2 : U32}, {C.Program.unbytes(v) == None{} : Maybe<&2, List<&2, U32>>})>
# the conclusion of out.post (proof_mach.bend), for the phase that proves it
def OutPost(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32,
  +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>,
  +v: C.Term, +ks2: List<&2, List<&2, U32>>,
  hv: Is(ds, m, im, fi, nx, ks, img, foc, v),
  hk: {ks == C.Img.known(ks2) : List<&2, List<&2, U32>>}) ->
  Type:
  Post(False{}, C.Cir.exec(f, C.M.out(), S(foc, 1, 0, pend, rest, m, nx, fi, im, pg, lim, inp)), st => Empty,
    s => st2 => OutH(v, s, st2))

# the conclusion of out.done (proof_mach.bend), for the phase that proves it
def OutDone(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32,
  +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>,
  +v: C.Term, +ks2: List<&2, List<&2, U32>>,
  hv: Is(ds, m, im, fi, nx, ks, img, foc, v),
  hk: {ks == C.Img.known(ks2) : List<&2, List<&2, U32>>}) ->
  Data:
  Ex(Nat, f => Ends(C.Cir.exec(f, C.M.out(), S(foc, 1, 0, pend, rest, m, nx, fi, im, pg, lim, inp))))


# Open: the frame conditions of allocation (this file)
# ----------------------------------------------------
#
# M.alloc takes the first cell of the pend list, or a new one (next). Neither
# is a node of a term that HS holds: a cell of the pend list has no pointer
# (PendOK), and every node below a held cell that is not STATIC has one, of
# its part's cell (Pc) or of a root (Rc); a new cell is no cell yet. So
# setting either keeps every held term.

def is.pend(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +m: C.Cir.Cells, +nx: U32,
  +fi: U32, +im: U32, +os: List<&2, Rt>, +bs: List<&2, Rt>, +fs: List<&2, AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +x: C.Cir.Cell,
  hs: HS(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps),
  hp: {Mem(ps, pend) == True{} : Bool}) ->
  P2(Rts(ds, C.Cir.Cells.set(m, pend, x), im, fi, nx, ks, img, os), P2(Rts(ds, C.Cir.Cells.set(m, pend, x), im, fi, nx, ks, img, bs),
    Frs(ds, C.Cir.Cells.set(m, pend, x), im, fi, nx, ks, img, ps, sp, fs))):
  ?TODO

def is.fresh(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +m: C.Cir.Cells, +nx: U32,
  +fi: U32, +im: U32, +os: List<&2, Rt>, +bs: List<&2, Rt>, +fs: List<&2, AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +x: C.Cir.Cell,
  hs: HS(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps)) ->
  P2(Rts(ds, C.Cir.Cells.set(m, nx, x), im, fi, U32.inc(nx), ks, img, os), P2(Rts(ds, C.Cir.Cells.set(m, nx, x), im, fi, U32.inc(nx), ks, img, bs),
    Frs(ds, C.Cir.Cells.set(m, nx, x), im, fi, U32.inc(nx), ks, img, ps, sp, fs))):
  ?TODO

# Rounds
# ------

# the main loop of Mach.code and its body: a move by the mode
def B.body() -> C.Cir.Stmt:
  C.M.if(C.M.eq(C.M.g(C.R.mode()), C.M.c(0)), C.M.ev(), C.M.ret())

def B.loop() -> C.Cir.Stmt:
  C.M.while(C.M.c(1), B.body())

# what follows M.input in Mach.code
def B.rest() -> C.Cir.Stmt:
  C.Cir.Stmt.seq{C.M.set(C.R.mode(), C.M.c(0)), C.Cir.Stmt.seq{B.loop(), C.Cir.Stmt.nop{}}}

def St.regs(st: C.Cir.State) -> List<&2, U32>:
  match st:
    case C.Cir.State{regs, _, _, _, _, _, _, _, _, _}:
      regs

def St.out(st: C.Cir.State) -> List<&2, U32>:
  match st:
    case C.Cir.State{_, _, _, _, _, _, _, _, out, _}:
      out

# an admin move: the same term, with a smaller measure
def Adm(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +st: C.Cir.State, +t: C.Term,
  +w: Nat) -> Data:
  Ex(Nat, w2 => P2(Inv(ds, ks, img, st, t, w2), N.Le(1n+w2, w)))

# a step: the term u of Eval's step
def Stp(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +st: C.Cir.State, +t: C.Term) ->
  Data:
  Ex(C.Term, u => P2({C.Eval.step(ds, t) == Some{u} : Maybe<C.Term>}, Ex(Nat, w2 => Inv(ds, ks, img, st, u, w2))))

# a round from the term t and the measure w that goes on: an admin move or a
# step
def Rnd(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +t: C.Term, +w: Nat,
  +st: C.Cir.State) -> Type:
  Or(Adm(ds, ks, img, st, t, w), Stp(ds, ks, img, st, t))

# a round that halts, from the term t: with 0, t has no step and its result
# is the output's bytes; with 2, it has no step and no result
def HR(+ds: List<&2, C.Def>, +t: C.Term, +s: U32, st: C.Cir.State) -> Type:
  Or(P2({s == 0 : U32}, P2({C.Eval.step(ds, t) == None{} : Maybe<C.Term>},
      {C.Program.result(ds, Some{t}) == Some{List.reverse(&2, U32, St.out(st))} : Maybe<&2, List<&2, U32>>})),
    P2({s == 2 : U32}, P2({C.Eval.step(ds, t) == None{} : Maybe<C.Term>},
      {C.Program.result(ds, Some{t}) == None{} : Maybe<&2, List<&2, U32>>})))

# a halt of the main loop, from the term t: with 0, Eval reaches from t the
# output's bytes; with 2, it reaches no result
def HE(+ds: List<&2, C.Def>, +t: C.Term, +s: U32, st: C.Cir.State) -> Type:
  Or(P2({s == 0 : U32}, Ex(Nat, k => {C.Program.result(ds, C.Eval.steps(k, ds, t)) == Some{List.reverse(&2, U32, St.out(st))} : Maybe<&2, List<&2, U32>>})),
    {s == 2 : U32} & @k: Nat -> {C.Program.result(ds, C.Eval.steps(k, ds, t)) == None{} : Maybe<&2, List<&2, U32>>})

# the end of a run that gives the bytes o, or runs out of memory
def Good(+o: List<&2, U32>, r: C.Cir.Out) -> Data:
  match r:
    case C.Cir.Out.next{_}:
      Empty
    case C.Cir.Out.halt{s, st}:
      P2({s == 0 : U32}, {List.reverse(&2, U32, St.out(st)) == o : List<&2, U32>})
    case C.Cir.Out.out_of_memory{}:
      Unit
    case C.Cir.Out.trap{}:
      Empty
    case C.Cir.Out.not_done{}:
      Empty

# the parts of an admin move and of a step
def adm.w(-ds: List<&2, C.Def>, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, -st: C.Cir.State, -t: C.Term,
  -w: Nat, a: Adm(ds, ks, img, st, t, w)) -> Nat:
  match a:
    case Tuple{w2, _}:
      w2

def adm.inv(-ds: List<&2, C.Def>, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, -st: C.Cir.State, -t: C.Term,
  -w: Nat, a: Adm(ds, ks, img, st, t, w)) -> Inv(ds, ks, img, st, t, adm.w(ds, ks, img, st, t, w, a)):
  match a:
    case Tuple{_, Tuple{i, _}}:
      i

def adm.lt(-ds: List<&2, C.Def>, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, -st: C.Cir.State, -t: C.Term,
  -w: Nat, a: Adm(ds, ks, img, st, t, w)) -> N.Le(1n+adm.w(ds, ks, img, st, t, w, a), w):
  match a:
    case Tuple{_, Tuple{_, l}}:
      l

def stp.u(-ds: List<&2, C.Def>, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, -st: C.Cir.State, -t: C.Term,
  x: Stp(ds, ks, img, st, t)) -> C.Term:
  match x:
    case Tuple{u, _}:
      u

def stp.es(-ds: List<&2, C.Def>, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, -st: C.Cir.State, -t: C.Term,
  x: Stp(ds, ks, img, st, t)) -> {C.Eval.step(ds, t) == Some{stp.u(ds, ks, img, st, t, x)} : Maybe<C.Term>}:
  match x:
    case Tuple{_, Tuple{e, _}}:
      e

def stp.w(-ds: List<&2, C.Def>, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, -st: C.Cir.State, -t: C.Term,
  x: Stp(ds, ks, img, st, t)) -> Nat:
  match x:
    case Tuple{_, Tuple{_, Tuple{w2, _}}}:
      w2

def stp.inv(-ds: List<&2, C.Def>, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, -st: C.Cir.State, -t: C.Term,
  x: Stp(ds, ks, img, st, t)) -> Inv(ds, ks, img, st, stp.u(ds, ks, img, st, t, x), stp.w(ds, ks, img, st, t, x)):
  match x:
    case Tuple{_, Tuple{_, Tuple{_, i}}}:
      i

# Small facts
# -----------

def mb.get(x: Maybe<&2, List<&2, U32>>, d: List<&2, U32>) -> List<&2, U32>:
  match x:
    case None{}:
      d
    case Some{y}:
      y

# Some is one to one
def mb.inj(+a: List<&2, U32>, -b: List<&2, U32>, e: {Some{a} == Some{b} : Maybe<&2, List<&2, U32>>}) ->
  {a == b : List<&2, U32>}:
  Equal.cong(Maybe<&2, List<&2, U32>>, List<&2, U32>, x => mb.get(x, a), Some{a}, Some{b}, e)

def mb.none(x: Maybe<&2, List<&2, U32>>) -> Type:
  match x:
    case None{}:
      Unit
    case Some{_}:
      Empty

# None is not Some
def mb.ne(-o: List<&2, U32>, e: {None{} == Some{o} : Maybe<&2, List<&2, U32>>}) -> Empty:
  %e : mb.none(_)
  Unit{}

# no steps from None
def run.none(+j: Nat, +ds: List<&2, C.Def>) -> {C.Eval.run(j, ds, None{}) == None{} : Maybe<C.Term>}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      {==}

# the result of a term that is no value is none
def res.nv(+ds: List<&2, C.Def>, +t: C.Term, nv: {C.Eval.vals(ds, t, False{}) == False{} : Bool}) ->
  {C.Program.result(ds, Some{t}) == None{} : Maybe<&2, List<&2, U32>>}:
  %Equal.sym(Bool, C.Eval.vals(ds, t, False{}), False{}, nv) : {C.Program.result.if(_, t) == None{} : Maybe<&2, List<&2, U32>>}
  {==}

def st.none(x: Maybe<C.Term>) -> Type:
  match x:
    case None{}:
      Unit
    case Some{_}:
      Empty

# no step is not a step
def st.ne(-u: C.Term, e: {None{} == Some{u} : Maybe<C.Term>}) -> Empty:
  %e : st.none(_)
  Unit{}

# Words and cells
# ---------------
#
# U32.is_eq decides equality (u32.eq, u32.refl), through Weq, the equality of
# words bit by bit; a cell set is there (cl.gs), and the others are kept
# (cl.go).

def bool.t(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def bool.ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  Empty.absurd(G, (%e : bool.t(_); Unit{}))

def bq(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case True{} False{}:
      False{}
    case False{} True{}:
      False{}

def Weq(n: Nat, v: Word(n), w: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match v w:
        case WCon{a, s} WCon{b, t}:
          Bool.and(bq(a, b), Weq(p, s, t))

def weq.fin(a: Bool, b: Bool, x: Cmp) -> {Cmp.is_eq(Word.cmp.fin(a, b, x)) == Bool.and(bq(a, b), Cmp.is_eq(x)) : Bool}:
  match a b x:
    case True{} True{} LT{}:
      {==}
    case True{} False{} LT{}:
      {==}
    case False{} True{} LT{}:
      {==}
    case False{} False{} LT{}:
      {==}
    case True{} True{} EQ{}:
      {==}
    case True{} False{} EQ{}:
      {==}
    case False{} True{} EQ{}:
      {==}
    case False{} False{} EQ{}:
      {==}
    case True{} True{} GT{}:
      {==}
    case True{} False{} GT{}:
      {==}
    case False{} True{} GT{}:
      {==}
    case False{} False{} GT{}:
      {==}

def weq.cmp(n: Nat, v: Word(n), w: Word(n)) -> {Cmp.is_eq(Word.cmp(n, v, w)) == Weq(n, v, w) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      match v w:
        case WCon{+a, +s} WCon{+b, +t}:
          Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(a, b, Word.cmp(p, s, t))), Bool.and(bq(a, b), Cmp.is_eq(Word.cmp(p, s, t))),
            Bool.and(bq(a, b), Weq(p, s, t)), weq.fin(a, b, Word.cmp(p, s, t)),
            Equal.cong(Bool, Bool, x => Bool.and(bq(a, b), x), Cmp.is_eq(Word.cmp(p, s, t)), Weq(p, s, t), weq.cmp(p, s, t)))

def weq.eq(n: Nat, v: Word(n), w: Word(n), h: {Weq(n, v, w) == True{} : Bool}) -> {v == w : Word(n)}:
  match n:
    case 0n:
      match v w:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match v w:
        case WCon{True{}, +s} WCon{True{}, +t}:
          Equal.cong(Word(p), Word(1n+p), x => WCon{True{}, x}, s, t, weq.eq(p, s, t, h))
        case WCon{False{}, +s} WCon{False{}, +t}:
          Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x}, s, t, weq.eq(p, s, t, h))
        case WCon{True{}, +s} WCon{False{}, +t}:
          bool.ft({WCon{True{}, s} == WCon{False{}, t} : Word(1n+p)}, h)
        case WCon{False{}, +s} WCon{True{}, +t}:
          bool.ft({WCon{False{}, s} == WCon{True{}, t} : Word(1n+p)}, h)

def weq.refl(n: Nat, w: Word(n)) -> {Weq(n, w, w) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{True{}, s}:
          weq.refl(p, s)
        case WCon{False{}, s}:
          weq.refl(p, s)

# U32.is_eq decides equality
def u32.eq(+a: U32, +b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{+v} U32{+w}:
      Equal.cong(Word(32n), U32, x => U32{x}, v, w, weq.eq(32n, v, w,
        Equal.trans(Bool, Weq(32n, v, w), Cmp.is_eq(Word.cmp(32n, v, w)), True{},
          Equal.sym(Bool, Cmp.is_eq(Word.cmp(32n, v, w)), Weq(32n, v, w), weq.cmp(32n, v, w)), h)))

def u32.refl(+a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  match a:
    case U32{+w}:
      Equal.trans(Bool, Cmp.is_eq(Word.cmp(32n, w, w)), Weq(32n, w, w), True{}, weq.cmp(32n, w, w), weq.refl(32n, w))

# equal numbers that U32.is_eq says differ: none
def u32.ne(+a: U32, +b: U32, h: {U32.is_eq(a, b) == False{} : Bool}, e: {a == b : U32}) -> Empty:
  bool.ft(Empty, Equal.trans(Bool, False{}, U32.is_eq(a, b), True{}, Equal.sym(Bool, U32.is_eq(a, b), False{}, h),
    (%e : {U32.is_eq(a, _) == True{} : Bool}; u32.refl(a))))

def cl.none(n: Nat, +w: Word(n)) -> {C.Cir.Cells.get.at(n, w, C.Cir.Cells.none{}) == C.Cir.Cell.zero() : C.Cir.Cell}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{True{}, t}:
          {==}
        case WCon{False{}, t}:
          {==}

def cl.gs.at(n: Nat, +w: Word(n), +m: C.Cir.Cells, +c: C.Cir.Cell) ->
  {C.Cir.Cells.get.at(n, w, C.Cir.Cells.set.at(n, w, m, c)) == c : C.Cir.Cell}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w m:
        case WCon{False{}, +t} C.Cir.Cells.node{+lo, +hi}:
          cl.gs.at(p, t, lo, c)
        case WCon{True{}, +t} C.Cir.Cells.node{+lo, +hi}:
          cl.gs.at(p, t, hi, c)
        case WCon{False{}, +t} C.Cir.Cells.none{}:
          cl.gs.at(p, t, C.Cir.Cells.none{}, c)
        case WCon{True{}, +t} C.Cir.Cells.none{}:
          cl.gs.at(p, t, C.Cir.Cells.none{}, c)
        case WCon{False{}, +t} C.Cir.Cells.one{d}:
          cl.gs.at(p, t, C.Cir.Cells.none{}, c)
        case WCon{True{}, +t} C.Cir.Cells.one{d}:
          cl.gs.at(p, t, C.Cir.Cells.none{}, c)

# a cell set is there
def cl.gs(+m: C.Cir.Cells, +i: U32, +c: C.Cir.Cell) -> {C.Cir.Cells.get(C.Cir.Cells.set(m, i, c), i) == c : C.Cir.Cell}:
  match i:
    case U32{+w}:
      cl.gs.at(32n, w, m, c)

def cl.go.at(n: Nat, +v: Word(n), +w: Word(n), +m: C.Cir.Cells, +c: C.Cir.Cell, h: {Weq(n, v, w) == False{} : Bool}) ->
  {C.Cir.Cells.get.at(n, v, C.Cir.Cells.set.at(n, w, m, c)) == C.Cir.Cells.get.at(n, v, m) : C.Cir.Cell}:
  match n:
    case 0n:
      match v w:
        case WNil{} WNil{}:
          bool.ft({C.Cir.Cells.get.at(0n, WNil{}, C.Cir.Cells.set.at(0n, WNil{}, m, c)) == C.Cir.Cells.get.at(0n, WNil{}, m) : C.Cir.Cell},
            Equal.sym(Bool, True{}, False{}, h))
    case 1n+(+p):
      match v w m:
        case WCon{False{}, +s} WCon{False{}, +t} C.Cir.Cells.node{+lo, +hi}:
          cl.go.at(p, s, t, lo, c, h)
        case WCon{False{}, +s} WCon{False{}, +t} C.Cir.Cells.none{}:
          Equal.trans(C.Cir.Cell, C.Cir.Cells.get.at(p, s, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, c)), C.Cir.Cells.get.at(p, s, C.Cir.Cells.none{}), C.Cir.Cell.zero(),
            cl.go.at(p, s, t, C.Cir.Cells.none{}, c, h), cl.none(p, s))
        case WCon{False{}, +s} WCon{False{}, +t} C.Cir.Cells.one{+d}:
          Equal.trans(C.Cir.Cell, C.Cir.Cells.get.at(p, s, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, c)), C.Cir.Cells.get.at(p, s, C.Cir.Cells.none{}), C.Cir.Cell.zero(),
            cl.go.at(p, s, t, C.Cir.Cells.none{}, c, h), cl.none(p, s))
        case WCon{False{}, +s} WCon{True{}, +t} C.Cir.Cells.node{+lo, +hi}:
          {==}
        case WCon{False{}, +s} WCon{True{}, +t} C.Cir.Cells.none{}:
          cl.none(p, s)
        case WCon{False{}, +s} WCon{True{}, +t} C.Cir.Cells.one{+d}:
          cl.none(p, s)
        case WCon{True{}, +s} WCon{False{}, +t} C.Cir.Cells.node{+lo, +hi}:
          {==}
        case WCon{True{}, +s} WCon{False{}, +t} C.Cir.Cells.none{}:
          cl.none(p, s)
        case WCon{True{}, +s} WCon{False{}, +t} C.Cir.Cells.one{+d}:
          cl.none(p, s)
        case WCon{True{}, +s} WCon{True{}, +t} C.Cir.Cells.node{+lo, +hi}:
          cl.go.at(p, s, t, hi, c, h)
        case WCon{True{}, +s} WCon{True{}, +t} C.Cir.Cells.none{}:
          Equal.trans(C.Cir.Cell, C.Cir.Cells.get.at(p, s, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, c)), C.Cir.Cells.get.at(p, s, C.Cir.Cells.none{}), C.Cir.Cell.zero(),
            cl.go.at(p, s, t, C.Cir.Cells.none{}, c, h), cl.none(p, s))
        case WCon{True{}, +s} WCon{True{}, +t} C.Cir.Cells.one{+d}:
          Equal.trans(C.Cir.Cell, C.Cir.Cells.get.at(p, s, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, c)), C.Cir.Cells.get.at(p, s, C.Cir.Cells.none{}), C.Cir.Cell.zero(),
            cl.go.at(p, s, t, C.Cir.Cells.none{}, c, h), cl.none(p, s))

# a set keeps the other cells
def cl.go(+m: C.Cir.Cells, +j: U32, +i: U32, +c: C.Cir.Cell, h: {U32.is_eq(j, i) == False{} : Bool}) ->
  {C.Cir.Cells.get(C.Cir.Cells.set(m, i, c), j) == C.Cir.Cells.get(m, j) : C.Cir.Cell}:
  match j i:
    case U32{+v} U32{+w}:
      cl.go.at(32n, v, w, m, c, Equal.trans(Bool, Weq(32n, v, w), Cmp.is_eq(Word.cmp(32n, v, w)), False{},
        Equal.sym(Bool, Cmp.is_eq(Word.cmp(32n, v, w)), Weq(32n, v, w), weq.cmp(32n, v, w)), h))

# a cell equal to sx would have sx's tag
def ne.of(b: Bool, +m: C.Cir.Cells, +c: U32, +sx: U32, -tag: U32, eb: {U32.is_eq(c, sx) == b : Bool},
  etag: {TgW(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c))) == tag : U32}, ht: {U32.is_lt(TgW(Fd(0n, m, sx)), 32) == False{} : Bool},
  hl: {U32.is_lt(tag, 32) == True{} : Bool}) -> {U32.is_eq(c, sx) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +e = u32.eq(c, sx, eb)
      bool.ft({U32.is_eq(c, sx) == False{} : Bool},
        Equal.trans(Bool, False{}, U32.is_lt(TgW(Fd(0n, m, c)), 32), True{},
          (%Equal.sym(U32, c, sx, e) : {False{} == U32.is_lt(TgW(Fd(0n, m, _)), 32) : Bool}; Equal.sym(Bool, U32.is_lt(TgW(Fd(0n, m, sx)), 32), False{}, ht)),
          (%Equal.sym(U32, TgW(C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c))), tag, etag) : {U32.is_lt(_, 32) == True{} : Bool}; hl)))

# Stores to a cell of the machine's own kinds
# -------------------------------------------
#
# A store to a cell whose tag is 32 or more (a frame, an argument, a check, a
# root) keeps every term that Is says: a node of a term has a tag below 32,
# so it is another cell (is.st, by induction on the term).

# a node of the tag tag (below 32) is not the cell sx (of a tag of 32 or more)
def ne.nd(+ds: List<&2, C.Def>, +im: U32, +fi: U32, +nx: U32, +m: C.Cir.Cells, +c: U32, +sx: U32, -t: C.Term, +tag: U32,
  nd: Nd(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), t, tag), ht: {U32.is_lt(TgW(Fd(0n, m, sx)), 32) == False{} : Bool},
  hl: {U32.is_lt(tag, 32) == True{} : Bool}) -> {U32.is_eq(c, sx) == False{} : Bool}:
  match nd:
    case Tuple{_, Tuple{_, Tuple{etag, _}}}:
      ne.of(U32.is_eq(c, sx), m, c, sx, tag, {==}, etag, ht, hl)

def isc.at(+ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +c: U32, -y1: C.Cir.Cell, -y2: C.Cir.Cell, -t: C.Term, e: {y1 == y2 : C.Cir.Cell},
  h: IsC(ds, m, im, fi, nx, ks, img, c, y2, t)) -> IsC(ds, m, im, fi, nx, ks, img, c, y1, t):
  %Equal.sym(C.Cir.Cell, y1, y2, e) : IsC(ds, m, im, fi, nx, ks, img, c, _, t)
  h

def sp.at(+fi: U32, +nx: U32, +c: U32, -y1: C.Cir.Cell, -y2: C.Cir.Cell, e: {y1 == y2 : C.Cir.Cell}, h: Sp(fi, nx, c, y2)) ->
  Sp(fi, nx, c, y1):
  %Equal.sym(C.Cir.Cell, y1, y2, e) : Sp(fi, nx, c, _)
  h

# a store to the cell sx, of a tag of 32 or more, keeps the cell c and its term
def is.st(t: C.Term, +ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +sx: U32, +sv: C.Cir.Cell, +c: U32, +ht: {U32.is_lt(TgW(Fd(0n, m, sx)), 32) == False{} : Bool},
  h: Is(ds, m, im, fi, nx, ks, img, c, t)) ->
  P2({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), c) == C.Cir.Cells.get(m, c) : C.Cir.Cell}, Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, t)):
  match t:
    case C.Term.Var{+i}:
      match h:
        case Tuple{+nd, x1}:
          +ec = cl.go(m, c, sx, sv, ne.nd(ds, im, fi, nx, m, c, sx, C.Term.Var{i}, 0, nd, ht, {==}))
          (ec, isc.at(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), c), C.Cir.Cells.get(m, c), C.Term.Var{i}, ec, (nd, x1)))
    case C.Term.Ref{+kk}:
      match h:
        case Tuple{+nd, Tuple{x1, Tuple{x2, x3}}}:
          +ec = cl.go(m, c, sx, sv, ne.nd(ds, im, fi, nx, m, c, sx, C.Term.Ref{kk}, 1, nd, ht, {==}))
          (ec, isc.at(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), c), C.Cir.Cells.get(m, c), C.Term.Ref{kk}, ec, (nd, (x1, (x2, x3)))))
    case C.Term.Ann{+t1, +t2}:
      match h:
        case Tuple{+nd, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}:
          +ec = cl.go(m, c, sx, sv, ne.nd(ds, im, fi, nx, m, c, sx, C.Term.Ann{t1, t2}, 2, nd, ht, {==}))
          +r2 = is.st(t1, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), ht, h2)
          +r3 = is.st(t2, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), ht, h3)
          (ec, isc.at(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), c), C.Cir.Cells.get(m, c), C.Term.Ann{t1, t2}, ec, (nd, ((sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), t1), r2), sp2), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), t1), r2)), (sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), t2), r3), sp3), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), t2), r3))))))
    case C.Term.Let{+qq, +t1, +t2}:
      match h:
        case Tuple{+nd, Tuple{x1, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
          +ec = cl.go(m, c, sx, sv, ne.nd(ds, im, fi, nx, m, c, sx, C.Term.Let{qq, t1, t2}, 3, nd, ht, {==}))
          +r2 = is.st(t1, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), ht, h2)
          +r3 = is.st(t2, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), ht, h3)
          (ec, isc.at(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), c), C.Cir.Cells.get(m, c), C.Term.Let{qq, t1, t2}, ec, (nd, (x1, ((sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), t1), r2), sp2), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), t1), r2)), (sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), t2), r3), sp3), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), t2), r3)))))))
    case C.Term.Typ{+t1}:
      match h:
        case Tuple{+nd, Tuple{sp2, h2}}:
          +ec = cl.go(m, c, sx, sv, ne.nd(ds, im, fi, nx, m, c, sx, C.Term.Typ{t1}, 4, nd, ht, {==}))
          +r2 = is.st(t1, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), ht, h2)
          (ec, isc.at(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), c), C.Cir.Cells.get(m, c), C.Term.Typ{t1}, ec, (nd, (sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), t1), r2), sp2), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), t1), r2)))))
    case C.Term.Min{+t1, +t2}:
      match h:
        case Tuple{+nd, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}:
          +ec = cl.go(m, c, sx, sv, ne.nd(ds, im, fi, nx, m, c, sx, C.Term.Min{t1, t2}, 5, nd, ht, {==}))
          +r2 = is.st(t1, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), ht, h2)
          +r3 = is.st(t2, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), ht, h3)
          (ec, isc.at(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), c), C.Cir.Cells.get(m, c), C.Term.Min{t1, t2}, ec, (nd, ((sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), t1), r2), sp2), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), t1), r2)), (sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), t2), r3), sp3), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), t2), r3))))))
    case C.Term.All{+qq, +t1, +t2}:
      match h:
        case Tuple{+nd, Tuple{x1, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
          +ec = cl.go(m, c, sx, sv, ne.nd(ds, im, fi, nx, m, c, sx, C.Term.All{qq, t1, t2}, 6, nd, ht, {==}))
          +r2 = is.st(t1, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), ht, h2)
          +r3 = is.st(t2, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), ht, h3)
          (ec, isc.at(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), c), C.Cir.Cells.get(m, c), C.Term.All{qq, t1, t2}, ec, (nd, (x1, ((sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), t1), r2), sp2), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), t1), r2)), (sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), t2), r3), sp3), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), t2), r3)))))))
    case C.Term.Lam{+qq, +t1}:
      match h:
        case Tuple{+nd, Tuple{x1, Tuple{sp2, h2}}}:
          +ec = cl.go(m, c, sx, sv, ne.nd(ds, im, fi, nx, m, c, sx, C.Term.Lam{qq, t1}, 7, nd, ht, {==}))
          +r2 = is.st(t1, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), ht, h2)
          (ec, isc.at(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), c), C.Cir.Cells.get(m, c), C.Term.Lam{qq, t1}, ec, (nd, (x1, (sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), t1), r2), sp2), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), t1), r2))))))
    case C.Term.App{+qq, +t1, +t2}:
      match h:
        case Tuple{+nd, Tuple{x1, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
          +ec = cl.go(m, c, sx, sv, ne.nd(ds, im, fi, nx, m, c, sx, C.Term.App{qq, t1, t2}, 8, nd, ht, {==}))
          +r2 = is.st(t1, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), ht, h2)
          +r3 = is.st(t2, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), ht, h3)
          (ec, isc.at(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), c), C.Cir.Cells.get(m, c), C.Term.App{qq, t1, t2}, ec, (nd, (x1, ((sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), t1), r2), sp2), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), t1), r2)), (sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), t2), r3), sp3), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), t2), r3)))))))
    case C.Term.Sig{+qq, +t1, +t2}:
      match h:
        case Tuple{+nd, Tuple{x1, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
          +ec = cl.go(m, c, sx, sv, ne.nd(ds, im, fi, nx, m, c, sx, C.Term.Sig{qq, t1, t2}, 9, nd, ht, {==}))
          +r2 = is.st(t1, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), ht, h2)
          +r3 = is.st(t2, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), ht, h3)
          (ec, isc.at(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), c), C.Cir.Cells.get(m, c), C.Term.Sig{qq, t1, t2}, ec, (nd, (x1, ((sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), t1), r2), sp2), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), t1), r2)), (sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), t2), r3), sp3), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), t2), r3)))))))
    case C.Term.Tup{+qq, +t1, +t2}:
      match h:
        case Tuple{+nd, Tuple{x1, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
          +ec = cl.go(m, c, sx, sv, ne.nd(ds, im, fi, nx, m, c, sx, C.Term.Tup{qq, t1, t2}, 10, nd, ht, {==}))
          +r2 = is.st(t1, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), ht, h2)
          +r3 = is.st(t2, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), ht, h3)
          (ec, isc.at(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), c), C.Cir.Cells.get(m, c), C.Term.Tup{qq, t1, t2}, ec, (nd, (x1, ((sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), t1), r2), sp2), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), t1), r2)), (sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), t2), r3), sp3), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), t2), r3)))))))
    case C.Term.Prj{+t1}:
      match h:
        case Tuple{+nd, Tuple{sp2, h2}}:
          +ec = cl.go(m, c, sx, sv, ne.nd(ds, im, fi, nx, m, c, sx, C.Term.Prj{t1}, 11, nd, ht, {==}))
          +r2 = is.st(t1, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), ht, h2)
          (ec, isc.at(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), c), C.Cir.Cells.get(m, c), C.Term.Prj{t1}, ec, (nd, (sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), t1), r2), sp2), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), t1), r2)))))
    case C.Term.Enu{+ee}:
      match h:
        case Tuple{+nd, Tuple{x1, x2}}:
          +ec = cl.go(m, c, sx, sv, ne.nd(ds, im, fi, nx, m, c, sx, C.Term.Enu{ee}, 12, nd, ht, {==}))
          (ec, isc.at(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), c), C.Cir.Cells.get(m, c), C.Term.Enu{ee}, ec, (nd, (x1, x2))))
    case C.Term.Lab{+kk}:
      match h:
        case Tuple{+nd, x1}:
          +ec = cl.go(m, c, sx, sv, ne.nd(ds, im, fi, nx, m, c, sx, C.Term.Lab{kk}, 13, nd, ht, {==}))
          (ec, isc.at(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), c), C.Cir.Cells.get(m, c), C.Term.Lab{kk}, ec, (nd, x1)))
    case C.Term.Mat{+kk, +t1, +t2}:
      match h:
        case Tuple{+nd, Tuple{x1, Tuple{Tuple{sp3, h3}, Tuple{sp4, h4}}}}:
          +ec = cl.go(m, c, sx, sv, ne.nd(ds, im, fi, nx, m, c, sx, C.Term.Mat{kk, t1, t2}, 14, nd, ht, {==}))
          +r3 = is.st(t1, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), ht, h3)
          +r4 = is.st(t2, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c)), ht, h4)
          (ec, isc.at(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), c), C.Cir.Cells.get(m, c), C.Term.Mat{kk, t1, t2}, ec, (nd, (x1, ((sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), t1), r3), sp3), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), t1), r3)), (sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c)), t2), r4), sp4), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c)), t2), r4)))))))
    case C.Term.Efq{}:
      +nd = h
      +ec = cl.go(m, c, sx, sv, ne.nd(ds, im, fi, nx, m, c, sx, C.Term.Efq{}, 15, nd, ht, {==}))
      (ec, isc.at(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), c), C.Cir.Cells.get(m, c), C.Term.Efq{}, ec, nd))
    case C.Term.Eql{+t1, +t2, +t3}:
      match h:
        case Tuple{+nd, Tuple{Tuple{sp2, h2}, Tuple{Tuple{sp3, h3}, Tuple{sp4, h4}}}}:
          +ec = cl.go(m, c, sx, sv, ne.nd(ds, im, fi, nx, m, c, sx, C.Term.Eql{t1, t2, t3}, 16, nd, ht, {==}))
          +r2 = is.st(t1, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), ht, h2)
          +r3 = is.st(t2, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), ht, h3)
          +r4 = is.st(t3, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c)), ht, h4)
          (ec, isc.at(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), c), C.Cir.Cells.get(m, c), C.Term.Eql{t1, t2, t3}, ec, (nd, ((sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), t1), r2), sp2), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), t1), r2)), ((sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), t2), r3), sp3), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), t2), r3)), (sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c)), t3), r4), sp4), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c)), t3), r4)))))))
    case C.Term.Rfl{}:
      +nd = h
      +ec = cl.go(m, c, sx, sv, ne.nd(ds, im, fi, nx, m, c, sx, C.Term.Rfl{}, 17, nd, ht, {==}))
      (ec, isc.at(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), c), C.Cir.Cells.get(m, c), C.Term.Rfl{}, ec, nd))
    case C.Term.Rwt{+t1, +t2, +t3}:
      match h:
        case Tuple{+nd, Tuple{Tuple{sp2, h2}, Tuple{Tuple{sp3, h3}, Tuple{sp4, h4}}}}:
          +ec = cl.go(m, c, sx, sv, ne.nd(ds, im, fi, nx, m, c, sx, C.Term.Rwt{t1, t2, t3}, 18, nd, ht, {==}))
          +r2 = is.st(t1, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), ht, h2)
          +r3 = is.st(t2, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), ht, h3)
          +r4 = is.st(t3, ds, m, im, fi, nx, ks, img, sx, sv, C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c)), ht, h4)
          (ec, isc.at(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), c), C.Cir.Cells.get(m, c), C.Term.Rwt{t1, t2, t3}, ec, (nd, ((sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), t1), r2), sp2), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(2n, C.Cir.Cells.get(m, c)), t1), r2)), ((sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), t2), r3), sp3), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(3n, C.Cir.Cells.get(m, c)), t2), r3)), (sp.at(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c))), C.Cir.Cells.get(m, C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c))), Ex.fst({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c)), t3), r4), sp4), Ex.snd({C.Cir.Cells.get(C.Cir.Cells.set(m, sx, sv), C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c))) == C.Cir.Cells.get(m, C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c))) : C.Cir.Cell}, _ => Is(ds, C.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, C.Cir.Cell.get(4n, C.Cir.Cells.get(m, c)), t3), r4)))))))

# Stores to field 1
# -----------------
#
# A store to field 1 of any cell (a count, or a link of the pend list or of
# the frames) keeps every term that Is says, and field 0 of its cells (is.f1,
# by induction on the term): Is reads fields 0, 2, 3 and 4 only.

def set1.id(+y: C.Cir.Cell) -> {y == C.Cir.Cell.set(1n, y, C.Cir.Cell.get(1n, y)) : C.Cir.Cell}:
  match y:
    case C.Cir.Cell{a, b, x2, x3, x4}:
      {==}

def cl.f1.of(b: Bool, +m: C.Cir.Cells, +sx: U32, +sv: U32, +c: U32, eb: {U32.is_eq(c, sx) == b : Bool}) ->
  Ex(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, c), w) : C.Cir.Cell}):
  match b:
    case True{}:
      +e = u32.eq(c, sx, eb)
      %Equal.sym(U32, c, sx, e) :
        Ex(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), _) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, _), w) : C.Cir.Cell})
      (sv, cl.gs(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)))
    case False{}:
      (C.Cir.Cell.get(1n, C.Cir.Cells.get(m, c)),
        Equal.trans(C.Cir.Cell, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cells.get(m, c),
          C.Cir.Cell.set(1n, C.Cir.Cells.get(m, c), C.Cir.Cell.get(1n, C.Cir.Cells.get(m, c))),
          cl.go(m, c, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv), eb), set1.id(C.Cir.Cells.get(m, c))))

# after a store to field 1, a cell is its old one with another field 1
def cl.f1(+m: C.Cir.Cells, +sx: U32, +sv: U32, +c: U32) ->
  Ex(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, c), w) : C.Cir.Cell}):
  cl.f1.of(U32.is_eq(c, sx), m, sx, sv, c, {==})

def sp.at0(+fi: U32, +nx: U32, +c: U32, -y1: C.Cir.Cell, -y2: C.Cir.Cell,
  e: {C.Cir.Cell.get(0n, y1) == C.Cir.Cell.get(0n, y2) : U32}, h: Sp(fi, nx, c, y2)) -> Sp(fi, nx, c, y1):
  %Equal.sym(U32, C.Cir.Cell.get(0n, y1), C.Cir.Cell.get(0n, y2), e) : {Bool.or(Own(fi, nx, c), FlW(_, 1024)) == True{} : Bool}
  h


# a store to field 1 of the cell sx keeps field 0 of the cell c, of the old
# value y, and its term
def is.f1(t: C.Term, +ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +sx: U32, +sv: U32, +c: U32, y: C.Cir.Cell, +w: U32,
  +ew: {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c) == C.Cir.Cell.set(1n, y, w) : C.Cir.Cell},
  +ey: {C.Cir.Cells.get(m, c) == y : C.Cir.Cell}, h: IsC(ds, m, im, fi, nx, ks, img, c, y, t)) ->
  P2({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)) : U32},
    Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, c, t)):
  match t:
    case C.Term.Var{+i}:
      match y:
        case C.Cir.Cell{+a, b0, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, x1e}:
              (Equal.trans(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c)), a, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)),
            Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, ew),
            Equal.sym(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), a, Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(m, c), C.Cir.Cell{a, b0, x2, x3, x4}, ey))),
                isc.at(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, C.Term.Var{i}, ew, (nd, x1e)))
    case C.Term.Ref{+kk}:
      match y:
        case C.Cir.Cell{+a, b0, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{x1e, Tuple{x2e, x3e}}}:
              (Equal.trans(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c)), a, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)),
            Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, ew),
            Equal.sym(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), a, Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(m, c), C.Cir.Cell{a, b0, x2, x3, x4}, ey))),
                isc.at(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, C.Term.Ref{kk}, ew, (nd, (x1e, (x2e, x3e)))))
    case C.Term.Ann{+t1, +t2}:
      match y:
        case C.Cir.Cell{+a, b0, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}:
              +c2 = cl.f1(m, sx, sv, x2)
              +r2 = is.f1(t1, ds, m, im, fi, nx, ks, img, sx, sv, x2, C.Cir.Cells.get(m, x2), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x2), w) : C.Cir.Cell}, c2),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x2), w) : C.Cir.Cell}, c2), {==}, h2)
              +c3 = cl.f1(m, sx, sv, x3)
              +r3 = is.f1(t2, ds, m, im, fi, nx, ks, img, sx, sv, x3, C.Cir.Cells.get(m, x3), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x3), w) : C.Cir.Cell}, c3),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x3), w) : C.Cir.Cell}, c3), {==}, h3)
              (Equal.trans(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c)), a, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)),
            Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, ew),
            Equal.sym(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), a, Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(m, c), C.Cir.Cell{a, b0, x2, x3, x4}, ey))),
                isc.at(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, C.Term.Ann{t1, t2}, ew, (nd, ((sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2), C.Cir.Cells.get(m, x2), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x2)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x2, t1), r2), sp2), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x2)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x2, t1), r2)), (sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3), C.Cir.Cells.get(m, x3), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x3)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x3, t2), r3), sp3), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x3)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x3, t2), r3))))))
    case C.Term.Let{+qq, +t1, +t2}:
      match y:
        case C.Cir.Cell{+a, b0, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{x1e, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
              +c2 = cl.f1(m, sx, sv, x2)
              +r2 = is.f1(t1, ds, m, im, fi, nx, ks, img, sx, sv, x2, C.Cir.Cells.get(m, x2), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x2), w) : C.Cir.Cell}, c2),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x2), w) : C.Cir.Cell}, c2), {==}, h2)
              +c3 = cl.f1(m, sx, sv, x3)
              +r3 = is.f1(t2, ds, m, im, fi, nx, ks, img, sx, sv, x3, C.Cir.Cells.get(m, x3), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x3), w) : C.Cir.Cell}, c3),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x3), w) : C.Cir.Cell}, c3), {==}, h3)
              (Equal.trans(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c)), a, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)),
            Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, ew),
            Equal.sym(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), a, Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(m, c), C.Cir.Cell{a, b0, x2, x3, x4}, ey))),
                isc.at(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, C.Term.Let{qq, t1, t2}, ew, (nd, (x1e, ((sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2), C.Cir.Cells.get(m, x2), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x2)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x2, t1), r2), sp2), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x2)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x2, t1), r2)), (sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3), C.Cir.Cells.get(m, x3), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x3)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x3, t2), r3), sp3), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x3)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x3, t2), r3)))))))
    case C.Term.Typ{+t1}:
      match y:
        case C.Cir.Cell{+a, b0, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{sp2, h2}}:
              +c2 = cl.f1(m, sx, sv, x2)
              +r2 = is.f1(t1, ds, m, im, fi, nx, ks, img, sx, sv, x2, C.Cir.Cells.get(m, x2), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x2), w) : C.Cir.Cell}, c2),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x2), w) : C.Cir.Cell}, c2), {==}, h2)
              (Equal.trans(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c)), a, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)),
            Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, ew),
            Equal.sym(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), a, Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(m, c), C.Cir.Cell{a, b0, x2, x3, x4}, ey))),
                isc.at(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, C.Term.Typ{t1}, ew, (nd, (sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2), C.Cir.Cells.get(m, x2), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x2)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x2, t1), r2), sp2), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x2)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x2, t1), r2)))))
    case C.Term.Min{+t1, +t2}:
      match y:
        case C.Cir.Cell{+a, b0, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}:
              +c2 = cl.f1(m, sx, sv, x2)
              +r2 = is.f1(t1, ds, m, im, fi, nx, ks, img, sx, sv, x2, C.Cir.Cells.get(m, x2), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x2), w) : C.Cir.Cell}, c2),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x2), w) : C.Cir.Cell}, c2), {==}, h2)
              +c3 = cl.f1(m, sx, sv, x3)
              +r3 = is.f1(t2, ds, m, im, fi, nx, ks, img, sx, sv, x3, C.Cir.Cells.get(m, x3), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x3), w) : C.Cir.Cell}, c3),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x3), w) : C.Cir.Cell}, c3), {==}, h3)
              (Equal.trans(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c)), a, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)),
            Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, ew),
            Equal.sym(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), a, Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(m, c), C.Cir.Cell{a, b0, x2, x3, x4}, ey))),
                isc.at(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, C.Term.Min{t1, t2}, ew, (nd, ((sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2), C.Cir.Cells.get(m, x2), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x2)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x2, t1), r2), sp2), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x2)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x2, t1), r2)), (sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3), C.Cir.Cells.get(m, x3), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x3)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x3, t2), r3), sp3), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x3)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x3, t2), r3))))))
    case C.Term.All{+qq, +t1, +t2}:
      match y:
        case C.Cir.Cell{+a, b0, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{x1e, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
              +c2 = cl.f1(m, sx, sv, x2)
              +r2 = is.f1(t1, ds, m, im, fi, nx, ks, img, sx, sv, x2, C.Cir.Cells.get(m, x2), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x2), w) : C.Cir.Cell}, c2),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x2), w) : C.Cir.Cell}, c2), {==}, h2)
              +c3 = cl.f1(m, sx, sv, x3)
              +r3 = is.f1(t2, ds, m, im, fi, nx, ks, img, sx, sv, x3, C.Cir.Cells.get(m, x3), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x3), w) : C.Cir.Cell}, c3),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x3), w) : C.Cir.Cell}, c3), {==}, h3)
              (Equal.trans(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c)), a, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)),
            Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, ew),
            Equal.sym(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), a, Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(m, c), C.Cir.Cell{a, b0, x2, x3, x4}, ey))),
                isc.at(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, C.Term.All{qq, t1, t2}, ew, (nd, (x1e, ((sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2), C.Cir.Cells.get(m, x2), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x2)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x2, t1), r2), sp2), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x2)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x2, t1), r2)), (sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3), C.Cir.Cells.get(m, x3), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x3)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x3, t2), r3), sp3), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x3)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x3, t2), r3)))))))
    case C.Term.Lam{+qq, +t1}:
      match y:
        case C.Cir.Cell{+a, b0, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{x1e, Tuple{sp2, h2}}}:
              +c2 = cl.f1(m, sx, sv, x2)
              +r2 = is.f1(t1, ds, m, im, fi, nx, ks, img, sx, sv, x2, C.Cir.Cells.get(m, x2), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x2), w) : C.Cir.Cell}, c2),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x2), w) : C.Cir.Cell}, c2), {==}, h2)
              (Equal.trans(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c)), a, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)),
            Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, ew),
            Equal.sym(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), a, Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(m, c), C.Cir.Cell{a, b0, x2, x3, x4}, ey))),
                isc.at(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, C.Term.Lam{qq, t1}, ew, (nd, (x1e, (sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2), C.Cir.Cells.get(m, x2), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x2)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x2, t1), r2), sp2), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x2)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x2, t1), r2))))))
    case C.Term.App{+qq, +t1, +t2}:
      match y:
        case C.Cir.Cell{+a, b0, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{x1e, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
              +c2 = cl.f1(m, sx, sv, x2)
              +r2 = is.f1(t1, ds, m, im, fi, nx, ks, img, sx, sv, x2, C.Cir.Cells.get(m, x2), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x2), w) : C.Cir.Cell}, c2),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x2), w) : C.Cir.Cell}, c2), {==}, h2)
              +c3 = cl.f1(m, sx, sv, x3)
              +r3 = is.f1(t2, ds, m, im, fi, nx, ks, img, sx, sv, x3, C.Cir.Cells.get(m, x3), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x3), w) : C.Cir.Cell}, c3),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x3), w) : C.Cir.Cell}, c3), {==}, h3)
              (Equal.trans(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c)), a, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)),
            Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, ew),
            Equal.sym(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), a, Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(m, c), C.Cir.Cell{a, b0, x2, x3, x4}, ey))),
                isc.at(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, C.Term.App{qq, t1, t2}, ew, (nd, (x1e, ((sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2), C.Cir.Cells.get(m, x2), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x2)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x2, t1), r2), sp2), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x2)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x2, t1), r2)), (sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3), C.Cir.Cells.get(m, x3), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x3)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x3, t2), r3), sp3), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x3)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x3, t2), r3)))))))
    case C.Term.Sig{+qq, +t1, +t2}:
      match y:
        case C.Cir.Cell{+a, b0, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{x1e, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
              +c2 = cl.f1(m, sx, sv, x2)
              +r2 = is.f1(t1, ds, m, im, fi, nx, ks, img, sx, sv, x2, C.Cir.Cells.get(m, x2), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x2), w) : C.Cir.Cell}, c2),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x2), w) : C.Cir.Cell}, c2), {==}, h2)
              +c3 = cl.f1(m, sx, sv, x3)
              +r3 = is.f1(t2, ds, m, im, fi, nx, ks, img, sx, sv, x3, C.Cir.Cells.get(m, x3), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x3), w) : C.Cir.Cell}, c3),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x3), w) : C.Cir.Cell}, c3), {==}, h3)
              (Equal.trans(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c)), a, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)),
            Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, ew),
            Equal.sym(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), a, Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(m, c), C.Cir.Cell{a, b0, x2, x3, x4}, ey))),
                isc.at(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, C.Term.Sig{qq, t1, t2}, ew, (nd, (x1e, ((sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2), C.Cir.Cells.get(m, x2), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x2)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x2, t1), r2), sp2), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x2)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x2, t1), r2)), (sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3), C.Cir.Cells.get(m, x3), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x3)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x3, t2), r3), sp3), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x3)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x3, t2), r3)))))))
    case C.Term.Tup{+qq, +t1, +t2}:
      match y:
        case C.Cir.Cell{+a, b0, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{x1e, Tuple{Tuple{sp2, h2}, Tuple{sp3, h3}}}}:
              +c2 = cl.f1(m, sx, sv, x2)
              +r2 = is.f1(t1, ds, m, im, fi, nx, ks, img, sx, sv, x2, C.Cir.Cells.get(m, x2), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x2), w) : C.Cir.Cell}, c2),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x2), w) : C.Cir.Cell}, c2), {==}, h2)
              +c3 = cl.f1(m, sx, sv, x3)
              +r3 = is.f1(t2, ds, m, im, fi, nx, ks, img, sx, sv, x3, C.Cir.Cells.get(m, x3), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x3), w) : C.Cir.Cell}, c3),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x3), w) : C.Cir.Cell}, c3), {==}, h3)
              (Equal.trans(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c)), a, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)),
            Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, ew),
            Equal.sym(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), a, Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(m, c), C.Cir.Cell{a, b0, x2, x3, x4}, ey))),
                isc.at(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, C.Term.Tup{qq, t1, t2}, ew, (nd, (x1e, ((sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2), C.Cir.Cells.get(m, x2), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x2)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x2, t1), r2), sp2), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x2)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x2, t1), r2)), (sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3), C.Cir.Cells.get(m, x3), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x3)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x3, t2), r3), sp3), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x3)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x3, t2), r3)))))))
    case C.Term.Prj{+t1}:
      match y:
        case C.Cir.Cell{+a, b0, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{sp2, h2}}:
              +c2 = cl.f1(m, sx, sv, x2)
              +r2 = is.f1(t1, ds, m, im, fi, nx, ks, img, sx, sv, x2, C.Cir.Cells.get(m, x2), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x2), w) : C.Cir.Cell}, c2),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x2), w) : C.Cir.Cell}, c2), {==}, h2)
              (Equal.trans(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c)), a, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)),
            Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, ew),
            Equal.sym(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), a, Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(m, c), C.Cir.Cell{a, b0, x2, x3, x4}, ey))),
                isc.at(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, C.Term.Prj{t1}, ew, (nd, (sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2), C.Cir.Cells.get(m, x2), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x2)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x2, t1), r2), sp2), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x2)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x2, t1), r2)))))
    case C.Term.Enu{+ee}:
      match y:
        case C.Cir.Cell{+a, b0, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{x1e, x2e}}:
              (Equal.trans(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c)), a, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)),
            Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, ew),
            Equal.sym(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), a, Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(m, c), C.Cir.Cell{a, b0, x2, x3, x4}, ey))),
                isc.at(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, C.Term.Enu{ee}, ew, (nd, (x1e, x2e))))
    case C.Term.Lab{+kk}:
      match y:
        case C.Cir.Cell{+a, b0, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, x1e}:
              (Equal.trans(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c)), a, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)),
            Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, ew),
            Equal.sym(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), a, Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(m, c), C.Cir.Cell{a, b0, x2, x3, x4}, ey))),
                isc.at(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, C.Term.Lab{kk}, ew, (nd, x1e)))
    case C.Term.Mat{+kk, +t1, +t2}:
      match y:
        case C.Cir.Cell{+a, b0, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{x1e, Tuple{Tuple{sp3, h3}, Tuple{sp4, h4}}}}:
              +c3 = cl.f1(m, sx, sv, x3)
              +r3 = is.f1(t1, ds, m, im, fi, nx, ks, img, sx, sv, x3, C.Cir.Cells.get(m, x3), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x3), w) : C.Cir.Cell}, c3),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x3), w) : C.Cir.Cell}, c3), {==}, h3)
              +c4 = cl.f1(m, sx, sv, x4)
              +r4 = is.f1(t2, ds, m, im, fi, nx, ks, img, sx, sv, x4, C.Cir.Cells.get(m, x4), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x4) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x4), w) : C.Cir.Cell}, c4),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x4) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x4), w) : C.Cir.Cell}, c4), {==}, h4)
              (Equal.trans(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c)), a, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)),
            Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, ew),
            Equal.sym(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), a, Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(m, c), C.Cir.Cell{a, b0, x2, x3, x4}, ey))),
                isc.at(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, C.Term.Mat{kk, t1, t2}, ew, (nd, (x1e, ((sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3), C.Cir.Cells.get(m, x3), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x3)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x3, t1), r3), sp3), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x3)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x3, t1), r3)), (sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x4), C.Cir.Cells.get(m, x4), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x4)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x4)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x4, t2), r4), sp4), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x4)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x4)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x4, t2), r4)))))))
    case C.Term.Efq{}:
      match y:
        case C.Cir.Cell{+a, b0, +x2, +x3, +x4}:
          (Equal.trans(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c)), a, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)),
            Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, ew),
            Equal.sym(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), a, Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(m, c), C.Cir.Cell{a, b0, x2, x3, x4}, ey))),
            isc.at(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, C.Term.Efq{}, ew, h))
    case C.Term.Eql{+t1, +t2, +t3}:
      match y:
        case C.Cir.Cell{+a, b0, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{Tuple{sp2, h2}, Tuple{Tuple{sp3, h3}, Tuple{sp4, h4}}}}:
              +c2 = cl.f1(m, sx, sv, x2)
              +r2 = is.f1(t1, ds, m, im, fi, nx, ks, img, sx, sv, x2, C.Cir.Cells.get(m, x2), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x2), w) : C.Cir.Cell}, c2),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x2), w) : C.Cir.Cell}, c2), {==}, h2)
              +c3 = cl.f1(m, sx, sv, x3)
              +r3 = is.f1(t2, ds, m, im, fi, nx, ks, img, sx, sv, x3, C.Cir.Cells.get(m, x3), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x3), w) : C.Cir.Cell}, c3),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x3), w) : C.Cir.Cell}, c3), {==}, h3)
              +c4 = cl.f1(m, sx, sv, x4)
              +r4 = is.f1(t3, ds, m, im, fi, nx, ks, img, sx, sv, x4, C.Cir.Cells.get(m, x4), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x4) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x4), w) : C.Cir.Cell}, c4),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x4) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x4), w) : C.Cir.Cell}, c4), {==}, h4)
              (Equal.trans(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c)), a, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)),
            Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, ew),
            Equal.sym(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), a, Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(m, c), C.Cir.Cell{a, b0, x2, x3, x4}, ey))),
                isc.at(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, C.Term.Eql{t1, t2, t3}, ew, (nd, ((sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2), C.Cir.Cells.get(m, x2), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x2)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x2, t1), r2), sp2), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x2)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x2, t1), r2)), ((sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3), C.Cir.Cells.get(m, x3), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x3)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x3, t2), r3), sp3), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x3)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x3, t2), r3)), (sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x4), C.Cir.Cells.get(m, x4), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x4)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x4)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x4, t3), r4), sp4), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x4)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x4)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x4, t3), r4)))))))
    case C.Term.Rfl{}:
      match y:
        case C.Cir.Cell{+a, b0, +x2, +x3, +x4}:
          (Equal.trans(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c)), a, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)),
            Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, ew),
            Equal.sym(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), a, Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(m, c), C.Cir.Cell{a, b0, x2, x3, x4}, ey))),
            isc.at(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, C.Term.Rfl{}, ew, h))
    case C.Term.Rwt{+t1, +t2, +t3}:
      match y:
        case C.Cir.Cell{+a, b0, +x2, +x3, +x4}:
          match h:
            case Tuple{nd, Tuple{Tuple{sp2, h2}, Tuple{Tuple{sp3, h3}, Tuple{sp4, h4}}}}:
              +c2 = cl.f1(m, sx, sv, x2)
              +r2 = is.f1(t1, ds, m, im, fi, nx, ks, img, sx, sv, x2, C.Cir.Cells.get(m, x2), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x2), w) : C.Cir.Cell}, c2),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x2), w) : C.Cir.Cell}, c2), {==}, h2)
              +c3 = cl.f1(m, sx, sv, x3)
              +r3 = is.f1(t2, ds, m, im, fi, nx, ks, img, sx, sv, x3, C.Cir.Cells.get(m, x3), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x3), w) : C.Cir.Cell}, c3),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x3), w) : C.Cir.Cell}, c3), {==}, h3)
              +c4 = cl.f1(m, sx, sv, x4)
              +r4 = is.f1(t3, ds, m, im, fi, nx, ks, img, sx, sv, x4, C.Cir.Cells.get(m, x4), Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x4) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x4), w) : C.Cir.Cell}, c4),
                Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x4) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, x4), w) : C.Cir.Cell}, c4), {==}, h4)
              (Equal.trans(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c)), a, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)),
            Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, ew),
            Equal.sym(U32, C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)), a, Equal.cong(C.Cir.Cell, U32, z => C.Cir.Cell.get(0n, z), C.Cir.Cells.get(m, c), C.Cir.Cell{a, b0, x2, x3, x4}, ey))),
                isc.at(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c), C.Cir.Cell{a, w, x2, x3, x4}, C.Term.Rwt{t1, t2, t3}, ew, (nd, ((sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2), C.Cir.Cells.get(m, x2), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x2)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x2, t1), r2), sp2), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x2)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x2)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x2, t1), r2)), ((sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3), C.Cir.Cells.get(m, x3), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x3)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x3, t2), r3), sp3), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x3)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x3)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x3, t2), r3)), (sp.at0(fi, nx, c, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x4), C.Cir.Cells.get(m, x4), Ex.fst({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x4)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x4)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x4, t3), r4), sp4), Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), x4)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, x4)) : U32}, _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, x4, t3), r4)))))))

# a store to field 1 keeps every term
def is.f1.top(+t: C.Term, +ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +sx: U32, +sv: U32, +c: U32, h: Is(ds, m, im, fi, nx, ks, img, c, t)) ->
  Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, c, t):
  +r = cl.f1(m, sx, sv, c)
  +q = is.f1(t, ds, m, im, fi, nx, ks, img, sx, sv, c, C.Cir.Cells.get(m, c),
    Ex.fst(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, c), w) : C.Cir.Cell}, r),
    Ex.snd(U32, w => {C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c) == C.Cir.Cell.set(1n, C.Cir.Cells.get(m, c), w) : C.Cir.Cell}, r), {==}, h)
  Ex.snd({C.Cir.Cell.get(0n, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), c)) == C.Cir.Cell.get(0n, C.Cir.Cells.get(m, c)) : U32},
    _ => Is(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, c, t), q)

def ne.fr.k(kind: FK, -fr: U32, -sx: U32, h: {U32.is_lt(FK.tag(kind), 32) == True{} : Bool}) ->
  {U32.is_eq(fr, sx) == False{} : Bool}:
  match kind:
    case FK.arg{}:
      bool.ft({U32.is_eq(fr, sx) == False{} : Bool}, h)
    case FK.val{}:
      bool.ft({U32.is_eq(fr, sx) == False{} : Bool}, h)
    case FK.fun{}:
      bool.ft({U32.is_eq(fr, sx) == False{} : Bool}, h)
    case FK.let{}:
      bool.ft({U32.is_eq(fr, sx) == False{} : Bool}, h)
    case FK.tupb{}:
      bool.ft({U32.is_eq(fr, sx) == False{} : Bool}, h)
    case FK.tupa{}:
      bool.ft({U32.is_eq(fr, sx) == False{} : Bool}, h)
    case FK.rwt{}:
      bool.ft({U32.is_eq(fr, sx) == False{} : Bool}, h)
    case FK.minb{}:
      bool.ft({U32.is_eq(fr, sx) == False{} : Bool}, h)
    case FK.mina{}:
      bool.ft({U32.is_eq(fr, sx) == False{} : Bool}, h)

# the frames from fr, with the top cell's value x (Frs, by its parts)
def FrsC(+ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +ps: List<&2, U32>, +fr: U32, +x: C.Cir.Cell, fs: List<&2, AF>) -> Data:
  match fs:
    case Nil{}:
      {fr == 0 : U32}
    case Con{AF{+kind, +q, +k, +a, +b}, rest}:
      P2({U32.is_eq(fr, 0) == False{} : Bool},
      P2({C.Cir.is_cell(fr, im, fi, nx) == True{} : Bool},
      P2({Own(fi, nx, fr) == True{} : Bool},
      P2({FlW(C.Cir.Cell.get(0n, x), 1024) == False{} : Bool},
      P2({Mem(ps, fr) == False{} : Bool},
      P2({TgW(C.Cir.Cell.get(0n, x)) == FK.tag(kind) : U32},
      P2(Qs(x, q),
      P2({FlW(C.Cir.Cell.get(0n, x), 2048) == k : Bool},
      P2(Is(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), a),
      P2(Frs.b(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(3n, x), kind, b),
        Frs(ds, m, im, fi, nx, ks, img, ps, C.Cir.Cell.get(1n, x), rest)))))))))))

def frsc.at(+ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +ps: List<&2, U32>, +fr: U32, -y1: C.Cir.Cell, -y2: C.Cir.Cell, -fs: List<&2, AF>,
  e: {y1 == y2 : C.Cir.Cell}, h: FrsC(ds, m, im, fi, nx, ks, img, ps, fr, y2, fs)) -> FrsC(ds, m, im, fi, nx, ks, img, ps, fr, y1, fs):
  %Equal.sym(C.Cir.Cell, y1, y2, e) : FrsC(ds, m, im, fi, nx, ks, img, ps, fr, _, fs)
  h

# a frame's cell (of a tag of 32 or more) is not the cell sx (of a tag below 32)
def ne.fr(b: Bool, +m: C.Cir.Cells, +fr: U32, +sx: U32, kind: FK, eb: {U32.is_eq(fr, sx) == b : Bool},
  etag: {Tg(m, fr) == FK.tag(kind) : U32}, hsx: {U32.is_lt(TgW(Fd(0n, m, sx)), 32) == True{} : Bool}) ->
  {U32.is_eq(fr, sx) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +e = u32.eq(fr, sx, eb)
      +h2 = {(%Equal.sym(U32, fr, sx, e) : {U32.is_lt(TgW(Fd(0n, m, _)), 32) == True{} : Bool}; hsx) : {U32.is_lt(TgW(Fd(0n, m, fr)), 32) == True{} : Bool}}
      ne.fr.k(kind, fr, sx, Equal.trans(Bool, U32.is_lt(FK.tag(kind), 32), U32.is_lt(Tg(m, fr), 32), True{},
        Equal.cong(U32, Bool, z => U32.is_lt(z, 32), FK.tag(kind), Tg(m, fr), Equal.sym(U32, Tg(m, fr), FK.tag(kind), etag)), h2))

def frs.c(+ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +ps: List<&2, U32>, +fr: U32, fs: List<&2, AF>, h: Frs(ds, m, im, fi, nx, ks, img, ps, fr, fs)) ->
  FrsC(ds, m, im, fi, nx, ks, img, ps, fr, C.Cir.Cells.get(m, fr), fs):
  match fs:
    case Nil{}:
      h
    case Con{AF{kind, q, k, a, b}, rest}:
      h

def frs.uc(+ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +ps: List<&2, U32>, +fr: U32, fs: List<&2, AF>, h: FrsC(ds, m, im, fi, nx, ks, img, ps, fr, C.Cir.Cells.get(m, fr), fs)) ->
  Frs(ds, m, im, fi, nx, ks, img, ps, fr, fs):
  match fs:
    case Nil{}:
      h
    case Con{AF{kind, q, k, a, b}, rest}:
      h

def frsb.f1(kind: FK, +ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +sx: U32, +sv: U32, +c: U32, +b: C.Term, h: Frs.b(ds, m, im, fi, nx, ks, img, c, kind, b)) ->
  Frs.b(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, c, kind, b):
  match kind:
    case FK.rwt{}:
      is.f1.top(b, ds, m, im, fi, nx, ks, img, sx, sv, c, h)
    case FK.arg{}:
      Unit{}
    case FK.val{}:
      Unit{}
    case FK.fun{}:
      Unit{}
    case FK.let{}:
      Unit{}
    case FK.tupb{}:
      Unit{}
    case FK.tupa{}:
      Unit{}
    case FK.minb{}:
      Unit{}
    case FK.mina{}:
      Unit{}

# a store to field 1 of a cell of a tag below 32 keeps the frames
def frs.f1(fs: List<&2, AF>, +ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +ps: List<&2, U32>, +sx: U32, +sv: U32, +fr: U32,
  +hsx: {U32.is_lt(TgW(Fd(0n, m, sx)), 32) == True{} : Bool}, h: Frs(ds, m, im, fi, nx, ks, img, ps, fr, fs)) ->
  Frs(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, ps, fr, fs):
  match fs:
    case Nil{}:
      h
    case Con{AF{+kind, +q, +k, +a, +b}, +rest}:
      match h:
        case Tuple{e0, Tuple{ev, Tuple{eo, Tuple{es, Tuple{em, Tuple{+etg, Tuple{eq, Tuple{ek, Tuple{ia, Tuple{ib, ir}}}}}}}}}}:
          +ne = ne.fr(U32.is_eq(fr, sx), m, fr, sx, kind, {==}, etg, hsx)
          +ec = cl.go(m, fr, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv), ne)
          frs.uc(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, ps, fr, Con{AF{kind, q, k, a, b}, rest},
            frsc.at(ds, C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), im, fi, nx, ks, img, ps, fr, C.Cir.Cells.get(C.Cir.Cells.set(m, sx, C.Cir.Cell.set(1n, C.Cir.Cells.get(m, sx), sv)), fr), C.Cir.Cells.get(m, fr),
              Con{AF{kind, q, k, a, b}, rest}, ec,
              (e0, (ev, (eo, (es, (em, (etg, (eq, (ek,
                (is.f1.top(a, ds, m, im, fi, nx, ks, img, sx, sv, Fd(2n, m, fr), ia),
                (frsb.f1(kind, ds, m, im, fi, nx, ks, img, sx, sv, Fd(3n, m, fr), b, ib),
                 frs.f1(rest, ds, m, im, fi, nx, ks, img, ps, sx, sv, Fd(1n, m, fr), hsx, ir)))))))))))))

# Move kit
# --------
#
# The run of a move's statements as equations of their outcomes (eq.*, and
# rw.* in the orientation that a rewrite of the goal takes: the new outcome
# first), the values of expressions (ev.*), and the parts of Is (is.nd) and of
# the table (tbl.at).

# the state with the register r set to v, or with field k of the cell i set to x
def St.set(st: C.Cir.State, +r: Nat, +v: U32) -> C.Cir.State:
  match st:
    case C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}:
      C.Cir.State{List.set(&2, U32, regs, r, v), m, nx, fi, im, pg, lim, inp, out, outn}

def eq.set(+f: Nat, +r: Nat, e: C.Cir.Expr, st: C.Cir.State, +v: U32,
  ev: {C.Cir.eval(e, st) == Some{v} : Maybe<&2, U32>},
  hl: {Nat.is_lt(r, List.length(&2, U32, St.regs(st))) == True{} : Bool}) ->
  {C.Cir.exec(f, C.Cir.Stmt.set{r, e}, st) == C.Cir.Out.next{St.set(st, r, v)} : C.Cir.Out}:
  match f st:
    case 0n C.Cir.State{+regs, +m, +nx, +fi, +im, +pg, +lim, +inp, +out, +outn}:
      %Equal.sym(Maybe<&2, U32>, C.Cir.eval(e, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}), Some{v}, ev) :
        {C.Cir.exec.set(r, _, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}) ==
          C.Cir.Out.next{C.Cir.State{List.set(&2, U32, regs, r, v), m, nx, fi, im, pg, lim, inp, out, outn}} : C.Cir.Out}
      %Equal.sym(Bool, Nat.is_lt(r, List.length(&2, U32, regs)), True{}, hl) :
        {C.Cir.exec.set.of(C.Cir.regs.set.if(_, regs, r, v), C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}) ==
          C.Cir.Out.next{C.Cir.State{List.set(&2, U32, regs, r, v), m, nx, fi, im, pg, lim, inp, out, outn}} : C.Cir.Out}
      {==}
    case 1n+g C.Cir.State{+regs, +m, +nx, +fi, +im, +pg, +lim, +inp, +out, +outn}:
      %Equal.sym(Maybe<&2, U32>, C.Cir.eval(e, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}), Some{v}, ev) :
        {C.Cir.exec.set(r, _, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}) ==
          C.Cir.Out.next{C.Cir.State{List.set(&2, U32, regs, r, v), m, nx, fi, im, pg, lim, inp, out, outn}} : C.Cir.Out}
      %Equal.sym(Bool, Nat.is_lt(r, List.length(&2, U32, regs)), True{}, hl) :
        {C.Cir.exec.set.of(C.Cir.regs.set.if(_, regs, r, v), C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}) ==
          C.Cir.Out.next{C.Cir.State{List.set(&2, U32, regs, r, v), m, nx, fi, im, pg, lim, inp, out, outn}} : C.Cir.Out}
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

# an if whose condition is not 0, and one whose condition is 0
def eq.if.t(+f: Nat, c: C.Cir.Expr, +t: C.Cir.Stmt, +e: C.Cir.Stmt, +st: C.Cir.State, -v: U32,
  ev: {C.Cir.eval(c, st) == Some{v} : Maybe<&2, U32>}, nz: {U32.is_zero(v) == False{} : Bool}) ->
  {C.Cir.exec(f, C.Cir.Stmt.if{c, t, e}, st) == C.Cir.exec(f, t, st) : C.Cir.Out}:
  match f:
    case 0n:
      %Equal.sym(Maybe<&2, U32>, C.Cir.eval(c, st), Some{v}, ev) :
        {C.Cir.exec.if(_, u => C.Cir.exec(0n, t, st), u => C.Cir.exec(0n, e, st)) == C.Cir.exec(0n, t, st) : C.Cir.Out}
      %Equal.sym(Bool, U32.is_zero(v), False{}, nz) :
        {C.Cir.exec.if.of(_, u => C.Cir.exec(0n, t, st), u => C.Cir.exec(0n, e, st)) == C.Cir.exec(0n, t, st) : C.Cir.Out}
      {==}
    case 1n+g:
      %Equal.sym(Maybe<&2, U32>, C.Cir.eval(c, st), Some{v}, ev) :
        {C.Cir.exec.if(_, u => C.Cir.exec(1n+g, t, st), u => C.Cir.exec(1n+g, e, st)) == C.Cir.exec(1n+g, t, st) : C.Cir.Out}
      %Equal.sym(Bool, U32.is_zero(v), False{}, nz) :
        {C.Cir.exec.if.of(_, u => C.Cir.exec(1n+g, t, st), u => C.Cir.exec(1n+g, e, st)) == C.Cir.exec(1n+g, t, st) : C.Cir.Out}
      {==}

def eq.if.e(+f: Nat, c: C.Cir.Expr, +t: C.Cir.Stmt, +e: C.Cir.Stmt, +st: C.Cir.State, -v: U32,
  ev: {C.Cir.eval(c, st) == Some{v} : Maybe<&2, U32>}, z: {U32.is_zero(v) == True{} : Bool}) ->
  {C.Cir.exec(f, C.Cir.Stmt.if{c, t, e}, st) == C.Cir.exec(f, e, st) : C.Cir.Out}:
  match f:
    case 0n:
      %Equal.sym(Maybe<&2, U32>, C.Cir.eval(c, st), Some{v}, ev) :
        {C.Cir.exec.if(_, u => C.Cir.exec(0n, t, st), u => C.Cir.exec(0n, e, st)) == C.Cir.exec(0n, e, st) : C.Cir.Out}
      %Equal.sym(Bool, U32.is_zero(v), True{}, z) :
        {C.Cir.exec.if.of(_, u => C.Cir.exec(0n, t, st), u => C.Cir.exec(0n, e, st)) == C.Cir.exec(0n, e, st) : C.Cir.Out}
      {==}
    case 1n+g:
      %Equal.sym(Maybe<&2, U32>, C.Cir.eval(c, st), Some{v}, ev) :
        {C.Cir.exec.if(_, u => C.Cir.exec(1n+g, t, st), u => C.Cir.exec(1n+g, e, st)) == C.Cir.exec(1n+g, e, st) : C.Cir.Out}
      %Equal.sym(Bool, U32.is_zero(v), True{}, z) :
        {C.Cir.exec.if.of(_, u => C.Cir.exec(1n+g, t, st), u => C.Cir.exec(1n+g, e, st)) == C.Cir.exec(1n+g, e, st) : C.Cir.Out}
      {==}

def eq.nop(+f: Nat, +st: C.Cir.State) -> {C.Cir.exec(f, C.Cir.Stmt.nop{}, st) == C.Cir.Out.next{st} : C.Cir.Out}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

# the value of an operation, from its operands'
def ev.op(o: C.Wasm.Op, a: C.Cir.Expr, b: C.Cir.Expr, +st: C.Cir.State, -x: U32, -y: U32,
  ea: {C.Cir.eval(a, st) == Some{x} : Maybe<&2, U32>}, eb: {C.Cir.eval(b, st) == Some{y} : Maybe<&2, U32>}) ->
  {C.Cir.eval(C.Cir.Expr.op{o, a, b}, st) == Some{C.Wasm.op(o, x, y)} : Maybe<&2, U32>}:
  %Equal.sym(Maybe<&2, U32>, C.Cir.eval(a, st), Some{x}, ea) :
    {C.Cir.eval.op(o, _, C.Cir.eval(b, st)) == Some{C.Wasm.op(o, x, y)} : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, C.Cir.eval(b, st), Some{y}, eb) :
    {C.Cir.eval.op(o, Some{x}, _) == Some{C.Wasm.op(o, x, y)} : Maybe<&2, U32>}
  {==}

# the value of a field of a cell
def ev.fld(+k: Nat, c: C.Cir.Expr, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32,
  +lim: U32, +inp: List<&2, U32>, +out: List<&2, U32>, +outn: U32, +i: U32,
  ec: {C.Cir.eval(c, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}) == Some{i} : Maybe<&2, U32>},
  hv: {C.Cir.is_cell(i, im, fi, nx) == True{} : Bool}) ->
  {C.Cir.eval(C.Cir.Expr.field{k, c}, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}) ==
    Some{C.Cir.Cell.get(k, C.Cir.Cells.get(m, i))} : Maybe<&2, U32>}:
  %Equal.sym(Maybe<&2, U32>, C.Cir.eval(c, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}), Some{i}, ec) :
    {C.Cir.eval.field(k, _, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}) ==
      Some{C.Cir.Cell.get(k, C.Cir.Cells.get(m, i))} : Maybe<&2, U32>}
  %Equal.sym(Bool, C.Cir.is_cell(i, im, fi, nx), True{}, hv) :
    {C.Cir.eval.field.if(_, k, m, i) == Some{C.Cir.Cell.get(k, C.Cir.Cells.get(m, i))} : Maybe<&2, U32>}
  {==}

# 1 or'ed with a Bool is not 0
def or1(b: Bool) -> {U32.is_zero(U32.or(1, Bool.to_u32(b))) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the tag of a term's cell
def A.tag(t: C.Term) -> U32:
  match t:

    case C.Term.Var{_}:
      0
    case C.Term.Ref{_}:
      1
    case C.Term.Ann{_, _}:
      2
    case C.Term.Let{_, _, _}:
      3
    case C.Term.Typ{_}:
      4
    case C.Term.Min{_, _}:
      5
    case C.Term.All{_, _, _}:
      6
    case C.Term.Lam{_, _}:
      7
    case C.Term.App{_, _, _}:
      8
    case C.Term.Sig{_, _, _}:
      9
    case C.Term.Tup{_, _, _}:
      10
    case C.Term.Prj{_}:
      11
    case C.Term.Enu{_}:
      12
    case C.Term.Lab{_}:
      13
    case C.Term.Mat{_, _, _}:
      14
    case C.Term.Efq{}:
      15
    case C.Term.Eql{_, _, _}:
      16
    case C.Term.Rfl{}:
      17
    case C.Term.Rwt{_, _, _}:
      18

# what the cell of a term says of itself
def is.nd(+ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +c: U32, t: C.Term, h: Is(ds, m, im, fi, nx, ks, img, c, t)) ->
  Nd(ds, im, fi, nx, c, C.Cir.Cells.get(m, c), t, A.tag(t)):
  match t:
    case C.Term.Var{+i}:
      match h:
        case Tuple{n, _}:
          n
    case C.Term.Ref{+k}:
      match h:
        case Tuple{n, _}:
          n
    case C.Term.Ann{+x, +y}:
      match h:
        case Tuple{n, _}:
          n
    case C.Term.Let{+q, +v, +b}:
      match h:
        case Tuple{n, _}:
          n
    case C.Term.Typ{+x}:
      match h:
        case Tuple{n, _}:
          n
    case C.Term.Min{+a, +b}:
      match h:
        case Tuple{n, _}:
          n
    case C.Term.All{+q, +a, +b}:
      match h:
        case Tuple{n, _}:
          n
    case C.Term.Lam{+q, +b}:
      match h:
        case Tuple{n, _}:
          n
    case C.Term.App{+q, +g, +x}:
      match h:
        case Tuple{n, _}:
          n
    case C.Term.Sig{+q, +a, +b}:
      match h:
        case Tuple{n, _}:
          n
    case C.Term.Tup{+q, +a, +b}:
      match h:
        case Tuple{n, _}:
          n
    case C.Term.Prj{+hh}:
      match h:
        case Tuple{n, _}:
          n
    case C.Term.Enu{+e}:
      match h:
        case Tuple{n, _}:
          n
    case C.Term.Lab{+k}:
      match h:
        case Tuple{n, _}:
          n
    case C.Term.Mat{+k, +hh, +n}:
      match h:
        case Tuple{n, _}:
          n
    case C.Term.Efq{}:
      h
    case C.Term.Eql{+a, +b, +y}:
      match h:
        case Tuple{n, _}:
          n
    case C.Term.Rfl{}:
      h
    case C.Term.Rwt{+e, +p, +b}:
      match h:
        case Tuple{n, _}:
          n

# the table's cell for the tag of t is a cell (I.table)
def tbl.at(-m: C.Cir.Cells, -im: U32, -fi: U32, -nx: U32, t: C.Term, h: Tbl(m, im, fi, nx)) ->
  {C.Cir.is_cell(U32.add(345, A.tag(t)), im, fi, nx) == True{} : Bool}:
  match t:
    case C.Term.Var{_}:
      match h:
        case Tuple{e, _}:
          e
    case C.Term.Ref{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}:
          e
    case C.Term.Ann{_, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}:
          e
    case C.Term.Let{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}:
          e
    case C.Term.Typ{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Min{_, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.All{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Lam{_, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.App{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Sig{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Tup{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Prj{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Enu{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Lab{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Mat{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Efq{}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Eql{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Rfl{}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e
    case C.Term.Rwt{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          e

def nat.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# a term has a node or more
def size.pos(t: C.Term) -> {C.Term.size(t) == 1n+nat.pred(C.Term.size(t)) : Nat}:
  match t:
    case C.Term.Var{_}:
      {==}
    case C.Term.Ref{_}:
      {==}
    case C.Term.Ann{_, _}:
      {==}
    case C.Term.Let{_, _, _}:
      {==}
    case C.Term.Typ{_}:
      {==}
    case C.Term.Min{_, _}:
      {==}
    case C.Term.All{_, _, _}:
      {==}
    case C.Term.Lam{_, _}:
      {==}
    case C.Term.App{_, _, _}:
      {==}
    case C.Term.Sig{_, _, _}:
      {==}
    case C.Term.Tup{_, _, _}:
      {==}
    case C.Term.Prj{_}:
      {==}
    case C.Term.Enu{_}:
      {==}
    case C.Term.Lab{_}:
      {==}
    case C.Term.Mat{_, _, _}:
      {==}
    case C.Term.Efq{}:
      {==}
    case C.Term.Eql{_, _, _}:
      {==}
    case C.Term.Rfl{}:
      {==}
    case C.Term.Rwt{_, _, _}:
      {==}

# the measure of a term to evaluate is at least 1
def A.w3.pos(+t: C.Term) -> N.Le(1n, A.w3(t)):
  %Equal.sym(Nat, C.Term.size(t), 1n+nat.pred(C.Term.size(t)), size.pos(t)) : N.Le(1n, Nat.add(_, Nat.add(_, _)))
  N.le_zero(Nat.add(nat.pred(C.Term.size(t)), Nat.add(1n+nat.pred(C.Term.size(t)), 1n+nat.pred(C.Term.size(t)))))

# The run
# -------
#
# Cir.result runs the program from St0, once it has room for the cells and
# the input (Start says what it computed), or runs out of memory first.

# the state from which Cir.result runs the program
def St0(+regs: Nat, cells: List<&2, C.Cir.Cell>, +first: U32, +k: U32, +p: U32, +lim: U32, i: List<&2, U32>) ->
  C.Cir.State:
  C.Cir.State{List.replicate(U32, regs, 0), C.Cir.load(cells, 1, C.Cir.Cells.none{}), first, first, k, p, lim, i, Nil{}, 0}

# what Cir.result computed for the start: the image's k cells, its room for
# them, the input's len bytes, the limit lim of the pages, the p pages after
# alloc, and the first cell after the input
def Start(cells: List<&2, C.Cir.Cell>, +i: List<&2, U32>, +m: U32, +k: U32, +len: U32, +p: U32, +lim: U32,
  +first: U32) -> Data:
  P2({k == C.Wasm.encode.len(C.Cir.Cell, cells) : U32},
  P2({U32.is_le(C.Cir.pages(C.Cir.input.at(k)), m) == True{} : Bool},
  P2({lim == C.Wasm.min(m, 65536) : U32},
  P2({C.Wasm.length32(i) == Some{len} : Maybe<&2, U32>},
  P2({C.Cir.alloc.pages(k, len, C.Cir.pages(C.Cir.input.at(k)), lim) == Some{p} : Maybe<&2, U32>},
    {first == C.Cir.first(k, U32.add(C.Cir.input.at(k), len)) : U32})))))

# The start
# ---------

# the state with the mode 0
def Mode0(st: C.Cir.State) -> C.Cir.State:
  match st:
    case C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}:
      C.Cir.State{List.set(&2, U32, regs, 1n, 0), m, nx, fi, im, pg, lim, inp, out, outn}

def regs.set1(+regs: List<&2, U32>, e: {List.length(&2, U32, regs) == 64n : Nat}) ->
  {C.Cir.regs.set(regs, 1n, 0) == Some{List.set(&2, U32, regs, 1n, 0)} : Maybe<&2, List<&2, U32>>}:
  %Equal.sym(Nat, List.length(&2, U32, regs), 64n, e) :
    {C.Cir.regs.set.if(Nat.is_lt(1n, _), regs, 1n, 0) == Some{List.set(&2, U32, regs, 1n, 0)} : Maybe<&2, List<&2, U32>>}
  {==}

# Mach.code's M.set(R.mode(), M.c(0)), after M.input
def setmode(+f: Nat, st: C.Cir.State, e: {List.length(&2, U32, St.regs(st)) == 64n : Nat}) ->
  {C.Cir.exec(f, C.M.set(C.R.mode(), C.M.c(0)), st) == C.Cir.Out.next{Mode0(st)} : C.Cir.Out}:
  match f st:
    case 0n C.Cir.State{+regs, +m, +nx, +fi, +im, +pg, +lim, +inp, +out, +outn}:
      %Equal.sym(Maybe<&2, List<&2, U32>>, C.Cir.regs.set(regs, 1n, 0), Some{List.set(&2, U32, regs, 1n, 0)}, regs.set1(regs, e)) : {C.Cir.exec.set.of(_, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}) ==
        C.Cir.Out.next{C.Cir.State{List.set(&2, U32, regs, 1n, 0), m, nx, fi, im, pg, lim, inp, out, outn}} : C.Cir.Out}
      {==}
    case 1n+p C.Cir.State{+regs, +m, +nx, +fi, +im, +pg, +lim, +inp, +out, +outn}:
      %Equal.sym(Maybe<&2, List<&2, U32>>, C.Cir.regs.set(regs, 1n, 0), Some{List.set(&2, U32, regs, 1n, 0)}, regs.set1(regs, e)) : {C.Cir.exec.set.of(_, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}) ==
        C.Cir.Out.next{C.Cir.State{List.set(&2, U32, regs, 1n, 0), m, nx, fi, im, pg, lim, inp, out, outn}} : C.Cir.Out}
      {==}

# after M.input: ten registers or more, and once the mode is 0, the invariant
# of Program.start(i), with the image's names and terms (proof_term.bend)
def InvIn(+ds: List<&2, C.Def>, +i: List<&2, U32>, +st: C.Cir.State) -> Data:
  P2({List.length(&2, U32, St.regs(st)) == 64n : Nat},
    Ex(Nat, w => Inv(ds, T.tm.names(ds), T.tm.img(ds), Mode0(st), C.Program.start(i), w)))
# the conclusion of input.post (proof_mach.bend), for the phase that proves it
def InputPost(+f: Nat, +p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +k: U32, +len: U32,
  +pg: U32, +lim: U32, +first: U32,
  rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  small: {C.Img.small(p, 0) == True{} : Bool},
  s: Start(C.Img.cells(ds), i, m, k, len, pg, lim, first)) ->
  Type:
  Post(False{}, C.Cir.exec(f, C.M.input(), St0(C.Mach.regs(), C.Img.cells(ds), first, k, pg, lim, i)),
    st => InvIn(ds, i, st), s2 => st2 => Empty)

# the conclusion of input.done (proof_mach.bend), for the phase that proves it
def InputDone(+p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +k: U32, +len: U32,
  +pg: U32, +lim: U32, +first: U32,
  rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  small: {C.Img.small(p, 0) == True{} : Bool},
  s: Start(C.Img.cells(ds), i, m, k, len, pg, lim, first)) ->
  Data:
  Ex(Nat, f => Ends(C.Cir.exec(f, C.M.input(), St0(C.Mach.regs(), C.Img.cells(ds), first, k, pg, lim, i))))


# Memory (mach.memory)
# --------------------
#
# With the memory of INVARIANTS #4 the machine never runs out of memory, so
# mach.complete's out-of-memory case cannot occur. What it needs:
#
#   1. a round takes a new cell (Cir alloc) only when the pend list is
#      empty, and the cells of the machine's own (next - first) stay within
#      Peak(t) of the term t of the round's state, or of an earlier one
#      (round.peak): the live cells are the nodes of t, each at most once
#      (a copy shares what it does not reach), and its frames, at most
#      2 × |t|; a move takes at most |t| more for a while (a copy's new
#      cells, M.data's checks, a walk's locals and arguments); about 2.5 ×
#      S in all, which Peak rounds up to 3 × |t| + 2^16 (the cache of the
#      input's bytes: 256 × 26 cells);
#   2. the bytes: the image's k cells, k <= 363 + |p| / 2 (img.small's
#      count), the input's |i| bytes after them, then 20 × Peak bytes of
#      cells, then the output's bytes, |o| <= S: in all at most
#      20 × (364 + |p| / 2) + |i| + 20 × (3 × S + 2^16) + |o|, which is at
#      most 64 × (|p| + S) + 2^24 = Program.need (|i| <= S, as the input is
#      in the first term); so Cir.result's alloc, every Cir alloc
#      (Cir.room) and every emit find their pages (round.room), and
#      next < 214748364 since need <= 2^32;
#   3. then loop.done's out-of-memory cases are empty, and its Good is a
#      halt with 0 (mach.memory.proof, from the parts of mach.complete).

def St.lim(st: C.Cir.State) -> U32:
  match st:
    case C.Cir.State{_, _, _, _, _, _, lim, _, _, _}:
      lim

def St.first(st: C.Cir.State) -> U32:
  match st:
    case C.Cir.State{_, _, _, fi, _, _, _, _, _, _}:
      fi

# the machine's own cells of a state
def Mem.cells(+st: C.Cir.State) -> Nat:
  Nat.sub(U32.to_nat(St.next(st)), U32.to_nat(St.first(st)))

# the most cells of the machine's own that a round from the term t needs
def Peak(t: C.Term) -> Nat:
  Nat.add(Nat.mul(3n, C.Term.size(t)), N.D(16n, 1n))

# the run does not run out of memory
def NoOom(o: C.Cir.Out) -> Data:
  match o:
    case C.Cir.Out.out_of_memory{}:
      Empty
    case _:
      Unit
