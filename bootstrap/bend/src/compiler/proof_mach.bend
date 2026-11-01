# compiler: layer B, the machine
# ==============================
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

# what the cell c, of the value x, of the term t says of itself: it is a
# cell; one of the machine's own, or STATIC; its tag; VALUE says t is a value,
# DATA that it is Data; fv bounds its free variables, unless it is fv_max
def Nd(+ds: List<&2, C.Def>, +im: U32, +fi: U32, +nx: U32, +c: U32, +x: C.Cir.Cell, +t: C.Term, +tag: U32) -> Data:
  +f0 = C.Cir.Cell.get(0n, x)
  P2({C.Cir.is_cell(c, im, fi, nx) == True{} : Bool},
  P2({Bool.or(Own(fi, nx, c), FlW(f0, 1024)) == True{} : Bool},
  P2({TgW(f0) == tag : U32},
  P2({Bool.or(Bool.not(FlW(f0, 256)), C.Eval.vals(ds, t, False{})) == True{} : Bool},
  P2({Bool.or(Bool.not(FlW(f0, 512)), C.Term.is_data(t)) == True{} : Bool},
    {Bool.or(U32.is_eq(FvW(f0), 524287), Term.below(t, U32.to_nat(FvW(f0)))) == True{} : Bool})))))

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
def IsC(+ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +c: U32, +x: C.Cir.Cell, t: C.Term) -> Data:
  match t:
    case C.Term.Var{+i}:
      P2(Nd(ds, im, fi, nx, c, x, C.Term.Var{i}, 0), {U32.to_nat(C.Cir.Cell.get(2n, x)) == i : Nat})
    case C.Term.Ref{+k}:
      P2(Nd(ds, im, fi, nx, c, x, C.Term.Ref{k}, 1),
      P2({T.tm.image(img, c) == Some{C.Term.Ref{k}} : Maybe<&2, C.Term>},
      P2({FvW(C.Cir.Cell.get(0n, x)) == 0 : U32},
        {C.Cir.Cell.get(2n, x) == C.Img.ref(C.Img.defs(ds, C.I.book()), k) : U32})))
    case C.Term.Ann{+y, +z}:
      P2(Nd(ds, im, fi, nx, c, x, C.Term.Ann{y, z}, 2),
      P2(P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x)), y)), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(3n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x)), z))))
    case C.Term.Let{+q, +v, +f}:
      P2(Nd(ds, im, fi, nx, c, x, C.Term.Let{q, v, f}, 3), P2(Qs(x, q),
      P2(P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x)), v)), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(3n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x)), f)))))
    case C.Term.Typ{+y}:
      P2(Nd(ds, im, fi, nx, c, x, C.Term.Typ{y}, 4), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x)), y)))
    case C.Term.Min{+a, +b}:
      P2(Nd(ds, im, fi, nx, c, x, C.Term.Min{a, b}, 5),
      P2(P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x)), a)), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(3n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x)), b))))
    case C.Term.All{+q, +a, +b}:
      P2(Nd(ds, im, fi, nx, c, x, C.Term.All{q, a, b}, 6), P2(Qs(x, q),
      P2(P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x)), a)), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(3n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x)), b)))))
    case C.Term.Lam{+q, +f}:
      P2(Nd(ds, im, fi, nx, c, x, C.Term.Lam{q, f}, 7), P2(Qs(x, q), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x)), f))))
    case C.Term.App{+q, +f, +y}:
      P2(Nd(ds, im, fi, nx, c, x, C.Term.App{q, f, y}, 8), P2(Qs(x, q),
      P2(P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x)), f)), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(3n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x)), y)))))
    case C.Term.Sig{+q, +a, +b}:
      P2(Nd(ds, im, fi, nx, c, x, C.Term.Sig{q, a, b}, 9), P2(Qs(x, q),
      P2(P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x)), a)), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(3n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x)), b)))))
    case C.Term.Tup{+q, +a, +b}:
      P2(Nd(ds, im, fi, nx, c, x, C.Term.Tup{q, a, b}, 10), P2(Qs(x, q),
      P2(P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x)), a)), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(3n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x)), b)))))
    case C.Term.Prj{+h}:
      P2(Nd(ds, im, fi, nx, c, x, C.Term.Prj{h}, 11), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x)), h)))
    case C.Term.Enu{+e}:
      P2(Nd(ds, im, fi, nx, c, x, C.Term.Enu{e}, 12),
      P2({T.tm.image(img, c) == Some{C.Term.Enu{e}} : Maybe<&2, C.Term>}, {FvW(C.Cir.Cell.get(0n, x)) == 0 : U32}))
    case C.Term.Lab{+k}:
      P2(Nd(ds, im, fi, nx, c, x, C.Term.Lab{k}, 13), Nm(ks, x, k))
    case C.Term.Mat{+k, +h, +n}:
      P2(Nd(ds, im, fi, nx, c, x, C.Term.Mat{k, h, n}, 14), P2(Nm(ks, x, k),
      P2(P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(3n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x)), h)), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(4n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(4n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(4n, x)), n)))))
    case C.Term.Efq{}:
      Nd(ds, im, fi, nx, c, x, C.Term.Efq{}, 15)
    case C.Term.Eql{+a, +b, +y}:
      P2(Nd(ds, im, fi, nx, c, x, C.Term.Eql{a, b, y}, 16),
      P2(P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x)), a)),
      P2(P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(3n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x)), b)), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(4n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(4n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(4n, x)), y)))))
    case C.Term.Rfl{}:
      Nd(ds, im, fi, nx, c, x, C.Term.Rfl{}, 17)
    case C.Term.Rwt{+e, +p, +f}:
      P2(Nd(ds, im, fi, nx, c, x, C.Term.Rwt{e, p, f}, 18),
      P2(P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(2n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(2n, x)), e)),
      P2(P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(3n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(3n, x)), p)), P2(Sp(fi, nx, c, C.Cir.Cells.get(m, C.Cir.Cell.get(4n, x))), IsC(ds, m, im, fi, nx, ks, img, C.Cir.Cell.get(4n, x), C.Cir.Cells.get(m, C.Cir.Cell.get(4n, x)), f)))))

# the cell c of the cells m stands for the term t
def Is(+ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +c: U32, t: C.Term) -> Data:
  IsC(ds, m, im, fi, nx, ks, img, c, C.Cir.Cells.get(m, c), t)

def Mem(xs: List<&2, U32>, +c: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, rest}:
      Bool.or(U32.is_eq(x, c), Mem(rest, c))

# the part b of a frame: in field 3, for Rwt only
def Frs.b(+ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +c: U32, kind: FK, b: C.Term) -> Data:
  match kind:
    case FK.rwt{}:
      Is(ds, m, im, fi, nx, ks, img, c, b)
    case _:
      Unit

# the frames from the cell fr on, linked by field 1, the innermost first: each
# one of the machine's own cells, not STATIC, not in the pend list ps, of its
# kind's tag, its quantity and its flag K, with its parts standing for a and,
# for Rwt, b; 0 after the last
def Frs(+ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
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
      P2(Is(ds, m, im, fi, nx, ks, img, Fd(2n, m, fr), a),
      P2(Frs.b(ds, m, im, fi, nx, ks, img, Fd(3n, m, fr), kind, b),
        Frs(ds, m, im, fi, nx, ks, img, ps, Fd(1n, m, fr), rest)))))))))))

# Counts and the pend list
# ------------------------
#
# The heap of the machine, shared by every phase (M.input, the moves,
# M.copy, M.data, M.walk, M.out). A cell holds pointers (Fs): a term cell its
# parts, by its tag's mask (the image's table), in or out of the pend list (a
# cell of the pend list drops them when it is reused); a frame (tags 32 to
# 40) its field 2, and field 3 for Rwt, and an argument that owns its term
# (K.arg, OWNED) its field 2, while out of the pend list. The roots rs are the
# registers that own a pointer. Counts are exact (Cnt): each term cell of the
# machine's, not STATIC and out of the pend list, counts its pointers, from
# the cells (Pc) and the roots. So the pend list's cells, which count none
# (PendOK), are no part of a term that anything holds, and a count is at most
# 3 × the machine's cells + the roots: with next <= 214748364 (Room) that is
# below 2^30, so M.inc never wraps (ptr.bound). A pointer is below next (Pts),
# so a new cell has none.

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
  Bool.pick(List<&2, U32>, U32.is_lt(tg, 32),
    Fs.term(Fd(2n, m, U32.add(345, tg)), Fd(2n, m, o), Fd(3n, m, o), Fd(4n, m, o)),
    Bool.pick(List<&2, U32>, Bool.and(U32.is_le(tg, 40), Bool.not(Mem(ps, o))),
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
        Bool.or(U32.is_ge(Tg(m, c), 32), Bool.or(Fl(m, c, 1024), Bool.or(Mem(ps, c),
          Nat.is_eq(U32.to_nat(Fd(1n, m, c)), Ptr(N, m, fi, ps, rs, c))))),
        Cnt(p, m, U32.inc(c), N, fi, ps, rs))

# each pointer of xs is below nx, to a term cell (a tag below 32)
def Lt.all(xs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Bool.and(U32.is_lt(x, nx), U32.is_lt(Tg(m, x), 32)), Lt.all(rest, m, nx))

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
# STATIC, and nothing points to it
def PendOK(qs: List<&2, U32>, +ps: List<&2, U32>, +m: C.Cir.Cells, +fi: U32, +nx: U32, +rs: List<&2, U32>) -> Data:
  match qs:
    case Nil{}:
      Unit
    case Con{+p, rest}:
      P2({Own(fi, nx, p) == True{} : Bool},
      P2({Fl(m, p, 1024) == False{} : Bool},
      P2({Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, p) == 0n : Nat},
        PendOK(rest, ps, m, fi, nx, rs))))

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

# the bodies of the defs dl, from the cell at on, as Img.defs places them
def Defs(dl: List<&2, C.Def>, +ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +at: U32) -> Data:
  match dl:
    case Nil{}:
      Unit
    case Con{C.Def{_, _, +v, _}, rest}:
      P2({U32.is_eq(at, 0) == False{} : Bool},
      P2(Is(ds, m, im, fi, nx, ks, img, at, v),
        Defs(rest, ds, m, im, fi, nx, ks, img, U32.add(at, C.Img.size(v)))))

def ImgOK(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +m: C.Cir.Cells, +im: U32,
  +fi: U32, +nx: U32) -> Data:
  P2(Tbl(m, im, fi, nx),
  P2(Defs(ds, ds, m, im, fi, nx, ks, img, C.I.book()),
  P2(Is(ds, m, im, fi, nx, ks, img, 9, C.Term.Lab{C.Quan.name(C.Quan.Q0{})}),
  P2(Is(ds, m, im, fi, nx, ks, img, 10, C.Term.Lab{C.Quan.name(C.Quan.Q1{})}),
  P2(Is(ds, m, im, fi, nx, ks, img, 11, C.Term.Lab{C.Quan.name(C.Quan.Q2{})}),
  P2(Ex(List<&2, List<&2, U32>>, ks2 => {ks == C.Img.known(ks2) : List<&2, List<&2, U32>>}),
  P2({U32.is_le(363, im) == True{} : Bool}, {U32.is_lt(im, fi) == True{} : Bool})))))))

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
# by Ptr), the borrowed terms bs (cells STATIC or out of the pend list, that a
# root or a frame holds), the frames, the pend list and the image. The
# premises of the moves on M.copy, M.data, M.walk and M.out below are stated
# with it.

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
def Rts(+ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, rs: List<&2, Rt>) -> Data:
  match rs:
    case Nil{}:
      Unit
    case Con{Rt{+c, +u}, rest}:
      P2(Is(ds, m, im, fi, nx, ks, img, c, u), Rts(ds, m, im, fi, nx, ks, img, rest))

# each cell of bs is STATIC or something points to it (a root of rs, or a
# cell of the machine's n from fi): so it is out of the pend list
def Held(+m: C.Cir.Cells, +n: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, bs: List<&2, Rt>) -> Data:
  match bs:
    case Nil{}:
      Unit
    case Con{Rt{+c, _}, rest}:
      P2({Bool.or(Fl(m, c, 1024), Nat.is_lt(0n, Ptr(n, m, fi, ps, rs, c))) == True{} : Bool}, Held(m, n, fi, ps, rs, rest))

def HS(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +m: C.Cir.Cells, +nx: U32,
  +fi: U32, +im: U32, +os: List<&2, Rt>, +bs: List<&2, Rt>, +fs: List<&2, AF>, +sp: U32, +pend: U32,
  +ps: List<&2, U32>) -> Data:
  P2(Rts(ds, m, im, fi, nx, ks, img, os),
  P2(Rts(ds, m, im, fi, nx, ks, img, bs),
  P2(Held(m, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, ps, Rt.cells(os), bs),
  P2(Frs(ds, m, im, fi, nx, ks, img, ps, sp, fs),
  P2(Heap(m, nx, fi, Rt.cells(os), pend, ps),
    ImgOK(ds, ks, img, m, im, fi, nx))))))

# the chain of K.arg cells from a, linked by field 1, that hold the terms of xs
# in field 2, at their quantities: the machine's own cells, out of the pend
# list, each term's cell STATIC or out of it too (M.walk's arguments and
# locals; M.copy's locals, with any quantity)
def Ag(+ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +ps: List<&2, U32>, +a: U32, xs: List<&2, C.Arg>) -> Data:
  match xs:
    case Nil{}:
      {a == 0 : U32}
    case Con{C.Arg{+q, +x}, rest}:
      P2({U32.is_eq(a, 0) == False{} : Bool},
      P2({C.Cir.is_cell(a, im, fi, nx) == True{} : Bool},
      P2({Own(fi, nx, a) == True{} : Bool},
      P2({Mem(ps, a) == False{} : Bool},
      P2({Tg(m, a) == 41 : U32},
      P2(Qs(C.Cir.Cells.get(m, a), q),
      P2({Bool.or(Bool.not(Fl(m, a, 2048)), C.Eval.vals(ds, x, False{})) == True{} : Bool},
      P2(Is(ds, m, im, fi, nx, ks, img, Fd(2n, m, a), x),
      P2({Bool.or(Fl(m, Fd(2n, m, a), 1024), Bool.not(Mem(ps, Fd(2n, m, a)))) == True{} : Bool},
        Ag(ds, m, im, fi, nx, ks, img, ps, Fd(1n, m, a), rest))))))))))

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
      Ag(ds, m2, im, fi, nx2, ks, img, ps2, ce, es))))))))

def copy.post(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, +src: Nat,
  +keep: List<&2, Nat>, +os: List<&2, Rt>, +bs: List<&2, Rt>, +fs: List<&2, AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +c: U32, +t: C.Term, +ce: U32, +es: List<&2, C.Arg>,
  hs: HS(ds, ks, img, m, nx, fi, im, os, Con{Rt{c, t}, bs}, fs, sp, pend, ps),
  hl: {List.length(&2, U32, regs) == 64n : Nat},
  hc: {List.get(&2, U32, regs, src) == Some{c} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  he: {List.get(&2, U32, regs, 36n) == Some{ce} : Maybe<&2, U32>},
  hn: {List.get(&2, U32, regs, 37n) == Some{U32.from_nat(List.length(&2, C.Arg, es))} : Maybe<&2, U32>},
  env: Ag(ds, m, im, fi, nx, ks, img, ps, ce, es),
  hk: {Disj(keep, Copy.scr(r)) == True{} : Bool}) ->
  Post(False{}, C.Cir.exec(f, C.M.copy(r, src), C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
    st2 => CopyQ(ds, ks, img, regs, fi, im, lim, inp, r, keep, os, Con{Rt{c, t}, bs}, fs, sp, t, ce, es, st2),
    s => st2 => Empty):
  ?TODO

def copy.done(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat, +src: Nat,
  +os: List<&2, Rt>, +bs: List<&2, Rt>, +fs: List<&2, AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +c: U32, +t: C.Term, +ce: U32, +es: List<&2, C.Arg>,
  hs: HS(ds, ks, img, m, nx, fi, im, os, Con{Rt{c, t}, bs}, fs, sp, pend, ps),
  hl: {List.length(&2, U32, regs) == 64n : Nat},
  hc: {List.get(&2, U32, regs, src) == Some{c} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  he: {List.get(&2, U32, regs, 36n) == Some{ce} : Maybe<&2, U32>},
  hn: {List.get(&2, U32, regs, 37n) == Some{U32.from_nat(List.length(&2, C.Arg, es))} : Maybe<&2, U32>},
  env: Ag(ds, m, im, fi, nx, ks, img, ps, ce, es)) ->
  Ex(Nat, f => Ends(C.Cir.exec(f, C.M.copy(r, src), C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}))):
  ?TODO

# Open: M.data (proof_walk.bend)
# ------------------------------
#
# From a state of HS, with the cell c of v (in register r) among its terms,
# M.data(r) sets register dok to 1 when Term.is_data(v), else to 0; when it is
# 1, HS holds again (the flags DATA that it set are true); when it is 0 the
# run halts with 2, and nothing more is needed. Only Data.scr()'s registers
# change. With some fuel it ends.

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

def data.post(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat,
  +keep: List<&2, Nat>, +os: List<&2, Rt>, +bs: List<&2, Rt>, +fs: List<&2, AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +c: U32, +v: C.Term,
  hs: HS(ds, ks, img, m, nx, fi, im, os, Con{Rt{c, v}, bs}, fs, sp, pend, ps),
  hl: {List.length(&2, U32, regs) == 64n : Nat},
  hc: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  hk: {Disj(keep, Data.scr()) == True{} : Bool}) ->
  Post(False{}, C.Cir.exec(f, C.M.data(r), C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
    st2 => DataQ(ds, ks, img, regs, fi, im, lim, inp, keep, os, Con{Rt{c, v}, bs}, fs, sp, v, st2), s => st2 => Empty):
  ?TODO

def data.done(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +r: Nat,
  +os: List<&2, Rt>, +bs: List<&2, Rt>, +fs: List<&2, AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +c: U32, +v: C.Term,
  hs: HS(ds, ks, img, m, nx, fi, im, os, Con{Rt{c, v}, bs}, fs, sp, pend, ps),
  hl: {List.length(&2, U32, regs) == 64n : Nat},
  hc: {List.get(&2, U32, regs, r) == Some{c} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  Ex(Nat, f => Ends(C.Cir.exec(f, C.M.data(r), C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}))):
  ?TODO

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
# again, and only Walk.scr()'s registers change. With some fuel it ends.

def WalkR(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +m2: C.Cir.Cells, +nx2: U32,
  +fi: U32, +im: U32, +ps2: List<&2, U32>, +tt: C.Term, +xs: List<&2, C.Arg>, +res: U32, +wt2: U32, +env: U32,
  +wn: U32, +args: U32) -> Type:
  Or(P2({res == 1 : U32}, Ex(C.Term, u => Ex(List<&2, C.Arg>, e => Ex(List<&2, C.Arg>, ys =>
      P2({C.Eval.walk(tt, Nil{}, xs) == Some{Some{C.Term.spine(ys, C.Term.subst(u, Arg.terms(e), 0n))}} : Maybe<Maybe<C.Term>>},
      P2(Is(ds, m2, im, fi, nx2, ks, img, wt2, u),
      P2({Fl(m2, wt2, 1024) == True{} : Bool},
      P2({wn == U32.from_nat(List.length(&2, C.Arg, e))  : U32},
      P2(Ag(ds, m2, im, fi, nx2, ks, img, ps2, env, e), Ag(ds, m2, im, fi, nx2, ks, img, ps2, args, ys)))))))))),
  Or(P2({res == 2 : U32}, P2({C.Eval.walk(tt, Nil{}, xs) == Some{None{}} : Maybe<Maybe<C.Term>>},
      Ex(List<&2, C.Arg>, e => Ex(List<&2, C.Arg>, ys =>
        P2(Ag(ds, m2, im, fi, nx2, ks, img, ps2, env, e), Ag(ds, m2, im, fi, nx2, ks, img, ps2, args, ys)))))),
    P2({res == 3 : U32}, {C.Eval.walk(tt, Nil{}, xs) == None{} : Maybe<Maybe<C.Term>>})))

def WalkQ(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +fi: U32, +im: U32, +lim: U32, +inp: List<&2, U32>, +keep: List<&2, Nat>, +os: List<&2, Rt>, +bs: List<&2, Rt>,
  +fs: List<&2, AF>, +sp: U32, +tt: C.Term, +xs: List<&2, C.Arg>, +st2: C.Cir.State) -> Type:
  +m2 = St.cells(st2)
  +nx2 = St.next(st2)
  Same(regs, fi, im, lim, inp, keep, st2) &
  &res: U32 -> &wt2: U32 -> &env: U32 -> &wn: U32 -> &args: U32 -> &pend2: U32 -> &ps2: List<&2, U32> ->
    Reg(st2, 26n, res) & Reg(st2, 19n, wt2) & Reg(st2, 20n, env) & Reg(st2, 25n, wn) & Reg(st2, 21n, args) &
    Reg(st2, 3n, pend2) & HS(ds, ks, img, m2, nx2, fi, im, os, bs, fs, sp, pend2, ps2) &
    WalkR(ds, ks, img, m2, nx2, fi, im, ps2, tt, xs, res, wt2, env, wn, args)

def walk.post(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>,
  +keep: List<&2, Nat>, +os: List<&2, Rt>, +bs: List<&2, Rt>, +fs: List<&2, AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +tc: U32, +tt: C.Term, +a: U32, +xs: List<&2, C.Arg>,
  hs: HS(ds, ks, img, m, nx, fi, im, os, Con{Rt{tc, tt}, bs}, fs, sp, pend, ps),
  hst: {Fl(m, tc, 1024) == True{} : Bool},
  hl: {List.length(&2, U32, regs) == 64n : Nat},
  ht: {List.get(&2, U32, regs, 19n) == Some{tc} : Maybe<&2, U32>},
  ha: {List.get(&2, U32, regs, 21n) == Some{a} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  args: Ag(ds, m, im, fi, nx, ks, img, ps, a, xs),
  hk: {Disj(keep, Walk.scr()) == True{} : Bool}) ->
  Post(False{}, C.Cir.exec(f, C.M.walk(), C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}),
    st2 => WalkQ(ds, ks, img, regs, fi, im, lim, inp, keep, os, Con{Rt{tc, tt}, bs}, fs, sp, tt, xs, st2), s => st2 => Empty):
  ?TODO

def walk.done(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>,
  +os: List<&2, Rt>, +bs: List<&2, Rt>, +fs: List<&2, AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>,
  +tc: U32, +tt: C.Term, +a: U32, +xs: List<&2, C.Arg>,
  hs: HS(ds, ks, img, m, nx, fi, im, os, Con{Rt{tc, tt}, bs}, fs, sp, pend, ps),
  hst: {Fl(m, tc, 1024) == True{} : Bool},
  hl: {List.length(&2, U32, regs) == 64n : Nat},
  ht: {List.get(&2, U32, regs, 19n) == Some{tc} : Maybe<&2, U32>},
  ha: {List.get(&2, U32, regs, 21n) == Some{a} : Maybe<&2, U32>},
  hp: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  args: Ag(ds, m, im, fi, nx, ks, img, ps, a, xs)) ->
  Ex(Nat, f => Ends(C.Cir.exec(f, C.M.walk(), C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}))):
  ?TODO

# Open: M.out (proof_out.bend)
# ----------------------------
#
# In mode 1 with no frame, from the focus' cell of the value v, M.out halts
# with 0 and the bytes of Program.unbytes(v) (the output, the last first), or
# with 2 when it is none; it may run out of memory. With some fuel it ends.

def OutH(+v: C.Term, +s: U32, st2: C.Cir.State) -> Data:
  Either<&2, &2, P2({s == 0 : U32}, {C.Program.unbytes(v) == Some{List.reverse(&2, U32, St.out(st2))} : Maybe<&2, List<&2, U32>>}),
    P2({s == 2 : U32}, {C.Program.unbytes(v) == None{} : Maybe<&2, List<&2, U32>>})>

def out.post(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32,
  +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>,
  +v: C.Term, +ks2: List<&2, List<&2, U32>>,
  hv: Is(ds, m, im, fi, nx, ks, img, foc, v),
  hk: {ks == C.Img.known(ks2) : List<&2, List<&2, U32>>}) ->
  Post(False{}, C.Cir.exec(f, C.M.out(), S(foc, 1, 0, pend, rest, m, nx, fi, im, pg, lim, inp)), st => Empty,
    s => st2 => OutH(v, s, st2)):
  ?TODO

def out.done(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32,
  +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>,
  +v: C.Term, +ks2: List<&2, List<&2, U32>>,
  hv: Is(ds, m, im, fi, nx, ks, img, foc, v),
  hk: {ks == C.Img.known(ks2) : List<&2, List<&2, U32>>}) ->
  Ex(Nat, f => Ends(C.Cir.exec(f, C.M.out(), S(foc, 1, 0, pend, rest, m, nx, fi, im, pg, lim, inp)))):
  ?TODO

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

# Open lemmas
# -----------
#
# Each is a premise of the proofs below, in the shape that they use; a body
# ?TODO is still open.

# Eval: a value has no step (Lean's eval_value)
def ev.stops(+ds: List<&2, C.Def>, +t: C.Term, h: {C.Eval.vals(ds, t, False{}) == True{} : Bool}) ->
  {C.Eval.step(ds, t) == None{} : Maybe<C.Term>}:
  ?TODO

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

# a term with a step is no value
def vals.of(b: Bool, +ds: List<&2, C.Def>, +t: C.Term, -u: C.Term, eb: {C.Eval.vals(ds, t, False{}) == b : Bool},
  es: {C.Eval.step(ds, t) == Some{u} : Maybe<C.Term>}) -> {C.Eval.vals(ds, t, False{}) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      Empty.absurd({C.Eval.vals(ds, t, False{}) == False{} : Bool},
        st.ne(u, Equal.trans(Maybe<C.Term>, None{}, C.Eval.step(ds, t), Some{u},
          Equal.sym(Maybe<C.Term>, C.Eval.step(ds, t), None{}, ev.stops(ds, t, eb)), es)))

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
        case WCon{a, +s} WCon{b, +t}:
          match a b:
            case True{} True{}:
              Equal.cong(Word(p), Word(1n+p), x => WCon{True{}, x}, s, t, weq.eq(p, s, t, h))
            case False{} False{}:
              Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x}, s, t, weq.eq(p, s, t, h))
            case True{} False{}:
              bool.ft({WCon{True{}, s} == WCon{False{}, t} : Word(1n+p)}, h)
            case False{} True{}:
              bool.ft({WCon{False{}, s} == WCon{True{}, t} : Word(1n+p)}, h)

def weq.refl(n: Nat, w: Word(n)) -> {Weq(n, w, w) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{a, s}:
          match a:
            case True{}:
              weq.refl(p, s)
            case False{}:
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
        case WCon{b, t}:
          match b:
            case True{}:
              {==}
            case False{}:
              {==}

def cl.gs.at(n: Nat, +w: Word(n), +m: C.Cir.Cells, +c: C.Cir.Cell) ->
  {C.Cir.Cells.get.at(n, w, C.Cir.Cells.set.at(n, w, m, c)) == c : C.Cir.Cell}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, +t}:
          match b m:
            case False{} C.Cir.Cells.node{+lo, +hi}:
              cl.gs.at(p, t, lo, c)
            case True{} C.Cir.Cells.node{+lo, +hi}:
              cl.gs.at(p, t, hi, c)
            case False{} C.Cir.Cells.none{}:
              cl.gs.at(p, t, C.Cir.Cells.none{}, c)
            case True{} C.Cir.Cells.none{}:
              cl.gs.at(p, t, C.Cir.Cells.none{}, c)
            case False{} C.Cir.Cells.one{d}:
              cl.gs.at(p, t, C.Cir.Cells.none{}, c)
            case True{} C.Cir.Cells.one{d}:
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
      match v w:
        case WCon{a, +s} WCon{b, +t}:
          match a b m:
            case False{} False{} C.Cir.Cells.node{+lo, +hi}:
              cl.go.at(p, s, t, lo, c, h)
            case False{} False{} C.Cir.Cells.none{}:
              Equal.trans(C.Cir.Cell, C.Cir.Cells.get.at(p, s, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, c)), C.Cir.Cells.get.at(p, s, C.Cir.Cells.none{}), C.Cir.Cell.zero(),
                cl.go.at(p, s, t, C.Cir.Cells.none{}, c, h), cl.none(p, s))
            case False{} False{} C.Cir.Cells.one{+d}:
              Equal.trans(C.Cir.Cell, C.Cir.Cells.get.at(p, s, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, c)), C.Cir.Cells.get.at(p, s, C.Cir.Cells.none{}), C.Cir.Cell.zero(),
                cl.go.at(p, s, t, C.Cir.Cells.none{}, c, h), cl.none(p, s))
            case False{} True{} C.Cir.Cells.node{+lo, +hi}:
              {==}
            case False{} True{} C.Cir.Cells.none{}:
              cl.none(p, s)
            case False{} True{} C.Cir.Cells.one{+d}:
              cl.none(p, s)
            case True{} False{} C.Cir.Cells.node{+lo, +hi}:
              {==}
            case True{} False{} C.Cir.Cells.none{}:
              cl.none(p, s)
            case True{} False{} C.Cir.Cells.one{+d}:
              cl.none(p, s)
            case True{} True{} C.Cir.Cells.node{+lo, +hi}:
              cl.go.at(p, s, t, hi, c, h)
            case True{} True{} C.Cir.Cells.none{}:
              Equal.trans(C.Cir.Cell, C.Cir.Cells.get.at(p, s, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, c)), C.Cir.Cells.get.at(p, s, C.Cir.Cells.none{}), C.Cir.Cell.zero(),
                cl.go.at(p, s, t, C.Cir.Cells.none{}, c, h), cl.none(p, s))
            case True{} True{} C.Cir.Cells.one{+d}:
              Equal.trans(C.Cir.Cell, C.Cir.Cells.get.at(p, s, C.Cir.Cells.set.at(p, t, C.Cir.Cells.none{}, c)), C.Cir.Cells.get.at(p, s, C.Cir.Cells.none{}), C.Cir.Cell.zero(),
                cl.go.at(p, s, t, C.Cir.Cells.none{}, c, h), cl.none(p, s))

# a set keeps the other cells
def cl.go(+m: C.Cir.Cells, +j: U32, +i: U32, +c: C.Cir.Cell, h: {U32.is_eq(j, i) == False{} : Bool}) ->
  {C.Cir.Cells.get(C.Cir.Cells.set(m, i, c), j) == C.Cir.Cells.get(m, j) : C.Cir.Cell}:
  match j i:
    case U32{+v} U32{+w}:
      cl.go.at(32n, v, w, m, c, Equal.trans(Bool, Weq(32n, v, w), Cmp.is_eq(Word.cmp(32n, v, w)), False{},
        Equal.sym(Bool, Cmp.is_eq(Word.cmp(32n, v, w)), Weq(32n, v, w), weq.cmp(32n, v, w)), h))

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

# Inv's facts of that state, with the abstract state of ret, focus and fs
def IV(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +t: C.Term, +w: Nat, +ret: Bool, +focus: C.Term,
  +fs: List<&2, AF>, +ps: List<&2, U32>) -> Data:
  InvOf(ds, ks, img, RG(foc, Bool.to_u32(ret), sp, pend, R60.list(rest)), m, nx, fi, im, Nil{}, 0, t, w, ret, focus, fs, foc, sp,
    pend, ps, rest)

# a move from st: for any fuel, a round that goes on (Rnd) or halts as HR
# says; and a fuel with which it ends
def MV(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +st: C.Cir.State, +t: C.Term, +w: Nat) ->
  Type:
  (@f: Nat -> Post(False{}, C.Cir.exec(f, B.body(), st), s => Rnd(ds, ks, img, t, w, s), s => st2 => HR(ds, t, s, st2))) &
    Ex(Nat, f => Ends(C.Cir.exec(f, B.body(), st)))

def mv.post(+f: Nat, -ds: List<&2, C.Def>, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, -st: C.Cir.State,
  -t: C.Term, -w: Nat, h: MV(ds, ks, img, st, t, w)) ->
  Post(False{}, C.Cir.exec(f, B.body(), st), s => Rnd(ds, ks, img, t, w, s), s => st2 => HR(ds, t, s, st2)):
  match h:
    case Tuple{p, _}:
      p(f)

def mv.done(-ds: List<&2, C.Def>, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, -st: C.Cir.State, -t: C.Term,
  -w: Nat, h: MV(ds, ks, img, st, t, w)) -> Ex(Nat, f => Ends(C.Cir.exec(f, B.body(), st))):
  match h:
    case Tuple{_, d}:
      d

# a frame of App q □ x: app_arg or app_val
def FK.isapp(k: FK) -> Bool:
  match k:
    case FK.arg{}:
      True{}
    case FK.val{}:
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
def vt.of(-m: C.Cir.Cells, -im: U32, -fi: U32, -nx: U32, -f0: U32, +focus: C.Term, etag: {TgW(f0) == A.tag(focus) : U32},
  tb: Tbl(m, im, fi, nx)) -> {C.Cir.is_cell(U32.add(345, U32.and(f0, 63)), im, fi, nx) == True{} : Bool}:
  %Equal.sym(U32, TgW(f0), A.tag(focus), etag) : {C.Cir.is_cell(U32.add(345, _), im, fi, nx) == True{} : Bool}
  tbl.at(m, im, fi, nx, focus, tb)

# the test of M.ev on a cell flagged VALUE is not 0
def nz.of(-f0: U32, +e4: U32, hv: {U32.is_ne(U32.and(f0, 256), 0) == True{} : Bool}) ->
  {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)), Bool.to_u32(U32.is_ne(e4, 0)))) == False{} : Bool}:
  %Equal.sym(Bool, U32.is_ne(U32.and(f0, 256), 0), True{}, hv) :
    {U32.is_zero(U32.or(Bool.to_u32(_), Bool.to_u32(U32.is_ne(e4, 0)))) == False{} : Bool}
  or1(U32.is_ne(e4, 0))

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

def tbl.f4(-m: C.Cir.Cells, -im: U32, -fi: U32, -nx: U32, t: C.Term, h: Tbl(m, im, fi, nx)) ->
  {Fd(4n, m, U32.add(345, A.tag(t))) == A.f4(t) : U32}:
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
      bool.ft({A.f4(C.Term.Var{x0}) == 1 : U32}, hf)
    case C.Term.Ref{+x0}:
      bool.ft({A.f4(C.Term.Ref{x0}) == 1 : U32}, hf)
    case C.Term.Ann{+x0, +x1}:
      bool.ft({A.f4(C.Term.Ann{x0, x1}) == 1 : U32}, hf)
    case C.Term.Let{+x0, +x1, +x2}:
      bool.ft({A.f4(C.Term.Let{x0, x1, x2}) == 1 : U32}, hf)
    case C.Term.Typ{+x0}:
      {==}
    case C.Term.Min{+x0, +x1}:
      bool.ft({A.f4(C.Term.Min{x0, x1}) == 1 : U32}, hf)
    case C.Term.All{+x0, +x1, +x2}:
      {==}
    case C.Term.Lam{+x0, +x1}:
      {==}
    case C.Term.App{+x0, +x1, +x2}:
      bool.ft({A.f4(C.Term.App{x0, x1, x2}) == 1 : U32}, hf)
    case C.Term.Sig{+x0, +x1, +x2}:
      {==}
    case C.Term.Tup{+x0, +x1, +x2}:
      bool.ft({A.f4(C.Term.Tup{x0, x1, x2}) == 1 : U32}, hf)
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
      bool.ft({A.f4(C.Term.Rwt{x0, x1, x2}) == 1 : U32}, hf)

# a value by its form, as the table says, is a value
def tbl.vals(+ds: List<&2, C.Def>, t: C.Term, hf: {A.tbl(t) == True{} : Bool}) ->
  {Bool.or(Bool.not(True{}), C.Eval.vals(ds, t, False{})) == True{} : Bool}:
  match t:
    case C.Term.Var{+x0}:
      bool.ft({Bool.or(Bool.not(True{}), C.Eval.vals(ds, C.Term.Var{x0}, False{})) == True{} : Bool}, hf)
    case C.Term.Ref{+x0}:
      bool.ft({Bool.or(Bool.not(True{}), C.Eval.vals(ds, C.Term.Ref{x0}, False{})) == True{} : Bool}, hf)
    case C.Term.Ann{+x0, +x1}:
      bool.ft({Bool.or(Bool.not(True{}), C.Eval.vals(ds, C.Term.Ann{x0, x1}, False{})) == True{} : Bool}, hf)
    case C.Term.Let{+x0, +x1, +x2}:
      bool.ft({Bool.or(Bool.not(True{}), C.Eval.vals(ds, C.Term.Let{x0, x1, x2}, False{})) == True{} : Bool}, hf)
    case C.Term.Typ{+x0}:
      {==}
    case C.Term.Min{+x0, +x1}:
      bool.ft({Bool.or(Bool.not(True{}), C.Eval.vals(ds, C.Term.Min{x0, x1}, False{})) == True{} : Bool}, hf)
    case C.Term.All{+x0, +x1, +x2}:
      {==}
    case C.Term.Lam{+x0, +x1}:
      {==}
    case C.Term.App{+x0, +x1, +x2}:
      bool.ft({Bool.or(Bool.not(True{}), C.Eval.vals(ds, C.Term.App{x0, x1, x2}, False{})) == True{} : Bool}, hf)
    case C.Term.Sig{+x0, +x1, +x2}:
      {==}
    case C.Term.Tup{+x0, +x1, +x2}:
      bool.ft({Bool.or(Bool.not(True{}), C.Eval.vals(ds, C.Term.Tup{x0, x1, x2}, False{})) == True{} : Bool}, hf)
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
      bool.ft({Bool.or(Bool.not(True{}), C.Eval.vals(ds, C.Term.Rwt{x0, x1, x2}, False{})) == True{} : Bool}, hf)

def or1r(b: Bool) -> {U32.is_zero(U32.or(Bool.to_u32(b), 1)) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the test of M.ev on a value by its form is not 0
def nzf.of(-m: C.Cir.Cells, -im: U32, -fi: U32, -nx: U32, +f0: U32, +focus: C.Term, etag: {TgW(f0) == A.tag(focus) : U32},
  tb: Tbl(m, im, fi, nx), hf: {A.tbl(focus) == True{} : Bool}) ->
  {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)),
    Bool.to_u32(U32.is_ne(C.Cir.Cell.get(4n, C.Cir.Cells.get(m, U32.add(345, U32.and(f0, 63)))), 0)))) == False{} : Bool}:
  %Equal.sym(U32, TgW(f0), A.tag(focus), etag) :
    {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)),
      Bool.to_u32(U32.is_ne(C.Cir.Cell.get(4n, C.Cir.Cells.get(m, U32.add(345, _))), 0)))) == False{} : Bool}
  %Equal.sym(U32, Fd(4n, m, U32.add(345, A.tag(focus))), A.f4(focus), tbl.f4(m, im, fi, nx, focus, tb)) :
    {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)), Bool.to_u32(U32.is_ne(_, 0)))) == False{} : Bool}
  %Equal.sym(U32, A.f4(focus), 1, f4.one(focus, hf)) :
    {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)), Bool.to_u32(U32.is_ne(_, 0)))) == False{} : Bool}
  or1r(U32.is_ne(U32.and(f0, 256), 0))

# the test of M.ev on a value by its form, from the facts of its cell
def nzf.go(-ds: List<&2, C.Def>, -im: U32, -fi: U32, -nx: U32, +foc: U32, +m: C.Cir.Cells, +focus: C.Term,
  nd: Nd(ds, im, fi, nx, foc, C.Cir.Cells.get(m, foc), focus, A.tag(focus)), tb: Tbl(m, im, fi, nx),
  hf: {A.tbl(focus) == True{} : Bool}) ->
  {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(Fd(0n, m, foc), 256), 0)), Bool.to_u32(U32.is_ne(C.Cir.Cell.get(4n, C.Cir.Cells.get(m, U32.add(345, U32.and(Fd(0n, m, foc), 63)))), 0)))) == False{} : Bool}:
  match nd:
    case Tuple{_, Tuple{_, Tuple{etag, _}}}:
      nzf.of(m, im, fi, nx, Fd(0n, m, foc), focus, etag, tb, hf)

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
def tag.ne(+f0: U32, +tag: U32, +x: U32, etag: {TgW(f0) == tag : U32}, e: {U32.is_eq(tag, x) == False{} : Bool}) ->
  {U32.is_zero(C.Wasm.op(C.Wasm.Op.eq{}, TgW(f0), x)) == True{} : Bool}:
  %Equal.sym(U32, TgW(f0), tag, etag) : {U32.is_zero(C.Wasm.op(C.Wasm.Op.eq{}, _, x)) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(tag, x), False{}, e) : {U32.is_zero(Bool.to_u32(_)) == True{} : Bool}
  {==}

# the test of M.ev on a cell not flagged VALUE, whose tag's table field 4 is 0, is 0
def z.of(-m: C.Cir.Cells, -im: U32, -fi: U32, -nx: U32, +f0: U32, +focus: C.Term, etag: {TgW(f0) == A.tag(focus) : U32},
  tb: Tbl(m, im, fi, nx), hv: {U32.is_ne(U32.and(f0, 256), 0) == False{} : Bool}, h0: {A.f4(focus) == 0 : U32}) ->
  {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)),
    Bool.to_u32(U32.is_ne(C.Cir.Cell.get(4n, C.Cir.Cells.get(m, U32.add(345, U32.and(f0, 63)))), 0)))) == True{} : Bool}:
  %Equal.sym(U32, TgW(f0), A.tag(focus), etag) :
    {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)),
      Bool.to_u32(U32.is_ne(C.Cir.Cell.get(4n, C.Cir.Cells.get(m, U32.add(345, _))), 0)))) == True{} : Bool}
  %Equal.sym(U32, Fd(4n, m, U32.add(345, A.tag(focus))), A.f4(focus), tbl.f4(m, im, fi, nx, focus, tb)) :
    {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)), Bool.to_u32(U32.is_ne(_, 0)))) == True{} : Bool}
  %Equal.sym(U32, A.f4(focus), 0, h0) :
    {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(f0, 256), 0)), Bool.to_u32(U32.is_ne(_, 0)))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_ne(U32.and(f0, 256), 0), False{}, hv) :
    {U32.is_zero(U32.or(Bool.to_u32(_), Bool.to_u32(U32.is_ne(0, 0)))) == True{} : Bool}
  {==}

# Eval: a focus with no step that is no value makes its frames' term so
def ev.stuck(+ds: List<&2, C.Def>, fs: List<&2, AF>, +u: C.Term, hfs: AFs.ok(ds, fs),
  hs: {C.Eval.step(ds, u) == None{} : Maybe<C.Term>}, hv: {C.Eval.vals(ds, u, False{}) == False{} : Bool}) ->
  P2({C.Eval.step(ds, A.plugs(fs, u)) == None{} : Maybe<C.Term>}, {C.Eval.vals(ds, A.plugs(fs, u), False{}) == False{} : Bool}):
  ?TODO

# a halt of a round, from a term equal to t
def hr.eq(+ds: List<&2, C.Def>, -u: C.Term, -t: C.Term, -s: U32, -st: C.Cir.State, e: {u == t : C.Term},
  h: HR(ds, u, s, st)) -> HR(ds, t, s, st):
  %e : HR(ds, _, s, st)
  h

# a halt with 2 from a term that is stuck
def hr.stuck(+ds: List<&2, C.Def>, +t: C.Term, -st: C.Cir.State,
  h: P2({C.Eval.step(ds, t) == None{} : Maybe<C.Term>}, {C.Eval.vals(ds, t, False{}) == False{} : Bool})) -> HR(ds, t, 2, st):
  match h:
    case Tuple{es, ev}:
      Inr{({==}, (es, res.nv(ds, t, ev)))}

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
  St.set(S(foc, 0, sp, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp), 8n, foc)

def ev.st2(+foc: U32, +sp: U32, +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +r63: U32, +m: C.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>) -> C.Cir.State:
  St.set(ev.st1(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp), 10n, TgW(Fd(0n, m, foc)))

# a round from mode 0 whose focus' cell c is flagged VALUE: c and tag are
# set, then the mode is 1
def ev.val.E(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32,
  +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +r63: U32, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, U32>, +focus: C.Term,
  +nd: Nd(ds, im, fi, nx, foc, C.Cir.Cells.get(m, foc), focus, A.tag(focus)),
  +tb: Tbl(m, im, fi, nx), +nz2: {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(Fd(0n, m, foc), 256), 0)), Bool.to_u32(U32.is_ne(C.Cir.Cell.get(4n, C.Cir.Cells.get(m, U32.add(345, U32.and(Fd(0n, m, foc), 63)))), 0)))) == False{} : Bool}) ->
  {C.Cir.exec(f, B.body(), S(foc, 0, sp, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)) ==
    C.Cir.Out.next{St.set(ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp), 1n, 1)} : C.Cir.Out}:
  match nd:
    case Tuple{+valid, Tuple{_, Tuple{+etag, _}}}:
      +st1 = ev.st1(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp)
      +st2 = ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp)
      +st3 = St.set(st2, 1n, 1)
      +f0 = Fd(0n, m, foc)
      +ef1 = ev.fld(0n, C.M.g(C.R.c()), St.regs(st1), m, nx, fi, im, pg, lim, inp, Nil{}, 0, foc, {==}, valid)
      +ef2 = ev.fld(0n, C.M.g(C.R.c()), St.regs(st2), m, nx, fi, im, pg, lim, inp, Nil{}, 0, foc, {==}, valid)
      +etg = ev.op(C.Wasm.Op.and{}, C.M.f(0n, C.M.g(C.R.c())), C.M.c(63), st1, f0, 63, ef1, {==})
      +etg2 = ev.op(C.Wasm.Op.and{}, C.M.f(0n, C.M.g(C.R.c())), C.M.c(63), st2, f0, 63, ef2, {==})
      +efl = ev.op(C.Wasm.Op.ne{}, C.M.and(C.M.f(0n, C.M.g(C.R.c())), C.M.c(256)), C.M.c(0), st2, C.Wasm.op(C.Wasm.Op.and{}, f0, 256), 0,
        ev.op(C.Wasm.Op.and{}, C.M.f(0n, C.M.g(C.R.c())), C.M.c(256), st2, f0, 256, ef2, {==}), {==})
      +addr = C.Wasm.op(C.Wasm.Op.add{}, 345, C.Wasm.op(C.Wasm.Op.and{}, f0, 63))
      +eadr = ev.op(C.Wasm.Op.add{}, C.M.c(345), C.M.tag(C.M.g(C.R.c())), st2, 345, C.Wasm.op(C.Wasm.Op.and{}, f0, 63), {==}, etg2)
      +vt = vt.of(m, im, fi, nx, f0, focus, etag, tb)
      +e4 = C.Cir.Cell.get(4n, C.Cir.Cells.get(m, addr))
      +ee4 = ev.fld(4n, C.M.add(C.M.c(345), C.M.tag(C.M.g(C.R.c()))), St.regs(st2), m, nx, fi, im, pg, lim, inp, Nil{}, 0, addr, eadr, vt)
      +ene = ev.op(C.Wasm.Op.ne{}, C.M.entry(4n, C.M.g(C.R.c())), C.M.c(0), st2, e4, 0, ee4, {==})
      +flv = C.Wasm.op(C.Wasm.Op.ne{}, C.Wasm.op(C.Wasm.Op.and{}, f0, 256), 0)
      +nev = C.Wasm.op(C.Wasm.Op.ne{}, e4, 0)
      +ec2 = ev.op(C.Wasm.Op.or{}, C.M.flag(C.M.g(C.R.c()), C.F.value()), C.M.ne(C.M.entry(4n, C.M.g(C.R.c())), C.M.c(0)), st2, flv, nev, efl, ene)
      +e3a = Equal.trans(C.Cir.Out, C.Cir.exec(f, C.Cir.Stmt.if{B.cond2(), C.M.set(C.R.mode(), C.M.c(1)), B.else()}, st2),
        C.Cir.exec(f, C.M.set(C.R.mode(), C.M.c(1)), st2), C.Cir.Out.next{st3},
        eq.if.t(f, B.cond2(), C.M.set(C.R.mode(), C.M.c(1)), B.else(), st2, C.Wasm.op(C.Wasm.Op.or{}, flv, nev), ec2, nz2),
        eq.set(f, 1n, C.M.c(1), st2, 1, {==}, {==}))
      %Equal.sym(C.Cir.Out, C.Cir.exec(f, B.body(), S(foc, 0, sp, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)), C.Cir.exec(f, C.M.ev(), S(foc, 0, sp, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)),
        eq.if.t(f, C.M.eq(C.M.g(C.R.mode()), C.M.c(0)), C.M.ev(), C.M.ret(), S(foc, 0, sp, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp), 1, {==}, {==})) :
        {_ == C.Cir.Out.next{st3} : C.Cir.Out}
      %rw.seq(f, C.M.set(C.R.c(), C.M.g(C.R.focus())), B.ev2(), S(foc, 0, sp, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp), st1,
        eq.set(f, 8n, C.M.g(C.R.focus()), S(foc, 0, sp, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp), foc, {==}, {==})) : {_ == C.Cir.Out.next{st3} : C.Cir.Out}
      %rw.seq(f, C.M.set(C.R.tag(), C.M.tag(C.M.g(C.R.c()))), B.ev3(), st1, st2,
        eq.set(f, 10n, C.M.tag(C.M.g(C.R.c())), st1, TgW(f0), etg, {==})) : {_ == C.Cir.Out.next{st3} : C.Cir.Out}
      %rw.seq(f, C.Cir.Stmt.if{B.cond2(), C.M.set(C.R.mode(), C.M.c(1)), B.else()}, C.Cir.Stmt.nop{}, st2, st3, e3a) :
        {_ == C.Cir.Out.next{st3} : C.Cir.Out}
      %Equal.sym(C.Cir.Out, C.Cir.exec(f, C.Cir.Stmt.nop{}, st3), C.Cir.Out.next{st3}, eq.nop(f, st3)) :
        {_ == C.Cir.Out.next{st3} : C.Cir.Out}
      {==}

# the table of the image
def img.tbl(-ds: List<&2, C.Def>, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, -m: C.Cir.Cells, -im: U32,
  -fi: U32, -nx: U32, io: ImgOK(ds, ks, img, m, im, fi, nx)) -> Tbl(m, im, fi, nx):
  match io:
    case Tuple{tb, _}:
      tb

# a cell flagged VALUE stands for a value
def nd.val(-ds: List<&2, C.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, -x: C.Cir.Cell, -t: C.Term, -tag: U32,
  nd: Nd(ds, im, fi, nx, c, x, t, tag), hv: {FlW(C.Cir.Cell.get(0n, x), 256) == True{} : Bool}) ->
  {Bool.or(Bool.not(True{}), C.Eval.vals(ds, t, False{})) == True{} : Bool}:
  match nd:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{nv, _}}}}:
      %hv : {Bool.or(Bool.not(_), C.Eval.vals(ds, t, False{})) == True{} : Bool}
      nv

# mode 1 costs less than mode 0 by the focus' measure
def ret.lt(+focus: C.Term, +fs: List<&2, AF>, -w: Nat, ew: {A.w(False{}, focus, fs) == w : Nat}) ->
  N.Le(1n+A.w(True{}, focus, fs), w):
  %ew : N.Le(1n+A.w(True{}, focus, fs), _)
  N.add_mono(1n, A.w3(focus), A.w.frames(fs), A.w.frames(fs), A.w3.pos(focus), N.le_refl(A.w.frames(fs)))

def ev.val.mv(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32,
  +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +r63: U32, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +focus: C.Term,
  +et: {A.plugs(fs, focus) == t : C.Term}, ew: {A.w(False{}, focus, fs) == w : Nat}, +afs: AFs.ok(ds, fs),
  +isf: Is(ds, m, im, fi, nx, ks, img, foc, focus), +frs: Frs(ds, m, im, fi, nx, ks, img, ps, sp, fs),
  +hp: Heap(m, nx, fi, [foc], pend, ps), +io: ImgOK(ds, ks, img, m, im, fi, nx),
  +nz2: {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(Fd(0n, m, foc), 256), 0)), Bool.to_u32(U32.is_ne(C.Cir.Cell.get(4n, C.Cir.Cells.get(m, U32.add(345, U32.and(Fd(0n, m, foc), 63)))), 0)))) == False{} : Bool},
  +evv: {Bool.or(Bool.not(True{}), C.Eval.vals(ds, focus, False{})) == True{} : Bool}) ->
  MV(ds, ks, img, S(foc, 0, sp, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp), t, w):
  +nd = is.nd(ds, m, im, fi, nx, ks, img, foc, focus, isf)
  +tb = img.tbl(ds, ks, img, m, im, fi, nx, io)
  +w2 = A.w(True{}, focus, fs)
  +inv3 = {(Wit{True{}, focus, fs, foc, sp, pend, ps, R60.of(St.regs(St.set(ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp), 1n, 1)))},
    (et, ({==}, (evv,
    (afs, ({==}, (isf, (frs, (hp, (io, ({==}, {==}))))))))))) : Inv(ds, ks, img, St.set(ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp), 1n, 1), t, w2)}
  +lt = ret.lt(focus, fs, w, ew)
  (f => (%Equal.sym(C.Cir.Out, C.Cir.exec(f, B.body(), S(foc, 0, sp, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)), C.Cir.Out.next{St.set(ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp), 1n, 1)},
      ev.val.E(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp, focus, nd, tb, nz2)) :
      Post(False{}, _, s => Rnd(ds, ks, img, t, w, s), s => st2 => HR(ds, t, s, st2));
      Inl{(w2, (inv3, lt))}),
   (0n, (%Equal.sym(C.Cir.Out, C.Cir.exec(0n, B.body(), S(foc, 0, sp, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)), C.Cir.Out.next{St.set(ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp), 1n, 1)},
      ev.val.E(0n, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp, focus, nd, tb, nz2)) : Ends(_);
      Unit{})))

# the tests of M.ev on a cell of the tag 0: none takes it, a halt with 2
def B.chain0(+f: Nat, +st: C.Cir.State, +f0: U32,
  +etag: {TgW(f0) == 0 : U32}, +er: {C.Cir.eval(C.M.g(C.R.tag()), st) == Some{TgW(f0)} : Maybe<&2, U32>}) ->
  {C.Cir.exec(f, B.else(), st) == C.Cir.Out.halt{2, st} : C.Cir.Out}:
  %Equal.sym(C.Cir.Out, C.Cir.exec(f, B.else(), st), C.Cir.exec(f, B.e1(), st),
    eq.if.e(f, C.M.eq(C.M.g(C.R.tag()), C.M.c(8)), C.M.ev.app(), B.e1(), st, C.Wasm.op(C.Wasm.Op.eq{}, TgW(f0), 8),
      ev.op(C.Wasm.Op.eq{}, C.M.g(C.R.tag()), C.M.c(8), st, TgW(f0), 8, er, {==}), tag.ne(f0, 0, 8, etag, {==}))) :
    {_ == C.Cir.Out.halt{2, st} : C.Cir.Out}
  %Equal.sym(C.Cir.Out, C.Cir.exec(f, B.e1(), st), C.Cir.exec(f, B.e2(), st),
    eq.if.e(f, C.M.eq(C.M.g(C.R.tag()), C.M.c(1)), C.M.ev.ref(), B.e2(), st, C.Wasm.op(C.Wasm.Op.eq{}, TgW(f0), 1),
      ev.op(C.Wasm.Op.eq{}, C.M.g(C.R.tag()), C.M.c(1), st, TgW(f0), 1, er, {==}), tag.ne(f0, 0, 1, etag, {==}))) :
    {_ == C.Cir.Out.halt{2, st} : C.Cir.Out}
  %Equal.sym(C.Cir.Out, C.Cir.exec(f, B.e2(), st), C.Cir.exec(f, B.e3(), st),
    eq.if.e(f, C.M.eq(C.M.g(C.R.tag()), C.M.c(2)), C.M.ev.ann(), B.e3(), st, C.Wasm.op(C.Wasm.Op.eq{}, TgW(f0), 2),
      ev.op(C.Wasm.Op.eq{}, C.M.g(C.R.tag()), C.M.c(2), st, TgW(f0), 2, er, {==}), tag.ne(f0, 0, 2, etag, {==}))) :
    {_ == C.Cir.Out.halt{2, st} : C.Cir.Out}
  %Equal.sym(C.Cir.Out, C.Cir.exec(f, B.e3(), st), C.Cir.exec(f, B.e4(), st),
    eq.if.e(f, C.M.eq(C.M.g(C.R.tag()), C.M.c(3)), C.M.ev.let(), B.e4(), st, C.Wasm.op(C.Wasm.Op.eq{}, TgW(f0), 3),
      ev.op(C.Wasm.Op.eq{}, C.M.g(C.R.tag()), C.M.c(3), st, TgW(f0), 3, er, {==}), tag.ne(f0, 0, 3, etag, {==}))) :
    {_ == C.Cir.Out.halt{2, st} : C.Cir.Out}
  %Equal.sym(C.Cir.Out, C.Cir.exec(f, B.e4(), st), C.Cir.exec(f, B.e5(), st),
    eq.if.e(f, C.M.eq(C.M.g(C.R.tag()), C.M.c(10)), C.M.ev.tup(), B.e5(), st, C.Wasm.op(C.Wasm.Op.eq{}, TgW(f0), 10),
      ev.op(C.Wasm.Op.eq{}, C.M.g(C.R.tag()), C.M.c(10), st, TgW(f0), 10, er, {==}), tag.ne(f0, 0, 10, etag, {==}))) :
    {_ == C.Cir.Out.halt{2, st} : C.Cir.Out}
  %Equal.sym(C.Cir.Out, C.Cir.exec(f, B.e5(), st), C.Cir.exec(f, B.e6(), st),
    eq.if.e(f, C.M.eq(C.M.g(C.R.tag()), C.M.c(18)), C.M.ev.rwt(), B.e6(), st, C.Wasm.op(C.Wasm.Op.eq{}, TgW(f0), 18),
      ev.op(C.Wasm.Op.eq{}, C.M.g(C.R.tag()), C.M.c(18), st, TgW(f0), 18, er, {==}), tag.ne(f0, 0, 18, etag, {==}))) :
    {_ == C.Cir.Out.halt{2, st} : C.Cir.Out}
  %Equal.sym(C.Cir.Out, C.Cir.exec(f, B.e6(), st), C.Cir.exec(f, C.M.halt(2), st),
    eq.if.e(f, C.M.eq(C.M.g(C.R.tag()), C.M.c(5)), C.M.ev.min(), C.M.halt(2), st, C.Wasm.op(C.Wasm.Op.eq{}, TgW(f0), 5),
      ev.op(C.Wasm.Op.eq{}, C.M.g(C.R.tag()), C.M.c(5), st, TgW(f0), 5, er, {==}), tag.ne(f0, 0, 5, etag, {==}))) :
    {_ == C.Cir.Out.halt{2, st} : C.Cir.Out}
  eq.halt(f, 2, st)

# a round from mode 0 whose focus' cell is a variable: no case of M.ev takes
# it, a halt with 2
def ev.var.E(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32,
  +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +r63: U32, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, U32>, +i: Nat,
  +nd: Nd(ds, im, fi, nx, foc, C.Cir.Cells.get(m, foc), C.Term.Var{i}, 0),
  +tb: Tbl(m, im, fi, nx), +hv: {Fl(m, foc, 256) == False{} : Bool}) ->
  {C.Cir.exec(f, B.body(), S(foc, 0, sp, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)) == C.Cir.Out.halt{2, ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp)} : C.Cir.Out}:
  match nd:
    case Tuple{+valid, Tuple{_, Tuple{+etag, _}}}:
      +st1 = ev.st1(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp)
      +st2 = ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp)
      +f0 = Fd(0n, m, foc)
      +ef1 = ev.fld(0n, C.M.g(C.R.c()), St.regs(st1), m, nx, fi, im, pg, lim, inp, Nil{}, 0, foc, {==}, valid)
      +ef2 = ev.fld(0n, C.M.g(C.R.c()), St.regs(st2), m, nx, fi, im, pg, lim, inp, Nil{}, 0, foc, {==}, valid)
      +etg = ev.op(C.Wasm.Op.and{}, C.M.f(0n, C.M.g(C.R.c())), C.M.c(63), st1, f0, 63, ef1, {==})
      +etg2 = ev.op(C.Wasm.Op.and{}, C.M.f(0n, C.M.g(C.R.c())), C.M.c(63), st2, f0, 63, ef2, {==})
      +efl = ev.op(C.Wasm.Op.ne{}, C.M.and(C.M.f(0n, C.M.g(C.R.c())), C.M.c(256)), C.M.c(0), st2, C.Wasm.op(C.Wasm.Op.and{}, f0, 256), 0,
        ev.op(C.Wasm.Op.and{}, C.M.f(0n, C.M.g(C.R.c())), C.M.c(256), st2, f0, 256, ef2, {==}), {==})
      +addr = C.Wasm.op(C.Wasm.Op.add{}, 345, C.Wasm.op(C.Wasm.Op.and{}, f0, 63))
      +eadr = ev.op(C.Wasm.Op.add{}, C.M.c(345), C.M.tag(C.M.g(C.R.c())), st2, 345, C.Wasm.op(C.Wasm.Op.and{}, f0, 63), {==}, etg2)
      +vt = vt.of(m, im, fi, nx, f0, C.Term.Var{i}, etag, tb)
      +e4 = C.Cir.Cell.get(4n, C.Cir.Cells.get(m, addr))
      +ee4 = ev.fld(4n, C.M.add(C.M.c(345), C.M.tag(C.M.g(C.R.c()))), St.regs(st2), m, nx, fi, im, pg, lim, inp, Nil{}, 0, addr, eadr, vt)
      +ene = ev.op(C.Wasm.Op.ne{}, C.M.entry(4n, C.M.g(C.R.c())), C.M.c(0), st2, e4, 0, ee4, {==})
      +flv = C.Wasm.op(C.Wasm.Op.ne{}, C.Wasm.op(C.Wasm.Op.and{}, f0, 256), 0)
      +nev = C.Wasm.op(C.Wasm.Op.ne{}, e4, 0)
      +ec2 = ev.op(C.Wasm.Op.or{}, C.M.flag(C.M.g(C.R.c()), C.F.value()), C.M.ne(C.M.entry(4n, C.M.g(C.R.c())), C.M.c(0)), st2, flv, nev, efl, ene)
      +z2 = z.of(m, im, fi, nx, f0, C.Term.Var{i}, etag, tb, hv, {==})
      +e3a = Equal.trans(C.Cir.Out, C.Cir.exec(f, C.Cir.Stmt.if{B.cond2(), C.M.set(C.R.mode(), C.M.c(1)), B.else()}, st2),
        C.Cir.exec(f, B.else(), st2), C.Cir.Out.halt{2, st2},
        eq.if.e(f, B.cond2(), C.M.set(C.R.mode(), C.M.c(1)), B.else(), st2, C.Wasm.op(C.Wasm.Op.or{}, flv, nev), ec2, z2),
        B.chain0(f, st2, f0, etag, {==}))
      %Equal.sym(C.Cir.Out, C.Cir.exec(f, B.body(), S(foc, 0, sp, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)), C.Cir.exec(f, C.M.ev(), S(foc, 0, sp, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)),
        eq.if.t(f, C.M.eq(C.M.g(C.R.mode()), C.M.c(0)), C.M.ev(), C.M.ret(), S(foc, 0, sp, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp), 1, {==}, {==})) :
        {_ == C.Cir.Out.halt{2, st2} : C.Cir.Out}
      %rw.seq(f, C.M.set(C.R.c(), C.M.g(C.R.focus())), B.ev2(), S(foc, 0, sp, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp), st1,
        eq.set(f, 8n, C.M.g(C.R.focus()), S(foc, 0, sp, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp), foc, {==}, {==})) : {_ == C.Cir.Out.halt{2, st2} : C.Cir.Out}
      %rw.seq(f, C.M.set(C.R.tag(), C.M.tag(C.M.g(C.R.c()))), B.ev3(), st1, st2,
        eq.set(f, 10n, C.M.tag(C.M.g(C.R.c())), st1, TgW(f0), etg, {==})) : {_ == C.Cir.Out.halt{2, st2} : C.Cir.Out}
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
  -H2: U32 -> C.Cir.State -> Type, h: Post(dn, o, Q1, H1), q: @st: C.Cir.State -> Q1(st) -> Q2(st),
  hh: @s: U32 -> @st: C.Cir.State -> H1(s, st) -> H2(s, st)) -> Post(dn, o, Q2, H2):
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
  h: OutH(v, s, st2)) -> HR(ds, v, s, st2):
  match h:
    case Inl{x}:
      (e0, eu) = x
      Inl{(e0, (ev.stops(ds, v, ev), res.val(ds, v, Some{List.reverse(&2, U32, St.out(st2))}, ev, eu)))}
    case Inr{x}:
      (e2, eu) = x
      Inr{(e2, (ev.stops(ds, v, ev), res.val(ds, v, None{}, ev, eu)))}

# a round from mode 1 with no frame is M.out
def out.E(+f: Nat, +foc: U32, +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +r63: U32, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, U32>) -> {C.Cir.exec(f, B.body(), S(foc, 1, 0, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)) == C.Cir.exec(f, C.M.out(), S(foc, 1, 0, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)) : C.Cir.Out}:
  Equal.trans(C.Cir.Out, C.Cir.exec(f, B.body(), S(foc, 1, 0, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)), C.Cir.exec(f, C.M.ret(), S(foc, 1, 0, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)), C.Cir.exec(f, C.M.out(), S(foc, 1, 0, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)),
    eq.if.e(f, C.M.eq(C.M.g(C.R.mode()), C.M.c(0)), C.M.ev(), C.M.ret(), S(foc, 1, 0, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp), 0, {==}, {==}),
    eq.if.t(f, stmt.cond(C.M.ret()), stmt.then(C.M.ret()), stmt.else(C.M.ret()), S(foc, 1, 0, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp), 1, {==}, {==}))

def out.mv(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +pend: U32,
  +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +r63: U32, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>,
  +t: C.Term, +w: Nat, +focus: C.Term, +et: {focus == t : C.Term},
  +ev: {C.Eval.vals(ds, focus, False{}) == True{} : Bool}, +isf: Is(ds, m, im, fi, nx, ks, img, foc, focus),
  +ks2: List<&2, List<&2, U32>>, +hk: {ks == C.Img.known(ks2) : List<&2, List<&2, U32>>}) ->
  MV(ds, ks, img, S(foc, 1, 0, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp), t, w):
  +od = out.done(ds, ks, img, foc, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp, focus, ks2, isf, hk)
  +f1 = Ex.fst(Nat, f => Ends(C.Cir.exec(f, C.M.out(), S(foc, 1, 0, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp))), od)
  (+f => (%Equal.sym(C.Cir.Out, C.Cir.exec(f, B.body(), S(foc, 1, 0, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)), C.Cir.exec(f, C.M.out(), S(foc, 1, 0, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)),
      out.E(f, foc, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp)) :
      Post(False{}, _, s => Rnd(ds, ks, img, t, w, s), s => st2 => HR(ds, t, s, st2));
      post.map(False{}, C.Cir.exec(f, C.M.out(), S(foc, 1, 0, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)), st => Empty, s => Rnd(ds, ks, img, t, w, s),
        s => st2 => OutH(focus, s, st2), s => st2 => HR(ds, t, s, st2),
        out.post(f, ds, ks, img, foc, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp, focus, ks2, isf, hk),
        st => h => Empty.absurd(Rnd(ds, ks, img, t, w, st), h),
        s => st2 => h => hr.eq(ds, focus, t, s, st2, et, out.hr(ds, focus, ev, s, st2, h)))),
   (f1, (%Equal.sym(C.Cir.Out, C.Cir.exec(f1, B.body(), S(foc, 1, 0, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)), C.Cir.exec(f1, C.M.out(), S(foc, 1, 0, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)),
      out.E(f1, foc, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp)) : Ends(_);
      Ex.snd(Nat, f => Ends(C.Cir.exec(f, C.M.out(), S(foc, 1, 0, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp))), od))))

# the image's names, the machine's first
def img.ks(-ds: List<&2, C.Def>, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, -m: C.Cir.Cells, -im: U32,
  -fi: U32, -nx: U32, io: ImgOK(ds, ks, img, m, im, fi, nx)) -> Ex(List<&2, List<&2, U32>>, ks2 => {ks == C.Img.known(ks2) : List<&2, List<&2, U32>>}):
  match io:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{k, _}}}}}}:
      k

# The moves, one lemma each (open where the body is ?TODO)

# mode 0, a focus flagged VALUE: a value, mode 1; an admin move
def mv.ev.val(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +focus: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, focus, fs, ps), +hv: {Fl(m, foc, 256) == True{} : Bool}) ->
  MV(ds, ks, img, S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match rest:
    case R60{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62, +r63}:
      match iv:
        case Tuple{+et, Tuple{+ew, Tuple{_, Tuple{+afs, Tuple{_, Tuple{+isf, Tuple{+frs, Tuple{+hp, Tuple{+io, Tuple{_, _}}}}}}}}}}:
          +nd = is.nd(ds, m, im, fi, nx, ks, img, foc, focus, isf)
          ev.val.mv(ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, et, ew, afs, isf, frs, hp,
            io, nz.of(Fd(0n, m, foc), C.Cir.Cell.get(4n, C.Cir.Cells.get(m, U32.add(345, U32.and(Fd(0n, m, foc), 63)))), hv),
            nd.val(ds, im, fi, nx, foc, C.Cir.Cells.get(m, foc), focus, A.tag(focus), nd, hv))

# mode 0, a focus that is a value by its form, as the table says (A.tbl): mode 1; an admin move
def mv.ev.former(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +focus: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, focus, fs, ps), +hf: {A.tbl(focus) == True{} : Bool}) ->
  MV(ds, ks, img, S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match rest:
    case R60{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62, +r63}:
      match iv:
        case Tuple{+et, Tuple{+ew, Tuple{_, Tuple{+afs, Tuple{_, Tuple{+isf, Tuple{+frs, Tuple{+hp, Tuple{+io, Tuple{_, _}}}}}}}}}}:
          +nd = is.nd(ds, m, im, fi, nx, ks, img, foc, focus, isf)
          ev.val.mv(ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, et, ew, afs, isf, frs, hp,
            io, nzf.go(ds, im, fi, nx, foc, m, focus, nd, img.tbl(ds, ks, img, m, im, fi, nx, io), hf), tbl.vals(ds, focus, hf))

# mode 0, a variable: free in the whole term, which has no step and is no value; halt 2
def mv.ev.var(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +i: Nat,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, C.Term.Var{i}, fs, ps), +hv: {Fl(m, foc, 256) == False{} : Bool}) ->
  MV(ds, ks, img, S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match rest:
    case R60{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62, +r63}:
      match iv:
        case Tuple{+et, Tuple{_, Tuple{_, Tuple{+afs, Tuple{_, Tuple{+isf, Tuple{_, Tuple{_, Tuple{+io, Tuple{_, _}}}}}}}}}}:
          +nd = is.nd(ds, m, im, fi, nx, ks, img, foc, C.Term.Var{i}, isf)
          +tb = img.tbl(ds, ks, img, m, im, fi, nx, io)
          hr = hr.eq(ds, A.plugs(fs, C.Term.Var{i}), t, 2, ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp), et,
            hr.stuck(ds, A.plugs(fs, C.Term.Var{i}), ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp), ev.stuck(ds, fs, C.Term.Var{i}, afs, {==}, {==})))
          (f => (%Equal.sym(C.Cir.Out, C.Cir.exec(f, B.body(), S(foc, 0, sp, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)), C.Cir.Out.halt{2, ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp)},
              ev.var.E(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp, i, nd, tb, hv)) :
              Post(False{}, _, s => Rnd(ds, ks, img, t, w, s), s => st2 => HR(ds, t, s, st2));
              hr),
           (0n, (%Equal.sym(C.Cir.Out, C.Cir.exec(0n, B.body(), S(foc, 0, sp, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp)), C.Cir.Out.halt{2, ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp)},
              ev.var.E(0n, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp, i, nd, tb, hv)) : Ends(_);
              Unit{})))

# mode 0, Ref k: the call of k on no arguments (M.call, with M.walk and M.copy): a step to the copy of its leaf; or, when its case tree takes an argument, mode 1, an admin move; halt 2 when no walk exists
def mv.ev.ref(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +k: List<&2, U32>,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, C.Term.Ref{k}, fs, ps), +hv: {Fl(m, foc, 256) == False{} : Bool}) ->
  MV(ds, ks, img, S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 0, Ann x y: x, a step
def mv.ev.ann(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +x: C.Term, +y: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, C.Term.Ann{x, y}, fs, ps), +hv: {Fl(m, foc, 256) == False{} : Bool}) ->
  MV(ds, ks, img, S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 0, Let q v b with q live: v in the frame Let q □ b; an admin move
def mv.ev.let(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +q: C.Quan, +v: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, C.Term.Let{q, v, b}, fs, ps), +hv: {Fl(m, foc, 256) == False{} : Bool}, +hq: {C.Quan.live(q) == True{} : Bool}) ->
  MV(ds, ks, img, S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 0, Let q v b with q dead: b with v put in (M.copy), a step
def mv.ev.unlet(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +q: C.Quan, +v: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, C.Term.Let{q, v, b}, fs, ps), +hv: {Fl(m, foc, 256) == False{} : Bool}, +hq: {C.Quan.live(q) == False{} : Bool}) ->
  MV(ds, ks, img, S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 0, App q g x: g in the frame App q □ x; an admin move
def mv.ev.app(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +q: C.Quan, +g: C.Term, +x: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, C.Term.App{q, g, x}, fs, ps), +hv: {Fl(m, foc, 256) == False{} : Bool}) ->
  MV(ds, ks, img, S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 0, Tup q a b with q live, not flagged VALUE: a in the frame Tup q □ b; an admin move
def mv.ev.tup(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +q: C.Quan, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, C.Term.Tup{q, a, b}, fs, ps), +hv: {Fl(m, foc, 256) == False{} : Bool}, +hq: {C.Quan.live(q) == True{} : Bool}) ->
  MV(ds, ks, img, S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 0, Tup q a b with q dead, not flagged VALUE: b in the frame Tup q a □; an admin move
def mv.ev.tup0(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +q: C.Quan, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, C.Term.Tup{q, a, b}, fs, ps), +hv: {Fl(m, foc, 256) == False{} : Bool}, +hq: {C.Quan.live(q) == False{} : Bool}) ->
  MV(ds, ks, img, S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 0, Rwt e p b: e in the frame Rwt □ p b; an admin move
def mv.ev.rwt(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +e: C.Term, +p: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, C.Term.Rwt{e, p, b}, fs, ps), +hv: {Fl(m, foc, 256) == False{} : Bool}) ->
  MV(ds, ks, img, S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 0, Min a b: a in the frame Min □ b; an admin move
def mv.ev.min(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, C.Term.Min{a, b}, fs, ps), +hv: {Fl(m, foc, 256) == False{} : Bool}) ->
  MV(ds, ks, img, S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, no frame: M.out halts with 0 and the bytes of the value (Program.unbytes), or with 2 when it is no list of bytes
def mv.out(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +focus: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Nil{}, ps)) ->
  MV(ds, ks, img, S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match rest:
    case R60{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62, +r63}:
      match iv:
        case Tuple{+et, Tuple{_, Tuple{+evv, Tuple{_, Tuple{_, Tuple{+isf, Tuple{+frs, Tuple{_, Tuple{+io, Tuple{_, _}}}}}}}}}}:
          +k = img.ks(ds, ks, img, m, im, fi, nx, io)
          %Equal.sym(U32, sp, 0, frs) : MV(ds, ks, img, S(foc, 1, _, pend, R60{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63}, m, nx, fi, im, pg, lim, inp), t, w)
          out.mv(ds, ks, img, foc, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, m, nx, fi, im, pg, lim, inp, t, w, focus, et, evv, isf,
            Ex.fst(List<&2, List<&2, U32>>, ks2 => {ks == C.Img.known(ks2) : List<&2, List<&2, U32>>}, k),
            Ex.snd(List<&2, List<&2, U32>>, ks2 => {ks == C.Img.known(ks2) : List<&2, List<&2, U32>>}, k))

# mode 1, App q □ a (app_arg, app_val) with q live and a not known: a to evaluate, in the frame App q v □; an admin move
def mv.ret.swap(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +focus: C.Term, +kind: FK, +q: C.Quan, +k: Bool, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{AF{kind, q, k, a, b}, fs}, ps), +hk: {FK.isapp(kind) == True{} : Bool}, +hs: {Bool.and(C.Quan.live(q), Bool.not(k)) == True{} : Bool}) ->
  MV(ds, ks, img, S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, App q v □ a (app_arg, app_val), when q is dead or a known: the redex of a λ (Eval.redex): its body with the argument put in (M.data, M.copy), a step; halt 2 when the λ does not bind it
def mv.ret.app.lam(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +r: C.Quan, +h: C.Term, +kind: FK, +q: C.Quan, +k: Bool, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, C.Term.Lam{r, h}, Con{AF{kind, q, k, a, b}, fs}, ps), +hk: {FK.isapp(kind) == True{} : Bool}, +hs: {Bool.and(C.Quan.live(q), Bool.not(k)) == False{} : Bool}) ->
  MV(ds, ks, img, S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, App q g □ (app_fun), with the value v: the redex of a λ (Eval.redex): its body with the argument put in (M.data, M.copy), a step; halt 2 when the λ does not bind it
def mv.ret.fun.lam(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +r: C.Quan, +h: C.Term, +focus: C.Term, +q: C.Quan, +k: Bool, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{AF{FK.fun{}, q, k, C.Term.Lam{r, h}, b}, fs}, ps)) ->
  MV(ds, ks, img, S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, App q v □ a (app_arg, app_val), when q is dead or a known: the redex of a λ-match of pairs: its case on the pair's fields, a step; halt 2 when the argument is no live pair
def mv.ret.app.prj(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +h: C.Term, +kind: FK, +q: C.Quan, +k: Bool, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, C.Term.Prj{h}, Con{AF{kind, q, k, a, b}, fs}, ps), +hk: {FK.isapp(kind) == True{} : Bool}, +hs: {Bool.and(C.Quan.live(q), Bool.not(k)) == False{} : Bool}) ->
  MV(ds, ks, img, S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, App q g □ (app_fun), with the value v: the redex of a λ-match of pairs: its case on the pair's fields, a step; halt 2 when the argument is no live pair
def mv.ret.fun.prj(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +h: C.Term, +focus: C.Term, +q: C.Quan, +k: Bool, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{AF{FK.fun{}, q, k, C.Term.Prj{h}, b}, fs}, ps)) ->
  MV(ds, ks, img, S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, App q v □ a (app_arg, app_val), when q is dead or a known: the redex of a λ-match of labels: the case of the label, a step; halt 2 when the argument is no live label
def mv.ret.app.mat(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +j: List<&2, U32>, +h: C.Term, +n: C.Term, +kind: FK, +q: C.Quan, +k: Bool, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, C.Term.Mat{j, h, n}, Con{AF{kind, q, k, a, b}, fs}, ps), +hk: {FK.isapp(kind) == True{} : Bool}, +hs: {Bool.and(C.Quan.live(q), Bool.not(k)) == False{} : Bool}) ->
  MV(ds, ks, img, S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, App q g □ (app_fun), with the value v: the redex of a λ-match of labels: the case of the label, a step; halt 2 when the argument is no live label
def mv.ret.fun.mat(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +j: List<&2, U32>, +h: C.Term, +n: C.Term, +focus: C.Term, +q: C.Quan, +k: Bool, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{AF{FK.fun{}, q, k, C.Term.Mat{j, h, n}, b}, fs}, ps)) ->
  MV(ds, ks, img, S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, App q v □ a (app_arg, app_val), when q is dead or a known: the redex of any other value: a call (M.call, with M.walk and M.copy) of the def at the head of its spine: a step to the copy of its leaf, or a value that waits for more arguments (an admin move); halt 2 when no walk exists
def mv.ret.app.call(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +focus: C.Term, +kind: FK, +q: C.Quan, +k: Bool, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{AF{kind, q, k, a, b}, fs}, ps), +hk: {FK.isapp(kind) == True{} : Bool}, +hs: {Bool.and(C.Quan.live(q), Bool.not(k)) == False{} : Bool}, +hn: {A.node(focus) == False{} : Bool}) ->
  MV(ds, ks, img, S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, App q g □ (app_fun), with the value v: the redex of any other value: a call (M.call, with M.walk and M.copy) of the def at the head of its spine: a step to the copy of its leaf, or a value that waits for more arguments (an admin move); halt 2 when no walk exists
def mv.ret.fun.call(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +g: C.Term, +focus: C.Term, +q: C.Quan, +k: Bool, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{AF{FK.fun{}, q, k, g, b}, fs}, ps), +hn: {A.node(g) == False{} : Bool}) ->
  MV(ds, ks, img, S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, Let q □ a, with the value v: a with v put in (M.data, M.copy), a step; halt 2 when q is 2 and v is no Data
def mv.ret.let(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +focus: C.Term, +q: C.Quan, +k: Bool, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{AF{FK.let{}, q, k, a, b}, fs}, ps)) ->
  MV(ds, ks, img, S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, Tup q □ a, with the value v: a to evaluate, in the frame Tup q v □; an admin move
def mv.ret.tupb(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +focus: C.Term, +q: C.Quan, +k: Bool, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{AF{FK.tupb{}, q, k, a, b}, fs}, ps)) ->
  MV(ds, ks, img, S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, Tup q a □, with the value v: the value Tup q a v; an admin move
def mv.ret.tupa(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +focus: C.Term, +q: C.Quan, +k: Bool, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{AF{FK.tupa{}, q, k, a, b}, fs}, ps)) ->
  MV(ds, ks, img, S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, Rwt □ a b, with the value v: b when v is Rfl, a step; else halt 2
def mv.ret.rwt(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +focus: C.Term, +q: C.Quan, +k: Bool, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{AF{FK.rwt{}, q, k, a, b}, fs}, ps)) ->
  MV(ds, ks, img, S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, Min □ a, with the value v: a to evaluate, in the frame Min v □; an admin move
def mv.ret.minb(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +focus: C.Term, +q: C.Quan, +k: Bool, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{AF{FK.minb{}, q, k, a, b}, fs}, ps)) ->
  MV(ds, ks, img, S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# mode 1, Min a □, with the value v: the meet of a and v, a step, when both are labels of quantities; else halt 2
def mv.ret.mina(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +focus: C.Term, +q: C.Quan, +k: Bool, +a: C.Term, +b: C.Term,
  +iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{AF{FK.mina{}, q, k, a, b}, fs}, ps)) ->
  MV(ds, ks, img, S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  ?TODO

# The choice of the move
# ----------------------

# mode 0: by the flag VALUE of the focus' cell, then by its term
def round.ev(b: Bool, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +focus: C.Term, eb: {Fl(m, foc, 256) == b : Bool},
  iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, False{}, focus, fs, ps)) -> MV(ds, ks, img, S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
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
def round.app(b: Bool, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +focus: C.Term, +kind: FK, +q: C.Quan, +k: Bool, +a: C.Term, +bb: C.Term,
  eb: {Bool.and(C.Quan.live(q), Bool.not(k)) == b : Bool}, hk: {FK.isapp(kind) == True{} : Bool},
  iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{AF{kind, q, k, a, bb}, fs}, ps)) -> MV(ds, ks, img, S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
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
def round.fun(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +focus: C.Term, +q: C.Quan, +k: Bool, +g: C.Term, +bb: C.Term,
  iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, True{}, focus, Con{AF{FK.fun{}, q, k, g, bb}, fs}, ps)) -> MV(ds, ks, img, S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
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
def round.go(+ret: Bool, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32, +sp: U32, +pend: U32, +rest: R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +t: C.Term, +w: Nat, +fs: List<&2, AF>, +ps: List<&2, U32>, +focus: C.Term,
  iv: IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, ret, focus, fs, ps)) -> MV(ds, ks, img, S(foc, Bool.to_u32(ret), sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match ret:
    case False{}:
      round.ev(Fl(m, foc, 256), ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, {==}, iv)
    case True{}:
      match fs:
        case Nil{}:
          mv.out(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, iv)
        case Con{AF{+kind, +q, +k, +a, +bb}, +fs2}:
          match kind:
            case FK.arg{}:
              round.app(Bool.and(C.Quan.live(q), Bool.not(k)), ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, FK.arg{}, q, k, a, bb, {==}, {==}, iv)
            case FK.val{}:
              round.app(Bool.and(C.Quan.live(q), Bool.not(k)), ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, FK.val{}, q, k, a, bb, {==}, {==}, iv)
            case FK.fun{}:
              round.fun(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)
            case FK.let{}:
              mv.ret.let(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)
            case FK.tupb{}:
              mv.ret.tupb(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)
            case FK.tupa{}:
              mv.ret.tupa(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)
            case FK.rwt{}:
              mv.ret.rwt(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)
            case FK.minb{}:
              mv.ret.minb(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)
            case FK.mina{}:
              mv.ret.mina(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs2, ps, focus, q, k, a, bb, iv)

# the registers, the output and its length that Inv finds
def inv.regs(-ds: List<&2, C.Def>, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, -regs: List<&2, U32>, -m: C.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -out: List<&2, U32>, -outn: U32, -t: C.Term, -w: Nat, -ret: Bool, -focus: C.Term, -fs: List<&2, AF>, -foc: U32, -sp: U32, -pend: U32, -ps: List<&2, U32>, -rest: R60, iw: InvOf(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest)) ->
  {regs == RG(foc, Bool.to_u32(ret), sp, pend, R60.list(rest)) : List<&2, U32>}:
  match iw:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}:
      e

def inv.out(-ds: List<&2, C.Def>, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, -regs: List<&2, U32>, -m: C.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -out: List<&2, U32>, -outn: U32, -t: C.Term, -w: Nat, -ret: Bool, -focus: C.Term, -fs: List<&2, AF>, -foc: U32, -sp: U32, -pend: U32, -ps: List<&2, U32>, -rest: R60, iw: InvOf(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest)) -> {out == Nil{} : List<&2, U32>}:
  match iw:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}:
      e

def inv.outn(-ds: List<&2, C.Def>, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, -regs: List<&2, U32>, -m: C.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -out: List<&2, U32>, -outn: U32, -t: C.Term, -w: Nat, -ret: Bool, -focus: C.Term, -fs: List<&2, AF>, -foc: U32, -sp: U32, -pend: U32, -ps: List<&2, U32>, -rest: R60, iw: InvOf(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest)) -> {outn == 0 : U32}:
  match iw:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, e}}}}}}}}}}:
      e

# Inv's facts, in the state that it finds
def iv.of(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +out: List<&2, U32>, +outn: U32, +t: C.Term, +w: Nat, +ret: Bool, +focus: C.Term, +fs: List<&2, AF>, +foc: U32, +sp: U32, +pend: U32, +ps: List<&2, U32>, +rest: R60,
  er: {regs == RG(foc, Bool.to_u32(ret), sp, pend, R60.list(rest)) : List<&2, U32>}, eo: {out == Nil{} : List<&2, U32>},
  en: {outn == 0 : U32}, iw: InvOf(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest)) ->
  IV(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, t, w, ret, focus, fs, ps):
  %er : InvOf(ds, ks, img, _, m, nx, fi, im, Nil{}, 0, t, w, ret, focus, fs, foc, sp, pend, ps, rest)
  %eo : InvOf(ds, ks, img, regs, m, nx, fi, im, _, 0, t, w, ret, focus, fs, foc, sp, pend, ps, rest)
  %en : InvOf(ds, ks, img, regs, m, nx, fi, im, out, _, t, w, ret, focus, fs, foc, sp, pend, ps, rest)
  iw

def round.iw(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +out: List<&2, U32>, +outn: U32, +t: C.Term, +w: Nat, +ret: Bool, +focus: C.Term, +fs: List<&2, AF>, +foc: U32, +sp: U32, +pend: U32, +ps: List<&2, U32>, +rest: R60, +pg: U32, +lim: U32, +inp: List<&2, U32>, +iw: InvOf(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest)) ->
  MV(ds, ks, img, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}, t, w):
  +er = inv.regs(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest, iw)
  +eo = inv.out(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest, iw)
  +en = inv.outn(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest, iw)
  %Equal.sym(List<&2, U32>, regs, RG(foc, Bool.to_u32(ret), sp, pend, R60.list(rest)), er) :
    MV(ds, ks, img, C.Cir.State{_, m, nx, fi, im, pg, lim, inp, out, outn}, t, w)
  %Equal.sym(List<&2, U32>, out, Nil{}, eo) :
    MV(ds, ks, img, C.Cir.State{RG(foc, Bool.to_u32(ret), sp, pend, R60.list(rest)), m, nx, fi, im, pg, lim, inp, _, outn}, t, w)
  %Equal.sym(U32, outn, 0, en) :
    MV(ds, ks, img, C.Cir.State{RG(foc, Bool.to_u32(ret), sp, pend, R60.list(rest)), m, nx, fi, im, pg, lim, inp, Nil{}, _}, t, w)
  round.go(ret, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus,
    iv.of(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest, er, eo, en, iw))

def round.wit(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +regs: List<&2, U32>,
  +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>, +out: List<&2, U32>, +outn: U32,
  +t: C.Term, +w: Nat, inv: Inv(ds, ks, img, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}, t, w)) ->
  MV(ds, ks, img, C.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn}, t, w):
  (x, iw) = inv
  match x:
    case Wit{+ret, +focus, +fs, +foc, +sp, +pend, +ps, +rest}:
      round.iw(ds, ks, img, regs, m, nx, fi, im, out, outn, t, w, ret, focus, fs, foc, sp, pend, ps, rest, pg, lim, inp, iw)

# the move of a state of the invariant
def round.mv(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, st: C.Cir.State, +t: C.Term,
  +w: Nat, inv: Inv(ds, ks, img, st, t, w)) -> MV(ds, ks, img, st, t, w):
  match st:
    case C.Cir.State{+regs, +m, +nx, +fi, +im, +pg, +lim, +inp, +out, +outn}:
      round.wit(ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, out, outn, t, w, inv)

# a round of the main loop, for any fuel: an admin move, a step, a halt that
# says what Eval gives, or out of memory
def round.post(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +st: C.Cir.State, +t: C.Term, +w: Nat, inv: Inv(ds, ks, img, st, t, w)) ->
  Post(False{}, C.Cir.exec(f, B.body(), st), s => Rnd(ds, ks, img, t, w, s), s => st2 => HR(ds, t, s, st2)):
  mv.post(f, ds, ks, img, st, t, w, round.mv(ds, ks, img, st, t, w, inv))

# a round of the main loop ends, with some fuel
def round.done(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +st: C.Cir.State,
  +t: C.Term, +w: Nat, inv: Inv(ds, ks, img, st, t, w)) -> Ex(Nat, f => Ends(C.Cir.exec(f, B.body(), st))):
  mv.done(ds, ks, img, st, t, w, round.mv(ds, ks, img, st, t, w, inv))

# The loop gives what Eval gives
# ------------------------------

# a weaker halt
def post.wk(dn: Bool, o: C.Cir.Out, -Q: C.Cir.State -> Type, -H1: U32 -> C.Cir.State -> Type,
  -H2: U32 -> C.Cir.State -> Type, h: Post(dn, o, Q, H1), hh: @s: U32 -> @st: C.Cir.State -> H1(s, st) -> H2(s, st)) ->
  Post(dn, o, Q, H2):
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
  %Equal.sym(Maybe<C.Term>, C.Eval.run(j, ds, None{}), None{}, run.none(j, ds)) : {C.Program.result(ds, _) == None{} : Maybe<&2, List<&2, U32>>}
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
def he.of(+ds: List<&2, C.Def>, +t: C.Term, -s: U32, -st: C.Cir.State, h: HR(ds, t, s, st)) -> HE(ds, t, s, st):
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
      res.nv(ds, t, vals.of(C.Eval.vals(ds, t, False{}), ds, t, u, {==}, es))
    case 1n+(+j):
      step.res(j, ds, t, u, None{}, es, g(j))

# a halt of the loop after a step says what Eval gives before the step
def he.step(+ds: List<&2, C.Def>, +t: C.Term, +u: C.Term, +es: {C.Eval.step(ds, t) == Some{u} : Maybe<C.Term>},
  -s: U32, -st: C.Cir.State, h: HE(ds, u, s, st)) -> HE(ds, t, s, st):
  match h:
    case Inl{x}:
      (e0, r) = x
      (+k, ek) = r
      Inl{(e0, (1n+k, step.res(k, ds, t, u, Some{List.reverse(&2, U32, St.out(st))}, es, ek)))}
    case Inr{x}:
      (e2, g) = x
      Inr{(e2, k => he.all(k, ds, t, u, es, g))}

# after a round that goes on: the loop from the next state, by ia after an
# admin move and by ist after a step
def loop.next(+p: Nat, +ds: List<&2, C.Def>, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, +u: C.Cir.State,
  +t: C.Term, -w: Nat, r: Rnd(ds, ks, img, t, w, u),
  ia: @w2: Nat -> Inv(ds, ks, img, u, t, w2) ->
    Post(False{}, C.Cir.exec(p, B.loop(), u), s => Empty, s => st2 => HE(ds, t, s, st2)),
  ist: @v: C.Term -> @w2: Nat -> Inv(ds, ks, img, u, v, w2) ->
    Post(False{}, C.Cir.exec(p, B.loop(), u), s => Empty, s => st2 => HE(ds, v, s, st2))) ->
  Post(False{}, C.Cir.exec(p, B.loop(), u), s => Empty, s => st2 => HE(ds, t, s, st2)):
  match r:
    case Inl{a}:
      (w2, r2) = a
      (inv2, lt) = r2
      ia(w2, inv2)
    case Inr{b}:
      (+v, r2) = b
      (+es, r3) = r2
      (w2, inv2) = r3
      post.wk(False{}, C.Cir.exec(p, B.loop(), u), s => Empty, s => st2 => HE(ds, v, s, st2), s => st2 => HE(ds, t, s, st2),
        ist(v, w2, inv2), s => st2 => h => he.step(ds, t, v, es, s, st2, h))

# the main loop, from a state of the invariant of the term t, halts only as
# HE says, with any fuel: by induction on the fuel
def loop.post(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +st: C.Cir.State,
  +t: C.Term, +w: Nat, inv: Inv(ds, ks, img, st, t, w)) ->
  Post(False{}, C.Cir.exec(f, B.loop(), st), s => Empty, s => st2 => HE(ds, t, s, st2)):
  match f:
    case 0n:
      Unit{}
    case 1n+p:
      post.then(False{}, C.Cir.exec(p, B.body(), st), u => C.Cir.exec(p, B.loop(), u), s => Rnd(ds, ks, img, t, w, s),
        s => Empty, s => st2 => HR(ds, t, s, st2), s => st2 => HE(ds, t, s, st2),
        round.post(p, ds, ks, img, st, t, w, inv),
        s => st2 => h => he.of(ds, t, s, st2, h),
        +u => r => loop.next(p, ds, ks, img, u, t, w, r, w2 => i2 => loop.post(p, ds, ks, img, u, t, w2, i2),
          v => w2 => i2 => loop.post(p, ds, ks, img, u, v, w2, i2)))

# The loop reaches what Eval reaches
# ----------------------------------

def good.ends(-o: List<&2, U32>, r: C.Cir.Out, g: Good(o, r)) -> Ends(r):
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

def good.then(-o: List<&2, U32>, r: C.Cir.Out, -k: C.Cir.State -> C.Cir.Out, g: Good(o, r)) ->
  Good(o, C.Cir.exec.then(r, k)):
  match r:
    case C.Cir.Out.next{st}:
      Empty.absurd(Good(o, k(st)), g)
    case C.Cir.Out.halt{s, st}:
      g
    case C.Cir.Out.out_of_memory{}:
      Unit{}
    case C.Cir.Out.trap{}:
      g
    case C.Cir.Out.not_done{}:
      g

def ends.eq(-a: C.Cir.Out, -b: C.Cir.Out, e: {a == b : C.Cir.Out}, d: Ends(b)) -> Ends(a):
  %Equal.sym(C.Cir.Out, a, b, e) : Ends(_)
  d

# a round that halts or runs out of memory with the fuel f0 ends the loop the
# same with 1 + f0
def out.fin(-o: List<&2, U32>, +f0: Nat, -st: C.Cir.State, r: C.Cir.Out, er: {C.Cir.exec(f0, B.body(), st) == r : C.Cir.Out},
  g: Good(o, r)) -> Good(o, C.Cir.exec(1n+f0, B.loop(), st)):
  %Equal.sym(C.Cir.Out, C.Cir.exec(f0, B.body(), st), r, er) : Good(o, C.Cir.exec.then(_, u => C.Cir.exec(f0, B.loop(), u)))
  good.then(o, r, u => C.Cir.exec(f0, B.loop(), u), g)

# a round that goes on with the fuel f0, then the loop with n1, are the loop
# with 1 + f0 + n1
def next.fin(+o: List<&2, U32>, +f0: Nat, +n1: Nat, +st: C.Cir.State, +u: C.Cir.State,
  +er: {C.Cir.exec(f0, B.body(), st) == C.Cir.Out.next{u} : C.Cir.Out},
  +g1: Good(o, C.Cir.exec(n1, B.loop(), u))) -> Good(o, C.Cir.exec(1n+Nat.add(f0, n1), B.loop(), st)):
  +n = Nat.add(f0, n1)
  +d0 = ends.eq(C.Cir.exec(f0, B.body(), st), C.Cir.Out.next{u}, er, Unit{})
  +e1 = Equal.trans(C.Cir.Out, C.Cir.Out.next{u}, C.Cir.exec(f0, B.body(), st), C.Cir.exec(n, B.body(), st),
    Equal.sym(C.Cir.Out, C.Cir.exec(f0, B.body(), st), C.Cir.Out.next{u}, er),
    mono(f0, n, B.body(), st, N.le_add_r(f0, n1), d0))
  +e2 = mono(n1, n, B.loop(), u, N.le_add_l(f0, n1), good.ends(o, C.Cir.exec(n1, B.loop(), u), g1))
  %e1 : Good(o, C.Cir.exec.then(_, v => C.Cir.exec(n, B.loop(), v)))
  %e2 : Good(o, _)
  g1

# a round that halts, from a term from which Eval reaches the bytes o: the
# loop gives them
def loop.halt(k: Nat, +ds: List<&2, C.Def>, +t: C.Term, -s: U32, +st2: C.Cir.State, +o: List<&2, U32>,
  e: {C.Program.result(ds, C.Eval.steps(k, ds, t)) == Some{o} : Maybe<&2, List<&2, U32>>},
  h: HR(ds, t, s, st2)) -> Good(o, C.Cir.Out.halt{s, st2}):
  match k:
    case 0n:
      match h:
        case Inl{x}:
          (e0, r) = x
          (es, er) = r
          (e0, mb.inj(List.reverse(&2, U32, St.out(st2)), o,
            Equal.trans(Maybe<&2, List<&2, U32>>, Some{List.reverse(&2, U32, St.out(st2))}, C.Program.result(ds, Some{t}), Some{o},
              Equal.sym(Maybe<&2, List<&2, U32>>, C.Program.result(ds, Some{t}), Some{List.reverse(&2, U32, St.out(st2))}, er), e)))
        case Inr{x}:
          (e2, r) = x
          (es, er) = r
          Empty.absurd(Good(o, C.Cir.Out.halt{s, st2}), mb.ne(o,
            Equal.trans(Maybe<&2, List<&2, U32>>, None{}, C.Program.result(ds, Some{t}), Some{o},
              Equal.sym(Maybe<&2, List<&2, U32>>, C.Program.result(ds, Some{t}), None{}, er), e)))
    case 1n+(+j):
      match h:
        case Inl{x}:
          (e0, r) = x
          (es, er) = r
          Empty.absurd(Good(o, C.Cir.Out.halt{s, st2}), mb.ne(o,
            Equal.trans(Maybe<&2, List<&2, U32>>, None{}, C.Program.result(ds, C.Eval.steps(1n+j, ds, t)), Some{o},
              Equal.sym(Maybe<&2, List<&2, U32>>, C.Program.result(ds, C.Eval.steps(1n+j, ds, t)), None{}, none.after(j, ds, t, es)), e)))
        case Inr{x}:
          (e2, r) = x
          (es, er) = r
          Empty.absurd(Good(o, C.Cir.Out.halt{s, st2}), mb.ne(o,
            Equal.trans(Maybe<&2, List<&2, U32>>, None{}, C.Program.result(ds, C.Eval.steps(1n+j, ds, t)), Some{o},
              Equal.sym(Maybe<&2, List<&2, U32>>, C.Program.result(ds, C.Eval.steps(1n+j, ds, t)), None{}, none.after(j, ds, t, es)), e)))

# a step from a term from which Eval reaches the bytes o at once: none
def loop.step0(+ds: List<&2, C.Def>, +t: C.Term, +u: C.Term, -o: List<&2, U32>,
  e: {C.Program.result(ds, Some{t}) == Some{o} : Maybe<&2, List<&2, U32>>},
  es: {C.Eval.step(ds, t) == Some{u} : Maybe<C.Term>}) -> Empty:
  mb.ne(o, Equal.trans(Maybe<&2, List<&2, U32>>, None{}, C.Program.result(ds, Some{t}), Some{o},
    Equal.sym(Maybe<&2, List<&2, U32>>, C.Program.result(ds, Some{t}), None{},
      res.nv(ds, t, vals.of(C.Eval.vals(ds, t, False{}), ds, t, u, {==}, es))), e))

# when Eval reaches the bytes o from t within k steps, the loop gives them or
# runs out of memory, with some fuel: by induction on k, and on b, above the
# measure of the admin moves; r0 is the round with the fuel f0, that ends
def loop.done(k: Nat, b: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +st: C.Cir.State, +t: C.Term, +w: Nat, +o: List<&2, U32>, +hw: N.Le(1n+w, b),
  +e: {C.Program.result(ds, C.Eval.steps(k, ds, t)) == Some{o} : Maybe<&2, List<&2, U32>>},
  +f0: Nat, r0: C.Cir.Out, +er: {C.Cir.exec(f0, B.body(), st) == r0 : C.Cir.Out}, d0: Ends(r0),
  p0: Post(False{}, r0, s => Rnd(ds, ks, img, t, w, s), s => st2 => HR(ds, t, s, st2))) ->
  Ex(Nat, n => Good(o, C.Cir.exec(n, B.loop(), st))):
  match k:
    case 0n:
      match b:
        case 0n:
          Empty.absurd(Ex(Nat, n => Good(o, C.Cir.exec(n, B.loop(), st))), hw)
        case 1n+(+c):
          match r0:
            case C.Cir.Out.next{+u}:
              match p0:
                case Inl{+a}:
                  +w2 = adm.w(ds, ks, img, u, t, w, a)
                  +inv2 = adm.inv(ds, ks, img, u, t, w, a)
                  +lt = adm.lt(ds, ks, img, u, t, w, a)
                  +rd = round.done(ds, ks, img, u, t, w2, inv2)
                  +f1 = Ex.fst(Nat, f => Ends(C.Cir.exec(f, B.body(), u)), rd)
                  +ld = loop.done(0n, c, ds, ks, img, u, t, w2, o, N.le_trans(1n+w2, w, c, lt, hw), e, f1,
                    C.Cir.exec(f1, B.body(), u), {==}, Ex.snd(Nat, f => Ends(C.Cir.exec(f, B.body(), u)), rd),
                    round.post(f1, ds, ks, img, u, t, w2, inv2))
                  +n1 = Ex.fst(Nat, n => Good(o, C.Cir.exec(n, B.loop(), u)), ld)
                  (1n+Nat.add(f0, n1), next.fin(o, f0, n1, st, u, er, Ex.snd(Nat, n => Good(o, C.Cir.exec(n, B.loop(), u)), ld)))
                case Inr{+x}:
                  +v = stp.u(ds, ks, img, u, t, x)
                  +es = stp.es(ds, ks, img, u, t, x)
                  +w2 = stp.w(ds, ks, img, u, t, x)
                  +inv2 = stp.inv(ds, ks, img, u, t, x)
                  Empty.absurd(Ex(Nat, n => Good(o, C.Cir.exec(n, B.loop(), st))), loop.step0(ds, t, v, o, e, es))
            case C.Cir.Out.halt{+s, +st2}:
              (1n+f0, out.fin(o, f0, st, C.Cir.Out.halt{s, st2}, er, loop.halt(0n, ds, t, s, st2, o, e, p0)))
            case C.Cir.Out.out_of_memory{}:
              (1n+f0, out.fin(o, f0, st, C.Cir.Out.out_of_memory{}, er, Unit{}))
            case C.Cir.Out.trap{}:
              Empty.absurd(Ex(Nat, n => Good(o, C.Cir.exec(n, B.loop(), st))), p0)
            case C.Cir.Out.not_done{}:
              Empty.absurd(Ex(Nat, n => Good(o, C.Cir.exec(n, B.loop(), st))), d0)
    case 1n+(+j):
      match b:
        case 0n:
          Empty.absurd(Ex(Nat, n => Good(o, C.Cir.exec(n, B.loop(), st))), hw)
        case 1n+(+c):
          match r0:
            case C.Cir.Out.next{+u}:
              match p0:
                case Inl{+a}:
                  +w2 = adm.w(ds, ks, img, u, t, w, a)
                  +inv2 = adm.inv(ds, ks, img, u, t, w, a)
                  +lt = adm.lt(ds, ks, img, u, t, w, a)
                  +rd = round.done(ds, ks, img, u, t, w2, inv2)
                  +f1 = Ex.fst(Nat, f => Ends(C.Cir.exec(f, B.body(), u)), rd)
                  +ld = loop.done(1n+j, c, ds, ks, img, u, t, w2, o, N.le_trans(1n+w2, w, c, lt, hw), e, f1,
                    C.Cir.exec(f1, B.body(), u), {==}, Ex.snd(Nat, f => Ends(C.Cir.exec(f, B.body(), u)), rd),
                    round.post(f1, ds, ks, img, u, t, w2, inv2))
                  +n1 = Ex.fst(Nat, n => Good(o, C.Cir.exec(n, B.loop(), u)), ld)
                  (1n+Nat.add(f0, n1), next.fin(o, f0, n1, st, u, er, Ex.snd(Nat, n => Good(o, C.Cir.exec(n, B.loop(), u)), ld)))
                case Inr{+x}:
                  +v = stp.u(ds, ks, img, u, t, x)
                  +es = stp.es(ds, ks, img, u, t, x)
                  +w2 = stp.w(ds, ks, img, u, t, x)
                  +inv2 = stp.inv(ds, ks, img, u, t, x)
                  +rd = round.done(ds, ks, img, u, v, w2, inv2)
                  +f1 = Ex.fst(Nat, f => Ends(C.Cir.exec(f, B.body(), u)), rd)
                  +ld = loop.done(j, 1n+w2, ds, ks, img, u, v, w2, o, N.le_refl(1n+w2), res.step(j, ds, t, v, Some{o}, es, e), f1,
                    C.Cir.exec(f1, B.body(), u), {==}, Ex.snd(Nat, f => Ends(C.Cir.exec(f, B.body(), u)), rd),
                    round.post(f1, ds, ks, img, u, v, w2, inv2))
                  +n1 = Ex.fst(Nat, n => Good(o, C.Cir.exec(n, B.loop(), u)), ld)
                  (1n+Nat.add(f0, n1), next.fin(o, f0, n1, st, u, er, Ex.snd(Nat, n => Good(o, C.Cir.exec(n, B.loop(), u)), ld)))
            case C.Cir.Out.halt{+s, +st2}:
              (1n+f0, out.fin(o, f0, st, C.Cir.Out.halt{s, st2}, er, loop.halt(1n+j, ds, t, s, st2, o, e, p0)))
            case C.Cir.Out.out_of_memory{}:
              (1n+f0, out.fin(o, f0, st, C.Cir.Out.out_of_memory{}, er, Unit{}))
            case C.Cir.Out.trap{}:
              Empty.absurd(Ex(Nat, n => Good(o, C.Cir.exec(n, B.loop(), st))), p0)
            case C.Cir.Out.not_done{}:
              Empty.absurd(Ex(Nat, n => Good(o, C.Cir.exec(n, B.loop(), st))), d0)

# the loop, from a state of the invariant
def loop.start(k: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +st: C.Cir.State, +t: C.Term, +w: Nat, +o: List<&2, U32>, +inv: Inv(ds, ks, img, st, t, w),
  +e: {C.Program.result(ds, C.Eval.steps(k, ds, t)) == Some{o} : Maybe<&2, List<&2, U32>>}) ->
  Ex(Nat, n => Good(o, C.Cir.exec(n, B.loop(), st))):
  +rd = round.done(ds, ks, img, st, t, w, inv)
  +f0 = Ex.fst(Nat, f => Ends(C.Cir.exec(f, B.body(), st)), rd)
  loop.done(k, 1n+w, ds, ks, img, st, t, w, o, N.le_refl(1n+w), e, f0, C.Cir.exec(f0, B.body(), st), {==},
    Ex.snd(Nat, f => Ends(C.Cir.exec(f, B.body(), st)), rd), round.post(f0, ds, ks, img, st, t, w, inv))

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

def res.alloced(r: Maybe<&2, U32>, fuel: Nat, prog: C.Cir.Stmt, +regs: Nat, +cells: List<&2, C.Cir.Cell>, +k: U32,
  +len: U32, +lim: U32, +i: List<&2, U32>, +m: U32, -P: C.Wasm.Outcome -> Type, po: P(C.Wasm.Outcome.out_of_memory{}),
  ek: {k == C.Wasm.encode.len(C.Cir.Cell, cells) : U32},
  em: {U32.is_le(C.Cir.pages(C.Cir.input.at(k)), m) == True{} : Bool},
  elim: {lim == C.Wasm.min(m, 65536) : U32},
  el: {C.Wasm.length32(i) == Some{len} : Maybe<&2, U32>},
  er: {C.Cir.alloc.pages(k, len, C.Cir.pages(C.Cir.input.at(k)), lim) == r : Maybe<&2, U32>},
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    P(C.Cir.ended(C.Cir.exec(fuel, prog, St0(regs, cells, first2, k2, p2, lim2, i))))) ->
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
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    P(C.Cir.ended(C.Cir.exec(fuel, prog, St0(regs, cells, first2, k2, p2, lim2, i))))) ->
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
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    P(C.Cir.ended(C.Cir.exec(fuel, prog, St0(regs, cells, first2, k2, p2, lim2, i))))) ->
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
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    P(C.Cir.ended(C.Cir.exec(fuel, prog, St0(regs, cells, first2, k2, p2, lim2, i))))) ->
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
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    &n: Nat -> P(C.Cir.ended(C.Cir.exec(n, prog, St0(regs, cells, first2, k2, p2, lim2, i))))) ->
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
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    &n: Nat -> P(C.Cir.ended(C.Cir.exec(n, prog, St0(regs, cells, first2, k2, p2, lim2, i))))) ->
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
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    &n: Nat -> P(C.Cir.ended(C.Cir.exec(n, prog, St0(regs, cells, first2, k2, p2, lim2, i))))) ->
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
  g: @k2: U32 -> @len2: U32 -> @p2: U32 -> @lim2: U32 -> @first2: U32 -> Start(cells, i, m, k2, len2, p2, lim2, first2) ->
    &n: Nat -> P(C.Cir.ended(C.Cir.exec(n, prog, St0(regs, cells, first2, k2, p2, lim2, i))))) ->
  &n: Nat -> P(C.Cir.result(n, prog, regs, cells, i, m)):
  rex.memory(U32.is_le(C.Cir.pages(C.Cir.input.at(C.Wasm.encode.len(C.Cir.Cell, cells))), m), prog, regs, cells,
    C.Wasm.encode.len(C.Cir.Cell, cells), C.Wasm.min(m, 65536), i, m, P, po, {==}, {==}, {==}, g)

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

# Open: the start (proof_in.bend). From St0, with the image of a book that
# Book.read reads, M.input ends with InvIn, or runs out of memory, for any
# fuel; and with some fuel it ends.
def input.post(+f: Nat, +p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +k: U32, +len: U32,
  +pg: U32, +lim: U32, +first: U32,
  rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  small: {C.Img.small(p, 0) == True{} : Bool},
  s: Start(C.Img.cells(ds), i, m, k, len, pg, lim, first)) ->
  Post(False{}, C.Cir.exec(f, C.M.input(), St0(C.Mach.regs(), C.Img.cells(ds), first, k, pg, lim, i)),
    st => InvIn(ds, i, st), s2 => st2 => Empty):
  ?TODO

def input.done(+p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +k: U32, +len: U32,
  +pg: U32, +lim: U32, +first: U32,
  rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  small: {C.Img.small(p, 0) == True{} : Bool},
  s: Start(C.Img.cells(ds), i, m, k, len, pg, lim, first)) ->
  Ex(Nat, f => Ends(C.Cir.exec(f, C.M.input(), St0(C.Mach.regs(), C.Img.cells(ds), first, k, pg, lim, i)))):
  ?TODO

# The machine gives what Eval gives
# ---------------------------------

def run.loop(+n: Nat, +ds: List<&2, C.Def>, +i: List<&2, U32>, +st2: C.Cir.State,
  q: Ex(Nat, w => Inv(ds, T.tm.names(ds), T.tm.img(ds), st2, C.Program.start(i), w))) ->
  Post(False{}, C.Cir.exec(n, C.Cir.Stmt.seq{B.loop(), C.Cir.Stmt.nop{}}, st2), st => Unit,
    s2 => st3 => HE(ds, C.Program.start(i), s2, st3)):
  (w, inv) = q
  post.seq(n, False{}, B.loop(), C.Cir.Stmt.nop{}, st2, s => Empty, s => Unit, s2 => st3 => HE(ds, C.Program.start(i), s2, st3),
    s2 => st3 => HE(ds, C.Program.start(i), s2, st3),
    loop.post(n, ds, T.tm.names(ds), T.tm.img(ds), st2, C.Program.start(i), w, inv),
    s2 => st3 => h => h, st3 => h => Empty.absurd(Post(False{}, C.Cir.exec(n, C.Cir.Stmt.nop{}, st3), s => Unit,
      s2 => st4 => HE(ds, C.Program.start(i), s2, st4)), h))

def run.rest(+n: Nat, +ds: List<&2, C.Def>, +i: List<&2, U32>, +st1: C.Cir.State, q1: InvIn(ds, i, st1)) ->
  Post(False{}, C.Cir.exec(n, B.rest(), st1), st => Unit, s2 => st2 => HE(ds, C.Program.start(i), s2, st2)):
  (len, ex) = q1
  post.seq(n, False{}, C.M.set(C.R.mode(), C.M.c(0)), C.Cir.Stmt.seq{B.loop(), C.Cir.Stmt.nop{}}, st1,
    st2 => Ex(Nat, w => Inv(ds, T.tm.names(ds), T.tm.img(ds), st2, C.Program.start(i), w)), st => Unit,
    s2 => st2 => Empty, s2 => st2 => HE(ds, C.Program.start(i), s2, st2),
    (%Equal.sym(C.Cir.Out, C.Cir.exec(n, C.M.set(C.R.mode(), C.M.c(0)), st1), C.Cir.Out.next{Mode0(st1)}, setmode(n, st1, len)) :
      Post(False{}, _, st2 => Ex(Nat, w => Inv(ds, T.tm.names(ds), T.tm.img(ds), st2, C.Program.start(i), w)), s2 => st2 => Empty);
     ex),
    s2 => st2 => h => Empty.absurd(HE(ds, C.Program.start(i), s2, st2), h),
    st2 => q2 => run.loop(n, ds, i, st2, q2))

# a run of Mach.code from the start halts only as HE says, from Program.start
def run.post(+n: Nat, +p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +k: U32, +len: U32,
  +pg: U32, +lim: U32, +first: U32,
  rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  small: {C.Img.small(p, 0) == True{} : Bool},
  s: Start(C.Img.cells(ds), i, m, k, len, pg, lim, first)) ->
  Post(False{}, C.Cir.exec(n, C.Mach.code(), St0(C.Mach.regs(), C.Img.cells(ds), first, k, pg, lim, i)), st => Unit,
    s2 => st2 => HE(ds, C.Program.start(i), s2, st2)):
  post.seq(n, False{}, C.M.input(), B.rest(), St0(C.Mach.regs(), C.Img.cells(ds), first, k, pg, lim, i),
    st => InvIn(ds, i, st), st => Unit, s2 => st2 => Empty, s2 => st2 => HE(ds, C.Program.start(i), s2, st2),
    input.post(n, p, ds, i, m, k, len, pg, lim, first, rd, small, s),
    s2 => st2 => h => Empty.absurd(HE(ds, C.Program.start(i), s2, st2), h),
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
  h: Post(False{}, o, st => Unit, s => st2 => HE(ds, t, s, st2))) ->
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
  h: Post(False{}, o, st => Unit, s => st2 => HE(ds, t, s, st2)),
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
def good.end(+o: List<&2, U32>, r: C.Cir.Out, g: Good(o, r)) ->
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
  +len: {List.length(&2, U32, St.regs(st1)) == 64n : Nat},
  +g2: Good(o, C.Cir.exec(n2, B.loop(), Mode0(st1)))) -> Good(o, C.Cir.exec(1n+Nat.add(f1, n2), C.Mach.code(), st0)):
  +n = {1n+Nat.add(f1, n2) : Nat}
  +d1 = ends.eq(C.Cir.exec(f1, C.M.input(), st0), C.Cir.Out.next{st1}, er1, Unit{})
  +e1 = Equal.trans(C.Cir.Out, C.Cir.Out.next{st1}, C.Cir.exec(f1, C.M.input(), st0), C.Cir.exec(n, C.M.input(), st0),
    Equal.sym(C.Cir.Out, C.Cir.exec(f1, C.M.input(), st0), C.Cir.Out.next{st1}, er1),
    mono(f1, n, C.M.input(), st0, N.le_succ(f1, Nat.add(f1, n2), N.le_add_r(f1, n2)), d1))
  +e2 = Equal.sym(C.Cir.Out, C.Cir.exec(n, C.M.set(C.R.mode(), C.M.c(0)), st1), C.Cir.Out.next{Mode0(st1)}, setmode(n, st1, len))
  +e3 = mono(n2, n, B.loop(), Mode0(st1), N.le_succ(n2, Nat.add(f1, n2), N.le_add_l(f1, n2)),
    good.ends(o, C.Cir.exec(n2, B.loop(), Mode0(st1)), g2))
  %e1 : Good(o, C.Cir.exec.then(_, s1 => C.Cir.exec(n, B.rest(), s1)))
  %e2 : Good(o, C.Cir.exec.then(_, s2 => C.Cir.exec(n, C.Cir.Stmt.seq{B.loop(), C.Cir.Stmt.nop{}}, s2)))
  %e3 : Good(o, C.Cir.exec.then(_, s3 => C.Cir.exec(n, C.Cir.Stmt.nop{}, s3)))
  good.then(o, C.Cir.exec(n2, B.loop(), Mode0(st1)), s3 => C.Cir.exec(n, C.Cir.Stmt.nop{}, s3), g2)

# M.input that runs out of memory with the fuel f1 ends Mach.code so with 1 + f1
def oom.fin(-o: List<&2, U32>, +f1: Nat, +st0: C.Cir.State,
  er1: {C.Cir.exec(f1, C.M.input(), st0) == C.Cir.Out.out_of_memory{} : C.Cir.Out}) ->
  Good(o, C.Cir.exec(1n+f1, C.Mach.code(), st0)):
  +n = {1n+f1 : Nat}
  +er = er1
  +e1 = Equal.trans(C.Cir.Out, C.Cir.Out.out_of_memory{}, C.Cir.exec(f1, C.M.input(), st0), C.Cir.exec(n, C.M.input(), st0),
    Equal.sym(C.Cir.Out, C.Cir.exec(f1, C.M.input(), st0), C.Cir.Out.out_of_memory{}, er),
    mono(f1, n, C.M.input(), st0, N.le_succ(f1, f1, N.le_refl(f1)), ends.eq(C.Cir.exec(f1, C.M.input(), st0), C.Cir.Out.out_of_memory{}, er, Unit{})))
  %e1 : Good(o, C.Cir.exec.then(_, s1 => C.Cir.exec(n, B.rest(), s1)))
  Unit{}

def run.next(k: Nat, +ds: List<&2, C.Def>, +i: List<&2, U32>, +o: List<&2, U32>, +f1: Nat, +st0: C.Cir.State,
  +st1: C.Cir.State, +er1: {C.Cir.exec(f1, C.M.input(), st0) == C.Cir.Out.next{st1} : C.Cir.Out},
  +len: {List.length(&2, U32, St.regs(st1)) == 64n : Nat}, +w: Nat,
  +inv: Inv(ds, T.tm.names(ds), T.tm.img(ds), Mode0(st1), C.Program.start(i), w),
  +e: {C.Program.result(ds, C.Eval.steps(k, ds, C.Program.start(i))) == Some{o} : Maybe<&2, List<&2, U32>>}) ->
  Ex(Nat, n => Good(o, C.Cir.exec(n, C.Mach.code(), st0))):
  +ls = loop.start(k, ds, T.tm.names(ds), T.tm.img(ds), Mode0(st1), C.Program.start(i), w, o, inv, e)
  +n2 = Ex.fst(Nat, n => Good(o, C.Cir.exec(n, B.loop(), Mode0(st1))), ls)
  (1n+Nat.add(f1, n2), run.fin(o, f1, n2, st0, st1, er1, len, Ex.snd(Nat, n => Good(o, C.Cir.exec(n, B.loop(), Mode0(st1))), ls)))

def run.done.r(k: Nat, +ds: List<&2, C.Def>, +i: List<&2, U32>, +o: List<&2, U32>, +f1: Nat, +st0: C.Cir.State,
  r1: C.Cir.Out, +er1: {C.Cir.exec(f1, C.M.input(), st0) == r1 : C.Cir.Out}, d1: Ends(r1),
  p1: Post(False{}, r1, st => InvIn(ds, i, st), s2 => st2 => Empty),
  +e: {C.Program.result(ds, C.Eval.steps(k, ds, C.Program.start(i))) == Some{o} : Maybe<&2, List<&2, U32>>}) ->
  Ex(Nat, n => Good(o, C.Cir.exec(n, C.Mach.code(), st0))):
  match r1:
    case C.Cir.Out.next{+st1}:
      (len, q) = p1
      (w, inv) = q
      run.next(k, ds, i, o, f1, st0, st1, er1, len, w, inv, e)
    case C.Cir.Out.halt{s, st}:
      Empty.absurd(Ex(Nat, n => Good(o, C.Cir.exec(n, C.Mach.code(), st0))), p1)
    case C.Cir.Out.out_of_memory{}:
      (1n+f1, oom.fin(o, f1, st0, er1))
    case C.Cir.Out.trap{}:
      Empty.absurd(Ex(Nat, n => Good(o, C.Cir.exec(n, C.Mach.code(), st0))), p1)
    case C.Cir.Out.not_done{}:
      Empty.absurd(Ex(Nat, n => Good(o, C.Cir.exec(n, C.Mach.code(), st0))), d1)

# when Eval reaches the bytes o from Program.start(i), a run of Mach.code from
# the start gives them, or runs out of memory, with some fuel
def run.done(k: Nat, +p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +o: List<&2, U32>, +kk: U32,
  +len: U32, +pg: U32, +lim: U32, +first: U32,
  +rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  +small: {C.Img.small(p, 0) == True{} : Bool},
  +s: Start(C.Img.cells(ds), i, m, kk, len, pg, lim, first),
  +e: {C.Program.result(ds, C.Eval.steps(k, ds, C.Program.start(i))) == Some{o} : Maybe<&2, List<&2, U32>>}) ->
  Ex(Nat, n => Good(o, C.Cir.exec(n, C.Mach.code(), St0(C.Mach.regs(), C.Img.cells(ds), first, kk, pg, lim, i)))):
  +st0 = St0(C.Mach.regs(), C.Img.cells(ds), first, kk, pg, lim, i)
  +id = input.done(p, ds, i, m, kk, len, pg, lim, first, rd, small, s)
  +f1 = Ex.fst(Nat, f => Ends(C.Cir.exec(f, C.M.input(), st0)), id)
  run.done.r(k, ds, i, o, f1, st0, C.Cir.exec(f1, C.M.input(), st0), {==}, Ex.snd(Nat, f => Ends(C.Cir.exec(f, C.M.input(), st0)), id),
    input.post(f1, p, ds, i, m, kk, len, pg, lim, first, rd, small, s), e)

def comp.of(k: Nat, +p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +o: List<&2, U32>, +kk: U32,
  +len: U32, +pg: U32, +lim: U32, +first: U32,
  +rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  +small: {C.Img.small(p, 0) == True{} : Bool},
  +s: Start(C.Img.cells(ds), i, m, kk, len, pg, lim, first),
  +e: {C.Program.result(ds, C.Eval.steps(k, ds, C.Program.start(i))) == Some{o} : Maybe<&2, List<&2, U32>>}) ->
  &n: Nat -> Or({C.Cir.ended(C.Cir.exec(n, C.Mach.code(), St0(C.Mach.regs(), C.Img.cells(ds), first, kk, pg, lim, i))) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome},
    {C.Cir.ended(C.Cir.exec(n, C.Mach.code(), St0(C.Mach.regs(), C.Img.cells(ds), first, kk, pg, lim, i))) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}):
  +st0 = St0(C.Mach.regs(), C.Img.cells(ds), first, kk, pg, lim, i)
  +rn = run.done(k, p, ds, i, m, o, kk, len, pg, lim, first, rd, small, s, e)
  +n = Ex.fst(Nat, n => Good(o, C.Cir.exec(n, C.Mach.code(), st0)), rn)
  (n, good.end(o, C.Cir.exec(n, C.Mach.code(), st0), Ex.snd(Nat, n => Good(o, C.Cir.exec(n, C.Mach.code(), st0)), rn)))

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
      safe.end(C.Cir.exec(n, C.Mach.code(), St0(C.Mach.regs(), C.Img.cells(ds), first, kk, pg, lim, i)), ds, C.Program.start(i),
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
      sound.end(C.Cir.exec(n, C.Mach.code(), St0(C.Mach.regs(), C.Img.cells(ds), first, kk, pg, lim, i)), ds, C.Program.start(i), o,
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

# Open: a round keeps the machine's cells within the peak of its term
def round.peak(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +st: C.Cir.State, +t: C.Term, +w: Nat, inv: Inv(ds, ks, img, st, t, w)) ->
  Post(False{}, C.Cir.exec(f, B.body(), st), s => N.Le(Mem.cells(s), Nat.max(Mem.cells(st), Peak(t))), s => st2 => Unit):
  ?TODO

# Open: a round whose memory has room for the peak of its term, and for the
# output, does not run out of memory
def round.room(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +st: C.Cir.State, +t: C.Term, +w: Nat, inv: Inv(ds, ks, img, st, t, w),
  room: N.Le(Nat.add(Nat.mul(20n, Nat.add(U32.to_nat(St.first(st)), Nat.max(Mem.cells(st), Peak(t)))), C.Term.size(t)),
    U32.to_nat(U32.shln(C.Wasm.min(St.lim(st), 65536), 16n)))) ->
  NoOom(C.Cir.exec(f, B.body(), st)):
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
