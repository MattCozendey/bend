# compiler: layer B, Eval's meta-theory for the moves
# ===================================================
#
# What the moves of proof_mach.bend need of Eval: a value has no step
# (ev.stops, Lean's eval_value), and a focus with no step that is no value
# makes its frames' term so (ev.stuck). Both rest on walk.more: a walk of a
# case tree that does not wait for more arguments does not wait with more
# either (a walk that fails still fails; one that reaches its leaf still
# does).

import Base
import ./impl.bend as C
import ./proof_mach_defs.bend as D

# Kit
# ---

def ft(-G: Type, e: {True{} == False{} : Bool}) -> G:
  D.bool.ft(G, Equal.sym(Bool, True{}, False{}, e))

def and.l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def and.r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      D.bool.ft({b == True{} : Bool}, h)

def and.f(a: Bool, -b: Bool, h: {b == False{} : Bool}) -> {Bool.and(a, b) == False{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      {==}

# a step is not none
def sm.ne(-u: C.Term, e: {Some{u} == None{} : Maybe<C.Term>}) -> Empty:
  D.st.ne(u, Equal.sym(Maybe<C.Term>, Some{u}, None{}, e))

# x is True when y is, and y is False when x is
def bool.back(b: Bool, -x: Bool, -y: Bool, eb: {x == b : Bool}, more: {x == False{} : Bool} -> {y == False{} : Bool},
  hy: {y == True{} : Bool}) -> {x == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      D.bool.ft({x == True{} : Bool}, Equal.trans(Bool, False{}, y, True{}, Equal.sym(Bool, y, False{}, more(eb)), hy))

# A walk that does not wait does not wait with more arguments
# ------------------------------------------------------------

def w.if(b: Bool, -r: Maybe<Maybe<C.Term>>, -s: Maybe<Maybe<C.Term>>,
  h: {C.Eval.waits(C.Eval.walk.if(b, r)) == False{} : Bool},
  g: {C.Eval.waits(r) == False{} : Bool} -> {C.Eval.waits(s) == False{} : Bool}) ->
  {C.Eval.waits(C.Eval.walk.if(b, s)) == False{} : Bool}:
  match b:
    case True{}:
      g(h)
    case False{}:
      {==}

def w.pick(b: Bool, -r1: Maybe<Maybe<C.Term>>, -s1: Maybe<Maybe<C.Term>>, -r2: Maybe<Maybe<C.Term>>, -s2: Maybe<Maybe<C.Term>>,
  h: {C.Eval.waits(C.Eval.walk.pick(b, r1, s1)) == False{} : Bool},
  g1: {C.Eval.waits(r1) == False{} : Bool} -> {C.Eval.waits(r2) == False{} : Bool},
  g2: {C.Eval.waits(s1) == False{} : Bool} -> {C.Eval.waits(s2) == False{} : Bool}) ->
  {C.Eval.waits(C.Eval.walk.pick(b, r2, s2)) == False{} : Bool}:
  match b:
    case True{}:
      g1(h)
    case False{}:
      g2(h)

def w.app(b: Bool, -r: Maybe<Maybe<C.Term>>, -s: Maybe<Maybe<C.Term>>, -u: C.Term, -v: C.Term,
  h: {C.Eval.waits(C.Eval.walk.app(b, r, u)) == False{} : Bool},
  g: {C.Eval.waits(r) == False{} : Bool} -> {C.Eval.waits(s) == False{} : Bool}) ->
  {C.Eval.waits(C.Eval.walk.app(b, s, v)) == False{} : Bool}:
  match b:
    case True{}:
      g(h)
    case False{}:
      {==}

# the walk of the case tree t, with e bound, on xs then ys
def WM(t: C.Term, e: List<&2, C.Term>, xs: List<&2, C.Arg>, ys: List<&2, C.Arg>) -> Type:
  {C.Eval.waits(C.Eval.walk(t, e, List.append(&2, C.Arg, xs, ys))) == False{} : Bool}

def walk.more(t: C.Term, +e: List<&2, C.Term>, xs: List<&2, C.Arg>, +ys: List<&2, C.Arg>,
  h: {C.Eval.waits(C.Eval.walk(t, e, xs)) == False{} : Bool}) -> WM(t, e, xs, ys):
  match t:
    case C.Term.Var{+z0}:
      {==}
    case C.Term.Ref{+z0}:
      {==}
    case C.Term.Ann{+z0, +z1}:
      {==}
    case C.Term.Let{+z0, +z1, +z2}:
      {==}
    case C.Term.Typ{+z0}:
      {==}
    case C.Term.Min{+z0, +z1}:
      {==}
    case C.Term.All{+z0, +z1, +z2}:
      {==}
    case C.Term.Lam{+z0, +z1}:
      match xs:
        case Nil{}:
          ft(WM(C.Term.Lam{z0, z1}, e, Nil{}, ys), h)
        case Con{C.Arg{+q, +x}, +rest}:
          w.if(C.Quan.binds(z0, q, x), C.Eval.walk(z1, Con{x, e}, rest), C.Eval.walk(z1, Con{x, e}, List.append(&2, C.Arg, rest, ys)), h,
            hr => walk.more(z1, Con{x, e}, rest, ys, hr))
    case C.Term.App{+z0, +z1, +z2}:
      match z2:
        case C.Term.Var{+y0}:
          w.app(C.Term.takes(C.Term.head(z1)), C.Eval.walk(z1, e, Con{C.Arg{z0, C.Env.sub(e, y0)}, xs}),
            C.Eval.walk(z1, e, Con{C.Arg{z0, C.Env.sub(e, y0)}, List.append(&2, C.Arg, xs, ys)}),
            C.Term.spine(xs, C.Term.subst(C.Term.App{z0, z1, C.Term.Var{y0}}, e, 0n)),
            C.Term.spine(List.append(&2, C.Arg, xs, ys), C.Term.subst(C.Term.App{z0, z1, C.Term.Var{y0}}, e, 0n)), h,
            hr => walk.more(z1, e, Con{C.Arg{z0, C.Env.sub(e, y0)}, xs}, ys, hr))
        case C.Term.Ref{+y0}:
          {==}
        case C.Term.Ann{+y0, +y1}:
          {==}
        case C.Term.Let{+y0, +y1, +y2}:
          {==}
        case C.Term.Typ{+y0}:
          {==}
        case C.Term.Min{+y0, +y1}:
          {==}
        case C.Term.All{+y0, +y1, +y2}:
          {==}
        case C.Term.Lam{+y0, +y1}:
          {==}
        case C.Term.App{+y0, +y1, +y2}:
          {==}
        case C.Term.Sig{+y0, +y1, +y2}:
          {==}
        case C.Term.Tup{+y0, +y1, +y2}:
          {==}
        case C.Term.Prj{+y0}:
          {==}
        case C.Term.Enu{+y0}:
          {==}
        case C.Term.Lab{+y0}:
          {==}
        case C.Term.Mat{+y0, +y1, +y2}:
          {==}
        case C.Term.Efq{}:
          {==}
        case C.Term.Eql{+y0, +y1, +y2}:
          {==}
        case C.Term.Rfl{}:
          {==}
        case C.Term.Rwt{+y0, +y1, +y2}:
          {==}
    case C.Term.Sig{+z0, +z1, +z2}:
      {==}
    case C.Term.Tup{+z0, +z1, +z2}:
      {==}
    case C.Term.Prj{+z0}:
      match xs:
        case Nil{}:
          ft(WM(C.Term.Prj{z0}, e, Nil{}, ys), h)
        case Con{C.Arg{+q, +x}, +rest}:
          match x:
            case C.Term.Var{+y0}:
              {==}
            case C.Term.Ref{+y0}:
              {==}
            case C.Term.Ann{+y0, +y1}:
              {==}
            case C.Term.Let{+y0, +y1, +y2}:
              {==}
            case C.Term.Typ{+y0}:
              {==}
            case C.Term.Min{+y0, +y1}:
              {==}
            case C.Term.All{+y0, +y1, +y2}:
              {==}
            case C.Term.Lam{+y0, +y1}:
              {==}
            case C.Term.App{+y0, +y1, +y2}:
              {==}
            case C.Term.Sig{+y0, +y1, +y2}:
              {==}
            case C.Term.Tup{+y0, +y1, +y2}:
              w.if(C.Quan.live(q), C.Eval.walk(z0, e, Con{C.Arg{C.Quan.fld(y0, q), y1}, Con{C.Arg{q, y2}, rest}}),
                C.Eval.walk(z0, e, Con{C.Arg{C.Quan.fld(y0, q), y1}, Con{C.Arg{q, y2}, List.append(&2, C.Arg, rest, ys)}}), h,
                hr => walk.more(z0, e, Con{C.Arg{C.Quan.fld(y0, q), y1}, Con{C.Arg{q, y2}, rest}}, ys, hr))
            case C.Term.Prj{+y0}:
              {==}
            case C.Term.Enu{+y0}:
              {==}
            case C.Term.Lab{+y0}:
              {==}
            case C.Term.Mat{+y0, +y1, +y2}:
              {==}
            case C.Term.Efq{}:
              {==}
            case C.Term.Eql{+y0, +y1, +y2}:
              {==}
            case C.Term.Rfl{}:
              {==}
            case C.Term.Rwt{+y0, +y1, +y2}:
              {==}
    case C.Term.Enu{+z0}:
      {==}
    case C.Term.Lab{+z0}:
      {==}
    case C.Term.Mat{+z0, +z1, +z2}:
      match xs:
        case Nil{}:
          ft(WM(C.Term.Mat{z0, z1, z2}, e, Nil{}, ys), h)
        case Con{C.Arg{+q, +x}, +rest}:
          match x:
            case C.Term.Var{+y0}:
              {==}
            case C.Term.Ref{+y0}:
              {==}
            case C.Term.Ann{+y0, +y1}:
              {==}
            case C.Term.Let{+y0, +y1, +y2}:
              {==}
            case C.Term.Typ{+y0}:
              {==}
            case C.Term.Min{+y0, +y1}:
              {==}
            case C.Term.All{+y0, +y1, +y2}:
              {==}
            case C.Term.Lam{+y0, +y1}:
              {==}
            case C.Term.App{+y0, +y1, +y2}:
              {==}
            case C.Term.Sig{+y0, +y1, +y2}:
              {==}
            case C.Term.Tup{+y0, +y1, +y2}:
              {==}
            case C.Term.Prj{+y0}:
              {==}
            case C.Term.Enu{+y0}:
              {==}
            case C.Term.Lab{+y0}:
              w.if(C.Quan.live(q), C.Eval.walk.pick(C.Name.is_eq(y0, z0), C.Eval.walk(z1, e, rest), C.Eval.walk(z2, e, Con{C.Arg{q, C.Term.Lab{y0}}, rest})),
                C.Eval.walk.pick(C.Name.is_eq(y0, z0), C.Eval.walk(z1, e, List.append(&2, C.Arg, rest, ys)), C.Eval.walk(z2, e, Con{C.Arg{q, C.Term.Lab{y0}}, List.append(&2, C.Arg, rest, ys)})), h,
                hr => w.pick(C.Name.is_eq(y0, z0), C.Eval.walk(z1, e, rest), C.Eval.walk(z2, e, Con{C.Arg{q, C.Term.Lab{y0}}, rest}),
                  C.Eval.walk(z1, e, List.append(&2, C.Arg, rest, ys)), C.Eval.walk(z2, e, Con{C.Arg{q, C.Term.Lab{y0}}, List.append(&2, C.Arg, rest, ys)}), hr,
                  a1 => walk.more(z1, e, rest, ys, a1), a2 => walk.more(z2, e, Con{C.Arg{q, C.Term.Lab{y0}}, rest}, ys, a2)))
            case C.Term.Mat{+y0, +y1, +y2}:
              {==}
            case C.Term.Efq{}:
              {==}
            case C.Term.Eql{+y0, +y1, +y2}:
              {==}
            case C.Term.Rfl{}:
              {==}
            case C.Term.Rwt{+y0, +y1, +y2}:
              {==}
    case C.Term.Efq{}:
      match xs:
        case Nil{}:
          ft(WM(C.Term.Efq{}, e, Nil{}, ys), h)
        case Con{+x, +rest}:
          {==}
    case C.Term.Eql{+z0, +z1, +z2}:
      {==}
    case C.Term.Rfl{}:
      {==}
    case C.Term.Rwt{+z0, +z1, +z2}:
      {==}

# the same for a call's walk, from the head of its spine
def cwd.more(mb: Maybe<C.Def>, xs: List<&2, C.Arg>, +ys: List<&2, C.Arg>,
  h: {C.Eval.waits(C.Eval.callWalk.def(mb, xs)) == False{} : Bool}) ->
  {C.Eval.waits(C.Eval.callWalk.def(mb, List.append(&2, C.Arg, xs, ys))) == False{} : Bool}:
  match mb:
    case None{}:
      {==}
    case Some{C.Def{+k, +T, +v, +o}}:
      walk.more(v, Nil{}, xs, ys, h)

def cwh.more(+ds: List<&2, C.Def>, hd: C.Term, xs: List<&2, C.Arg>, +ys: List<&2, C.Arg>,
  h: {C.Eval.waits(C.Eval.callWalk.head(ds, hd, xs)) == False{} : Bool}) ->
  {C.Eval.waits(C.Eval.callWalk.head(ds, hd, List.append(&2, C.Arg, xs, ys))) == False{} : Bool}:
  match hd:
    case C.Term.Var{+z0}:
      {==}
    case C.Term.Ref{+z0}:
      cwd.more(C.Book.get(ds, z0), xs, ys, h)
    case C.Term.Ann{+z0, +z1}:
      {==}
    case C.Term.Let{+z0, +z1, +z2}:
      {==}
    case C.Term.Typ{+z0}:
      {==}
    case C.Term.Min{+z0, +z1}:
      {==}
    case C.Term.All{+z0, +z1, +z2}:
      {==}
    case C.Term.Lam{+z0, +z1}:
      {==}
    case C.Term.App{+z0, +z1, +z2}:
      {==}
    case C.Term.Sig{+z0, +z1, +z2}:
      {==}
    case C.Term.Tup{+z0, +z1, +z2}:
      {==}
    case C.Term.Prj{+z0}:
      {==}
    case C.Term.Enu{+z0}:
      {==}
    case C.Term.Lab{+z0}:
      {==}
    case C.Term.Mat{+z0, +z1, +z2}:
      {==}
    case C.Term.Efq{}:
      {==}
    case C.Term.Eql{+z0, +z1, +z2}:
      {==}
    case C.Term.Rfl{}:
      {==}
    case C.Term.Rwt{+z0, +z1, +z2}:
      {==}

# the arguments of a spine, in front of xs then ys
def args.app(t: C.Term, xs: List<&2, C.Arg>, +ys: List<&2, C.Arg>) ->
  {C.Term.args(t, List.append(&2, C.Arg, xs, ys)) == List.append(&2, C.Arg, C.Term.args(t, xs), ys) : List<&2, C.Arg>}:
  match t:
    case C.Term.Var{+z0}:
      {==}
    case C.Term.Ref{+z0}:
      {==}
    case C.Term.Ann{+z0, +z1}:
      {==}
    case C.Term.Let{+z0, +z1, +z2}:
      {==}
    case C.Term.Typ{+z0}:
      {==}
    case C.Term.Min{+z0, +z1}:
      {==}
    case C.Term.All{+z0, +z1, +z2}:
      {==}
    case C.Term.Lam{+z0, +z1}:
      {==}
    case C.Term.App{+z0, +z1, +z2}:
      args.app(z1, Con{C.Arg{z0, z2}, xs}, ys)
    case C.Term.Sig{+z0, +z1, +z2}:
      {==}
    case C.Term.Tup{+z0, +z1, +z2}:
      {==}
    case C.Term.Prj{+z0}:
      {==}
    case C.Term.Enu{+z0}:
      {==}
    case C.Term.Lab{+z0}:
      {==}
    case C.Term.Mat{+z0, +z1, +z2}:
      {==}
    case C.Term.Efq{}:
      {==}
    case C.Term.Eql{+z0, +z1, +z2}:
      {==}
    case C.Term.Rfl{}:
      {==}
    case C.Term.Rwt{+z0, +z1, +z2}:
      {==}

# a call's walk that does not wait does not wait with one more argument
def cw.app(+ds: List<&2, C.Def>, +u: C.Term, +q: C.Quan, +a: C.Term,
  h: {C.Eval.waits(C.Eval.callWalk(ds, u)) == False{} : Bool}) ->
  {C.Eval.waits(C.Eval.callWalk(ds, C.Term.App{q, u, a})) == False{} : Bool}:
  %Equal.sym(List<&2, C.Arg>, C.Term.args(u, List.append(&2, C.Arg, Nil{}, [C.Arg{q, a}])), List.append(&2, C.Arg, C.Term.args(u, Nil{}), [C.Arg{q, a}]),
    args.app(u, Nil{}, [C.Arg{q, a}])) : {C.Eval.waits(C.Eval.callWalk.head(ds, C.Term.head(u), _)) == False{} : Bool}
  cwh.more(ds, C.Term.head(u), C.Term.args(u, Nil{}), [C.Arg{q, a}], h)

def cw.acc(+ds: List<&2, C.Def>, +f: C.Term, +acc: List<&2, C.Arg>,
  hw: {C.Eval.waits(C.Eval.callWalk.head(ds, C.Term.head(f), C.Term.args(f, acc))) == True{} : Bool}) ->
  {C.Eval.waits(C.Eval.callWalk.head(ds, C.Term.head(f), List.append(&2, C.Arg, C.Term.args(f, Nil{}), acc))) == True{} : Bool}:
  %args.app(f, Nil{}, acc) : {C.Eval.waits(C.Eval.callWalk.head(ds, C.Term.head(f), _)) == True{} : Bool}
  hw

# a call's walk that waits with more arguments waits with none
def cw.back(+ds: List<&2, C.Def>, +f: C.Term, +acc: List<&2, C.Arg>,
  hw: {C.Eval.waits(C.Eval.callWalk.head(ds, C.Term.head(f), C.Term.args(f, acc))) == True{} : Bool}) ->
  {C.Eval.waits(C.Eval.callWalk(ds, f)) == True{} : Bool}:
  +hw2 = cw.acc(ds, f, acc, hw)
  bool.back(C.Eval.waits(C.Eval.callWalk(ds, f)), C.Eval.waits(C.Eval.callWalk(ds, f)),
    C.Eval.waits(C.Eval.callWalk.head(ds, C.Term.head(f), List.append(&2, C.Arg, C.Term.args(f, Nil{}), acc))), {==},
    e => cwh.more(ds, C.Term.head(f), C.Term.args(f, Nil{}), acc, e), hw2)

# Values
# ------

# a spine of a def on arguments that are values is a value when its walk waits
def vals.tf(+ds: List<&2, C.Def>, u: C.Term, ht: {C.Eval.vals(ds, u, True{}) == True{} : Bool}) ->
  {C.Eval.vals(ds, u, False{}) == C.Eval.waits(C.Eval.callWalk(ds, u)) : Bool}:
  match u:
    case C.Term.Var{+z0}:
      D.bool.ft({C.Eval.vals(ds, C.Term.Var{z0}, False{}) == C.Eval.waits(C.Eval.callWalk(ds, C.Term.Var{z0})) : Bool}, ht)
    case C.Term.Ref{+z0}:
      {==}
    case C.Term.Ann{+z0, +z1}:
      D.bool.ft({C.Eval.vals(ds, C.Term.Ann{z0, z1}, False{}) == C.Eval.waits(C.Eval.callWalk(ds, C.Term.Ann{z0, z1})) : Bool}, ht)
    case C.Term.Let{+z0, +z1, +z2}:
      D.bool.ft({C.Eval.vals(ds, C.Term.Let{z0, z1, z2}, False{}) == C.Eval.waits(C.Eval.callWalk(ds, C.Term.Let{z0, z1, z2})) : Bool}, ht)
    case C.Term.Typ{+z0}:
      D.bool.ft({C.Eval.vals(ds, C.Term.Typ{z0}, False{}) == C.Eval.waits(C.Eval.callWalk(ds, C.Term.Typ{z0})) : Bool}, ht)
    case C.Term.Min{+z0, +z1}:
      D.bool.ft({C.Eval.vals(ds, C.Term.Min{z0, z1}, False{}) == C.Eval.waits(C.Eval.callWalk(ds, C.Term.Min{z0, z1})) : Bool}, ht)
    case C.Term.All{+z0, +z1, +z2}:
      D.bool.ft({C.Eval.vals(ds, C.Term.All{z0, z1, z2}, False{}) == C.Eval.waits(C.Eval.callWalk(ds, C.Term.All{z0, z1, z2})) : Bool}, ht)
    case C.Term.Lam{+z0, +z1}:
      D.bool.ft({C.Eval.vals(ds, C.Term.Lam{z0, z1}, False{}) == C.Eval.waits(C.Eval.callWalk(ds, C.Term.Lam{z0, z1})) : Bool}, ht)
    case C.Term.App{+z0, +z1, +z2}:
      %Equal.sym(Bool, Bool.and(C.Eval.vals(ds, z1, True{}), Bool.or(Bool.not(C.Quan.live(z0)), C.Eval.vals(ds, z2, False{}))), True{}, ht) :
        {Bool.and(_, C.Eval.waits(C.Eval.callWalk(ds, C.Term.App{z0, z1, z2}))) == C.Eval.waits(C.Eval.callWalk(ds, C.Term.App{z0, z1, z2})) : Bool}
      {==}
    case C.Term.Sig{+z0, +z1, +z2}:
      D.bool.ft({C.Eval.vals(ds, C.Term.Sig{z0, z1, z2}, False{}) == C.Eval.waits(C.Eval.callWalk(ds, C.Term.Sig{z0, z1, z2})) : Bool}, ht)
    case C.Term.Tup{+z0, +z1, +z2}:
      D.bool.ft({C.Eval.vals(ds, C.Term.Tup{z0, z1, z2}, False{}) == C.Eval.waits(C.Eval.callWalk(ds, C.Term.Tup{z0, z1, z2})) : Bool}, ht)
    case C.Term.Prj{+z0}:
      D.bool.ft({C.Eval.vals(ds, C.Term.Prj{z0}, False{}) == C.Eval.waits(C.Eval.callWalk(ds, C.Term.Prj{z0})) : Bool}, ht)
    case C.Term.Enu{+z0}:
      D.bool.ft({C.Eval.vals(ds, C.Term.Enu{z0}, False{}) == C.Eval.waits(C.Eval.callWalk(ds, C.Term.Enu{z0})) : Bool}, ht)
    case C.Term.Lab{+z0}:
      D.bool.ft({C.Eval.vals(ds, C.Term.Lab{z0}, False{}) == C.Eval.waits(C.Eval.callWalk(ds, C.Term.Lab{z0})) : Bool}, ht)
    case C.Term.Mat{+z0, +z1, +z2}:
      D.bool.ft({C.Eval.vals(ds, C.Term.Mat{z0, z1, z2}, False{}) == C.Eval.waits(C.Eval.callWalk(ds, C.Term.Mat{z0, z1, z2})) : Bool}, ht)
    case C.Term.Efq{}:
      D.bool.ft({C.Eval.vals(ds, C.Term.Efq{}, False{}) == C.Eval.waits(C.Eval.callWalk(ds, C.Term.Efq{})) : Bool}, ht)
    case C.Term.Eql{+z0, +z1, +z2}:
      D.bool.ft({C.Eval.vals(ds, C.Term.Eql{z0, z1, z2}, False{}) == C.Eval.waits(C.Eval.callWalk(ds, C.Term.Eql{z0, z1, z2})) : Bool}, ht)
    case C.Term.Rfl{}:
      D.bool.ft({C.Eval.vals(ds, C.Term.Rfl{}, False{}) == C.Eval.waits(C.Eval.callWalk(ds, C.Term.Rfl{})) : Bool}, ht)
    case C.Term.Rwt{+z0, +z1, +z2}:
      D.bool.ft({C.Eval.vals(ds, C.Term.Rwt{z0, z1, z2}, False{}) == C.Eval.waits(C.Eval.callWalk(ds, C.Term.Rwt{z0, z1, z2})) : Bool}, ht)

# the call of a walk that waits is none
def call.none(ok: Bool, r: Maybe<Maybe<C.Term>>, h: {C.Eval.waits(r) == True{} : Bool}) -> {C.Eval.call.if(ok, r) == None{} : Maybe<C.Term>}:
  match ok:
    case True{}:
      match r:
        case None{}:
          D.bool.ft({C.Eval.call.if(True{}, None{}) == None{} : Maybe<C.Term>}, h)
        case Some{+s}:
          match s:
            case None{}:
              {==}
            case Some{+u}:
              D.bool.ft({C.Eval.call.if(True{}, Some{Some{u}}) == None{} : Maybe<C.Term>}, h)
    case False{}:
      {==}

# the redex of a spine of a def is its call
def redex.call(+ds: List<&2, C.Def>, g: C.Term, +q: C.Quan, +x: C.Term, ht: {C.Eval.vals(ds, g, True{}) == True{} : Bool}) ->
  {C.Eval.redex(ds, q, g, x) == C.Eval.call(ds, C.Term.App{q, g, x}) : Maybe<C.Term>}:
  match g:
    case C.Term.Var{+z0}:
      D.bool.ft({C.Eval.redex(ds, q, C.Term.Var{z0}, x) == C.Eval.call(ds, C.Term.App{q, C.Term.Var{z0}, x}) : Maybe<C.Term>}, ht)
    case C.Term.Ref{+z0}:
      {==}
    case C.Term.Ann{+z0, +z1}:
      D.bool.ft({C.Eval.redex(ds, q, C.Term.Ann{z0, z1}, x) == C.Eval.call(ds, C.Term.App{q, C.Term.Ann{z0, z1}, x}) : Maybe<C.Term>}, ht)
    case C.Term.Let{+z0, +z1, +z2}:
      D.bool.ft({C.Eval.redex(ds, q, C.Term.Let{z0, z1, z2}, x) == C.Eval.call(ds, C.Term.App{q, C.Term.Let{z0, z1, z2}, x}) : Maybe<C.Term>}, ht)
    case C.Term.Typ{+z0}:
      D.bool.ft({C.Eval.redex(ds, q, C.Term.Typ{z0}, x) == C.Eval.call(ds, C.Term.App{q, C.Term.Typ{z0}, x}) : Maybe<C.Term>}, ht)
    case C.Term.Min{+z0, +z1}:
      D.bool.ft({C.Eval.redex(ds, q, C.Term.Min{z0, z1}, x) == C.Eval.call(ds, C.Term.App{q, C.Term.Min{z0, z1}, x}) : Maybe<C.Term>}, ht)
    case C.Term.All{+z0, +z1, +z2}:
      D.bool.ft({C.Eval.redex(ds, q, C.Term.All{z0, z1, z2}, x) == C.Eval.call(ds, C.Term.App{q, C.Term.All{z0, z1, z2}, x}) : Maybe<C.Term>}, ht)
    case C.Term.Lam{+z0, +z1}:
      D.bool.ft({C.Eval.redex(ds, q, C.Term.Lam{z0, z1}, x) == C.Eval.call(ds, C.Term.App{q, C.Term.Lam{z0, z1}, x}) : Maybe<C.Term>}, ht)
    case C.Term.App{+z0, +z1, +z2}:
      {==}
    case C.Term.Sig{+z0, +z1, +z2}:
      D.bool.ft({C.Eval.redex(ds, q, C.Term.Sig{z0, z1, z2}, x) == C.Eval.call(ds, C.Term.App{q, C.Term.Sig{z0, z1, z2}, x}) : Maybe<C.Term>}, ht)
    case C.Term.Tup{+z0, +z1, +z2}:
      D.bool.ft({C.Eval.redex(ds, q, C.Term.Tup{z0, z1, z2}, x) == C.Eval.call(ds, C.Term.App{q, C.Term.Tup{z0, z1, z2}, x}) : Maybe<C.Term>}, ht)
    case C.Term.Prj{+z0}:
      D.bool.ft({C.Eval.redex(ds, q, C.Term.Prj{z0}, x) == C.Eval.call(ds, C.Term.App{q, C.Term.Prj{z0}, x}) : Maybe<C.Term>}, ht)
    case C.Term.Enu{+z0}:
      D.bool.ft({C.Eval.redex(ds, q, C.Term.Enu{z0}, x) == C.Eval.call(ds, C.Term.App{q, C.Term.Enu{z0}, x}) : Maybe<C.Term>}, ht)
    case C.Term.Lab{+z0}:
      D.bool.ft({C.Eval.redex(ds, q, C.Term.Lab{z0}, x) == C.Eval.call(ds, C.Term.App{q, C.Term.Lab{z0}, x}) : Maybe<C.Term>}, ht)
    case C.Term.Mat{+z0, +z1, +z2}:
      D.bool.ft({C.Eval.redex(ds, q, C.Term.Mat{z0, z1, z2}, x) == C.Eval.call(ds, C.Term.App{q, C.Term.Mat{z0, z1, z2}, x}) : Maybe<C.Term>}, ht)
    case C.Term.Efq{}:
      D.bool.ft({C.Eval.redex(ds, q, C.Term.Efq{}, x) == C.Eval.call(ds, C.Term.App{q, C.Term.Efq{}, x}) : Maybe<C.Term>}, ht)
    case C.Term.Eql{+z0, +z1, +z2}:
      D.bool.ft({C.Eval.redex(ds, q, C.Term.Eql{z0, z1, z2}, x) == C.Eval.call(ds, C.Term.App{q, C.Term.Eql{z0, z1, z2}, x}) : Maybe<C.Term>}, ht)
    case C.Term.Rfl{}:
      D.bool.ft({C.Eval.redex(ds, q, C.Term.Rfl{}, x) == C.Eval.call(ds, C.Term.App{q, C.Term.Rfl{}, x}) : Maybe<C.Term>}, ht)
    case C.Term.Rwt{+z0, +z1, +z2}:
      D.bool.ft({C.Eval.redex(ds, q, C.Term.Rwt{z0, z1, z2}, x) == C.Eval.call(ds, C.Term.App{q, C.Term.Rwt{z0, z1, z2}, x}) : Maybe<C.Term>}, ht)

# App q f x has no step, when f has none, is a value, and x has none and is a
# value when q is live, and the redex is none
def app.none(+q: C.Quan, +f: C.Term, +x: C.Term, sf: Maybe<C.Term>, vf: Bool, live: Bool, sx: Maybe<C.Term>, vx: Bool, -r: Maybe<C.Term>,
  esf: {sf == None{} : Maybe<C.Term>}, hx: {Bool.or(Bool.not(live), vx) == True{} : Bool},
  esx: {vx == True{} : Bool} -> {sx == None{} : Maybe<C.Term>}, er: {r == None{} : Maybe<C.Term>}) ->
  {C.Eval.step.app(q, f, x, sf, vf, live, sx, vx, r) == None{} : Maybe<C.Term>}:
  match sf:
    case Some{+f2}:
      Empty.absurd({C.Eval.step.app(q, f, x, Some{f2}, vf, live, sx, vx, r) == None{} : Maybe<C.Term>}, sm.ne(f2, esf))
    case None{}:
      match vf:
        case False{}:
          {==}
        case True{}:
          match live:
            case False{}:
              er
            case True{}:
              match sx:
                case Some{+x2}:
                  Empty.absurd({C.Eval.step.app(q, f, x, None{}, True{}, True{}, Some{x2}, vx, r) == None{} : Maybe<C.Term>}, sm.ne(x2, esx(hx)))
                case None{}:
                  match vx:
                    case True{}:
                      er
                    case False{}:
                      {==}

# Tup q a b has no step, when a has none when it is a value and q live, and b
# has none
def tup.none(+q: C.Quan, +a: C.Term, +b: C.Term, live: Bool, sa: Maybe<C.Term>, va: Bool, sb: Maybe<C.Term>,
  hx: {Bool.or(Bool.not(live), va) == True{} : Bool}, esa: {va == True{} : Bool} -> {sa == None{} : Maybe<C.Term>},
  esb: {sb == None{} : Maybe<C.Term>}) -> {C.Eval.step.tup(q, a, b, live, sa, va, sb) == None{} : Maybe<C.Term>}:
  match live:
    case False{}:
      %Equal.sym(Maybe<C.Term>, sb, None{}, esb) : {C.Eval.step.tup_b(q, a, _) == None{} : Maybe<C.Term>}
      {==}
    case True{}:
      match sa:
        case Some{+a2}:
          Empty.absurd({C.Eval.step.tup(q, a, b, True{}, Some{a2}, va, sb) == None{} : Maybe<C.Term>}, sm.ne(a2, esa(hx)))
        case None{}:
          match va:
            case True{}:
              %Equal.sym(Maybe<C.Term>, sb, None{}, esb) : {C.Eval.step.tup_b(q, a, _) == None{} : Maybe<C.Term>}
              {==}
            case False{}:
              {==}

# A value has no step
# -------------------

# what stops says has no step: a value (a False), or a spine of a def on
# arguments that are values, whose walk with more arguments acc waits (a True)
def SH(a: Bool, +ds: List<&2, C.Def>, +t: C.Term, +acc: List<&2, C.Arg>) -> Data:
  match a:
    case False{}:
      {C.Eval.vals(ds, t, False{}) == True{} : Bool}
    case True{}:
      D.P2({C.Eval.vals(ds, t, True{}) == True{} : Bool},
        {C.Eval.waits(C.Eval.callWalk.head(ds, C.Term.head(t), C.Term.args(t, acc))) == True{} : Bool})

def stops(t: C.Term, a: Bool, +ds: List<&2, C.Def>, +acc: List<&2, C.Arg>, +h: SH(a, ds, t, acc)) ->
  {C.Eval.step(ds, t) == None{} : Maybe<C.Term>}:
  match t:
    case C.Term.Var{+z0}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          D.bool.ft({C.Eval.step(ds, C.Term.Var{z0}) == None{} : Maybe<C.Term>}, ht)
    case C.Term.Ref{+z0}:
      match a:
        case False{}:
          call.none(True{}, C.Eval.callWalk(ds, C.Term.Ref{z0}), h)
        case True{}:
          (ht, hw) = h
          call.none(True{}, C.Eval.callWalk(ds, C.Term.Ref{z0}), cw.back(ds, C.Term.Ref{z0}, acc, hw))
    case C.Term.Ann{+z0, +z1}:
      match a:
        case False{}:
          D.bool.ft({C.Eval.step(ds, C.Term.Ann{z0, z1}) == None{} : Maybe<C.Term>}, h)
        case True{}:
          (ht, hw) = h
          D.bool.ft({C.Eval.step(ds, C.Term.Ann{z0, z1}) == None{} : Maybe<C.Term>}, ht)
    case C.Term.Let{+z0, +z1, +z2}:
      match a:
        case False{}:
          D.bool.ft({C.Eval.step(ds, C.Term.Let{z0, z1, z2}) == None{} : Maybe<C.Term>}, h)
        case True{}:
          (ht, hw) = h
          D.bool.ft({C.Eval.step(ds, C.Term.Let{z0, z1, z2}) == None{} : Maybe<C.Term>}, ht)
    case C.Term.Typ{+z0}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          D.bool.ft({C.Eval.step(ds, C.Term.Typ{z0}) == None{} : Maybe<C.Term>}, ht)
    case C.Term.Min{+z0, +z1}:
      match a:
        case False{}:
          D.bool.ft({C.Eval.step(ds, C.Term.Min{z0, z1}) == None{} : Maybe<C.Term>}, h)
        case True{}:
          (ht, hw) = h
          D.bool.ft({C.Eval.step(ds, C.Term.Min{z0, z1}) == None{} : Maybe<C.Term>}, ht)
    case C.Term.All{+z0, +z1, +z2}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          D.bool.ft({C.Eval.step(ds, C.Term.All{z0, z1, z2}) == None{} : Maybe<C.Term>}, ht)
    case C.Term.Lam{+z0, +z1}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          D.bool.ft({C.Eval.step(ds, C.Term.Lam{z0, z1}) == None{} : Maybe<C.Term>}, ht)
    case C.Term.App{+z0, +z1, +z2}:
      match a:
        case False{}:
          +ok = and.l(Bool.and(C.Eval.vals(ds, z1, True{}), Bool.or(Bool.not(C.Quan.live(z0)), C.Eval.vals(ds, z2, False{}))), C.Eval.waits(C.Eval.callWalk(ds, C.Term.App{z0, z1, z2})), h)
          +hw = and.r(Bool.and(C.Eval.vals(ds, z1, True{}), Bool.or(Bool.not(C.Quan.live(z0)), C.Eval.vals(ds, z2, False{}))), C.Eval.waits(C.Eval.callWalk(ds, C.Term.App{z0, z1, z2})), h)
          +hg = and.l(C.Eval.vals(ds, z1, True{}), Bool.or(Bool.not(C.Quan.live(z0)), C.Eval.vals(ds, z2, False{})), ok)
          +hx = and.r(C.Eval.vals(ds, z1, True{}), Bool.or(Bool.not(C.Quan.live(z0)), C.Eval.vals(ds, z2, False{})), ok)
          +er = Equal.trans(Maybe<C.Term>, C.Eval.redex(ds, z0, z1, z2), C.Eval.call(ds, C.Term.App{z0, z1, z2}), None{},
            redex.call(ds, z1, z0, z2, hg),
            call.none(C.Eval.vals(ds, C.Term.App{z0, z1, z2}, True{}), C.Eval.callWalk(ds, C.Term.App{z0, z1, z2}), hw))
          app.none(z0, z1, z2, C.Eval.step(ds, z1), C.Eval.vals(ds, z1, False{}), C.Quan.live(z0), C.Eval.step(ds, z2), C.Eval.vals(ds, z2, False{}),
            C.Eval.redex(ds, z0, z1, z2), stops(z1, True{}, ds, [C.Arg{z0, z2}], (hg, hw)), hx, e => stops(z2, False{}, ds, Nil{}, e), er)
        case True{}:
          (+ht, +hw) = h
          +hg = and.l(C.Eval.vals(ds, z1, True{}), Bool.or(Bool.not(C.Quan.live(z0)), C.Eval.vals(ds, z2, False{})), ht)
          +hx = and.r(C.Eval.vals(ds, z1, True{}), Bool.or(Bool.not(C.Quan.live(z0)), C.Eval.vals(ds, z2, False{})), ht)
          +er = Equal.trans(Maybe<C.Term>, C.Eval.redex(ds, z0, z1, z2), C.Eval.call(ds, C.Term.App{z0, z1, z2}), None{},
            redex.call(ds, z1, z0, z2, hg),
            call.none(C.Eval.vals(ds, C.Term.App{z0, z1, z2}, True{}), C.Eval.callWalk(ds, C.Term.App{z0, z1, z2}), cw.back(ds, C.Term.App{z0, z1, z2}, acc, hw)))
          app.none(z0, z1, z2, C.Eval.step(ds, z1), C.Eval.vals(ds, z1, False{}), C.Quan.live(z0), C.Eval.step(ds, z2), C.Eval.vals(ds, z2, False{}),
            C.Eval.redex(ds, z0, z1, z2), stops(z1, True{}, ds, Con{C.Arg{z0, z2}, acc}, (hg, hw)), hx, e => stops(z2, False{}, ds, Nil{}, e), er)
    case C.Term.Sig{+z0, +z1, +z2}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          D.bool.ft({C.Eval.step(ds, C.Term.Sig{z0, z1, z2}) == None{} : Maybe<C.Term>}, ht)
    case C.Term.Tup{+z0, +z1, +z2}:
      match a:
        case False{}:
          +hx = and.l(Bool.or(Bool.not(C.Quan.live(z0)), C.Eval.vals(ds, z1, False{})), C.Eval.vals(ds, z2, False{}), h)
          +hb = and.r(Bool.or(Bool.not(C.Quan.live(z0)), C.Eval.vals(ds, z1, False{})), C.Eval.vals(ds, z2, False{}), h)
          tup.none(z0, z1, z2, C.Quan.live(z0), C.Eval.step(ds, z1), C.Eval.vals(ds, z1, False{}), C.Eval.step(ds, z2), hx,
            e => stops(z1, False{}, ds, Nil{}, e), stops(z2, False{}, ds, Nil{}, hb))
        case True{}:
          (ht, hw) = h
          D.bool.ft({C.Eval.step(ds, C.Term.Tup{z0, z1, z2}) == None{} : Maybe<C.Term>}, ht)
    case C.Term.Prj{+z0}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          D.bool.ft({C.Eval.step(ds, C.Term.Prj{z0}) == None{} : Maybe<C.Term>}, ht)
    case C.Term.Enu{+z0}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          D.bool.ft({C.Eval.step(ds, C.Term.Enu{z0}) == None{} : Maybe<C.Term>}, ht)
    case C.Term.Lab{+z0}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          D.bool.ft({C.Eval.step(ds, C.Term.Lab{z0}) == None{} : Maybe<C.Term>}, ht)
    case C.Term.Mat{+z0, +z1, +z2}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          D.bool.ft({C.Eval.step(ds, C.Term.Mat{z0, z1, z2}) == None{} : Maybe<C.Term>}, ht)
    case C.Term.Efq{}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          D.bool.ft({C.Eval.step(ds, C.Term.Efq{}) == None{} : Maybe<C.Term>}, ht)
    case C.Term.Eql{+z0, +z1, +z2}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          D.bool.ft({C.Eval.step(ds, C.Term.Eql{z0, z1, z2}) == None{} : Maybe<C.Term>}, ht)
    case C.Term.Rfl{}:
      match a:
        case False{}:
          {==}
        case True{}:
          (ht, hw) = h
          D.bool.ft({C.Eval.step(ds, C.Term.Rfl{}) == None{} : Maybe<C.Term>}, ht)
    case C.Term.Rwt{+z0, +z1, +z2}:
      match a:
        case False{}:
          D.bool.ft({C.Eval.step(ds, C.Term.Rwt{z0, z1, z2}) == None{} : Maybe<C.Term>}, h)
        case True{}:
          (ht, hw) = h
          D.bool.ft({C.Eval.step(ds, C.Term.Rwt{z0, z1, z2}) == None{} : Maybe<C.Term>}, ht)

# a value has no step (Lean's eval_value)
def ev.stops(+ds: List<&2, C.Def>, +t: C.Term, h: {C.Eval.vals(ds, t, False{}) == True{} : Bool}) ->
  {C.Eval.step(ds, t) == None{} : Maybe<C.Term>}:
  stops(t, False{}, ds, Nil{}, h)


# A stuck focus makes its frames' term stuck
# ------------------------------------------

# Rwt e P f, Min a b and Let q v f, with a first part that has no step and is
# no value, have no step
def rwt.none(+e: C.Term, +p: C.Term, +f: C.Term, se: Maybe<C.Term>, ve: Bool, ese: {se == None{} : Maybe<C.Term>},
  eve: {ve == False{} : Bool}) -> {C.Eval.step.rwt(e, p, f, se, ve) == None{} : Maybe<C.Term>}:
  match se:
    case Some{+e2}:
      Empty.absurd({C.Eval.step.rwt(e, p, f, Some{e2}, ve) == None{} : Maybe<C.Term>}, sm.ne(e2, ese))
    case None{}:
      match ve:
        case True{}:
          D.bool.ft({C.Eval.step.rwt(e, p, f, None{}, True{}) == None{} : Maybe<C.Term>}, Equal.sym(Bool, True{}, False{}, eve))
        case False{}:
          {==}

def min.none(+a: C.Term, +b: C.Term, sa: Maybe<C.Term>, va: Bool, sb: Maybe<C.Term>, +vb: Bool, mt: Maybe<C.Term>,
  esa: {sa == None{} : Maybe<C.Term>}, eva: {va == False{} : Bool}) -> {C.Eval.step.min(a, b, sa, va, sb, vb, mt) == None{} : Maybe<C.Term>}:
  match sa:
    case Some{+a2}:
      Empty.absurd({C.Eval.step.min(a, b, Some{a2}, va, sb, vb, mt) == None{} : Maybe<C.Term>}, sm.ne(a2, esa))
    case None{}:
      match va:
        case True{}:
          D.bool.ft({C.Eval.step.min(a, b, None{}, True{}, sb, vb, mt) == None{} : Maybe<C.Term>}, Equal.sym(Bool, True{}, False{}, eva))
        case False{}:
          {==}

# Min a b, with a value a with no step and a b with no step that is no value
def min.none2(+a: C.Term, +b: C.Term, sa: Maybe<C.Term>, va: Bool, sb: Maybe<C.Term>, vb: Bool, mt: Maybe<C.Term>,
  esa: {sa == None{} : Maybe<C.Term>}, eva: {va == True{} : Bool}, esb: {sb == None{} : Maybe<C.Term>}, evb: {vb == False{} : Bool}) ->
  {C.Eval.step.min(a, b, sa, va, sb, vb, mt) == None{} : Maybe<C.Term>}:
  match sa:
    case Some{+a2}:
      Empty.absurd({C.Eval.step.min(a, b, Some{a2}, va, sb, vb, mt) == None{} : Maybe<C.Term>}, sm.ne(a2, esa))
    case None{}:
      match va:
        case False{}:
          {==}
        case True{}:
          match sb:
            case Some{+b2}:
              Empty.absurd({C.Eval.step.min(a, b, None{}, True{}, Some{b2}, vb, mt) == None{} : Maybe<C.Term>}, sm.ne(b2, esb))
            case None{}:
              match vb:
                case True{}:
                  D.bool.ft({C.Eval.step.min(a, b, None{}, True{}, None{}, True{}, mt) == None{} : Maybe<C.Term>}, Equal.sym(Bool, True{}, False{}, evb))
                case False{}:
                  {==}

def let.none(+q: C.Quan, +v: C.Term, +f: C.Term, live: Bool, sv: Maybe<C.Term>, vv: Bool, +fits: Bool, el: {live == True{} : Bool},
  esv: {sv == None{} : Maybe<C.Term>}, evv: {vv == False{} : Bool}) -> {C.Eval.step.let(q, v, f, live, sv, vv, fits) == None{} : Maybe<C.Term>}:
  match live:
    case False{}:
      D.bool.ft({C.Eval.step.let(q, v, f, False{}, sv, vv, fits) == None{} : Maybe<C.Term>}, el)
    case True{}:
      match sv:
        case Some{+v2}:
          Empty.absurd({C.Eval.step.let(q, v, f, True{}, Some{v2}, vv, fits) == None{} : Maybe<C.Term>}, sm.ne(v2, esv))
        case None{}:
          match vv:
            case True{}:
              D.bool.ft({C.Eval.step.let(q, v, f, True{}, None{}, True{}, fits) == None{} : Maybe<C.Term>}, Equal.sym(Bool, True{}, False{}, evv))
            case False{}:
              {==}

# Tup q a b, q live, with an a with no step that is no value
def tupb.none(+q: C.Quan, +a: C.Term, +b: C.Term, live: Bool, sa: Maybe<C.Term>, va: Bool, sb: Maybe<C.Term>, el: {live == True{} : Bool},
  esa: {sa == None{} : Maybe<C.Term>}, eva: {va == False{} : Bool}) -> {C.Eval.step.tup(q, a, b, live, sa, va, sb) == None{} : Maybe<C.Term>}:
  match live:
    case False{}:
      D.bool.ft({C.Eval.step.tup(q, a, b, False{}, sa, va, sb) == None{} : Maybe<C.Term>}, el)
    case True{}:
      match sa:
        case Some{+a2}:
          Empty.absurd({C.Eval.step.tup(q, a, b, True{}, Some{a2}, va, sb) == None{} : Maybe<C.Term>}, sm.ne(a2, esa))
        case None{}:
          match va:
            case True{}:
              D.bool.ft({C.Eval.step.tup(q, a, b, True{}, None{}, True{}, sb) == None{} : Maybe<C.Term>}, Equal.sym(Bool, True{}, False{}, eva))
            case False{}:
              {==}

# App q f x, with an f with no step that is no value
def appf.none(+q: C.Quan, +f: C.Term, +x: C.Term, sf: Maybe<C.Term>, vf: Bool, +live: Bool, sx: Maybe<C.Term>, +vx: Bool, r: Maybe<C.Term>,
  esf: {sf == None{} : Maybe<C.Term>}, evf: {vf == False{} : Bool}) -> {C.Eval.step.app(q, f, x, sf, vf, live, sx, vx, r) == None{} : Maybe<C.Term>}:
  match sf:
    case Some{+f2}:
      Empty.absurd({C.Eval.step.app(q, f, x, Some{f2}, vf, live, sx, vx, r) == None{} : Maybe<C.Term>}, sm.ne(f2, esf))
    case None{}:
      match vf:
        case True{}:
          D.bool.ft({C.Eval.step.app(q, f, x, None{}, True{}, live, sx, vx, r) == None{} : Maybe<C.Term>}, Equal.sym(Bool, True{}, False{}, evf))
        case False{}:
          {==}

# App q f x, with a live q, a value f with no step and an x with no step that
# is no value
def appx.none(+q: C.Quan, +f: C.Term, +x: C.Term, sf: Maybe<C.Term>, vf: Bool, live: Bool, sx: Maybe<C.Term>, vx: Bool, r: Maybe<C.Term>,
  el: {live == True{} : Bool}, esf: {sf == None{} : Maybe<C.Term>}, esx: {sx == None{} : Maybe<C.Term>},
  evx: {vx == False{} : Bool}) -> {C.Eval.step.app(q, f, x, sf, vf, live, sx, vx, r) == None{} : Maybe<C.Term>}:
  match sf:
    case Some{+f2}:
      Empty.absurd({C.Eval.step.app(q, f, x, Some{f2}, vf, live, sx, vx, r) == None{} : Maybe<C.Term>}, sm.ne(f2, esf))
    case None{}:
      match vf:
        case False{}:
          {==}
        case True{}:
          match live:
            case False{}:
              D.bool.ft({C.Eval.step.app(q, f, x, None{}, True{}, False{}, sx, vx, r) == None{} : Maybe<C.Term>}, el)
            case True{}:
              match sx:
                case Some{+x2}:
                  Empty.absurd({C.Eval.step.app(q, f, x, None{}, True{}, True{}, Some{x2}, vx, r) == None{} : Maybe<C.Term>}, sm.ne(x2, esx))
                case None{}:
                  match vx:
                    case True{}:
                      D.bool.ft({C.Eval.step.app(q, f, x, None{}, True{}, True{}, None{}, True{}, r) == None{} : Maybe<C.Term>}, Equal.sym(Bool, True{}, False{}, evx))
                    case False{}:
                      {==}


# the stuck facts of a term
def Stk(+ds: List<&2, C.Def>, t: C.Term) -> Data:
  D.P2({C.Eval.step(ds, t) == None{} : Maybe<C.Term>}, {C.Eval.vals(ds, t, False{}) == False{} : Bool})

# App q u a is no value, when u is none
def vapp.f(b: Bool, +ds: List<&2, C.Def>, +q: C.Quan, +u: C.Term, +a: C.Term, +eb: {C.Eval.vals(ds, u, True{}) == b : Bool},
  hv: {C.Eval.vals(ds, u, False{}) == False{} : Bool}) -> {C.Eval.vals(ds, C.Term.App{q, u, a}, False{}) == False{} : Bool}:
  match b:
    case False{}:
      %Equal.sym(Bool, C.Eval.vals(ds, u, True{}), False{}, eb) :
        {Bool.and(Bool.and(_, Bool.or(Bool.not(C.Quan.live(q)), C.Eval.vals(ds, a, False{}))), C.Eval.waits(C.Eval.callWalk(ds, C.Term.App{q, u, a}))) == False{} : Bool}
      {==}
    case True{}:
      +ew = Equal.trans(Bool, C.Eval.waits(C.Eval.callWalk(ds, u)), C.Eval.vals(ds, u, False{}), False{},
        Equal.sym(Bool, C.Eval.vals(ds, u, False{}), C.Eval.waits(C.Eval.callWalk(ds, u)), vals.tf(ds, u, eb)), hv)
      %Equal.sym(Bool, C.Eval.vals(ds, u, True{}), True{}, eb) :
        {Bool.and(Bool.and(_, Bool.or(Bool.not(C.Quan.live(q)), C.Eval.vals(ds, a, False{}))), C.Eval.waits(C.Eval.callWalk(ds, C.Term.App{q, u, a}))) == False{} : Bool}
      and.f(Bool.or(Bool.not(C.Quan.live(q)), C.Eval.vals(ds, a, False{})), C.Eval.waits(C.Eval.callWalk(ds, C.Term.App{q, u, a})), cw.app(ds, u, q, a, ew))

# App q a u, with q live, is no value when u is none
def vfun.f(l: Bool, va: Bool, vu: Bool, +w: Bool, el: {l == True{} : Bool}, ev: {vu == False{} : Bool}) ->
  {Bool.and(Bool.and(va, Bool.or(Bool.not(l), vu)), w) == False{} : Bool}:
  match l:
    case False{}:
      D.bool.ft({Bool.and(Bool.and(va, Bool.or(Bool.not(False{}), vu)), w) == False{} : Bool}, el)
    case True{}:
      match va:
        case True{}:
          match vu:
            case True{}:
              D.bool.ft({Bool.and(Bool.and(True{}, Bool.or(Bool.not(True{}), True{})), w) == False{} : Bool}, Equal.sym(Bool, True{}, False{}, ev))
            case False{}:
              {==}
        case False{}:
          {==}

# Tup q u a, q live, is no value when u is none
def vtup.f(l: Bool, vu: Bool, +vb: Bool, el: {l == True{} : Bool}, ev: {vu == False{} : Bool}) ->
  {Bool.and(Bool.or(Bool.not(l), vu), vb) == False{} : Bool}:
  match l:
    case False{}:
      D.bool.ft({Bool.and(Bool.or(Bool.not(False{}), vu), vb) == False{} : Bool}, el)
    case True{}:
      match vu:
        case True{}:
          D.bool.ft({Bool.and(Bool.or(Bool.not(True{}), True{}), vb) == False{} : Bool}, Equal.sym(Bool, True{}, False{}, ev))
        case False{}:
          {==}

# one frame around a focus with no step that is no value
def stuck1(+ds: List<&2, C.Def>, fr: D.AF, +u: C.Term, +ok: D.AF.ok(ds, fr),
  +hs: {C.Eval.step(ds, u) == None{} : Maybe<C.Term>}, +hv: {C.Eval.vals(ds, u, False{}) == False{} : Bool}) ->
  Stk(ds, D.A.plug(fr, u)):
  match fr:
    case D.AF{+kind, +q, +k, +a, +b}:
      match kind:
        case D.FK.arg{}:
          (appf.none(q, u, a, C.Eval.step(ds, u), C.Eval.vals(ds, u, False{}), C.Quan.live(q), C.Eval.step(ds, a), C.Eval.vals(ds, a, False{}),
            C.Eval.redex(ds, q, u, a), hs, hv),
           vapp.f(C.Eval.vals(ds, u, True{}), ds, q, u, a, {==}, hv))
        case D.FK.val{}:
          (appf.none(q, u, a, C.Eval.step(ds, u), C.Eval.vals(ds, u, False{}), C.Quan.live(q), C.Eval.step(ds, a), C.Eval.vals(ds, a, False{}),
            C.Eval.redex(ds, q, u, a), hs, hv),
           vapp.f(C.Eval.vals(ds, u, True{}), ds, q, u, a, {==}, hv))
        case D.FK.fun{}:
          +el = and.l(C.Quan.live(q), C.Eval.vals(ds, a, False{}), ok)
          +ea = and.r(C.Quan.live(q), C.Eval.vals(ds, a, False{}), ok)
          (appx.none(q, a, u, C.Eval.step(ds, a), C.Eval.vals(ds, a, False{}), C.Quan.live(q), C.Eval.step(ds, u), C.Eval.vals(ds, u, False{}),
            C.Eval.redex(ds, q, a, u), el, ev.stops(ds, a, ea), hs, hv),
           vfun.f(C.Quan.live(q), C.Eval.vals(ds, a, True{}), C.Eval.vals(ds, u, False{}), C.Eval.waits(C.Eval.callWalk(ds, C.Term.App{q, a, u})), el, hv))
        case D.FK.let{}:
          (let.none(q, u, a, C.Quan.live(q), C.Eval.step(ds, u), C.Eval.vals(ds, u, False{}), C.Quan.fits(q, u), ok, hs, hv), {==})
        case D.FK.tupb{}:
          (tupb.none(q, u, a, C.Quan.live(q), C.Eval.step(ds, u), C.Eval.vals(ds, u, False{}), C.Eval.step(ds, a), ok, hs, hv),
           vtup.f(C.Quan.live(q), C.Eval.vals(ds, u, False{}), C.Eval.vals(ds, a, False{}), ok, hv))
        case D.FK.tupa{}:
          (tup.none(q, a, u, C.Quan.live(q), C.Eval.step(ds, a), C.Eval.vals(ds, a, False{}), C.Eval.step(ds, u), ok, e => ev.stops(ds, a, e), hs),
           and.f(Bool.or(Bool.not(C.Quan.live(q)), C.Eval.vals(ds, a, False{})), C.Eval.vals(ds, u, False{}), hv))
        case D.FK.rwt{}:
          (rwt.none(u, a, b, C.Eval.step(ds, u), C.Eval.vals(ds, u, False{}), hs, hv), {==})
        case D.FK.minb{}:
          (min.none(u, a, C.Eval.step(ds, u), C.Eval.vals(ds, u, False{}), C.Eval.step(ds, a), C.Eval.vals(ds, a, False{}), C.Eval.meet(u, a), hs, hv), {==})
        case D.FK.mina{}:
          (min.none2(a, u, C.Eval.step(ds, a), C.Eval.vals(ds, a, False{}), C.Eval.step(ds, u), C.Eval.vals(ds, u, False{}), C.Eval.meet(a, u),
            ev.stops(ds, a, ok), ok, hs, hv), {==})

def ev.stuck.go(+ds: List<&2, C.Def>, fs: List<&2, D.AF>, +u: C.Term, hfs: D.AFs.ok(ds, fs), st: Stk(ds, u)) ->
  Stk(ds, D.A.plugs(fs, u)):
  match fs:
    case Nil{}:
      st
    case Con{+fr, +rest}:
      (ok, oks) = hfs
      (hs, hv) = st
      ev.stuck.go(ds, rest, D.A.plug(fr, u), oks, stuck1(ds, fr, u, ok, hs, hv))

# a focus with no step that is no value makes its frames' term so
def ev.stuck(+ds: List<&2, C.Def>, fs: List<&2, D.AF>, +u: C.Term, hfs: D.AFs.ok(ds, fs),
  hs: {C.Eval.step(ds, u) == None{} : Maybe<C.Term>}, hv: {C.Eval.vals(ds, u, False{}) == False{} : Bool}) ->
  Stk(ds, D.A.plugs(fs, u)):
  ev.stuck.go(ds, fs, u, hfs, (hs, hv))
