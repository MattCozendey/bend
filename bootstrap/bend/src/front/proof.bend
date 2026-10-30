import Base
import ../source/impl.bend as Source
import ../shared/impl.bend as Shared
import ./impl.bend as Front
import ./spec.bend as Spec

# Front proofs
# ============
#
# Le p q L st: on each text s of at most L bytes, q gives each result that p
# gives, and its rest is no longer than s (shorter when st holds). The proof
# shows Le from Term.parse with any fuel to Term.parse with enough fuel, each
# parser from the Les of the parsers that it calls.

# Lengths
# =======

def Gap.le(s: List<&2, Nat>, +c: Bool) -> {Nat.is_le(List.length(&2, Nat, Source.Parse.gap(s, c)), List.length(&2, Nat, s)) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case Con{+b, +rest}:
      match c:
        case True{}:
          Shared.Nat.is_le_succ(List.length(&2, Nat, Source.Parse.gap(Con{b, rest}, True{})), List.length(&2, Nat, rest),
            Shared.Bool.elim(Nat.is_eq(b, 10n),
              x => {Nat.is_le(List.length(&2, Nat, Source.Bool.lazy(List<&2, Nat>, x, u => Source.Parse.gap(rest, False{}), u => Source.Parse.gap(rest, True{}))), List.length(&2, Nat, rest)) == True{} : Bool},
              Gap.le(rest, False{}), Gap.le(rest, True{})))
        case False{}:
          Shared.Bool.elim(Nat.is_eq(b, 35n),
            x => {Nat.is_le(List.length(&2, Nat, Source.Bool.lazy(List<&2, Nat>, x, u => Source.Parse.gap(rest, True{}), u => Source.Bool.lazy(List<&2, Nat>, Source.Byte.is_space(b), w => Source.Parse.gap(rest, False{}), w => Con{b, rest}))), 1n+List.length(&2, Nat, rest)) == True{} : Bool},
            Shared.Nat.is_le_succ(List.length(&2, Nat, Source.Parse.gap(rest, True{})), List.length(&2, Nat, rest), Gap.le(rest, True{})),
            Shared.Bool.elim(Source.Byte.is_space(b),
              x => {Nat.is_le(List.length(&2, Nat, Source.Bool.lazy(List<&2, Nat>, x, w => Source.Parse.gap(rest, False{}), w => Con{b, rest})), 1n+List.length(&2, Nat, rest)) == True{} : Bool},
              Shared.Nat.is_le_succ(List.length(&2, Nat, Source.Parse.gap(rest, False{})), List.length(&2, Nat, rest), Gap.le(rest, False{})),
              Shared.Nat.is_le_refl(List.length(&2, Nat, rest))))

def Strip.Ok(m: Maybe<&2, List<&2, Nat>>, w: List<&2, Nat>, s: List<&2, Nat>) -> Type:
  match m:
    case Some{r}:
      {Nat.is_le(Nat.add(List.length(&2, Nat, w), List.length(&2, Nat, r)), List.length(&2, Nat, s)) == True{} : Bool}
    case None{}:
      Unit

def Strip.le(w: List<&2, Nat>, s: List<&2, Nat>) -> Strip.Ok(Source.Bytes.strip(w, s), w, s):
  match w s:
    case Nil{} t:
      Shared.Nat.is_le_refl(List.length(&2, Nat, t))
    case Con{+x, +xs} Con{+y, +ys}:
      Shared.Bool.elim(Nat.is_eq(x, y),
        c => Strip.Ok(Source.Bool.lazy(Maybe<&2, List<&2, Nat>>, c, u => Source.Bytes.strip(xs, ys), u => None{}), Con{x, xs},
          Con{y, ys}),
        Shared.Maybe.elim(List<&2, Nat>, Source.Bytes.strip(xs, ys),
          m => Strip.Ok(m, xs, ys) -> Strip.Ok(m, Con{x, xs}, Con{y, ys}),
          r => h => h, h => Unit{})(Strip.le(xs, ys)),
        Unit{})
    case Con{x, xs} Nil{}:
      Unit{}

def Parsed.elim(-A: Data, x: Source.Parsed<A>, -P: Source.Parsed<A> -> Type, ok: @v:A -> @r:List<&2, Nat> -> P(Source.Parsed.ok{v, r}),
  fail: P(Source.Parsed.fail{})) -> P(x):
  match x:
    case Source.Parsed.ok{v, r}:
      ok(v, r)
    case Source.Parsed.fail{}:
      fail

def Span.Ok(x: Source.Parsed<List<&2, Nat>>, s: List<&2, Nat>) -> Type:
  match x:
    case Source.Parsed.ok{n, t}:
      {Nat.is_le(Nat.add(List.length(&2, Nat, n), List.length(&2, Nat, t)), List.length(&2, Nat, s)) == True{} : Bool}
    case Source.Parsed.fail{}:
      Unit

def Span.le(s: List<&2, Nat>) -> Span.Ok(Source.Parse.span(s), s):
  match s:
    case Nil{}:
      {==}
    case Con{+b, +rest}:
      Shared.Bool.elim(Source.Byte.is_name(b),
        c => Span.Ok(Source.Bool.lazy(Source.Parsed<List<&2, Nat>>, c, u => Source.Parse.span.cons(b, Source.Parse.span(rest)),
          u => Source.Parsed.ok{Nil{}, Con{b, rest}}), Con{b, rest}),
        Parsed.elim(List<&2, Nat>, Source.Parse.span(rest),
          x => Span.Ok(x, rest) -> Span.Ok(Source.Parse.span.cons(b, x), Con{b, rest}),
          n => t => h => h, h => Unit{})(Span.le(rest)),
        Shared.Nat.is_le_refl(1n+List.length(&2, Nat, rest)))

def Nat.is_le_add_left(+b: Nat, +a: Nat) -> {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      Shared.Nat.is_le_refl(b)
    case 1n+p:
      Shared.Nat.is_le_succ(b, Nat.add(p, b), Nat.is_le_add_left(b, p))

# Relation
# ========

# the rest r of a result on the text s: no longer than s, shorter when st holds
def Rest.ok(st: Bool, r: List<&2, Nat>, s: List<&2, Nat>) -> Bool:
  match st:
    case True{}:
      Nat.is_le(1n+List.length(&2, Nat, r), List.length(&2, Nat, s))
    case False{}:
      Nat.is_le(List.length(&2, Nat, r), List.length(&2, Nat, s))

# y is the result x, when x is one, with a rest as Rest.ok says
def Res.Le(-A: Data, x: Source.Parsed<A>, y: Source.Parsed<A>, s: List<&2, Nat>, st: Bool) -> Type:
  match x:
    case Source.Parsed.ok{v, r}:
      {y == Source.Parsed.ok{v, r} : Source.Parsed<A>} & {Rest.ok(st, r, s) == True{} : Bool}
    case Source.Parsed.fail{}:
      Unit

def Le(-A: Data, p: Source.Parse(A), q: Source.Parse(A), L: Nat, st: Bool) -> Type:
  @s:List<&2, Nat> -> @hl:{Nat.is_le(List.length(&2, Nat, s), L) == True{} : Bool} -> Res.Le(A, p(s), q(s), s, st)

def Rest.weak(st: Bool, r: List<&2, Nat>, s: List<&2, Nat>, h: {Rest.ok(st, r, s) == True{} : Bool}) ->
  {Rest.ok(False{}, r, s) == True{} : Bool}:
  match st:
    case True{}:
      Shared.Nat.is_le_pred(List.length(&2, Nat, r), List.length(&2, Nat, s), h)
    case False{}:
      h

def Rest.trans(sa: Bool, sb: Bool, +r: List<&2, Nat>, +s1: List<&2, Nat>, +s: List<&2, Nat>, h1: {Rest.ok(sb, r, s1) == True{} : Bool},
  h2: {Rest.ok(sa, s1, s) == True{} : Bool}) -> {Rest.ok(Bool.or(sa, sb), r, s) == True{} : Bool}:
  match sa sb:
    case True{} _:
      Shared.Nat.is_le_trans(1n+List.length(&2, Nat, r), 1n+List.length(&2, Nat, s1), List.length(&2, Nat, s), Rest.weak(sb, r, s1, h1), h2)
    case False{} True{}:
      Shared.Nat.is_le_trans(1n+List.length(&2, Nat, r), List.length(&2, Nat, s1), List.length(&2, Nat, s), h1, h2)
    case False{} False{}:
      Shared.Nat.is_le_trans(List.length(&2, Nat, r), List.length(&2, Nat, s1), List.length(&2, Nat, s), h1, h2)

def Res.widen(-A: Data, x: Source.Parsed<A>, -y: Source.Parsed<A>, +s1: List<&2, Nat>, +s: List<&2, Nat>, sp: Bool, sk: Bool,
  hs: {Rest.ok(sp, s1, s) == True{} : Bool}, h: Res.Le(A, x, y, s1, sk)) -> Res.Le(A, x, y, s, Bool.or(sp, sk)):
  match x:
    case Source.Parsed.ok{v, +r}:
      (e, t) = h
      (e, Rest.trans(sp, sk, r, s1, s, t, hs))
    case Source.Parsed.fail{}:
      Unit{}

def Rest.from_true(f: Bool, +r: List<&2, Nat>, +s: List<&2, Nat>, h: {Rest.ok(True{}, r, s) == True{} : Bool}) ->
  {Rest.ok(f, r, s) == True{} : Bool}:
  match f:
    case True{}:
      h
    case False{}:
      Rest.weak(True{}, r, s, h)

# Res.widen after a strict step: then any flag holds
def Res.widen1(-A: Data, x: Source.Parsed<A>, -y: Source.Parsed<A>, +s1: List<&2, Nat>, +s: List<&2, Nat>, sk: Bool, f: Bool,
  hs: {Rest.ok(True{}, s1, s) == True{} : Bool}, h: Res.Le(A, x, y, s1, sk)) -> Res.Le(A, x, y, s, f):
  match x:
    case Source.Parsed.ok{v, +r}:
      (e, t) = h
      (e, Rest.from_true(f, r, s, Rest.trans(True{}, sk, r, s1, s, t, hs)))
    case Source.Parsed.fail{}:
      Unit{}

def Le.weaken(-A: Data, p: Source.Parse(A), q: Source.Parse(A), +L: Nat, +M: Nat, st: Bool, h: {Nat.is_le(M, L) == True{} : Bool},
  r: Le(A, p, q, L, st)) -> Le(A, p, q, M, st):
  +s => hl => r(s, Shared.Nat.is_le_trans(List.length(&2, Nat, s), M, L, hl, h))

# Le.bind after p gave v and the rest s1 on s; qs is q's result on s. k runs on
# s1, which lift bounds by M.
def Le.bind.ok(-A: Data, -B: Data, +v: A, +s1: List<&2, Nat>, +s: List<&2, Nat>, -qs: Source.Parsed<A>,
  k: A -> Source.Parse(B), k2: A -> Source.Parse(B), +M: Nat, +sp: Bool, +sk: Bool,
  rk: @a:A -> Le(B, k(a), k2(a), M, sk),
  lift: {Rest.ok(sp, s1, s) == True{} : Bool} -> {Nat.is_le(List.length(&2, Nat, s1), M) == True{} : Bool},
  h: Res.Le(A, Source.Parsed.ok{v, s1}, qs, s, sp)) ->
  Res.Le(B, k(v, s1), Source.Parse.bind.of(A, B, k2, qs), s, Bool.or(sp, sk)):
  (e, +t) = h
  %Equal.sym(Source.Parsed<A>, qs, Source.Parsed.ok{v, s1}, e) :
    Res.Le(B, k(v, s1), Source.Parse.bind.of(A, B, k2, _), s, Bool.or(sp, sk))
  Res.widen(B, k(v, s1), k2(v, s1), s1, s, sp, sk, t, rk(v, s1, lift(t)))

# p, then k on its value
def Le.bind(-A: Data, -B: Data, p: Source.Parse(A), q: Source.Parse(A), k: A -> Source.Parse(B),
  k2: A -> Source.Parse(B), +L: Nat, +sp: Bool, +sk: Bool, rp: Le(A, p, q, L, sp),
  rk: @a:A -> Le(B, k(a), k2(a), L, sk)) ->
  Le(B, Source.Parse.bind(A, B, p, k), Source.Parse.bind(A, B, q, k2), L, Bool.or(sp, sk)):
  +s => +hl => Parsed.elim(A, p(s),
    x => Res.Le(A, x, q(s), s, sp) ->
      Res.Le(B, Source.Parse.bind.of(A, B, k, x), Source.Parse.bind.of(A, B, k2, q(s)), s, Bool.or(sp, sk)),
    v => +s1 => h => Le.bind.ok(A, B, v, s1, s, q(s), k, k2, L, sp, sk, rk,
      t => Shared.Nat.is_le_trans(List.length(&2, Nat, s1), List.length(&2, Nat, s), L, Rest.weak(sp, s1, s, t), hl), h),
    h => Unit{})(rp(s, hl))

# a strict p, then k on its value, on a shorter text
def Le.bind1(-A: Data, -B: Data, p: Source.Parse(A), q: Source.Parse(A), k: A -> Source.Parse(B),
  k2: A -> Source.Parse(B), +L: Nat, +sk: Bool, rp: Le(A, p, q, L, True{}),
  rk: @a:A -> Le(B, k(a), k2(a), Shared.Nat.dec(L), sk)) ->
  Le(B, Source.Parse.bind(A, B, p, k), Source.Parse.bind(A, B, q, k2), L, True{}):
  +s => +hl => Parsed.elim(A, p(s),
    x => Res.Le(A, x, q(s), s, True{}) ->
      Res.Le(B, Source.Parse.bind.of(A, B, k, x), Source.Parse.bind.of(A, B, k2, q(s)), s, True{}),
    v => +s1 => h => Le.bind.ok(A, B, v, s1, s, q(s), k, k2, Shared.Nat.dec(L), True{}, sk, rk,
      t => Shared.Nat.is_le_below(List.length(&2, Nat, s1), L, Shared.Nat.is_le_trans(1n+List.length(&2, Nat, s1), List.length(&2, Nat, s), L, t, hl)), h),
    h => Unit{})(rp(s, hl))

# p or q, as c says
def Le.if(-A: Data, c: Bool, p: Source.Parse(A), p2: Source.Parse(A), q: Source.Parse(A), q2: Source.Parse(A),
  L: Nat, st: Bool, rp: Le(A, p, p2, L, st), rq: Le(A, q, q2, L, st)) ->
  Le(A, Source.Bool.if(Source.Parse(A), c, p, q), Source.Bool.if(Source.Parse(A), c, p2, q2), L, st):
  match c:
    case True{}:
      rp
    case False{}:
      rq

def Le.pure(-A: Data, +a: A, L: Nat) -> Le(A, Source.Parse.pure(A, a), Source.Parse.pure(A, a), L, False{}):
  s => hl => ({==}, Shared.Nat.is_le_refl(List.length(&2, Nat, s)))

def Le.fail(-A: Data, L: Nat, st: Bool) -> Le(A, Source.Parse.fail(A), Source.Parse.fail(A), L, st):
  s => hl => Unit{}

def Nat.is_le_one_add(+a: Nat, +b: Nat, h: {Nat.is_le(1n, a) == True{} : Bool}) -> {Nat.is_le(1n+b, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      Shared.Bool.absurd({Nat.is_le(1n+b, b) == True{} : Bool}, h)
    case 1n+p:
      Nat.is_le_add_left(b, p)

# Le.take_if after w was taken: p on the rest r, which is shorter than s
def Le.take_if.some(-A: Data, p: Source.Parse(A), p2: Source.Parse(A), +r: List<&2, Nat>, +s: List<&2, Nat>, +L: Nat, +sp: Bool,
  sq: Bool, rp: Le(A, p, p2, Shared.Nat.dec(L), sp), +hr: {Nat.is_le(1n+List.length(&2, Nat, r), List.length(&2, Nat, s)) == True{} : Bool}, hl: {Nat.is_le(List.length(&2, Nat, s), L) == True{} : Bool}) ->
  Res.Le(A, p(r), p2(r), s, sq):
  Res.widen1(A, p(r), p2(r), r, s, sp, sq, hr,
    rp(r, Shared.Nat.is_le_below(List.length(&2, Nat, r), L, Shared.Nat.is_le_trans(1n+List.length(&2, Nat, r), List.length(&2, Nat, s), L, hr, hl))))

# p when the word w comes next, taken; else q
def Le.take_if(-A: Data, +w: List<&2, Nat>, +hw: {Nat.is_le(1n, List.length(&2, Nat, w)) == True{} : Bool}, p: Source.Parse(A), p2: Source.Parse(A),
  q: Source.Parse(A), q2: Source.Parse(A), +L: Nat, +sp: Bool, +sq: Bool,
  rp: Le(A, p, p2, Shared.Nat.dec(L), sp), rq: Le(A, q, q2, L, sq)) ->
  Le(A, Source.Parse.take_if(A, w, p, q), Source.Parse.take_if(A, w, p2, q2), L, sq):
  +s => +hl => Shared.Maybe.elim(List<&2, Nat>, Source.Bytes.strip(w, Source.Parse.gap(s, False{})),
    m => Strip.Ok(m, w, Source.Parse.gap(s, False{})) -> Res.Le(A,
      Source.Parse.bind.of(Bool, A, c => Source.Bool.if(Source.Parse(A), c, p, q), Source.Parse.take.of(m, Source.Parse.gap(s, False{}))),
      Source.Parse.bind.of(Bool, A, c => Source.Bool.if(Source.Parse(A), c, p2, q2), Source.Parse.take.of(m, Source.Parse.gap(s, False{}))),
      s, sq),
    +r => hm => Le.take_if.some(A, p, p2, r, s, L, sp, sq, rp,
      Shared.Nat.is_le_trans(1n+List.length(&2, Nat, r), Nat.add(List.length(&2, Nat, w), List.length(&2, Nat, r)), List.length(&2, Nat, s),
        Nat.is_le_one_add(List.length(&2, Nat, w), List.length(&2, Nat, r), hw),
        Shared.Nat.is_le_trans(Nat.add(List.length(&2, Nat, w), List.length(&2, Nat, r)), List.length(&2, Nat, Source.Parse.gap(s, False{})), List.length(&2, Nat, s), hm, Gap.le(s, False{}))),
      hl),
    hm => Res.widen(A, q(Source.Parse.gap(s, False{})), q2(Source.Parse.gap(s, False{})), Source.Parse.gap(s, False{}), s, False{}, sq, Gap.le(s, False{}),
      rq(Source.Parse.gap(s, False{}), Shared.Nat.is_le_trans(List.length(&2, Nat, Source.Parse.gap(s, False{})), List.length(&2, Nat, s), L, Gap.le(s, False{}), hl))))(Strip.le(w, Source.Parse.gap(s, False{})))

# p when the word w comes next, not taken; else q
def Le.sees_if(-A: Data, +w: List<&2, Nat>, p: Source.Parse(A), p2: Source.Parse(A), q: Source.Parse(A),
  q2: Source.Parse(A), +L: Nat, +st: Bool, rp: Le(A, p, p2, L, st), rq: Le(A, q, q2, L, st)) ->
  Le(A, Source.Parse.sees_if(A, w, p, q), Source.Parse.sees_if(A, w, p2, q2), L, st):
  +s => +hl => Shared.Maybe.elim(List<&2, Nat>, Source.Bytes.strip(w, Source.Parse.gap(s, False{})),
    m => Res.Le(A,
      Source.Parse.bind.of(Bool, A, c => Source.Bool.if(Source.Parse(A), c, p, q), Source.Parse.sees.of(m, Source.Parse.gap(s, False{}))),
      Source.Parse.bind.of(Bool, A, c => Source.Bool.if(Source.Parse(A), c, p2, q2), Source.Parse.sees.of(m, Source.Parse.gap(s, False{}))),
      s, st),
    r => Res.widen(A, p(Source.Parse.gap(s, False{})), p2(Source.Parse.gap(s, False{})), Source.Parse.gap(s, False{}), s, False{}, st, Gap.le(s, False{}),
      rp(Source.Parse.gap(s, False{}), Shared.Nat.is_le_trans(List.length(&2, Nat, Source.Parse.gap(s, False{})), List.length(&2, Nat, s), L, Gap.le(s, False{}), hl))),
    Res.widen(A, q(Source.Parse.gap(s, False{})), q2(Source.Parse.gap(s, False{})), Source.Parse.gap(s, False{}), s, False{}, st, Gap.le(s, False{}),
      rq(Source.Parse.gap(s, False{}), Shared.Nat.is_le_trans(List.length(&2, Nat, Source.Parse.gap(s, False{})), List.length(&2, Nat, s), L, Gap.le(s, False{}), hl))))

# the word w, taken, then p on a shorter text
def Le.eat(-A: Data, +w: List<&2, Nat>, +hw: {Nat.is_le(1n, List.length(&2, Nat, w)) == True{} : Bool}, p: Source.Parse(A), p2: Source.Parse(A), +L: Nat,
  +sp: Bool, rp: Le(A, p, p2, Shared.Nat.dec(L), sp)) ->
  Le(A, Source.Parse.bind(Unit, A, Source.Parse.eat(w), u => p), Source.Parse.bind(Unit, A, Source.Parse.eat(w), u => p2),
    L, True{}):
  Le.bind1(Unit, A, Source.Parse.eat(w), Source.Parse.eat(w), u => p, u => p2, L, sp,
    Le.take_if(Unit, w, hw, Source.Parse.pure(Unit, Unit{}), Source.Parse.pure(Unit, Unit{}), Source.Parse.fail(Unit),
      Source.Parse.fail(Unit), L, False{}, True{}, Le.pure(Unit, Unit{}, Shared.Nat.dec(L)), Le.fail(Unit, L, True{})),
    u => rp)

def Name.elim(x: Source.Parsed<List<&2, Nat>>, -P: Source.Parsed<List<&2, Nat>> -> Type, nil: @t:List<&2, Nat> -> P(Source.Parsed.ok{Nil{}, t}),
  cons: @b:Nat -> @n:List<&2, Nat> -> @t:List<&2, Nat> -> P(Source.Parsed.ok{Con{b, n}, t}), fail: P(Source.Parsed.fail{})) -> P(x):
  match x:
    case Source.Parsed.ok{Nil{}, t}:
      nil(t)
    case Source.Parsed.ok{Con{b, n}, t}:
      cons(b, n, t)
    case Source.Parsed.fail{}:
      fail

def Le.name(+L: Nat) -> Le(List<&2, Nat>, Source.Parse.name, Source.Parse.name, L, True{}):
  +s => hl => Name.elim(Source.Parse.span(Source.Parse.gap(s, False{})),
    x => Span.Ok(x, Source.Parse.gap(s, False{})) -> Res.Le(List<&2, Nat>, Source.Parse.name.of(x), Source.Parse.name.of(x), s, True{}),
    t => h => Unit{},
    b => +n => +t => h => ({==}, Shared.Nat.is_le_trans(1n+List.length(&2, Nat, t), List.length(&2, Nat, Source.Parse.gap(s, False{})), List.length(&2, Nat, s),
      Shared.Nat.is_le_trans(1n+List.length(&2, Nat, t), 1n+Nat.add(List.length(&2, Nat, n), List.length(&2, Nat, t)), List.length(&2, Nat, Source.Parse.gap(s, False{})),
        Nat.is_le_add_left(List.length(&2, Nat, t), List.length(&2, Nat, n)), h), Gap.le(s, False{}))),
    h => Unit{})(Span.le(Source.Parse.gap(s, False{})))

def Lst.elim(xs: List<&2, Nat>, -P: List<&2, Nat> -> Type, nil: P(Nil{}), cons: @b:Nat -> @r:List<&2, Nat> -> P(Con{b, r})) -> P(xs):
  match xs:
    case Nil{}:
      nil
    case Con{b, r}:
      cons(b, r)

def Le.peek(L: Nat) -> Le(Nat, Source.Parse.peek, Source.Parse.peek, L, False{}):
  +s => hl => Lst.elim(Source.Parse.gap(s, False{}),
    g => {Nat.is_le(List.length(&2, Nat, g), List.length(&2, Nat, s)) == True{} : Bool} -> Res.Le(Nat, Source.Parse.peek.of(g), Source.Parse.peek.of(g), s, False{}),
    h => ({==}, Shared.Nat.is_le_zero(List.length(&2, Nat, s))),
    b => r => h => ({==}, h))(Gap.le(s, False{}))
