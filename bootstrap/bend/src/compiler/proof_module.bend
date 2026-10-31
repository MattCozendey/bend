# compiler: the round trip of the compiler's modules
# ==================================================
#
# Wasm.decode.module reads back the module of Cir.module that Wasm.encode
# writes (module.round, at the end). The bytes are the header and six
# sections whose contents stay variables (secs.six reads them back, with fuel
# of the form g + |rest|); the parts are then decoded one by one: the memory's
# limits (part.mem), the two codes (part.code, with I.instrs.round on each
# body; fits.stmt shows that Cir.code.stmt emits no br_table) and the data
# segment (part.data). The sizes that must fit a U32 come from the premises
# with the limits kept as variables (round.sized), so that the checker never
# expands 2^26, 2^32 - 1 or 50000.

import Base
import ./impl.bend as C
import ./proof_leb.bend as L
import ./proof_instrs.bend as I
import ./proof_need.bend as N
import ./proof_img.bend as G

# Lists
# -----

def app.nil(xs: List<&2, U32>) -> {List.append(&2, U32, xs, []) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, l => Con{x, l}, List.append(&2, U32, t, []), t, app.nil(t))

def app.assoc(xs: List<&2, U32>, +ys: List<&2, U32>, +zs: List<&2, U32>) ->
  {List.append(&2, U32, List.append(&2, U32, xs, ys), zs) == List.append(&2, U32, xs, List.append(&2, U32, ys, zs)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, l => Con{x, l},
        List.append(&2, U32, List.append(&2, U32, t, ys), zs), List.append(&2, U32, t, List.append(&2, U32, ys, zs)), app.assoc(t, ys, zs))

def len.app(xs: List<&2, U32>, +ys: List<&2, U32>) ->
  {List.length(&2, U32, List.append(&2, U32, xs, ys)) == Nat.add(List.length(&2, U32, xs), List.length(&2, U32, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, U32, List.append(&2, U32, t, ys)),
        Nat.add(List.length(&2, U32, t), List.length(&2, U32, ys)), len.app(t, ys))

def add.assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, Nat.add(b, c)), Nat.add(Nat.add(p, b), c), add.assoc(p, b, c))

# the bytes xs, then ys: |xs| of them are xs
def take.app(xs: List<&2, U32>, +ys: List<&2, U32>) ->
  {C.Wasm.decode.take(List.length(&2, U32, xs), List.append(&2, U32, xs, ys)) == Some{C.Wasm.Decoded{xs, ys}} : Maybe<&2, C.Wasm.Decoded<List<&2, U32>>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Maybe<&2, C.Wasm.Decoded<List<&2, U32>>>, C.Wasm.decode.take(List.length(&2, U32, t), List.append(&2, U32, t, ys)),
        Some{C.Wasm.Decoded{t, ys}}, take.app(t, ys)) :
        {C.Wasm.decode.cons(U32, x, _) == Some{C.Wasm.Decoded{Con{x, t}, ys}} : Maybe<&2, C.Wasm.Decoded<List<&2, U32>>>}
      {==}

# every list holds 0 bytes
def has0(xs: List<&2, U32>) -> {C.Wasm.has(xs, 0) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{_, _}:
      {==}

# Lengths that fit a U32
# ----------------------

# 1 + a fits a word: a + 1 is not 0
def nz.go(b: Bool, +w: Word(32n), e: {U32.is_zero(U32{Word.inc(32n, w)}) == b : Bool},
  l: N.Le(1n, Word.to_nat(32n, Word.inc(32n, w)))) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      +z = L.Word.eq_zero(32n, Word.inc(32n, w), e)
      Empty.absurd({True{} == False{} : Bool},
        N.le_rw_r(1n, Word.to_nat(32n, Word.inc(32n, w)), Word.to_nat(32n, Word.zero(32n)),
          Equal.cong(Word(32n), Nat, x => Word.to_nat(32n, x), Word.inc(32n, w), Word.zero(32n), z), l))

def nz.of(a: U32, l: N.Le(1n, U32.to_nat(U32.inc(a)))) -> {U32.is_zero(U32.inc(a)) == False{} : Bool}:
  match a:
    case U32{+w}:
      nz.go(U32.is_zero(U32{Word.inc(32n, w)}), w, {==}, l)

def nz(+a: U32, +M: U32, h: N.Le(1n+U32.to_nat(a), U32.to_nat(M))) -> {U32.is_zero(U32.inc(a)) == False{} : Bool}:
  nz.of(a, N.le_trans(1n, 1n+U32.to_nat(a), U32.to_nat(U32.inc(a)), N.le_zero(U32.to_nat(a)), G.U32.inc_ge(a, M, h)))

# a list of at most M bytes: each suffix's length, plus one, is not 0
def fits.of_le(xs: List<&2, U32>, +M: U32, +h: N.Le(List.length(&2, U32, xs), U32.to_nat(M))) -> {I.fits.labels(xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{_, +t}:
      +ih = fits.of_le(t, M, N.weaken(List.length(&2, U32, t), U32.to_nat(M), h))
      +n = I.labels.nat(t, ih)
      +h2 = N.le_rw_l(1n+List.length(&2, U32, t), 1n+U32.to_nat(C.Wasm.encode.len(U32, t)), U32.to_nat(M),
        Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, U32, t), U32.to_nat(C.Wasm.encode.len(U32, t)), n), h)
      +z = nz(C.Wasm.encode.len(U32, t), M, h2)
      %Equal.sym(Bool, U32.is_zero(U32.inc(C.Wasm.encode.len(U32, t))), False{}, z) : {Bool.and(Bool.not(_), I.fits.labels(t)) == True{} : Bool}
      ih

# xs, then A, hold as many bytes as xs has
def has.app(xs: List<&2, U32>, +A: List<&2, U32>, +h: {I.fits.labels(xs) == True{} : Bool}) ->
  {C.Wasm.has(List.append(&2, U32, xs, A), C.Wasm.encode.len(U32, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      has0(A)
    case Con{+y, +t}:
      +z = U32.is_zero(U32.inc(C.Wasm.encode.len(U32, t)))
      I.has.inc(y, [], List.append(&2, U32, t, A), C.Wasm.encode.len(U32, t),
        I.not.t(z, I.and.l(Bool.not(z), I.fits.labels(t), h)),
        has.app(t, A, I.and.r(Bool.not(z), I.fits.labels(t), h)))

# Vectors and sections
# --------------------

# the number of the bytes c, then c and acc: |c|
def count.sized(+c: List<&2, U32>, +acc: List<&2, U32>, +h: {I.fits.labels(c) == True{} : Bool}) ->
  {C.Wasm.decode.count(List.append(&2, U32, C.Wasm.encode.uleb(C.Wasm.encode.len(U32, c)), List.append(&2, U32, c, acc))) ==
    Some{C.Wasm.Decoded{List.length(&2, U32, c), List.append(&2, U32, c, acc)}} : Maybe<&2, C.Wasm.Decoded<Nat>>}:
  +X = List.append(&2, U32, c, acc)
  +v = C.Wasm.encode.len(U32, c)
  %I.uleb.back(v, X) : {C.Wasm.decode.bind(U32, Nat, _, +n => +r => C.Wasm.decode.count.if(C.Wasm.has(r, n), n, r)) ==
    Some{C.Wasm.Decoded{List.length(&2, U32, c), X}} : Maybe<&2, C.Wasm.Decoded<Nat>>}
  %Equal.sym(Bool, C.Wasm.has(X, v), True{}, has.app(c, acc, h)) : {C.Wasm.decode.count.if(_, v, X) ==
    Some{C.Wasm.Decoded{List.length(&2, U32, c), X}} : Maybe<&2, C.Wasm.Decoded<Nat>>}
  %I.labels.nat(c, h) : {Some{C.Wasm.Decoded{_, X}} == Some{C.Wasm.Decoded{List.length(&2, U32, c), X}} : Maybe<&2, C.Wasm.Decoded<Nat>>}
  {==}

# a section of the content c, then acc
def sec.round(+id: U32, +c: List<&2, U32>, +acc: List<&2, U32>, +h: {I.fits.labels(c) == True{} : Bool}) ->
  {C.Wasm.decode.section(C.Wasm.encode.section(id, c, acc)) == Some{C.Wasm.Decoded{C.Wasm.Section{id, c}, acc}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Section>>}:
  +u = C.Wasm.encode.uleb(C.Wasm.encode.len(U32, c))
  +X = List.append(&2, U32, c, acc)
  %Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, u, c), acc), List.append(&2, U32, u, X), app.assoc(u, c, acc)) :
    {C.Wasm.decode.section(Con{id, _}) == Some{C.Wasm.Decoded{C.Wasm.Section{id, c}, acc}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Section>>}
  %Equal.sym(Maybe<&2, C.Wasm.Decoded<Nat>>, C.Wasm.decode.count(List.append(&2, U32, u, X)), Some{C.Wasm.Decoded{List.length(&2, U32, c), X}}, count.sized(c, acc, h)) :
    {C.Wasm.decode.bind(Nat, C.Wasm.Section, _, n => r =>
      C.Wasm.decode.bind(List<&2, U32>, C.Wasm.Section, C.Wasm.decode.take(n, r), c2 => r2 =>
        Some{C.Wasm.Decoded{C.Wasm.Section{id, c2}, r2}})) == Some{C.Wasm.Decoded{C.Wasm.Section{id, c}, acc}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Section>>}
  %Equal.sym(Maybe<&2, C.Wasm.Decoded<List<&2, U32>>>, C.Wasm.decode.take(List.length(&2, U32, c), X), Some{C.Wasm.Decoded{c, acc}}, take.app(c, acc)) :
    {C.Wasm.decode.bind(List<&2, U32>, C.Wasm.Section, _, c2 => r2 =>
        Some{C.Wasm.Decoded{C.Wasm.Section{id, c2}, r2}}) == Some{C.Wasm.Decoded{C.Wasm.Section{id, c}, acc}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Section>>}
  {==}

# the fuel g + |the section|: 1 more than g, its size, and the bytes after it
def fuel.sec(+g: Nat, +id: U32, +c: List<&2, U32>, +acc: List<&2, U32>) ->
  {Nat.add(g, List.length(&2, U32, C.Wasm.encode.section(id, c, acc))) ==
    1n+Nat.add(Nat.add(g, List.length(&2, U32, C.Wasm.encode.sized(c))), List.length(&2, U32, acc)) : Nat}:
  +s = C.Wasm.encode.sized(c)
  +ls = List.length(&2, U32, s)
  +la = List.length(&2, U32, acc)
  +lx = List.length(&2, U32, List.append(&2, U32, s, acc))
  Equal.trans(Nat, Nat.add(g, 1n+lx), 1n+Nat.add(g, lx), 1n+Nat.add(Nat.add(g, ls), la),
    I.add.succ(g, lx),
    Equal.cong(Nat, Nat, n => 1n+n, Nat.add(g, lx), Nat.add(Nat.add(g, ls), la),
      Equal.trans(Nat, Nat.add(g, lx), Nat.add(g, Nat.add(ls, la)), Nat.add(Nat.add(g, ls), la),
        Equal.cong(Nat, Nat, n => Nat.add(g, n), lx, Nat.add(ls, la), len.app(s, acc)),
        add.assoc(g, ls, la))))

# the sections, from one of the content c
def secs.step(+g: Nat, +id: U32, +c: List<&2, U32>, +acc: List<&2, U32>, -ss: List<&2, C.Wasm.Section>,
  +h: {I.fits.labels(c) == True{} : Bool},
  rest: {C.Wasm.decode.sections(Nat.add(Nat.add(g, List.length(&2, U32, C.Wasm.encode.sized(c))), List.length(&2, U32, acc)), acc) == Some{ss} : Maybe<&2, List<&2, C.Wasm.Section>>}
) -> {C.Wasm.decode.sections(Nat.add(g, List.length(&2, U32, C.Wasm.encode.section(id, c, acc))), C.Wasm.encode.section(id, c, acc)) ==
    Some{Con{C.Wasm.Section{id, c}, ss}} : Maybe<&2, List<&2, C.Wasm.Section>>}:
  +S = C.Wasm.encode.section(id, c, acc)
  +F = Nat.add(Nat.add(g, List.length(&2, U32, C.Wasm.encode.sized(c))), List.length(&2, U32, acc))
  %Equal.sym(Nat, Nat.add(g, List.length(&2, U32, S)), 1n+F, fuel.sec(g, id, c, acc)) :
    {C.Wasm.decode.sections(_, S) == Some{Con{C.Wasm.Section{id, c}, ss}} : Maybe<&2, List<&2, C.Wasm.Section>>}
  %Equal.sym(Maybe<&2, C.Wasm.Decoded<C.Wasm.Section>>, C.Wasm.decode.section(S), Some{C.Wasm.Decoded{C.Wasm.Section{id, c}, acc}}, sec.round(id, c, acc, h)) :
    {C.Wasm.decode.sections.got(_, r => C.Wasm.decode.sections(F, r)) == Some{Con{C.Wasm.Section{id, c}, ss}} : Maybe<&2, List<&2, C.Wasm.Section>>}
  %Equal.sym(Maybe<&2, List<&2, C.Wasm.Section>>, C.Wasm.decode.sections(F, acc), Some{ss}, rest) :
    {C.Wasm.decode.sections.cons(C.Wasm.Section{id, c}, _) == Some{Con{C.Wasm.Section{id, c}, ss}} : Maybe<&2, List<&2, C.Wasm.Section>>}
  {==}

def secs.nil(f: Nat) -> {C.Wasm.decode.sections(f, []) == Some{[]} : Maybe<&2, List<&2, C.Wasm.Section>>}:
  match f:
    case 0n:
      {==}
    case 1n+p:
      {==}

# the six sections of the contents c1 to c11
def secs.bytes(c1: List<&2, U32>, c3: List<&2, U32>, c5: List<&2, U32>, c7: List<&2, U32>, c10: List<&2, U32>, c11: List<&2, U32>) -> List<&2, U32>:
  C.Wasm.encode.section(1, c1, C.Wasm.encode.section(3, c3, C.Wasm.encode.section(5, c5,
    C.Wasm.encode.section(7, c7, C.Wasm.encode.section(10, c10, C.Wasm.encode.section(11, c11, []))))))

def secs.six(+c1: List<&2, U32>, +c3: List<&2, U32>, +c5: List<&2, U32>, +c7: List<&2, U32>, +c10: List<&2, U32>, +c11: List<&2, U32>,
  +h1: {I.fits.labels(c1) == True{} : Bool}, +h3: {I.fits.labels(c3) == True{} : Bool}, +h5: {I.fits.labels(c5) == True{} : Bool},
  +h7: {I.fits.labels(c7) == True{} : Bool}, +h10: {I.fits.labels(c10) == True{} : Bool}, +h11: {I.fits.labels(c11) == True{} : Bool}
) -> {C.Wasm.decode.sections(List.length(&2, U32, secs.bytes(c1, c3, c5, c7, c10, c11)), secs.bytes(c1, c3, c5, c7, c10, c11)) ==
    Some{[C.Wasm.Section{1, c1}, C.Wasm.Section{3, c3}, C.Wasm.Section{5, c5}, C.Wasm.Section{7, c7}, C.Wasm.Section{10, c10}, C.Wasm.Section{11, c11}]} :
    Maybe<&2, List<&2, C.Wasm.Section>>}:
  +S11 = C.Wasm.encode.section(11, c11, [])
  +S10 = C.Wasm.encode.section(10, c10, S11)
  +S7 = C.Wasm.encode.section(7, c7, S10)
  +S5 = C.Wasm.encode.section(5, c5, S7)
  +S3 = C.Wasm.encode.section(3, c3, S5)
  +g1 = Nat.add(0n, List.length(&2, U32, C.Wasm.encode.sized(c1)))
  +g3 = Nat.add(g1, List.length(&2, U32, C.Wasm.encode.sized(c3)))
  +g5 = Nat.add(g3, List.length(&2, U32, C.Wasm.encode.sized(c5)))
  +g7 = Nat.add(g5, List.length(&2, U32, C.Wasm.encode.sized(c7)))
  +g10 = Nat.add(g7, List.length(&2, U32, C.Wasm.encode.sized(c10)))
  +g11 = Nat.add(g10, List.length(&2, U32, C.Wasm.encode.sized(c11)))
  secs.step(0n, 1, c1, S3, [C.Wasm.Section{3, c3}, C.Wasm.Section{5, c5}, C.Wasm.Section{7, c7}, C.Wasm.Section{10, c10}, C.Wasm.Section{11, c11}], h1,
    secs.step(g1, 3, c3, S5, [C.Wasm.Section{5, c5}, C.Wasm.Section{7, c7}, C.Wasm.Section{10, c10}, C.Wasm.Section{11, c11}], h3,
      secs.step(g3, 5, c5, S7, [C.Wasm.Section{7, c7}, C.Wasm.Section{10, c10}, C.Wasm.Section{11, c11}], h5,
        secs.step(g5, 7, c7, S10, [C.Wasm.Section{10, c10}, C.Wasm.Section{11, c11}], h7,
          secs.step(g7, 10, c10, S11, [C.Wasm.Section{11, c11}], h10,
            secs.step(g10, 11, c11, [], [], h11, secs.nil(Nat.add(g11, 0n))))))))

# Modules
# -------

# Wasm.decode.module.parts, from the decoded items of its sections
def parts(
  ts: Maybe<&2, List<&2, C.Wasm.Type>>, idx: Maybe<&2, List<&2, U32>>, mem: Maybe<&2, Maybe<&2, C.Wasm.Limits>>,
  es: Maybe<&2, List<&2, C.Wasm.Export>>, cs: Maybe<&2, List<&2, C.Wasm.Code>>, seg: Maybe<&2, Maybe<&2, C.Wasm.Segment>>
) -> Maybe<&2, C.Wasm.Module>:
  Maybe.bind(&2, List<&2, C.Wasm.Type>, C.Wasm.Module, ts, ts2 =>
    Maybe.bind(&2, List<&2, U32>, C.Wasm.Module, idx, idx2 =>
      Maybe.bind(&2, Maybe<&2, C.Wasm.Limits>, C.Wasm.Module, mem, mem2 =>
        Maybe.bind(&2, List<&2, C.Wasm.Export>, C.Wasm.Module, es, es2 =>
          Maybe.bind(&2, List<&2, C.Wasm.Code>, C.Wasm.Module, cs, cs2 =>
            Maybe.bind(&2, Maybe<&2, C.Wasm.Segment>, C.Wasm.Module, seg, seg2 =>
              Maybe.bind(&2, List<&2, C.Wasm.Func>, C.Wasm.Module, C.Wasm.funcs.of(ts2, idx2, cs2), fs =>
                Some{C.Wasm.Module{fs, mem2, es2, seg2}})))))))

# a module of the six sections decodes to the items of their contents
def mod.of(+c1: List<&2, U32>, +c3: List<&2, U32>, +c5: List<&2, U32>, +c7: List<&2, U32>, +c10: List<&2, U32>, +c11: List<&2, U32>,
  +h1: {I.fits.labels(c1) == True{} : Bool}, +h3: {I.fits.labels(c3) == True{} : Bool}, +h5: {I.fits.labels(c5) == True{} : Bool},
  +h7: {I.fits.labels(c7) == True{} : Bool}, +h10: {I.fits.labels(c10) == True{} : Bool}, +h11: {I.fits.labels(c11) == True{} : Bool}
) -> {C.Wasm.decode.module(Con{0, Con{97, Con{115, Con{109, Con{1, Con{0, Con{0, Con{0, secs.bytes(c1, c3, c5, c7, c10, c11)}}}}}}}}) ==
    parts(C.Wasm.decode.part(~C.Wasm.Type, ~C.Wasm.decode.functype, Some{c1}),
      C.Wasm.decode.part(~U32, ~C.Wasm.decode.u32, Some{c3}),
      C.Wasm.decode.one(C.Wasm.Limits, C.Wasm.decode.part(~C.Wasm.Limits, ~C.Wasm.decode.limits, Some{c5})),
      C.Wasm.decode.part(~C.Wasm.Export, ~C.Wasm.decode.export, Some{c7}),
      C.Wasm.decode.part(~C.Wasm.Code, ~C.Wasm.decode.code, Some{c10}),
      C.Wasm.decode.one(C.Wasm.Segment, C.Wasm.decode.part(~C.Wasm.Segment, ~C.Wasm.decode.data, Some{c11}))) : Maybe<&2, C.Wasm.Module>}:
  +B = secs.bytes(c1, c3, c5, c7, c10, c11)
  %Equal.sym(Maybe<&2, List<&2, C.Wasm.Section>>, C.Wasm.decode.sections(List.length(&2, U32, B), B),
    Some{[C.Wasm.Section{1, c1}, C.Wasm.Section{3, c3}, C.Wasm.Section{5, c5}, C.Wasm.Section{7, c7}, C.Wasm.Section{10, c10}, C.Wasm.Section{11, c11}]},
    secs.six(c1, c3, c5, c7, c10, c11, h1, h3, h5, h7, h10, h11)) :
    {C.Wasm.decode.module.sections(_) ==
    parts(C.Wasm.decode.part(~C.Wasm.Type, ~C.Wasm.decode.functype, Some{c1}),
      C.Wasm.decode.part(~U32, ~C.Wasm.decode.u32, Some{c3}),
      C.Wasm.decode.one(C.Wasm.Limits, C.Wasm.decode.part(~C.Wasm.Limits, ~C.Wasm.decode.limits, Some{c5})),
      C.Wasm.decode.part(~C.Wasm.Export, ~C.Wasm.decode.export, Some{c7}),
      C.Wasm.decode.part(~C.Wasm.Code, ~C.Wasm.decode.code, Some{c10}),
      C.Wasm.decode.one(C.Wasm.Segment, C.Wasm.decode.part(~C.Wasm.Segment, ~C.Wasm.decode.data, Some{c11}))) : Maybe<&2, C.Wasm.Module>}
  {==}

# The memory section
# ------------------

# a vector of one item, then the byte y
def count1(+y: U32, +U: List<&2, U32>) -> {C.Wasm.decode.count(Con{1, Con{y, U}}) == Some{C.Wasm.Decoded{1n, Con{y, U}}} : Maybe<&2, C.Wasm.Decoded<Nat>>}:
  %Equal.sym(Bool, C.Wasm.has(Con{y, U}, 1), True{}, has0(U)) :
    {C.Wasm.decode.count.if(_, 1, Con{y, U}) == Some{C.Wasm.Decoded{1n, Con{y, U}}} : Maybe<&2, C.Wasm.Decoded<Nat>>}
  {==}

def lim(+P: U32) -> {C.Wasm.decode.limits(Con{0, C.Wasm.encode.uleb(P)}) == Some{C.Wasm.Decoded{C.Wasm.Limits{P, None{}}, []}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Limits>>}:
  +U = C.Wasm.encode.uleb(P)
  %app.nil(U) : {C.Wasm.decode.limits(Con{0, _}) == Some{C.Wasm.Decoded{C.Wasm.Limits{P, None{}}, []}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Limits>>}
  %I.uleb.back(P, []) : {C.Wasm.decode.bind(U32, C.Wasm.Limits, _, n => r => Some{C.Wasm.Decoded{C.Wasm.Limits{n, None{}}, r}}) ==
    Some{C.Wasm.Decoded{C.Wasm.Limits{P, None{}}, []}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Limits>>}
  {==}

# the memory section's content decodes to its limits
def part.mem(+P: U32) ->
  {C.Wasm.decode.one(C.Wasm.Limits, C.Wasm.decode.part(~C.Wasm.Limits, ~C.Wasm.decode.limits, Some{Con{1, Con{0, C.Wasm.encode.uleb(P)}}})) ==
    Some{Some{C.Wasm.Limits{P, None{}}}} : Maybe<&2, Maybe<&2, C.Wasm.Limits>>}:
  +U = C.Wasm.encode.uleb(P)
  %Equal.sym(Maybe<&2, C.Wasm.Decoded<Nat>>, C.Wasm.decode.count(Con{1, Con{0, U}}), Some{C.Wasm.Decoded{1n, Con{0, U}}}, count1(0, U)) :
    {C.Wasm.decode.one(C.Wasm.Limits, C.Wasm.decode.done(List<&2, C.Wasm.Limits>,
      C.Wasm.decode.bind(Nat, List<&2, C.Wasm.Limits>, _, n => r => C.Wasm.decode.items(~C.Wasm.Limits, ~C.Wasm.decode.limits, n, r)))) ==
      Some{Some{C.Wasm.Limits{P, None{}}}} : Maybe<&2, Maybe<&2, C.Wasm.Limits>>}
  %Equal.sym(Maybe<&2, C.Wasm.Decoded<C.Wasm.Limits>>, C.Wasm.decode.limits(Con{0, U}), Some{C.Wasm.Decoded{C.Wasm.Limits{P, None{}}, []}}, lim(P)) :
    {C.Wasm.decode.one(C.Wasm.Limits, C.Wasm.decode.done(List<&2, C.Wasm.Limits>,
      C.Wasm.decode.bind(C.Wasm.Limits, List<&2, C.Wasm.Limits>, _, x => r =>
        C.Wasm.decode.cons(C.Wasm.Limits, x, C.Wasm.decode.items(~C.Wasm.Limits, ~C.Wasm.decode.limits, 0n, r))))) ==
      Some{Some{C.Wasm.Limits{P, None{}}}} : Maybe<&2, Maybe<&2, C.Wasm.Limits>>}
  {==}

# The data section
# ----------------

def dbytes(+B: List<&2, U32>, +h: {I.fits.labels(B) == True{} : Bool}) ->
  {C.Wasm.decode.bytes(C.Wasm.encode.sized(B)) == Some{C.Wasm.Decoded{B, []}} : Maybe<&2, C.Wasm.Decoded<List<&2, U32>>>}:
  +u = C.Wasm.encode.uleb(C.Wasm.encode.len(U32, B))
  %app.nil(B) : {C.Wasm.decode.bytes(List.append(&2, U32, u, _)) == Some{C.Wasm.Decoded{B, []}} : Maybe<&2, C.Wasm.Decoded<List<&2, U32>>>}
  %Equal.sym(Maybe<&2, C.Wasm.Decoded<Nat>>, C.Wasm.decode.count(List.append(&2, U32, u, List.append(&2, U32, B, []))),
    Some{C.Wasm.Decoded{List.length(&2, U32, B), List.append(&2, U32, B, [])}}, count.sized(B, [], h)) :
    {C.Wasm.decode.bind(Nat, List<&2, U32>, _, n => r => C.Wasm.decode.take(n, r)) == Some{C.Wasm.Decoded{B, []}} : Maybe<&2, C.Wasm.Decoded<List<&2, U32>>>}
  take.app(B, [])

def ddata(+B: List<&2, U32>, +h: {I.fits.labels(B) == True{} : Bool}) ->
  {C.Wasm.decode.data(Con{0, Con{65, List.append(&2, U32, C.Wasm.encode.sleb(20), Con{11, C.Wasm.encode.sized(B)})}}) ==
    Some{C.Wasm.Decoded{C.Wasm.Segment{20, B}, []}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Segment>>}:
  %Equal.sym(Maybe<&2, C.Wasm.Decoded<List<&2, U32>>>, C.Wasm.decode.bytes(C.Wasm.encode.sized(B)), Some{C.Wasm.Decoded{B, []}}, dbytes(B, h)) :
    {C.Wasm.decode.bind(List<&2, U32>, C.Wasm.Segment, _, b => r4 => Some{C.Wasm.Decoded{C.Wasm.Segment{20, b}, r4}}) ==
      Some{C.Wasm.Decoded{C.Wasm.Segment{20, B}, []}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Segment>>}
  {==}

# the data section's content decodes to its segment
def part.data(+B: List<&2, U32>, +h: {I.fits.labels(B) == True{} : Bool}) ->
  {C.Wasm.decode.one(C.Wasm.Segment, C.Wasm.decode.part(~C.Wasm.Segment, ~C.Wasm.decode.data,
    Some{Con{1, Con{0, Con{65, List.append(&2, U32, C.Wasm.encode.sleb(20), Con{11, C.Wasm.encode.sized(B)})}}}})) ==
    Some{Some{C.Wasm.Segment{20, B}}} : Maybe<&2, Maybe<&2, C.Wasm.Segment>>}:
  +U = {Con{65, List.append(&2, U32, C.Wasm.encode.sleb(20), Con{11, C.Wasm.encode.sized(B)})} : List<&2, U32>}
  %Equal.sym(Maybe<&2, C.Wasm.Decoded<Nat>>, C.Wasm.decode.count(Con{1, Con{0, U}}), Some{C.Wasm.Decoded{1n, Con{0, U}}}, count1(0, U)) :
    {C.Wasm.decode.one(C.Wasm.Segment, C.Wasm.decode.done(List<&2, C.Wasm.Segment>,
      C.Wasm.decode.bind(Nat, List<&2, C.Wasm.Segment>, _, n => r => C.Wasm.decode.items(~C.Wasm.Segment, ~C.Wasm.decode.data, n, r)))) ==
      Some{Some{C.Wasm.Segment{20, B}}} : Maybe<&2, Maybe<&2, C.Wasm.Segment>>}
  %Equal.sym(Maybe<&2, C.Wasm.Decoded<C.Wasm.Segment>>, C.Wasm.decode.data(Con{0, U}), Some{C.Wasm.Decoded{C.Wasm.Segment{20, B}, []}}, ddata(B, h)) :
    {C.Wasm.decode.one(C.Wasm.Segment, C.Wasm.decode.done(List<&2, C.Wasm.Segment>,
      C.Wasm.decode.bind(C.Wasm.Segment, List<&2, C.Wasm.Segment>, _, x => r =>
        C.Wasm.decode.cons(C.Wasm.Segment, x, C.Wasm.decode.items(~C.Wasm.Segment, ~C.Wasm.decode.data, 0n, r))))) ==
      Some{Some{C.Wasm.Segment{20, B}}} : Maybe<&2, Maybe<&2, C.Wasm.Segment>>}
  {==}

# The code section
# ----------------

# an entry of the code section, whose code X decodes to Cd
def code.round(+X: List<&2, U32>, +rest: List<&2, U32>, -Cd: C.Wasm.Code, +hF: {I.fits.labels(X) == True{} : Bool},
  d: {C.Wasm.decode.func(X) == Some{C.Wasm.Decoded{Cd, []}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Code>>}) ->
  {C.Wasm.decode.code(List.append(&2, U32, C.Wasm.encode.sized(X), rest)) == Some{C.Wasm.Decoded{Cd, rest}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Code>>}:
  +u = C.Wasm.encode.uleb(C.Wasm.encode.len(U32, X))
  +Y = List.append(&2, U32, X, rest)
  %Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, u, X), rest), List.append(&2, U32, u, Y), app.assoc(u, X, rest)) :
    {C.Wasm.decode.code(_) == Some{C.Wasm.Decoded{Cd, rest}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Code>>}
  %Equal.sym(Maybe<&2, C.Wasm.Decoded<Nat>>, C.Wasm.decode.count(List.append(&2, U32, u, Y)), Some{C.Wasm.Decoded{List.length(&2, U32, X), Y}}, count.sized(X, rest, hF)) :
    {C.Wasm.decode.bind(Nat, C.Wasm.Code, _, n => r =>
      C.Wasm.decode.bind(List<&2, U32>, C.Wasm.Code, C.Wasm.decode.take(n, r), c => r2 =>
        C.Wasm.decode.whole(C.Wasm.Code, C.Wasm.decode.func(c), r2))) == Some{C.Wasm.Decoded{Cd, rest}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Code>>}
  %Equal.sym(Maybe<&2, C.Wasm.Decoded<List<&2, U32>>>, C.Wasm.decode.take(List.length(&2, U32, X), Y), Some{C.Wasm.Decoded{X, rest}}, take.app(X, rest)) :
    {C.Wasm.decode.bind(List<&2, U32>, C.Wasm.Code, _, c => r2 =>
        C.Wasm.decode.whole(C.Wasm.Code, C.Wasm.decode.func(c), r2)) == Some{C.Wasm.Decoded{Cd, rest}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Code>>}
  %Equal.sym(Maybe<&2, C.Wasm.Decoded<C.Wasm.Code>>, C.Wasm.decode.func(X), Some{C.Wasm.Decoded{Cd, []}}, d) :
    {C.Wasm.decode.whole(C.Wasm.Code, _, rest) == Some{C.Wasm.Decoded{Cd, rest}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Code>>}
  {==}

# two entries hold 2 bytes
def has.two(+ya: U32, +ta: List<&2, U32>, +Z: List<&2, U32>) ->
  {C.Wasm.has(List.append(&2, U32, C.Wasm.encode.sized(Con{ya, ta}), Z), 2) == True{} : Bool}:
  +u = C.Wasm.encode.uleb(C.Wasm.encode.len(U32, Con{ya, ta}))
  %Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, u, Con{ya, ta}), Z), List.append(&2, U32, u, Con{ya, List.append(&2, U32, ta, Z)}),
    app.assoc(u, Con{ya, ta}, Z)) : {C.Wasm.has(_, 2) == True{} : Bool}
  I.has.uleb(C.Wasm.encode.len(U32, Con{ya, ta}), Con{ya, List.append(&2, U32, ta, Z)}, 1, {==}, has0(List.append(&2, U32, ta, Z)))

# the code section's content, of two functions, decodes to their codes
def part.code(+ya: U32, +ta: List<&2, U32>, +XR: List<&2, U32>, -CA: C.Wasm.Code, -CR: C.Wasm.Code,
  +hA: {I.fits.labels(Con{ya, ta}) == True{} : Bool}, +hR: {I.fits.labels(XR) == True{} : Bool},
  dA: {C.Wasm.decode.func(Con{ya, ta}) == Some{C.Wasm.Decoded{CA, []}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Code>>},
  dR: {C.Wasm.decode.func(XR) == Some{C.Wasm.Decoded{CR, []}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Code>>}) ->
  {C.Wasm.decode.part(~C.Wasm.Code, ~C.Wasm.decode.code,
    Some{Con{2, List.append(&2, U32, C.Wasm.encode.sized(Con{ya, ta}), List.append(&2, U32, C.Wasm.encode.sized(XR), []))}}) ==
    Some{[CA, CR]} : Maybe<&2, List<&2, C.Wasm.Code>>}:
  +ZR = List.append(&2, U32, C.Wasm.encode.sized(XR), [])
  +Y = List.append(&2, U32, C.Wasm.encode.sized(Con{ya, ta}), ZR)
  %Equal.sym(Bool, C.Wasm.has(Y, 2), True{}, has.two(ya, ta, ZR)) :
    {C.Wasm.decode.done(List<&2, C.Wasm.Code>, C.Wasm.decode.bind(Nat, List<&2, C.Wasm.Code>, C.Wasm.decode.count.if(_, 2, Y), n => r =>
      C.Wasm.decode.items(~C.Wasm.Code, ~C.Wasm.decode.code, n, r))) == Some{[CA, CR]} : Maybe<&2, List<&2, C.Wasm.Code>>}
  %Equal.sym(Maybe<&2, C.Wasm.Decoded<C.Wasm.Code>>, C.Wasm.decode.code(Y), Some{C.Wasm.Decoded{CA, ZR}}, code.round(Con{ya, ta}, ZR, CA, hA, dA)) :
    {C.Wasm.decode.done(List<&2, C.Wasm.Code>, C.Wasm.decode.bind(C.Wasm.Code, List<&2, C.Wasm.Code>, _, x => r =>
      C.Wasm.decode.cons(C.Wasm.Code, x, C.Wasm.decode.items(~C.Wasm.Code, ~C.Wasm.decode.code, 1n, r)))) == Some{[CA, CR]} : Maybe<&2, List<&2, C.Wasm.Code>>}
  %Equal.sym(Maybe<&2, C.Wasm.Decoded<C.Wasm.Code>>, C.Wasm.decode.code(ZR), Some{C.Wasm.Decoded{CR, []}}, code.round(XR, [], CR, hR, dR)) :
    {C.Wasm.decode.done(List<&2, C.Wasm.Code>, C.Wasm.decode.cons(C.Wasm.Code, CA, C.Wasm.decode.bind(C.Wasm.Code, List<&2, C.Wasm.Code>, _, x => r =>
      C.Wasm.decode.cons(C.Wasm.Code, x, C.Wasm.decode.items(~C.Wasm.Code, ~C.Wasm.decode.code, 0n, r))))) == Some{[CA, CR]} : Maybe<&2, List<&2, C.Wasm.Code>>}
  {==}

# 0 + w = w
def Word.add0(n: Nat, w: Word(n)) -> {Word.adc(n, Word.zero(n), w, False{}, False{}) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x}, Word.adc(p, Word.zero(p), t, False{}, False{}), t, Word.add0(p, t))
        case WCon{True{}, t}:
          Equal.cong(Word(p), Word(1n+p), x => WCon{True{}, x}, Word.adc(p, Word.zero(p), t, False{}, False{}), t, Word.add0(p, t))

def U32.add0(x: U32) -> {U32.add(0, x) == x : U32}:
  match x:
    case U32{w}:
      Equal.cong(Word(32n), U32, y => U32{y}, Word.adc(32n, Word.zero(32n), w, False{}, False{}), w, Word.add0(32n, w))

# a function's code of 3 locals, whose body decodes to b
def func.three(+bs: List<&2, U32>, -b: List<&2, C.Wasm.Instr>,
  h: {C.Wasm.decode.instrs(1n+List.length(&2, U32, bs), bs) == Some{C.Wasm.Decoded{b, []}} : Maybe<&2, C.Wasm.Decoded<List<&2, C.Wasm.Instr>>>}) ->
  {C.Wasm.decode.func(Con{1, Con{3, Con{127, bs}}}) == Some{C.Wasm.Decoded{C.Wasm.Code{3n, b}, []}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Code>>}:
  %Equal.sym(Maybe<&2, C.Wasm.Decoded<List<&2, C.Wasm.Instr>>>, C.Wasm.decode.instrs(1n+List.length(&2, U32, bs), bs),
    Some{C.Wasm.Decoded{b, []}}, h) :
    {C.Wasm.decode.bind(List<&2, C.Wasm.Instr>, C.Wasm.Code, _, x => r => Some{C.Wasm.Decoded{C.Wasm.Code{U32.to_nat(3), x}, r}}) ==
      Some{C.Wasm.Decoded{C.Wasm.Code{3n, b}, []}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Code>>}
  {==}

# one group of N locals, then the bytes IR
def has.locals(+N: U32, +IR: List<&2, U32>) ->
  {C.Wasm.has(List.append(&2, U32, List.append(&2, U32, C.Wasm.encode.uleb(N), [127]), IR), 1) == True{} : Bool}:
  +u = C.Wasm.encode.uleb(N)
  %Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, u, [127]), IR), List.append(&2, U32, u, Con{127, IR}), app.assoc(u, [127], IR)) :
    {C.Wasm.has(_, 1) == True{} : Bool}
  I.has.uleb(N, Con{127, IR}, 0, {==}, has0(Con{127, IR}))

def local.round(+N: U32, +IR: List<&2, U32>) ->
  {C.Wasm.decode.local(List.append(&2, U32, List.append(&2, U32, C.Wasm.encode.uleb(N), [127]), IR)) == Some{C.Wasm.Decoded{N, IR}} : Maybe<&2, C.Wasm.Decoded<U32>>}:
  +u = C.Wasm.encode.uleb(N)
  %Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, u, [127]), IR), List.append(&2, U32, u, Con{127, IR}), app.assoc(u, [127], IR)) :
    {C.Wasm.decode.local(_) == Some{C.Wasm.Decoded{N, IR}} : Maybe<&2, C.Wasm.Decoded<U32>>}
  %I.uleb.back(N, Con{127, IR}) :
    {C.Wasm.decode.bind(U32, U32, _, n => r => C.Wasm.decode.bind(U32, U32, C.Wasm.decode.byte(127, r), t => r2 => Some{C.Wasm.Decoded{n, r2}})) ==
      Some{C.Wasm.Decoded{N, IR}} : Maybe<&2, C.Wasm.Decoded<U32>>}
  {==}

def locals.one(+N: U32, +hN: {U32.is_le(N, 50000) == True{} : Bool}) -> {C.Wasm.locals.sum([N], 0) == Some{N} : Maybe<&2, U32>}:
  %Equal.sym(U32, U32.add(0, N), N, U32.add0(N)) : {C.Wasm.locals.if(Bool.and(U32.is_le(N, 50000), U32.is_le(_, 50000)), u => C.Wasm.locals.sum([], _)) == Some{N} : Maybe<&2, U32>}
  %Equal.sym(Bool, U32.is_le(N, 50000), True{}, hN) : {C.Wasm.locals.if(Bool.and(_, _), u => C.Wasm.locals.sum([], N)) == Some{N} : Maybe<&2, U32>}
  {==}

# a function's code of one group of N locals, whose body decodes to b
def func.many(+N: U32, -n: Nat, +IR: List<&2, U32>, -b: List<&2, C.Wasm.Instr>,
  +hN: {U32.is_le(N, 50000) == True{} : Bool}, eN: {U32.to_nat(N) == n : Nat},
  h: {C.Wasm.decode.instrs(1n+List.length(&2, U32, IR), IR) == Some{C.Wasm.Decoded{b, []}} : Maybe<&2, C.Wasm.Decoded<List<&2, C.Wasm.Instr>>>}) ->
  {C.Wasm.decode.func(Con{1, List.append(&2, U32, List.append(&2, U32, C.Wasm.encode.uleb(N), [127]), IR)}) ==
    Some{C.Wasm.Decoded{C.Wasm.Code{n, b}, []}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Code>>}:
  +W = List.append(&2, U32, List.append(&2, U32, C.Wasm.encode.uleb(N), [127]), IR)
  %Equal.sym(Bool, C.Wasm.has(W, 1), True{}, has.locals(N, IR)) :
    {C.Wasm.decode.bind(List<&2, U32>, C.Wasm.Code,
      C.Wasm.decode.bind(Nat, List<&2, U32>, C.Wasm.decode.count.if(_, 1, W), n => r => C.Wasm.decode.items(~U32, ~C.Wasm.decode.local, n, r)),
      ns => r => C.Wasm.decode.func.body(C.Wasm.locals.sum(ns, 0), r)) == Some{C.Wasm.Decoded{C.Wasm.Code{n, b}, []}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Code>>}
  %Equal.sym(Maybe<&2, C.Wasm.Decoded<U32>>, C.Wasm.decode.local(W), Some{C.Wasm.Decoded{N, IR}}, local.round(N, IR)) :
    {C.Wasm.decode.bind(List<&2, U32>, C.Wasm.Code,
      C.Wasm.decode.bind(U32, List<&2, U32>, _, x => r => C.Wasm.decode.cons(U32, x, C.Wasm.decode.items(~U32, ~C.Wasm.decode.local, 0n, r))),
      ns => r => C.Wasm.decode.func.body(C.Wasm.locals.sum(ns, 0), r)) == Some{C.Wasm.Decoded{C.Wasm.Code{n, b}, []}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Code>>}
  %Equal.sym(Maybe<&2, U32>, C.Wasm.locals.sum([N], 0), Some{N}, locals.one(N, hN)) :
    {C.Wasm.decode.func.body(_, IR) == Some{C.Wasm.Decoded{C.Wasm.Code{n, b}, []}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Code>>}
  %Equal.sym(Maybe<&2, C.Wasm.Decoded<List<&2, C.Wasm.Instr>>>, C.Wasm.decode.instrs(1n+List.length(&2, U32, IR), IR),
    Some{C.Wasm.Decoded{b, []}}, h) :
    {C.Wasm.decode.bind(List<&2, C.Wasm.Instr>, C.Wasm.Code, _, x => r => Some{C.Wasm.Decoded{C.Wasm.Code{U32.to_nat(N), x}, r}}) ==
      Some{C.Wasm.Decoded{C.Wasm.Code{n, b}, []}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Code>>}
  %Equal.sym(Nat, U32.to_nat(N), n, eN) : {Some{C.Wasm.Decoded{C.Wasm.Code{_, b}, []}} == Some{C.Wasm.Decoded{C.Wasm.Code{n, b}, []}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Code>>}
  {==}

# Cir.code emits no br_table
# --------------------------

def fits.expr(e: C.Cir.Expr, +acc: List<&2, C.Wasm.Instr>) -> {I.fits(C.Cir.code.expr(e, acc)) == I.fits(acc) : Bool}:
  match e:
    case C.Cir.Expr.const{n}:
      {==}
    case C.Cir.Expr.get{r}:
      {==}
    case C.Cir.Expr.op{+o, +a, +b}:
      +X = C.Cir.code.expr(b, Con{C.Cir.i.op(o), acc})
      Equal.trans(Bool, I.fits(C.Cir.code.expr(a, X)), I.fits(X), I.fits(acc), fits.expr(a, X), fits.expr(b, Con{C.Cir.i.op(o), acc}))
    case C.Cir.Expr.eqz{+a}:
      fits.expr(a, Con{C.Wasm.Instr.eqz{}, acc})
    case C.Cir.Expr.field{+k, +c}:
      fits.expr(c, C.Cir.code.at(Con{C.Wasm.Instr.load{U32.shln(U32.from_nat(k), 2n)}, acc}))
    case C.Cir.Expr.byte{+i}:
      fits.expr(i, Con{C.Cir.i.get(0), Con{C.Cir.i.op(C.Wasm.Op.add{}), Con{C.Wasm.Instr.load8_u{0},
        Con{C.Cir.i.const(255), Con{C.Cir.i.op(C.Wasm.Op.and{}), acc}}}}})
    case C.Cir.Expr.size{}:
      {==}

def fits.result(z: Bool, +l: U32) -> {I.fits(List.append(&2, C.Wasm.Instr, C.Cir.code.result(z), [C.Wasm.Instr.br{l}])) == True{} : Bool}:
  match z:
    case True{}:
      {==}
    case False{}:
      {==}

def fits.stmt(s: C.Cir.Stmt, +d: Nat, +acc: List<&2, C.Wasm.Instr>) -> {I.fits(C.Cir.code.stmt(s, d, acc)) == I.fits(acc) : Bool}:
  match s:
    case C.Cir.Stmt.nop{}:
      {==}
    case C.Cir.Stmt.set{+r, +e}:
      fits.expr(e, Con{C.Cir.i.set(C.Cir.l.reg(r)), acc})
    case C.Cir.Stmt.store{+k, +c, +v}:
      +X = C.Cir.code.expr(v, Con{C.Wasm.Instr.store{U32.shln(U32.from_nat(k), 2n)}, acc})
      Equal.trans(Bool, I.fits(C.Cir.code.expr(c, C.Cir.code.at(X))), I.fits(X), I.fits(acc),
        fits.expr(c, C.Cir.code.at(X)), fits.expr(v, Con{C.Wasm.Instr.store{U32.shln(U32.from_nat(k), 2n)}, acc}))
    case C.Cir.Stmt.alloc{+r}:
      {==}
    case C.Cir.Stmt.emit{+v}:
      fits.expr(v, Con{C.Wasm.Instr.store8{0},
        Con{C.Cir.i.get(C.Cir.l.outn()), Con{C.Cir.i.const(1), Con{C.Cir.i.op(C.Wasm.Op.add{}),
          Con{C.Cir.i.set(C.Cir.l.outn()), acc}}}}})
    case C.Cir.Stmt.seq{+a, +b}:
      +X = C.Cir.code.stmt(b, d, acc)
      Equal.trans(Bool, I.fits(C.Cir.code.stmt(a, d, X)), I.fits(X), I.fits(acc), fits.stmt(a, d, X), fits.stmt(b, d, acc))
    case C.Cir.Stmt.if{+c, +t, +e}:
      +T = C.Cir.code.stmt(t, 2n+d, [C.Wasm.Instr.br{1}])
      +X = {Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{0}, T}} : List<&2, C.Wasm.Instr>}
      +E = C.Cir.code.stmt(e, 1n+d, [])
      +e1 = Equal.trans(Bool, I.fits(C.Cir.code.expr(c, X)), I.fits(T), True{}, fits.expr(c, X), fits.stmt(t, 2n+d, [C.Wasm.Instr.br{1}]))
      %Equal.sym(Bool, I.fits(C.Cir.code.expr(c, X)), True{}, e1) : {Bool.and(Bool.and(_, I.fits(E)), I.fits(acc)) == I.fits(acc) : Bool}
      %Equal.sym(Bool, I.fits(E), True{}, fits.stmt(e, 1n+d, [])) : {Bool.and(Bool.and(True{}, _), I.fits(acc)) == I.fits(acc) : Bool}
      {==}
    case C.Cir.Stmt.while{+c, +body}:
      +T = C.Cir.code.stmt(body, 2n+d, [C.Wasm.Instr.br{0}])
      +X = {Con{C.Wasm.Instr.eqz{}, Con{C.Wasm.Instr.br_if{1}, T}} : List<&2, C.Wasm.Instr>}
      +e1 = Equal.trans(Bool, I.fits(C.Cir.code.expr(c, X)), I.fits(T), True{}, fits.expr(c, X), fits.stmt(body, 2n+d, [C.Wasm.Instr.br{0}]))
      %Equal.sym(Bool, I.fits(C.Cir.code.expr(c, X)), True{}, e1) : {Bool.and(Bool.and(_, True{}), I.fits(acc)) == I.fits(acc) : Bool}
      {==}
    case C.Cir.Stmt.halt{+s}:
      %Equal.sym(Bool, I.fits(List.append(&2, C.Wasm.Instr, C.Cir.code.result(U32.is_zero(s)), [C.Wasm.Instr.br{U32.from_nat(1n+d)}])), True{},
        fits.result(U32.is_zero(s), U32.from_nat(1n+d))) : {Bool.and(_, I.fits(acc)) == I.fits(acc) : Bool}
      {==}

# The module
# ----------

def body(f: C.Wasm.Func) -> List<&2, C.Wasm.Instr>:
  match f:
    case C.Wasm.Func{_, _, _, b}:
      b

def fits.alloc(+k: U32) -> {I.fits(body(C.Cir.alloc(k))) == True{} : Bool}:
  {==}

def fits.run(+prog: C.Cir.Stmt, +regs: Nat, +k: U32) -> {I.fits(body(C.Cir.run(prog, regs, k))) == True{} : Bool}:
  %Equal.sym(Bool, I.fits(C.Cir.code.stmt(prog, 0n, [])), True{}, fits.stmt(prog, 0n, [])) : {Bool.and(_, True{}) == True{} : Bool}
  {==}

# the code of alloc, after its size
def XA(+k: U32) -> List<&2, U32>:
  Con{1, Con{3, Con{127, C.Wasm.encode.instrs(body(C.Cir.alloc(k)), [11])}}}

# the code of run, after its size
def XR(+prog: C.Cir.Stmt, +regs: Nat, +k: U32) -> List<&2, U32>:
  Con{1, List.append(&2, U32, List.append(&2, U32, C.Wasm.encode.uleb(U32.from_nat(6n+regs)), [127]),
    C.Wasm.encode.instrs(body(C.Cir.run(prog, regs, k)), [11]))}

def c10(+prog: C.Cir.Stmt, +regs: Nat, +k: U32) -> List<&2, U32>:
  Con{2, List.append(&2, U32, C.Wasm.encode.sized(XA(k)), List.append(&2, U32, C.Wasm.encode.sized(XR(prog, regs, k)), []))}

def c11(+cells: List<&2, C.Cir.Cell>) -> List<&2, U32>:
  Con{1, Con{0, Con{65, List.append(&2, U32, C.Wasm.encode.sleb(20), Con{11, C.Wasm.encode.sized(C.Cir.bytes(cells))})}}}

def c5(+k: U32) -> List<&2, U32>:
  Con{1, Con{0, C.Wasm.encode.uleb(C.Cir.pages(C.Cir.input.at(k)))}}

def fs(+prog: C.Cir.Stmt, +regs: Nat, +k: U32) -> List<&2, C.Wasm.Func>:
  [C.Cir.alloc(k), C.Cir.run(prog, regs, k)]

def es() -> List<&2, C.Wasm.Export>:
  [C.Wasm.Export.memory{C.Wasm.name.memory()}, C.Wasm.Export.func{C.Wasm.name.alloc(), 0}, C.Wasm.Export.func{C.Wasm.name.run(), 1}]

def c1(+prog: C.Cir.Stmt, +regs: Nat, +k: U32) -> List<&2, U32>:
  C.Wasm.encode.vec(2, C.Wasm.encode.functypes(fs(prog, regs, k)))

def c3(+prog: C.Cir.Stmt, +regs: Nat, +k: U32) -> List<&2, U32>:
  C.Wasm.encode.vec(2, C.Wasm.encode.indices(fs(prog, regs, k), 0))

def c7() -> List<&2, U32>:
  C.Wasm.encode.vec(3, C.Wasm.encode.exports(es()))

def enc(+prog: C.Cir.Stmt, +regs: Nat, +cells: List<&2, C.Cir.Cell>) ->
  {C.Wasm.encode(C.Cir.module(prog, regs, cells)) ==
    Con{0, Con{97, Con{115, Con{109, Con{1, Con{0, Con{0, Con{0,
      secs.bytes(c1(prog, regs, C.Wasm.encode.len(C.Cir.Cell, cells)), c3(prog, regs, C.Wasm.encode.len(C.Cir.Cell, cells)),
        c5(C.Wasm.encode.len(C.Cir.Cell, cells)), c7(), c10(prog, regs, C.Wasm.encode.len(C.Cir.Cell, cells)), c11(cells))}}}}}}}} : List<&2, U32>}:
  {==}

def round.of(+prog: C.Cir.Stmt, +regs: Nat, +cells: List<&2, C.Cir.Cell>,
  +h5: {I.fits.labels(c5(C.Wasm.encode.len(C.Cir.Cell, cells))) == True{} : Bool},
  +h10: {I.fits.labels(c10(prog, regs, C.Wasm.encode.len(C.Cir.Cell, cells))) == True{} : Bool},
  +h11: {I.fits.labels(c11(cells)) == True{} : Bool},
  +hA: {I.fits.labels(XA(C.Wasm.encode.len(C.Cir.Cell, cells))) == True{} : Bool},
  +hR: {I.fits.labels(XR(prog, regs, C.Wasm.encode.len(C.Cir.Cell, cells))) == True{} : Bool},
  +hB: {I.fits.labels(C.Cir.bytes(cells)) == True{} : Bool},
  +hN: {U32.is_le(U32.from_nat(6n+regs), 50000) == True{} : Bool},
  eN: {U32.to_nat(U32.from_nat(6n+regs)) == 6n+regs : Nat}
) -> {C.Wasm.decode.module(C.Wasm.encode(C.Cir.module(prog, regs, cells))) == Some{C.Cir.module(prog, regs, cells)} : Maybe<&2, C.Wasm.Module>}:
  +k = C.Wasm.encode.len(C.Cir.Cell, cells)
  +M = C.Cir.module(prog, regs, cells)
  +A = C.Cir.alloc(k)
  +R = C.Cir.run(prog, regs, k)
  +IA = C.Wasm.encode.instrs(body(A), [11])
  +IR = C.Wasm.encode.instrs(body(R), [11])
  +N = U32.from_nat(6n+regs)
  +CA = {C.Wasm.Code{3n, body(A)} : C.Wasm.Code}
  +CR = {C.Wasm.Code{6n+regs, body(R)} : C.Wasm.Code}
  +dA = func.three(IA, body(A), I.instrs.round(body(A), fits.alloc(k)))
  +dR = func.many(N, 6n+regs, IR, body(R), hN, eN, I.instrs.round(body(R), fits.run(prog, regs, k)))
  +p10 = part.code(1, {Con{3, Con{127, IA}} : List<&2, U32>}, XR(prog, regs, k), CA, CR, hA, hR, dA, dR)
  +p5 = part.mem(C.Cir.pages(C.Cir.input.at(k)))
  +p11 = part.data(C.Cir.bytes(cells), hB)
  +q1 = C.Wasm.decode.part(~C.Wasm.Type, ~C.Wasm.decode.functype, Some{c1(prog, regs, k)})
  +q3 = C.Wasm.decode.part(~U32, ~C.Wasm.decode.u32, Some{c3(prog, regs, k)})
  +q7 = C.Wasm.decode.part(~C.Wasm.Export, ~C.Wasm.decode.export, Some{c7()})
  +q5 = C.Wasm.decode.one(C.Wasm.Limits, C.Wasm.decode.part(~C.Wasm.Limits, ~C.Wasm.decode.limits, Some{c5(k)}))
  +q10 = C.Wasm.decode.part(~C.Wasm.Code, ~C.Wasm.decode.code, Some{c10(prog, regs, k)})
  +q11 = C.Wasm.decode.one(C.Wasm.Segment, C.Wasm.decode.part(~C.Wasm.Segment, ~C.Wasm.decode.data, Some{c11(cells)}))
  +m = mod.of(c1(prog, regs, k), c3(prog, regs, k), c5(k), c7(), c10(prog, regs, k), c11(cells), {==}, {==}, h5, {==}, h10, h11)
  +L5 = {Some{Some{C.Wasm.Limits{C.Cir.pages(C.Cir.input.at(k)), None{}}}} : Maybe<&2, Maybe<&2, C.Wasm.Limits>>}
  +L10 = {Some{[CA, CR]} : Maybe<&2, List<&2, C.Wasm.Code>>}
  +L11 = {Some{Some{C.Wasm.Segment{20, C.Cir.bytes(cells)}}} : Maybe<&2, Maybe<&2, C.Wasm.Segment>>}
  +rest = {(
    %Equal.sym(Maybe<&2, Maybe<&2, C.Wasm.Limits>>, q5, L5, p5) : {parts(q1, q3, _, q7, q10, q11) == Some{M} : Maybe<&2, C.Wasm.Module>}
    %Equal.sym(Maybe<&2, List<&2, C.Wasm.Code>>, q10, L10, p10) : {parts(q1, q3, L5, q7, _, q11) == Some{M} : Maybe<&2, C.Wasm.Module>}
    %Equal.sym(Maybe<&2, Maybe<&2, C.Wasm.Segment>>, q11, L11, p11) : {parts(q1, q3, L5, q7, L10, _) == Some{M} : Maybe<&2, C.Wasm.Module>}
    {==}) : {parts(q1, q3, q5, q7, q10, q11) == Some{M} : Maybe<&2, C.Wasm.Module>}}
  Equal.trans(Maybe<&2, C.Wasm.Module>, C.Wasm.decode.module(C.Wasm.encode(M)), parts(q1, q3, q5, q7, q10, q11), Some{M}, m, rest)

# Sizes
# -----

def ulen.if(c: Bool, +b: U32, +f: Nat, +r: U32, ih: N.Le(List.length(&2, U32, C.Wasm.encode.uleb.go(f, r)), f)) ->
  N.Le(List.length(&2, U32, C.Wasm.encode.leb.if(c, b, u => C.Wasm.encode.uleb.go(f, r))), 1n+f):
  match c:
    case True{}:
      N.le_zero(f)
    case False{}:
      ih

# the unsigned LEB128 bytes of k rounds are at most k
def ulen(+k: Nat, +v: U32) -> N.Le(List.length(&2, U32, C.Wasm.encode.uleb.go(k, v)), k):
  match k:
    case 0n:
      Unit{}
    case 1n+f:
      +r = U32.shrn(v, 7n)
      ulen.if(U32.is_zero(r), U32.and(v, 127), f, r, ulen(f, r))

# a < b as a <= b
def lt_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> N.Le(1n+a, b):
  match a b:
    case 0n 0n:
      L.ft(N.Le(1n, 0n), h)
    case 0n 1n+q:
      N.le_zero(q)
    case 1n+p 0n:
      L.ft(N.Le(2n+p, 0n), h)
    case 1n+p 1n+q:
      lt_le(p, q, h)

# a <= b gives 2^k a <= 2^k b
def D_mono(+k: Nat, +a: Nat, +b: Nat, h: N.Le(a, b)) -> N.Le(N.D(k, a), N.D(k, b)):
  match k:
    case 0n:
      h
    case 1n+q:
      N.double_mono(N.D(q, a), N.D(q, b), D_mono(q, a, b, h))

# 1 <= y gives 1 + y <= 2y
def lt_double(+y: Nat, h: N.Le(1n, y)) -> N.Le(1n+y, Nat.double(y)):
  match y:
    case 0n:
      Empty.absurd(N.Le(1n, 0n), h)
    case 1n+p:
      G.le_double(p)

# the bytes of the cells: at most 32 for each
def bytes.le(cs: List<&2, C.Cir.Cell>) -> N.Le(List.length(&2, U32, C.Cir.bytes(cs)), N.D(5n, List.length(&2, C.Cir.Cell, cs))):
  match cs:
    case Nil{}:
      Unit{}
    case Con{C.Cir.Cell{a, b, c, d, e}, +rest}:
      N.add_mono(20n, 32n, List.length(&2, U32, C.Cir.bytes(rest)), N.D(5n, List.length(&2, C.Cir.Cell, rest)), Unit{}, bytes.le(rest))

# the number of n, as a U32, is n, when n <= M
def tofrom(+n: Nat, +M: U32, +h: N.Le(n, U32.to_nat(M))) -> {U32.to_nat(U32.from_nat(n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      +x = U32.from_nat(p)
      +ih = tofrom(p, M, N.weaken(p, U32.to_nat(M), h))
      +h2 = N.le_rw_l(1n+p, 1n+U32.to_nat(x), U32.to_nat(M), Equal.cong(Nat, Nat, q => 1n+q, p, U32.to_nat(x), Equal.sym(Nat, U32.to_nat(x), p, ih)), h)
      +e = I.U32.inc_nat(x, Equal.sym(Bool, U32.is_zero(U32.inc(x)), False{}, nz(x, M, h2)))
      Equal.trans(Nat, U32.to_nat(U32.inc(x)), 1n+U32.to_nat(x), 1n+p, e, Equal.cong(Nat, Nat, q => 1n+q, U32.to_nat(x), p, ih))

# x <= y makes the comparison at most EQ
def le_true(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(x, y)) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(y, N.le_trans(1n+y, x, y, r, h)))

# X sits inside u, X, then Z
def le.mid(+u: List<&2, U32>, +X: List<&2, U32>, +Z: List<&2, U32>) ->
  N.Le(List.length(&2, U32, X), List.length(&2, U32, List.append(&2, U32, List.append(&2, U32, u, X), Z))):
  +lu = List.length(&2, U32, u)
  +lx = List.length(&2, U32, X)
  +ux = List.append(&2, U32, u, X)
  +lux = List.length(&2, U32, ux)
  N.le_trans(lx, lux, List.length(&2, U32, List.append(&2, U32, ux, Z)),
    N.le_rw_r(lx, Nat.add(lu, lx), lux, Equal.sym(Nat, lux, Nat.add(lu, lx), len.app(u, X)), N.le_add_l(lu, lx)),
    N.le_rw_r(lux, Nat.add(lux, List.length(&2, U32, Z)), List.length(&2, U32, List.append(&2, U32, ux, Z)),
      Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, ux, Z)), Nat.add(lux, List.length(&2, U32, Z)), len.app(ux, Z)),
      N.le_add_r(lux, List.length(&2, U32, Z))))

# X sits at the end of P, X
def le.tail(+P: List<&2, U32>, +X: List<&2, U32>) -> N.Le(List.length(&2, U32, X), List.length(&2, U32, List.append(&2, U32, P, X))):
  +lp = List.length(&2, U32, P)
  +lx = List.length(&2, U32, X)
  N.le_rw_r(lx, Nat.add(lp, lx), List.length(&2, U32, List.append(&2, U32, P, X)),
    Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, P, X)), Nat.add(lp, lx), len.app(P, X)), N.le_add_l(lp, lx))

def codes(+prog: C.Cir.Stmt, +regs: Nat, +k: U32) -> List<&2, U32>:
  C.Wasm.encode.codes([C.Cir.alloc(k), C.Cir.run(prog, regs, k)])

def fits.c10(+prog: C.Cir.Stmt, +regs: Nat, +k: U32, +M: U32, +h: N.Le(1n+List.length(&2, U32, codes(prog, regs, k)), U32.to_nat(M))) ->
  {I.fits.labels(c10(prog, regs, k)) == True{} : Bool}:
  fits.of_le(c10(prog, regs, k), M, h)

def fits.XA(+prog: C.Cir.Stmt, +regs: Nat, +k: U32, +M: U32, +h: N.Le(1n+List.length(&2, U32, codes(prog, regs, k)), U32.to_nat(M))) ->
  {I.fits.labels(XA(k)) == True{} : Bool}:
  +ZR = List.append(&2, U32, C.Wasm.encode.sized(XR(prog, regs, k)), [])
  +Y = List.append(&2, U32, C.Wasm.encode.sized(XA(k)), ZR)
  fits.of_le(XA(k), M, N.le_trans(List.length(&2, U32, XA(k)), List.length(&2, U32, Y), U32.to_nat(M),
    le.mid(C.Wasm.encode.uleb(C.Wasm.encode.len(U32, XA(k))), XA(k), ZR), N.weaken(List.length(&2, U32, Y), U32.to_nat(M), h)))

def fits.XR(+prog: C.Cir.Stmt, +regs: Nat, +k: U32, +M: U32, +h: N.Le(1n+List.length(&2, U32, codes(prog, regs, k)), U32.to_nat(M))) ->
  {I.fits.labels(XR(prog, regs, k)) == True{} : Bool}:
  +X = XR(prog, regs, k)
  +ZR = List.append(&2, U32, C.Wasm.encode.sized(X), [])
  +Y = List.append(&2, U32, C.Wasm.encode.sized(XA(k)), ZR)
  fits.of_le(X, M, N.le_trans(List.length(&2, U32, X), List.length(&2, U32, Y), U32.to_nat(M),
    N.le_trans(List.length(&2, U32, X), List.length(&2, U32, ZR), List.length(&2, U32, Y),
      le.mid(C.Wasm.encode.uleb(C.Wasm.encode.len(U32, X)), X, []), le.tail(C.Wasm.encode.sized(XA(k)), ZR)),
    N.weaken(List.length(&2, U32, Y), U32.to_nat(M), h)))

# the memory section's content: at most 7 bytes
def fits.c5(+k: U32) -> {I.fits.labels(c5(k)) == True{} : Bool}:
  +P = C.Cir.pages(C.Cir.input.at(k))
  +x = List.length(&2, U32, C.Wasm.encode.uleb(P))
  fits.of_le(c5(k), 255, N.le_trans(2n+x, 7n, U32.to_nat(255), ulen(5n, P), Unit{}))

# 4294967295 is the word of 32 set bits
def lit_MAX() -> {4294967295 == U32{N.ones(32n, 32n)} : U32}:
  {==}

# 1 + 4294967295 = 2^32
def val_MAX() -> {1n+U32.to_nat(4294967295) == N.D(32n, 1n) : Nat}:
  %Equal.sym(U32, 4294967295, U32{N.ones(32n, 32n)}, lit_MAX()) : {1n+U32.to_nat(_) == N.D(32n, 1n) : Nat}
  %Equal.sym(Nat, U32.to_nat(U32{N.ones(32n, 32n)}), Word.to_nat(32n, N.ones(32n, 32n)), N.u32_to_nat(N.ones(32n, 32n))) : {1n+_ == N.D(32n, 1n) : Nat}
  N.ones_val(32n, 32n, Unit{})

def step32(+a: Nat, +b: Nat, h: N.Le(a, 5n+b)) -> N.Le(5n+a, 32n+b):
  N.le_trans(a, 5n+b, 27n+b, h, N.le_add_l(22n, b))

# y <= M, when 1 + M = 2y and 1 <= y
def le.half(+y: Nat, +m: Nat, vm: {1n+m == Nat.double(y) : Nat}, hy: N.Le(1n, y)) -> N.Le(y, m):
  N.le_rw_r(1n+y, Nat.double(y), 1n+m, Equal.sym(Nat, 1n+m, Nat.double(y), vm), lt_double(y, hy))

# 2^q <= M, when 1 + M = 2^(1 + q)
def le.pow(+q: Nat, +m: Nat, vm: {1n+m == N.D(1n+q, 1n) : Nat}) -> N.Le(N.D(q, 1n), m):
  le.half(N.D(q, 1n), m, vm, G.D_ge(q, 1n))

# the data section's content, of fewer than h26 cells (to_nat(K) = h26), has
# at most y31 = 2^5 h26 <= M bytes
def le.c11(+cells: List<&2, C.Cir.Cell>, +K: U32, +M: U32, +h26: Nat, +y31: Nat,
  vK: {U32.to_nat(K) == h26 : Nat}, e31: {N.D(5n, h26) == y31 : Nat}, l31: N.Le(y31, U32.to_nat(M)),
  hL: N.Le(1n+List.length(&2, C.Cir.Cell, cells), U32.to_nat(K))) -> N.Le(List.length(&2, U32, c11(cells)), U32.to_nat(M)):
  +B = C.Cir.bytes(cells)
  +l = List.length(&2, C.Cir.Cell, cells)
  +u = C.Wasm.encode.uleb(C.Wasm.encode.len(U32, B))
  +x = List.length(&2, U32, u)
  +y = List.length(&2, U32, B)
  +d5 = N.D(5n, l)
  +a = List.length(&2, U32, List.append(&2, U32, u, B))
  +s3 = N.add_mono(x, 5n, y, d5, ulen(5n, C.Wasm.encode.len(U32, B)), bytes.le(cells))
  +s4 = N.le_rw_l(Nat.add(x, y), a, Nat.add(5n, d5), Equal.sym(Nat, a, Nat.add(x, y), len.app(u, B)), s3)
  +s45 = {step32(a, d5, s4) : N.Le(5n+a, N.D(5n, 1n+l))}
  +s5 = D_mono(5n, 1n+l, h26, N.le_rw_r(1n+l, U32.to_nat(K), h26, vK, hL))
  +s6 = N.le_rw_r(5n+a, N.D(5n, h26), y31, e31, N.le_trans(5n+a, N.D(5n, 1n+l), N.D(5n, h26), s45, s5))
  N.le_trans(5n+a, y31, U32.to_nat(M), s6, l31)

def fits.B(+cells: List<&2, C.Cir.Cell>, +M: U32, +h: N.Le(List.length(&2, U32, c11(cells)), U32.to_nat(M))) ->
  {I.fits.labels(C.Cir.bytes(cells)) == True{} : Bool}:
  +B = C.Cir.bytes(cells)
  +u = C.Wasm.encode.uleb(C.Wasm.encode.len(U32, B))
  +a = List.length(&2, U32, List.append(&2, U32, u, B))
  fits.of_le(B, M, N.le_trans(List.length(&2, U32, B), a, U32.to_nat(M), le.tail(u, B),
    N.le_trans(a, 5n+a, U32.to_nat(M), N.le_add_l(5n, a), h)))

# the round trip, with the limits as variables: K = 2^26 cells, M = 2^32 - 1
# bytes, W = 50000 locals
def round.sized(+prog: C.Cir.Stmt, +regs: Nat, +cells: List<&2, C.Cir.Cell>, +K: U32, +M: U32, +W: U32,
  vK: {U32.to_nat(K) == N.D(26n, 1n) : Nat}, vM: {1n+U32.to_nat(M) == N.D(32n, 1n) : Nat}, eW: {W == 50000 : U32},
  hc: N.Le(1n+List.length(&2, C.Cir.Cell, cells), U32.to_nat(K)),
  +hr: N.Le(6n+regs, U32.to_nat(W)),
  +hs: N.Le(1n+List.length(&2, U32, C.Wasm.encode.codes([C.Cir.alloc(C.Wasm.encode.len(C.Cir.Cell, cells)),
    C.Cir.run(prog, regs, C.Wasm.encode.len(C.Cir.Cell, cells))])), U32.to_nat(M))
) -> {C.Wasm.decode.module(C.Wasm.encode(C.Cir.module(prog, regs, cells))) == Some{C.Cir.module(prog, regs, cells)} : Maybe<&2, C.Wasm.Module>}:
  +k = C.Wasm.encode.len(C.Cir.Cell, cells)
  +N = U32.from_nat(6n+regs)
  +l31 = le.pow(31n, U32.to_nat(M), vM)
  +h11 = le.c11(cells, K, M, N.D(26n, 1n), N.D(31n, 1n), vK, N.D_add(5n, 26n, 31n, 1n, {==}), l31, hc)
  +eN = tofrom(6n+regs, W, hr)
  +hNW = le_true(U32.cmp(N, W), U32.to_nat(N), U32.to_nat(W), N.U32.rel(N, W),
    N.le_rw_l(6n+regs, U32.to_nat(N), U32.to_nat(W), Equal.sym(Nat, U32.to_nat(N), 6n+regs, eN), hr))
  +hN = {(%eW : {U32.is_le(N, _) == True{} : Bool}; hNW) : {U32.is_le(N, 50000) == True{} : Bool}}
  round.of(prog, regs, cells, fits.c5(k), fits.c10(prog, regs, k, M, hs), fits.of_le(c11(cells), M, h11),
    fits.XA(prog, regs, k, M, hs), fits.XR(prog, regs, k, M, hs), fits.B(cells, M, h11), hN, eN)

# The round trip
# --------------
#
# Wasm.decode.module reads back the module of Cir.module that Wasm.encode
# writes, when it has fewer than 2^26 cells, at most 50000 locals in run, and
# a code section of fewer than 2^32 - 1 bytes. The program needs no premise:
# Cir.code.stmt emits no br_table (fits.stmt).
def module.round(+prog: C.Cir.Stmt, +regs: Nat, +cells: List<&2, C.Cir.Cell>,
  hc: {Nat.is_lt(List.length(&2, C.Cir.Cell, cells), U32.to_nat(67108864)) == True{} : Bool},
  +hr: {Nat.is_le(6n+regs, U32.to_nat(50000)) == True{} : Bool},
  hs: {Nat.is_lt(List.length(&2, U32, C.Wasm.encode.codes([C.Cir.alloc(C.Wasm.encode.len(C.Cir.Cell, cells)),
    C.Cir.run(prog, regs, C.Wasm.encode.len(C.Cir.Cell, cells))])), U32.to_nat(4294967295)) == True{} : Bool}
) -> {C.Wasm.decode.module(C.Wasm.encode(C.Cir.module(prog, regs, cells))) == Some{C.Cir.module(prog, regs, cells)} : Maybe<&2, C.Wasm.Module>}:
  round.sized(prog, regs, cells, 67108864, 4294967295, 50000, G.val_M2(), val_MAX(), {==},
    lt_le(List.length(&2, C.Cir.Cell, cells), U32.to_nat(67108864), hc),
    N.toLe(6n+regs, U32.to_nat(50000), hr),
    lt_le(List.length(&2, U32, C.Wasm.encode.codes([C.Cir.alloc(C.Wasm.encode.len(C.Cir.Cell, cells)), C.Cir.run(prog, regs, C.Wasm.encode.len(C.Cir.Cell, cells))])), U32.to_nat(4294967295), hs))
