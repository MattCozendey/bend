# compiler: the proofs of halt.no_result and halt.oom
# ===================================================
#
# Compiler.halt(s) is a small module: alloc, then run, whose first loop
# counts next from 1 until 20 × next >= a + n, then sets the status to s.
#
# Decoding (H.decoded): for any s, the bytes of s are those of
# Wasm.encode.sleb(s), at most 5 (H.len_go); the decoder reads the module's
# sections up to run's code (H.E1, by cases on those few bytes), and reads the
# i32.const of s with the round trip of proof_leb.bend (H.go_const); so the
# module decodes to H.mod(s, False), when s is not 0.
#
# halt.no_result: every run of run gives [s], traps or runs out of fuel
# (H.loop, by induction on a bound of the fuel; H.ext steps a call), so the
# host never reads a result.
#
# halt.oom: with the fuel 64 + 10 + 16 × (n + 1) + 18, alloc gives -1 or the
# input's address 20 with room for it (H.A.al1 to H.A.al4, by the cases of
# its branches), and the first loop ends (H.loopO): a round that goes on has
# 20 × next < a + n <= 2^32 - 16 = 20 × 214748364, so next < 214748364 and
# 20 × (next + 1) is exact. The arithmetic of words is over n bits, so that
# no proof computes 2^32.

import Base
import ./impl.bend as C
import ./proof_leb.bend as L
import ./proof_need.bend as PN

# The module
# ----------

# run's body before the halt's code: the start and the first loop
def H.pre() -> List<&2, C.Wasm.Instr>:
  [C.Cir.i.const(2), C.Cir.i.set(C.Cir.l.status()),
    C.Cir.i.get(0), C.Cir.i.get(1), C.Cir.i.op(C.Wasm.Op.add{}), C.Cir.i.set(C.Cir.l.addr()),
    C.Cir.i.const(U32.inc(0)), C.Cir.i.set(C.Cir.l.next()),
    C.Wasm.Instr.block{[C.Wasm.Instr.loop{Con{C.Cir.i.get(C.Cir.l.next()), C.Cir.code.at(
      [C.Cir.i.get(C.Cir.l.addr()), C.Cir.i.op(C.Wasm.Op.ge_u{}), C.Wasm.Instr.br_if{1},
       C.Cir.i.get(C.Cir.l.next()), C.Cir.i.const(1), C.Cir.i.op(C.Wasm.Op.add{}), C.Cir.i.set(C.Cir.l.next()),
       C.Wasm.Instr.br{0}])}}]}]

# run's body, with the halt's result code chosen by z (U32.is_zero(s))
def H.body(+s: U32, z: Bool) -> List<&2, C.Wasm.Instr>:
  List.append(&2, C.Wasm.Instr, H.pre(), [
    C.Wasm.Instr.block{[C.Wasm.Instr.block{Con{C.Cir.i.const(s), Con{C.Cir.i.set(C.Cir.l.status()),
      List.append(&2, C.Wasm.Instr, C.Cir.code.result(z), [C.Wasm.Instr.br{U32.from_nat(1n)}])}}}]},
    C.Cir.i.get(C.Cir.l.status())])

def H.mod(+s: U32, z: Bool) -> C.Wasm.Module:
  C.Wasm.Module{
    [C.Cir.alloc(0), C.Wasm.Func{2n, 1n, 6n, H.body(s, z)}],
    Some{C.Wasm.Limits{C.Cir.pages(C.Cir.input.at(0)), None{}}},
    [C.Wasm.Export.memory{C.Wasm.name.memory()}, C.Wasm.Export.func{C.Wasm.name.alloc(), 0},
     C.Wasm.Export.func{C.Wasm.name.run(), 1}],
    Some{C.Wasm.Segment{20, []}}}

# the bytes of run's body after those of s
def H.R() -> List<&2, U32>:
  C.Wasm.encode.instrs([C.Cir.i.set(C.Cir.l.status()), C.Wasm.Instr.br{1}],
    Con{11, Con{11, C.Wasm.encode.instrs([C.Cir.i.get(C.Cir.l.status())], [11])}})

# the bytes of run's body, with cs for the bytes of s
def H.BB(cs: List<&2, U32>) -> List<&2, U32>:
  C.Wasm.encode.instrs(H.pre(), Con{2, Con{64, Con{2, Con{64, Con{65, List.append(&2, U32, cs, H.R())}}}}})

# the bytes of run's code: its locals, then its body
def H.RUNC(cs: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, C.Wasm.encode.locals(6n), H.BB(cs))

# the bytes of H.mod(s, False), with cs for the bytes of s
def H.bytes(cs: List<&2, U32>) -> List<&2, U32>:
  +fs = {[C.Cir.alloc(0), C.Wasm.Func{2n, 1n, 6n, []}] : List<&2, C.Wasm.Func>}
  +es = {[C.Wasm.Export.memory{C.Wasm.name.memory()}, C.Wasm.Export.func{C.Wasm.name.alloc(), 0},
     C.Wasm.Export.func{C.Wasm.name.run(), 1}] : List<&2, C.Wasm.Export>}
  Con{0, Con{97, Con{115, Con{109, Con{1, Con{0, Con{0, Con{0,
    C.Wasm.encode.section(1, C.Wasm.encode.vec(2, C.Wasm.encode.functypes(fs)),
      C.Wasm.encode.section(3, C.Wasm.encode.vec(2, C.Wasm.encode.indices(fs, 0)),
        C.Wasm.encode.memory(Some{C.Wasm.Limits{C.Cir.pages(C.Cir.input.at(0)), None{}}},
          C.Wasm.encode.section(7, C.Wasm.encode.vec(C.Wasm.encode.len(C.Wasm.Export, es), C.Wasm.encode.exports(es)),
            C.Wasm.encode.section(10, C.Wasm.encode.vec(2, List.append(&2, U32, C.Wasm.encode.code(C.Cir.alloc(0)),
              List.append(&2, U32, C.Wasm.encode.sized(H.RUNC(cs)), []))),
              C.Wasm.encode.data(Some{C.Wasm.Segment{20, []}}))))))}}}}}}}}

# Decoding
# --------

def H.code_of(f: C.Wasm.Func) -> C.Wasm.Code:
  match f:
    case C.Wasm.Func{_, _, n, b}:
      C.Wasm.Code{n, b}

# the module's parts, from the codes x
def H.parts(x: Maybe<&2, List<&2, C.Wasm.Code>>) -> Maybe<&2, C.Wasm.Module>:
  Maybe.bind(&2, List<&2, C.Wasm.Code>, C.Wasm.Module, x, cs =>
    Maybe.bind(&2, List<&2, C.Wasm.Func>, C.Wasm.Module,
      C.Wasm.funcs.of([C.Wasm.Type{1n, 1n}, C.Wasm.Type{2n, 1n}], [0, 1], cs), fs =>
      Some{C.Wasm.Module{fs, Some{C.Wasm.Limits{1, None{}}},
        [C.Wasm.Export.memory{C.Wasm.name.memory()}, C.Wasm.Export.func{C.Wasm.name.alloc(), 0},
         C.Wasm.Export.func{C.Wasm.name.run(), 1}],
        Some{C.Wasm.Segment{20, []}}}}))

# the module, from x, what run's code decodes to
def H.Q(x: Maybe<&2, C.Wasm.Decoded<C.Wasm.Code>>) -> Maybe<&2, C.Wasm.Module>:
  H.parts(C.Wasm.decode.done(List<&2, C.Wasm.Code>, C.Wasm.decode.cons(C.Wasm.Code, H.code_of(C.Cir.alloc(0)),
    C.Wasm.decode.bind(C.Wasm.Code, List<&2, C.Wasm.Code>, C.Wasm.decode.whole(C.Wasm.Code, x, []), y => r =>
      C.Wasm.decode.cons(C.Wasm.Code, y, C.Wasm.decode.items(~C.Wasm.Code, ~C.Wasm.decode.code, 0n, r))))))

# with at most 5 bytes for s, the module decodes up to run's code
def H.E1(cs: List<&2, U32>, ok: {Nat.is_le(List.length(&2, U32, cs), 5n) == True{} : Bool}) ->
  {C.Wasm.decode.module(H.bytes(cs)) == H.Q(C.Wasm.decode.func(H.RUNC(cs))) : Maybe<&2, C.Wasm.Module>}:
  match cs:
    case Nil{}:
      {==}
    case Con{+a, Nil{}}:
      {==}
    case Con{+a, Con{+b, Nil{}}}:
      {==}
    case Con{+a, Con{+b, Con{+c, Nil{}}}}:
      {==}
    case Con{+a, Con{+b, Con{+c, Con{+d, Nil{}}}}}:
      {==}
    case Con{+a, Con{+b, Con{+c, Con{+d, Con{+e, Nil{}}}}}}:
      {==}
    case Con{_, Con{_, Con{_, Con{_, Con{_, Con{_, _}}}}}}:
      L.ft({C.Wasm.decode.module(H.bytes(cs)) == H.Q(C.Wasm.decode.func(H.RUNC(cs))) : Maybe<&2, C.Wasm.Module>}, ok)

def H.E3(+s: U32) -> {H.Q(Some{C.Wasm.Decoded{C.Wasm.Code{6n, H.body(s, False{})}, []}}) == Some{H.mod(s, False{})} : Maybe<&2, C.Wasm.Module>}:
  {==}

# the open blocks at the halt's i32.const
def H.ST() -> List<&2, C.Wasm.Open>:
  [C.Wasm.Open{False{}, []}, C.Wasm.Open{False{}, List.reverse(&2, C.Wasm.Instr, H.pre())}]

def H.c3a(cs: List<&2, U32>) ->
  {C.Wasm.decode.instrs(1n+List.length(&2, U32, H.BB(cs)), H.BB(cs)) ==
    C.Wasm.decode.instrs.go(24n+List.length(&2, U32, List.append(&2, U32, cs, H.R())),
      Con{65, List.append(&2, U32, cs, H.R())}, [], H.ST()) : Maybe<&2, C.Wasm.Decoded<List<&2, C.Wasm.Instr>>>}:
  {==}

def H.c3c(+s: U32, -cs: List<&2, U32>) ->
  {C.Wasm.decode.instrs.go(23n+List.length(&2, U32, List.append(&2, U32, cs, H.R())), H.R(), [C.Wasm.Instr.const{s}], H.ST()) ==
    Some{C.Wasm.Decoded{H.body(s, False{}), []}} : Maybe<&2, C.Wasm.Decoded<List<&2, C.Wasm.Instr>>>}:
  {==}

# the head of an i32.const whose bytes decode to s
def H.tok(+s: U32, +bs: List<&2, U32>, +R: List<&2, U32>,
  h: {C.Wasm.decode.sleb(32n, bs) == Some{C.Wasm.Decoded{s, R}} : Maybe<&2, C.Wasm.Decoded<U32>>}) ->
  {C.Wasm.decode.token(65n, bs) == Some{C.Wasm.Decoded{C.Wasm.Token.instr{C.Wasm.Instr.const{s}}, R}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Token>>}:
  %Equal.sym(Maybe<&2, C.Wasm.Decoded<U32>>, C.Wasm.decode.sleb(32n, bs), Some{C.Wasm.Decoded{s, R}}, h) :
    {C.Wasm.decode.bind(U32, C.Wasm.Token, _, m => r => C.Wasm.decode.as(C.Wasm.Instr.const{m}, r)) ==
      Some{C.Wasm.Decoded{C.Wasm.Token.instr{C.Wasm.Instr.const{s}}, R}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Token>>}
  {==}

# the decoder reads such an i32.const in one step
def H.go_const(+p: Nat, +s: U32, +bs: List<&2, U32>, +R: List<&2, U32>, +xs: List<&2, C.Wasm.Instr>, +st: List<&2, C.Wasm.Open>,
  h: {C.Wasm.decode.sleb(32n, bs) == Some{C.Wasm.Decoded{s, R}} : Maybe<&2, C.Wasm.Decoded<U32>>}) ->
  {C.Wasm.decode.instrs.go(1n+p, Con{65, bs}, xs, st) == C.Wasm.decode.instrs.go(p, R, Con{C.Wasm.Instr.const{s}, xs}, st) : Maybe<&2, C.Wasm.Decoded<List<&2, C.Wasm.Instr>>>}:
  %Equal.sym(Maybe<&2, C.Wasm.Decoded<C.Wasm.Token>>, C.Wasm.decode.token(65n, bs),
    Some{C.Wasm.Decoded{C.Wasm.Token.instr{C.Wasm.Instr.const{s}}, R}}, H.tok(s, bs, R, h)) :
    {C.Wasm.decode.instrs.then(_, xs, st, r => ys => st2 => C.Wasm.decode.instrs.go(p, r, ys, st2)) ==
      C.Wasm.decode.instrs.go(p, R, Con{C.Wasm.Instr.const{s}, xs}, st) : Maybe<&2, C.Wasm.Decoded<List<&2, C.Wasm.Instr>>>}
  {==}

# run's body decodes, when the bytes cs decode to s
def H.c3(+s: U32, +cs: List<&2, U32>,
  h: {C.Wasm.decode.sleb(32n, List.append(&2, U32, cs, H.R())) == Some{C.Wasm.Decoded{s, H.R()}} : Maybe<&2, C.Wasm.Decoded<U32>>}) ->
  {C.Wasm.decode.instrs(1n+List.length(&2, U32, H.BB(cs)), H.BB(cs)) ==
    Some{C.Wasm.Decoded{H.body(s, False{}), []}} : Maybe<&2, C.Wasm.Decoded<List<&2, C.Wasm.Instr>>>}:
  +bs = List.append(&2, U32, cs, H.R())
  +p = {23n+List.length(&2, U32, bs) : Nat}
  Equal.trans(Maybe<&2, C.Wasm.Decoded<List<&2, C.Wasm.Instr>>>,
    C.Wasm.decode.instrs(1n+List.length(&2, U32, H.BB(cs)), H.BB(cs)),
    C.Wasm.decode.instrs.go(p, H.R(), [C.Wasm.Instr.const{s}], H.ST()),
    Some{C.Wasm.Decoded{H.body(s, False{}), []}},
    Equal.trans(Maybe<&2, C.Wasm.Decoded<List<&2, C.Wasm.Instr>>>,
      C.Wasm.decode.instrs(1n+List.length(&2, U32, H.BB(cs)), H.BB(cs)),
      C.Wasm.decode.instrs.go(1n+p, Con{65, bs}, [], H.ST()),
      C.Wasm.decode.instrs.go(p, H.R(), [C.Wasm.Instr.const{s}], H.ST()),
      H.c3a(cs), H.go_const(p, s, bs, H.R(), [], H.ST(), h)),
    H.c3c(s, cs))

# a function's code of 6 locals, whose body decodes to b
def H.f1(+bs: List<&2, U32>, -b: List<&2, C.Wasm.Instr>,
  h: {C.Wasm.decode.instrs(1n+List.length(&2, U32, bs), bs) == Some{C.Wasm.Decoded{b, []}} : Maybe<&2, C.Wasm.Decoded<List<&2, C.Wasm.Instr>>>}) ->
  {C.Wasm.decode.func(Con{1, Con{6, Con{127, bs}}}) == Some{C.Wasm.Decoded{C.Wasm.Code{6n, b}, []}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Code>>}:
  %Equal.sym(Maybe<&2, C.Wasm.Decoded<List<&2, C.Wasm.Instr>>>, C.Wasm.decode.instrs(1n+List.length(&2, U32, bs), bs),
    Some{C.Wasm.Decoded{b, []}}, h) :
    {C.Wasm.decode.bind(List<&2, C.Wasm.Instr>, C.Wasm.Code, _, x => r => Some{C.Wasm.Decoded{C.Wasm.Code{U32.to_nat(6), x}, r}}) ==
      Some{C.Wasm.Decoded{C.Wasm.Code{6n, b}, []}} : Maybe<&2, C.Wasm.Decoded<C.Wasm.Code>>}
  {==}

def H.le0(p: Nat) -> {Nat.is_le(0n, p) == True{} : Bool}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      {==}

def H.len_if(c: Bool, +b: U32, +p: Nat, +r: U32,
  ih: {Nat.is_le(List.length(&2, U32, C.Wasm.encode.sleb.go(p, r)), p) == True{} : Bool}) ->
  {Nat.is_le(List.length(&2, U32, C.Wasm.encode.leb.if(c, b, u => C.Wasm.encode.sleb.go(p, r))), 1n+p) == True{} : Bool}:
  match c:
    case True{}:
      H.le0(p)
    case False{}:
      ih

# the signed LEB128 bytes of k rounds are at most k
def H.len_go(+k: Nat, +v: U32) -> {Nat.is_le(List.length(&2, U32, C.Wasm.encode.sleb.go(k, v)), k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      +b = U32.and(v, 127)
      +r = L.sleb.next(v)
      +low = U32.is_zero(U32.and(b, 64))
      H.len_if((U32.is_zero(r) && low) || (U32.is_eq(r, 4294967295) && Bool.not(low)), b, p, r, H.len_go(p, r))

# the module that halts with s decodes, when s is not 0
def H.decoded(+s: U32, ez: {U32.is_zero(s) == False{} : Bool}) ->
  {C.Wasm.decode.module(C.Compiler.halt(s)) == Some{H.mod(s, False{})} : Maybe<&2, C.Wasm.Module>}:
  %Equal.sym(Bool, U32.is_zero(s), False{}, ez) :
    {C.Wasm.decode.module(C.Wasm.encode(H.mod(s, _))) == Some{H.mod(s, False{})} : Maybe<&2, C.Wasm.Module>}
  +cs = C.Wasm.encode.sleb(s)
  +f1 = H.f1(H.BB(cs), H.body(s, False{}), H.c3(s, cs, L.sleb.round(s, H.R())))
  Equal.trans(Maybe<&2, C.Wasm.Module>, C.Wasm.decode.module(H.bytes(cs)),
    H.Q(Some{C.Wasm.Decoded{C.Wasm.Code{6n, H.body(s, False{})}, []}}),
    Some{H.mod(s, False{})},
    Equal.trans(Maybe<&2, C.Wasm.Module>, C.Wasm.decode.module(H.bytes(cs)),
      H.Q(C.Wasm.decode.func(H.RUNC(cs))),
      H.Q(Some{C.Wasm.Decoded{C.Wasm.Code{6n, H.body(s, False{})}, []}}),
      H.E1(cs, H.len_go(5n, s)),
      Equal.cong(Maybe<&2, C.Wasm.Decoded<C.Wasm.Code>>, Maybe<&2, C.Wasm.Module>, x => H.Q(x),
        C.Wasm.decode.func(H.RUNC(cs)), Some{C.Wasm.Decoded{C.Wasm.Code{6n, H.body(s, False{})}, []}}, f1)),
    H.E3(s))

# Running
# -------

# a call that gives the results [s], traps or runs out of fuel
def H.Good(s: U32, c: C.Wasm.Call) -> Type:
  match c:
    case C.Wasm.Call.done{rs, _, _}:
      {rs == [s] : List<&2, U32>}
    case C.Wasm.Call.trap{_}:
      Unit
    case C.Wasm.Call.not_done{}:
      Unit

def H.Good.plus(-s: U32, c: C.Wasm.Call, g: H.Good(s, c)) -> H.Good(s, C.Wasm.call.plus(c)):
  match c:
    case C.Wasm.Call.done{rs, m, n}:
      g
    case C.Wasm.Call.trap{m}:
      g
    case C.Wasm.Call.not_done{}:
      g

# the result of n more steps, until the function ends or traps
def H.steps(n: Nat, st: C.Wasm.Step) -> C.Wasm.Step:
  match n:
    case 0n:
      st
    case 1n+p:
      match st:
        case C.Wasm.Step.next{fr, m}:
          H.steps(p, C.Wasm.step(fr, m))
        case C.Wasm.Step.done{rs, m}:
          C.Wasm.Step.done{rs, m}
        case C.Wasm.Step.trap{m}:
          C.Wasm.Step.trap{m}

# what Good asks of the run that goes on from st with the fuel F
def H.G(s: U32, F: Nat, st: C.Wasm.Step) -> Type:
  match st:
    case C.Wasm.Step.next{fr, m}:
      H.Good(s, C.Wasm.call.go(F, fr, m))
    case C.Wasm.Step.done{rs, _}:
      {rs == [s] : List<&2, U32>}
    case C.Wasm.Step.trap{_}:
      Unit

def H.G.stepped(-s: U32, F: Nat, st: C.Wasm.Step, h: H.G(s, F, st)) ->
  H.Good(s, C.Wasm.call.stepped(st, g => m => C.Wasm.call.go(F, g, m))):
  match st:
    case C.Wasm.Step.next{fr, m}:
      H.Good.plus(s, C.Wasm.call.go(F, fr, m), h)
    case C.Wasm.Step.done{rs, m}:
      h
    case C.Wasm.Step.trap{m}:
      h

# a run is good when it is good after n steps, with the fuel left
def H.ext(n: Nat, +st: C.Wasm.Step, +F: Nat, -s: U32, g: H.G(s, Nat.sub(F, n), H.steps(n, st))) -> H.G(s, F, st):
  match n:
    case 0n:
      match F:
        case 0n:
          g
        case 1n+q:
          g
    case 1n+p:
      match st:
        case C.Wasm.Step.next{fr, m}:
          match F:
            case 0n:
              Unit{}
            case 1n+F1:
              H.G.stepped(s, F1, C.Wasm.step(fr, m), H.ext(p, C.Wasm.step(fr, m), F1, s, g))
        case C.Wasm.Step.done{rs, m}:
          g
        case C.Wasm.Step.trap{m}:
          g

# The function run
# ----------------

# the first loop's body
def H.LB() -> List<&2, C.Wasm.Instr>:
  Con{C.Cir.i.get(C.Cir.l.next()), C.Cir.code.at(
    [C.Cir.i.get(C.Cir.l.addr()), C.Cir.i.op(C.Wasm.Op.ge_u{}), C.Wasm.Instr.br_if{1},
     C.Cir.i.get(C.Cir.l.next()), C.Cir.i.const(1), C.Cir.i.op(C.Wasm.Op.add{}), C.Cir.i.set(C.Cir.l.next()),
     C.Wasm.Instr.br{0}])}

# run's body after the first loop
def H.AFTER(+s: U32) -> List<&2, C.Wasm.Instr>:
  [C.Wasm.Instr.block{[C.Wasm.Instr.block{[C.Wasm.Instr.const{s}, C.Wasm.Instr.local_set{2}, C.Wasm.Instr.br{1}]}]},
   C.Wasm.Instr.local_get{2}]

# the labels inside the first loop
def H.LL(+s: U32) -> List<&2, C.Wasm.Label>:
  [C.Wasm.Label{Some{H.LB()}, [], 0n}, C.Wasm.Label{None{}, H.AFTER(s), 0n}]

def H.locals(+a: U32, +k: U32, +nx: U32, +tmp: U32) -> List<&2, U32>:
  [a, k, 2, nx, 0, tmp, 0, U32.add(a, k)]

# the first loop, at the start of a round
def H.loopfr(+s: U32, +a: U32, +k: U32, +nx: U32, +tmp: U32) -> C.Wasm.Frame:
  C.Wasm.Frame{H.LB(), H.LL(s), 1n, [], H.locals(a, k, nx, tmp)}

# the loop's condition: 20 × next >= a + n
def H.C(+a: U32, +k: U32, +nx: U32) -> Bool:
  U32.is_ge(U32.add(U32.shln(nx, U32.to_nat(U32.and(4, 31))), U32.shln(nx, U32.to_nat(U32.and(2, 31)))), U32.add(a, k))

# the first loop, at its br_if, with the condition c
def H.brfr(+s: U32, +a: U32, +k: U32, +nx: U32, c: Bool) -> C.Wasm.Frame:
  C.Wasm.Frame{[C.Wasm.Instr.br_if{1}, C.Wasm.Instr.local_get{3}, C.Wasm.Instr.const{1}, C.Wasm.Instr.op{C.Wasm.Op.add{}},
    C.Wasm.Instr.local_set{3}, C.Wasm.Instr.br{0}], H.LL(s), 1n, [Bool.to_u32(c)], H.locals(a, k, nx, nx)}

# after the first loop
def H.exfr(+s: U32, +a: U32, +k: U32, +nx: U32) -> C.Wasm.Frame:
  C.Wasm.Frame{H.AFTER(s), [], 1n, [], H.locals(a, k, nx, nx)}

def H.exit(+F: Nat, +s: U32, +a: U32, +k: U32, +nx: U32, +mem: C.Wasm.Memory) ->
  H.Good(s, C.Wasm.call.go(F, H.exfr(s, a, k, nx), mem)):
  H.ext(7n, C.Wasm.Step.next{H.exfr(s, a, k, nx), mem}, F, s, {==})

def H.brfix(+F: Nat, +s: U32, +a: U32, +k: U32, +nx: U32, +mem: C.Wasm.Memory, -c: Bool, -B: Bool, e: {c == B : Bool},
  g: H.Good(s, C.Wasm.call.go(F, H.brfr(s, a, k, nx, B), mem))) -> H.Good(s, C.Wasm.call.go(F, H.brfr(s, a, k, nx, c), mem)):
  %Equal.sym(Bool, c, B, e) : H.Good(s, C.Wasm.call.go(F, H.brfr(s, a, k, nx, _), mem))
  g

# Order of Nat
def H.le_weak(a: Nat, +r: Nat, h: {Nat.is_le(1n+a, r) == True{} : Bool}) -> {Nat.is_le(a, r) == True{} : Bool}:
  match a:
    case 0n:
      H.le0(r)
    case 1n+a1:
      match r:
        case 0n:
          L.ft({Nat.is_le(1n+a1, 0n) == True{} : Bool}, h)
        case 1n+r1:
          H.le_weak(a1, r1, h)

def H.le_sub(+a: Nat, +r: Nat, k: Nat, h: {Nat.is_le(a, r) == True{} : Bool}) -> {Nat.is_le(Nat.sub(a, k), r) == True{} : Bool}:
  match a:
    case 0n:
      H.le0(r)
    case 1n+a1:
      match k:
        case 0n:
          h
        case 1n+k1:
          H.le_sub(a1, r, k1, H.le_weak(a1, r, h))

def H.le_sub1(F: Nat, +r: Nat, k: Nat, h: {Nat.is_le(F, 1n+r) == True{} : Bool}) -> {Nat.is_le(Nat.sub(F, 1n+k), r) == True{} : Bool}:
  match F:
    case 0n:
      H.le0(r)
    case 1n+F1:
      H.le_sub(F1, r, k, h)

def H.le_refl(a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      H.le_refl(p)

# the first loop gives [s], traps or runs out of fuel, for any fuel F <= r
def H.loop(+r: Nat, +F: Nat, +s: U32, +a: U32, +k: U32, +nx: U32, +tmp: U32, +mem: C.Wasm.Memory, B: Bool,
  eB: {H.C(a, k, nx) == B : Bool}, hr: {Nat.is_le(F, r) == True{} : Bool}) ->
  H.Good(s, C.Wasm.call.go(F, H.loopfr(s, a, k, nx, tmp), mem)):
  match r:
    case 0n:
      match F:
        case 0n:
          Unit{}
        case 1n+q:
          L.ft(H.Good(s, C.Wasm.call.go(1n+q, H.loopfr(s, a, k, nx, tmp), mem)), hr)
    case 1n+r1:
      match B:
        case True{}:
          +F10 = Nat.sub(F, 10n)
          H.ext(10n, C.Wasm.Step.next{H.loopfr(s, a, k, nx, tmp), mem}, F, s,
            H.brfix(F10, s, a, k, nx, mem, H.C(a, k, nx), True{}, eB,
              H.ext(1n, C.Wasm.Step.next{H.brfr(s, a, k, nx, True{}), mem}, F10, s,
                H.exit(Nat.sub(F10, 1n), s, a, k, nx, mem))))
        case False{}:
          +F10 = Nat.sub(F, 10n)
          +n1 = U32.add(nx, 1)
          H.ext(10n, C.Wasm.Step.next{H.loopfr(s, a, k, nx, tmp), mem}, F, s,
            H.brfix(F10, s, a, k, nx, mem, H.C(a, k, nx), False{}, eB,
              H.ext(6n, C.Wasm.Step.next{H.brfr(s, a, k, nx, False{}), mem}, F10, s,
                H.loop(r1, Nat.sub(F10, 6n), s, a, k, n1, nx, mem, H.C(a, k, n1), {==},
                  H.le_sub(F10, r1, 6n, H.le_sub1(F, r1, 9n, hr))))))

# run(a, k) gives [s], traps or runs out of fuel
def H.run_good(+F: Nat, +s: U32, +a: U32, +k: U32, +mem: C.Wasm.Memory) ->
  H.Good(s, C.Wasm.call(F, C.Wasm.Func{2n, 1n, 6n, H.body(s, False{})}, [a, k], mem)):
  +F10 = Nat.sub(F, 10n)
  H.ext(10n, C.Wasm.Step.next{C.Wasm.Frame{H.body(s, False{}), [], 1n, [], [a, k, 0, 0, 0, 0, 0, 0]}, mem}, F, s,
    H.loop(F10, F10, s, a, k, 1, 0, mem, H.C(a, k, 1), {==}, H.le_refl(F10)))

# The host
# --------

# not a result
def H.NR(x: C.Wasm.Outcome) -> Type:
  match x:
    case C.Wasm.Outcome.result{_}:
      Empty
    case _:
      Unit

def H.nr.use(-x: C.Wasm.Outcome, -o: List<&2, U32>, n: H.NR(x), e: {x == C.Wasm.Outcome.result{o} : C.Wasm.Outcome}) -> Empty:
  %e : H.NR(_)
  n

def H.nr.status(b1: Bool, b2: Bool, mem: C.Wasm.Memory) -> H.NR(C.Wasm.run.status(False{}, b1, b2, mem)):
  match b1 b2:
    case True{} _:
      Unit{}
    case False{} True{}:
      Unit{}
    case False{} False{}:
      Unit{}

# what run gave, when it is good
def H.nr.ran(+s: U32, ns: {U32.is_eq(s, 0) == False{} : Bool}, c: C.Wasm.Call, g: H.Good(s, c)) ->
  H.NR(C.Wasm.run.ran(C.Wasm.invoked(c, H.mod(s, False{})))):
  match c:
    case C.Wasm.Call.done{vs, mem, n}:
      %Equal.sym(List<&2, U32>, vs, [s], g) : H.NR(C.Wasm.run.ran(C.Wasm.invoked(C.Wasm.Call.done{_, mem, n}, H.mod(s, False{}))))
      %Equal.sym(Bool, U32.is_eq(s, 0), False{}, ns) : H.NR(C.Wasm.run.status(_, U32.is_eq(s, 1), U32.is_eq(s, 2), mem))
      H.nr.status(U32.is_eq(s, 1), U32.is_eq(s, 2), mem)
    case C.Wasm.Call.trap{mem}:
      Unit{}
    case C.Wasm.Call.not_done{}:
      Unit{}

def H.nr.written(b: Bool, +f: Nat, +s: U32, ns: {U32.is_eq(s, 0) == False{} : Bool}, +a: U32, +k: U32,
  +p: U32, +lim: U32, +bytes: C.Wasm.Bytes, +i: List<&2, U32>) ->
  H.NR(C.Wasm.run.written(b, f, C.Wasm.Instance{H.mod(s, False{}), C.Wasm.Memory{p, lim, C.Wasm.write.bytes(i, a, bytes)}}, a, k)):
  match b:
    case True{}:
      +mem = {C.Wasm.Memory{p, lim, C.Wasm.write.bytes(i, a, bytes)} : C.Wasm.Memory}
      H.nr.ran(s, ns, C.Wasm.call(f, C.Wasm.Func{2n, 1n, 6n, H.body(s, False{})}, [a, k], mem), H.run_good(f, s, a, k, mem))
    case False{}:
      Unit{}

def H.nr.full(b: Bool, +f: Nat, +s: U32, ns: {U32.is_eq(s, 0) == False{} : Bool}, +a: U32, +k: U32,
  mem: C.Wasm.Memory, +i: List<&2, U32>) ->
  H.NR(C.Wasm.run.alloced.if(b, f, C.Wasm.Instance{H.mod(s, False{}), mem}, a, k, i)):
  match b:
    case True{}:
      Unit{}
    case False{}:
      match mem:
        case C.Wasm.Memory{+p, +lim, +bytes}:
          H.nr.written(C.Wasm.fits(p, a, k), f, s, ns, a, k, p, lim, bytes, i)

# what alloc gave
def H.nr.alloced(c: C.Wasm.Call, +f: Nat, +s: U32, ns: {U32.is_eq(s, 0) == False{} : Bool}, +k: U32, +i: List<&2, U32>) ->
  H.NR(C.Wasm.run.alloced(C.Wasm.invoked(c, H.mod(s, False{})), f, k, i)):
  match c:
    case C.Wasm.Call.done{vs, mem, used}:
      match vs:
        case Nil{}:
          Unit{}
        case Con{+a, rest}:
          H.nr.full(U32.is_eq(a, 4294967295), Nat.sub(f, used), s, ns, a, k, mem, i)
    case C.Wasm.Call.trap{mem}:
      Unit{}
    case C.Wasm.Call.not_done{}:
      Unit{}

def H.nr.sized(n: Maybe<&2, U32>, +f: Nat, +s: U32, ns: {U32.is_eq(s, 0) == False{} : Bool}, +mem: C.Wasm.Memory, +i: List<&2, U32>) ->
  H.NR(C.Wasm.run.sized(n, f, C.Wasm.Instance{H.mod(s, False{}), mem}, i)):
  match n:
    case None{}:
      Unit{}
    case Some{+k}:
      H.nr.alloced(C.Wasm.call(f, C.Cir.alloc(0), [k], mem), f, s, ns, k, i)

def H.nr.mem(b: Bool, +f: Nat, +s: U32, ns: {U32.is_eq(s, 0) == False{} : Bool}, +m: U32, +i: List<&2, U32>) ->
  H.NR(C.Wasm.run.made(f, C.Wasm.instantiate.sized(C.Wasm.memory.of.if(b, C.Wasm.Memory{1, C.Wasm.limit(None{}, m), C.Wasm.Bytes.zero{}}),
    Some{C.Wasm.Segment{20, []}}, H.mod(s, False{})), i)):
  match b:
    case True{}:
      H.nr.sized(C.Wasm.length32(i), f, s, ns, C.Wasm.Memory{1, C.Wasm.limit(None{}, m), C.Wasm.Bytes.zero{}}, i)
    case False{}:
      Unit{}

# the module that halts at once with s, not 0, gives no result
def H.nr.run(+f: Nat, +s: U32, +i: List<&2, U32>, +m: U32, +ns: {U32.is_eq(s, 0) == False{} : Bool}) ->
  H.NR(C.Wasm.run(f, C.Compiler.halt(s), i, m)):
  %Equal.sym(Maybe<&2, C.Wasm.Module>, C.Wasm.decode.module(C.Compiler.halt(s)), Some{H.mod(s, False{})}, H.decoded(s, ns)) :
    H.NR(C.Wasm.run.made(f, C.Wasm.instantiate.decoded(_, m), i))
  H.nr.mem(U32.is_le(1, m), f, s, ns, m, i)

# The lemmas
# ----------

# a module that halts at once with a status other than 0 gives no result
def halt.no_result.proof(
  +f: Nat, +s: U32, +i: List<&2, U32>, +m: U32, +o: List<&2, U32>,
  ns: {U32.is_eq(s, 0) == False{} : Bool},
  e: {C.Wasm.run(f, C.Compiler.halt(s), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome}
) -> Empty:
  H.nr.use(C.Wasm.run(f, C.Compiler.halt(s), i, m), o, H.nr.run(f, s, i, m, ns), e)

# Arithmetic of words
# -------------------
#
# Every lemma here is over words of any n bits, so that its proof computes
# only with variables; 2^32 never unfolds.

def H.bn(b: Bool) -> Nat:
  match b:
    case False{}:
      0n
    case True{}:
      1n

# 2^n
def H.W(n: Nat) -> Nat:
  PN.D(n, H.bn(True{}))

# a word is below 2^n
def H.bound(+n: Nat, w: Word(n)) -> PN.Le(1n+Word.to_nat(n, w), H.W(n)):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          PN.weaken(1n+Nat.double(Word.to_nat(p, t)), Nat.double(H.W(p)),
            PN.double_mono(1n+Word.to_nat(p, t), H.W(p), H.bound(p, t)))
        case WCon{True{}, +t}:
          PN.double_mono(1n+Word.to_nat(p, t), H.W(p), H.bound(p, t))

# the carry of a full adder
def H.carry(a: Bool, +b: Bool, +c: Bool) -> Bool:
  match a:
    case False{}:
      Bool.and(b, c)
    case True{}:
      Bool.or(b, c)

# the carry out of Word.adc(n, a, b, False, c)
def H.cout(n: Nat, a: Word(n), b: Word(n), c: Bool) -> Bool:
  match n:
    case 0n:
      c
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          H.cout(p, at, bt, H.carry(ab, bb, c))

# 2x + 2y = 2(x + y)
def H.dd(+x: Nat, +y: Nat) -> {Nat.add(Nat.double(x), Nat.double(y)) == Nat.double(Nat.add(x, y)) : Nat}:
  Equal.sym(Nat, Nat.double(Nat.add(x, y)), Nat.add(Nat.double(x), Nat.double(y)), PN.double_add(x, y))

# x + (b + y) = b + (x + y), for a bit b
def H.add_bit(+x: Nat, b: Bool, +y: Nat) -> {Nat.add(x, Nat.add(H.bn(b), y)) == Nat.add(H.bn(b), Nat.add(x, y)) : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      PN.add_succ_r(x, y)

def H.adc.l(+s: Bool, +S: Nat, +Dp: Nat, +k: Bool, +A: Nat, +B: Nat,
  ih: {Nat.add(S, Dp) == Nat.add(H.bn(k), Nat.add(A, B)) : Nat}) ->
  {Nat.add(H.bn(s), Nat.add(Nat.double(S), Nat.double(Dp))) == Nat.add(H.bn(s), Nat.double(Nat.add(H.bn(k), Nat.add(A, B)))) : Nat}:
  %ih : {Nat.add(H.bn(s), Nat.add(Nat.double(S), Nat.double(Dp))) == Nat.add(H.bn(s), Nat.double(_)) : Nat}
  Equal.cong(Nat, Nat, z => Nat.add(H.bn(s), z), Nat.add(Nat.double(S), Nat.double(Dp)), Nat.double(Nat.add(S, Dp)), H.dd(S, Dp))

def H.adc.r(+c: Bool, +ab: Bool, +bb: Bool, +A: Nat, +B: Nat) ->
  {Nat.add(H.bn(c), Nat.add(H.bn(ab), Nat.add(Nat.double(A), Nat.add(H.bn(bb), Nat.double(B))))) ==
    Nat.add(H.bn(c), Nat.add(H.bn(ab), Nat.add(H.bn(bb), Nat.double(Nat.add(A, B))))) : Nat}:
  %H.dd(A, B) : {Nat.add(H.bn(c), Nat.add(H.bn(ab), Nat.add(Nat.double(A), Nat.add(H.bn(bb), Nat.double(B))))) ==
    Nat.add(H.bn(c), Nat.add(H.bn(ab), Nat.add(H.bn(bb), _))) : Nat}
  Equal.cong(Nat, Nat, z => Nat.add(H.bn(c), Nat.add(H.bn(ab), z)),
    Nat.add(Nat.double(A), Nat.add(H.bn(bb), Nat.double(B))), Nat.add(H.bn(bb), Nat.add(Nat.double(A), Nat.double(B))),
    H.add_bit(Nat.double(A), bb, Nat.double(B)))

# one bit of an addition: s + 2k = a + b + c
def H.adc.fin(+s: Bool, +k: Bool, +c: Bool, +ab: Bool, +bb: Bool, +S: Nat, +Dp: Nat, +A: Nat, +B: Nat,
  ih: {Nat.add(S, Dp) == Nat.add(H.bn(k), Nat.add(A, B)) : Nat},
  mid: {Nat.add(H.bn(s), Nat.double(Nat.add(H.bn(k), Nat.add(A, B)))) ==
    Nat.add(H.bn(c), Nat.add(H.bn(ab), Nat.add(H.bn(bb), Nat.double(Nat.add(A, B))))) : Nat}) ->
  {Nat.add(H.bn(s), Nat.add(Nat.double(S), Nat.double(Dp))) ==
    Nat.add(H.bn(c), Nat.add(H.bn(ab), Nat.add(Nat.double(A), Nat.add(H.bn(bb), Nat.double(B))))) : Nat}:
  Equal.trans(Nat, Nat.add(H.bn(s), Nat.add(Nat.double(S), Nat.double(Dp))),
    Nat.add(H.bn(s), Nat.double(Nat.add(H.bn(k), Nat.add(A, B)))),
    Nat.add(H.bn(c), Nat.add(H.bn(ab), Nat.add(Nat.double(A), Nat.add(H.bn(bb), Nat.double(B))))),
    H.adc.l(s, S, Dp, k, A, B, ih),
    Equal.trans(Nat, Nat.add(H.bn(s), Nat.double(Nat.add(H.bn(k), Nat.add(A, B)))),
      Nat.add(H.bn(c), Nat.add(H.bn(ab), Nat.add(H.bn(bb), Nat.double(Nat.add(A, B))))),
      Nat.add(H.bn(c), Nat.add(H.bn(ab), Nat.add(Nat.double(A), Nat.add(H.bn(bb), Nat.double(B))))),
      mid, Equal.sym(Nat, Nat.add(H.bn(c), Nat.add(H.bn(ab), Nat.add(Nat.double(A), Nat.add(H.bn(bb), Nat.double(B))))),
        Nat.add(H.bn(c), Nat.add(H.bn(ab), Nat.add(H.bn(bb), Nat.double(Nat.add(A, B))))), H.adc.r(c, ab, bb, A, B))))

# the value of an addition, with its carry out
def H.adc(+n: Nat, +a: Word(n), +b: Word(n), +c: Bool) ->
  {Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, c)), PN.D(n, H.bn(H.cout(n, a, b, c)))) ==
    Nat.add(H.bn(c), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))) : Nat}:
  match n:
    case 0n:
      match c:
        case False{}:
          {==}
        case True{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          H.adc.fin(False{}, False{}, False{}, False{}, False{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})),
            PN.D(p, H.bn(H.cout(p, at, bt, False{}))), Word.to_nat(p, at), Word.to_nat(p, bt), H.adc(p, at, bt, False{}), {==})
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          H.adc.fin(True{}, False{}, True{}, False{}, False{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})),
            PN.D(p, H.bn(H.cout(p, at, bt, False{}))), Word.to_nat(p, at), Word.to_nat(p, bt), H.adc(p, at, bt, False{}), {==})
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          H.adc.fin(True{}, False{}, False{}, False{}, True{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})),
            PN.D(p, H.bn(H.cout(p, at, bt, False{}))), Word.to_nat(p, at), Word.to_nat(p, bt), H.adc(p, at, bt, False{}), {==})
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          H.adc.fin(False{}, True{}, True{}, False{}, True{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})),
            PN.D(p, H.bn(H.cout(p, at, bt, True{}))), Word.to_nat(p, at), Word.to_nat(p, bt), H.adc(p, at, bt, True{}), {==})
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          H.adc.fin(True{}, False{}, False{}, True{}, False{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})),
            PN.D(p, H.bn(H.cout(p, at, bt, False{}))), Word.to_nat(p, at), Word.to_nat(p, bt), H.adc(p, at, bt, False{}), {==})
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          H.adc.fin(False{}, True{}, True{}, True{}, False{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})),
            PN.D(p, H.bn(H.cout(p, at, bt, True{}))), Word.to_nat(p, at), Word.to_nat(p, bt), H.adc(p, at, bt, True{}), {==})
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          H.adc.fin(False{}, True{}, False{}, True{}, True{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})),
            PN.D(p, H.bn(H.cout(p, at, bt, True{}))), Word.to_nat(p, at), Word.to_nat(p, bt), H.adc(p, at, bt, True{}), {==})
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          H.adc.fin(True{}, True{}, True{}, True{}, True{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})),
            PN.D(p, H.bn(H.cout(p, at, bt, True{}))), Word.to_nat(p, at), Word.to_nat(p, bt), H.adc(p, at, bt, True{}), {==})

# 2^n × 0 = 0
def H.D0(n: Nat) -> {PN.D(n, 0n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %H.D0(p) : {Nat.double(PN.D(p, 0n)) == Nat.double(_) : Nat}
      {==}

def H.noc.z(+n: Nat, +V: Nat) -> {V == Nat.add(V, PN.D(n, 0n)) : Nat}:
  %Equal.sym(Nat, PN.D(n, 0n), 0n, H.D0(n)) : {V == Nat.add(V, _) : Nat}
  Equal.sym(Nat, Nat.add(V, 0n), V, PN.add_zero(V))

# a sum below 2^n has no carry out
def H.noc(o: Bool, +n: Nat, +V: Nat, +X: Nat, e: {Nat.add(V, PN.D(n, H.bn(o))) == X : Nat}, h: PN.Le(1n+X, H.W(n))) ->
  {V == X : Nat}:
  match o:
    case False{}:
      Equal.trans(Nat, V, Nat.add(V, PN.D(n, 0n)), X, H.noc.z(n, V), e)
    case True{}:
      +W = H.W(n)
      Empty.absurd({V == X : Nat}, PN.not_succ_le(W,
        PN.le_trans(1n+W, 1n+Nat.add(V, W), W, PN.le_add_l(V, W),
          PN.le_rw_l(1n+X, 1n+Nat.add(V, W), W, Equal.sym(Nat, 1n+Nat.add(V, W), 1n+X,
            Equal.cong(Nat, Nat, z => 1n+z, Nat.add(V, W), X, e)), h))))

# an addition below 2^n is exact
def H.add_ex(+n: Nat, +a: Word(n), +b: Word(n), h: PN.Le(1n+Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), H.W(n))) ->
  {Word.to_nat(n, Word.add(n, a, b)) == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}:
  H.noc(H.cout(n, a, b, False{}), n, Word.to_nat(n, Word.add(n, a, b)), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)),
    H.adc(n, a, b, False{}), h)

# an addition is at most the sum
def H.add_le(+n: Nat, +a: Word(n), +b: Word(n)) ->
  PN.Le(Word.to_nat(n, Word.add(n, a, b)), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))):
  +V = Word.to_nat(n, Word.add(n, a, b))
  +Dc = PN.D(n, H.bn(H.cout(n, a, b, False{})))
  PN.le_rw_r(V, Nat.add(V, Dc), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), H.adc(n, a, b, False{}), PN.le_add_r(V, Dc))

# the bit that a shift left pushes out of the top
def H.pout(n: Nat, c: Bool, w: Word(n)) -> Bool:
  match n:
    case 0n:
      c
    case 1n+p:
      match w:
        case WCon{b, t}:
          H.pout(p, b, t)

def H.sout(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          H.pout(p, b, t)

def H.put.fin(+c: Bool, +b: Bool, +Pv: Nat, +Dp: Nat, +T: Nat,
  ih: {Nat.add(Pv, Dp) == Nat.add(H.bn(b), Nat.double(T)) : Nat}) ->
  {Nat.add(H.bn(c), Nat.add(Nat.double(Pv), Nat.double(Dp))) == Nat.add(H.bn(c), Nat.double(Nat.add(H.bn(b), Nat.double(T)))) : Nat}:
  %ih : {Nat.add(H.bn(c), Nat.add(Nat.double(Pv), Nat.double(Dp))) == Nat.add(H.bn(c), Nat.double(_)) : Nat}
  Equal.cong(Nat, Nat, z => Nat.add(H.bn(c), z), Nat.add(Nat.double(Pv), Nat.double(Dp)), Nat.double(Nat.add(Pv, Dp)), H.dd(Pv, Dp))

# the value of a shift with c in at the bottom, with the bit out at the top
def H.put(+n: Nat, +c: Bool, +w: Word(n)) ->
  {Nat.add(Word.to_nat(n, Word.shl.put(n, c, w)), PN.D(n, H.bn(H.pout(n, c, w)))) == Nat.add(H.bn(c), Nat.double(Word.to_nat(n, w))) : Nat}:
  match n:
    case 0n:
      match c:
        case False{}:
          {==}
        case True{}:
          {==}
    case 1n+p:
      match c w:
        case False{} WCon{False{}, +t}:
          H.put.fin(False{}, False{}, Word.to_nat(p, Word.shl.put(p, False{}, t)), PN.D(p, H.bn(H.pout(p, False{}, t))), Word.to_nat(p, t), H.put(p, False{}, t))
        case False{} WCon{True{}, +t}:
          H.put.fin(False{}, True{}, Word.to_nat(p, Word.shl.put(p, True{}, t)), PN.D(p, H.bn(H.pout(p, True{}, t))), Word.to_nat(p, t), H.put(p, True{}, t))
        case True{} WCon{False{}, +t}:
          H.put.fin(True{}, False{}, Word.to_nat(p, Word.shl.put(p, False{}, t)), PN.D(p, H.bn(H.pout(p, False{}, t))), Word.to_nat(p, t), H.put(p, False{}, t))
        case True{} WCon{True{}, +t}:
          H.put.fin(True{}, True{}, Word.to_nat(p, Word.shl.put(p, True{}, t)), PN.D(p, H.bn(H.pout(p, True{}, t))), Word.to_nat(p, t), H.put(p, True{}, t))

# the value of a shift left, with the bit out at the top
def H.shl(+n: Nat, +w: Word(n)) ->
  {Nat.add(Word.to_nat(n, Word.shl(n, w)), PN.D(n, H.bn(H.sout(n, w)))) == Nat.double(Word.to_nat(n, w)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          H.put.fin(False{}, False{}, Word.to_nat(p, Word.shl.put(p, False{}, t)), PN.D(p, H.bn(H.pout(p, False{}, t))), Word.to_nat(p, t), H.put(p, False{}, t))
        case WCon{True{}, +t}:
          H.put.fin(False{}, True{}, Word.to_nat(p, Word.shl.put(p, True{}, t)), PN.D(p, H.bn(H.pout(p, True{}, t))), Word.to_nat(p, t), H.put(p, True{}, t))

# a shift left below 2^n is exact
def H.shl_ex(+n: Nat, +w: Word(n), h: PN.Le(1n+Nat.double(Word.to_nat(n, w)), H.W(n))) ->
  {Word.to_nat(n, Word.shl(n, w)) == Nat.double(Word.to_nat(n, w)) : Nat}:
  H.noc(H.sout(n, w), n, Word.to_nat(n, Word.shl(n, w)), Nat.double(Word.to_nat(n, w)), H.shl(n, w), h)

# all n bits are set (the top bit first)
def H.is_ones(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          Bool.and(H.is_ones(p, t), b)

# the word 1
def H.one(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{True{}, Word.zero(p)}

def H.and_l(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      L.ft({False{} == True{} : Bool}, h)

def H.and_r(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      L.ft({b == True{} : Bool}, h)

def H.and_t(a: Bool, h: {Bool.and(a, True{}) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      {==}

# adding zero with no carry
def H.z0(+n: Nat, +t: Word(n)) -> {Word.adc(n, t, Word.zero(n), False{}, False{}) == t : Word(n)}:
  match n:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+p:
      match t:
        case WCon{False{}, +r}:
          %H.z0(p, r) : {WCon{False{}, Word.adc(p, r, Word.zero(p), False{}, False{})} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +r}:
          %H.z0(p, r) : {WCon{True{}, Word.adc(p, r, Word.zero(p), False{}, False{})} == WCon{True{}, _} : Word(1n+p)}
          {==}

# adding zero with a carry, to a word that is not all ones
def H.z1(+n: Nat, +t: Word(n), ok: {H.is_ones(n, t) == False{} : Bool}) ->
  {Word.to_nat(n, Word.adc(n, t, Word.zero(n), False{}, True{})) == 1n+Word.to_nat(n, t) : Nat}:
  match n:
    case 0n:
      match t:
        case WNil{}:
          L.ft({Word.to_nat(0n, Word.adc(0n, WNil{}, Word.zero(0n), False{}, True{})) == 1n+Word.to_nat(0n, WNil{}) : Nat}, Equal.sym(Bool, True{}, False{}, ok))
    case 1n+p:
      match t:
        case WCon{False{}, +r}:
          %Equal.sym(Word(p), Word.adc(p, r, Word.zero(p), False{}, False{}), r, H.z0(p, r)) :
            {Word.to_nat(1n+p, WCon{True{}, _}) == 1n+Nat.double(Word.to_nat(p, r)) : Nat}
          {==}
        case WCon{True{}, +r}:
          %Equal.sym(Nat, Word.to_nat(p, Word.adc(p, r, Word.zero(p), False{}, True{})), 1n+Word.to_nat(p, r),
            H.z1(p, r, H.and_t(H.is_ones(p, r), ok))) :
            {Nat.double(_) == 2n+Nat.double(Word.to_nat(p, r)) : Nat}
          {==}

# adding 1 to a word that is not all ones
def H.inc(+n: Nat, +w: Word(n), ok: {H.is_ones(n, w) == False{} : Bool}) ->
  {Word.to_nat(n, Word.add(n, w, H.one(n))) == 1n+Word.to_nat(n, w) : Nat}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          L.ft({Word.to_nat(0n, Word.add(0n, WNil{}, H.one(0n))) == 1n+Word.to_nat(0n, WNil{}) : Nat}, Equal.sym(Bool, True{}, False{}, ok))
    case 1n+p:
      match w:
        case WCon{False{}, +r}:
          %Equal.sym(Word(p), Word.adc(p, r, Word.zero(p), False{}, False{}), r, H.z0(p, r)) :
            {Word.to_nat(1n+p, WCon{True{}, _}) == 1n+Nat.double(Word.to_nat(p, r)) : Nat}
          {==}
        case WCon{True{}, +r}:
          %Equal.sym(Nat, Word.to_nat(p, Word.adc(p, r, Word.zero(p), False{}, True{})), 1n+Word.to_nat(p, r),
            H.z1(p, r, H.and_t(H.is_ones(p, r), ok))) :
            {Nat.double(_) == 2n+Nat.double(Word.to_nat(p, r)) : Nat}
          {==}

# a word of all ones is 2^n - 1
def H.ones_val(+n: Nat, +w: Word(n), e: {H.is_ones(n, w) == True{} : Bool}) -> {1n+Word.to_nat(n, w) == H.W(n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, +r}:
          L.ft({1n+Word.to_nat(1n+p, WCon{False{}, r}) == H.W(1n+p) : Nat}, H.and_r(H.is_ones(p, r), False{}, e))
        case WCon{True{}, +r}:
          %H.ones_val(p, r, H.and_l(H.is_ones(p, r), True{}, e)) :
            {2n+Nat.double(Word.to_nat(p, r)) == Nat.double(_) : Nat}
          {==}

def H.not_ones.if(b: Bool, +n: Nat, +w: Word(n), e: {H.is_ones(n, w) == b : Bool},
  h: PN.Le(2n+Word.to_nat(n, w), H.W(n))) -> {H.is_ones(n, w) == False{} : Bool}:
  match b:
    case False{}:
      e
    case True{}:
      Empty.absurd({H.is_ones(n, w) == False{} : Bool}, PN.not_succ_le(1n+Word.to_nat(n, w),
        PN.le_rw_r(2n+Word.to_nat(n, w), H.W(n), 1n+Word.to_nat(n, w),
          Equal.sym(Nat, 1n+Word.to_nat(n, w), H.W(n), H.ones_val(n, w, e)), h)))

# a word 2 below 2^n is not all ones
def H.not_ones(+n: Nat, +w: Word(n), h: PN.Le(2n+Word.to_nat(n, w), H.W(n))) -> {H.is_ones(n, w) == False{} : Bool}:
  H.not_ones.if(H.is_ones(n, w), n, w, {==}, h)

# a shift right leaves the top bit clear
def H.pad_top(+p: Nat, +t: Word(p)) -> {H.is_ones(1n+p, Word.shr.pad(p, t)) == False{} : Bool}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      match t:
        case WCon{+b, +r}:
          %Equal.sym(Bool, H.is_ones(1n+q, Word.shr.pad(q, r)), False{}, H.pad_top(q, r)) : {Bool.and(_, b) == False{} : Bool}
          {==}

def H.shr_top(+n: Nat, +w: Word(1n+n)) -> {H.is_ones(1n+n, Word.shr(1n+n, w)) == False{} : Bool}:
  match w:
    case WCon{b, +t}:
      H.pad_top(n, t)

# Nat
# ---

# 20 × x
def H.t20(x: Nat) -> Nat:
  match x:
    case 0n:
      0n
    case 1n+p:
      20n+H.t20(p)

def H.t20_mono(+x: Nat, +y: Nat, h: PN.Le(x, y)) -> PN.Le(H.t20(x), H.t20(y)):
  match x:
    case 0n:
      PN.le_zero(H.t20(y))
    case 1n+p:
      match y:
        case 0n:
          Empty.absurd(PN.Le(H.t20(1n+p), 0n), h)
        case 1n+q:
          H.t20_mono(p, q, h)

# 20x < 20y gives x < y
def H.t20_lt(+x: Nat, +y: Nat, h: PN.Le(1n+H.t20(x), H.t20(y))) -> PN.Le(1n+x, y):
  match x y:
    case _ 0n:
      Empty.absurd(PN.Le(1n+x, 0n), h)
    case 0n 1n+q:
      PN.le_zero(q)
    case 1n+p 1n+q:
      H.t20_lt(p, q, h)

def H.le_t20(+x: Nat) -> PN.Le(x, H.t20(x)):
  match x:
    case 0n:
      Unit{}
    case 1n+p:
      PN.le_trans(p, H.t20(p), 19n+H.t20(p), H.le_t20(p), PN.le_add_l(19n, H.t20(p)))

# 20 × 2x = 2 × 20x
def H.t20_double(+x: Nat) -> {H.t20(Nat.double(x)) == Nat.double(H.t20(x)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %H.t20_double(p) : {40n+H.t20(Nat.double(p)) == 40n+_ : Nat}
      {==}

# a + (k + b) = k + (a + b)
def H.add_k(+a: Nat, +k: Nat, +b: Nat) -> {Nat.add(a, Nat.add(k, b)) == Nat.add(k, Nat.add(a, b)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+q:
      %H.add_k(a, q, b) : {Nat.add(a, 1n+Nat.add(q, b)) == 1n+_ : Nat}
      PN.add_succ_r(a, Nat.add(q, b))

# 16x + 4x = 20x
def H.t20_shifts(+x: Nat) -> {Nat.add(PN.D(4n, x), PN.D(2n, x)) == H.t20(x) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(PN.D(4n, p), Nat.add(4n, PN.D(2n, p))), Nat.add(4n, Nat.add(PN.D(4n, p), PN.D(2n, p))),
        H.add_k(PN.D(4n, p), 4n, PN.D(2n, p))) : {16n+_ == 20n+H.t20(p) : Nat}
      %Equal.sym(Nat, Nat.add(PN.D(4n, p), PN.D(2n, p)), H.t20(p), H.t20_shifts(p)) : {20n+_ == 20n+H.t20(p) : Nat}
      {==}

# n + m <= F gives m <= F - n
def H.le_sub_add(+n: Nat, +m: Nat, +F: Nat, h: PN.Le(Nat.add(n, m), F)) -> PN.Le(m, Nat.sub(F, n)):
  match n:
    case 0n:
      match F:
        case 0n:
          h
        case 1n+q:
          h
    case 1n+p:
      match F:
        case 0n:
          Empty.absurd(PN.Le(m, 0n), h)
        case 1n+q:
          H.le_sub_add(p, m, q, h)

# n + m <= F gives n <= F
def H.le_add_part(+n: Nat, +m: Nat, +F: Nat, h: PN.Le(Nat.add(n, m), F)) -> PN.Le(n, F):
  PN.le_trans(n, Nat.add(n, m), F, PN.le_add_r(n, m), h)

def H.le_double(+x: Nat) -> PN.Le(x, Nat.double(x)):
  match x:
    case 0n:
      Unit{}
    case 1n+p:
      PN.le_succ(p, Nat.double(p), H.le_double(p))

# j shifts left
def H.shlj(j: Nat, +n: Nat, w: Word(n)) -> Word(n):
  match j:
    case 0n:
      w
    case 1n+q:
      Word.shl(n, H.shlj(q, n, w))

# j shifts left below 2^n are exact
def H.shlj_ex(+j: Nat, +n: Nat, +w: Word(n), +h: PN.Le(1n+PN.D(j, Word.to_nat(n, w)), H.W(n))) ->
  {Word.to_nat(n, H.shlj(j, n, w)) == PN.D(j, Word.to_nat(n, w)) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+q:
      +X = Word.to_nat(n, w)
      +Y = PN.D(q, X)
      +sq = H.shlj(q, n, w)
      +ih = H.shlj_ex(q, n, w, PN.le_trans(1n+Y, 1n+Nat.double(Y), H.W(n), H.le_double(Y), h))
      Equal.trans(Nat, Word.to_nat(n, Word.shl(n, sq)), Nat.double(Word.to_nat(n, sq)), Nat.double(Y),
        H.shl_ex(n, sq, PN.le_rw_l(1n+Nat.double(Y), 1n+Nat.double(Word.to_nat(n, sq)), H.W(n),
          Equal.cong(Nat, Nat, z => 1n+Nat.double(z), Y, Word.to_nat(n, sq), Equal.sym(Nat, Word.to_nat(n, sq), Y, ih)), h)),
        Equal.cong(Nat, Nat, z => Nat.double(z), Word.to_nat(n, sq), Y, ih))

# 20x below 2^n, for x <= P where 2^4 + 20P = 2^n
def H.t20_bound(+n: Nat, +X: Nat, +P: Nat, +hP: {Nat.add(H.W(4n), H.t20(P)) == H.W(n) : Nat}, +hx: PN.Le(X, P)) ->
  PN.Le(1n+H.t20(X), H.W(n)):
  PN.le_trans(1n+H.t20(X), 1n+H.t20(P), H.W(n), H.t20_mono(X, P, hx),
    PN.le_rw_r(1n+H.t20(P), Nat.add(H.W(4n), H.t20(P)), H.W(n), hP, PN.le_add_l(15n, H.t20(P))))

# 16x + 4x, the module's 20 × x, is exact for x <= P
def H.tex_w(+n: Nat, +w: Word(n), +P: Nat, +hP: {Nat.add(H.W(4n), H.t20(P)) == H.W(n) : Nat},
  +hx: PN.Le(Word.to_nat(n, w), P)) ->
  {Word.to_nat(n, Word.add(n, H.shlj(4n, n, w), H.shlj(2n, n, w))) == H.t20(Word.to_nat(n, w)) : Nat}:
  +X = Word.to_nat(n, w)
  +b0 = H.t20_bound(n, X, P, hP, hx)
  +D4 = PN.D(4n, X)
  +D2 = PN.D(2n, X)
  +ts = H.t20_shifts(X)
  +s4 = H.shlj(4n, n, w)
  +s2 = H.shlj(2n, n, w)
  +bsum = PN.le_rw_l(1n+H.t20(X), 1n+Nat.add(D4, D2), H.W(n), Equal.cong(Nat, Nat, z => 1n+z, H.t20(X), Nat.add(D4, D2), Equal.sym(Nat, Nat.add(D4, D2), H.t20(X), ts)), b0)
  +e4 = H.shlj_ex(4n, n, w, PN.le_trans(1n+D4, 1n+Nat.add(D4, D2), H.W(n), PN.le_add_r(D4, D2), bsum))
  +e2 = H.shlj_ex(2n, n, w, PN.le_trans(1n+D2, 1n+Nat.add(D4, D2), H.W(n), PN.le_add_l(D4, D2), bsum))
  +esum = Equal.trans(Nat, Nat.add(Word.to_nat(n, s4), Word.to_nat(n, s2)), Nat.add(D4, Word.to_nat(n, s2)), Nat.add(D4, D2),
    Equal.cong(Nat, Nat, z => Nat.add(z, Word.to_nat(n, s2)), Word.to_nat(n, s4), D4, e4),
    Equal.cong(Nat, Nat, z => Nat.add(D4, z), Word.to_nat(n, s2), D2, e2))
  +ha = PN.le_rw_l(1n+Nat.add(D4, D2), 1n+Nat.add(Word.to_nat(n, s4), Word.to_nat(n, s2)), H.W(n),
    Equal.cong(Nat, Nat, z => 1n+z, Nat.add(D4, D2), Nat.add(Word.to_nat(n, s4), Word.to_nat(n, s2)),
      Equal.sym(Nat, Nat.add(Word.to_nat(n, s4), Word.to_nat(n, s2)), Nat.add(D4, D2), esum)), bsum)
  Equal.trans(Nat, Word.to_nat(n, Word.add(n, s4, s2)), Nat.add(D4, D2), H.t20(X),
    Equal.trans(Nat, Word.to_nat(n, Word.add(n, s4, s2)), Nat.add(Word.to_nat(n, s4), Word.to_nat(n, s2)), Nat.add(D4, D2),
      H.add_ex(n, s4, s2, ha), esum),
    ts)

# Comparisons
# -----------

def H.rel_nge(c: Cmp, +x: Nat, +y: Nat, h: PN.Rel(c, x, y), e: {Cmp.is_ge(c) == False{} : Bool}) -> PN.Le(1n+x, y):
  match c:
    case LT{}:
      h
    case EQ{}:
      Empty.absurd(PN.Le(1n+x, y), PN.true_ne_false(e))
    case GT{}:
      Empty.absurd(PN.Le(1n+x, y), PN.true_ne_false(e))

def H.rel_ngt(c: Cmp, +x: Nat, +y: Nat, h: PN.Rel(c, x, y), e: {Cmp.is_gt(c) == False{} : Bool}) -> PN.Le(x, y):
  match c:
    case LT{}:
      PN.weaken(x, y, h)
    case EQ{}:
      %h : PN.Le(x, _)
      PN.le_refl(x)
    case GT{}:
      Empty.absurd(PN.Le(x, y), PN.true_ne_false(e))

def H.rel_le(c: Cmp, +x: Nat, +y: Nat, h: PN.Rel(c, x, y), e: {Cmp.is_le(c) == True{} : Bool}) -> PN.Le(x, y):
  match c:
    case LT{}:
      PN.weaken(x, y, h)
    case EQ{}:
      %h : PN.Le(x, _)
      PN.le_refl(x)
    case GT{}:
      Empty.absurd(PN.Le(x, y), PN.false_ne_true(e))

def H.rel_lt(c: Cmp, +x: Nat, +y: Nat, h: PN.Rel(c, x, y), l: PN.Le(1n+x, y)) -> {Cmp.is_lt(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_lt(EQ{}) == True{} : Bool}, PN.not_succ_le(y, PN.le_rw_l(1n+x, 1n+y, y, Equal.cong(Nat, Nat, z => 1n+z, x, y, h), l)))
    case GT{}:
      Empty.absurd({Cmp.is_lt(GT{}) == True{} : Bool}, PN.not_succ_le(y, PN.le_trans(1n+y, x, y, h, PN.weaken(x, y, l))))

# Running to a status of 1
# ------------------------

# a call that gives the results [1]
def H.GoodO(c: C.Wasm.Call) -> Type:
  match c:
    case C.Wasm.Call.done{rs, _, _}:
      {rs == [1] : List<&2, U32>}
    case C.Wasm.Call.trap{_}:
      Empty
    case C.Wasm.Call.not_done{}:
      Empty

def H.GoodO.plus(c: C.Wasm.Call, g: H.GoodO(c)) -> H.GoodO(C.Wasm.call.plus(c)):
  match c:
    case C.Wasm.Call.done{rs, m, n}:
      g
    case C.Wasm.Call.trap{m}:
      g
    case C.Wasm.Call.not_done{}:
      g

def H.GO(F: Nat, st: C.Wasm.Step) -> Type:
  match st:
    case C.Wasm.Step.next{fr, m}:
      H.GoodO(C.Wasm.call.go(F, fr, m))
    case C.Wasm.Step.done{rs, _}:
      {rs == [1] : List<&2, U32>}
    case C.Wasm.Step.trap{_}:
      Empty

def H.GO.stepped(F: Nat, st: C.Wasm.Step, h: H.GO(F, st)) ->
  H.GoodO(C.Wasm.call.stepped(st, g => m => C.Wasm.call.go(F, g, m))):
  match st:
    case C.Wasm.Step.next{fr, m}:
      H.GoodO.plus(C.Wasm.call.go(F, fr, m), h)
    case C.Wasm.Step.done{rs, m}:
      h
    case C.Wasm.Step.trap{m}:
      h

# a run gives [1] when it does after n steps, with the fuel left
def H.extO(n: Nat, +st: C.Wasm.Step, +F: Nat, hF: PN.Le(n, F), g: H.GO(Nat.sub(F, n), H.steps(n, st))) -> H.GO(F, st):
  match n:
    case 0n:
      match F:
        case 0n:
          g
        case 1n+q:
          g
    case 1n+p:
      match st:
        case C.Wasm.Step.next{fr, m}:
          match F:
            case 0n:
              Empty.absurd(H.GO(0n, C.Wasm.Step.next{fr, m}), hF)
            case 1n+F1:
              H.GO.stepped(F1, C.Wasm.step(fr, m), H.extO(p, C.Wasm.step(fr, m), F1, hF, g))
        case C.Wasm.Step.done{rs, m}:
          g
        case C.Wasm.Step.trap{m}:
          g

def H.brfixO(+F: Nat, +a: U32, +k: U32, +nx: U32, +mem: C.Wasm.Memory, -c: Bool, -B: Bool, e: {c == B : Bool},
  g: H.GoodO(C.Wasm.call.go(F, H.brfr(1, a, k, nx, B), mem))) -> H.GoodO(C.Wasm.call.go(F, H.brfr(1, a, k, nx, c), mem)):
  %Equal.sym(Bool, c, B, e) : H.GoodO(C.Wasm.call.go(F, H.brfr(1, a, k, nx, _), mem))
  g

def H.exitO(+F: Nat, hF: PN.Le(7n, F), +a: U32, +k: U32, +nx: U32, +mem: C.Wasm.Memory) ->
  H.GoodO(C.Wasm.call.go(F, H.exfr(1, a, k, nx), mem)):
  H.extO(7n, C.Wasm.Step.next{H.exfr(1, a, k, nx), mem}, F, hF, {==})

# the fuel of b rounds of the first loop that go on
def H.Rf(b: Nat) -> Nat:
  match b:
    case 0n:
      0n
    case 1n+p:
      16n+H.Rf(p)

# x < P gives x + 2 <= 2^n
def H.small(+n: Nat, +X: Nat, +P: Nat, +hP: {Nat.add(H.W(4n), H.t20(P)) == H.W(n) : Nat}, h: PN.Le(1n+X, P)) ->
  PN.Le(2n+X, H.W(n)):
  PN.le_trans(2n+X, 1n+H.t20(P), H.W(n), PN.le_trans(1n+X, P, H.t20(P), h, H.le_t20(P)),
    PN.le_rw_r(1n+H.t20(P), Nat.add(H.W(4n), H.t20(P)), H.W(n), hP, PN.le_add_l(15n, H.t20(P))))

# the loop's exit, for any number of rounds left
def H.loopO.exit(+F: Nat, +k: U32, +x: U32, +tmp: U32, +mem: C.Wasm.Memory, e: {H.C(20, k, x) == True{} : Bool},
  +h18: PN.Le(18n, F)) -> H.GoodO(C.Wasm.call.go(F, H.loopfr(1, 20, k, x, tmp), mem)):
  +F10 = Nat.sub(F, 10n)
  +h8 = H.le_sub_add(10n, 8n, F, h18)
  H.extO(10n, C.Wasm.Step.next{H.loopfr(1, 20, k, x, tmp), mem}, F, H.le_add_part(10n, 8n, F, h18),
    H.brfixO(F10, 20, k, x, mem, H.C(20, k, x), True{}, e,
      H.extO(1n, C.Wasm.Step.next{H.brfr(1, 20, k, x, True{}), mem}, F10, H.le_add_part(1n, 7n, F10, h8),
        H.exitO(Nat.sub(F10, 1n), H.le_sub_add(1n, 7n, F10, h8), 20, k, x, mem))))

# a round that goes on: 20 × next < a + n
def H.loopO.lt(+k: U32, +w: Word(32n), +P: Nat, +hP: {Nat.add(H.W(4n), H.t20(P)) == H.W(32n) : Nat},
  +hx: PN.Le(U32.to_nat(U32{w}), P), e: {H.C(20, k, U32{w}) == False{} : Bool}) ->
  PN.Le(1n+H.t20(U32.to_nat(U32{w})), U32.to_nat(U32.add(20, k))):
  +T = U32.add(U32.shln(U32{w}, 4n), U32.shln(U32{w}, 2n))
  +E = U32.add(20, k)
  PN.le_rw_l(1n+U32.to_nat(T), 1n+H.t20(U32.to_nat(U32{w})), U32.to_nat(E),
    Equal.cong(Nat, Nat, z => 1n+z, U32.to_nat(T), H.t20(U32.to_nat(U32{w})), H.tex_w(32n, w, P, hP, hx)),
    H.rel_nge(U32.cmp(T, E), U32.to_nat(T), U32.to_nat(E), PN.U32.rel(T, E), e))

# the first loop gives [1], with b rounds of fuel at least: a round that
# goes on has 20 × next < a + n <= 20P, so next < P, and next + 1 is exact
def H.loopO(+b: Nat, +F: Nat, +k: U32, +x: U32, +tmp: U32, +mem: C.Wasm.Memory, B: Bool,
  +eB: {H.C(20, k, x) == B : Bool}, +P: Nat, +hP: {Nat.add(H.W(4n), H.t20(P)) == H.W(32n) : Nat},
  +hE: PN.Le(U32.to_nat(U32.add(20, k)), H.t20(P)), +hx: PN.Le(U32.to_nat(x), P),
  +hb: PN.Le(1n+U32.to_nat(U32.add(20, k)), H.t20(Nat.add(U32.to_nat(x), b))),
  +hF: PN.Le(Nat.add(H.Rf(b), 18n), F)) ->
  H.GoodO(C.Wasm.call.go(F, H.loopfr(1, 20, k, x, tmp), mem)):
  match b:
    case 0n:
      match x:
        case U32{+w}:
          match B:
            case True{}:
              H.loopO.exit(F, k, U32{w}, tmp, mem, eB, hF)
            case False{}:
              +X = U32.to_nat(U32{w})
              +E = U32.to_nat(U32.add(20, k))
              +lt = H.loopO.lt(k, w, P, hP, hx, eB)
              +hb0 = PN.le_rw_r(1n+E, H.t20(Nat.add(X, 0n)), H.t20(X), Equal.cong(Nat, Nat, z => H.t20(z), Nat.add(X, 0n), X, PN.add_zero(X)), hb)
              Empty.absurd(H.GoodO(C.Wasm.call.go(F, H.loopfr(1, 20, k, U32{w}, tmp), mem)),
                PN.not_succ_le(H.t20(X), PN.weaken(1n+H.t20(X), H.t20(X), PN.le_trans(2n+H.t20(X), 1n+E, H.t20(X), lt, hb0))))
    case 1n+q:
      match x:
        case U32{+w}:
          match B:
            case True{}:
              H.loopO.exit(F, k, U32{w}, tmp, mem, eB, PN.le_trans(18n, Nat.add(H.Rf(1n+q), 18n), F, PN.le_add_l(H.Rf(1n+q), 18n), hF))
            case False{}:
              +X = U32.to_nat(U32{w})
              +E = U32.to_nat(U32.add(20, k))
              +lt = H.loopO.lt(k, w, P, hP, hx, eB)
              +hxP = H.t20_lt(X, P, PN.le_trans(1n+H.t20(X), E, H.t20(P), lt, hE))
              +ok = H.not_ones(32n, w, H.small(32n, Word.to_nat(32n, w), P, hP, hxP))
              +x1 = U32.add(U32{w}, 1)
              +einc = {H.inc(32n, w, ok) : {U32.to_nat(x1) == 1n+X : Nat}}
              +hx1 = PN.le_rw_l(1n+X, U32.to_nat(x1), P, Equal.sym(Nat, U32.to_nat(x1), 1n+X, einc), hxP)
              +eb = Equal.trans(Nat, H.t20(Nat.add(X, 1n+q)), H.t20(Nat.add(1n+X, q)), H.t20(Nat.add(U32.to_nat(x1), q)),
                Equal.cong(Nat, Nat, z => H.t20(z), Nat.add(X, 1n+q), 1n+Nat.add(X, q), PN.add_succ_r(X, q)),
                Equal.cong(Nat, Nat, z => H.t20(Nat.add(z, q)), 1n+X, U32.to_nat(x1), Equal.sym(Nat, U32.to_nat(x1), 1n+X, einc)))
              +hb1 = PN.le_rw_r(1n+E, H.t20(Nat.add(X, 1n+q)), H.t20(Nat.add(U32.to_nat(x1), q)), eb, hb)
              +F10 = Nat.sub(F, 10n)
              +rest = Nat.add(H.Rf(q), 18n)
              +h10 = H.le_sub_add(10n, Nat.add(6n, rest), F, hF)
              H.extO(10n, C.Wasm.Step.next{H.loopfr(1, 20, k, U32{w}, tmp), mem}, F, H.le_add_part(10n, Nat.add(6n, rest), F, hF),
                H.brfixO(F10, 20, k, U32{w}, mem, H.C(20, k, U32{w}), False{}, eB,
                  H.extO(6n, C.Wasm.Step.next{H.brfr(1, 20, k, U32{w}, False{}), mem}, F10, H.le_add_part(6n, rest, F10, h10),
                    H.loopO(q, Nat.sub(F10, 6n), k, x1, U32{w}, mem, H.C(20, k, x1), {==}, P, hP, hE, hx1, hb1,
                      H.le_sub_add(6n, rest, F10, h10)))))

# Identities of words
# -------------------

# an addition does not depend on the order of its terms
def H.add_comm(+n: Nat, +a: Word(n), +b: Word(n), +c: Bool) ->
  {Word.adc(n, a, b, False{}, c) == Word.adc(n, b, a, False{}, c) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          %H.add_comm(p, at, bt, False{}) : {WCon{False{}, Word.adc(p, at, bt, False{}, False{})} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          %H.add_comm(p, at, bt, False{}) : {WCon{True{}, Word.adc(p, at, bt, False{}, False{})} == WCon{True{}, _} : Word(1n+p)}
          {==}
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          %H.add_comm(p, at, bt, False{}) : {WCon{True{}, Word.adc(p, at, bt, False{}, False{})} == WCon{True{}, _} : Word(1n+p)}
          {==}
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          %H.add_comm(p, at, bt, True{}) : {WCon{False{}, Word.adc(p, at, bt, False{}, True{})} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          %H.add_comm(p, at, bt, False{}) : {WCon{True{}, Word.adc(p, at, bt, False{}, False{})} == WCon{True{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          %H.add_comm(p, at, bt, True{}) : {WCon{False{}, Word.adc(p, at, bt, False{}, True{})} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          %H.add_comm(p, at, bt, True{}) : {WCon{False{}, Word.adc(p, at, bt, False{}, True{})} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          %H.add_comm(p, at, bt, True{}) : {WCon{True{}, Word.adc(p, at, bt, False{}, True{})} == WCon{True{}, _} : Word(1n+p)}
          {==}

# adding all ones and a carry leaves a word as it was
def H.s1(+n: Nat, +t: Word(n)) -> {Word.adc(n, t, Word.zero(n), True{}, True{}) == t : Word(n)}:
  match n:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+p:
      match t:
        case WCon{False{}, +r}:
          %Equal.sym(Word(p), Word.adc(p, r, Word.zero(p), True{}, True{}), r, H.s1(p, r)) : {WCon{False{}, _} == WCon{False{}, r} : Word(1n+p)}
          {==}
        case WCon{True{}, +r}:
          %Equal.sym(Word(p), Word.adc(p, r, Word.zero(p), True{}, True{}), r, H.s1(p, r)) : {WCon{True{}, _} == WCon{True{}, r} : Word(1n+p)}
          {==}

# adding 1, then all ones, leaves a word as it was
def H.incdec(+n: Nat, +t: Word(n)) ->
  {Word.adc(n, Word.adc(n, t, Word.zero(n), False{}, True{}), Word.zero(n), True{}, False{}) == t : Word(n)}:
  match n:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+p:
      match t:
        case WCon{False{}, +r}:
          %Equal.sym(Word(p), Word.adc(p, r, Word.zero(p), False{}, False{}), r, H.z0(p, r)) :
            {Word.adc(1n+p, WCon{True{}, _}, Word.zero(1n+p), True{}, False{}) == WCon{False{}, r} : Word(1n+p)}
          %Equal.sym(Word(p), Word.adc(p, r, Word.zero(p), True{}, True{}), r, H.s1(p, r)) : {WCon{False{}, _} == WCon{False{}, r} : Word(1n+p)}
          {==}
        case WCon{True{}, +r}:
          %Equal.sym(Word(p), Word.adc(p, Word.adc(p, r, Word.zero(p), False{}, True{}), Word.zero(p), True{}, False{}), r, H.incdec(p, r)) :
            {WCon{True{}, _} == WCon{True{}, r} : Word(1n+p)}
          {==}

# x + 1 - 1 = x
def H.sub_add1(+n: Nat, +x: Word(n)) -> {Word.sub(n, Word.add(n, x, H.one(n)), H.one(n)) == x : Word(n)}:
  match n:
    case 0n:
      match x:
        case WNil{}:
          {==}
    case 1n+p:
      match x:
        case WCon{False{}, +r}:
          %Equal.sym(Word(p), Word.adc(p, r, Word.zero(p), False{}, False{}), r, H.z0(p, r)) :
            {Word.sub(1n+p, WCon{True{}, _}, H.one(1n+p)) == WCon{False{}, r} : Word(1n+p)}
          %Equal.sym(Word(p), Word.adc(p, r, Word.zero(p), True{}, True{}), r, H.s1(p, r)) : {WCon{False{}, _} == WCon{False{}, r} : Word(1n+p)}
          {==}
        case WCon{True{}, +r}:
          %Equal.sym(Word(p), Word.adc(p, Word.adc(p, r, Word.zero(p), False{}, True{}), Word.zero(p), True{}, False{}), r, H.incdec(p, r)) :
            {WCon{True{}, _} == WCon{True{}, r} : Word(1n+p)}
          {==}

# The host, for the status 1
# --------------------------

def H.M1() -> C.Wasm.Module:
  H.mod(1, False{})

# run gave [1]: out of memory
def H.ranO(c: C.Wasm.Call, g: H.GoodO(c)) ->
  {C.Wasm.run.ran(C.Wasm.invoked(c, H.M1())) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}:
  match c:
    case C.Wasm.Call.done{vs, mem, n}:
      %Equal.sym(List<&2, U32>, vs, [1], g) :
        {C.Wasm.run.ran(C.Wasm.invoked(C.Wasm.Call.done{_, mem, n}, H.M1())) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}
      {==}
    case C.Wasm.Call.trap{mem}:
      Empty.absurd({C.Wasm.run.ran(C.Wasm.invoked(C.Wasm.Call.trap{mem}, H.M1())) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}, g)
    case C.Wasm.Call.not_done{}:
      Empty.absurd({C.Wasm.run.ran(C.Wasm.invoked(C.Wasm.Call.not_done{}, H.M1())) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}, g)

# the fuel that run needs, for an input of K bytes
def H.runfuel(K: Nat) -> Nat:
  Nat.add(10n, Nat.add(H.Rf(1n+K), 18n))

# the bits of a U32
def H.u32w(x: U32) -> Word(32n):
  match x:
    case U32{w}:
      w

# a + n <= 20 + n < 20 × (2 + n)
def H.hb0(+kw: Word(32n)) ->
  PN.Le(1n+U32.to_nat(U32.add(20, U32{kw})), H.t20(Nat.add(U32.to_nat(1), 1n+U32.to_nat(U32{kw})))):
  +K = U32.to_nat(U32{kw})
  +E = U32.to_nat(U32.add(20, U32{kw}))
  +le = {H.add_le(32n, H.u32w(20), kw) : PN.Le(E, Nat.add(20n, K))}
  PN.le_trans(1n+E, 21n+K, 40n+H.t20(K), le,
    PN.le_trans(21n+K, 21n+H.t20(K), 40n+H.t20(K), H.le_t20(K), PN.le_add_l(19n, H.t20(K))))

# run(20, k) gives [1], with enough fuel
def H.runO(+F: Nat, +k: U32, +mem: C.Wasm.Memory, +P: Nat, +hP: {Nat.add(H.W(4n), H.t20(P)) == H.W(32n) : Nat},
  +hE: PN.Le(U32.to_nat(U32.add(20, k)), H.t20(P)), +h1: PN.Le(U32.to_nat(1), P),
  +hF: PN.Le(H.runfuel(U32.to_nat(k)), F)) ->
  H.GoodO(C.Wasm.call(F, C.Wasm.Func{2n, 1n, 6n, H.body(1, False{})}, [20, k], mem)):
  match k:
    case U32{+kw}:
      +rest = Nat.add(H.Rf(1n+U32.to_nat(U32{kw})), 18n)
      H.extO(10n, C.Wasm.Step.next{C.Wasm.Frame{H.body(1, False{}), [], 1n, [], [20, U32{kw}, 0, 0, 0, 0, 0, 0]}, mem}, F,
        H.le_add_part(10n, rest, F, hF),
        H.loopO(1n+U32.to_nat(U32{kw}), Nat.sub(F, 10n), U32{kw}, 1, 0, mem, H.C(20, U32{kw}, 1), {==}, P, hP, hE, h1,
          H.hb0(kw), H.le_sub_add(10n, rest, F, hF)))

# The input fits
# --------------

def H.or_r(a: Bool, -b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

# the input's k bytes from 20 fit in p pages, when 20 + k does not wrap and
# its last byte's page is below p
def H.fits(+k: U32, +p: U32, c1: {U32.is_lt(U32.add(20, k), 20) == False{} : Bool},
  hX: {U32.is_lt(U32.shrn(U32.sub(U32.add(20, k), 1), 16n), p) == True{} : Bool}) -> {C.Wasm.fits(p, 20, k) == True{} : Bool}:
  +E = U32.add(20, k)
  %Equal.sym(Bool, U32.is_lt(E, 20), False{}, c1) :
    {Bool.and(Bool.not(_), Bool.or(U32.is_zero(E), U32.is_lt(U32.shrn(U32.sub(E, 1), 16n), p))) == True{} : Bool}
  H.or_r(U32.is_zero(E), U32.is_lt(U32.shrn(U32.sub(E, 1), 16n), p), hX)

# x + 1 <= 1 gives x < 1, for x = z >> 1
def H.hX1(+Z: U32, c3: {U32.is_le(U32.add(U32.shr(Z), 1), 1) == True{} : Bool}) -> {U32.is_lt(U32.shr(Z), 1) == True{} : Bool}:
  match Z:
    case U32{+zw}:
      +X = U32.shr(U32{zw})
      +A = U32.add(X, 1)
      +inc = {H.inc(32n, Word.shr(32n, zw), H.shr_top(31n, zw)) : {U32.to_nat(A) == 1n+U32.to_nat(X) : Nat}}
      +le = H.rel_le(U32.cmp(A, 1), U32.to_nat(A), U32.to_nat(1), PN.U32.rel(A, 1), c3)
      H.rel_lt(U32.cmp(X, 1), U32.to_nat(X), U32.to_nat(1), PN.U32.rel(X, 1), PN.le_rw_l(U32.to_nat(A), 1n+U32.to_nat(X), U32.to_nat(1), inc, le))

# x < 1 + (x + 1 - 1), for x = z >> 1
def H.hX2(+Z: U32) -> {U32.is_lt(U32.shr(Z), U32.add(1, U32.sub(U32.add(U32.shr(Z), 1), 1))) == True{} : Bool}:
  match Z:
    case U32{+zw}:
      +Xw = Word.shr(32n, zw)
      +X = {U32{Xw} : U32}
      +A = U32.add(X, 1)
      %Equal.sym(Word(32n), Word.sub(32n, Word.add(32n, Xw, H.one(32n)), H.one(32n)), Xw, H.sub_add1(32n, Xw)) :
        {U32.is_lt(X, U32{Word.add(32n, H.one(32n), _)}) == True{} : Bool}
      %Equal.sym(Word(32n), Word.adc(32n, H.one(32n), Xw, False{}, False{}), Word.adc(32n, Xw, H.one(32n), False{}, False{}),
        H.add_comm(32n, H.one(32n), Xw, False{})) : {U32.is_lt(X, U32{_}) == True{} : Bool}
      +inc = {H.inc(32n, Xw, H.shr_top(31n, zw)) : {U32.to_nat(A) == 1n+U32.to_nat(X) : Nat}}
      H.rel_lt(U32.cmp(X, A), U32.to_nat(X), U32.to_nat(A), PN.U32.rel(X, A),
        PN.le_rw_r(1n+U32.to_nat(X), 1n+U32.to_nat(X), U32.to_nat(A), Equal.sym(Nat, U32.to_nat(A), 1n+U32.to_nat(X), inc), PN.le_refl(1n+U32.to_nat(X))))

# The bounds
# ----------

# the word of n bits whose z lowest bits are clear, and the others set
def H.fwc(n: Nat, z: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match z:
        case 0n:
          WCon{True{}, H.fwc(p, 0n)}
        case 1n+q:
          WCon{False{}, H.fwc(p, q)}

# 2^z + that word = 2^n
def H.fwc_val(+n: Nat, +z: Nat, h: PN.Le(z, n)) -> {Nat.add(H.W(z), Word.to_nat(n, H.fwc(n, z))) == H.W(n) : Nat}:
  match n:
    case 0n:
      match z:
        case 0n:
          {==}
        case 1n+q:
          Empty.absurd({Nat.add(H.W(1n+q), Word.to_nat(0n, H.fwc(0n, 1n+q))) == H.W(0n) : Nat}, h)
    case 1n+p:
      match z:
        case 0n:
          %H.fwc_val(p, 0n, PN.le_zero(p)) : {2n+Nat.double(Word.to_nat(p, H.fwc(p, 0n))) == Nat.double(_) : Nat}
          {==}
        case 1n+q:
          %H.fwc_val(p, q, h) : {Nat.add(Nat.double(H.W(q)), Nat.double(Word.to_nat(p, H.fwc(p, q)))) == Nat.double(_) : Nat}
          H.dd(H.W(q), Word.to_nat(p, H.fwc(p, q)))

def H.pred(z: Nat) -> Nat:
  match z:
    case 0n:
      0n
    case 1n+q:
      q

# a + x = a + y gives x = y
def H.lcancel(+a: Nat, -x: Nat, -y: Nat, e: {Nat.add(a, x) == Nat.add(a, y) : Nat}) -> {x == y : Nat}:
  match a:
    case 0n:
      e
    case 1n+p:
      H.lcancel(p, x, y, Equal.cong(Nat, Nat, z => H.pred(z), 1n+Nat.add(p, x), 1n+Nat.add(p, y), e))

def H.cancel(-E: Nat, -Fu: Nat, -Fv: Nat, +A: Nat, -Pt: Nat, -W: Nat, e1: {Fu == Fv : Nat},
  e2: {Nat.add(A, Fv) == W : Nat}, e3: {Nat.add(A, Pt) == W : Nat}, h: PN.Le(E, Fu)) -> PN.Le(E, Pt):
  PN.le_rw_r(E, Fu, Pt, Equal.trans(Nat, Fu, Fv, Pt, e1,
    H.lcancel(A, Fv, Pt, Equal.trans(Nat, Nat.add(A, Fv), W, Nat.add(A, Pt), e2, Equal.sym(Nat, Nat.add(A, Pt), W, e3)))), h)

def H.lit_fw() -> {4294967280 == U32{H.fwc(32n, 4n)} : U32}:
  {==}

# a + n <= 2^32 - 16 = 20P
def H.hE(+kw: Word(32n), -P: Nat, hP: {Nat.add(H.W(4n), H.t20(P)) == H.W(32n) : Nat},
  c2: {U32.is_gt(U32.add(20, U32{kw}), 4294967280) == False{} : Bool}) -> PN.Le(U32.to_nat(U32.add(20, U32{kw})), H.t20(P)):
  +E = U32.add(20, U32{kw})
  +fw = H.fwc(32n, 4n)
  +c2w = Equal.trans(Bool, U32.is_gt(E, U32{fw}), U32.is_gt(E, 4294967280), False{},
    Equal.cong(U32, Bool, z => U32.is_gt(E, z), U32{fw}, 4294967280, Equal.sym(U32, 4294967280, U32{fw}, H.lit_fw())), c2)
  +ngt = H.rel_ngt(U32.cmp(E, U32{fw}), U32.to_nat(E), U32.to_nat(U32{fw}), PN.U32.rel(E, U32{fw}), c2w)
  H.cancel(U32.to_nat(E), U32.to_nat(U32{fw}), Word.to_nat(32n, fw), H.W(4n), H.t20(P), H.W(32n), PN.u32_to_nat(fw),
    H.fwc_val(32n, 4n, Unit{}), hP, ngt)

# 20 × t20(2^4 x) = 2^4 × 20x
def H.t20_D4(+x: Nat) -> {H.t20(PN.D(4n, x)) == PN.D(4n, H.t20(x)) : Nat}:
  +x1 = Nat.double(x)
  +x2 = Nat.double(x1)
  +x3 = Nat.double(x2)
  Equal.trans(Nat, H.t20(Nat.double(x3)), Nat.double(H.t20(x3)), Nat.double(Nat.double(Nat.double(Nat.double(H.t20(x))))),
    H.t20_double(x3),
    Equal.cong(Nat, Nat, z => Nat.double(z), H.t20(x3), Nat.double(Nat.double(Nat.double(H.t20(x)))),
      Equal.trans(Nat, H.t20(x3), Nat.double(H.t20(x2)), Nat.double(Nat.double(Nat.double(H.t20(x)))),
        H.t20_double(x2),
        Equal.cong(Nat, Nat, z => Nat.double(z), H.t20(x2), Nat.double(Nat.double(H.t20(x))),
          Equal.trans(Nat, H.t20(x2), Nat.double(H.t20(x1)), Nat.double(Nat.double(H.t20(x))),
            H.t20_double(x1),
            Equal.cong(Nat, Nat, z => Nat.double(z), H.t20(x1), Nat.double(H.t20(x)), H.t20_double(x)))))))

# 0x0CCC...C, nibble by nibble: 12 + 16 × the rest
def H.pat(j: Nat) -> Nat:
  match j:
    case 0n:
      0n
    case 1n+q:
      Nat.add(12n, PN.D(4n, H.pat(q)))

def H.e4(j: Nat) -> Nat:
  match j:
    case 0n:
      4n
    case 1n+q:
      4n+H.e4(q)

# 2^4 + 20 × pat(j) = 2^(4 + 4j)
def H.pat_val(+j: Nat) -> {Nat.add(H.W(4n), H.t20(H.pat(j))) == H.W(H.e4(j)) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+q:
      %H.pat_val(q) : {256n+H.t20(PN.D(4n, H.pat(q))) == PN.D(4n, _) : Nat}
      %Equal.sym(Nat, H.t20(PN.D(4n, H.pat(q))), PN.D(4n, H.t20(H.pat(q))), H.t20_D4(H.pat(q))) :
        {256n+_ == 256n+PN.D(4n, H.t20(H.pat(q))) : Nat}
      {==}

# 2^4 + 20 × 214748364 = 2^32
def H.hP() -> {Nat.add(H.W(4n), H.t20(H.pat(7n))) == H.W(32n) : Nat}:
  %{{==} : {H.e4(7n) == 32n : Nat}} : {Nat.add(H.W(4n), H.t20(H.pat(7n))) == H.W(_) : Nat}
  H.pat_val(7n)

def H.h1g(j: Nat, h: PN.Le(1n, j)) -> PN.Le(U32.to_nat(1), H.pat(j)):
  match j:
    case 0n:
      Empty.absurd(PN.Le(U32.to_nat(1), H.pat(0n)), h)
    case 1n+q:
      Unit{}

def H.h1() -> PN.Le(U32.to_nat(1), H.pat(7n)):
  H.h1g(7n, Unit{})

# The function alloc
# ------------------

def H.plusN(n: Nat, c: C.Wasm.Call) -> C.Wasm.Call:
  match n:
    case 0n:
      c
    case 1n+p:
      C.Wasm.call.plus(H.plusN(p, c))

def H.A.B2() -> List<&2, C.Wasm.Instr>:
  [C.Wasm.Instr.local_get{3}, C.Wasm.Instr.memory_size{}, C.Wasm.Instr.op{C.Wasm.Op.le_u{}}, C.Wasm.Instr.br_if{0},
   C.Wasm.Instr.local_get{3}, C.Wasm.Instr.memory_size{}, C.Wasm.Instr.op{C.Wasm.Op.sub{}}, C.Wasm.Instr.memory_grow{},
   C.Wasm.Instr.const{4294967295}, C.Wasm.Instr.op{C.Wasm.Op.eq{}}, C.Wasm.Instr.br_if{1}]

def H.A.B1() -> List<&2, C.Wasm.Instr>:
  [C.Wasm.Instr.local_get{1}, C.Wasm.Instr.const{20}, C.Wasm.Instr.op{C.Wasm.Op.lt_u{}}, C.Wasm.Instr.br_if{0},
   C.Wasm.Instr.local_get{1}, C.Wasm.Instr.const{4294967280}, C.Wasm.Instr.op{C.Wasm.Op.gt_u{}}, C.Wasm.Instr.br_if{0},
   C.Wasm.Instr.local_get{1}, C.Wasm.Instr.const{1}, C.Wasm.Instr.op{C.Wasm.Op.sub{}}, C.Wasm.Instr.const{16},
   C.Wasm.Instr.op{C.Wasm.Op.shr_u{}}, C.Wasm.Instr.const{1}, C.Wasm.Instr.op{C.Wasm.Op.add{}}, C.Wasm.Instr.local_set{3},
   C.Wasm.Instr.block{H.A.B2()}, C.Wasm.Instr.const{20}, C.Wasm.Instr.local_set{2}]

def H.A.LA1() -> List<&2, C.Wasm.Label>:
  [C.Wasm.Label{None{}, [C.Wasm.Instr.local_get{2}], 0n}]

def H.A.LA2() -> List<&2, C.Wasm.Label>:
  Con{C.Wasm.Label{None{}, [C.Wasm.Instr.const{20}, C.Wasm.Instr.local_set{2}], 0n}, H.A.LA1()}

def H.A.E(+k: U32) -> U32:
  U32.add(20, k)

def H.A.X(+k: U32) -> U32:
  U32.shrn(U32.sub(H.A.E(k), 1), 16n)

def H.A.need(+k: U32) -> U32:
  U32.add(H.A.X(k), 1)

def H.A.L0(+k: U32) -> List<&2, U32>:
  [k, H.A.E(k), 4294967295, 0]

def H.A.L3(+k: U32) -> List<&2, U32>:
  [k, H.A.E(k), 4294967295, H.A.need(k)]

def H.A.BP1(+k: U32, c: Bool) -> C.Wasm.Frame:
  C.Wasm.Frame{List.drop(&2, C.Wasm.Instr, H.A.B1(), 3n), H.A.LA1(), 1n, [Bool.to_u32(c)], H.A.L0(k)}

def H.A.BP2(+k: U32, c: Bool) -> C.Wasm.Frame:
  C.Wasm.Frame{List.drop(&2, C.Wasm.Instr, H.A.B1(), 7n), H.A.LA1(), 1n, [Bool.to_u32(c)], H.A.L0(k)}

def H.A.BP3(+k: U32, c: Bool) -> C.Wasm.Frame:
  C.Wasm.Frame{List.drop(&2, C.Wasm.Instr, H.A.B2(), 3n), H.A.LA2(), 1n, [Bool.to_u32(c)], H.A.L3(k)}

def H.A.mem(+m: U32) -> C.Wasm.Memory:
  C.Wasm.Memory{1, C.Wasm.limit(None{}, m), C.Wasm.Bytes.zero{}}

# the pages after a memory.grow that succeeds
def H.A.np(+k: U32) -> U32:
  U32.add(1, U32.sub(H.A.need(k), 1))

def H.A.c4(+k: U32, +m: U32) -> Bool:
  U32.is_ge(H.A.np(k), 1) && U32.is_le(H.A.np(k), C.Wasm.limit(None{}, m))

def H.A.GP(+k: U32, +m: U32, c: Bool) -> C.Wasm.Step:
  C.Wasm.step.grown(c, 1, H.A.np(k), C.Wasm.limit(None{}, m), C.Wasm.Bytes.zero{},
    [C.Wasm.Instr.const{4294967295}, C.Wasm.Instr.op{C.Wasm.Op.eq{}}, C.Wasm.Instr.br_if{1}], H.A.LA2(), 1n, [], H.A.L3(k))

def H.A.Y(+k: U32) -> Nat:
  H.runfuel(U32.to_nat(k))

# what the host does with alloc's call c
def H.AO(+f: Nat, +k: U32, +i: List<&2, U32>, c: C.Wasm.Call) -> Type:
  {C.Wasm.run.alloced(C.Wasm.invoked(c, H.M1()), f, k, i) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}

# the input's pages after a memory.grow that succeeds
def H.A.al4(B: Bool, +kw: Word(32n), +i: List<&2, U32>, +m: U32, e4: {H.A.c4(U32{kw}, m) == B : Bool},
  +P: Nat, +hP: {Nat.add(H.W(4n), H.t20(P)) == H.W(32n) : Nat},
  +hE: PN.Le(U32.to_nat(U32.add(20, U32{kw})), H.t20(P)), +h1: PN.Le(U32.to_nat(1), P),
  +e1: {U32.is_lt(H.A.E(U32{kw}), 20) == False{} : Bool}) ->
  H.AO(Nat.add(64n, H.A.Y(U32{kw})), U32{kw}, i, H.plusN(31n, C.Wasm.call.stepped(H.A.GP(U32{kw}, m, H.A.c4(U32{kw}, m)),
    g => mm => C.Wasm.call.go(Nat.add(32n, H.A.Y(U32{kw})), g, mm)))):
  match B:
    case True{}:
      +k = {U32{kw} : U32}
      +Y = H.A.Y(k)
      +f = Nat.add(64n, Y)
      %Equal.sym(Bool, H.A.c4(k, m), True{}, e4) :
        H.AO(f, k, i, H.plusN(31n, C.Wasm.call.stepped(H.A.GP(k, m, _), g => mm => C.Wasm.call.go(Nat.add(32n, Y), g, mm))))
      +memw = {C.Wasm.Memory{H.A.np(k), C.Wasm.limit(None{}, m), C.Wasm.write.bytes(i, 20, C.Wasm.Bytes.zero{})} : C.Wasm.Memory}
      %Equal.sym(Bool, C.Wasm.fits(H.A.np(k), 20, k), True{},
        H.fits(k, H.A.np(k), e1, H.hX2(U32.shrn(U32.sub(H.A.E(k), 1), 15n)))) :
        {C.Wasm.run.written(_, Nat.sub(f, 41n), C.Wasm.Instance{H.M1(), memw}, 20, k) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}
      H.ranO(C.Wasm.call(Nat.sub(f, 41n), C.Wasm.Func{2n, 1n, 6n, H.body(1, False{})}, [20, k], memw),
        H.runO(Nat.sub(f, 41n), k, memw, P, hP, hE, h1, PN.le_add_l(23n, Y)))
    case False{}:
      +k = {U32{kw} : U32}
      +Y = H.A.Y(k)
      +f = Nat.add(64n, Y)
      %Equal.sym(Bool, H.A.c4(k, m), False{}, e4) :
        H.AO(f, k, i, H.plusN(31n, C.Wasm.call.stepped(H.A.GP(k, m, _), g => mm => C.Wasm.call.go(Nat.add(32n, Y), g, mm))))
      {==}

# the memory holds the input already, or must grow
def H.A.al3(B: Bool, +kw: Word(32n), +i: List<&2, U32>, +m: U32, +e3: {U32.is_le(H.A.need(U32{kw}), 1) == B : Bool},
  +P: Nat, +hP: {Nat.add(H.W(4n), H.t20(P)) == H.W(32n) : Nat},
  +hE: PN.Le(U32.to_nat(U32.add(20, U32{kw})), H.t20(P)), +h1: PN.Le(U32.to_nat(1), P),
  +e1: {U32.is_lt(H.A.E(U32{kw}), 20) == False{} : Bool}) ->
  H.AO(Nat.add(64n, H.A.Y(U32{kw})), U32{kw}, i,
    H.plusN(27n, C.Wasm.call.go(Nat.add(37n, H.A.Y(U32{kw})), H.A.BP3(U32{kw}, U32.is_le(H.A.need(U32{kw}), 1)), H.A.mem(m)))):
  match B:
    case True{}:
      +k = {U32{kw} : U32}
      +Y = H.A.Y(k)
      +f = Nat.add(64n, Y)
      %Equal.sym(Bool, U32.is_le(H.A.need(k), 1), True{}, e3) :
        H.AO(f, k, i, H.plusN(27n, C.Wasm.call.go(Nat.add(37n, Y), H.A.BP3(k, _), H.A.mem(m))))
      +memw = {C.Wasm.Memory{1, C.Wasm.limit(None{}, m), C.Wasm.write.bytes(i, 20, C.Wasm.Bytes.zero{})} : C.Wasm.Memory}
      %Equal.sym(Bool, C.Wasm.fits(1, 20, k), True{},
        H.fits(k, 1, e1, H.hX1(U32.shrn(U32.sub(H.A.E(k), 1), 15n), e3))) :
        {C.Wasm.run.written(_, Nat.sub(f, 33n), C.Wasm.Instance{H.M1(), memw}, 20, k) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}
      H.ranO(C.Wasm.call(Nat.sub(f, 33n), C.Wasm.Func{2n, 1n, 6n, H.body(1, False{})}, [20, k], memw),
        H.runO(Nat.sub(f, 33n), k, memw, P, hP, hE, h1, PN.le_add_l(31n, Y)))
    case False{}:
      +k = {U32{kw} : U32}
      +Y = H.A.Y(k)
      +f = Nat.add(64n, Y)
      %Equal.sym(Bool, U32.is_le(H.A.need(k), 1), False{}, e3) :
        H.AO(f, k, i, H.plusN(27n, C.Wasm.call.go(Nat.add(37n, Y), H.A.BP3(k, _), H.A.mem(m))))
      H.A.al4(H.A.c4(k, m), kw, i, m, {==}, P, hP, hE, h1, e1)

# the input ends at 2^32 - 16 or below
def H.A.al2(B: Bool, +kw: Word(32n), +i: List<&2, U32>, +m: U32, +e2: {U32.is_gt(H.A.E(U32{kw}), 4294967280) == B : Bool},
  +P: Nat, +hP: {Nat.add(H.W(4n), H.t20(P)) == H.W(32n) : Nat}, +h1: PN.Le(U32.to_nat(1), P),
  +e1: {U32.is_lt(H.A.E(U32{kw}), 20) == False{} : Bool}) ->
  H.AO(Nat.add(64n, H.A.Y(U32{kw})), U32{kw}, i,
    H.plusN(14n, C.Wasm.call.go(Nat.add(50n, H.A.Y(U32{kw})), H.A.BP2(U32{kw}, U32.is_gt(H.A.E(U32{kw}), 4294967280)), H.A.mem(m)))):
  match B:
    case True{}:
      +k = {U32{kw} : U32}
      +Y = H.A.Y(k)
      %Equal.sym(Bool, U32.is_gt(H.A.E(k), 4294967280), True{}, e2) :
        H.AO(Nat.add(64n, Y), k, i, H.plusN(14n, C.Wasm.call.go(Nat.add(50n, Y), H.A.BP2(k, _), H.A.mem(m))))
      {==}
    case False{}:
      +k = {U32{kw} : U32}
      +Y = H.A.Y(k)
      %Equal.sym(Bool, U32.is_gt(H.A.E(k), 4294967280), False{}, e2) :
        H.AO(Nat.add(64n, Y), k, i, H.plusN(14n, C.Wasm.call.go(Nat.add(50n, Y), H.A.BP2(k, _), H.A.mem(m))))
      H.A.al3(U32.is_le(H.A.need(k), 1), kw, i, m, {==}, P, hP, H.hE(kw, P, hP, e2), h1, e1)

# 20 + n does not wrap
def H.A.al1(B: Bool, +kw: Word(32n), +i: List<&2, U32>, +m: U32, +e1: {U32.is_lt(H.A.E(U32{kw}), 20) == B : Bool},
  +P: Nat, +hP: {Nat.add(H.W(4n), H.t20(P)) == H.W(32n) : Nat}, +h1: PN.Le(U32.to_nat(1), P)) ->
  H.AO(Nat.add(64n, H.A.Y(U32{kw})), U32{kw}, i,
    H.plusN(10n, C.Wasm.call.go(Nat.add(54n, H.A.Y(U32{kw})), H.A.BP1(U32{kw}, U32.is_lt(H.A.E(U32{kw}), 20)), H.A.mem(m)))):
  match B:
    case True{}:
      +k = {U32{kw} : U32}
      +Y = H.A.Y(k)
      %Equal.sym(Bool, U32.is_lt(H.A.E(k), 20), True{}, e1) :
        H.AO(Nat.add(64n, Y), k, i, H.plusN(10n, C.Wasm.call.go(Nat.add(54n, Y), H.A.BP1(k, _), H.A.mem(m))))
      {==}
    case False{}:
      +k = {U32{kw} : U32}
      +Y = H.A.Y(k)
      %Equal.sym(Bool, U32.is_lt(H.A.E(k), 20), False{}, e1) :
        H.AO(Nat.add(64n, Y), k, i, H.plusN(10n, C.Wasm.call.go(Nat.add(54n, Y), H.A.BP1(k, _), H.A.mem(m))))
      H.A.al2(U32.is_gt(H.A.E(k), 4294967280), kw, i, m, {==}, P, hP, h1, e1)

# alloc, then run: out of memory, for an input of k bytes
def H.A.top(+kw: Word(32n), +i: List<&2, U32>, +m: U32, +P: Nat, +hP: {Nat.add(H.W(4n), H.t20(P)) == H.W(32n) : Nat},
  +h1: PN.Le(U32.to_nat(1), P)) ->
  H.AO(Nat.add(64n, H.A.Y(U32{kw})), U32{kw}, i, C.Wasm.call(Nat.add(64n, H.A.Y(U32{kw})), C.Cir.alloc(0), [U32{kw}], H.A.mem(m))):
  H.A.al1(U32.is_lt(H.A.E(U32{kw}), 20), kw, i, m, {==}, P, hP, h1)

def H.oom.len(n: Maybe<&2, U32>, +i: List<&2, U32>, +m: U32) ->
  &f:Nat -> {C.Wasm.run.sized(n, f, C.Wasm.Instance{H.M1(), H.A.mem(m)}, i) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}:
  match n:
    case None{}:
      (0n, {==})
    case Some{+k}:
      match k:
        case U32{+kw}:
          (Nat.add(64n, H.A.Y(U32{kw})), H.A.top(kw, i, m, H.pat(7n), H.hP(), H.h1()))

def H.oom.mem(b: Bool, +i: List<&2, U32>, +m: U32) ->
  &f:Nat -> {C.Wasm.run.made(f, C.Wasm.instantiate.sized(C.Wasm.memory.of.if(b, C.Wasm.Memory{1, C.Wasm.limit(None{}, m), C.Wasm.Bytes.zero{}}),
    Some{C.Wasm.Segment{20, []}}, H.M1()), i) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}:
  match b:
    case False{}:
      (0n, {==})
    case True{}:
      H.oom.len(C.Wasm.length32(i), i, m)

# a module that halts at once with the status 1 runs out of memory
def halt.oom.proof(+i: List<&2, U32>, +m: U32) -> &f:Nat -> {C.Wasm.run(f, C.Compiler.halt(1), i, m) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}:
  %Equal.sym(Maybe<&2, C.Wasm.Module>, C.Wasm.decode.module(C.Compiler.halt(1)), Some{H.mod(1, False{})}, H.decoded(1, {==})) :
    &f:Nat -> {C.Wasm.run.made(f, C.Wasm.instantiate.decoded(_, m), i) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}
  H.oom.mem(U32.is_le(1, m), i, m)
