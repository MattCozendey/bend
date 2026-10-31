# compiler: the proofs of halt.no_result and halt.oom
# ===================================================

import Base
import ./impl.bend as C
import ./proof_leb.bend as L

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

def H.mod_is(+s: U32) -> {C.Cir.module(C.Cir.Stmt.halt{s}, 0n, []) == H.mod(s, U32.is_zero(s)) : C.Wasm.Module}:
  {==}

def H.t1() -> {C.Wasm.decode.module(C.Wasm.encode(H.mod(1, False{}))) == Some{H.mod(1, False{})} : Maybe<&2, C.Wasm.Module>}:
  {==}

def H.t2(+s: U32) -> {C.Wasm.valid.module(H.mod(s, False{})) == True{} : Bool}:
  {==}

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

def H.bytes_is(+s: U32) -> {C.Wasm.encode(H.mod(s, False{})) == H.bytes(C.Wasm.encode.sleb(s)) : List<&2, U32>}:
  {==}

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
