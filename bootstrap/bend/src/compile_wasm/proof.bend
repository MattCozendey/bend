import Base
import ../shared/impl.bend as Shared
import ../source/impl.bend as Source
import ../source/proof.bend as SP
import ../front/impl.bend as Front
import ../front/spec.bend as FrS
import ../front/proof.bend as FrP
import ../machine/impl.bend as Machine
import ../machine/spec.bend as MS
import ../machine/proof.bend as MP
import ../wasm/impl.bend as Wasm
import ../imp/impl.bend as Imp
import ../imp/spec.bend as IS
import ../imp/proof.bend as IP
import ../fun/impl.bend as Fun
import ../fun/proof.bend as FP
import ../fmachine/impl.bend as FM
import ../fmachine/code.bend as Code
import ../fmachine/spec.bend as FMS
import ../fmachine/proof.bend as FMP
import ../runtime/impl.bend as RT
import ../runtime/spec.bend as RS
import ../runtime/proof.bend as RP
import ./spec.bend as Spec
import ./impl.bend as C

# Proof of the contract
# =====================
#
# The laws of the contract (spec.bend) for the compiler of impl.bend, from the
# laws of its steps: the front, the machine, the machine in F, the run time
# and Imp. The fuel of the module comes from these laws: the machine's fuel
# (MS.fuel_m), the steps of F that the law keeps of the machine in F gives,
# the fuel of the run time (RS.fuel), then the fuel of Imp (IS.fuel_out).

# Facts
# =====

# the steps of a reach, and its end after them
def Reach.n(+prog: List<&2, Fun.C>, +s: Fun.Step, +t: Fun.Step, r: Fun.Reach(prog, s, t)) -> Nat:
  (+n, +e) = r
  n

def Reach.at(+prog: List<&2, Fun.C>, +s: Fun.Step, +t: Fun.Step, r: Fun.Reach(prog, s, t)) ->
  {Fun.F.iter(Reach.n(prog, s, t, r), prog, s) == t : Fun.Step}:
  (+n, +e) = r
  e

def Or.t(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def Bytes.or(m: Maybe<&2, List<&2, Nat>>, d: List<&2, Nat>) -> List<&2, Nat>:
  match m:
    case Some{x}:
      x
    case None{}:
      d

def Bytes.inj(-a: List<&2, Nat>, -b: List<&2, Nat>, e: {Some{a} == Some{b} : Maybe<&2, List<&2, Nat>>}) ->
  {a == b : List<&2, Nat>}:
  Equal.cong(Maybe<&2, List<&2, Nat>>, List<&2, Nat>, m => Bytes.or(m, []), Some{a}, Some{b}, e)

def V.inj(-a: Fun.V, -b: Fun.V, e: {Some{a} == Some{b} : Maybe<&2, Fun.V>}) -> {a == b : Fun.V}:
  Equal.cong(Maybe<&2, Fun.V>, Fun.V, m => FP.Out.value(m, Fun.V.z{}), Some{a}, Some{b}, e)

# Bytes.is_eq of the run time is Name.is_eq
def Bytes.name(a: List<&2, Nat>, b: List<&2, Nat>) -> {RS.Bytes.is_eq(a, b) == Source.Name.is_eq(a, b) : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Con{+x, +xs} Con{+y, +ys}:
      Equal.cong(Bool, Bool, t => Bool.and(Nat.is_eq(x, y), t), RS.Bytes.is_eq(xs, ys), Source.Name.is_eq(xs, ys),
        Bytes.name(xs, ys))
    case Nil{} Con{y, ys}:
      {==}
    case Con{x, xs} Nil{}:
      {==}

# the run time decodes the output that the machine in F encodes
def Name.dec(xs: List<&2, Nat>) -> {RS.Out.dec(FM.Enc.name(xs)) == Some{xs} : Maybe<&2, List<&2, Nat>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %Equal.sym(Maybe<&2, List<&2, Nat>>, RS.Out.dec(FM.Enc.name(rest)), Some{rest}, Name.dec(rest)) :
        {RS.Out.dec.con(x, _) == Some{Con{x, rest}} : Maybe<&2, List<&2, Nat>>}
      {==}

# the input as the run time builds it is the input of FM.start
def Name.in(bs: List<&2, Nat>) -> {FM.Enc.name(bs) == RS.In.name(bs) : Fun.V}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +rest}:
      Equal.cong(Fun.V, Fun.V, t => Fun.V.n{1n, Fun.V.num(b), t}, FM.Enc.name(rest), RS.In.name(rest), Name.in(rest))

def Mname.in(input: Maybe<&2, List<&2, Nat>>) -> {FM.Enc.mname(input) == RS.In.val(input) : Fun.V}:
  match input:
    case None{}:
      {==}
    case Some{+bs}:
      Equal.cong(Fun.V, Fun.V, t => Fun.V.n{1n, t, Fun.V.z{}}, FM.Enc.name(bs), RS.In.name(bs), Name.in(bs))

def Start.eq(+bk: List<&2, Source.Def>, +input: Maybe<&2, List<&2, Nat>>) ->
  {FM.start.of(bk, input, 255n) == RS.Start(Code.F.Main(), FM.Enc.book(bk), input, C.Tail(bk)) : Fun.S}:
  Equal.cong(Fun.V, Fun.S, v => Fun.S.run{Code.F.Main(), Con{FM.Enc.book(bk), Con{v, C.Tail(bk)}}, []},
    FM.Enc.mname(input), RS.In.val(input), Mname.in(input))

# Wasm.fits gives an input of bytes
def Bytes.le(xs: List<&2, Nat>, +h: {Wasm.Bytes.is(xs) == True{} : Bool}) -> {FMS.Input.le(xs, 255n) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      RP.And.mk(Nat.is_le(x, 255n), FMS.Input.le(rest, 255n),
        RP.AtMost.le(x, 255, RP.And.l(Wasm.Nat.at_most(x, 255), Wasm.Bytes.is(rest), h)),
        Bytes.le(rest, RP.And.r(Wasm.Nat.at_most(x, 255), Wasm.Bytes.is(rest), h)))

def In.ok(input: Maybe<&2, List<&2, Nat>>, +lim: U32, h: {Wasm.Input.fits(input, lim) == True{} : Bool}) ->
  {FMS.Input.ok(input, 255n) == True{} : Bool}:
  match input:
    case None{}:
      {==}
    case Some{+xs}:
      Bytes.le(xs, RP.And.l(Wasm.Bytes.is(xs), Wasm.Nat.at_most(List.length(&2, Nat, xs), lim), h))

def Fits.ok(+pages: Nat, +input: Maybe<&2, List<&2, Nat>>, +hf: {Wasm.Wasm.fits(pages, input) == True{} : Bool}) ->
  {FMS.Input.ok(input, 255n) == True{} : Bool}:
  In.ok(input, U32.sub(Wasm.Wasm.size(pages), 4), RP.Wf.in(pages, input, hf))

# Obs.is_eq is equality
def Obs.eq_of(a: Source.Obs, b: Source.Obs, +h: {Source.Obs.is_eq(a, b) == True{} : Bool}) -> {a == b : Source.Obs}:
  match a b:
    case Source.Obs.lab{+x} Source.Obs.lab{+y}:
      Equal.cong(List<&2, Nat>, Source.Obs, k => Source.Obs.lab{k}, x, y, SP.Name.is_eq_true(x, y, h))
    case Source.Obs.rfl{} Source.Obs.rfl{}:
      {==}
    case Source.Obs.tup{+a1, +a2} Source.Obs.tup{+b1, +b2}:
      +e1 = Obs.eq_of(a1, b1, RP.And.l(Source.Obs.is_eq(a1, b1), Source.Obs.is_eq(a2, b2), h))
      +e2 = Obs.eq_of(a2, b2, RP.And.r(Source.Obs.is_eq(a1, b1), Source.Obs.is_eq(a2, b2), h))
      %e1 : {Source.Obs.tup{a1, a2} == Source.Obs.tup{_, b2} : Source.Obs}
      %e2 : {Source.Obs.tup{a1, a2} == Source.Obs.tup{a1, _} : Source.Obs}
      {==}
    case Source.Obs.tup0{+a2} Source.Obs.tup0{+b2}:
      Equal.cong(Source.Obs, Source.Obs, o => Source.Obs.tup0{o}, a2, b2, Obs.eq_of(a2, b2, h))
    case Source.Obs.lab{x} Source.Obs.rfl{}:
      Shared.Bool.absurd({Source.Obs.lab{x} == Source.Obs.rfl{} : Source.Obs}, h)
    case Source.Obs.lab{x} Source.Obs.tup{b1, b2}:
      Shared.Bool.absurd({Source.Obs.lab{x} == Source.Obs.tup{b1, b2} : Source.Obs}, h)
    case Source.Obs.lab{x} Source.Obs.tup0{b2}:
      Shared.Bool.absurd({Source.Obs.lab{x} == Source.Obs.tup0{b2} : Source.Obs}, h)
    case Source.Obs.rfl{} Source.Obs.lab{y}:
      Shared.Bool.absurd({Source.Obs.rfl{} == Source.Obs.lab{y} : Source.Obs}, h)
    case Source.Obs.rfl{} Source.Obs.tup{b1, b2}:
      Shared.Bool.absurd({Source.Obs.rfl{} == Source.Obs.tup{b1, b2} : Source.Obs}, h)
    case Source.Obs.rfl{} Source.Obs.tup0{b2}:
      Shared.Bool.absurd({Source.Obs.rfl{} == Source.Obs.tup0{b2} : Source.Obs}, h)
    case Source.Obs.tup{a1, a2} Source.Obs.lab{y}:
      Shared.Bool.absurd({Source.Obs.tup{a1, a2} == Source.Obs.lab{y} : Source.Obs}, h)
    case Source.Obs.tup{a1, a2} Source.Obs.rfl{}:
      Shared.Bool.absurd({Source.Obs.tup{a1, a2} == Source.Obs.rfl{} : Source.Obs}, h)
    case Source.Obs.tup{a1, a2} Source.Obs.tup0{b2}:
      Shared.Bool.absurd({Source.Obs.tup{a1, a2} == Source.Obs.tup0{b2} : Source.Obs}, h)
    case Source.Obs.tup0{a2} Source.Obs.lab{y}:
      Shared.Bool.absurd({Source.Obs.tup0{a2} == Source.Obs.lab{y} : Source.Obs}, h)
    case Source.Obs.tup0{a2} Source.Obs.rfl{}:
      Shared.Bool.absurd({Source.Obs.tup0{a2} == Source.Obs.rfl{} : Source.Obs}, h)
    case Source.Obs.tup0{a2} Source.Obs.tup{b1, b2}:
      Shared.Bool.absurd({Source.Obs.tup0{a2} == Source.Obs.tup{b1, b2} : Source.Obs}, h)

# a result that is kept is the same result
def Kept.some(m: Maybe<&2, Source.Obs>, +o: Source.Obs, h: {Source.Obs.is_kept(Some{o}, m) == True{} : Bool}) ->
  {m == Some{o} : Maybe<&2, Source.Obs>}:
  match m:
    case Some{+o2}:
      Equal.cong(Source.Obs, Maybe<&2, Source.Obs>, x => Some{x}, o2, o, Equal.sym(Source.Obs, o, o2, Obs.eq_of(o, o2, h)))
    case None{}:
      Shared.Bool.absurd({None{} == Some{o} : Maybe<&2, Source.Obs>}, h)

# more fuel keeps the source's result
def Obs.more(j: Nat, +t: Source.Term, +m: Nat, +bk: List<&2, Source.Def>, -o: Source.Obs,
  h: {Source.Maybe.observe(Source.Term.run(m, t, bk)) == Some{o} : Maybe<&2, Source.Obs>}) ->
  {Source.Maybe.observe(Source.Term.run(Nat.add(j, m), t, bk)) == Some{o} : Maybe<&2, Source.Obs>}:
  match j:
    case 0n:
      h
    case 1n++i:
      MP.Obs.mono(t, Nat.add(i, m), bk, o, Obs.more(i, t, m, bk, o, h))

# Front.book gives the defs that some fuel parses
def Book.ok(+n: Nat, +src: List<&2, Nat>, +bk: List<&2, Source.Def>,
  h: {Source.Book.parse(n, src) == Some{bk} : Maybe<&2, List<&2, Source.Def>>}) ->
  {Front.Front.book(src) == Some{bk} : Maybe<&2, List<&2, Source.Def>>}:
  %MP.Nat.add_zero(Front.Front.fuel(src)) : {Source.Book.parse(_, src) == Some{bk} : Maybe<&2, List<&2, Source.Def>>}
  FrS.parse_above(n, 0n, src, bk, h)


# Programs
# ========

# the program Oom gives Out.oom
def Oom.run(+p: Nat, +pages: Nat, +input: Maybe<&2, List<&2, Nat>>, +hf: {Wasm.Wasm.fits(pages, input) == True{} : Bool}) ->
  {Imp.Imp.run(pages, 1n+p, C.Oom(), input) == Some{[255n]} : Maybe<&2, List<&2, Nat>>}:
  +size = Wasm.Wasm.size(pages)
  +mem = Wasm.Input.mem(input)
  +hs5 = RP.Size.five(pages, RP.Wf.pages(pages, input, hf), RP.Wf.nz(pages, input, hf))
  %Equal.sym(Bool, Wasm.Wasm.fits(pages, input), True{}, hf) :
    {Imp.Imp.run.of(_, 1n+p, size, C.Oom(), input) == Some{[255n]} : Maybe<&2, List<&2, Nat>>}
  %Equal.sym(Maybe<&2, Imp.Res>, Imp.Stm.run(RT.S.oom(0n), p, size, Wasm.Locals.zero(18n), mem),
    Some{Imp.Res.brk{0n, Wasm.Locals.zero(18n), RP.Oom.mem(mem)}},
    RP.R.oom(0n, p, size, Wasm.Locals.zero(18n), mem, Wasm.Locals.zero(18n), hs5, {==})) :
    {Wasm.Halted.output(Imp.Prog.ret(Imp.Res.loop(_, x => y => Imp.Stm.run(Imp.Stm.loop{RT.S.oom(0n)}, p, size, x, y)),
      RT.E.l(8n), size), size) == Some{[255n]} : Maybe<&2, List<&2, Nat>>}
  RP.Oom.out(mem, size, hs5)

def Oom.zero(+pages: Nat, +input: Maybe<&2, List<&2, Nat>>, +hf: {Wasm.Wasm.fits(pages, input) == True{} : Bool}) ->
  {Imp.Imp.run(pages, 0n, C.Oom(), input) == None{} : Maybe<&2, List<&2, Nat>>}:
  %Equal.sym(Bool, Wasm.Wasm.fits(pages, input), True{}, hf) :
    {Imp.Imp.run.of(_, 0n, Wasm.Wasm.size(pages), C.Oom(), input) == None{} : Maybe<&2, List<&2, Nat>>}
  {==}

# each output of the program Oom is Out.oom
def Oom.only(n: Nat, +pages: Nat, +input: Maybe<&2, List<&2, Nat>>, +hf: {Wasm.Wasm.fits(pages, input) == True{} : Bool},
  -x: List<&2, Nat>, h: {Imp.Imp.run(pages, n, C.Oom(), input) == Some{x} : Maybe<&2, List<&2, Nat>>}) ->
  {x == [255n] : List<&2, Nat>}:
  match n:
    case 0n:
      Empty.absurd({x == [255n] : List<&2, Nat>}, Shared.Maybe.no_none(List<&2, Nat>, x,
        Equal.trans(Maybe<&2, List<&2, Nat>>, None{}, Imp.Imp.run(pages, 0n, C.Oom(), input), Some{x},
          Equal.sym(Maybe<&2, List<&2, Nat>>, Imp.Imp.run(pages, 0n, C.Oom(), input), None{}, Oom.zero(pages, input, hf)), h)))
    case 1n++p:
      Equal.sym(List<&2, Nat>, [255n], x, Bytes.inj([255n], x,
        Equal.trans(Maybe<&2, List<&2, Nat>>, Some{[255n]}, Imp.Imp.run(pages, 1n+p, C.Oom(), input), Some{x},
          Equal.sym(Maybe<&2, List<&2, Nat>>, Imp.Imp.run(pages, 1n+p, C.Oom(), input), Some{[255n]}, Oom.run(p, pages, input, hf)), h)))

# the program Trap gives no output
def Trap.none(n: Nat, +pages: Nat, +input: Maybe<&2, List<&2, Nat>>, +hf: {Wasm.Wasm.fits(pages, input) == True{} : Bool}) ->
  {Imp.Imp.run(pages, n, C.Trap(), input) == None{} : Maybe<&2, List<&2, Nat>>}:
  %Equal.sym(Bool, Wasm.Wasm.fits(pages, input), True{}, hf) :
    {Imp.Imp.run.of(_, n, Wasm.Wasm.size(pages), C.Trap(), input) == None{} : Maybe<&2, List<&2, Nat>>}
  {==}

# Outputs
# =======

# a module keeps what its program keeps
def K.imp(r: Maybe<&2, Source.Obs>, m: Maybe<&2, List<&2, Nat>>, +p: Imp.Prog, +F: Nat, +pages: Nat,
  +input: Maybe<&2, List<&2, Nat>>, hm: {Imp.Imp.run(pages, F, p, input) == m : Maybe<&2, List<&2, Nat>>},
  h: {Spec.Out.keeps(True{}, r, m) == True{} : Bool}) ->
  {Spec.Out.keeps(True{}, r, Wasm.Wasm.run(pages, IS.fuel_out(p, pages, input, F), Imp.Imp.compile(p), input)) == True{} : Bool}:
  match r m:
    case None{} _:
      {==}
    case Some{+o} Some{+y}:
      %Equal.sym(Maybe<&2, List<&2, Nat>>, Wasm.Wasm.run(pages, IS.fuel_out(p, pages, input, F), Imp.Imp.compile(p), input), Some{y},
        IS.compile_keeps(p, pages, input, F, y, hm)) :
        {Spec.Out.keeps(True{}, Some{o}, _) == True{} : Bool}
      h
    case Some{+o} None{}:
      Shared.Bool.absurd({Spec.Out.keeps(True{}, Some{o}, Wasm.Wasm.run(pages, IS.fuel_out(p, pages, input, F), Imp.Imp.compile(p), input)) == True{} : Bool}, h)

# the output of the run time is the output of the contract
def Is.keeps(m: Maybe<&2, List<&2, Nat>>, +o: Source.Obs, h: {RS.Out.is(m, Spec.Out.of(o)) == True{} : Bool}) ->
  {Spec.Out.keeps(True{}, Some{o}, m) == True{} : Bool}:
  match m:
    case Some{+y}:
      %Bytes.name(y, Spec.Out.of(o)) : {Bool.or(_, Source.Name.is_eq(y, Spec.Out.oom())) == True{} : Bool}
      %Bytes.name(y, [255n]) : {Bool.or(RS.Bytes.is_eq(y, Spec.Out.of(o)), _) == True{} : Bool}
      h
    case None{}:
      Shared.Bool.absurd({Spec.Out.keeps(True{}, Some{o}, None{}) == True{} : Bool}, h)

# Out.oom keeps each result
def Keep.oom(r: Maybe<&2, Source.Obs>) -> {Spec.Out.keeps(True{}, r, Some{[255n]}) == True{} : Bool}:
  match r:
    case None{}:
      {==}
    case Some{+o}:
      Or.t(Source.Name.is_eq([255n], Spec.Out.of(o)))

# Out.oom adds no result
def Adds.oom(r: Maybe<&2, Source.Obs>, -x: List<&2, Nat>, hx: {x == [255n] : List<&2, Nat>}) ->
  {Spec.Out.adds_none(True{}, Some{x}, r) == True{} : Bool}:
  match r:
    case None{}:
      %Equal.sym(List<&2, Nat>, x, [255n], hx) : {Spec.Out.adds_none(True{}, Some{_}, None{}) == True{} : Bool}
      {==}
    case Some{+o}:
      %Equal.sym(List<&2, Nat>, x, [255n], hx) : {Spec.Out.adds_none(True{}, Some{_}, Some{o}) == True{} : Bool}
      Or.t(Source.Name.is_eq([255n], Spec.Out.of(o)))

# Fuel
# ====
#
# The proofs take the F program as a parameter prog, with prog ==
# Code.prog(): the laws give Code.prog(). So no proof unfolds the image of the
# F program.

# the machine's fuel for the source's fuel n, on the entry e
def Fuel.m(e: Maybe<&2, Source.Entry>, n: Nat) -> Nat:
  match e:
    case Some{Source.Entry{bk, k}}:
      MS.fuel_m(bk, k, n)
    case None{}:
      0n

# the steps of F that the law keeps of the machine in F gives, for the
# machine's fuel m, when the machine has a result and the input is bytes
def Fuel.f.of(+bk: List<&2, Source.Def>, +input: Maybe<&2, List<&2, Nat>>, +m: Nat,
  r: Maybe<&2, Fun.V>, hr: {FMS.Res(FMS.Run.at(m, Source.entry(input, bk))) == r : Maybe<&2, Fun.V>}, b: Bool,
  hb: {FMS.Input.ok(input, 255n) == b : Bool}) -> Nat:
  match r b:
    case Some{+w} True{}:
      Reach.n(Code.prog(), Fun.Step.go{FM.start.of(bk, input, 255n)}, Fun.Step.halt{w}, FMS.keeps(bk, input, m, 255n, w, hb, hr))
    case _ _:
      0n

def Fuel.f(+bk: List<&2, Source.Def>, +input: Maybe<&2, List<&2, Nat>>, +m: Nat) -> Nat:
  Fuel.f.of(bk, input, m, FMS.Res(FMS.Run.at(m, Source.entry(input, bk))), {==}, FMS.Input.ok(input, 255n), {==})

# the fuel of the run time on the book bk, for the source's fuel n
def Fuel.rt(+prog: List<&2, Fun.C>, +bk: List<&2, Source.Def>, +input: Maybe<&2, List<&2, Nat>>, +n: Nat) -> Nat:
  RS.fuel(prog, Code.F.Main(), FM.Enc.book(bk), C.Tail(bk), input, Fuel.f(bk, input, Fuel.m(Source.entry(input, bk), n)), [])

def Fuel.book(+prog: List<&2, Fun.C>, +bk: List<&2, Source.Def>, +input: Maybe<&2, List<&2, Nat>>, +n: Nat) -> Nat:
  Bool.pick(Nat, RT.fits(prog, FM.Enc.book(bk), C.Tail(bk)), Fuel.rt(prog, bk, input, n), 1n)

def Fuel.out(+prog: List<&2, Fun.C>, m: Maybe<&2, List<&2, Source.Def>>, +input: Maybe<&2, List<&2, Nat>>,
  +pages: Nat, +n: Nat) -> Nat:
  match m:
    case Some{+bk}:
      IS.fuel_out(C.Prog.book(prog, bk), pages, input, Fuel.book(prog, bk, input, n))
    case None{}:
      0n

# Keeps
# =====

# the fuel of the run time does not read the output
def Fuel.bs(+prog: List<&2, Fun.C>, +c: Fun.C, +head: Fun.V, +tail: List<&2, Fun.V>, +input: Maybe<&2, List<&2, Nat>>,
  +n: Nat, +bs: List<&2, Nat>) -> {RS.fuel(prog, c, head, tail, input, n, bs) == RS.fuel(prog, c, head, tail, input, n, []) : Nat}:
  {==}

# the run time keeps the machine's result r, by the law keeps of the machine
# in F
def K.f(+prog: List<&2, Fun.C>, +bk: List<&2, Source.Def>, +input: Maybe<&2, List<&2, Nat>>, +pages: Nat,
  +M: Nat, +o: Source.Obs, r: Maybe<&2, Fun.V>,
  +hr: {FMS.Res(FMS.Run.at(M, Source.entry(input, bk))) == r : Maybe<&2, Fun.V>}, b: Bool,
  +hb: {FMS.Input.ok(input, 255n) == b : Bool},
  hro: {r == Some{FM.Enc.name(Spec.Out.of(o))} : Maybe<&2, Fun.V>}, hbt: {b == True{} : Bool},
  +hp: {prog == Code.prog() : List<&2, Fun.C>},
  +he: {List.get(&2, Fun.C, prog, 51n) == Some{Code.F.Main()} : Maybe<&2, Fun.C>},
  +hf: {Wasm.Wasm.fits(pages, input) == True{} : Bool},
  +hi: {RT.fits(prog, FM.Enc.book(bk), C.Tail(bk)) == True{} : Bool}) ->
  {Spec.Out.keeps(True{}, Some{o}, Imp.Imp.run(pages, RS.fuel(prog, Code.F.Main(), FM.Enc.book(bk), C.Tail(bk), input,
    Fuel.f.of(bk, input, M, r, hr, b, hb), []), RT.RT(prog, 51n, FM.Enc.book(bk), C.Tail(bk)), input)) == True{} : Bool}:
  match r b:
    case Some{+w} True{}:
      +bs = Spec.Out.of(o)
      +nF = Reach.n(Code.prog(), Fun.Step.go{FM.start.of(bk, input, 255n)}, Fun.Step.halt{w}, FMS.keeps(bk, input, M, 255n, w, hb, hr))
      +h0 = MP.Eq.rw(List<&2, Fun.C>, Code.prog(), prog, Equal.sym(List<&2, Fun.C>, prog, Code.prog(), hp),
        q => {Fun.F.iter(nF, q, Fun.Step.go{FM.start.of(bk, input, 255n)}) == Fun.Step.halt{w} : Fun.Step},
        Reach.at(Code.prog(), Fun.Step.go{FM.start.of(bk, input, 255n)}, Fun.Step.halt{w}, FMS.keeps(bk, input, M, 255n, w, hb, hr)))
      +h = MP.Eq.rw(Fun.S, FM.start.of(bk, input, 255n), RS.Start(Code.F.Main(), FM.Enc.book(bk), input, C.Tail(bk)), Start.eq(bk, input),
        s => {Fun.F.iter(nF, prog, Fun.Step.go{s}) == Fun.Step.halt{w} : Fun.Step}, h0)
      +hd = MP.Eq.rw(Fun.V, FM.Enc.name(bs), w, Equal.sym(Fun.V, w, FM.Enc.name(bs), V.inj(w, FM.Enc.name(bs), hro)),
        v => {RS.Out.dec(v) == Some{bs} : Maybe<&2, List<&2, Nat>>}, Name.dec(bs))
      %Fuel.bs(prog, Code.F.Main(), FM.Enc.book(bk), C.Tail(bk), input, nF, bs) :
        {Spec.Out.keeps(True{}, Some{o}, Imp.Imp.run(pages, _, RT.RT(prog, 51n, FM.Enc.book(bk), C.Tail(bk)), input)) == True{} : Bool}
      Is.keeps(Imp.Imp.run(pages, RS.fuel(prog, Code.F.Main(), FM.Enc.book(bk), C.Tail(bk), input, nF, bs),
        RT.RT(prog, 51n, FM.Enc.book(bk), C.Tail(bk)), input), o,
        RS.keeps(prog, 51n, Code.F.Main(), FM.Enc.book(bk), C.Tail(bk), pages, input, nF, w, bs, he, hi, hf, h, hd))
    case Some{+w} False{}:
      Shared.Bool.absurd({Spec.Out.keeps(True{}, Some{o}, Imp.Imp.run(pages, RS.fuel(prog, Code.F.Main(), FM.Enc.book(bk), C.Tail(bk), input,
        Fuel.f.of(bk, input, M, Some{w}, hr, False{}, hb), []), RT.RT(prog, 51n, FM.Enc.book(bk), C.Tail(bk)), input)) == True{} : Bool}, hbt)
    case None{} _:
      Empty.absurd({Spec.Out.keeps(True{}, Some{o}, Imp.Imp.run(pages, RS.fuel(prog, Code.F.Main(), FM.Enc.book(bk), C.Tail(bk), input,
        Fuel.f.of(bk, input, M, None{}, hr, b, hb), []), RT.RT(prog, 51n, FM.Enc.book(bk), C.Tail(bk)), input)) == True{} : Bool},
        Shared.Maybe.no_none(Fun.V, FM.Enc.name(Spec.Out.of(o)), hro))

# the machine in F gives the encoding of the machine's result
def Res.at(+bk: List<&2, Source.Def>, +input: Maybe<&2, List<&2, Nat>>, +M: Nat, +bk2: List<&2, Source.Def>,
  +k: List<&2, Nat>, +o: Source.Obs,
  he: {Source.entry(input, bk) == Some{Source.Entry{bk2, k}} : Maybe<&2, Source.Entry>},
  hms: {Machine.Machine.start(M, bk2, k) == Some{o} : Maybe<&2, Source.Obs>}) ->
  {FMS.Res(FMS.Run.at(M, Source.entry(input, bk))) == Some{FM.Enc.name(Spec.Out.of(o))} : Maybe<&2, Fun.V>}:
  %Equal.sym(Maybe<&2, Source.Entry>, Source.entry(input, bk), Some{Source.Entry{bk2, k}}, he) :
    {FMS.Res(FMS.Run.at(M, _)) == Some{FM.Enc.name(Spec.Out.of(o))} : Maybe<&2, Fun.V>}
  %Equal.sym(Maybe<&2, Source.Obs>, Machine.Machine.start(M, bk2, k), Some{o}, hms) :
    {FMS.Res(_) == Some{FM.Enc.name(Spec.Out.of(o))} : Maybe<&2, Fun.V>}
  {==}

# the run time keeps the source's result mo, by the law keeps of the machine
def K.obs(mo: Maybe<&2, Source.Obs>, +prog: List<&2, Fun.C>, +bk: List<&2, Source.Def>, +bk2: List<&2, Source.Def>,
  +k: List<&2, Nat>, +input: Maybe<&2, List<&2, Nat>>, +pages: Nat, +n: Nat,
  hmo: {Source.Maybe.observe(Source.Term.run(n, Source.Term.Ref{k}, bk2)) == mo : Maybe<&2, Source.Obs>},
  +hen: {Source.entry(input, bk) == Some{Source.Entry{bk2, k}} : Maybe<&2, Source.Entry>},
  +hp: {prog == Code.prog() : List<&2, Fun.C>},
  +he: {List.get(&2, Fun.C, prog, 51n) == Some{Code.F.Main()} : Maybe<&2, Fun.C>},
  +hf: {Wasm.Wasm.fits(pages, input) == True{} : Bool},
  +hi: {RT.fits(prog, FM.Enc.book(bk), C.Tail(bk)) == True{} : Bool}) ->
  {Spec.Out.keeps(True{}, mo, Imp.Imp.run(pages, RS.fuel(prog, Code.F.Main(), FM.Enc.book(bk), C.Tail(bk), input,
    Fuel.f(bk, input, MS.fuel_m(bk2, k, n)), []), RT.RT(prog, 51n, FM.Enc.book(bk), C.Tail(bk)), input)) == True{} : Bool}:
  match mo:
    case None{}:
      {==}
    case Some{+o}:
      +M = MS.fuel_m(bk2, k, n)
      +hms = Kept.some(Machine.Machine.start(M, bk2, k), o,
        MP.Eq.rw(Maybe<&2, Source.Obs>, Source.Maybe.observe(Source.Term.run(n, Source.Term.Ref{k}, bk2)), Some{o}, hmo,
          z => {Source.Obs.is_kept(z, Machine.Machine.start(M, bk2, k)) == True{} : Bool}, MS.keeps(bk2, k, n)))
      K.f(prog, bk, input, pages, M, o, FMS.Res(FMS.Run.at(M, Source.entry(input, bk))), {==}, FMS.Input.ok(input, 255n), {==},
        Res.at(bk, input, M, bk2, k, o, hen, hms), Fits.ok(pages, input, hf), hp, he, hf, hi)

def K.entry(e: Maybe<&2, Source.Entry>, +prog: List<&2, Fun.C>, +bk: List<&2, Source.Def>,
  +input: Maybe<&2, List<&2, Nat>>, +pages: Nat, +n: Nat,
  hen: {Source.entry(input, bk) == e : Maybe<&2, Source.Entry>},
  +hp: {prog == Code.prog() : List<&2, Fun.C>},
  +he: {List.get(&2, Fun.C, prog, 51n) == Some{Code.F.Main()} : Maybe<&2, Fun.C>},
  +hf: {Wasm.Wasm.fits(pages, input) == True{} : Bool},
  +hi: {RT.fits(prog, FM.Enc.book(bk), C.Tail(bk)) == True{} : Bool}) ->
  {Spec.Out.keeps(True{}, Source.run.at(n, e), Imp.Imp.run(pages, RS.fuel(prog, Code.F.Main(), FM.Enc.book(bk), C.Tail(bk), input,
    Fuel.f(bk, input, Fuel.m(e, n)), []), RT.RT(prog, 51n, FM.Enc.book(bk), C.Tail(bk)), input)) == True{} : Bool}:
  match e:
    case None{}:
      {==}
    case Some{Source.Entry{+bk2, +k}}:
      K.obs(Source.Maybe.observe(Source.Term.run(n, Source.Term.Ref{k}, bk2)), prog, bk, bk2, k, input, pages, n, {==}, hen, hp, he, hf, hi)

# the program of the book bk keeps the result: the run time, or Oom when the
# image does not fit
def K.book(fi: Bool, +prog: List<&2, Fun.C>, +bk: List<&2, Source.Def>, +input: Maybe<&2, List<&2, Nat>>,
  +pages: Nat, +n: Nat,
  hfi: {RT.fits(prog, FM.Enc.book(bk), C.Tail(bk)) == fi : Bool},
  +hp: {prog == Code.prog() : List<&2, Fun.C>},
  +he: {List.get(&2, Fun.C, prog, 51n) == Some{Code.F.Main()} : Maybe<&2, Fun.C>},
  +hf: {Wasm.Wasm.fits(pages, input) == True{} : Bool}) ->
  {Spec.Out.keeps(True{}, Source.run.at(n, Source.entry(input, bk)), Imp.Imp.run(pages, Bool.pick(Nat, fi, Fuel.rt(prog, bk, input, n), 1n),
    Bool.pick(Imp.Prog, fi, RT.RT(prog, 51n, FM.Enc.book(bk), C.Tail(bk)), C.Oom()), input)) == True{} : Bool}:
  match fi:
    case True{}:
      K.entry(Source.entry(input, bk), prog, bk, input, pages, n, {==}, hp, he, hf, hfi)
    case False{}:
      %Equal.sym(Maybe<&2, List<&2, Nat>>, Imp.Imp.run(pages, 1n, C.Oom(), input), Some{[255n]}, Oom.run(0n, pages, input, hf)) :
        {Spec.Out.keeps(True{}, Source.run.at(n, Source.entry(input, bk)), _) == True{} : Bool}
      Keep.oom(Source.run.at(n, Source.entry(input, bk)))

# the module keeps the result of each parse
def K.parse(mb: Maybe<&2, List<&2, Source.Def>>, +prog: List<&2, Fun.C>, +src: List<&2, Nat>,
  +input: Maybe<&2, List<&2, Nat>>, +pages: Nat, +n: Nat,
  hmb: {Source.Book.parse(n, src) == mb : Maybe<&2, List<&2, Source.Def>>},
  +hp: {prog == Code.prog() : List<&2, Fun.C>},
  +he: {List.get(&2, Fun.C, prog, 51n) == Some{Code.F.Main()} : Maybe<&2, Fun.C>},
  +hf: {Wasm.Wasm.fits(pages, input) == True{} : Bool}) ->
  {Spec.Out.keeps(True{}, Source.run.of(n, input, mb), Wasm.Wasm.run(pages, Fuel.out(prog, Front.Front.book(src), input, pages, n),
    Imp.Imp.compile(C.Prog.of(prog, Front.Front.book(src))), input)) == True{} : Bool}:
  match mb:
    case None{}:
      {==}
    case Some{+bk}:
      %Equal.sym(Maybe<&2, List<&2, Source.Def>>, Front.Front.book(src), Some{bk}, Book.ok(n, src, bk, hmb)) :
        {Spec.Out.keeps(True{}, Source.run.of(n, input, Some{bk}), Wasm.Wasm.run(pages, Fuel.out(prog, _, input, pages, n),
          Imp.Imp.compile(C.Prog.of(prog, _)), input)) == True{} : Bool}
      K.imp(Source.run.at(n, Source.entry(input, bk)), Imp.Imp.run(pages, Fuel.book(prog, bk, input, n), C.Prog.book(prog, bk), input),
        C.Prog.book(prog, bk), Fuel.book(prog, bk, input, n), pages, input, {==},
        K.book(RT.fits(prog, FM.Enc.book(bk), C.Tail(bk)), prog, bk, input, pages, n, {==}, hp, he, hf))

# the law keeps_results, for the program prog
def K.fits(ok: Bool, +prog: List<&2, Fun.C>, +src: List<&2, Nat>, +input: Maybe<&2, List<&2, Nat>>, +pages: Nat,
  +n: Nat, hok: {Spec.Out.fits(src, pages, input) == ok : Bool}, +hp: {prog == Code.prog() : List<&2, Fun.C>},
  +he: {List.get(&2, Fun.C, prog, 51n) == Some{Code.F.Main()} : Maybe<&2, Fun.C>}) ->
  {Spec.Out.keeps(ok, Source.run(n, src, input), Wasm.Wasm.run(pages, Fuel.out(prog, Front.Front.book(src), input, pages, n),
    Imp.Imp.compile(C.Prog.of(prog, Front.Front.book(src))), input)) == True{} : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      K.parse(Source.Book.parse(n, src), prog, src, input, pages, n, {==}, hp, he,
        RP.And.r(Wasm.Bytes.is(src), Wasm.Wasm.fits(pages, input), hok))

# Adds none
# =========

# the source's run, with the fuel fuel_src, gives the result o of the machine
def A.entry(e: Maybe<&2, Source.Entry>, +src: List<&2, Nat>, +bk: List<&2, Source.Def>, +input: Maybe<&2, List<&2, Nat>>, +n: Nat, +o: Source.Obs, -x: List<&2, Nat>,
  hen: {Source.entry(input, bk) == e : Maybe<&2, Source.Entry>},
  hro: {FMS.Run.at(n, e) == Some{o} : Maybe<&2, Source.Obs>},
  hx: {x == Spec.Out.of(o) : List<&2, Nat>},
  +hfb: {Front.Front.book(src) == Some{bk} : Maybe<&2, List<&2, Source.Def>>}) ->
  {Spec.Out.adds_none(True{}, Some{x}, Source.run(Nat.add(Front.Front.fuel(src), 1n+n), src, input)) == True{} : Bool}:
  match e:
    case None{}:
      Empty.absurd({Spec.Out.adds_none(True{}, Some{x}, Source.run(Nat.add(Front.Front.fuel(src), 1n+n), src, input)) == True{} : Bool}, Shared.Maybe.no_none(Source.Obs, o, hro))
    case Some{Source.Entry{+bk2, +k}}:
      +N = Nat.add(Front.Front.fuel(src), 1n+n)
      +hob = Kept.some(Source.Maybe.observe(Source.Term.run(1n+n, Source.Term.Ref{k}, bk2)), o,
        MP.Eq.rw(Maybe<&2, Source.Obs>, Machine.Machine.start(n, bk2, k), Some{o}, hro,
          z => {Source.Obs.is_kept(z, Source.Maybe.observe(Source.Term.run(1n+n, Source.Term.Ref{k}, bk2))) == True{} : Bool},
          MS.adds_none(bk2, k, n)))
      +hmore = Obs.more(Front.Front.fuel(src), Source.Term.Ref{k}, 1n+n, bk2, o, hob)
      %Equal.sym(Maybe<&2, List<&2, Source.Def>>, Source.Book.parse(N, src), Some{bk},
        FrS.parse_above(Front.Front.fuel(src), 1n+n, src, bk, hfb)) :
        {Spec.Out.adds_none(True{}, Some{x}, Source.run.of(N, input, _)) == True{} : Bool}
      %Equal.sym(Maybe<&2, Source.Entry>, Source.entry(input, bk), Some{Source.Entry{bk2, k}}, hen) :
        {Spec.Out.adds_none(True{}, Some{x}, Source.run.at(N, _)) == True{} : Bool}
      %Equal.sym(Maybe<&2, Source.Obs>, Source.Maybe.observe(Source.Term.run(N, Source.Term.Ref{k}, bk2)), Some{o}, hmore) :
        {Spec.Out.adds_none(True{}, Some{x}, _) == True{} : Bool}
      %Equal.sym(List<&2, Nat>, x, Spec.Out.of(o), hx) :
        {Spec.Out.is(_, o) == True{} : Bool}
      %Equal.sym(Bool, Source.Name.is_eq(Spec.Out.of(o), Spec.Out.of(o)), True{}, SP.Name.is_eq_self(Spec.Out.of(o))) :
        {Bool.or(_, Source.Name.is_eq(Spec.Out.of(o), Spec.Out.oom())) == True{} : Bool}
      {==}

# an output w of the machine in F is the encoding of the machine's result
def A.res(ro: Maybe<&2, Source.Obs>, +src: List<&2, Nat>, +bk: List<&2, Source.Def>, +input: Maybe<&2, List<&2, Nat>>, +n: Nat, -w: Fun.V, -x: List<&2, Nat>,
  hro: {FMS.Run.at(n, Source.entry(input, bk)) == ro : Maybe<&2, Source.Obs>},
  hres: {FMS.Res(ro) == Some{w} : Maybe<&2, Fun.V>},
  hd: {RS.Out.dec(w) == Some{x} : Maybe<&2, List<&2, Nat>>},
  +hfb: {Front.Front.book(src) == Some{bk} : Maybe<&2, List<&2, Source.Def>>}) ->
  {Spec.Out.adds_none(True{}, Some{x}, Source.run(Nat.add(Front.Front.fuel(src), 1n+n), src, input)) == True{} : Bool}:
  match ro:
    case None{}:
      Empty.absurd({Spec.Out.adds_none(True{}, Some{x}, Source.run(Nat.add(Front.Front.fuel(src), 1n+n), src, input)) == True{} : Bool}, Shared.Maybe.no_none(Fun.V, w, hres))
    case Some{+o}:
      +hw = V.inj(FM.Enc.name(Spec.Out.of(o)), w, hres)
      +hdx = MP.Eq.rw(Fun.V, w, FM.Enc.name(Spec.Out.of(o)), Equal.sym(Fun.V, FM.Enc.name(Spec.Out.of(o)), w, hw),
        v => {RS.Out.dec(v) == Some{x} : Maybe<&2, List<&2, Nat>>}, hd)
      +hx = Equal.sym(List<&2, Nat>, Spec.Out.of(o), x, Bytes.inj(Spec.Out.of(o), x,
        Equal.trans(Maybe<&2, List<&2, Nat>>, Some{Spec.Out.of(o)}, RS.Out.dec(FM.Enc.name(Spec.Out.of(o))), Some{x},
          Equal.sym(Maybe<&2, List<&2, Nat>>, RS.Out.dec(FM.Enc.name(Spec.Out.of(o))), Some{Spec.Out.of(o)}, Name.dec(Spec.Out.of(o))), hdx)))
      A.entry(Source.entry(input, bk), src, bk, input, n, o, x, {==}, hro, hx, hfb)

# an end of the F program is the output of the machine's result
def A.f(mf: Maybe<&2, Fun.V>, +src: List<&2, Nat>, +bk: List<&2, Source.Def>, +input: Maybe<&2, List<&2, Nat>>, +pages: Nat, +n: Nat, -x: List<&2, Nat>,
  hmf: {Fun.F.run(n, Code.prog(), FM.start.of(bk, input, 255n)) == mf : Maybe<&2, Fun.V>},
  hd: {RS.Out.dec.of(mf) == Some{x} : Maybe<&2, List<&2, Nat>>},
  +hf: {Wasm.Wasm.fits(pages, input) == True{} : Bool}, +hfb: {Front.Front.book(src) == Some{bk} : Maybe<&2, List<&2, Source.Def>>}) ->
  {Spec.Out.adds_none(True{}, Some{x}, Source.run(Nat.add(Front.Front.fuel(src), 1n+n), src, input)) == True{} : Bool}:
  match mf:
    case None{}:
      Empty.absurd({Spec.Out.adds_none(True{}, Some{x}, Source.run(Nat.add(Front.Front.fuel(src), 1n+n), src, input)) == True{} : Bool}, Shared.Maybe.no_none(List<&2, Nat>, x, hd))
    case Some{+w}:
      A.res(FMS.Run.at(n, Source.entry(input, bk)), src, bk, input, n, w, x, {==},
        FMS.adds_none(bk, input, n, 255n, w, Fits.ok(pages, input, hf), hmf), hd, hfb)

# an output x of the run time is Out.oom, or an end of the F program
def A.x(bx: Bool, +prog: List<&2, Fun.C>, +src: List<&2, Nat>, +bk: List<&2, Source.Def>, +input: Maybe<&2, List<&2, Nat>>, +pages: Nat, +n: Nat, +x: List<&2, Nat>,
  hbx: {RS.Bytes.is_eq(x, [255n]) == bx : Bool},
  hi: {Imp.Imp.run(pages, n, RT.RT(prog, 51n, FM.Enc.book(bk), C.Tail(bk)), input) == Some{x} : Maybe<&2, List<&2, Nat>>},
  +hp: {prog == Code.prog() : List<&2, Fun.C>}, +he: {List.get(&2, Fun.C, prog, 51n) == Some{Code.F.Main()} : Maybe<&2, Fun.C>},
  +hfit: {RT.fits(prog, FM.Enc.book(bk), C.Tail(bk)) == True{} : Bool},
  +hf: {Wasm.Wasm.fits(pages, input) == True{} : Bool}, +hfb: {Front.Front.book(src) == Some{bk} : Maybe<&2, List<&2, Source.Def>>}) ->
  {Spec.Out.adds_none(True{}, Some{x}, Source.run(Nat.add(Front.Front.fuel(src), 1n+n), src, input)) == True{} : Bool}:
  match bx:
    case True{}:
      Adds.oom(Source.run(Nat.add(Front.Front.fuel(src), 1n+n), src, input), x, RP.Bytes.eq(x, [255n], hbx))
    case False{}:
      +h1 = RS.adds_none(prog, 51n, Code.F.Main(), FM.Enc.book(bk), C.Tail(bk), pages, input, n, x, he, hfit, hi, hbx)
      +h2 = MP.Eq.rw(Fun.S, RS.Start(Code.F.Main(), FM.Enc.book(bk), input, C.Tail(bk)), FM.start.of(bk, input, 255n),
        Equal.sym(Fun.S, FM.start.of(bk, input, 255n), RS.Start(Code.F.Main(), FM.Enc.book(bk), input, C.Tail(bk)), Start.eq(bk, input)),
        s => {RS.Out.dec.of(Fun.F.run(n, prog, s)) == Some{x} : Maybe<&2, List<&2, Nat>>}, h1)
      +h3 = MP.Eq.rw(List<&2, Fun.C>, prog, Code.prog(), hp,
        q => {RS.Out.dec.of(Fun.F.run(n, q, FM.start.of(bk, input, 255n))) == Some{x} : Maybe<&2, List<&2, Nat>>}, h2)
      A.f(Fun.F.run(n, Code.prog(), FM.start.of(bk, input, 255n)), src, bk, input, pages, n, x, {==}, h3, hf, hfb)

# an output x of the program of the book bk
def A.rt(fi: Bool, +prog: List<&2, Fun.C>, +src: List<&2, Nat>, +bk: List<&2, Source.Def>, +input: Maybe<&2, List<&2, Nat>>, +pages: Nat, +n: Nat, +x: List<&2, Nat>,
  hfi: {RT.fits(prog, FM.Enc.book(bk), C.Tail(bk)) == fi : Bool},
  hi: {Imp.Imp.run(pages, n, Bool.pick(Imp.Prog, fi, RT.RT(prog, 51n, FM.Enc.book(bk), C.Tail(bk)), C.Oom()), input) == Some{x} : Maybe<&2, List<&2, Nat>>},
  +hp: {prog == Code.prog() : List<&2, Fun.C>}, +he: {List.get(&2, Fun.C, prog, 51n) == Some{Code.F.Main()} : Maybe<&2, Fun.C>}, +hf: {Wasm.Wasm.fits(pages, input) == True{} : Bool}, +hfb: {Front.Front.book(src) == Some{bk} : Maybe<&2, List<&2, Source.Def>>}) ->
  {Spec.Out.adds_none(True{}, Some{x}, Source.run(Nat.add(Front.Front.fuel(src), 1n+n), src, input)) == True{} : Bool}:
  match fi:
    case True{}:
      A.x(RS.Bytes.is_eq(x, [255n]), prog, src, bk, input, pages, n, x, {==}, hi, hp, he, hfi, hf, hfb)
    case False{}:
      Adds.oom(Source.run(Nat.add(Front.Front.fuel(src), 1n+n), src, input), x, Oom.only(n, pages, input, hf, x, hi))

# an output x of the program of the parse
def A.book(fb: Maybe<&2, List<&2, Source.Def>>, +prog: List<&2, Fun.C>, +src: List<&2, Nat>, +input: Maybe<&2, List<&2, Nat>>, +pages: Nat, +n: Nat, +x: List<&2, Nat>,
  hfb: {Front.Front.book(src) == fb : Maybe<&2, List<&2, Source.Def>>},
  hi: {Imp.Imp.run(pages, n, C.Prog.of(prog, fb), input) == Some{x} : Maybe<&2, List<&2, Nat>>},
  +hp: {prog == Code.prog() : List<&2, Fun.C>}, +he: {List.get(&2, Fun.C, prog, 51n) == Some{Code.F.Main()} : Maybe<&2, Fun.C>}, +hf: {Wasm.Wasm.fits(pages, input) == True{} : Bool}) ->
  {Spec.Out.adds_none(True{}, Some{x}, Source.run(Nat.add(Front.Front.fuel(src), 1n+n), src, input)) == True{} : Bool}:
  match fb:
    case None{}:
      Empty.absurd({Spec.Out.adds_none(True{}, Some{x}, Source.run(Nat.add(Front.Front.fuel(src), 1n+n), src, input)) == True{} : Bool}, Shared.Maybe.no_none(List<&2, Nat>, x,
        Equal.trans(Maybe<&2, List<&2, Nat>>, None{}, Imp.Imp.run(pages, n, C.Trap(), input), Some{x},
          Equal.sym(Maybe<&2, List<&2, Nat>>, Imp.Imp.run(pages, n, C.Trap(), input), None{}, Trap.none(n, pages, input, hf)), hi)))
    case Some{+bk}:
      A.rt(RT.fits(prog, FM.Enc.book(bk), C.Tail(bk)), prog, src, bk, input, pages, n, x, {==}, hi, hp, he, hf, hfb)

def A.out(mw: Maybe<&2, List<&2, Nat>>, +prog: List<&2, Fun.C>, +src: List<&2, Nat>, +input: Maybe<&2, List<&2, Nat>>, +pages: Nat, +n: Nat,
  hmw: {Wasm.Wasm.run(pages, n, Imp.Imp.compile(C.Prog.of(prog, Front.Front.book(src))), input) == mw : Maybe<&2, List<&2, Nat>>},
  +hp: {prog == Code.prog() : List<&2, Fun.C>}, +he: {List.get(&2, Fun.C, prog, 51n) == Some{Code.F.Main()} : Maybe<&2, Fun.C>}, +hf: {Wasm.Wasm.fits(pages, input) == True{} : Bool}) ->
  {Spec.Out.adds_none(True{}, mw, Source.run(Nat.add(Front.Front.fuel(src), 1n+n), src, input)) == True{} : Bool}:
  match mw:
    case None{}:
      {==}
    case Some{+x}:
      A.book(Front.Front.book(src), prog, src, input, pages, n, x, {==},
        IS.compile_adds_none(C.Prog.of(prog, Front.Front.book(src)), pages, input, n, x, hmw), hp, he, hf)

# the law adds_no_results, for the program prog
def A.fits(ok: Bool, +prog: List<&2, Fun.C>, +src: List<&2, Nat>, +input: Maybe<&2, List<&2, Nat>>, +pages: Nat, +n: Nat,
  hok: {Spec.Out.fits(src, pages, input) == ok : Bool}, +hp: {prog == Code.prog() : List<&2, Fun.C>}, +he: {List.get(&2, Fun.C, prog, 51n) == Some{Code.F.Main()} : Maybe<&2, Fun.C>}) ->
  {Spec.Out.adds_none(ok, Wasm.Wasm.run(pages, n, Imp.Imp.compile(C.Prog.of(prog, Front.Front.book(src))), input),
    Source.run(Nat.add(Front.Front.fuel(src), 1n+n), src, input)) == True{} : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      A.out(Wasm.Wasm.run(pages, n, Imp.Imp.compile(C.Prog.of(prog, Front.Front.book(src))), input), prog, src, input, pages, n, {==}, hp, he,
        RP.And.r(Wasm.Bytes.is(src), Wasm.Wasm.fits(pages, input), hok))

# The laws
# ========

def Spec.compile(src):
  C.compile(src)

def Spec.fuel_out(src, input, pages, n):
  Fuel.out(Code.prog(), Front.Front.book(src), input, pages, n)

def Spec.fuel_src(src, input, pages, n):
  Nat.add(Front.Front.fuel(src), 1n+n)

def Spec.keeps_results(src, input, pages, n):
  +src = src
  +input = input
  +pages = pages
  K.fits(Spec.Out.fits(src, pages, input), Code.prog(), src, input, pages, n, {==}, {==}, {==})

def Spec.adds_no_results(src, input, pages, n):
  +src = src
  +input = input
  +pages = pages
  A.fits(Spec.Out.fits(src, pages, input), Code.prog(), src, input, pages, n, {==}, {==}, {==})
