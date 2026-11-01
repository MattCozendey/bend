# compiler: more fuel keeps an outcome
# ===================================
#
# A run that ends (anything but not_done) with the fuel f ends the same with
# the fuel f + g. A call that ends with some fuel ends the same with more
# fuel, in the same steps, which are at most its fuel; the host gives run the
# steps that alloc left, Nat.sub(f, used), and with f + g it gives
# Nat.sub(f, used) + g, as used <= f.

import Base
import ./impl.bend as C
import ./proof_need.bend as PN

# the outcome ends: anything but not_done
def done(x: C.Wasm.Outcome) -> Bool:
  match x:
    case C.Wasm.Outcome.not_done{}:
      False{}
    case _:
      True{}

# Monotony relations: a ends gives b == a
# ---------------------------------------

def CM(a: C.Wasm.Call, b: C.Wasm.Call) -> Type:
  match a:
    case C.Wasm.Call.done{rs, m, n}:
      {C.Wasm.Call.done{rs, m, n} == b : C.Wasm.Call}
    case C.Wasm.Call.trap{m}:
      {C.Wasm.Call.trap{m} == b : C.Wasm.Call}
    case C.Wasm.Call.not_done{}:
      Unit

# a done call took at most k steps
def CB(k: Nat, a: C.Wasm.Call) -> Type:
  match a:
    case C.Wasm.Call.done{_, _, n}:
      PN.Le(n, k)
    case C.Wasm.Call.trap{_}:
      Unit
    case C.Wasm.Call.not_done{}:
      Unit

def IM(a: C.Wasm.Invoked, b: C.Wasm.Invoked) -> Type:
  match a:
    case C.Wasm.Invoked.values{vs, i, n}:
      {C.Wasm.Invoked.values{vs, i, n} == b : C.Wasm.Invoked}
    case C.Wasm.Invoked.trap{i}:
      {C.Wasm.Invoked.trap{i} == b : C.Wasm.Invoked}
    case C.Wasm.Invoked.not_done{}:
      Unit
    case C.Wasm.Invoked.unsupported{}:
      {C.Wasm.Invoked.unsupported{} == b : C.Wasm.Invoked}

def IB(k: Nat, a: C.Wasm.Invoked) -> Type:
  match a:
    case C.Wasm.Invoked.values{_, _, n}:
      PN.Le(n, k)
    case C.Wasm.Invoked.trap{_}:
      Unit
    case C.Wasm.Invoked.not_done{}:
      Unit
    case C.Wasm.Invoked.unsupported{}:
      Unit

def OM(a: C.Wasm.Outcome, b: C.Wasm.Outcome) -> Type:
  match a:
    case C.Wasm.Outcome.result{bs}:
      {C.Wasm.Outcome.result{bs} == b : C.Wasm.Outcome}
    case C.Wasm.Outcome.out_of_memory{}:
      {C.Wasm.Outcome.out_of_memory{} == b : C.Wasm.Outcome}
    case C.Wasm.Outcome.no_result{}:
      {C.Wasm.Outcome.no_result{} == b : C.Wasm.Outcome}
    case C.Wasm.Outcome.unsupported{}:
      {C.Wasm.Outcome.unsupported{} == b : C.Wasm.Outcome}
    case C.Wasm.Outcome.trap{}:
      {C.Wasm.Outcome.trap{} == b : C.Wasm.Outcome}
    case C.Wasm.Outcome.not_done{}:
      Unit

def OM.refl(x: C.Wasm.Outcome) -> OM(x, x):
  match x:
    case C.Wasm.Outcome.result{bs}:
      {==}
    case C.Wasm.Outcome.out_of_memory{}:
      {==}
    case C.Wasm.Outcome.no_result{}:
      {==}
    case C.Wasm.Outcome.unsupported{}:
      {==}
    case C.Wasm.Outcome.trap{}:
      {==}
    case C.Wasm.Outcome.not_done{}:
      Unit{}

# Nat
# ---

# (f - u) + g = (f + g) - u, when u <= f
def sub_add(+f: Nat, +u: Nat, h: PN.Le(u, f), +g: Nat) -> {Nat.add(Nat.sub(f, u), g) == Nat.sub(Nat.add(f, g), u) : Nat}:
  match f:
    case 0n:
      match u:
        case 0n:
          match g:
            case 0n:
              {==}
            case 1n+q:
              {==}
        case 1n+v:
          Empty.absurd({Nat.add(Nat.sub(0n, 1n+v), g) == Nat.sub(Nat.add(0n, g), 1n+v) : Nat}, h)
    case 1n+p:
      match u:
        case 0n:
          {==}
        case 1n+v:
          sub_add(p, v, h, g)

# Calls
# -----

def CM.plus(c: C.Wasm.Call, -d: C.Wasm.Call, h: CM(c, d)) -> CM(C.Wasm.call.plus(c), C.Wasm.call.plus(d)):
  match c:
    case C.Wasm.Call.done{+rs, +m, +n}:
      %h : {C.Wasm.Call.done{rs, m, 1n+n} == C.Wasm.call.plus(_) : C.Wasm.Call}
      {==}
    case C.Wasm.Call.trap{+m}:
      %h : {C.Wasm.Call.trap{m} == C.Wasm.call.plus(_) : C.Wasm.Call}
      {==}
    case C.Wasm.Call.not_done{}:
      Unit{}

def CB.plus(+k: Nat, c: C.Wasm.Call, h: CB(k, c)) -> CB(1n+k, C.Wasm.call.plus(c)):
  match c:
    case C.Wasm.Call.done{rs, m, n}:
      h
    case C.Wasm.Call.trap{m}:
      h
    case C.Wasm.Call.not_done{}:
      h

# the steps after st, with the fuel k and k + g
def go.st(+k: Nat, +g: Nat, st: C.Wasm.Step) ->
  CM(C.Wasm.call.stepped(st, fr => mm => C.Wasm.call.go(k, fr, mm)),
     C.Wasm.call.stepped(st, fr => mm => C.Wasm.call.go(Nat.add(k, g), fr, mm))):
  match k:
    case 0n:
      match st:
        case C.Wasm.Step.next{+fr, +m}:
          Unit{}
        case C.Wasm.Step.done{+rs, +m}:
          {==}
        case C.Wasm.Step.trap{+m}:
          {==}
    case 1n+p:
      match st:
        case C.Wasm.Step.next{+fr, +m}:
          CM.plus(C.Wasm.call.go(1n+p, fr, m), C.Wasm.call.go(Nat.add(1n+p, g), fr, m), go.st(p, g, C.Wasm.step(fr, m)))
        case C.Wasm.Step.done{+rs, +m}:
          {==}
        case C.Wasm.Step.trap{+m}:
          {==}

def go.more(+k: Nat, +g: Nat, +f: C.Wasm.Frame, +mem: C.Wasm.Memory) ->
  CM(C.Wasm.call.go(k, f, mem), C.Wasm.call.go(Nat.add(k, g), f, mem)):
  match k:
    case 0n:
      Unit{}
    case 1n+p:
      go.st(p, g, C.Wasm.step(f, mem))

def go.st.bound(+k: Nat, st: C.Wasm.Step) ->
  CB(1n+k, C.Wasm.call.stepped(st, fr => mm => C.Wasm.call.go(k, fr, mm))):
  match k:
    case 0n:
      match st:
        case C.Wasm.Step.next{+fr, +m}:
          Unit{}
        case C.Wasm.Step.done{rs, m}:
          Unit{}
        case C.Wasm.Step.trap{m}:
          Unit{}
    case 1n+p:
      match st:
        case C.Wasm.Step.next{+fr, +m}:
          CB.plus(1n+p, C.Wasm.call.go(1n+p, fr, m), go.st.bound(p, C.Wasm.step(fr, m)))
        case C.Wasm.Step.done{rs, m}:
          Unit{}
        case C.Wasm.Step.trap{m}:
          Unit{}

def go.bound(+k: Nat, +f: C.Wasm.Frame, +mem: C.Wasm.Memory) -> CB(k, C.Wasm.call.go(k, f, mem)):
  match k:
    case 0n:
      Unit{}
    case 1n+p:
      go.st.bound(p, C.Wasm.step(f, mem))

def call.more(+k: Nat, +g: Nat, func: C.Wasm.Func, +args: List<&2, U32>, +mem: C.Wasm.Memory) ->
  CM(C.Wasm.call(k, func, args, mem), C.Wasm.call(Nat.add(k, g), func, args, mem)):
  match func:
    case C.Wasm.Func{a, +q, +n, +body}:
      go.more(k, g, C.Wasm.Frame{body, Nil{}, q, Nil{}, List.append(&2, U32, args, List.replicate(U32, n, 0))}, mem)

def call.bound(+k: Nat, func: C.Wasm.Func, +args: List<&2, U32>, +mem: C.Wasm.Memory) ->
  CB(k, C.Wasm.call(k, func, args, mem)):
  match func:
    case C.Wasm.Func{a, +q, +n, +body}:
      go.bound(k, C.Wasm.Frame{body, Nil{}, q, Nil{}, List.append(&2, U32, args, List.replicate(U32, n, 0))}, mem)

# Invocations
# -----------

def invoked.more(c: C.Wasm.Call, -d: C.Wasm.Call, h: CM(c, d), +module: C.Wasm.Module) ->
  IM(C.Wasm.invoked(c, module), C.Wasm.invoked(d, module)):
  match c:
    case C.Wasm.Call.done{+rs, +m, +n}:
      %h : IM(C.Wasm.invoked(C.Wasm.Call.done{rs, m, n}, module), C.Wasm.invoked(_, module))
      {==}
    case C.Wasm.Call.trap{+m}:
      %h : IM(C.Wasm.invoked(C.Wasm.Call.trap{m}, module), C.Wasm.invoked(_, module))
      {==}
    case C.Wasm.Call.not_done{}:
      Unit{}

def invoked.bound(-k: Nat, c: C.Wasm.Call, h: CB(k, c), -module: C.Wasm.Module) ->
  IB(k, C.Wasm.invoked(c, module)):
  match c:
    case C.Wasm.Call.done{rs, m, n}:
      h
    case C.Wasm.Call.trap{m}:
      h
    case C.Wasm.Call.not_done{}:
      h

def arity.more(ok: Bool, +fn: C.Wasm.Func, +k: Nat, +g: Nat, +args: List<&2, U32>, +mem: C.Wasm.Memory, +module: C.Wasm.Module) ->
  IM(C.Wasm.invoke.arity(ok, fn, k, args, mem, module), C.Wasm.invoke.arity(ok, fn, Nat.add(k, g), args, mem, module)):
  match ok:
    case True{}:
      invoked.more(C.Wasm.call(k, fn, args, mem), C.Wasm.call(Nat.add(k, g), fn, args, mem), call.more(k, g, fn, args, mem), module)
    case False{}:
      {==}

def arity.bound(ok: Bool, +fn: C.Wasm.Func, +k: Nat, +args: List<&2, U32>, +mem: C.Wasm.Memory, +module: C.Wasm.Module) ->
  IB(k, C.Wasm.invoke.arity(ok, fn, k, args, mem, module)):
  match ok:
    case True{}:
      invoked.bound(k, C.Wasm.call(k, fn, args, mem), call.bound(k, fn, args, mem), module)
    case False{}:
      Unit{}

def found.more(fm: Maybe<&2, C.Wasm.Func>, +k: Nat, +g: Nat, +args: List<&2, U32>, +mem: C.Wasm.Memory, +module: C.Wasm.Module) ->
  IM(C.Wasm.invoke.found(fm, k, args, mem, module), C.Wasm.invoke.found(fm, Nat.add(k, g), args, mem, module)):
  match fm:
    case None{}:
      {==}
    case Some{fn}:
      match fn:
        case C.Wasm.Func{+p, +q, +n, +body}:
          arity.more(Nat.is_eq(p, List.length(&2, U32, args)), C.Wasm.Func{p, q, n, body}, k, g, args, mem, module)

def found.bound(fm: Maybe<&2, C.Wasm.Func>, +k: Nat, +args: List<&2, U32>, +mem: C.Wasm.Memory, +module: C.Wasm.Module) ->
  IB(k, C.Wasm.invoke.found(fm, k, args, mem, module)):
  match fm:
    case None{}:
      Unit{}
    case Some{fn}:
      match fn:
        case C.Wasm.Func{+p, +q, +n, +body}:
          arity.bound(Nat.is_eq(p, List.length(&2, U32, args)), C.Wasm.Func{p, q, n, body}, k, args, mem, module)

def invoke.more(+k: Nat, +g: Nat, inst: C.Wasm.Instance, +name: List<&2, U32>, +args: List<&2, U32>) ->
  IM(C.Wasm.invoke(k, inst, name, args), C.Wasm.invoke(Nat.add(k, g), inst, name, args)):
  match inst:
    case C.Wasm.Instance{module, +mem}:
      match module:
        case C.Wasm.Module{+fs, +memory, +es, +seg}:
          found.more(C.Wasm.export.func(fs, es, name), k, g, args, mem, C.Wasm.Module{fs, memory, es, seg})

def invoke.bound(+k: Nat, inst: C.Wasm.Instance, +name: List<&2, U32>, +args: List<&2, U32>) ->
  IB(k, C.Wasm.invoke(k, inst, name, args)):
  match inst:
    case C.Wasm.Instance{module, +mem}:
      match module:
        case C.Wasm.Module{+fs, +memory, +es, +seg}:
          found.bound(C.Wasm.export.func(fs, es, name), k, args, mem, C.Wasm.Module{fs, memory, es, seg})

# The host
# --------

def ran.more(a: C.Wasm.Invoked, -b: C.Wasm.Invoked, h: IM(a, b)) -> OM(C.Wasm.run.ran(a), C.Wasm.run.ran(b)):
  match a:
    case C.Wasm.Invoked.values{+vs, +inst, +n}:
      %h : OM(C.Wasm.run.ran(C.Wasm.Invoked.values{vs, inst, n}), C.Wasm.run.ran(_))
      OM.refl(C.Wasm.run.ran(C.Wasm.Invoked.values{vs, inst, n}))
    case C.Wasm.Invoked.trap{+inst}:
      %h : OM(C.Wasm.run.ran(C.Wasm.Invoked.trap{inst}), C.Wasm.run.ran(_))
      {==}
    case C.Wasm.Invoked.not_done{}:
      Unit{}
    case C.Wasm.Invoked.unsupported{}:
      %h : OM(C.Wasm.run.ran(C.Wasm.Invoked.unsupported{}), C.Wasm.run.ran(_))
      {==}

def written.more(ok: Bool, +f: Nat, +g: Nat, +inst: C.Wasm.Instance, +a: U32, +n: U32) ->
  OM(C.Wasm.run.written(ok, f, inst, a, n), C.Wasm.run.written(ok, Nat.add(f, g), inst, a, n)):
  match ok:
    case True{}:
      ran.more(C.Wasm.invoke(f, inst, C.Wasm.name.run(), [a, n]), C.Wasm.invoke(Nat.add(f, g), inst, C.Wasm.name.run(), [a, n]),
        invoke.more(f, g, inst, C.Wasm.name.run(), [a, n]))
    case False{}:
      {==}

def input.more(+f: Nat, +g: Nat, inst: C.Wasm.Instance, +a: U32, +n: U32, +i: List<&2, U32>) ->
  OM(C.Wasm.run.input(f, inst, a, n, i), C.Wasm.run.input(Nat.add(f, g), inst, a, n, i)):
  match inst:
    case C.Wasm.Instance{+module, mem}:
      match mem:
        case C.Wasm.Memory{+p, +lim, +bytes}:
          written.more(C.Wasm.fits(p, a, n), f, g,
            C.Wasm.Instance{module, C.Wasm.Memory{p, lim, C.Wasm.write.bytes(i, a, bytes)}}, a, n)

def alloced.if.more(full: Bool, +f: Nat, +g: Nat, +inst: C.Wasm.Instance, +a: U32, +n: U32, +i: List<&2, U32>) ->
  OM(C.Wasm.run.alloced.if(full, f, inst, a, n, i), C.Wasm.run.alloced.if(full, Nat.add(f, g), inst, a, n, i)):
  match full:
    case True{}:
      {==}
    case False{}:
      input.more(f, g, inst, a, n, i)

def alloced.more(+f: Nat, +g: Nat, r: C.Wasm.Invoked, -s: C.Wasm.Invoked, h: IM(r, s), hb: IB(f, r), +k: U32, +i: List<&2, U32>) ->
  OM(C.Wasm.run.alloced(r, f, k, i), C.Wasm.run.alloced(s, Nat.add(f, g), k, i)):
  match r:
    case C.Wasm.Invoked.values{vs, +inst, +used}:
      match vs:
        case Nil{}:
          %h : OM(C.Wasm.run.alloced(C.Wasm.Invoked.values{Nil{}, inst, used}, f, k, i), C.Wasm.run.alloced(_, Nat.add(f, g), k, i))
          {==}
        case Con{+a, +rest}:
          %h : OM(C.Wasm.run.alloced(C.Wasm.Invoked.values{Con{a, rest}, inst, used}, f, k, i), C.Wasm.run.alloced(_, Nat.add(f, g), k, i))
          %sub_add(f, used, hb, g) : OM(C.Wasm.run.alloced.if(U32.is_eq(a, 4294967295), Nat.sub(f, used), inst, a, k, i),
            C.Wasm.run.alloced.if(U32.is_eq(a, 4294967295), _, inst, a, k, i))
          alloced.if.more(U32.is_eq(a, 4294967295), Nat.sub(f, used), g, inst, a, k, i)
    case C.Wasm.Invoked.trap{+inst}:
      %h : OM(C.Wasm.run.alloced(C.Wasm.Invoked.trap{inst}, f, k, i), C.Wasm.run.alloced(_, Nat.add(f, g), k, i))
      {==}
    case C.Wasm.Invoked.not_done{}:
      Unit{}
    case C.Wasm.Invoked.unsupported{}:
      %h : OM(C.Wasm.run.alloced(C.Wasm.Invoked.unsupported{}, f, k, i), C.Wasm.run.alloced(_, Nat.add(f, g), k, i))
      {==}

def sized.more(n: Maybe<&2, U32>, +f: Nat, +g: Nat, +inst: C.Wasm.Instance, +i: List<&2, U32>) ->
  OM(C.Wasm.run.sized(n, f, inst, i), C.Wasm.run.sized(n, Nat.add(f, g), inst, i)):
  match n:
    case None{}:
      {==}
    case Some{+k}:
      alloced.more(f, g, C.Wasm.invoke(f, inst, C.Wasm.name.alloc(), [k]), C.Wasm.invoke(Nat.add(f, g), inst, C.Wasm.name.alloc(), [k]),
        invoke.more(f, g, inst, C.Wasm.name.alloc(), [k]), invoke.bound(f, inst, C.Wasm.name.alloc(), [k]), k, i)

def instance.more(ok: Bool, +f: Nat, +g: Nat, +inst: C.Wasm.Instance, +i: List<&2, U32>) ->
  OM(C.Wasm.run.instance(ok, f, inst, i), C.Wasm.run.instance(ok, Nat.add(f, g), inst, i)):
  match ok:
    case True{}:
      sized.more(C.Wasm.length32(i), f, g, inst, i)
    case False{}:
      {==}

def made.more(+f: Nat, +g: Nat, made: C.Wasm.Made, +i: List<&2, U32>) ->
  OM(C.Wasm.run.made(f, made, i), C.Wasm.run.made(Nat.add(f, g), made, i)):
  match made:
    case C.Wasm.Made.instance{+inst}:
      instance.more(C.Wasm.run.is_host(inst), f, g, inst, i)
    case C.Wasm.Made.unsupported{}:
      {==}
    case C.Wasm.Made.out_of_memory{}:
      {==}
    case C.Wasm.Made.trap{}:
      {==}

def run.om(+f: Nat, +g: Nat, +w: List<&2, U32>, +i: List<&2, U32>, +m: U32) ->
  OM(C.Wasm.run(f, w, i, m), C.Wasm.run(Nat.add(f, g), w, i, m)):
  made.more(f, g, C.Wasm.instantiate(w, m), i)

# The lemma
# ---------

def OM.rw(-a: C.Wasm.Outcome, -x: C.Wasm.Outcome, -b: C.Wasm.Outcome, e: {a == x : C.Wasm.Outcome}, h: OM(a, b)) -> OM(x, b):
  %e : OM(_, b)
  h

def OM.use(x: C.Wasm.Outcome, -b: C.Wasm.Outcome, nd: {done(x) == True{} : Bool}, h: OM(x, b)) -> {b == x : C.Wasm.Outcome}:
  match x:
    case C.Wasm.Outcome.result{+bs}:
      Equal.sym(C.Wasm.Outcome, C.Wasm.Outcome.result{bs}, b, h)
    case C.Wasm.Outcome.out_of_memory{}:
      Equal.sym(C.Wasm.Outcome, C.Wasm.Outcome.out_of_memory{}, b, h)
    case C.Wasm.Outcome.no_result{}:
      Equal.sym(C.Wasm.Outcome, C.Wasm.Outcome.no_result{}, b, h)
    case C.Wasm.Outcome.unsupported{}:
      Equal.sym(C.Wasm.Outcome, C.Wasm.Outcome.unsupported{}, b, h)
    case C.Wasm.Outcome.trap{}:
      Equal.sym(C.Wasm.Outcome, C.Wasm.Outcome.trap{}, b, h)
    case C.Wasm.Outcome.not_done{}:
      Empty.absurd({b == C.Wasm.Outcome.not_done{} : C.Wasm.Outcome}, PN.false_ne_true(nd))

# more fuel never changes an outcome that is not not_done
def run.more(+f: Nat, +g: Nat, +w: List<&2, U32>, +i: List<&2, U32>, +m: U32, +x: C.Wasm.Outcome,
  nd: {done(x) == True{} : Bool},
  e: {C.Wasm.run(f, w, i, m) == x : C.Wasm.Outcome}
) -> {C.Wasm.run(Nat.add(f, g), w, i, m) == x : C.Wasm.Outcome}:
  OM.use(x, C.Wasm.run(Nat.add(f, g), w, i, m), nd,
    OM.rw(C.Wasm.run(f, w, i, m), x, C.Wasm.run(Nat.add(f, g), w, i, m), e, run.om(f, g, w, i, m)))
