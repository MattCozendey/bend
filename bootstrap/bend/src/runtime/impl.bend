import Base
import ../wasm/impl.bend as Wasm
import ../imp/impl.bend as Imp
import ../fun/impl.bend as Fun

# The run time
# ============
#
# An Imp program that runs an F program (step 5). It builds the input as an F
# value, loads an image of the program's code and of the start's values, runs
# the abstract machine of F, and writes the bytes of the value at its end.
#
# The memory holds the input (by the protocol of Wasm.run) at 0, then the
# heap, which grows up from hp. A value z is the address 0; a node {t, a, b}
# is three words at its address: t, the address of a and the address of b.
# The run time never changes a node. An allocation that does not fit below
# the end of the memory ends the run with Out.oom.
#
# The code and the state of the abstract machine are values too (Enc): an
# instruction is a node whose tag is its number in Fun.C; a list is z or a
# node {0, x, rest}; a frame is the node {0, k, env}.

# Encodings
# =========

# a list, z at its end
def Enc.list(xs: List<&2, Fun.V>) -> Fun.V:
  match xs:
    case Nil{}:
      Fun.V.z{}
    case Con{x, rest}:
      Fun.V.n{0n, x, Enc.list(rest)}

# the variable i is {0, i, z}; a number or z is {1, its value, z}
def Enc.atom(a: Fun.A) -> Fun.V:
  match a:
    case Fun.A.var{i}:
      Fun.V.n{0n, Fun.V.num(i), Fun.V.z{}}
    case Fun.A.num{t}:
      Fun.V.n{1n, Fun.V.num(t), Fun.V.z{}}
    case Fun.A.z{}:
      Fun.V.n{1n, Fun.V.z{}, Fun.V.z{}}

# the atoms xs onto acc, the last first: a call's environment is its list
# built from the end
def Enc.args(xs: List<&2, Fun.A>, acc: Fun.V) -> Fun.V:
  match xs:
    case Nil{}:
      acc
    case Con{a, rest}:
      Enc.args(rest, Fun.V.n{0n, Enc.atom(a), acc})

# a call of the function f with the arguments xs, as tag (6: call, 7: jump)
# and k; stop when the program has no function f. Its tag is the offset 4 f of
# f in the table of the image, and room is the bytes that it allocates.
def Enc.call(tag: Nat, +f: Nat, +len: Nat, +xs: List<&2, Fun.A>, room: Nat, k: Fun.V) -> Fun.V:
  Bool.pick(Fun.V, Nat.is_lt(f, len),
    Fun.V.n{tag, Fun.V.n{Nat.double(Nat.double(f)), Enc.args(xs, Fun.V.z{}),
      Fun.V.num(Nat.add(Nat.mul(12n, List.length(&2, Fun.A, xs)), room))}, k},
    Fun.V.num(8n))

# the code c, in a program of len functions
def Enc.code(c: Fun.C, +len: Nat) -> Fun.V:
  match c:
    case Fun.C.ret{a}:
      Fun.V.n{0n, Enc.atom(a), Fun.V.z{}}
    case Fun.C.mk{t, a, b, k}:
      Fun.V.n{1n, Fun.V.n{t, Enc.atom(a), Enc.atom(b)}, Enc.code(k, len)}
    case Fun.C.case{a, t, y, n}:
      Fun.V.n{2n, Fun.V.n{t, Enc.atom(a), Enc.code(y, len)}, Enc.code(n, len)}
    case Fun.C.same{a, b, y, n}:
      Fun.V.n{3n, Fun.V.n{0n, Enc.atom(a), Enc.atom(b)}, Fun.V.n{0n, Enc.code(y, len), Enc.code(n, len)}}
    case Fun.C.dec{a, z, s}:
      Fun.V.n{4n, Enc.atom(a), Fun.V.n{0n, Enc.code(z, len), Enc.code(s, len)}}
    case Fun.C.inc{a, k}:
      Fun.V.n{5n, Enc.atom(a), Enc.code(k, len)}
    case Fun.C.call{f, xs, k}:
      Enc.call(6n, f, len, xs, 24n, Enc.code(k, len))
    case Fun.C.jump{f, xs}:
      Enc.call(7n, f, len, xs, 0n, Fun.V.z{})
    case Fun.C.stop{}:
      Fun.V.num(8n)

def Enc.codes(cs: List<&2, Fun.C>, +len: Nat) -> List<&2, Fun.V>:
  match cs:
    case Nil{}:
      []
    case Con{c, rest}:
      Con{Enc.code(c, len), Enc.codes(rest, len)}

# The image
# =========
#
# The words that the run time stores from the address base on: the address
# of the code of each function, the address of head and of tail, then the
# nodes of these values, each child before its node.

# a word: the number n, or the address base plus off
type W is Data:
  W.k{n: Nat}
  W.p{off: Nat}

# words (the last first), the word of a value, and the offset after them
type Img is Data:
  Img{ws: List<&2, W>, r: W, off: Nat}

def Img.elim(i: Img, f: List<&2, W> -> W -> Nat -> Img) -> Img:
  match i:
    case Img{ws, r, off}:
      f(ws)(r)(off)

# the node {t, ra, the word of i} after the words of i
def Img.node(t: Nat, ra: W, i: Img) -> Img:
  match i:
    case Img{ws, rb, +off}:
      Img{Con{rb, Con{ra, Con{W.k{t}, ws}}}, W.p{off}, 12n+off}

# the nodes of v after ws, from off on
def Img.val(v: Fun.V, ws: List<&2, W>, off: Nat) -> Img:
  match v:
    case Fun.V.z{}:
      Img{ws, W.k{0n}, off}
    case Fun.V.n{t, a, b}:
      Img.elim(Img.val(a, ws, off), ws1 => ra => off1 => Img.node(t, ra, Img.val(b, ws1, off1)))

# words (the last first), the words of the values (the last first), and the
# offset after them
type Imgs is Data:
  Imgs{ws: List<&2, W>, rs: List<&2, W>, off: Nat}

def Imgs.of(i: Img, rs: List<&2, W>) -> Imgs:
  match i:
    case Img{ws, r, off}:
      Imgs{ws, Con{r, rs}, off}

def Imgs.vals(vs: List<&2, Fun.V>, acc: Imgs) -> Imgs:
  match vs acc:
    case Nil{} _:
      acc
    case Con{v, rest} Imgs{ws, rs, off}:
      Imgs.vals(rest, Imgs.of(Img.val(v, ws, off), rs))

def Imgs.words(i: Imgs) -> List<&2, W>:
  match i:
    case Imgs{ws, rs, off}:
      List.append(&2, W, List.reverse(&2, W, rs), List.reverse(&2, W, ws))

# the words of the image of the values vs
def Img.of(+vs: List<&2, Fun.V>) -> List<&2, W>:
  Imgs.words(Imgs.vals(vs, Imgs{[], [], Nat.double(Nat.double(List.length(&2, Fun.V, vs)))}))

# Imp code
# ========

def E.l(i: Nat) -> Imp.Exp:
  Imp.Exp.get{i}

def E.k(v: U32) -> Imp.Exp:
  Imp.Exp.const{v}

def E.n(n: Nat) -> Imp.Exp:
  Imp.Exp.const{U32.from_nat(n)}

def E.add(a: Imp.Exp, b: Imp.Exp) -> Imp.Exp:
  Imp.Exp.bin{Wasm.Bin.add{}, a, b}

def E.sub(a: Imp.Exp, b: Imp.Exp) -> Imp.Exp:
  Imp.Exp.bin{Wasm.Bin.sub{}, a, b}

def E.eq(a: Imp.Exp, b: Imp.Exp) -> Imp.Exp:
  Imp.Exp.bin{Wasm.Bin.eq{}, a, b}

def E.lt(a: Imp.Exp, b: Imp.Exp) -> Imp.Exp:
  Imp.Exp.bin{Wasm.Bin.lt_u{}, a, b}

def E.ld(off: U32, a: Imp.Exp) -> Imp.Exp:
  Imp.Exp.load{off, a}

def S.all(ss: List<&2, Imp.Stm>) -> Imp.Stm:
  match ss:
    case Nil{}:
      Imp.Stm.skip{}
    case Con{s, rest}:
      Imp.Stm.seq{s, S.all(rest)}

def S.if(c: Imp.Exp, a: Imp.Stm, b: Imp.Stm) -> Imp.Stm:
  Imp.Stm.if{c, a, b}

# The locals
# ==========
#
# 0 hp: the start of the free memory
# 1 lim: the end of the memory
# 2 base: the address of the image
# 3 c: the code that runs
# 4 env: the environment
# 5 ks: the frames
# 6 v: the value that returns
# 7 mode: 0 runs c, 1 returns v
# 8 out: the address of the output
# 9 to 17: temporaries t, x, y, p, q, acc, a, i, w

# The parts
# =========

# the end with Out.oom, by a break out of d loops
def S.oom(d: Nat) -> Imp.Stm:
  S.all([Imp.Stm.store{0, E.k(0), E.k(1)}, Imp.Stm.store8{4, E.k(0), E.k(255)}, Imp.Stm.set{8n, E.k(0)},
    Imp.Stm.break{d}])

# Out.oom when fewer than n bytes are free
def S.room(n: Imp.Exp, d: Nat) -> Imp.Stm:
  S.if(E.lt(E.sub(E.l(1n), E.l(0n)), n), S.oom(d), Imp.Stm.skip{})

# the node {t, a, b} at hp, then w := its address and hp := hp + 12. t, a
# and b read only locals and constants. The caller checks the room.
def S.alloc(t: Imp.Exp, a: Imp.Exp, b: Imp.Exp) -> Imp.Stm:
  S.all([Imp.Stm.store{0, E.l(0n), t}, Imp.Stm.store{4, E.l(0n), a}, Imp.Stm.store{8, E.l(0n), b},
    Imp.Stm.set{17n, E.l(0n)}, Imp.Stm.set{0n, E.add(E.l(0n), E.k(12))}])

# env := {0, {t, a, b}, env}: 24 bytes, which the caller checks
def S.push(t: Imp.Exp, a: Imp.Exp, b: Imp.Exp) -> Imp.Stm:
  S.all([S.alloc(t, a, b), S.alloc(E.k(0), E.l(17n), E.l(4n)), Imp.Stm.set{4n, E.l(17n)}])

# w := the cell of the variable i of the environment at w; a trap when the
# environment has no such variable
def S.walk.body() -> Imp.Stm:
  S.all([S.if(Imp.Exp.eqz{E.l(17n)}, Imp.Stm.trap{}, Imp.Stm.skip{}),
    S.if(Imp.Exp.eqz{E.l(16n)}, Imp.Stm.break{0n}, Imp.Stm.skip{}),
    Imp.Stm.set{17n, E.ld(8, E.l(17n))},
    Imp.Stm.set{16n, E.sub(E.l(16n), E.k(1))}])

def S.walk() -> Imp.Stm:
  Imp.Stm.loop{S.walk.body()}

# y := the value of the atom at e, and a, i, w := 0
def S.atom(e: Imp.Exp) -> Imp.Stm:
  S.all([Imp.Stm.set{15n, e},
    S.if(E.eq(E.ld(0, E.l(15n)), E.k(1)),
      Imp.Stm.set{11n, E.ld(4, E.l(15n))},
      S.all([Imp.Stm.set{16n, E.ld(0, E.ld(4, E.l(15n)))}, Imp.Stm.set{17n, E.l(4n)}, S.walk(),
        Imp.Stm.set{11n, E.ld(4, E.l(17n))}])),
    Imp.Stm.set{15n, E.k(0)}, Imp.Stm.set{16n, E.k(0)}, Imp.Stm.set{17n, E.k(0)}])

def S.args.body() -> Imp.Stm:
  S.all([S.if(Imp.Exp.eqz{E.l(13n)}, Imp.Stm.break{0n}, Imp.Stm.skip{}),
    S.atom(E.ld(4, E.l(13n))),
    S.alloc(E.k(0), E.l(11n), E.l(14n)),
    Imp.Stm.set{14n, E.l(17n)},
    Imp.Stm.set{13n, E.ld(8, E.l(13n))}])

# acc := the environment of a call, from the atoms at e, and y, q, a, i,
# w := 0. The caller checks the room: 12 bytes for each atom.
def S.args(e: Imp.Exp) -> Imp.Stm:
  S.all([Imp.Stm.set{13n, e}, Imp.Stm.set{14n, E.k(0)}, Imp.Stm.loop{S.args.body()},
    Imp.Stm.set{11n, E.k(0)}, Imp.Stm.set{13n, E.k(0)}, Imp.Stm.set{15n, E.k(0)}, Imp.Stm.set{16n, E.k(0)},
    Imp.Stm.set{17n, E.k(0)}])

# the code of the function whose offset is at x
def E.fun() -> Imp.Exp:
  E.ld(0, E.add(E.l(2n), E.ld(0, E.l(10n))))

# The steps
# =========

def I.ret() -> Imp.Stm:
  S.all([S.atom(E.ld(4, E.l(3n))), Imp.Stm.set{6n, E.l(11n)}, Imp.Stm.set{7n, E.k(1)}, Imp.Stm.set{3n, E.k(0)},
    Imp.Stm.set{4n, E.k(0)}])

def I.mk() -> Imp.Stm:
  S.all([Imp.Stm.set{10n, E.ld(4, E.l(3n))}, S.atom(E.ld(4, E.l(10n))), Imp.Stm.set{12n, E.l(11n)},
    S.atom(E.ld(8, E.l(10n))), Imp.Stm.set{9n, E.ld(0, E.l(10n))}, S.room(E.k(24), 1n),
    S.push(E.l(9n), E.l(12n), E.l(11n)),
    Imp.Stm.set{3n, E.ld(8, E.l(3n))}])

def I.case() -> Imp.Stm:
  S.all([Imp.Stm.set{10n, E.ld(4, E.l(3n))}, S.atom(E.ld(4, E.l(10n))),
    S.if(Imp.Exp.eqz{E.l(11n)}, Imp.Stm.set{3n, E.ld(8, E.l(3n))},
      S.if(E.eq(E.ld(0, E.l(11n)), E.ld(0, E.l(10n))),
        S.all([S.room(E.k(24), 1n), Imp.Stm.set{12n, E.ld(4, E.l(11n))}, Imp.Stm.set{13n, E.ld(8, E.l(11n))},
          S.alloc(E.k(0), E.l(12n), E.l(4n)), S.alloc(E.k(0), E.l(13n), E.l(17n)), Imp.Stm.set{4n, E.l(17n)},
          Imp.Stm.set{3n, E.ld(8, E.l(10n))}]),
        Imp.Stm.set{3n, E.ld(8, E.l(3n))}))])

def I.same() -> Imp.Stm:
  S.all([Imp.Stm.set{10n, E.ld(4, E.l(3n))}, S.atom(E.ld(4, E.l(10n))), Imp.Stm.set{12n, E.l(11n)},
    S.atom(E.ld(8, E.l(10n))),
    S.if(Imp.Exp.eqz{E.l(12n)}, Imp.Stm.trap{}, Imp.Stm.skip{}),
    S.if(Imp.Exp.eqz{E.l(11n)}, Imp.Stm.trap{}, Imp.Stm.skip{}),
    Imp.Stm.set{10n, E.ld(8, E.l(3n))},
    S.if(E.eq(E.ld(0, E.l(12n)), E.ld(0, E.l(11n))), Imp.Stm.set{3n, E.ld(4, E.l(10n))},
      Imp.Stm.set{3n, E.ld(8, E.l(10n))})])

def I.dec() -> Imp.Stm:
  S.all([S.atom(E.ld(4, E.l(3n))), S.if(Imp.Exp.eqz{E.l(11n)}, Imp.Stm.trap{}, Imp.Stm.skip{}),
    Imp.Stm.set{9n, E.ld(0, E.l(11n))}, Imp.Stm.set{10n, E.ld(8, E.l(3n))},
    S.if(Imp.Exp.eqz{E.l(9n)}, Imp.Stm.set{3n, E.ld(4, E.l(10n))},
      S.all([S.room(E.k(24), 1n), S.push(E.sub(E.l(9n), E.k(1)), E.k(0), E.k(0)),
        Imp.Stm.set{3n, E.ld(8, E.l(10n))}]))])

def I.inc() -> Imp.Stm:
  S.all([S.atom(E.ld(4, E.l(3n))), S.if(Imp.Exp.eqz{E.l(11n)}, Imp.Stm.trap{}, Imp.Stm.skip{}),
    Imp.Stm.set{9n, E.ld(0, E.l(11n))},
    S.if(E.eq(E.l(9n), E.k(4294967295)), S.oom(1n), Imp.Stm.skip{}),
    S.room(E.k(24), 1n), S.push(E.add(E.l(9n), E.k(1)), E.k(0), E.k(0)), Imp.Stm.set{3n, E.ld(8, E.l(3n))}])

# the room of the call at x
def S.call_room() -> Imp.Stm:
  S.all([Imp.Stm.set{10n, E.ld(4, E.l(3n))}, Imp.Stm.set{9n, E.ld(0, E.ld(8, E.l(10n)))}, S.room(E.l(9n), 1n)])

def I.call() -> Imp.Stm:
  S.all([S.call_room(), S.args(E.ld(4, E.l(10n))),
    Imp.Stm.set{12n, E.ld(8, E.l(3n))}, S.alloc(E.k(0), E.l(12n), E.l(4n)), S.alloc(E.k(0), E.l(17n), E.l(5n)),
    Imp.Stm.set{5n, E.l(17n)}, Imp.Stm.set{4n, E.l(14n)}, Imp.Stm.set{3n, E.fun()}])

def I.jump() -> Imp.Stm:
  S.all([S.call_room(), S.args(E.ld(4, E.l(10n))), Imp.Stm.set{4n, E.l(14n)},
    Imp.Stm.set{3n, E.fun()}])

# the instruction at c, by its tag t
def I.run() -> Imp.Stm:
  S.all([Imp.Stm.set{9n, E.ld(0, E.l(3n))},
    S.if(E.eq(E.l(9n), E.k(0)), I.ret(),
    S.if(E.eq(E.l(9n), E.k(1)), I.mk(),
    S.if(E.eq(E.l(9n), E.k(2)), I.case(),
    S.if(E.eq(E.l(9n), E.k(3)), I.same(),
    S.if(E.eq(E.l(9n), E.k(4)), I.dec(),
    S.if(E.eq(E.l(9n), E.k(5)), I.inc(),
    S.if(E.eq(E.l(9n), E.k(6)), I.call(),
    S.if(E.eq(E.l(9n), E.k(7)), I.jump(), Imp.Stm.trap{}))))))))])

# the output: the bytes of the list at v, at out; Out.oom when one is above
# 255 or when they do not fit
def I.halt() -> Imp.Stm:
  S.all([S.room(E.k(4), 1n), Imp.Stm.set{8n, E.l(0n)}, Imp.Stm.set{16n, E.k(0)}, Imp.Stm.set{12n, E.l(6n)},
    Imp.Stm.loop{S.all([
      S.if(Imp.Exp.eqz{E.l(12n)}, Imp.Stm.trap{}, Imp.Stm.skip{}),
      Imp.Stm.set{9n, E.ld(0, E.l(12n))},
      S.if(Imp.Exp.eqz{E.l(9n)}, Imp.Stm.break{0n}, Imp.Stm.skip{}),
      S.if(E.eq(E.l(9n), E.k(1)), Imp.Stm.skip{}, Imp.Stm.trap{}),
      Imp.Stm.set{10n, E.ld(4, E.l(12n))},
      S.if(Imp.Exp.eqz{E.l(10n)}, Imp.Stm.trap{}, Imp.Stm.skip{}),
      Imp.Stm.set{9n, E.ld(0, E.l(10n))},
      S.if(E.lt(E.k(255), E.l(9n)), S.oom(2n), Imp.Stm.skip{}),
      S.if(E.lt(E.l(16n), E.sub(E.sub(E.l(1n), E.l(8n)), E.k(4))), Imp.Stm.skip{}, S.oom(2n)),
      Imp.Stm.store8{4, E.add(E.l(8n), E.l(16n)), E.l(9n)},
      Imp.Stm.set{16n, E.add(E.l(16n), E.k(1))},
      Imp.Stm.set{12n, E.ld(8, E.l(12n))}])},
    Imp.Stm.store{0, E.l(8n), E.l(16n)}, Imp.Stm.break{1n}])

# the return of v to the innermost frame, or the output when there is none
def I.back() -> Imp.Stm:
  S.if(Imp.Exp.eqz{E.l(5n)}, I.halt(),
    S.all([S.room(E.k(12), 1n), Imp.Stm.set{10n, E.ld(4, E.l(5n))}, Imp.Stm.set{12n, E.ld(8, E.l(10n))},
      S.alloc(E.k(0), E.l(6n), E.l(12n)), Imp.Stm.set{4n, E.l(17n)}, Imp.Stm.set{3n, E.ld(4, E.l(10n))},
      Imp.Stm.set{5n, E.ld(8, E.l(5n))}, Imp.Stm.set{6n, E.k(0)}, Imp.Stm.set{7n, E.k(0)}]))

# a step of the abstract machine. c and env are 0 when it returns v, and v
# is 0 when it runs c.
def I.step() -> Imp.Stm:
  S.if(Imp.Exp.eqz{E.l(7n)}, I.run(), I.back())

# The start
# =========

# the input as a Maybe of a list of numbers, into x
def S.input() -> Imp.Stm:
  S.all([Imp.Stm.set{9n, E.ld(0, E.k(0))},
    S.if(E.eq(E.l(9n), E.k(4294967295)),
      S.all([Imp.Stm.set{0n, E.k(4)}, S.room(E.k(12), 0n), S.alloc(E.k(0), E.k(0), E.k(0)), Imp.Stm.set{10n, E.l(17n)}]),
      S.all([Imp.Stm.set{0n, E.add(E.k(4), E.l(9n))}, S.room(E.k(12), 0n), S.alloc(E.k(0), E.k(0), E.k(0)),
        Imp.Stm.set{14n, E.l(17n)}, Imp.Stm.set{16n, E.l(9n)},
        Imp.Stm.loop{S.all([
          S.if(Imp.Exp.eqz{E.l(16n)}, Imp.Stm.break{0n}, Imp.Stm.skip{}),
          Imp.Stm.set{16n, E.sub(E.l(16n), E.k(1))},
          S.room(E.k(24), 1n),
          Imp.Stm.set{9n, Imp.Exp.load8{4, E.l(16n)}},
          S.alloc(E.l(9n), E.k(0), E.k(0)),
          S.alloc(E.k(1), E.l(17n), E.l(14n)),
          Imp.Stm.set{14n, E.l(17n)}])},
        S.room(E.k(12), 0n), S.alloc(E.k(1), E.l(14n), E.k(0)), Imp.Stm.set{10n, E.l(17n)}]))])

# the stores of the words ws at base + off on
def S.load(ws: List<&2, W>, +off: Nat) -> Imp.Stm:
  match ws:
    case Nil{}:
      Imp.Stm.skip{}
    case Con{W.k{n}, rest}:
      Imp.Stm.seq{Imp.Stm.store{U32.from_nat(off), E.l(2n), E.n(n)}, S.load(rest, 4n+off)}
    case Con{W.p{p}, rest}:
      Imp.Stm.seq{Imp.Stm.store{U32.from_nat(off), E.l(2n), E.add(E.l(2n), E.n(p))}, S.load(rest, 4n+off)}

# the image of ws at hp, then env := [head, input, tail...] and c := the code
# of entry. len: the number of functions.
def S.image(+ws: List<&2, W>, +len: Nat, entry: Nat) -> Imp.Stm:
  +size = U32.from_nat(Nat.double(Nat.double(List.length(&2, W, ws))))
  S.all([S.room(E.k(size), 0n), Imp.Stm.set{2n, E.l(0n)}, S.load(ws, 0n),
    Imp.Stm.set{0n, E.add(E.l(0n), E.k(size))},
    S.room(E.k(24), 0n),
    Imp.Stm.set{12n, E.ld(U32.from_nat(Nat.double(Nat.double(1n+len))), E.l(2n))},
    Imp.Stm.set{13n, E.ld(U32.from_nat(Nat.double(Nat.double(len))), E.l(2n))},
    S.alloc(E.k(0), E.l(10n), E.l(12n)), S.alloc(E.k(0), E.l(13n), E.l(17n)), Imp.Stm.set{4n, E.l(17n)},
    Imp.Stm.set{3n, E.ld(U32.from_nat(Nat.double(Nat.double(entry))), E.l(2n))},
    Imp.Stm.set{5n, E.k(0)}, Imp.Stm.set{7n, E.k(0)}])

# The program
# ===========

# the image of the code of prog, head and tail
def Img.prog(+prog: List<&2, Fun.C>, head: Fun.V, tail: List<&2, Fun.V>) -> List<&2, W>:
  Img.of(List.append(&2, Fun.V, Enc.codes(prog, List.length(&2, Fun.C, prog)), [head, Enc.list(tail)]))

def W.fits(w: W) -> Bool:
  match w:
    case W.k{n}:
      Nat.is_le(n, 4294967295n)
    case W.p{off}:
      Nat.is_le(off, 4294967295n)

def Ws.fits(ws: List<&2, W>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{w, rest}:
      W.fits(w) && Ws.fits(rest)

# whether each word of the image fits in an i32, and the image in the memory
def fits(+prog: List<&2, Fun.C>, head: Fun.V, tail: List<&2, Fun.V>) -> Bool:
  +ws = Img.prog(prog, head, tail)
  Ws.fits(ws) && Nat.is_le(Nat.double(Nat.double(List.length(&2, W, ws))), 4294967295n)

# the run time of the program prog from its function entry, with the
# environment head, the input, then the values of tail
def RT(+prog: List<&2, Fun.C>, entry: Nat, head: Fun.V, tail: List<&2, Fun.V>) -> Imp.Prog:
  Imp.Prog{18n,
    Imp.Stm.loop{S.all([Imp.Stm.set{1n, Imp.Exp.bin{Wasm.Bin.shl{}, Imp.Exp.size{}, E.k(16)}}, S.input(),
      S.image(Img.prog(prog, head, tail), List.length(&2, Fun.C, prog), entry),
      Imp.Stm.loop{I.step()}])},
    E.l(8n)}
