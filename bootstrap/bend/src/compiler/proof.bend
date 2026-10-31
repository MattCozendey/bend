# compiler: the proofs of the laws of step 1
# =========================================
#
# The laws of spec.bend follow from two layers, each a lemma below:
#
#   A (translation): the module that Cir.module makes of the machine runs in
#     the Bend copy of WASM as Cir.exec says (Cir.result), for any image of
#     fewer than 2^26 cells, when Cir.exec never traps; and a module whose
#     program halts at once gives no result.
#   B (machine): from the image of a book, Mach.code never traps, and it
#     gives what Eval gives, or runs out of memory; with the memory of
#     INVARIANTS #4, it gives it.
#
# A lemma whose body is ?TODO is still open: the laws hold once each is
# proven. The proofs of the laws themselves, at the end, are complete.

import Base
import ./impl.bend as C
import ./spec.bend as S
import ./proof_need.bend as PN
import ./proof_img.bend as PI

# Open lemmas
# -----------

# A: a result of the machine's module is one that Cir gives
def mach_wasm.sound(
  +f: Nat, +cells: List<&2, C.Cir.Cell>, +i: List<&2, U32>, +m: U32, +o: List<&2, U32>,
  small: {U32.is_lt(C.Wasm.encode.len(C.Cir.Cell, cells), 67108864) == True{} : Bool},
  safe: @n:Nat -> {C.Cir.result(n, C.Mach.code(), C.Mach.regs(), cells, i, m) != C.Wasm.Outcome.trap{} : C.Wasm.Outcome},
  e: {C.Wasm.run(f, C.Compiler.module(cells), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome}
) -> &n:Nat -> {C.Cir.result(n, C.Mach.code(), C.Mach.regs(), cells, i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome}:
  ?TODO

# A: a result that Cir gives is one of the machine's module
def mach_wasm.result(
  +n: Nat, +cells: List<&2, C.Cir.Cell>, +i: List<&2, U32>, +m: U32, +o: List<&2, U32>,
  small: {U32.is_lt(C.Wasm.encode.len(C.Cir.Cell, cells), 67108864) == True{} : Bool},
  e: {C.Cir.result(n, C.Mach.code(), C.Mach.regs(), cells, i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome}
) -> &f:Nat -> {C.Wasm.run(f, C.Compiler.module(cells), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome}:
  ?TODO

# A: when Cir runs out of memory, so does the machine's module
def mach_wasm.oom(
  +n: Nat, +cells: List<&2, C.Cir.Cell>, +i: List<&2, U32>, +m: U32,
  small: {U32.is_lt(C.Wasm.encode.len(C.Cir.Cell, cells), 67108864) == True{} : Bool},
  e: {C.Cir.result(n, C.Mach.code(), C.Mach.regs(), cells, i, m) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}
) -> &f:Nat -> {C.Wasm.run(f, C.Compiler.module(cells), i, m) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}:
  ?TODO

# A: a module that halts at once with a status other than 0 gives no result
def halt.no_result(
  +f: Nat, +s: U32, +i: List<&2, U32>, +m: U32, +o: List<&2, U32>,
  ns: {U32.is_eq(s, 0) == False{} : Bool},
  e: {C.Wasm.run(f, C.Compiler.halt(s), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome}
) -> Empty:
  ?TODO

# A: a module that halts at once with the status 1 runs out of memory
def halt.oom(+i: List<&2, U32>, +m: U32) -> &f:Nat -> {C.Wasm.run(f, C.Compiler.halt(1), i, m) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}:
  ?TODO

# the image of a book of fewer than 2^26 bytes has fewer than 2^26 cells
def img.small(
  +p: List<&2, U32>, +ds: List<&2, C.Def>,
  rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  small: {C.Img.small(p, 0) == True{} : Bool}
) -> {U32.is_lt(C.Wasm.encode.len(C.Cir.Cell, C.Img.cells(ds)), 67108864) == True{} : Bool}:
  PI.img.small.proof(p, ds, rd, small)

# a book of 2^26 bytes or more needs more memory than a module can have
def need.big(
  +p: List<&2, U32>, +i: List<&2, U32>, +n: Nat, +m: U32,
  small: {C.Img.small(p, 0) == False{} : Bool},
  big: {Nat.is_le(C.Program.need(p, i, n), C.Program.memory(m)) == True{} : Bool}
) -> Empty:
  PN.need.big.proof(p, i, n, m, small, big)

# B: the machine never makes an access that its module could not make the
# same way
def mach.safe(
  +p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +n: Nat,
  rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  small: {C.Img.small(p, 0) == True{} : Bool}
) -> {C.Cir.result(n, C.Mach.code(), C.Mach.regs(), C.Img.cells(ds), i, m) != C.Wasm.Outcome.trap{} : C.Wasm.Outcome}:
  ?TODO

# B: a result of the machine is the list of bytes of a value that Eval reaches
def mach.sound(
  +p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +n: Nat, +o: List<&2, U32>,
  rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  small: {C.Img.small(p, 0) == True{} : Bool},
  e: {C.Cir.result(n, C.Mach.code(), C.Mach.regs(), C.Img.cells(ds), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome}
) -> &k:Nat -> {C.Program.result(ds, C.Eval.steps(k, ds, C.Program.start(i))) == Some{o} : Maybe<&2, List<&2, U32>>}:
  ?TODO

# B: when Eval reaches a list of bytes, the machine gives it, or runs out of
# memory
def mach.complete(
  +p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +k: Nat, +o: List<&2, U32>,
  rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  small: {C.Img.small(p, 0) == True{} : Bool},
  e: {C.Program.result(ds, C.Eval.steps(k, ds, C.Program.start(i))) == Some{o} : Maybe<&2, List<&2, U32>>}
) -> &n:Nat -> Or({C.Cir.result(n, C.Mach.code(), C.Mach.regs(), C.Img.cells(ds), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome},
  {C.Cir.result(n, C.Mach.code(), C.Mach.regs(), C.Img.cells(ds), i, m) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}):
  ?TODO

# B: with the memory of INVARIANTS #4, the machine gives the list of bytes
def mach.memory(
  +p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +k: Nat, +o: List<&2, U32>,
  rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  small: {C.Img.small(p, 0) == True{} : Bool},
  e: {C.Program.result(ds, C.Eval.steps(k, ds, C.Program.start(i))) == Some{o} : Maybe<&2, List<&2, U32>>},
  big: {Nat.is_le(C.Program.need(p, i, k), C.Program.memory(m)) == True{} : Bool}
) -> &n:Nat -> {C.Cir.result(n, C.Mach.code(), C.Mach.regs(), C.Img.cells(ds), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome}:
  ?TODO

# The laws
# --------
#
# Each law goes by the cases of Compiler.compile: a book of 2^26 bytes or
# more, a book that Book.read cannot read, and a book that it reads.

def gives.read.at(
  +p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +o: List<&2, U32>, +k: Nat,
  er: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  ek: {C.Program.result(ds, C.Eval.steps(k, ds, C.Program.start(i))) == Some{o} : Maybe<&2, List<&2, U32>>}
) -> {C.Program.gives(p, i, k) == Some{o} : Maybe<&2, List<&2, U32>>}:
  %Equal.sym(Maybe<List<&2, C.Def>>, C.Book.read(p), Some{ds}, er) : {C.Program.gives.of(_, i, k) == Some{o} : Maybe<&2, List<&2, U32>>}
  ek

# what a program gives after k steps, once its book is read
def gives.read(
  +p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +o: List<&2, U32>,
  er: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  s: &k:Nat -> {C.Program.result(ds, C.Eval.steps(k, ds, C.Program.start(i))) == Some{o} : Maybe<&2, List<&2, U32>>}
) -> &k:Nat -> {C.Program.gives(p, i, k) == Some{o} : Maybe<&2, List<&2, U32>>}:
  (+k, ek) = s
  (k, gives.read.at(p, ds, i, o, k, er, ek))

# the compiler's module of a book that it reads, and of fewer than 2^26
# bytes, is the machine's module of its image; machine is any maker of it,
# so that no check computes the machine's module
def compile.machine(machine: List<&2, C.Cir.Cell> -> List<&2, U32>, +ds: List<&2, C.Def>) ->
  {C.Compiler.compile.of(machine, True{}, Some{ds}) == machine(C.Img.cells(ds)) : List<&2, U32>}:
  {==}

# no_wrong_result, for a book that Book.read reads: its machine's result is,
# by A, one that Cir gives, and so, by B, one that Eval gives
def nwr.machine(
  +p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +o: List<&2, U32>,
  +er: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  +es: {C.Img.small(p, 0) == True{} : Bool},
  s: &n:Nat -> {C.Cir.result(n, C.Mach.code(), C.Mach.regs(), C.Img.cells(ds), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome}
) -> &k:Nat -> {C.Program.gives(p, i, k) == Some{o} : Maybe<&2, List<&2, U32>>}:
  (+n, en) = s
  gives.read(p, ds, i, o, er, mach.sound(p, ds, i, m, n, o, er, es, en))

def nwr.of(+f: Nat, +p: List<&2, U32>, +i: List<&2, U32>, +m: U32, +o: List<&2, U32>, small: Bool,
  r: Maybe<List<&2, C.Def>>) ->
  {C.Img.small(p, 0) == small : Bool} -> {C.Book.read(p) == r : Maybe<List<&2, C.Def>>} ->
  {C.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, small, r), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome} ->
  &k:Nat -> {C.Program.gives(p, i, k) == Some{o} : Maybe<&2, List<&2, U32>>}:
  match small r:
    case False{} _:
      es => er => e => Empty.absurd(&k:Nat -> {C.Program.gives(p, i, k) == Some{o} : Maybe<&2, List<&2, U32>>},
        halt.no_result(f, 1, i, m, o, {==}, e))
    case True{} None{}:
      es => er => e => Empty.absurd(&k:Nat -> {C.Program.gives(p, i, k) == Some{o} : Maybe<&2, List<&2, U32>>},
        halt.no_result(f, 2, i, m, o, {==}, e))
    case True{} Some{+ds}:
      +es => +er => e => nwr.machine(p, ds, i, m, o, er, es,
        mach_wasm.sound(f, C.Img.cells(ds), i, m, o, img.small(p, ds, er, es), x => mach.safe(p, ds, i, m, x, er, es),
          (%compile.machine(C.Compiler.module, ds) : {C.Wasm.run(f, _, i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome}; e)))

def S.no_wrong_result(f, p, i, m, o, e):
  nwr.of(f, p, i, m, o, C.Img.small(p, 0), C.Book.read(p))({==}, {==}, e)

# Some and None differ: a motive that is Empty at None
def maybe.none(x: Maybe<&2, List<&2, U32>>) -> Type:
  match x:
    case None{}:
      Empty
    case Some{_}:
      Unit

# Eval gives no result from a book that Book.read cannot read
def gives.none(-o: List<&2, U32>, e: {None{} == Some{o} : Maybe<&2, List<&2, U32>>}) -> Empty:
  %Equal.sym(Maybe<&2, List<&2, U32>>, None{}, Some{o}, e) : maybe.none(_)
  Unit{}

# the machine's module of a book that the compiler reads is its module
def run.machine(+f: Nat, +ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +x: C.Wasm.Outcome,
  ef: {C.Wasm.run(f, C.Compiler.module(C.Img.cells(ds)), i, m) == x : C.Wasm.Outcome}) ->
  {C.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, True{}, Some{ds}), i, m) == x : C.Wasm.Outcome}:
  %Equal.sym(List<&2, U32>, C.Compiler.compile.of(C.Compiler.module, True{}, Some{ds}), C.Compiler.module(C.Img.cells(ds)),
    compile.machine(C.Compiler.module, ds)) : {C.Wasm.run(f, _, i, m) == x : C.Wasm.Outcome}
  ef

# no_other_failure, for a book that the compiler reads: by B, the machine gives
# the result or runs out of memory, and so, by A, does its module
def nof.result(+ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +o: List<&2, U32>,
  s: &f:Nat -> {C.Wasm.run(f, C.Compiler.module(C.Img.cells(ds)), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome}) ->
  &f:Nat -> Or({C.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, True{}, Some{ds}), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome},
    {C.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, True{}, Some{ds}), i, m) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}):
  (+f, ef) = s
  (f, Inl{run.machine(f, ds, i, m, C.Wasm.Outcome.result{o}, ef)})

def nof.oom(+ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, -o: List<&2, U32>,
  s: &f:Nat -> {C.Wasm.run(f, C.Compiler.module(C.Img.cells(ds)), i, m) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}) ->
  &f:Nat -> Or({C.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, True{}, Some{ds}), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome},
    {C.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, True{}, Some{ds}), i, m) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}):
  (+f, ef) = s
  (f, Inr{run.machine(f, ds, i, m, C.Wasm.Outcome.out_of_memory{}, ef)})

def nof.machine(+p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +o: List<&2, U32>,
  +er: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  +es: {C.Img.small(p, 0) == True{} : Bool},
  s: &n:Nat -> Or({C.Cir.result(n, C.Mach.code(), C.Mach.regs(), C.Img.cells(ds), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome},
    {C.Cir.result(n, C.Mach.code(), C.Mach.regs(), C.Img.cells(ds), i, m) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome})) ->
  &f:Nat -> Or({C.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, True{}, Some{ds}), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome},
    {C.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, True{}, Some{ds}), i, m) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}):
  (+n, c) = s
  match c:
    case Inl{a}:
      nof.result(ds, i, m, o, mach_wasm.result(n, C.Img.cells(ds), i, m, o, img.small(p, ds, er, es), a))
    case Inr{b}:
      nof.oom(ds, i, m, o, mach_wasm.oom(n, C.Img.cells(ds), i, m, img.small(p, ds, er, es), b))

# a module that halts with 1 runs out of memory
def nof.halt(+i: List<&2, U32>, +m: U32, -o: List<&2, U32>,
  s: &f:Nat -> {C.Wasm.run(f, C.Compiler.halt(1), i, m) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}) ->
  &f:Nat -> Or({C.Wasm.run(f, C.Compiler.halt(1), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome},
    {C.Wasm.run(f, C.Compiler.halt(1), i, m) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}):
  (+f, ef) = s
  (f, Inr{ef})

def nof.of(+p: List<&2, U32>, +i: List<&2, U32>, +n: Nat, +o: List<&2, U32>, +m: U32, small: Bool,
  r: Maybe<List<&2, C.Def>>) ->
  {C.Img.small(p, 0) == small : Bool} -> {C.Book.read(p) == r : Maybe<List<&2, C.Def>>} ->
  {C.Program.gives.of(r, i, n) == Some{o} : Maybe<&2, List<&2, U32>>} ->
  &f:Nat -> Or({C.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, small, r), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome},
    {C.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, small, r), i, m) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}):
  match small r:
    case False{} _:
      es => er => e => nof.halt(i, m, o, halt.oom(i, m))
    case True{} None{}:
      es => er => e => Empty.absurd(
        &f:Nat -> Or({C.Wasm.run(f, C.Compiler.halt(2), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome},
          {C.Wasm.run(f, C.Compiler.halt(2), i, m) == C.Wasm.Outcome.out_of_memory{} : C.Wasm.Outcome}),
        gives.none(o, e))
    case True{} Some{+ds}:
      +es => +er => e => nof.machine(p, ds, i, m, o, er, es, mach.complete(p, ds, i, m, n, o, er, es, e))

def S.no_other_failure(p, i, n, o, m, e):
  nof.of(p, i, n, o, m, C.Img.small(p, 0), C.Book.read(p))({==}, {==}, e)

# enough_memory: a book of 2^26 bytes or more asks more memory than a module
# can have; for one that the compiler reads, B then A
def em.result(+ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +o: List<&2, U32>,
  s: &f:Nat -> {C.Wasm.run(f, C.Compiler.module(C.Img.cells(ds)), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome}) ->
  &f:Nat -> {C.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, True{}, Some{ds}), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome}:
  (+f, ef) = s
  (f, run.machine(f, ds, i, m, C.Wasm.Outcome.result{o}, ef))

def em.machine(+p: List<&2, U32>, +ds: List<&2, C.Def>, +i: List<&2, U32>, +m: U32, +o: List<&2, U32>,
  +er: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  +es: {C.Img.small(p, 0) == True{} : Bool},
  s: &n:Nat -> {C.Cir.result(n, C.Mach.code(), C.Mach.regs(), C.Img.cells(ds), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome}) ->
  &f:Nat -> {C.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, True{}, Some{ds}), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome}:
  (+n, en) = s
  em.result(ds, i, m, o, mach_wasm.result(n, C.Img.cells(ds), i, m, o, img.small(p, ds, er, es), en))

def em.of(+p: List<&2, U32>, +i: List<&2, U32>, +n: Nat, +o: List<&2, U32>, +m: U32, small: Bool,
  r: Maybe<List<&2, C.Def>>) ->
  {C.Img.small(p, 0) == small : Bool} -> {C.Book.read(p) == r : Maybe<List<&2, C.Def>>} ->
  {C.Program.gives.of(r, i, n) == Some{o} : Maybe<&2, List<&2, U32>>} ->
  {Nat.is_le(C.Program.need(p, i, n), C.Program.memory(m)) == True{} : Bool} ->
  &f:Nat -> {C.Wasm.run(f, C.Compiler.compile.of(C.Compiler.module, small, r), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome}:
  match small r:
    case False{} _:
      es => er => e => big => Empty.absurd(
        &f:Nat -> {C.Wasm.run(f, C.Compiler.halt(1), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome},
        need.big(p, i, n, m, es, big))
    case True{} None{}:
      es => er => e => big => Empty.absurd(
        &f:Nat -> {C.Wasm.run(f, C.Compiler.halt(2), i, m) == C.Wasm.Outcome.result{o} : C.Wasm.Outcome},
        gives.none(o, e))
    case True{} Some{+ds}:
      +es => +er => e => big => em.machine(p, ds, i, m, o, er, es, mach.memory(p, ds, i, m, n, o, er, es, e, big))

def S.enough_memory(p, i, n, o, m, e, big):
  em.of(p, i, n, o, m, C.Img.small(p, 0), C.Book.read(p))({==}, {==}, e, big)
