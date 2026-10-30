import Base
import ../source/impl.bend as Source
import ../machine/impl.bend as Machine
import ../fun/impl.bend as Fun

# The machine in F
# ================
#
# The machine (step 3) as an F program, and its data as F values. code.bend
# holds the program; spec.bend states that it computes what the machine
# computes.
#
# The encoding of a constructor with the tag t: the number t when it has no
# field; {t, a, z} with one field a; {t, a, b} with two; {t, a, {0, b, c}} with
# three. Each type numbers its constructors from 0, in the order of its
# definition; a list is Nil (0) or Con (1), a Maybe None (0) or Some (1), and
# a Bool False (0) or True (1). A def keeps its name and body: no step of the
# machine reads its type.

# Encodings
# =========

def Enc.p(a: Fun.V, b: Fun.V) -> Fun.V:
  Fun.V.n{0n, a, b}

def Enc.one(t: Nat, a: Fun.V) -> Fun.V:
  Fun.V.n{t, a, Fun.V.z{}}

def Enc.nat(n: Nat) -> Fun.V:
  Fun.V.num(n)

def Enc.bool(b: Bool) -> Fun.V:
  match b:
    case False{}:
      Fun.V.num(0n)
    case True{}:
      Fun.V.num(1n)

def Enc.name(k: List<&2, Nat>) -> Fun.V:
  match k:
    case Nil{}:
      Fun.V.num(0n)
    case Con{x, rest}:
      Fun.V.n{1n, Enc.nat(x), Enc.name(rest)}

def Enc.names(ks: List<&2, List<&2, Nat>>) -> Fun.V:
  match ks:
    case Nil{}:
      Fun.V.num(0n)
    case Con{k, rest}:
      Fun.V.n{1n, Enc.name(k), Enc.names(rest)}

def Enc.quan(q: Source.Quan) -> Fun.V:
  match q:
    case Source.Q0{}:
      Fun.V.num(0n)
    case Source.Q1{}:
      Fun.V.num(1n)
    case Source.Q2{}:
      Fun.V.num(2n)

def Enc.term(t: Source.Term) -> Fun.V:
  match t:
    case Source.Term.Var{i}:
      Enc.one(0n, Enc.nat(i))
    case Source.Term.Ref{k}:
      Enc.one(1n, Enc.name(k))
    case Source.Term.Ann{x, a}:
      Fun.V.n{2n, Enc.term(x), Enc.term(a)}
    case Source.Term.Let{q, v, f}:
      Fun.V.n{3n, Enc.quan(q), Enc.p(Enc.term(v), Enc.term(f))}
    case Source.Term.Typ{q}:
      Enc.one(4n, Enc.term(q))
    case Source.Term.Min{a, b}:
      Fun.V.n{5n, Enc.term(a), Enc.term(b)}
    case Source.Term.All{q, a, b}:
      Fun.V.n{6n, Enc.quan(q), Enc.p(Enc.term(a), Enc.term(b))}
    case Source.Term.Lam{q, f}:
      Fun.V.n{7n, Enc.quan(q), Enc.term(f)}
    case Source.Term.App{q, f, x}:
      Fun.V.n{8n, Enc.quan(q), Enc.p(Enc.term(f), Enc.term(x))}
    case Source.Term.Sig{q, a, b}:
      Fun.V.n{9n, Enc.quan(q), Enc.p(Enc.term(a), Enc.term(b))}
    case Source.Term.Tup{q, a, b}:
      Fun.V.n{10n, Enc.quan(q), Enc.p(Enc.term(a), Enc.term(b))}
    case Source.Term.Prj{h}:
      Enc.one(11n, Enc.term(h))
    case Source.Term.Enu{ks}:
      Enc.one(12n, Enc.names(ks))
    case Source.Term.Lab{k}:
      Enc.one(13n, Enc.name(k))
    case Source.Term.Mat{k, h, m}:
      Fun.V.n{14n, Enc.name(k), Enc.p(Enc.term(h), Enc.term(m))}
    case Source.Term.Efq{}:
      Fun.V.num(15n)
    case Source.Term.Eql{a, b, x}:
      Fun.V.n{16n, Enc.term(a), Enc.p(Enc.term(b), Enc.term(x))}
    case Source.Term.Rfl{}:
      Fun.V.num(17n)
    case Source.Term.Rwt{e, p, f}:
      Fun.V.n{18n, Enc.term(e), Enc.p(Enc.term(p), Enc.term(f))}

def Enc.terms(ts: List<&2, Source.Term>) -> Fun.V:
  match ts:
    case Nil{}:
      Fun.V.num(0n)
    case Con{t, rest}:
      Fun.V.n{1n, Enc.term(t), Enc.terms(rest)}

def Enc.def(d: Source.Def) -> Fun.V:
  match d:
    case Source.Def{k, t, v, o}:
      Fun.V.n{0n, Enc.name(k), Enc.term(v)}

def Enc.book(bk: List<&2, Source.Def>) -> Fun.V:
  match bk:
    case Nil{}:
      Fun.V.num(0n)
    case Con{d, rest}:
      Fun.V.n{1n, Enc.def(d), Enc.book(rest)}

def Enc.mdef(m: Maybe<&2, Source.Def>) -> Fun.V:
  match m:
    case None{}:
      Fun.V.num(0n)
    case Some{d}:
      Enc.one(1n, Enc.def(d))

def Enc.val(v: Machine.Val) -> Fun.V:
  match v:
    case Machine.Val.nil{}:
      Fun.V.num(0n)
    case Machine.Val.env{x, rest}:
      Fun.V.n{1n, Enc.val(x), Enc.val(rest)}
    case Machine.Val.arg{q, x, rest}:
      Fun.V.n{2n, Enc.quan(q), Enc.p(Enc.val(x), Enc.val(rest))}
    case Machine.Val.clo{t, e}:
      Fun.V.n{3n, Enc.term(t), Enc.val(e)}
    case Machine.Val.lab{k}:
      Enc.one(4n, Enc.name(k))
    case Machine.Val.rfl{}:
      Fun.V.num(5n)
    case Machine.Val.tup{q, a, b}:
      Fun.V.n{6n, Enc.quan(q), Enc.p(Enc.val(a), Enc.val(b))}
    case Machine.Val.call{k, xs}:
      Fun.V.n{7n, Enc.name(k), Enc.val(xs)}

def Enc.fr(f: Machine.Fr) -> Fun.V:
  match f:
    case Machine.Fr.arg{q, x}:
      Fun.V.n{0n, Enc.quan(q), Enc.val(x)}
    case Machine.Fr.fun{q, g}:
      Fun.V.n{1n, Enc.quan(q), Enc.val(g)}
    case Machine.Fr.let{q, g, e}:
      Fun.V.n{2n, Enc.quan(q), Enc.p(Enc.term(g), Enc.val(e))}
    case Machine.Fr.fst{q, b, e}:
      Fun.V.n{3n, Enc.quan(q), Enc.p(Enc.term(b), Enc.val(e))}
    case Machine.Fr.snd{q, a}:
      Fun.V.n{4n, Enc.quan(q), Enc.val(a)}
    case Machine.Fr.rwt{p, g, e}:
      Fun.V.n{5n, Enc.term(p), Enc.p(Enc.term(g), Enc.val(e))}
    case Machine.Fr.min1{b, e}:
      Fun.V.n{6n, Enc.term(b), Enc.val(e)}
    case Machine.Fr.min2{a}:
      Enc.one(7n, Enc.val(a))

def Enc.frs(fs: List<&2, Machine.Fr>) -> Fun.V:
  match fs:
    case Nil{}:
      Fun.V.num(0n)
    case Con{f, rest}:
      Fun.V.n{1n, Enc.fr(f), Enc.frs(rest)}

def Enc.st(s: Machine.St) -> Fun.V:
  match s:
    case Machine.St.eval{t, e, fs}:
      Fun.V.n{0n, Enc.term(t), Enc.p(Enc.val(e), Enc.frs(fs))}
    case Machine.St.ret{v, fs}:
      Fun.V.n{1n, Enc.val(v), Enc.frs(fs)}

def Enc.move(m: Machine.Move) -> Fun.V:
  match m:
    case Machine.Move.go{s}:
      Enc.one(0n, Enc.st(s))
    case Machine.Move.done{v}:
      Enc.one(1n, Enc.val(v))
    case Machine.Move.stuck{}:
      Fun.V.num(2n)

def Enc.leaf(l: Machine.Leaf) -> Fun.V:
  match l:
    case Machine.Leaf.need{}:
      Fun.V.num(0n)
    case Machine.Leaf.at{t, e, xs}:
      Fun.V.n{1n, Enc.term(t), Enc.p(Enc.val(e), Enc.val(xs))}
    case Machine.Leaf.fail{}:
      Fun.V.num(2n)

def Enc.look(l: Machine.Look) -> Fun.V:
  match l:
    case Machine.Look.val{v}:
      Enc.one(0n, Enc.val(v))
    case Machine.Look.free{j}:
      Enc.one(1n, Enc.nat(j))

def Enc.form(f: Machine.Form) -> Fun.V:
  match f:
    case Machine.Form.tup{r, a, b}:
      Fun.V.n{0n, Enc.quan(r), Enc.p(Enc.val(a), Enc.val(b))}
    case Machine.Form.lab{k}:
      Enc.one(1n, Enc.name(k))
    case Machine.Form.other{}:
      Fun.V.num(2n)

def Enc.obs(o: Source.Obs) -> Fun.V:
  match o:
    case Source.Obs.lab{k}:
      Enc.one(0n, Enc.name(k))
    case Source.Obs.rfl{}:
      Fun.V.num(1n)
    case Source.Obs.tup{a, b}:
      Fun.V.n{2n, Enc.obs(a), Enc.obs(b)}
    case Source.Obs.tup0{b}:
      Enc.one(3n, Enc.obs(b))

def Enc.mobs(m: Maybe<&2, Source.Obs>) -> Fun.V:
  match m:
    case None{}:
      Fun.V.num(0n)
    case Some{o}:
      Enc.one(1n, Enc.obs(o))

def Enc.mnat(m: Maybe<&2, Nat>) -> Fun.V:
  match m:
    case None{}:
      Fun.V.num(0n)
    case Some{n}:
      Enc.one(1n, Enc.nat(n))

def Enc.mname(m: Maybe<&2, List<&2, Nat>>) -> Fun.V:
  match m:
    case None{}:
      Fun.V.num(0n)
    case Some{k}:
      Enc.one(1n, Enc.name(k))
