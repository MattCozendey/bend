import Base
import ./impl.bend as Source

# Source laws
# ===========
#
# The kernel's run-time relations, copied rule by rule from bend2/bendtt.lean
# (Evaluation), and the laws of Step.lean that tie the meaning's step to them.
# A person reviews the relations against the kernel; proof.bend proves the
# laws. Each rule states its terms as equalities (et, eu, ex, eo). Walk drops
# the kernel's book parameter, which no rule of Walk reads.

# Relations
# =========

# Data: the live part holds labels, proofs and pairs, no λ, no call
type Term.Data<-t: Source.Term> is Type:
  Term.Data.lab{k: List<&2, Nat>, et: {t == Source.Term.Lab{k} : Source.Term}}
  Term.Data.rfl{et: {t == Source.Term.Rfl{} : Source.Term}}
  Term.Data.tup{q: Source.Quan, a: Source.Term, b: Source.Term,
    da: {Source.Quan.live(q) == True{} : Bool} -> Term.Data<a>, db: Term.Data<b>,
    et: {t == Source.Term.Tup{q, a, b} : Source.Term}}

# Walk: a def's case tree walked on a spine, with an environment e for the
# variables its λs bind: some leaf (under e, on the rest of the spine) when it
# leaves the tree, none when it needs more arguments
type Term.Walk<-t: Source.Term, -e: List<&2, Source.Term>, -xs: List<&2, Source.Arg>,
  -o: Maybe<&2, Source.Term>> is Type:
  Term.Walk.lam{p: Source.Quan, q: Source.Quan, f: Source.Term, x: Source.Term,
    rest: List<&2, Source.Arg>,
    l: {Source.Quan.live(p) == Source.Quan.live(q) : Bool},
    d: {p == Source.Q2{} : Source.Quan} -> Term.Data<x>,
    w: Term.Walk<f, Con{x, e}, rest, o>,
    et: {t == Source.Term.Lam{p, f} : Source.Term},
    ex: {xs == Con{Source.Arg{q, x}, rest} : List<&2, Source.Arg>}}
  Term.Walk.prj{q: Source.Quan, r: Source.Quan, h: Source.Term, a: Source.Term, b: Source.Term,
    rest: List<&2, Source.Arg>,
    l: {Source.Quan.live(q) == True{} : Bool},
    w: Term.Walk<h, e, Con{Source.Arg{Source.Quan.fld(r, q), a}, Con{Source.Arg{q, b}, rest}}, o>,
    et: {t == Source.Term.Prj{h} : Source.Term},
    ex: {xs == Con{Source.Arg{q, Source.Term.Tup{r, a, b}}, rest} : List<&2, Source.Arg>}}
  Term.Walk.hit{q: Source.Quan, k: List<&2, Nat>, h: Source.Term, m: Source.Term,
    rest: List<&2, Source.Arg>,
    l: {Source.Quan.live(q) == True{} : Bool},
    w: Term.Walk<h, e, rest, o>,
    et: {t == Source.Term.Mat{k, h, m} : Source.Term},
    ex: {xs == Con{Source.Arg{q, Source.Term.Lab{k}}, rest} : List<&2, Source.Arg>}}
  Term.Walk.miss{q: Source.Quan, j: List<&2, Nat>, k: List<&2, Nat>, h: Source.Term,
    m: Source.Term, rest: List<&2, Source.Arg>,
    l: {Source.Quan.live(q) == True{} : Bool},
    n: {j == k : List<&2, Nat>} -> Empty,
    w: Term.Walk<m, e, Con{Source.Arg{q, Source.Term.Lab{j}}, rest}, o>,
    et: {t == Source.Term.Mat{k, h, m} : Source.Term},
    ex: {xs == Con{Source.Arg{q, Source.Term.Lab{j}}, rest} : List<&2, Source.Arg>}}
  Term.Walk.app{q: Source.Quan, f: Source.Term, v: Nat,
    n: {Source.Term.node(Source.Term.App{q, f, Source.Term.Var{v}}) == True{} : Bool},
    w: Term.Walk<f, e, Con{Source.Arg{q, Source.Env.sub(e, v)}, xs}, o>,
    et: {t == Source.Term.App{q, f, Source.Term.Var{v}} : Source.Term}}
  Term.Walk.need{
    n: {Source.Term.takes(t) == True{} : Bool},
    ex: {xs == Nil{} : List<&2, Source.Arg>},
    eo: {o == None{} : Maybe<&2, Source.Term>}}
  Term.Walk.done{
    n: {Source.Term.node(t) == False{} : Bool},
    eo: {o == Some{Source.Term.spine(xs, Source.Term.sub(t, 0n, Source.Sub.env{e}))} :
      Maybe<&2, Source.Term>}}

# Value: a term that Eval does not step and that is not stuck
type Term.Value<-bk: List<&2, Source.Def>, -t: Source.Term> is Type:
  Term.Value.lam{q: Source.Quan, f: Source.Term, et: {t == Source.Term.Lam{q, f} : Source.Term}}
  Term.Value.prj{h: Source.Term, et: {t == Source.Term.Prj{h} : Source.Term}}
  Term.Value.mat{k: List<&2, Nat>, h: Source.Term, m: Source.Term,
    et: {t == Source.Term.Mat{k, h, m} : Source.Term}}
  Term.Value.efq{et: {t == Source.Term.Efq{} : Source.Term}}
  Term.Value.lab{k: List<&2, Nat>, et: {t == Source.Term.Lab{k} : Source.Term}}
  Term.Value.rfl{et: {t == Source.Term.Rfl{} : Source.Term}}
  Term.Value.typ{q: Source.Term, et: {t == Source.Term.Typ{q} : Source.Term}}
  Term.Value.all{q: Source.Quan, a: Source.Term, b: Source.Term,
    et: {t == Source.Term.All{q, a, b} : Source.Term}}
  Term.Value.sig{q: Source.Quan, a: Source.Term, b: Source.Term,
    et: {t == Source.Term.Sig{q, a, b} : Source.Term}}
  Term.Value.enu{ks: List<&2, List<&2, Nat>>, et: {t == Source.Term.Enu{ks} : Source.Term}}
  Term.Value.eql{a: Source.Term, b: Source.Term, c: Source.Term,
    et: {t == Source.Term.Eql{a, b, c} : Source.Term}}
  Term.Value.tup{q: Source.Quan, a: Source.Term, b: Source.Term,
    va: {Source.Quan.live(q) == True{} : Bool} -> Term.Value<bk, a>, vb: Term.Value<bk, b>,
    et: {t == Source.Term.Tup{q, a, b} : Source.Term}}
  Term.Value.call{k: List<&2, Nat>, d: Source.Def, xs: List<&2, Source.Arg>,
    g: {Source.Book.get(bk, k) == Some{d} : Maybe<&2, Source.Def>},
    vs: Term.Values<bk, xs>,
    w: Term.Walk<Source.Def.body(d), [], xs, None{}>,
    et: {t == Source.Term.spine(xs, Source.Term.Ref{k}) : Source.Term}}

# Values: every live argument is a value
type Term.Values<-bk: List<&2, Source.Def>, -xs: List<&2, Source.Arg>> is Type:
  Term.Values.nil{ex: {xs == Nil{} : List<&2, Source.Arg>}}
  Term.Values.cons{q: Source.Quan, x: Source.Term, rest: List<&2, Source.Arg>,
    v: {Source.Quan.live(q) == True{} : Bool} -> Term.Value<bk, x>, vs: Term.Values<bk, rest>,
    ex: {xs == Con{Source.Arg{q, x}, rest} : List<&2, Source.Arg>}}

# Eval: call-by-value evaluation of the live part
type Term.Eval<-bk: List<&2, Source.Def>, -t: Source.Term, -u: Source.Term> is Type:
  Term.Eval.ann{x: Source.Term, a: Source.Term,
    et: {t == Source.Term.Ann{x, a} : Source.Term}, eu: {u == x : Source.Term}}
  Term.Eval.app_f{q: Source.Quan, f: Source.Term, g: Source.Term, x: Source.Term,
    s: Term.Eval<bk, f, g>,
    et: {t == Source.Term.App{q, f, x} : Source.Term},
    eu: {u == Source.Term.App{q, g, x} : Source.Term}}
  Term.Eval.app_x{q: Source.Quan, f: Source.Term, x: Source.Term, y: Source.Term,
    v: Term.Value<bk, f>, l: {Source.Quan.live(q) == True{} : Bool}, s: Term.Eval<bk, x, y>,
    et: {t == Source.Term.App{q, f, x} : Source.Term},
    eu: {u == Source.Term.App{q, f, y} : Source.Term}}
  Term.Eval.beta{q: Source.Quan, p: Source.Quan, f: Source.Term, x: Source.Term,
    l: {Source.Quan.live(p) == Source.Quan.live(q) : Bool},
    v: {Source.Quan.live(q) == True{} : Bool} -> Term.Value<bk, x>,
    d: {p == Source.Q2{} : Source.Quan} -> Term.Data<x>,
    et: {t == Source.Term.App{q, Source.Term.Lam{p, f}, x} : Source.Term},
    eu: {u == Source.Term.sub(f, 0n, Source.Sub.one{x}) : Source.Term}}
  Term.Eval.split{q: Source.Quan, r: Source.Quan, h: Source.Term, a: Source.Term, b: Source.Term,
    l: {Source.Quan.live(q) == True{} : Bool}, v: Term.Value<bk, Source.Term.Tup{r, a, b}>,
    et: {t == Source.Term.App{q, Source.Term.Prj{h}, Source.Term.Tup{r, a, b}} : Source.Term},
    eu: {u == Source.Term.App{q, Source.Term.App{Source.Quan.fld(r, q), h, a}, b} : Source.Term}}
  Term.Eval.hit{q: Source.Quan, k: List<&2, Nat>, h: Source.Term, m: Source.Term,
    l: {Source.Quan.live(q) == True{} : Bool},
    et: {t == Source.Term.App{q, Source.Term.Mat{k, h, m}, Source.Term.Lab{k}} : Source.Term},
    eu: {u == h : Source.Term}}
  Term.Eval.miss{q: Source.Quan, j: List<&2, Nat>, k: List<&2, Nat>, h: Source.Term,
    m: Source.Term,
    l: {Source.Quan.live(q) == True{} : Bool}, n: {j == k : List<&2, Nat>} -> Empty,
    et: {t == Source.Term.App{q, Source.Term.Mat{k, h, m}, Source.Term.Lab{j}} : Source.Term},
    eu: {u == Source.Term.App{q, m, Source.Term.Lab{j}} : Source.Term}}
  Term.Eval.call{k: List<&2, Nat>, d: Source.Def, xs: List<&2, Source.Arg>,
    g: {Source.Book.get(bk, k) == Some{d} : Maybe<&2, Source.Def>},
    vs: Term.Values<bk, xs>,
    w: Term.Walk<Source.Def.body(d), [], xs, Some{u}>,
    et: {t == Source.Term.spine(xs, Source.Term.Ref{k}) : Source.Term}}
  Term.Eval.lett{q: Source.Quan, v: Source.Term, w: Source.Term, f: Source.Term,
    l: {Source.Quan.live(q) == True{} : Bool}, s: Term.Eval<bk, v, w>,
    et: {t == Source.Term.Let{q, v, f} : Source.Term},
    eu: {u == Source.Term.Let{q, w, f} : Source.Term}}
  Term.Eval.unlet{q: Source.Quan, v: Source.Term, f: Source.Term,
    l: {Source.Quan.live(q) == True{} : Bool} -> Term.Value<bk, v>,
    d: {q == Source.Q2{} : Source.Quan} -> Term.Data<v>,
    et: {t == Source.Term.Let{q, v, f} : Source.Term},
    eu: {u == Source.Term.sub(f, 0n, Source.Sub.one{v}) : Source.Term}}
  Term.Eval.tup_a{q: Source.Quan, a: Source.Term, c: Source.Term, b: Source.Term,
    l: {Source.Quan.live(q) == True{} : Bool}, s: Term.Eval<bk, a, c>,
    et: {t == Source.Term.Tup{q, a, b} : Source.Term},
    eu: {u == Source.Term.Tup{q, c, b} : Source.Term}}
  Term.Eval.tup_b{q: Source.Quan, a: Source.Term, b: Source.Term, c: Source.Term,
    v: {Source.Quan.live(q) == True{} : Bool} -> Term.Value<bk, a>, s: Term.Eval<bk, b, c>,
    et: {t == Source.Term.Tup{q, a, b} : Source.Term},
    eu: {u == Source.Term.Tup{q, a, c} : Source.Term}}
  Term.Eval.rwt{e: Source.Term, c: Source.Term, p: Source.Term, f: Source.Term,
    s: Term.Eval<bk, e, c>,
    et: {t == Source.Term.Rwt{e, p, f} : Source.Term},
    eu: {u == Source.Term.Rwt{c, p, f} : Source.Term}}
  Term.Eval.cast{p: Source.Term, f: Source.Term,
    et: {t == Source.Term.Rwt{Source.Term.Rfl{}, p, f} : Source.Term}, eu: {u == f : Source.Term}}
  Term.Eval.min_a{a: Source.Term, c: Source.Term, b: Source.Term, s: Term.Eval<bk, a, c>,
    et: {t == Source.Term.Min{a, b} : Source.Term},
    eu: {u == Source.Term.Min{c, b} : Source.Term}}
  Term.Eval.min_b{a: Source.Term, b: Source.Term, c: Source.Term,
    v: Term.Value<bk, a>, s: Term.Eval<bk, b, c>,
    et: {t == Source.Term.Min{a, b} : Source.Term},
    eu: {u == Source.Term.Min{a, c} : Source.Term}}
  Term.Eval.meet{i: List<&2, Nat>, j: List<&2, Nat>,
    li: {Source.Name.is_quan(i) == True{} : Bool}, lj: {Source.Name.is_quan(j) == True{} : Bool},
    et: {t == Source.Term.Min{Source.Term.Lab{i}, Source.Term.Lab{j}} : Source.Term},
    eu: {u == Source.Term.qmin(i, j) : Source.Term}}

# Evals: zero or more Eval steps, as Contract/Spec.lean has it
type Term.Evals<-bk: List<&2, Source.Def>, -t: Source.Term, -u: Source.Term> is Type:
  Term.Evals.refl{e: {t == u : Source.Term}}
  Term.Evals.step{m: Source.Term, s: Term.Eval<bk, t, m>, r: Term.Evals<bk, m, u>}

# Laws
# ====

# walk's result for o: Walk.need for none, Walk.done u for some u
def Walk.of(o: Maybe<&2, Source.Term>) -> Source.Walk:
  match o:
    case None{}:
      Source.Walk.need{}
    case Some{u}:
      Source.Walk.done{u}

# isData_iff, in its two directions
law Term.is_data_sound:
  for t: Source.Term
  for h: {Source.Term.is_data(t) == True{} : Bool}
  Term.Data<t>

law Term.is_data_complete:
  for t: Source.Term
  for d: Term.Data<t>
  {Source.Term.is_data(t) == True{} : Bool}

# walk_sound
law Term.walk_sound:
  for t: Source.Term
  for e: List<&2, Source.Term>
  for xs: List<&2, Source.Arg>
  for o: Maybe<&2, Source.Term>
  for h: {Source.Term.walk(t, e, xs) == Walk.of(o) : Source.Walk}
  Term.Walk<t, e, xs, o>

# walk_complete
law Term.walk_complete:
  for t: Source.Term
  for e: List<&2, Source.Term>
  for xs: List<&2, Source.Arg>
  for o: Maybe<&2, Source.Term>
  for w: Term.Walk<t, e, xs, o>
  {Source.Term.walk(t, e, xs) == Walk.of(o) : Source.Walk}

# isValue_iff, in its two directions
law Term.is_value_sound:
  for bk: List<&2, Source.Def>
  for t: Source.Term
  for h: {Source.Term.is_value(t, False{}, bk) == True{} : Bool}
  Term.Value<bk, t>

law Term.is_value_complete:
  for bk: List<&2, Source.Def>
  for t: Source.Term
  for v: Term.Value<bk, t>
  {Source.Term.is_value(t, False{}, bk) == True{} : Bool}

# step_sound
law Term.step_sound:
  for bk: List<&2, Source.Def>
  for t: Source.Term
  for u: Source.Term
  for h: {Source.Term.step(t, bk) == Some{u} : Maybe<&2, Source.Term>}
  Term.Eval<bk, t, u>

# step_complete
law Term.step_complete:
  for bk: List<&2, Source.Def>
  for t: Source.Term
  for u: Source.Term
  for s: Term.Eval<bk, t, u>
  for h: {Source.Term.step(t, bk) == None{} : Maybe<&2, Source.Term>}
  Empty

# stepUntil_some, at stop = isValue: a run's end is reached by Eval steps,
# and it is a value or no step fits there
law Term.run_sound:
  for n: Nat
  for bk: List<&2, Source.Def>
  for t: Source.Term
  for u: Source.Term
  for h: {Source.Term.run(n, t, bk) == Some{u} : Maybe<&2, Source.Term>}
  Term.Evals<bk, t, u> & (Term.Value<bk, u> | {Source.Term.step(u, bk) == None{} : Maybe<&2, Source.Term>})
