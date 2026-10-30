import Base
import ./impl.bend as Source
import ./spec.bend as Spec

# Source proofs
# =============
#
# The proofs of the laws of spec.bend, in the order of Step.lean. An induction
# on a relation goes through a helper whose term index is erased, as Bend's
# termination check reads the arguments from the left.

# Bools
# =====

def Bool.disc(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def Bool.no(h: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, h) : Bool.disc(_)
  Unit{}

def Empty.elim(-A: Type, e: Empty) -> A:
  match e:

# anything, from False == True
def Bool.absurd(-A: Type, h: {False{} == True{} : Bool}) -> A:
  Empty.elim(A, Bool.no(h))

# the left side of a true and
def Bool.and_left(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Bool.absurd({False{} == True{} : Bool}, h)

# the right side of a true and
def Bool.and_right(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Bool.absurd({b == True{} : Bool}, h)

def Bool.and_intro(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) ->
  {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

# Data
# ====

def Spec.Term.is_data_sound(t, h):
  match t:
    case Source.Term.Lab{k}:
      Spec.Term.Data.lab{k, {==}}
    case Source.Term.Rfl{}:
      Spec.Term.Data.rfl{{==}}
    case Source.Term.Tup{q, +a, +b}:
      match q:
        case Source.Q0{}:
          Spec.Term.Data.tup{Source.Q0{}, a, b, Unit{}, Spec.Term.is_data_sound(b, h), {==}}
        case Source.Q1{}:
          +g = h
          Spec.Term.Data.tup{Source.Q1{}, a, b,
            Spec.Term.is_data_sound(a, Bool.and_left(Source.Term.is_data(a), Source.Term.is_data(b), g)),
            Spec.Term.is_data_sound(b, Bool.and_right(Source.Term.is_data(a), Source.Term.is_data(b), g)),
            {==}}
        case Source.Q2{}:
          +g = h
          Spec.Term.Data.tup{Source.Q2{}, a, b,
            Spec.Term.is_data_sound(a, Bool.and_left(Source.Term.is_data(a), Source.Term.is_data(b), g)),
            Spec.Term.is_data_sound(b, Bool.and_right(Source.Term.is_data(a), Source.Term.is_data(b), g)),
            {==}}
    case Source.Term.Var{i}:
      Bool.absurd(Spec.Term.Data<Source.Term.Var{i}>, h)
    case Source.Term.Ref{k}:
      Bool.absurd(Spec.Term.Data<Source.Term.Ref{k}>, h)
    case Source.Term.Ann{x, a}:
      Bool.absurd(Spec.Term.Data<Source.Term.Ann{x, a}>, h)
    case Source.Term.Let{q, v, f}:
      Bool.absurd(Spec.Term.Data<Source.Term.Let{q, v, f}>, h)
    case Source.Term.Typ{q}:
      Bool.absurd(Spec.Term.Data<Source.Term.Typ{q}>, h)
    case Source.Term.Min{a, b}:
      Bool.absurd(Spec.Term.Data<Source.Term.Min{a, b}>, h)
    case Source.Term.All{q, a, b}:
      Bool.absurd(Spec.Term.Data<Source.Term.All{q, a, b}>, h)
    case Source.Term.Lam{q, f}:
      Bool.absurd(Spec.Term.Data<Source.Term.Lam{q, f}>, h)
    case Source.Term.App{q, f, x}:
      Bool.absurd(Spec.Term.Data<Source.Term.App{q, f, x}>, h)
    case Source.Term.Sig{q, a, b}:
      Bool.absurd(Spec.Term.Data<Source.Term.Sig{q, a, b}>, h)
    case Source.Term.Prj{x}:
      Bool.absurd(Spec.Term.Data<Source.Term.Prj{x}>, h)
    case Source.Term.Enu{ks}:
      Bool.absurd(Spec.Term.Data<Source.Term.Enu{ks}>, h)
    case Source.Term.Mat{k, x, m}:
      Bool.absurd(Spec.Term.Data<Source.Term.Mat{k, x, m}>, h)
    case Source.Term.Efq{}:
      Bool.absurd(Spec.Term.Data<Source.Term.Efq{}>, h)
    case Source.Term.Eql{a, b, c}:
      Bool.absurd(Spec.Term.Data<Source.Term.Eql{a, b, c}>, h)
    case Source.Term.Rwt{e, p, f}:
      Bool.absurd(Spec.Term.Data<Source.Term.Rwt{e, p, f}>, h)

def Term.is_data_complete.go(-t: Source.Term, d: Spec.Term.Data<t>) ->
  {Source.Term.is_data(t) == True{} : Bool}:
  match d:
    case Spec.Term.Data.lab{k, et}:
      %Equal.sym(Source.Term, t, Source.Term.Lab{k}, et) : {Source.Term.is_data(_) == True{} : Bool}
      {==}
    case Spec.Term.Data.rfl{et}:
      %Equal.sym(Source.Term, t, Source.Term.Rfl{}, et) : {Source.Term.is_data(_) == True{} : Bool}
      {==}
    case Spec.Term.Data.tup{q, a, b, da, db, et}:
      match q:
        case Source.Q0{}:
          %Equal.sym(Source.Term, t, Source.Term.Tup{Source.Q0{}, a, b}, et) :
            {Source.Term.is_data(_) == True{} : Bool}
          Term.is_data_complete.go(b, db)
        case Source.Q1{}:
          %Equal.sym(Source.Term, t, Source.Term.Tup{Source.Q1{}, a, b}, et) :
            {Source.Term.is_data(_) == True{} : Bool}
          Bool.and_intro(Source.Term.is_data(a), Source.Term.is_data(b),
            Term.is_data_complete.go(a, da), Term.is_data_complete.go(b, db))
        case Source.Q2{}:
          %Equal.sym(Source.Term, t, Source.Term.Tup{Source.Q2{}, a, b}, et) :
            {Source.Term.is_data(_) == True{} : Bool}
          Bool.and_intro(Source.Term.is_data(a), Source.Term.is_data(b),
            Term.is_data_complete.go(a, da), Term.is_data_complete.go(b, db))

def Spec.Term.is_data_complete(t, d):
  Term.is_data_complete.go(t, d)

# Nat and names
# =============

def Nat.cmp_self(a: Nat) -> {Nat.cmp(a, a) == EQ{} : Cmp}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.cmp_self(p)

def Nat.is_eq_self(a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  %Equal.sym(Cmp, Nat.cmp(a, a), EQ{}, Nat.cmp_self(a)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

def Nat.is_eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Bool.absurd({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      Bool.absurd({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, Nat.is_eq_true(p, q, h))

def Name.is_eq_self(a: List<&2, Nat>) -> {Source.Name.is_eq(a, a) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{x, xs}:
      %Equal.sym(Bool, Nat.is_eq(x, x), True{}, Nat.is_eq_self(x)) :
        {Bool.and(_, Source.Name.is_eq(xs, xs)) == True{} : Bool}
      Name.is_eq_self(xs)

def Name.cons_eq(-x: Nat, -y: Nat, -xs: List<&2, Nat>, -ys: List<&2, Nat>, ex: {x == y : Nat},
  e2: {xs == ys : List<&2, Nat>}) -> {Con{x, xs} == Con{y, ys} : List<&2, Nat>}:
  %ex : {Con{x, xs} == Con{_, ys} : List<&2, Nat>}
  %e2 : {Con{x, xs} == Con{x, _} : List<&2, Nat>}
  {==}

def Name.is_eq_true(a: List<&2, Nat>, b: List<&2, Nat>, h: {Source.Name.is_eq(a, b) == True{} : Bool}) ->
  {a == b : List<&2, Nat>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Con{+x, +xs} Con{+y, +ys}:
      +g = h
      Name.cons_eq(x, y, xs, ys,
        Nat.is_eq_true(x, y, Bool.and_left(Nat.is_eq(x, y), Source.Name.is_eq(xs, ys), g)),
        Name.is_eq_true(xs, ys, Bool.and_right(Nat.is_eq(x, y), Source.Name.is_eq(xs, ys), g)))
    case Nil{} Con{y, ys}:
      Bool.absurd({Nil{} == Con{y, ys} : List<&2, Nat>}, h)
    case Con{x, xs} Nil{}:
      Bool.absurd({Con{x, xs} == Nil{} : List<&2, Nat>}, h)

def Name.is_eq_false.of(-j: List<&2, Nat>, +k: List<&2, Nat>,
  y: {Source.Name.is_eq(j, k) == False{} : Bool}, e: {j == k : List<&2, Nat>}) -> Empty:
  Bool.no(Equal.trans(Bool, False{}, Source.Name.is_eq(k, k), True{},
    Equal.trans(Bool, False{}, Source.Name.is_eq(j, k), Source.Name.is_eq(k, k),
      Equal.sym(Bool, Source.Name.is_eq(j, k), False{}, y),
      Equal.cong(List<&2, Nat>, Bool, n => Source.Name.is_eq(n, k), j, k, e)),
    Name.is_eq_self(k)))

def Name.is_eq_false(-j: List<&2, Nat>, +k: List<&2, Nat>,
  y: {Source.Name.is_eq(j, k) == False{} : Bool}) -> {j == k : List<&2, Nat>} -> Empty:
  e => Name.is_eq_false.of(j, k, y, e)

# Choices
# =======

def Bool.is_eq_true(a: Bool, b: Bool, h: {Source.Bool.is_eq(a, b) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Bool.absurd({True{} == False{} : Bool}, h)
    case False{} True{}:
      Bool.absurd({False{} == True{} : Bool}, h)

# a case split on a lazy choice that gave r: R from either side
def Bool.lazy.by(-A: Type, -R: Type, c: Bool, -a: Unit -> A, -b: Unit -> A, -r: A,
  h: {Source.Bool.lazy(A, c, a, b) == r : A},
  yes: {c == True{} : Bool} -> {a(Unit{}) == r : A} -> R,
  no: {c == False{} : Bool} -> {b(Unit{}) == r : A} -> R) -> R:
  match c:
    case True{}:
      yes({==}, h)
    case False{}:
      no({==}, h)

# Walks
# =====

def Term.Data.when_of(p: Source.Quan, x: Source.Term,
  h: {Bool.or(Bool.not(Source.Quan.is_q2(p)), Source.Term.is_data(x)) == True{} : Bool}) ->
  Spec.Term.Data.when(Source.Quan.is_q2(p), x):
  match p:
    case Source.Q2{}:
      Spec.Term.is_data_sound(x, h)
    case Source.Q0{}:
      Unit{}
    case Source.Q1{}:
      Unit{}

def Walk.is_fail(w: Source.Walk) -> Bool:
  match w:
    case Source.Walk.fail{}:
      True{}
    case _:
      False{}

def Walk.term(w: Source.Walk) -> Source.Term:
  match w:
    case Source.Walk.done{t}:
      t
    case _:
      Source.Term.Rfl{}

def Walk.no_fail(o: Maybe<&2, Source.Term>, h: {Source.Walk.fail{} == Spec.Walk.of(o) : Source.Walk}) ->
  Empty:
  match o:
    case None{}:
      Bool.no(Equal.sym(Bool, True{}, False{},
        Equal.cong(Source.Walk, Bool, Walk.is_fail, Source.Walk.fail{}, Source.Walk.need{}, h)))
    case Some{u}:
      Bool.no(Equal.sym(Bool, True{}, False{},
        Equal.cong(Source.Walk, Bool, Walk.is_fail, Source.Walk.fail{}, Source.Walk.done{u}, h)))

def Walk.of_need(o: Maybe<&2, Source.Term>, h: {Source.Walk.need{} == Spec.Walk.of(o) : Source.Walk}) ->
  {o == None{} : Maybe<&2, Source.Term>}:
  match o:
    case None{}:
      {==}
    case Some{u}:
      Bool.absurd({Some{u} == None{} : Maybe<&2, Source.Term>}, Equal.sym(Bool, True{}, False{},
        Equal.cong(Source.Walk, Bool, Source.Walk.is_need, Source.Walk.need{}, Source.Walk.done{u}, h)))

def Walk.of_done(o: Maybe<&2, Source.Term>, -u: Source.Term,
  h: {Source.Walk.done{u} == Spec.Walk.of(o) : Source.Walk}) -> {o == Some{u} : Maybe<&2, Source.Term>}:
  match o:
    case None{}:
      Bool.absurd({None{} == Some{u} : Maybe<&2, Source.Term>},
        Equal.cong(Source.Walk, Bool, Source.Walk.is_need, Source.Walk.done{u}, Source.Walk.need{}, h))
    case Some{v}:
      Equal.sym(Maybe<&2, Source.Term>, Some{u}, Some{v},
        Equal.cong(Source.Term, Maybe<&2, Source.Term>, x => Some{x}, u, v,
          Equal.cong(Source.Walk, Source.Term, Walk.term, Source.Walk.done{u}, Source.Walk.done{v}, h)))

def Term.walk_sound.hit(q: Source.Quan, -j: List<&2, Nat>, k: List<&2, Nat>, hh: Source.Term,
  m: Source.Term, -e: List<&2, Source.Term>, rest: List<&2, Source.Arg>, -o: Maybe<&2, Source.Term>,
  c: {Source.Quan.live(q) == True{} : Bool}, ejk: {j == k : List<&2, Nat>},
  w: Spec.Term.Walk<hh, e, rest, o>) ->
  Spec.Term.Walk<Source.Term.Mat{k, hh, m}, e, Con{Source.Arg{q, Source.Term.Lab{j}}, rest}, o>:
  Spec.Term.Walk.hit{q, k, hh, m, rest, c, w, {==},
    Equal.cong(List<&2, Nat>, List<&2, Source.Arg>, n => Con{Source.Arg{q, Source.Term.Lab{n}}, rest},
      j, k, ejk)}

# walk_sound, as Step.lean: by induction on t
def Term.walk_sound.go(t: Source.Term, +e: List<&2, Source.Term>, +xs: List<&2, Source.Arg>,
  +o: Maybe<&2, Source.Term>, h: {Source.Term.walk(t, e, xs) == Spec.Walk.of(o) : Source.Walk}) ->
  Spec.Term.Walk<t, e, xs, o>:
  match t:
    case Source.Term.Lam{+p, +f}:
      match xs:
        case Nil{}:
          Spec.Term.Walk.need{{==}, {==}, Walk.of_need(o, h)}
        case Con{Source.Arg{+q, +x}, +rest}:
          Bool.lazy.by(Source.Walk, Spec.Term.Walk<Source.Term.Lam{p, f}, e, Con{Source.Arg{q, x}, rest}, o>,
            Bool.and(Source.Bool.is_eq(Source.Quan.live(p), Source.Quan.live(q)),
              Bool.or(Bool.not(Source.Quan.is_q2(p)), Source.Term.is_data(x))),
            u => Source.Term.walk(f, Con{x, e}, rest), u => Source.Walk.fail{}, Spec.Walk.of(o), h,
            +c => w => Spec.Term.Walk.lam{p, q, f, x, rest,
              Bool.is_eq_true(Source.Quan.live(p), Source.Quan.live(q),
                Bool.and_left(Source.Bool.is_eq(Source.Quan.live(p), Source.Quan.live(q)),
                  Bool.or(Bool.not(Source.Quan.is_q2(p)), Source.Term.is_data(x)), c)),
              Term.Data.when_of(p, x,
                Bool.and_right(Source.Bool.is_eq(Source.Quan.live(p), Source.Quan.live(q)),
                  Bool.or(Bool.not(Source.Quan.is_q2(p)), Source.Term.is_data(x)), c)),
              Term.walk_sound.go(f, Con{x, e}, rest, o, w), {==}, {==}},
            c => w => Empty.elim(Spec.Term.Walk<Source.Term.Lam{p, f}, e, Con{Source.Arg{q, x}, rest}, o>, Walk.no_fail(o, w)))
    case Source.Term.Prj{+hh}:
      match xs:
        case Nil{}:
          Spec.Term.Walk.need{{==}, {==}, Walk.of_need(o, h)}
        case Con{Source.Arg{+q, x}, +rest}:
          match x:
            case Source.Term.Tup{+r, +a, +b}:
              Bool.lazy.by(Source.Walk, Spec.Term.Walk<Source.Term.Prj{hh}, e, Con{Source.Arg{q, Source.Term.Tup{r, a, b}}, rest}, o>, Source.Quan.live(q),
                u => Source.Term.walk(hh, e, Con{Source.Arg{Source.Quan.fld(r, q), a},
                  Con{Source.Arg{q, b}, rest}}),
                u => Source.Walk.fail{}, Spec.Walk.of(o), h,
                c => w => Spec.Term.Walk.prj{q, r, hh, a, b, rest, c,
                  Term.walk_sound.go(hh, e, Con{Source.Arg{Source.Quan.fld(r, q), a},
                    Con{Source.Arg{q, b}, rest}}, o, w), {==}, {==}},
                c => w => Empty.elim(Spec.Term.Walk<Source.Term.Prj{hh}, e, Con{Source.Arg{q, Source.Term.Tup{r, a, b}}, rest}, o>, Walk.no_fail(o, w)))
            case Source.Term.Var{+z0}:
              Empty.elim(Spec.Term.Walk<Source.Term.Prj{hh}, e, Con{Source.Arg{q, Source.Term.Var{z0}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Ref{+z0}:
              Empty.elim(Spec.Term.Walk<Source.Term.Prj{hh}, e, Con{Source.Arg{q, Source.Term.Ref{z0}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Ann{+z0, +z1}:
              Empty.elim(Spec.Term.Walk<Source.Term.Prj{hh}, e, Con{Source.Arg{q, Source.Term.Ann{z0, z1}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Let{+z0, +z1, +z2}:
              Empty.elim(Spec.Term.Walk<Source.Term.Prj{hh}, e, Con{Source.Arg{q, Source.Term.Let{z0, z1, z2}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Typ{+z0}:
              Empty.elim(Spec.Term.Walk<Source.Term.Prj{hh}, e, Con{Source.Arg{q, Source.Term.Typ{z0}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Min{+z0, +z1}:
              Empty.elim(Spec.Term.Walk<Source.Term.Prj{hh}, e, Con{Source.Arg{q, Source.Term.Min{z0, z1}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.All{+z0, +z1, +z2}:
              Empty.elim(Spec.Term.Walk<Source.Term.Prj{hh}, e, Con{Source.Arg{q, Source.Term.All{z0, z1, z2}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Lam{+z0, +z1}:
              Empty.elim(Spec.Term.Walk<Source.Term.Prj{hh}, e, Con{Source.Arg{q, Source.Term.Lam{z0, z1}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.App{+z0, +z1, +z2}:
              Empty.elim(Spec.Term.Walk<Source.Term.Prj{hh}, e, Con{Source.Arg{q, Source.Term.App{z0, z1, z2}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Sig{+z0, +z1, +z2}:
              Empty.elim(Spec.Term.Walk<Source.Term.Prj{hh}, e, Con{Source.Arg{q, Source.Term.Sig{z0, z1, z2}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Prj{+z0}:
              Empty.elim(Spec.Term.Walk<Source.Term.Prj{hh}, e, Con{Source.Arg{q, Source.Term.Prj{z0}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Enu{+z0}:
              Empty.elim(Spec.Term.Walk<Source.Term.Prj{hh}, e, Con{Source.Arg{q, Source.Term.Enu{z0}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Lab{+z0}:
              Empty.elim(Spec.Term.Walk<Source.Term.Prj{hh}, e, Con{Source.Arg{q, Source.Term.Lab{z0}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Mat{+z0, +z1, +z2}:
              Empty.elim(Spec.Term.Walk<Source.Term.Prj{hh}, e, Con{Source.Arg{q, Source.Term.Mat{z0, z1, z2}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Efq{}:
              Empty.elim(Spec.Term.Walk<Source.Term.Prj{hh}, e, Con{Source.Arg{q, Source.Term.Efq{}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Eql{+z0, +z1, +z2}:
              Empty.elim(Spec.Term.Walk<Source.Term.Prj{hh}, e, Con{Source.Arg{q, Source.Term.Eql{z0, z1, z2}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Rfl{}:
              Empty.elim(Spec.Term.Walk<Source.Term.Prj{hh}, e, Con{Source.Arg{q, Source.Term.Rfl{}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Rwt{+z0, +z1, +z2}:
              Empty.elim(Spec.Term.Walk<Source.Term.Prj{hh}, e, Con{Source.Arg{q, Source.Term.Rwt{z0, z1, z2}}, rest}, o>, Walk.no_fail(o, h))
    case Source.Term.Mat{+k, +hh, +m}:
      match xs:
        case Nil{}:
          Spec.Term.Walk.need{{==}, {==}, Walk.of_need(o, h)}
        case Con{Source.Arg{+q, x}, +rest}:
          match x:
            case Source.Term.Lab{+j}:
              Bool.lazy.by(Source.Walk, Spec.Term.Walk<Source.Term.Mat{k, hh, m}, e, Con{Source.Arg{q, Source.Term.Lab{j}}, rest}, o>, Source.Quan.live(q),
                u => Source.Bool.lazy(Source.Walk, Source.Name.is_eq(j, k),
                  w => Source.Term.walk(hh, e, rest),
                  w => Source.Term.walk(m, e, Con{Source.Arg{q, Source.Term.Lab{j}}, rest})),
                u => Source.Walk.fail{}, Spec.Walk.of(o), h,
                +c => w => Bool.lazy.by(Source.Walk, Spec.Term.Walk<Source.Term.Mat{k, hh, m}, e, Con{Source.Arg{q, Source.Term.Lab{j}}, rest}, o>, Source.Name.is_eq(j, k),
                  z => Source.Term.walk(hh, e, rest),
                  z => Source.Term.walk(m, e, Con{Source.Arg{q, Source.Term.Lab{j}}, rest}),
                  Spec.Walk.of(o), w,
                  y => z => Term.walk_sound.hit(q, j, k, hh, m, e, rest, o, c,
                    Name.is_eq_true(j, k, y), Term.walk_sound.go(hh, e, rest, o, z)),
                  y => z => Spec.Term.Walk.miss{q, j, k, hh, m, rest, c, Name.is_eq_false(j, k, y),
                    Term.walk_sound.go(m, e, Con{Source.Arg{q, Source.Term.Lab{j}}, rest}, o, z),
                    {==}, {==}}),
                c => w => Empty.elim(Spec.Term.Walk<Source.Term.Mat{k, hh, m}, e, Con{Source.Arg{q, Source.Term.Lab{j}}, rest}, o>, Walk.no_fail(o, w)))
            case Source.Term.Var{+z0}:
              Empty.elim(Spec.Term.Walk<Source.Term.Mat{k, hh, m}, e, Con{Source.Arg{q, Source.Term.Var{z0}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Ref{+z0}:
              Empty.elim(Spec.Term.Walk<Source.Term.Mat{k, hh, m}, e, Con{Source.Arg{q, Source.Term.Ref{z0}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Ann{+z0, +z1}:
              Empty.elim(Spec.Term.Walk<Source.Term.Mat{k, hh, m}, e, Con{Source.Arg{q, Source.Term.Ann{z0, z1}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Let{+z0, +z1, +z2}:
              Empty.elim(Spec.Term.Walk<Source.Term.Mat{k, hh, m}, e, Con{Source.Arg{q, Source.Term.Let{z0, z1, z2}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Typ{+z0}:
              Empty.elim(Spec.Term.Walk<Source.Term.Mat{k, hh, m}, e, Con{Source.Arg{q, Source.Term.Typ{z0}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Min{+z0, +z1}:
              Empty.elim(Spec.Term.Walk<Source.Term.Mat{k, hh, m}, e, Con{Source.Arg{q, Source.Term.Min{z0, z1}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.All{+z0, +z1, +z2}:
              Empty.elim(Spec.Term.Walk<Source.Term.Mat{k, hh, m}, e, Con{Source.Arg{q, Source.Term.All{z0, z1, z2}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Lam{+z0, +z1}:
              Empty.elim(Spec.Term.Walk<Source.Term.Mat{k, hh, m}, e, Con{Source.Arg{q, Source.Term.Lam{z0, z1}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.App{+z0, +z1, +z2}:
              Empty.elim(Spec.Term.Walk<Source.Term.Mat{k, hh, m}, e, Con{Source.Arg{q, Source.Term.App{z0, z1, z2}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Sig{+z0, +z1, +z2}:
              Empty.elim(Spec.Term.Walk<Source.Term.Mat{k, hh, m}, e, Con{Source.Arg{q, Source.Term.Sig{z0, z1, z2}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Tup{+z0, +z1, +z2}:
              Empty.elim(Spec.Term.Walk<Source.Term.Mat{k, hh, m}, e, Con{Source.Arg{q, Source.Term.Tup{z0, z1, z2}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Prj{+z0}:
              Empty.elim(Spec.Term.Walk<Source.Term.Mat{k, hh, m}, e, Con{Source.Arg{q, Source.Term.Prj{z0}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Enu{+z0}:
              Empty.elim(Spec.Term.Walk<Source.Term.Mat{k, hh, m}, e, Con{Source.Arg{q, Source.Term.Enu{z0}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Mat{+z0, +z1, +z2}:
              Empty.elim(Spec.Term.Walk<Source.Term.Mat{k, hh, m}, e, Con{Source.Arg{q, Source.Term.Mat{z0, z1, z2}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Efq{}:
              Empty.elim(Spec.Term.Walk<Source.Term.Mat{k, hh, m}, e, Con{Source.Arg{q, Source.Term.Efq{}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Eql{+z0, +z1, +z2}:
              Empty.elim(Spec.Term.Walk<Source.Term.Mat{k, hh, m}, e, Con{Source.Arg{q, Source.Term.Eql{z0, z1, z2}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Rfl{}:
              Empty.elim(Spec.Term.Walk<Source.Term.Mat{k, hh, m}, e, Con{Source.Arg{q, Source.Term.Rfl{}}, rest}, o>, Walk.no_fail(o, h))
            case Source.Term.Rwt{+z0, +z1, +z2}:
              Empty.elim(Spec.Term.Walk<Source.Term.Mat{k, hh, m}, e, Con{Source.Arg{q, Source.Term.Rwt{z0, z1, z2}}, rest}, o>, Walk.no_fail(o, h))
    case Source.Term.Efq{}:
      match xs:
        case Nil{}:
          Spec.Term.Walk.need{{==}, {==}, Walk.of_need(o, h)}
        case Con{a, rest}:
          Empty.elim(Spec.Term.Walk<Source.Term.Efq{}, e, Con{a, rest}, o>, Walk.no_fail(o, h))
    case Source.Term.App{+q, +f, x}:
      match x:
        case Source.Term.Var{+v}:
          Bool.lazy.by(Source.Walk, Spec.Term.Walk<Source.Term.App{q, f, Source.Term.Var{v}}, e, xs, o>,
            Source.Spine.head.takes(Source.Term.unspine(f, [])),
            u => Source.Term.walk(f, e, Con{Source.Arg{q, Source.Env.sub(e, v)}, xs}),
            u => Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(Source.Term.App{q, f,
              Source.Term.Var{v}}, 0n, Source.Sub.env{e}))},
            Spec.Walk.of(o), h,
            c => w => Spec.Term.Walk.app{q, f, v, c,
              Term.walk_sound.go(f, e, Con{Source.Arg{q, Source.Env.sub(e, v)}, xs}, o, w), {==}},
            c => w => Spec.Term.Walk.done{c, Walk.of_done(o, Source.Term.spine(xs,
              Source.Term.sub(Source.Term.App{q, f, Source.Term.Var{v}}, 0n, Source.Sub.env{e})), w)})
        case Source.Term.Ref{+z0}:
          Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.App{q, f, Source.Term.Ref{z0}}, 0n,
            Source.Sub.env{e})), h)}
        case Source.Term.Ann{+z0, +z1}:
          Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.App{q, f, Source.Term.Ann{z0, z1}}, 0n,
            Source.Sub.env{e})), h)}
        case Source.Term.Let{+z0, +z1, +z2}:
          Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.App{q, f, Source.Term.Let{z0, z1, z2}}, 0n,
            Source.Sub.env{e})), h)}
        case Source.Term.Typ{+z0}:
          Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.App{q, f, Source.Term.Typ{z0}}, 0n,
            Source.Sub.env{e})), h)}
        case Source.Term.Min{+z0, +z1}:
          Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.App{q, f, Source.Term.Min{z0, z1}}, 0n,
            Source.Sub.env{e})), h)}
        case Source.Term.All{+z0, +z1, +z2}:
          Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.App{q, f, Source.Term.All{z0, z1, z2}}, 0n,
            Source.Sub.env{e})), h)}
        case Source.Term.Lam{+z0, +z1}:
          Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.App{q, f, Source.Term.Lam{z0, z1}}, 0n,
            Source.Sub.env{e})), h)}
        case Source.Term.App{+z0, +z1, +z2}:
          Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.App{q, f, Source.Term.App{z0, z1, z2}}, 0n,
            Source.Sub.env{e})), h)}
        case Source.Term.Sig{+z0, +z1, +z2}:
          Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.App{q, f, Source.Term.Sig{z0, z1, z2}}, 0n,
            Source.Sub.env{e})), h)}
        case Source.Term.Tup{+z0, +z1, +z2}:
          Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.App{q, f, Source.Term.Tup{z0, z1, z2}}, 0n,
            Source.Sub.env{e})), h)}
        case Source.Term.Prj{+z0}:
          Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.App{q, f, Source.Term.Prj{z0}}, 0n,
            Source.Sub.env{e})), h)}
        case Source.Term.Enu{+z0}:
          Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.App{q, f, Source.Term.Enu{z0}}, 0n,
            Source.Sub.env{e})), h)}
        case Source.Term.Lab{+z0}:
          Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.App{q, f, Source.Term.Lab{z0}}, 0n,
            Source.Sub.env{e})), h)}
        case Source.Term.Mat{+z0, +z1, +z2}:
          Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.App{q, f, Source.Term.Mat{z0, z1, z2}}, 0n,
            Source.Sub.env{e})), h)}
        case Source.Term.Efq{}:
          Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.App{q, f, Source.Term.Efq{}}, 0n,
            Source.Sub.env{e})), h)}
        case Source.Term.Eql{+z0, +z1, +z2}:
          Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.App{q, f, Source.Term.Eql{z0, z1, z2}}, 0n,
            Source.Sub.env{e})), h)}
        case Source.Term.Rfl{}:
          Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.App{q, f, Source.Term.Rfl{}}, 0n,
            Source.Sub.env{e})), h)}
        case Source.Term.Rwt{+z0, +z1, +z2}:
          Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.App{q, f, Source.Term.Rwt{z0, z1, z2}}, 0n,
            Source.Sub.env{e})), h)}
    case Source.Term.Var{+z0}:
      Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.Var{z0}, 0n,
        Source.Sub.env{e})), h)}
    case Source.Term.Ref{+z0}:
      Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.Ref{z0}, 0n,
        Source.Sub.env{e})), h)}
    case Source.Term.Ann{+z0, +z1}:
      Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.Ann{z0, z1}, 0n,
        Source.Sub.env{e})), h)}
    case Source.Term.Let{+z0, +z1, +z2}:
      Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.Let{z0, z1, z2}, 0n,
        Source.Sub.env{e})), h)}
    case Source.Term.Typ{+z0}:
      Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.Typ{z0}, 0n,
        Source.Sub.env{e})), h)}
    case Source.Term.Min{+z0, +z1}:
      Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.Min{z0, z1}, 0n,
        Source.Sub.env{e})), h)}
    case Source.Term.All{+z0, +z1, +z2}:
      Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.All{z0, z1, z2}, 0n,
        Source.Sub.env{e})), h)}
    case Source.Term.Sig{+z0, +z1, +z2}:
      Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.Sig{z0, z1, z2}, 0n,
        Source.Sub.env{e})), h)}
    case Source.Term.Tup{+z0, +z1, +z2}:
      Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.Tup{z0, z1, z2}, 0n,
        Source.Sub.env{e})), h)}
    case Source.Term.Enu{+z0}:
      Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.Enu{z0}, 0n,
        Source.Sub.env{e})), h)}
    case Source.Term.Lab{+z0}:
      Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.Lab{z0}, 0n,
        Source.Sub.env{e})), h)}
    case Source.Term.Eql{+z0, +z1, +z2}:
      Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.Eql{z0, z1, z2}, 0n,
        Source.Sub.env{e})), h)}
    case Source.Term.Rfl{}:
      Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.Rfl{}, 0n,
        Source.Sub.env{e})), h)}
    case Source.Term.Rwt{+z0, +z1, +z2}:
      Spec.Term.Walk.done{{==}, Walk.of_done(o, Source.Term.spine(xs, Source.Term.sub(Source.Term.Rwt{z0, z1, z2}, 0n,
        Source.Sub.env{e})), h)}

def Spec.Term.walk_sound(t, e, xs, o, h):
  Term.walk_sound.go(t, e, xs, o, h)


# Data t when c holds gives the side of a premise (c = true → Data t)
def Term.Data.when_complete(p: Source.Quan, x: Source.Term,
  d: Spec.Term.Data.when(Source.Quan.is_q2(p), x)) ->
  {Bool.or(Bool.not(Source.Quan.is_q2(p)), Source.Term.is_data(x)) == True{} : Bool}:
  match p:
    case Source.Q2{}:
      Spec.Term.is_data_complete(x, d)
    case Source.Q0{}:
      {==}
    case Source.Q1{}:
      {==}

def Bool.is_eq_of(a: Bool, -b: Bool, l: {a == b : Bool}) -> {Source.Bool.is_eq(a, b) == True{} : Bool}:
  match a:
    case True{}:
      %l : {Source.Bool.is_eq(True{}, _) == True{} : Bool}
      {==}
    case False{}:
      %l : {Source.Bool.is_eq(False{}, _) == True{} : Bool}
      {==}

def Name.is_eq_of_ne.go(c: Bool, j: List<&2, Nat>, k: List<&2, Nat>,
  hc: {Source.Name.is_eq(j, k) == c : Bool}, n: {j == k : List<&2, Nat>} -> Empty) ->
  {Source.Name.is_eq(j, k) == False{} : Bool}:
  match c:
    case True{}:
      Empty.elim({Source.Name.is_eq(j, k) == False{} : Bool}, n(Name.is_eq_true(j, k, hc)))
    case False{}:
      hc

def Name.is_eq_of_ne(+j: List<&2, Nat>, +k: List<&2, Nat>, n: {j == k : List<&2, Nat>} -> Empty) ->
  {Source.Name.is_eq(j, k) == False{} : Bool}:
  Name.is_eq_of_ne.go(Source.Name.is_eq(j, k), j, k, {==}, n)

# walk_complete, as Step.lean: by induction on the Walk; s is t, for the rules
# that only say what t is not
def Term.walk_complete.go(-t: Source.Term, -e: List<&2, Source.Term>, -xs: List<&2, Source.Arg>,
  -o: Maybe<&2, Source.Term>, w: Spec.Term.Walk<t, e, xs, o>, s: Source.Term, +es: {s == t : Source.Term}) ->
  {Source.Term.walk(t, e, xs) == Spec.Walk.of(o) : Source.Walk}:
  match w:
    case Spec.Term.Walk.lam{+p, +q, +f, +x, +rest, l, d, w2, et, ex}:
      %Equal.sym(Source.Term, t, Source.Term.Lam{p, f}, et) :
        {Source.Term.walk(_, e, xs) == Spec.Walk.of(o) : Source.Walk}
      %Equal.sym(List<&2, Source.Arg>, xs, Con{Source.Arg{q, x}, rest}, ex) :
        {Source.Term.walk(Source.Term.Lam{p, f}, e, _) == Spec.Walk.of(o) : Source.Walk}
      %Equal.sym(Bool, Bool.and(Source.Bool.is_eq(Source.Quan.live(p), Source.Quan.live(q)),
          Bool.or(Bool.not(Source.Quan.is_q2(p)), Source.Term.is_data(x))), True{},
        Bool.and_intro(Source.Bool.is_eq(Source.Quan.live(p), Source.Quan.live(q)),
          Bool.or(Bool.not(Source.Quan.is_q2(p)), Source.Term.is_data(x)),
          Bool.is_eq_of(Source.Quan.live(p), Source.Quan.live(q), l), Term.Data.when_complete(p, x, d))) :
        {Source.Bool.lazy(Source.Walk, _, u => Source.Term.walk(f, Con{x, e}, rest), u => Source.Walk.fail{}) ==
          Spec.Walk.of(o) : Source.Walk}
      Term.walk_complete.go(f, Con{x, e}, rest, o, w2, f, {==})
    case Spec.Term.Walk.prj{+q, +r, +hh, +a, +b, +rest, l, w2, et, ex}:
      %Equal.sym(Source.Term, t, Source.Term.Prj{hh}, et) :
        {Source.Term.walk(_, e, xs) == Spec.Walk.of(o) : Source.Walk}
      %Equal.sym(List<&2, Source.Arg>, xs, Con{Source.Arg{q, Source.Term.Tup{r, a, b}}, rest}, ex) :
        {Source.Term.walk(Source.Term.Prj{hh}, e, _) == Spec.Walk.of(o) : Source.Walk}
      %Equal.sym(Bool, Source.Quan.live(q), True{}, l) :
        {Source.Bool.lazy(Source.Walk, _,
          u => Source.Term.walk(hh, e, Con{Source.Arg{Source.Quan.fld(r, q), a}, Con{Source.Arg{q, b}, rest}}),
          u => Source.Walk.fail{}) == Spec.Walk.of(o) : Source.Walk}
      Term.walk_complete.go(hh, e, Con{Source.Arg{Source.Quan.fld(r, q), a}, Con{Source.Arg{q, b}, rest}}, o,
        w2, hh, {==})
    case Spec.Term.Walk.hit{+q, +k, +hh, +m, +rest, l, w2, et, ex}:
      %Equal.sym(Source.Term, t, Source.Term.Mat{k, hh, m}, et) :
        {Source.Term.walk(_, e, xs) == Spec.Walk.of(o) : Source.Walk}
      %Equal.sym(List<&2, Source.Arg>, xs, Con{Source.Arg{q, Source.Term.Lab{k}}, rest}, ex) :
        {Source.Term.walk(Source.Term.Mat{k, hh, m}, e, _) == Spec.Walk.of(o) : Source.Walk}
      %Equal.sym(Bool, Source.Quan.live(q), True{}, l) :
        {Source.Bool.lazy(Source.Walk, _,
          u => Source.Bool.lazy(Source.Walk, Source.Name.is_eq(k, k),
            z => Source.Term.walk(hh, e, rest),
            z => Source.Term.walk(m, e, Con{Source.Arg{q, Source.Term.Lab{k}}, rest})),
          u => Source.Walk.fail{}) == Spec.Walk.of(o) : Source.Walk}
      %Equal.sym(Bool, Source.Name.is_eq(k, k), True{}, Name.is_eq_self(k)) :
        {Source.Bool.lazy(Source.Walk, _,
          z => Source.Term.walk(hh, e, rest),
          z => Source.Term.walk(m, e, Con{Source.Arg{q, Source.Term.Lab{k}}, rest})) == Spec.Walk.of(o) :
          Source.Walk}
      Term.walk_complete.go(hh, e, rest, o, w2, hh, {==})
    case Spec.Term.Walk.miss{+q, +j, +k, +hh, +m, +rest, l, n, w2, et, ex}:
      %Equal.sym(Source.Term, t, Source.Term.Mat{k, hh, m}, et) :
        {Source.Term.walk(_, e, xs) == Spec.Walk.of(o) : Source.Walk}
      %Equal.sym(List<&2, Source.Arg>, xs, Con{Source.Arg{q, Source.Term.Lab{j}}, rest}, ex) :
        {Source.Term.walk(Source.Term.Mat{k, hh, m}, e, _) == Spec.Walk.of(o) : Source.Walk}
      %Equal.sym(Bool, Source.Quan.live(q), True{}, l) :
        {Source.Bool.lazy(Source.Walk, _,
          u => Source.Bool.lazy(Source.Walk, Source.Name.is_eq(j, k),
            z => Source.Term.walk(hh, e, rest),
            z => Source.Term.walk(m, e, Con{Source.Arg{q, Source.Term.Lab{j}}, rest})),
          u => Source.Walk.fail{}) == Spec.Walk.of(o) : Source.Walk}
      %Equal.sym(Bool, Source.Name.is_eq(j, k), False{}, Name.is_eq_of_ne(j, k, n)) :
        {Source.Bool.lazy(Source.Walk, _,
          z => Source.Term.walk(hh, e, rest),
          z => Source.Term.walk(m, e, Con{Source.Arg{q, Source.Term.Lab{j}}, rest})) == Spec.Walk.of(o) :
          Source.Walk}
      Term.walk_complete.go(m, e, Con{Source.Arg{q, Source.Term.Lab{j}}, rest}, o, w2, m, {==})
    case Spec.Term.Walk.app{+q, +f, +v, n, w2, et}:
      %Equal.sym(Source.Term, t, Source.Term.App{q, f, Source.Term.Var{v}}, et) :
        {Source.Term.walk(_, e, xs) == Spec.Walk.of(o) : Source.Walk}
      %Equal.sym(Bool, Source.Spine.head.takes(Source.Term.unspine(f, [])), True{}, n) :
        {Source.Bool.lazy(Source.Walk, _,
          u => Source.Term.walk(f, e, Con{Source.Arg{q, Source.Env.sub(e, v)}, xs}),
          u => Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(Source.Term.App{q, f, Source.Term.Var{v}},
            0n, Source.Sub.env{e}))}) == Spec.Walk.of(o) : Source.Walk}
      Term.walk_complete.go(f, e, Con{Source.Arg{q, Source.Env.sub(e, v)}, xs}, o, w2, f, {==})
    case Spec.Term.Walk.need{n, ex, eo}:
      match s:
        case Source.Term.Var{+z0}:
          Bool.absurd({Source.Term.walk(t, e, xs) == Spec.Walk.of(o) : Source.Walk},
            Equal.trans(Bool, Source.Term.takes(Source.Term.Var{z0}), Source.Term.takes(t), True{},
              Equal.cong(Source.Term, Bool, Source.Term.takes, Source.Term.Var{z0}, t, es), n))
        case Source.Term.Ref{+z0}:
          Bool.absurd({Source.Term.walk(t, e, xs) == Spec.Walk.of(o) : Source.Walk},
            Equal.trans(Bool, Source.Term.takes(Source.Term.Ref{z0}), Source.Term.takes(t), True{},
              Equal.cong(Source.Term, Bool, Source.Term.takes, Source.Term.Ref{z0}, t, es), n))
        case Source.Term.Ann{+z0, +z1}:
          Bool.absurd({Source.Term.walk(t, e, xs) == Spec.Walk.of(o) : Source.Walk},
            Equal.trans(Bool, Source.Term.takes(Source.Term.Ann{z0, z1}), Source.Term.takes(t), True{},
              Equal.cong(Source.Term, Bool, Source.Term.takes, Source.Term.Ann{z0, z1}, t, es), n))
        case Source.Term.Let{+z0, +z1, +z2}:
          Bool.absurd({Source.Term.walk(t, e, xs) == Spec.Walk.of(o) : Source.Walk},
            Equal.trans(Bool, Source.Term.takes(Source.Term.Let{z0, z1, z2}), Source.Term.takes(t), True{},
              Equal.cong(Source.Term, Bool, Source.Term.takes, Source.Term.Let{z0, z1, z2}, t, es), n))
        case Source.Term.Typ{+z0}:
          Bool.absurd({Source.Term.walk(t, e, xs) == Spec.Walk.of(o) : Source.Walk},
            Equal.trans(Bool, Source.Term.takes(Source.Term.Typ{z0}), Source.Term.takes(t), True{},
              Equal.cong(Source.Term, Bool, Source.Term.takes, Source.Term.Typ{z0}, t, es), n))
        case Source.Term.Min{+z0, +z1}:
          Bool.absurd({Source.Term.walk(t, e, xs) == Spec.Walk.of(o) : Source.Walk},
            Equal.trans(Bool, Source.Term.takes(Source.Term.Min{z0, z1}), Source.Term.takes(t), True{},
              Equal.cong(Source.Term, Bool, Source.Term.takes, Source.Term.Min{z0, z1}, t, es), n))
        case Source.Term.All{+z0, +z1, +z2}:
          Bool.absurd({Source.Term.walk(t, e, xs) == Spec.Walk.of(o) : Source.Walk},
            Equal.trans(Bool, Source.Term.takes(Source.Term.All{z0, z1, z2}), Source.Term.takes(t), True{},
              Equal.cong(Source.Term, Bool, Source.Term.takes, Source.Term.All{z0, z1, z2}, t, es), n))
        case Source.Term.Lam{+z0, +z1}:
          %es : {Source.Term.walk(_, e, xs) == Spec.Walk.of(o) : Source.Walk}
          %Equal.sym(List<&2, Source.Arg>, xs, Nil{}, ex) :
            {Source.Term.walk(Source.Term.Lam{z0, z1}, e, _) == Spec.Walk.of(o) : Source.Walk}
          %Equal.sym(Maybe<&2, Source.Term>, o, None{}, eo) :
            {Source.Term.walk(Source.Term.Lam{z0, z1}, e, Nil{}) == Spec.Walk.of(_) : Source.Walk}
          {==}
        case Source.Term.App{+z0, +z1, +z2}:
          Bool.absurd({Source.Term.walk(t, e, xs) == Spec.Walk.of(o) : Source.Walk},
            Equal.trans(Bool, Source.Term.takes(Source.Term.App{z0, z1, z2}), Source.Term.takes(t), True{},
              Equal.cong(Source.Term, Bool, Source.Term.takes, Source.Term.App{z0, z1, z2}, t, es), n))
        case Source.Term.Sig{+z0, +z1, +z2}:
          Bool.absurd({Source.Term.walk(t, e, xs) == Spec.Walk.of(o) : Source.Walk},
            Equal.trans(Bool, Source.Term.takes(Source.Term.Sig{z0, z1, z2}), Source.Term.takes(t), True{},
              Equal.cong(Source.Term, Bool, Source.Term.takes, Source.Term.Sig{z0, z1, z2}, t, es), n))
        case Source.Term.Tup{+z0, +z1, +z2}:
          Bool.absurd({Source.Term.walk(t, e, xs) == Spec.Walk.of(o) : Source.Walk},
            Equal.trans(Bool, Source.Term.takes(Source.Term.Tup{z0, z1, z2}), Source.Term.takes(t), True{},
              Equal.cong(Source.Term, Bool, Source.Term.takes, Source.Term.Tup{z0, z1, z2}, t, es), n))
        case Source.Term.Prj{+z0}:
          %es : {Source.Term.walk(_, e, xs) == Spec.Walk.of(o) : Source.Walk}
          %Equal.sym(List<&2, Source.Arg>, xs, Nil{}, ex) :
            {Source.Term.walk(Source.Term.Prj{z0}, e, _) == Spec.Walk.of(o) : Source.Walk}
          %Equal.sym(Maybe<&2, Source.Term>, o, None{}, eo) :
            {Source.Term.walk(Source.Term.Prj{z0}, e, Nil{}) == Spec.Walk.of(_) : Source.Walk}
          {==}
        case Source.Term.Enu{+z0}:
          Bool.absurd({Source.Term.walk(t, e, xs) == Spec.Walk.of(o) : Source.Walk},
            Equal.trans(Bool, Source.Term.takes(Source.Term.Enu{z0}), Source.Term.takes(t), True{},
              Equal.cong(Source.Term, Bool, Source.Term.takes, Source.Term.Enu{z0}, t, es), n))
        case Source.Term.Lab{+z0}:
          Bool.absurd({Source.Term.walk(t, e, xs) == Spec.Walk.of(o) : Source.Walk},
            Equal.trans(Bool, Source.Term.takes(Source.Term.Lab{z0}), Source.Term.takes(t), True{},
              Equal.cong(Source.Term, Bool, Source.Term.takes, Source.Term.Lab{z0}, t, es), n))
        case Source.Term.Mat{+z0, +z1, +z2}:
          %es : {Source.Term.walk(_, e, xs) == Spec.Walk.of(o) : Source.Walk}
          %Equal.sym(List<&2, Source.Arg>, xs, Nil{}, ex) :
            {Source.Term.walk(Source.Term.Mat{z0, z1, z2}, e, _) == Spec.Walk.of(o) : Source.Walk}
          %Equal.sym(Maybe<&2, Source.Term>, o, None{}, eo) :
            {Source.Term.walk(Source.Term.Mat{z0, z1, z2}, e, Nil{}) == Spec.Walk.of(_) : Source.Walk}
          {==}
        case Source.Term.Efq{}:
          %es : {Source.Term.walk(_, e, xs) == Spec.Walk.of(o) : Source.Walk}
          %Equal.sym(List<&2, Source.Arg>, xs, Nil{}, ex) :
            {Source.Term.walk(Source.Term.Efq{}, e, _) == Spec.Walk.of(o) : Source.Walk}
          %Equal.sym(Maybe<&2, Source.Term>, o, None{}, eo) :
            {Source.Term.walk(Source.Term.Efq{}, e, Nil{}) == Spec.Walk.of(_) : Source.Walk}
          {==}
        case Source.Term.Eql{+z0, +z1, +z2}:
          Bool.absurd({Source.Term.walk(t, e, xs) == Spec.Walk.of(o) : Source.Walk},
            Equal.trans(Bool, Source.Term.takes(Source.Term.Eql{z0, z1, z2}), Source.Term.takes(t), True{},
              Equal.cong(Source.Term, Bool, Source.Term.takes, Source.Term.Eql{z0, z1, z2}, t, es), n))
        case Source.Term.Rfl{}:
          Bool.absurd({Source.Term.walk(t, e, xs) == Spec.Walk.of(o) : Source.Walk},
            Equal.trans(Bool, Source.Term.takes(Source.Term.Rfl{}), Source.Term.takes(t), True{},
              Equal.cong(Source.Term, Bool, Source.Term.takes, Source.Term.Rfl{}, t, es), n))
        case Source.Term.Rwt{+z0, +z1, +z2}:
          Bool.absurd({Source.Term.walk(t, e, xs) == Spec.Walk.of(o) : Source.Walk},
            Equal.trans(Bool, Source.Term.takes(Source.Term.Rwt{z0, z1, z2}), Source.Term.takes(t), True{},
              Equal.cong(Source.Term, Bool, Source.Term.takes, Source.Term.Rwt{z0, z1, z2}, t, es), n))
    case Spec.Term.Walk.done{n, eo}:
      match s:
        case Source.Term.Var{+z0}:
          %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
            Source.Sub.env{e}))}, eo) :
            {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
          %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
            Source.Sub.env{e}))} : Source.Walk}
          {==}
        case Source.Term.Ref{+z0}:
          %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
            Source.Sub.env{e}))}, eo) :
            {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
          %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
            Source.Sub.env{e}))} : Source.Walk}
          {==}
        case Source.Term.Ann{+z0, +z1}:
          %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
            Source.Sub.env{e}))}, eo) :
            {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
          %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
            Source.Sub.env{e}))} : Source.Walk}
          {==}
        case Source.Term.Let{+z0, +z1, +z2}:
          %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
            Source.Sub.env{e}))}, eo) :
            {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
          %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
            Source.Sub.env{e}))} : Source.Walk}
          {==}
        case Source.Term.Typ{+z0}:
          %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
            Source.Sub.env{e}))}, eo) :
            {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
          %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
            Source.Sub.env{e}))} : Source.Walk}
          {==}
        case Source.Term.Min{+z0, +z1}:
          %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
            Source.Sub.env{e}))}, eo) :
            {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
          %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
            Source.Sub.env{e}))} : Source.Walk}
          {==}
        case Source.Term.All{+z0, +z1, +z2}:
          %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
            Source.Sub.env{e}))}, eo) :
            {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
          %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
            Source.Sub.env{e}))} : Source.Walk}
          {==}
        case Source.Term.Lam{+z0, +z1}:
          Bool.absurd({Source.Term.walk(t, e, xs) == Spec.Walk.of(o) : Source.Walk},
            Equal.sym(Bool, True{}, False{},
              Equal.trans(Bool, Source.Term.node(Source.Term.Lam{z0, z1}), Source.Term.node(t), False{},
                Equal.cong(Source.Term, Bool, Source.Term.node, Source.Term.Lam{z0, z1}, t, es), n)))
        case Source.Term.App{+q, +f, x}:
          match x:
            case Source.Term.Var{+y0}:
              %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
                Source.Sub.env{e}))}, eo) :
                {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
              %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
                Source.Sub.env{e}))} : Source.Walk}
              %Equal.sym(Bool, Source.Spine.head.takes(Source.Term.unspine(f, [])), False{},
                Equal.trans(Bool, Source.Term.node(Source.Term.App{q, f, Source.Term.Var{y0}}), Source.Term.node(t), False{},
                  Equal.cong(Source.Term, Bool, Source.Term.node, Source.Term.App{q, f, Source.Term.Var{y0}}, t, es), n)) :
                {Source.Bool.lazy(Source.Walk, _,
                  u => Source.Term.walk(f, e, Con{Source.Arg{q, Source.Env.sub(e, y0)}, xs}),
                  u => Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(Source.Term.App{q, f, Source.Term.Var{y0}}, 0n, Source.Sub.env{e}))}) ==
                  Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(Source.Term.App{q, f, Source.Term.Var{y0}}, 0n, Source.Sub.env{e}))} :
                  Source.Walk}
              {==}
            case Source.Term.Ref{+y0}:
              %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
                Source.Sub.env{e}))}, eo) :
                {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
              %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
                Source.Sub.env{e}))} : Source.Walk}
              {==}
            case Source.Term.Ann{+y0, +y1}:
              %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
                Source.Sub.env{e}))}, eo) :
                {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
              %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
                Source.Sub.env{e}))} : Source.Walk}
              {==}
            case Source.Term.Let{+y0, +y1, +y2}:
              %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
                Source.Sub.env{e}))}, eo) :
                {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
              %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
                Source.Sub.env{e}))} : Source.Walk}
              {==}
            case Source.Term.Typ{+y0}:
              %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
                Source.Sub.env{e}))}, eo) :
                {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
              %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
                Source.Sub.env{e}))} : Source.Walk}
              {==}
            case Source.Term.Min{+y0, +y1}:
              %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
                Source.Sub.env{e}))}, eo) :
                {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
              %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
                Source.Sub.env{e}))} : Source.Walk}
              {==}
            case Source.Term.All{+y0, +y1, +y2}:
              %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
                Source.Sub.env{e}))}, eo) :
                {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
              %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
                Source.Sub.env{e}))} : Source.Walk}
              {==}
            case Source.Term.Lam{+y0, +y1}:
              %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
                Source.Sub.env{e}))}, eo) :
                {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
              %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
                Source.Sub.env{e}))} : Source.Walk}
              {==}
            case Source.Term.App{+y0, +y1, +y2}:
              %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
                Source.Sub.env{e}))}, eo) :
                {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
              %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
                Source.Sub.env{e}))} : Source.Walk}
              {==}
            case Source.Term.Sig{+y0, +y1, +y2}:
              %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
                Source.Sub.env{e}))}, eo) :
                {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
              %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
                Source.Sub.env{e}))} : Source.Walk}
              {==}
            case Source.Term.Tup{+y0, +y1, +y2}:
              %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
                Source.Sub.env{e}))}, eo) :
                {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
              %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
                Source.Sub.env{e}))} : Source.Walk}
              {==}
            case Source.Term.Prj{+y0}:
              %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
                Source.Sub.env{e}))}, eo) :
                {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
              %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
                Source.Sub.env{e}))} : Source.Walk}
              {==}
            case Source.Term.Enu{+y0}:
              %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
                Source.Sub.env{e}))}, eo) :
                {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
              %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
                Source.Sub.env{e}))} : Source.Walk}
              {==}
            case Source.Term.Lab{+y0}:
              %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
                Source.Sub.env{e}))}, eo) :
                {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
              %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
                Source.Sub.env{e}))} : Source.Walk}
              {==}
            case Source.Term.Mat{+y0, +y1, +y2}:
              %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
                Source.Sub.env{e}))}, eo) :
                {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
              %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
                Source.Sub.env{e}))} : Source.Walk}
              {==}
            case Source.Term.Efq{}:
              %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
                Source.Sub.env{e}))}, eo) :
                {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
              %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
                Source.Sub.env{e}))} : Source.Walk}
              {==}
            case Source.Term.Eql{+y0, +y1, +y2}:
              %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
                Source.Sub.env{e}))}, eo) :
                {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
              %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
                Source.Sub.env{e}))} : Source.Walk}
              {==}
            case Source.Term.Rfl{}:
              %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
                Source.Sub.env{e}))}, eo) :
                {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
              %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
                Source.Sub.env{e}))} : Source.Walk}
              {==}
            case Source.Term.Rwt{+y0, +y1, +y2}:
              %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
                Source.Sub.env{e}))}, eo) :
                {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
              %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
                Source.Sub.env{e}))} : Source.Walk}
              {==}
        case Source.Term.Sig{+z0, +z1, +z2}:
          %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
            Source.Sub.env{e}))}, eo) :
            {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
          %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
            Source.Sub.env{e}))} : Source.Walk}
          {==}
        case Source.Term.Tup{+z0, +z1, +z2}:
          %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
            Source.Sub.env{e}))}, eo) :
            {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
          %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
            Source.Sub.env{e}))} : Source.Walk}
          {==}
        case Source.Term.Prj{+z0}:
          Bool.absurd({Source.Term.walk(t, e, xs) == Spec.Walk.of(o) : Source.Walk},
            Equal.sym(Bool, True{}, False{},
              Equal.trans(Bool, Source.Term.node(Source.Term.Prj{z0}), Source.Term.node(t), False{},
                Equal.cong(Source.Term, Bool, Source.Term.node, Source.Term.Prj{z0}, t, es), n)))
        case Source.Term.Enu{+z0}:
          %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
            Source.Sub.env{e}))}, eo) :
            {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
          %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
            Source.Sub.env{e}))} : Source.Walk}
          {==}
        case Source.Term.Lab{+z0}:
          %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
            Source.Sub.env{e}))}, eo) :
            {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
          %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
            Source.Sub.env{e}))} : Source.Walk}
          {==}
        case Source.Term.Mat{+z0, +z1, +z2}:
          Bool.absurd({Source.Term.walk(t, e, xs) == Spec.Walk.of(o) : Source.Walk},
            Equal.sym(Bool, True{}, False{},
              Equal.trans(Bool, Source.Term.node(Source.Term.Mat{z0, z1, z2}), Source.Term.node(t), False{},
                Equal.cong(Source.Term, Bool, Source.Term.node, Source.Term.Mat{z0, z1, z2}, t, es), n)))
        case Source.Term.Efq{}:
          Bool.absurd({Source.Term.walk(t, e, xs) == Spec.Walk.of(o) : Source.Walk},
            Equal.sym(Bool, True{}, False{},
              Equal.trans(Bool, Source.Term.node(Source.Term.Efq{}), Source.Term.node(t), False{},
                Equal.cong(Source.Term, Bool, Source.Term.node, Source.Term.Efq{}, t, es), n)))
        case Source.Term.Eql{+z0, +z1, +z2}:
          %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
            Source.Sub.env{e}))}, eo) :
            {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
          %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
            Source.Sub.env{e}))} : Source.Walk}
          {==}
        case Source.Term.Rfl{}:
          %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
            Source.Sub.env{e}))}, eo) :
            {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
          %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
            Source.Sub.env{e}))} : Source.Walk}
          {==}
        case Source.Term.Rwt{+z0, +z1, +z2}:
          %Equal.sym(Maybe<&2, Source.Term>, o, Some{Source.Term.spine(xs, Source.Term.sub(t, 0n,
            Source.Sub.env{e}))}, eo) :
            {Source.Term.walk(t, e, xs) == Spec.Walk.of(_) : Source.Walk}
          %es : {Source.Term.walk(_, e, xs) == Source.Walk.done{Source.Term.spine(xs, Source.Term.sub(_, 0n,
            Source.Sub.env{e}))} : Source.Walk}
          {==}

def Spec.Term.walk_complete(t, e, xs, o, w):
  Term.walk_complete.go(t, e, xs, o, w, t, {==})


# Spines
# ======

def List.append_nil(ys: List<&2, Source.Arg>) -> {List.append(&2, Source.Arg, ys, []) == ys : List<&2, Source.Arg>}:
  match ys:
    case Nil{}:
      {==}
    case Con{a, rest}:
      Equal.cong(List<&2, Source.Arg>, List<&2, Source.Arg>, z => Con{a, z}, List.append(&2, Source.Arg, rest, []),
        rest, List.append_nil(rest))

# a spine with one more argument at its end is an application
def Term.spine_snoc(ys: List<&2, Source.Arg>, -h: Source.Term, -q: Source.Quan, -x: Source.Term) ->
  {Source.Term.spine(List.append(&2, Source.Arg, ys, Con{Source.Arg{q, x}, Nil{}}), h) ==
    Source.Term.App{q, Source.Term.spine(ys, h), x} : Source.Term}:
  match ys:
    case Nil{}:
      {==}
    case Con{Source.Arg{qa, xa}, rest}:
      Term.spine_snoc(rest, Source.Term.App{qa, h, xa}, q, x)

def Term.unspine_spine(ys: List<&2, Source.Arg>, -h: Source.Term, -zs: List<&2, Source.Arg>) ->
  {Source.Term.unspine(Source.Term.spine(ys, h), zs) ==
    Source.Term.unspine(h, List.append(&2, Source.Arg, ys, zs)) : Source.Spine}:
  match ys:
    case Nil{}:
      {==}
    case Con{Source.Arg{qa, xa}, rest}:
      Term.unspine_spine(rest, Source.Term.App{qa, h, xa}, zs)

# Values
# ======

def Term.Values.join(-bk: List<&2, Source.Def>, ys: List<&2, Source.Arg>, -zs: List<&2, Source.Arg>,
  vy: Spec.Term.Values(bk, ys), vz: Spec.Term.Values(bk, zs)) ->
  Spec.Term.Values(bk, List.append(&2, Source.Arg, ys, zs)):
  match ys:
    case Nil{}:
      vz
    case Con{Source.Arg{q, x}, rest}:
      match vy:
        case (vx, vr):
          (vx, Term.Values.join(bk, rest, zs, vr, vz))

# t is a spine on a def, and each live argument is a value (isArgs_iff)
type Term.Args<-bk: List<&2, Source.Def>, -t: Source.Term> is Type:
  Term.Args.of{k: List<&2, Nat>, ys: List<&2, Source.Arg>,
    et: {t == Source.Term.spine(ys, Source.Term.Ref{k}) : Source.Term}, vs: Spec.Term.Values(bk, ys)}

def Term.is_value.res(args: Bool, bk: List<&2, Source.Def>, t: Source.Term) -> Type:
  match args:
    case True{}:
      Term.Args<bk, t>
    case False{}:
      Spec.Term.Value<bk, t>

# the def and the walk of a call that stops
type Term.Stop<-bk: List<&2, Source.Def>, -k: List<&2, Nat>, -xs: List<&2, Source.Arg>> is Type:
  Term.Stop.of{d: Source.Def, g: {Source.Book.get(bk, k) == Some{d} : Maybe<&2, Source.Def>},
    w: Spec.Term.Walk<Source.Def.body(d), [], xs, None{}>}

def Walk.is_need_true(w: Source.Walk, h: {Source.Walk.is_need(w) == True{} : Bool}) ->
  {w == Spec.Walk.of(None{}) : Source.Walk}:
  match w:
    case Source.Walk.need{}:
      {==}
    case Source.Walk.done{t}:
      Bool.absurd({Source.Walk.done{t} == Source.Walk.need{} : Source.Walk}, h)
    case Source.Walk.fail{}:
      Bool.absurd({Source.Walk.fail{} == Source.Walk.need{} : Source.Walk}, h)

def Term.got_need(-bk: List<&2, Source.Def>, -k: List<&2, Nat>, m: Maybe<&2, Source.Def>,
  +xs: List<&2, Source.Arg>, hm: {Source.Book.get(bk, k) == m : Maybe<&2, Source.Def>},
  h: {Source.Walk.is_need(Source.Term.walk_call.got(m, xs)) == True{} : Bool}) -> Term.Stop<bk, k, xs>:
  match m:
    case None{}:
      Bool.absurd(Term.Stop<bk, k, xs>, h)
    case Some{Source.Def{dk, dt, +dv, dop}}:
      Term.Stop.of{Source.Def{dk, dt, dv, dop}, hm,
        Spec.Term.walk_sound(dv, [], xs, None{}, Walk.is_need_true(Source.Term.walk(dv, [], xs), h))}

# whether a call stops is whether its def's walk needs more arguments
def Term.stops_eq(+bk: List<&2, Source.Def>, +k: List<&2, Nat>, +xs: List<&2, Source.Arg>) ->
  {Source.Term.stops(bk, Source.Term.spine(xs, Source.Term.Ref{k})) ==
    Source.Walk.is_need(Source.Term.walk_call.got(Source.Book.get(bk, k), xs)) : Bool}:
  Equal.trans(Bool, Source.Term.stops(bk, Source.Term.spine(xs, Source.Term.Ref{k})),
    Source.Walk.is_need(Source.Term.walk_call.got(Source.Book.get(bk, k), List.append(&2, Source.Arg, xs, []))),
    Source.Walk.is_need(Source.Term.walk_call.got(Source.Book.get(bk, k), xs)),
    Equal.cong(Source.Spine, Bool, z => Source.Walk.is_need(Source.Term.walk_call.of(bk, z)),
      Source.Term.unspine(Source.Term.spine(xs, Source.Term.Ref{k}), []),
      Source.Term.unspine(Source.Term.Ref{k}, List.append(&2, Source.Arg, xs, [])),
      Term.unspine_spine(xs, Source.Term.Ref{k}, [])),
    Equal.cong(List<&2, Source.Arg>, Bool,
      z => Source.Walk.is_need(Source.Term.walk_call.got(Source.Book.get(bk, k), z)),
      List.append(&2, Source.Arg, xs, []), xs, List.append_nil(xs)))

# a call that stops has a def, and its walk needs more arguments
def Term.stops_call(+bk: List<&2, Source.Def>, +k: List<&2, Nat>, +xs: List<&2, Source.Arg>,
  h: {Source.Term.stops(bk, Source.Term.spine(xs, Source.Term.Ref{k})) == True{} : Bool}) -> Term.Stop<bk, k, xs>:
  Term.got_need(bk, k, Source.Book.get(bk, k), xs, {==},
    Equal.trans(Bool, Source.Walk.is_need(Source.Term.walk_call.got(Source.Book.get(bk, k), xs)),
      Source.Term.stops(bk, Source.Term.spine(xs, Source.Term.Ref{k})), True{},
      Equal.sym(Bool, Source.Term.stops(bk, Source.Term.spine(xs, Source.Term.Ref{k})),
        Source.Walk.is_need(Source.Term.walk_call.got(Source.Book.get(bk, k), xs)), Term.stops_eq(bk, k, xs)),
      h))

def Term.value_of_stop(-bk: List<&2, Source.Def>, k: List<&2, Nat>, xs: List<&2, Source.Arg>,
  s: Term.Stop<bk, k, xs>, vs: Spec.Term.Values(bk, xs)) ->
  Spec.Term.Value<bk, Source.Term.spine(xs, Source.Term.Ref{k})>:
  match s:
    case Term.Stop.of{d, g, w}:
      Spec.Term.Value.call{k, d, xs, g, vs, w, {==}}

# App q f x is the spine of f with x at its end
def Term.app_spine(-q: Source.Quan, -f: Source.Term, -x: Source.Term, -k: List<&2, Nat>, ys: List<&2, Source.Arg>,
  et: {f == Source.Term.spine(ys, Source.Term.Ref{k}) : Source.Term}) ->
  {Source.Term.App{q, f, x} == Source.Term.spine(List.append(&2, Source.Arg, ys, Con{Source.Arg{q, x}, Nil{}}), Source.Term.Ref{k}) : Source.Term}:
  Equal.trans(Source.Term, Source.Term.App{q, f, x},
    Source.Term.App{q, Source.Term.spine(ys, Source.Term.Ref{k}), x},
    Source.Term.spine(List.append(&2, Source.Arg, ys, Con{Source.Arg{q, x}, Nil{}}), Source.Term.Ref{k}),
    Equal.cong(Source.Term, Source.Term, z => Source.Term.App{q, z, x}, f,
      Source.Term.spine(ys, Source.Term.Ref{k}), et),
    Equal.sym(Source.Term, Source.Term.spine(List.append(&2, Source.Arg, ys, Con{Source.Arg{q, x}, Nil{}}), Source.Term.Ref{k}),
      Source.Term.App{q, Source.Term.spine(ys, Source.Term.Ref{k}), x},
      Term.spine_snoc(ys, Source.Term.Ref{k}, q, x)))

def Term.args_app(-bk: List<&2, Source.Def>, +q: Source.Quan, -f: Source.Term, +x: Source.Term,
  ra: Term.Args<bk, f>, vx: Spec.Term.Value.when(Source.Quan.live(q), bk, x)) ->
  Term.Args<bk, Source.Term.App{q, f, x}>:
  match ra:
    case Term.Args.of{k, +ys, et, vs}:
      Term.Args.of{k, List.append(&2, Source.Arg, ys, Con{Source.Arg{q, x}, Nil{}}), Term.app_spine(q, f, x, k, ys, et),
        Term.Values.join(bk, ys, Con{Source.Arg{q, x}, Nil{}}, vs, (vx, Unit{}))}

def Term.value_app(+bk: List<&2, Source.Def>, +q: Source.Quan, -f: Source.Term, +x: Source.Term,
  ra: Term.Args<bk, f>, vx: Spec.Term.Value.when(Source.Quan.live(q), bk, x),
  hs: {Source.Term.stops(bk, Source.Term.App{q, f, x}) == True{} : Bool}) ->
  Spec.Term.Value<bk, Source.Term.App{q, f, x}>:
  match ra:
    case Term.Args.of{+k, +ys, et, vs}:
      +e = Term.app_spine(q, f, x, k, ys, et)
      %Equal.sym(Source.Term, Source.Term.App{q, f, x}, Source.Term.spine(List.append(&2, Source.Arg, ys, Con{Source.Arg{q, x}, Nil{}}), Source.Term.Ref{k}), e) :
        Spec.Term.Value<bk, _>
      Term.value_of_stop(bk, k, List.append(&2, Source.Arg, ys, Con{Source.Arg{q, x}, Nil{}}),
        Term.stops_call(bk, k, List.append(&2, Source.Arg, ys, Con{Source.Arg{q, x}, Nil{}}),
          Equal.trans(Bool, Source.Term.stops(bk, Source.Term.spine(List.append(&2, Source.Arg, ys, Con{Source.Arg{q, x}, Nil{}}), Source.Term.Ref{k})),
            Source.Term.stops(bk, Source.Term.App{q, f, x}), True{},
            Equal.cong(Source.Term, Bool, z => Source.Term.stops(bk, z),
              Source.Term.spine(List.append(&2, Source.Arg, ys, Con{Source.Arg{q, x}, Nil{}}), Source.Term.Ref{k}), Source.Term.App{q, f, x},
              Equal.sym(Source.Term, Source.Term.App{q, f, x}, Source.Term.spine(List.append(&2, Source.Arg, ys, Con{Source.Arg{q, x}, Nil{}}), Source.Term.Ref{k}), e)),
            hs)),
        Term.Values.join(bk, ys, Con{Source.Arg{q, x}, Nil{}}, vs, (vx, Unit{})))

# isValue_iff and isArgs_iff, sound side, in one def as is_value is one def
def Term.is_value_sound.go(t: Source.Term, args: Bool, +bk: List<&2, Source.Def>,
  h: {Source.Term.is_value(t, args, bk) == True{} : Bool}) -> Term.is_value.res(args, bk, t):
  match t:
    case Source.Term.Var{+z0}:
      Bool.absurd(Term.is_value.res(args, bk, Source.Term.Var{z0}), h)
    case Source.Term.Ref{+z0}:
      match args:
        case True{}:
          Term.Args.of{z0, [], {==}, Unit{}}
        case False{}:
          Term.value_of_stop(bk, z0, [], Term.stops_call(bk, z0, [], h), Unit{})
    case Source.Term.Ann{+z0, +z1}:
      Bool.absurd(Term.is_value.res(args, bk, Source.Term.Ann{z0, z1}), h)
    case Source.Term.Let{+z0, +z1, +z2}:
      Bool.absurd(Term.is_value.res(args, bk, Source.Term.Let{z0, z1, z2}), h)
    case Source.Term.Typ{+z0}:
      match args:
        case True{}:
          Bool.absurd(Term.Args<bk, Source.Term.Typ{z0}>, h)
        case False{}:
          Spec.Term.Value.typ{z0, {==}}
    case Source.Term.Min{+z0, +z1}:
      Bool.absurd(Term.is_value.res(args, bk, Source.Term.Min{z0, z1}), h)
    case Source.Term.All{+z0, +z1, +z2}:
      match args:
        case True{}:
          Bool.absurd(Term.Args<bk, Source.Term.All{z0, z1, z2}>, h)
        case False{}:
          Spec.Term.Value.all{z0, z1, z2, {==}}
    case Source.Term.Lam{+z0, +z1}:
      match args:
        case True{}:
          Bool.absurd(Term.Args<bk, Source.Term.Lam{z0, z1}>, h)
        case False{}:
          Spec.Term.Value.lam{z0, z1, {==}}
    case Source.Term.App{+z0, +z1, +z2}:
      match z0:
        case Source.Q0{}:
          match args:
            case True{}:
              Term.args_app(bk, Source.Q0{}, z1, z2,
                Term.is_value_sound.go(z1, True{}, bk,
                  Bool.and_left(Source.Term.is_value(z1, True{}, bk), True{}, h)), Unit{})
            case False{}:
              +g = h
              Term.value_app(bk, Source.Q0{}, z1, z2,
                Term.is_value_sound.go(z1, True{}, bk,
                  Bool.and_left(Source.Term.is_value(z1, True{}, bk), True{},
                    Bool.and_left(Bool.and(Source.Term.is_value(z1, True{}, bk), True{}),
                      Source.Term.stops(bk, Source.Term.App{Source.Q0{}, z1, z2}), g))),
                Unit{},
                Bool.and_right(Bool.and(Source.Term.is_value(z1, True{}, bk), True{}),
                  Source.Term.stops(bk, Source.Term.App{Source.Q0{}, z1, z2}), g))
        case Source.Q1{}:
          match args:
            case True{}:
              +g = h
              Term.args_app(bk, Source.Q1{}, z1, z2,
                Term.is_value_sound.go(z1, True{}, bk,
                  Bool.and_left(Source.Term.is_value(z1, True{}, bk), Source.Term.is_value(z2, False{}, bk), g)),
                Term.is_value_sound.go(z2, False{}, bk,
                  Bool.and_right(Source.Term.is_value(z1, True{}, bk), Source.Term.is_value(z2, False{}, bk), g)))
            case False{}:
              +g = h
              Term.value_app(bk, Source.Q1{}, z1, z2,
                Term.is_value_sound.go(z1, True{}, bk,
                  Bool.and_left(Source.Term.is_value(z1, True{}, bk), Source.Term.is_value(z2, False{}, bk),
                    Bool.and_left(Bool.and(Source.Term.is_value(z1, True{}, bk), Source.Term.is_value(z2, False{}, bk)),
                      Source.Term.stops(bk, Source.Term.App{Source.Q1{}, z1, z2}), g))),
                Term.is_value_sound.go(z2, False{}, bk,
                  Bool.and_right(Source.Term.is_value(z1, True{}, bk), Source.Term.is_value(z2, False{}, bk),
                    Bool.and_left(Bool.and(Source.Term.is_value(z1, True{}, bk), Source.Term.is_value(z2, False{}, bk)),
                      Source.Term.stops(bk, Source.Term.App{Source.Q1{}, z1, z2}), g))),
                Bool.and_right(Bool.and(Source.Term.is_value(z1, True{}, bk), Source.Term.is_value(z2, False{}, bk)),
                  Source.Term.stops(bk, Source.Term.App{Source.Q1{}, z1, z2}), g))
        case Source.Q2{}:
          match args:
            case True{}:
              +g = h
              Term.args_app(bk, Source.Q2{}, z1, z2,
                Term.is_value_sound.go(z1, True{}, bk,
                  Bool.and_left(Source.Term.is_value(z1, True{}, bk), Source.Term.is_value(z2, False{}, bk), g)),
                Term.is_value_sound.go(z2, False{}, bk,
                  Bool.and_right(Source.Term.is_value(z1, True{}, bk), Source.Term.is_value(z2, False{}, bk), g)))
            case False{}:
              +g = h
              Term.value_app(bk, Source.Q2{}, z1, z2,
                Term.is_value_sound.go(z1, True{}, bk,
                  Bool.and_left(Source.Term.is_value(z1, True{}, bk), Source.Term.is_value(z2, False{}, bk),
                    Bool.and_left(Bool.and(Source.Term.is_value(z1, True{}, bk), Source.Term.is_value(z2, False{}, bk)),
                      Source.Term.stops(bk, Source.Term.App{Source.Q2{}, z1, z2}), g))),
                Term.is_value_sound.go(z2, False{}, bk,
                  Bool.and_right(Source.Term.is_value(z1, True{}, bk), Source.Term.is_value(z2, False{}, bk),
                    Bool.and_left(Bool.and(Source.Term.is_value(z1, True{}, bk), Source.Term.is_value(z2, False{}, bk)),
                      Source.Term.stops(bk, Source.Term.App{Source.Q2{}, z1, z2}), g))),
                Bool.and_right(Bool.and(Source.Term.is_value(z1, True{}, bk), Source.Term.is_value(z2, False{}, bk)),
                  Source.Term.stops(bk, Source.Term.App{Source.Q2{}, z1, z2}), g))
    case Source.Term.Sig{+z0, +z1, +z2}:
      match args:
        case True{}:
          Bool.absurd(Term.Args<bk, Source.Term.Sig{z0, z1, z2}>, h)
        case False{}:
          Spec.Term.Value.sig{z0, z1, z2, {==}}
    case Source.Term.Tup{+z0, +z1, +z2}:
      match z0:
        case Source.Q0{}:
          match args:
            case True{}:
              Bool.absurd(Term.Args<bk, Source.Term.Tup{Source.Q0{}, z1, z2}>, h)
            case False{}:
              Spec.Term.Value.tup{Source.Q0{}, z1, z2, Unit{}, Term.is_value_sound.go(z2, False{}, bk, h), {==}}
        case Source.Q1{}:
          match args:
            case True{}:
              Bool.absurd(Term.Args<bk, Source.Term.Tup{Source.Q1{}, z1, z2}>, h)
            case False{}:
              +g = h
              Spec.Term.Value.tup{Source.Q1{}, z1, z2,
                Term.is_value_sound.go(z1, False{}, bk,
                  Bool.and_left(Source.Term.is_value(z1, False{}, bk), Source.Term.is_value(z2, False{}, bk), g)),
                Term.is_value_sound.go(z2, False{}, bk,
                  Bool.and_right(Source.Term.is_value(z1, False{}, bk), Source.Term.is_value(z2, False{}, bk), g)),
                {==}}
        case Source.Q2{}:
          match args:
            case True{}:
              Bool.absurd(Term.Args<bk, Source.Term.Tup{Source.Q2{}, z1, z2}>, h)
            case False{}:
              +g = h
              Spec.Term.Value.tup{Source.Q2{}, z1, z2,
                Term.is_value_sound.go(z1, False{}, bk,
                  Bool.and_left(Source.Term.is_value(z1, False{}, bk), Source.Term.is_value(z2, False{}, bk), g)),
                Term.is_value_sound.go(z2, False{}, bk,
                  Bool.and_right(Source.Term.is_value(z1, False{}, bk), Source.Term.is_value(z2, False{}, bk), g)),
                {==}}
    case Source.Term.Prj{+z0}:
      match args:
        case True{}:
          Bool.absurd(Term.Args<bk, Source.Term.Prj{z0}>, h)
        case False{}:
          Spec.Term.Value.prj{z0, {==}}
    case Source.Term.Enu{+z0}:
      match args:
        case True{}:
          Bool.absurd(Term.Args<bk, Source.Term.Enu{z0}>, h)
        case False{}:
          Spec.Term.Value.enu{z0, {==}}
    case Source.Term.Lab{+z0}:
      match args:
        case True{}:
          Bool.absurd(Term.Args<bk, Source.Term.Lab{z0}>, h)
        case False{}:
          Spec.Term.Value.lab{z0, {==}}
    case Source.Term.Mat{+z0, +z1, +z2}:
      match args:
        case True{}:
          Bool.absurd(Term.Args<bk, Source.Term.Mat{z0, z1, z2}>, h)
        case False{}:
          Spec.Term.Value.mat{z0, z1, z2, {==}}
    case Source.Term.Efq{}:
      match args:
        case True{}:
          Bool.absurd(Term.Args<bk, Source.Term.Efq{}>, h)
        case False{}:
          Spec.Term.Value.efq{{==}}
    case Source.Term.Eql{+z0, +z1, +z2}:
      match args:
        case True{}:
          Bool.absurd(Term.Args<bk, Source.Term.Eql{z0, z1, z2}>, h)
        case False{}:
          Spec.Term.Value.eql{z0, z1, z2, {==}}
    case Source.Term.Rfl{}:
      match args:
        case True{}:
          Bool.absurd(Term.Args<bk, Source.Term.Rfl{}>, h)
        case False{}:
          Spec.Term.Value.rfl{{==}}
    case Source.Term.Rwt{+z0, +z1, +z2}:
      Bool.absurd(Term.is_value.res(args, bk, Source.Term.Rwt{z0, z1, z2}), h)

def Spec.Term.is_value_sound(bk, t, h):
  Term.is_value_sound.go(t, False{}, bk, h)


# Terms
# =====

def Term.tag(t: Source.Term) -> Nat:
  match t:
    case Source.Term.Var{z0}:
      0n
    case Source.Term.Ref{z0}:
      1n
    case Source.Term.Ann{z0, z1}:
      2n
    case Source.Term.Let{z0, z1, z2}:
      3n
    case Source.Term.Typ{z0}:
      4n
    case Source.Term.Min{z0, z1}:
      5n
    case Source.Term.All{z0, z1, z2}:
      6n
    case Source.Term.Lam{z0, z1}:
      7n
    case Source.Term.App{z0, z1, z2}:
      8n
    case Source.Term.Sig{z0, z1, z2}:
      9n
    case Source.Term.Tup{z0, z1, z2}:
      10n
    case Source.Term.Prj{z0}:
      11n
    case Source.Term.Enu{z0}:
      12n
    case Source.Term.Lab{z0}:
      13n
    case Source.Term.Mat{z0, z1, z2}:
      14n
    case Source.Term.Efq{}:
      15n
    case Source.Term.Eql{z0, z1, z2}:
      16n
    case Source.Term.Rfl{}:
      17n
    case Source.Term.Rwt{z0, z1, z2}:
      18n

# for two terms of different formers, False == True
def Term.clash(-x: Source.Term, -y: Source.Term, e: {x == y : Source.Term}) ->
  {Nat.is_eq(Term.tag(x), Term.tag(y)) == Nat.is_eq(Term.tag(y), Term.tag(y)) : Bool}:
  Equal.cong(Source.Term, Bool, z => Nat.is_eq(Term.tag(z), Term.tag(y)), x, y, e)

def Term.tup_q(t: Source.Term) -> Source.Quan:
  match t:
    case Source.Term.Tup{q, a, b}:
      q
    case _:
      Source.Q0{}

def Term.tup_a(t: Source.Term) -> Source.Term:
  match t:
    case Source.Term.Tup{q, a, b}:
      a
    case _:
      Source.Term.Rfl{}

def Term.tup_b(t: Source.Term) -> Source.Term:
  match t:
    case Source.Term.Tup{q, a, b}:
      b
    case _:
      Source.Term.Rfl{}

def Term.Value.cast(-bk: List<&2, Source.Def>, -a: Source.Term, -b: Source.Term, e: {a == b : Source.Term},
  v: Spec.Term.Value<bk, a>) -> Spec.Term.Value<bk, b>:
  %e : Spec.Term.Value<bk, _>
  v

def Term.Value.when.cast(-bk: List<&2, Source.Def>, -c: Bool, -d: Bool, -a: Source.Term, -b: Source.Term,
  ec: {c == d : Bool}, ea: {a == b : Source.Term}, v: Spec.Term.Value.when(c, bk, a)) ->
  Spec.Term.Value.when(d, bk, b):
  %ec : Spec.Term.Value.when(_, bk, b)
  %ea : Spec.Term.Value.when(c, bk, _)
  v

# Spines, rebuilt
# ===============

def Spine.head(s: Source.Spine) -> Source.Term:
  match s:
    case Source.Spine{h, xs}:
      h

def Spine.args(s: Source.Spine) -> List<&2, Source.Arg>:
  match s:
    case Source.Spine{h, xs}:
      xs

def Spine.more(s: Source.Spine, ws: List<&2, Source.Arg>) -> Source.Spine:
  match s:
    case Source.Spine{h, xs}:
      Source.Spine{h, List.append(&2, Source.Arg, xs, ws)}

def Spine.rebuild(s: Source.Spine) -> Source.Term:
  match s:
    case Source.Spine{h, xs}:
      Source.Term.spine(xs, h)

def Spine.head_more(s: Source.Spine, -ws: List<&2, Source.Arg>) ->
  {Spine.head(Spine.more(s, ws)) == Spine.head(s) : Source.Term}:
  match s:
    case Source.Spine{h, xs}:
      {==}

def Spine.args_more(s: Source.Spine, -ws: List<&2, Source.Arg>) ->
  {Spine.args(Spine.more(s, ws)) == List.append(&2, Source.Arg, Spine.args(s), ws) : List<&2, Source.Arg>}:
  match s:
    case Source.Spine{h, xs}:
      {==}

def Spine.rebuild_eq(s: Source.Spine) ->
  {Spine.rebuild(s) == Source.Term.spine(Spine.args(s), Spine.head(s)) : Source.Term}:
  match s:
    case Source.Spine{h, xs}:
      {==}

def Term.spine_unspine(t: Source.Term, -zs: List<&2, Source.Arg>) ->
  {Spine.rebuild(Source.Term.unspine(t, zs)) == Source.Term.spine(zs, t) : Source.Term}:
  match t:
    case Source.Term.Var{z0}:
      {==}
    case Source.Term.Ref{z0}:
      {==}
    case Source.Term.Ann{z0, z1}:
      {==}
    case Source.Term.Let{z0, z1, z2}:
      {==}
    case Source.Term.Typ{z0}:
      {==}
    case Source.Term.Min{z0, z1}:
      {==}
    case Source.Term.All{z0, z1, z2}:
      {==}
    case Source.Term.Lam{z0, z1}:
      {==}
    case Source.Term.App{+z0, +z1, +z2}:
      Term.spine_unspine(z1, Con{Source.Arg{z0, z2}, zs})
    case Source.Term.Sig{z0, z1, z2}:
      {==}
    case Source.Term.Tup{z0, z1, z2}:
      {==}
    case Source.Term.Prj{z0}:
      {==}
    case Source.Term.Enu{z0}:
      {==}
    case Source.Term.Lab{z0}:
      {==}
    case Source.Term.Mat{z0, z1, z2}:
      {==}
    case Source.Term.Efq{}:
      {==}
    case Source.Term.Eql{z0, z1, z2}:
      {==}
    case Source.Term.Rfl{}:
      {==}
    case Source.Term.Rwt{z0, z1, z2}:
      {==}

def Term.unspine_more(t: Source.Term, -zs: List<&2, Source.Arg>, -ws: List<&2, Source.Arg>) ->
  {Source.Term.unspine(t, List.append(&2, Source.Arg, zs, ws)) ==
    Spine.more(Source.Term.unspine(t, zs), ws) : Source.Spine}:
  match t:
    case Source.Term.Var{z0}:
      {==}
    case Source.Term.Ref{z0}:
      {==}
    case Source.Term.Ann{z0, z1}:
      {==}
    case Source.Term.Let{z0, z1, z2}:
      {==}
    case Source.Term.Typ{z0}:
      {==}
    case Source.Term.Min{z0, z1}:
      {==}
    case Source.Term.All{z0, z1, z2}:
      {==}
    case Source.Term.Lam{z0, z1}:
      {==}
    case Source.Term.App{+z0, +z1, +z2}:
      Term.unspine_more(z1, Con{Source.Arg{z0, z2}, zs}, ws)
    case Source.Term.Sig{z0, z1, z2}:
      {==}
    case Source.Term.Tup{z0, z1, z2}:
      {==}
    case Source.Term.Prj{z0}:
      {==}
    case Source.Term.Enu{z0}:
      {==}
    case Source.Term.Lab{z0}:
      {==}
    case Source.Term.Mat{z0, z1, z2}:
      {==}
    case Source.Term.Efq{}:
      {==}
    case Source.Term.Eql{z0, z1, z2}:
      {==}
    case Source.Term.Rfl{}:
      {==}
    case Source.Term.Rwt{z0, z1, z2}:
      {==}

# the head of a call
def Term.head_ref(-t: Source.Term, ys: List<&2, Source.Arg>, -k: List<&2, Nat>,
  et: {t == Source.Term.spine(ys, Source.Term.Ref{k}) : Source.Term}) ->
  {Spine.head(Source.Term.unspine(t, [])) == Source.Term.Ref{k} : Source.Term}:
  Equal.trans(Source.Term, Spine.head(Source.Term.unspine(t, [])),
    Spine.head(Source.Term.unspine(Source.Term.spine(ys, Source.Term.Ref{k}), [])), Source.Term.Ref{k},
    Equal.cong(Source.Term, Source.Term, z => Spine.head(Source.Term.unspine(z, [])), t,
      Source.Term.spine(ys, Source.Term.Ref{k}), et),
    Equal.cong(Source.Spine, Source.Term, Spine.head,
      Source.Term.unspine(Source.Term.spine(ys, Source.Term.Ref{k}), []),
      Source.Term.unspine(Source.Term.Ref{k}, List.append(&2, Source.Arg, ys, [])),
      Term.unspine_spine(ys, Source.Term.Ref{k}, [])))

# a call App q f x as a spine of ys: ys is the spine of f with x at its end
def Term.snoc_eq(-q: Source.Quan, +f: Source.Term, -x: Source.Term, -k: List<&2, Nat>, +ys: List<&2, Source.Arg>,
  et: {Source.Term.App{q, f, x} == Source.Term.spine(ys, Source.Term.Ref{k}) : Source.Term}) ->
  {Spine.more(Source.Term.unspine(f, []), Con{Source.Arg{q, x}, Nil{}}) ==
    Source.Spine{Source.Term.Ref{k}, ys} : Source.Spine}:
  Equal.trans(Source.Spine, Spine.more(Source.Term.unspine(f, []), Con{Source.Arg{q, x}, Nil{}}),
    Source.Term.unspine(Source.Term.App{q, f, x}, []), Source.Spine{Source.Term.Ref{k}, ys},
    Equal.sym(Source.Spine, Source.Term.unspine(f, Con{Source.Arg{q, x}, Nil{}}),
      Spine.more(Source.Term.unspine(f, []), Con{Source.Arg{q, x}, Nil{}}),
      Term.unspine_more(f, [], Con{Source.Arg{q, x}, Nil{}})),
    Equal.trans(Source.Spine, Source.Term.unspine(Source.Term.App{q, f, x}, []),
      Source.Term.unspine(Source.Term.spine(ys, Source.Term.Ref{k}), []), Source.Spine{Source.Term.Ref{k}, ys},
      Equal.cong(Source.Term, Source.Spine, z => Source.Term.unspine(z, []), Source.Term.App{q, f, x},
        Source.Term.spine(ys, Source.Term.Ref{k}), et),
      Equal.trans(Source.Spine, Source.Term.unspine(Source.Term.spine(ys, Source.Term.Ref{k}), []),
        Source.Spine{Source.Term.Ref{k}, List.append(&2, Source.Arg, ys, [])}, Source.Spine{Source.Term.Ref{k}, ys},
        Term.unspine_spine(ys, Source.Term.Ref{k}, []),
        Equal.cong(List<&2, Source.Arg>, Source.Spine, z => Source.Spine{Source.Term.Ref{k}, z},
          List.append(&2, Source.Arg, ys, []), ys, List.append_nil(ys)))))

def Term.snoc_ys(-q: Source.Quan, +f: Source.Term, -x: Source.Term, -k: List<&2, Nat>, +ys: List<&2, Source.Arg>,
  et: {Source.Term.App{q, f, x} == Source.Term.spine(ys, Source.Term.Ref{k}) : Source.Term}) ->
  {ys == List.append(&2, Source.Arg, Spine.args(Source.Term.unspine(f, [])), Con{Source.Arg{q, x}, Nil{}}) : List<&2, Source.Arg>}:
  Equal.sym(List<&2, Source.Arg>, List.append(&2, Source.Arg, Spine.args(Source.Term.unspine(f, [])), Con{Source.Arg{q, x}, Nil{}}), ys,
    Equal.trans(List<&2, Source.Arg>, List.append(&2, Source.Arg, Spine.args(Source.Term.unspine(f, [])), Con{Source.Arg{q, x}, Nil{}}),
      Spine.args(Spine.more(Source.Term.unspine(f, []), Con{Source.Arg{q, x}, Nil{}})), ys,
      Equal.sym(List<&2, Source.Arg>, Spine.args(Spine.more(Source.Term.unspine(f, []), Con{Source.Arg{q, x}, Nil{}})),
        List.append(&2, Source.Arg, Spine.args(Source.Term.unspine(f, [])), Con{Source.Arg{q, x}, Nil{}}),
        Spine.args_more(Source.Term.unspine(f, []), Con{Source.Arg{q, x}, Nil{}})),
      Equal.cong(Source.Spine, List<&2, Source.Arg>, Spine.args,
        Spine.more(Source.Term.unspine(f, []), Con{Source.Arg{q, x}, Nil{}}), Source.Spine{Source.Term.Ref{k}, ys},
        Term.snoc_eq(q, f, x, k, ys, et))))

def Term.snoc_f(-q: Source.Quan, +f: Source.Term, -x: Source.Term, -k: List<&2, Nat>, +ys: List<&2, Source.Arg>,
  et: {Source.Term.App{q, f, x} == Source.Term.spine(ys, Source.Term.Ref{k}) : Source.Term}) ->
  {f == Source.Term.spine(Spine.args(Source.Term.unspine(f, [])), Source.Term.Ref{k}) : Source.Term}:
  Equal.trans(Source.Term, f, Source.Term.spine(Spine.args(Source.Term.unspine(f, [])), Spine.head(Source.Term.unspine(f, []))),
    Source.Term.spine(Spine.args(Source.Term.unspine(f, [])), Source.Term.Ref{k}),
    Equal.sym(Source.Term, Source.Term.spine(Spine.args(Source.Term.unspine(f, [])), Spine.head(Source.Term.unspine(f, []))), f,
      Equal.trans(Source.Term, Source.Term.spine(Spine.args(Source.Term.unspine(f, [])), Spine.head(Source.Term.unspine(f, []))),
        Spine.rebuild(Source.Term.unspine(f, [])), f,
        Equal.sym(Source.Term, Spine.rebuild(Source.Term.unspine(f, [])),
          Source.Term.spine(Spine.args(Source.Term.unspine(f, [])), Spine.head(Source.Term.unspine(f, []))),
          Spine.rebuild_eq(Source.Term.unspine(f, []))),
        Term.spine_unspine(f, []))),
    Equal.cong(Source.Term, Source.Term, z => Source.Term.spine(Spine.args(Source.Term.unspine(f, [])), z), Spine.head(Source.Term.unspine(f, [])),
      Source.Term.Ref{k},
      Equal.trans(Source.Term, Spine.head(Source.Term.unspine(f, [])),
        Spine.head(Spine.more(Source.Term.unspine(f, []), Con{Source.Arg{q, x}, Nil{}})), Source.Term.Ref{k},
        Equal.sym(Source.Term, Spine.head(Spine.more(Source.Term.unspine(f, []), Con{Source.Arg{q, x}, Nil{}})),
          Spine.head(Source.Term.unspine(f, [])),
          Spine.head_more(Source.Term.unspine(f, []), Con{Source.Arg{q, x}, Nil{}})),
        Equal.cong(Source.Spine, Source.Term, Spine.head,
          Spine.more(Source.Term.unspine(f, []), Con{Source.Arg{q, x}, Nil{}}), Source.Spine{Source.Term.Ref{k}, ys},
          Term.snoc_eq(q, f, x, k, ys, et)))))

# Values, split
# =============

def Term.Values.cast(-bk: List<&2, Source.Def>, -ys: List<&2, Source.Arg>, -zs: List<&2, Source.Arg>,
  e: {ys == zs : List<&2, Source.Arg>}, v: Spec.Term.Values(bk, ys)) -> Spec.Term.Values(bk, zs):
  %e : Spec.Term.Values(bk, _)
  v

def Term.Values.split.cons(-bk: List<&2, Source.Def>, -q: Source.Quan, -x: Source.Term,
  -rest: List<&2, Source.Arg>, -zs: List<&2, Source.Arg>, vx: Spec.Term.Value.when(Source.Quan.live(q), bk, x),
  -R: Type, k: Spec.Term.Values(bk, Con{Source.Arg{q, x}, rest}) -> Spec.Term.Values(bk, zs) -> R) ->
  Spec.Term.Values(bk, rest) -> Spec.Term.Values(bk, zs) -> R:
  vr => vz => k((vx, vr), vz)

# the Values of ys ++ zs, as the Values of ys and those of zs, given to k
def Term.Values.split.by(-bk: List<&2, Source.Def>, ys: List<&2, Source.Arg>, -zs: List<&2, Source.Arg>,
  v: Spec.Term.Values(bk, List.append(&2, Source.Arg, ys, zs)), -R: Type,
  k: Spec.Term.Values(bk, ys) -> Spec.Term.Values(bk, zs) -> R) -> R:
  match ys:
    case Nil{}:
      k(Unit{}, v)
    case Con{Source.Arg{q, x}, rest}:
      match v:
        case (vx, vr):
          Term.Values.split.by(bk, rest, zs, vr, R, Term.Values.split.cons(bk, q, x, rest, zs, vx, R, k))

def Term.Values.head(-bk: List<&2, Source.Def>, -q: Source.Quan, -x: Source.Term, -rest: List<&2, Source.Arg>,
  v: Spec.Term.Values(bk, Con{Source.Arg{q, x}, rest})) -> Spec.Term.Value.when(Source.Quan.live(q), bk, x):
  match v:
    case (a, b):
      a

# Stops, complete
# ===============

def Term.need_of(d: Source.Def, +xs: List<&2, Source.Arg>, w: Spec.Term.Walk<Source.Def.body(d), [], xs, None{}>) ->
  {Source.Walk.is_need(Source.Term.walk_call.got(Some{d}, xs)) == True{} : Bool}:
  match d:
    case Source.Def{dk, dt, +dv, dop}:
      %Equal.sym(Source.Walk, Source.Term.walk(dv, [], xs), Source.Walk.need{},
        Spec.Term.walk_complete(dv, [], xs, None{}, w)) : {Source.Walk.is_need(_) == True{} : Bool}
      {==}

def Term.stops_of(+bk: List<&2, Source.Def>, +k: List<&2, Nat>, +xs: List<&2, Source.Arg>, +d: Source.Def,
  g: {Source.Book.get(bk, k) == Some{d} : Maybe<&2, Source.Def>},
  w: Spec.Term.Walk<Source.Def.body(d), [], xs, None{}>) ->
  {Source.Term.stops(bk, Source.Term.spine(xs, Source.Term.Ref{k})) == True{} : Bool}:
  Equal.trans(Bool, Source.Term.stops(bk, Source.Term.spine(xs, Source.Term.Ref{k})),
    Source.Walk.is_need(Source.Term.walk_call.got(Source.Book.get(bk, k), xs)), True{},
    Term.stops_eq(bk, k, xs),
    Equal.trans(Bool, Source.Walk.is_need(Source.Term.walk_call.got(Source.Book.get(bk, k), xs)),
      Source.Walk.is_need(Source.Term.walk_call.got(Some{d}, xs)), True{},
      Equal.cong(Maybe<&2, Source.Def>, Bool, z => Source.Walk.is_need(Source.Term.walk_call.got(z, xs)),
        Source.Book.get(bk, k), Some{d}, g),
      Term.need_of(d, xs, w)))

# isValue_iff and isArgs_iff, complete side: by induction on t
def Term.is_value_complete.go(t: Source.Term, args: Bool, +bk: List<&2, Source.Def>,
  r: Term.is_value.res(args, bk, t)) -> {Source.Term.is_value(t, args, bk) == True{} : Bool}:
  match t:
    case Source.Term.Var{+z0}:
      match args:
        case True{}:
          match r:
            case Term.Args.of{k, ys, et, vs}:
              Empty.elim({Source.Term.is_value(Source.Term.Var{z0}, True{}, bk) == True{} : Bool},
                Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Var{z0}, [])), Source.Term.Ref{k},
                  Term.head_ref(Source.Term.Var{z0}, ys, k, et))))
        case False{}:
          match r:
            case Spec.Term.Value.lam{r0, r1, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Var{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Var{z0}, Source.Term.Lam{r0, r1}, et)))
            case Spec.Term.Value.prj{r0, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Var{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Var{z0}, Source.Term.Prj{r0}, et)))
            case Spec.Term.Value.mat{r0, r1, r2, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Var{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Var{z0}, Source.Term.Mat{r0, r1, r2}, et)))
            case Spec.Term.Value.efq{et}:
              Empty.elim({Source.Term.is_value(Source.Term.Var{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Var{z0}, Source.Term.Efq{}, et)))
            case Spec.Term.Value.lab{r0, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Var{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Var{z0}, Source.Term.Lab{r0}, et)))
            case Spec.Term.Value.rfl{et}:
              Empty.elim({Source.Term.is_value(Source.Term.Var{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Var{z0}, Source.Term.Rfl{}, et)))
            case Spec.Term.Value.typ{r0, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Var{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Var{z0}, Source.Term.Typ{r0}, et)))
            case Spec.Term.Value.all{r0, r1, r2, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Var{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Var{z0}, Source.Term.All{r0, r1, r2}, et)))
            case Spec.Term.Value.sig{r0, r1, r2, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Var{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Var{z0}, Source.Term.Sig{r0, r1, r2}, et)))
            case Spec.Term.Value.enu{r0, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Var{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Var{z0}, Source.Term.Enu{r0}, et)))
            case Spec.Term.Value.eql{r0, r1, r2, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Var{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Var{z0}, Source.Term.Eql{r0, r1, r2}, et)))
            case Spec.Term.Value.tup{r0, r1, r2, va, vb, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Var{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Var{z0}, Source.Term.Tup{r0, r1, r2}, et)))
            case Spec.Term.Value.call{r0, r1, r2, g, vs, w, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Var{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Var{z0}, [])), Source.Term.Ref{r0}, Term.head_ref(Source.Term.Var{z0}, r2, r0, et))))
    case Source.Term.Ref{+z0}:
      match args:
        case True{}:
          {==}
        case False{}:
          match r:
            case Spec.Term.Value.lam{r0, r1, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ref{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Ref{z0}, Source.Term.Lam{r0, r1}, et)))
            case Spec.Term.Value.prj{r0, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ref{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Ref{z0}, Source.Term.Prj{r0}, et)))
            case Spec.Term.Value.mat{r0, r1, r2, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ref{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Ref{z0}, Source.Term.Mat{r0, r1, r2}, et)))
            case Spec.Term.Value.efq{et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ref{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Ref{z0}, Source.Term.Efq{}, et)))
            case Spec.Term.Value.lab{r0, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ref{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Ref{z0}, Source.Term.Lab{r0}, et)))
            case Spec.Term.Value.rfl{et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ref{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Ref{z0}, Source.Term.Rfl{}, et)))
            case Spec.Term.Value.typ{r0, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ref{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Ref{z0}, Source.Term.Typ{r0}, et)))
            case Spec.Term.Value.all{r0, r1, r2, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ref{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Ref{z0}, Source.Term.All{r0, r1, r2}, et)))
            case Spec.Term.Value.sig{r0, r1, r2, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ref{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Ref{z0}, Source.Term.Sig{r0, r1, r2}, et)))
            case Spec.Term.Value.enu{r0, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ref{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Ref{z0}, Source.Term.Enu{r0}, et)))
            case Spec.Term.Value.eql{r0, r1, r2, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ref{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Ref{z0}, Source.Term.Eql{r0, r1, r2}, et)))
            case Spec.Term.Value.tup{r0, r1, r2, va, vb, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ref{z0}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Ref{z0}, Source.Term.Tup{r0, r1, r2}, et)))
            case Spec.Term.Value.call{r0, r1, r2, g, vs, w, et}:
              Equal.trans(Bool, Source.Term.stops(bk, Source.Term.Ref{z0}),
                Source.Term.stops(bk, Source.Term.spine(r2, Source.Term.Ref{r0})), True{},
                Equal.cong(Source.Term, Bool, z => Source.Term.stops(bk, z), Source.Term.Ref{z0},
                  Source.Term.spine(r2, Source.Term.Ref{r0}), et),
                Term.stops_of(bk, r0, r2, r1, g, w))
    case Source.Term.Ann{+z0, +z1}:
      match args:
        case True{}:
          match r:
            case Term.Args.of{k, ys, et, vs}:
              Empty.elim({Source.Term.is_value(Source.Term.Ann{z0, z1}, True{}, bk) == True{} : Bool},
                Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Ann{z0, z1}, [])), Source.Term.Ref{k},
                  Term.head_ref(Source.Term.Ann{z0, z1}, ys, k, et))))
        case False{}:
          match r:
            case Spec.Term.Value.lam{r0, r1, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ann{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Ann{z0, z1}, Source.Term.Lam{r0, r1}, et)))
            case Spec.Term.Value.prj{r0, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ann{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Ann{z0, z1}, Source.Term.Prj{r0}, et)))
            case Spec.Term.Value.mat{r0, r1, r2, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ann{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Ann{z0, z1}, Source.Term.Mat{r0, r1, r2}, et)))
            case Spec.Term.Value.efq{et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ann{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Ann{z0, z1}, Source.Term.Efq{}, et)))
            case Spec.Term.Value.lab{r0, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ann{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Ann{z0, z1}, Source.Term.Lab{r0}, et)))
            case Spec.Term.Value.rfl{et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ann{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Ann{z0, z1}, Source.Term.Rfl{}, et)))
            case Spec.Term.Value.typ{r0, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ann{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Ann{z0, z1}, Source.Term.Typ{r0}, et)))
            case Spec.Term.Value.all{r0, r1, r2, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ann{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Ann{z0, z1}, Source.Term.All{r0, r1, r2}, et)))
            case Spec.Term.Value.sig{r0, r1, r2, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ann{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Ann{z0, z1}, Source.Term.Sig{r0, r1, r2}, et)))
            case Spec.Term.Value.enu{r0, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ann{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Ann{z0, z1}, Source.Term.Enu{r0}, et)))
            case Spec.Term.Value.eql{r0, r1, r2, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ann{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Ann{z0, z1}, Source.Term.Eql{r0, r1, r2}, et)))
            case Spec.Term.Value.tup{r0, r1, r2, va, vb, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ann{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Ann{z0, z1}, Source.Term.Tup{r0, r1, r2}, et)))
            case Spec.Term.Value.call{r0, r1, r2, g, vs, w, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Ann{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Ann{z0, z1}, [])), Source.Term.Ref{r0}, Term.head_ref(Source.Term.Ann{z0, z1}, r2, r0, et))))
    case Source.Term.Let{+z0, +z1, +z2}:
      match args:
        case True{}:
          match r:
            case Term.Args.of{k, ys, et, vs}:
              Empty.elim({Source.Term.is_value(Source.Term.Let{z0, z1, z2}, True{}, bk) == True{} : Bool},
                Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Let{z0, z1, z2}, [])), Source.Term.Ref{k},
                  Term.head_ref(Source.Term.Let{z0, z1, z2}, ys, k, et))))
        case False{}:
          match r:
            case Spec.Term.Value.lam{r0, r1, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Let{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Let{z0, z1, z2}, Source.Term.Lam{r0, r1}, et)))
            case Spec.Term.Value.prj{r0, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Let{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Let{z0, z1, z2}, Source.Term.Prj{r0}, et)))
            case Spec.Term.Value.mat{r0, r1, r2, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Let{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Let{z0, z1, z2}, Source.Term.Mat{r0, r1, r2}, et)))
            case Spec.Term.Value.efq{et}:
              Empty.elim({Source.Term.is_value(Source.Term.Let{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Let{z0, z1, z2}, Source.Term.Efq{}, et)))
            case Spec.Term.Value.lab{r0, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Let{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Let{z0, z1, z2}, Source.Term.Lab{r0}, et)))
            case Spec.Term.Value.rfl{et}:
              Empty.elim({Source.Term.is_value(Source.Term.Let{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Let{z0, z1, z2}, Source.Term.Rfl{}, et)))
            case Spec.Term.Value.typ{r0, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Let{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Let{z0, z1, z2}, Source.Term.Typ{r0}, et)))
            case Spec.Term.Value.all{r0, r1, r2, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Let{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Let{z0, z1, z2}, Source.Term.All{r0, r1, r2}, et)))
            case Spec.Term.Value.sig{r0, r1, r2, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Let{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Let{z0, z1, z2}, Source.Term.Sig{r0, r1, r2}, et)))
            case Spec.Term.Value.enu{r0, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Let{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Let{z0, z1, z2}, Source.Term.Enu{r0}, et)))
            case Spec.Term.Value.eql{r0, r1, r2, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Let{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Let{z0, z1, z2}, Source.Term.Eql{r0, r1, r2}, et)))
            case Spec.Term.Value.tup{r0, r1, r2, va, vb, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Let{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Let{z0, z1, z2}, Source.Term.Tup{r0, r1, r2}, et)))
            case Spec.Term.Value.call{r0, r1, r2, g, vs, w, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Let{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Let{z0, z1, z2}, [])), Source.Term.Ref{r0}, Term.head_ref(Source.Term.Let{z0, z1, z2}, r2, r0, et))))
    case Source.Term.Typ{+z0}:
      match args:
        case True{}:
          match r:
            case Term.Args.of{k, ys, et, vs}:
              Empty.elim({Source.Term.is_value(Source.Term.Typ{z0}, True{}, bk) == True{} : Bool},
                Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Typ{z0}, [])), Source.Term.Ref{k},
                  Term.head_ref(Source.Term.Typ{z0}, ys, k, et))))
        case False{}:
          {==}
    case Source.Term.Min{+z0, +z1}:
      match args:
        case True{}:
          match r:
            case Term.Args.of{k, ys, et, vs}:
              Empty.elim({Source.Term.is_value(Source.Term.Min{z0, z1}, True{}, bk) == True{} : Bool},
                Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Min{z0, z1}, [])), Source.Term.Ref{k},
                  Term.head_ref(Source.Term.Min{z0, z1}, ys, k, et))))
        case False{}:
          match r:
            case Spec.Term.Value.lam{r0, r1, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Min{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Min{z0, z1}, Source.Term.Lam{r0, r1}, et)))
            case Spec.Term.Value.prj{r0, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Min{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Min{z0, z1}, Source.Term.Prj{r0}, et)))
            case Spec.Term.Value.mat{r0, r1, r2, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Min{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Min{z0, z1}, Source.Term.Mat{r0, r1, r2}, et)))
            case Spec.Term.Value.efq{et}:
              Empty.elim({Source.Term.is_value(Source.Term.Min{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Min{z0, z1}, Source.Term.Efq{}, et)))
            case Spec.Term.Value.lab{r0, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Min{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Min{z0, z1}, Source.Term.Lab{r0}, et)))
            case Spec.Term.Value.rfl{et}:
              Empty.elim({Source.Term.is_value(Source.Term.Min{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Min{z0, z1}, Source.Term.Rfl{}, et)))
            case Spec.Term.Value.typ{r0, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Min{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Min{z0, z1}, Source.Term.Typ{r0}, et)))
            case Spec.Term.Value.all{r0, r1, r2, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Min{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Min{z0, z1}, Source.Term.All{r0, r1, r2}, et)))
            case Spec.Term.Value.sig{r0, r1, r2, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Min{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Min{z0, z1}, Source.Term.Sig{r0, r1, r2}, et)))
            case Spec.Term.Value.enu{r0, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Min{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Min{z0, z1}, Source.Term.Enu{r0}, et)))
            case Spec.Term.Value.eql{r0, r1, r2, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Min{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Min{z0, z1}, Source.Term.Eql{r0, r1, r2}, et)))
            case Spec.Term.Value.tup{r0, r1, r2, va, vb, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Min{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Min{z0, z1}, Source.Term.Tup{r0, r1, r2}, et)))
            case Spec.Term.Value.call{r0, r1, r2, g, vs, w, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Min{z0, z1}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Min{z0, z1}, [])), Source.Term.Ref{r0}, Term.head_ref(Source.Term.Min{z0, z1}, r2, r0, et))))
    case Source.Term.All{+z0, +z1, +z2}:
      match args:
        case True{}:
          match r:
            case Term.Args.of{k, ys, et, vs}:
              Empty.elim({Source.Term.is_value(Source.Term.All{z0, z1, z2}, True{}, bk) == True{} : Bool},
                Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.All{z0, z1, z2}, [])), Source.Term.Ref{k},
                  Term.head_ref(Source.Term.All{z0, z1, z2}, ys, k, et))))
        case False{}:
          {==}
    case Source.Term.Lam{+z0, +z1}:
      match args:
        case True{}:
          match r:
            case Term.Args.of{k, ys, et, vs}:
              Empty.elim({Source.Term.is_value(Source.Term.Lam{z0, z1}, True{}, bk) == True{} : Bool},
                Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Lam{z0, z1}, [])), Source.Term.Ref{k},
                  Term.head_ref(Source.Term.Lam{z0, z1}, ys, k, et))))
        case False{}:
          {==}
    case Source.Term.App{+z0, +z1, +z2}:
      match z0:
        case Source.Q0{}:
          match args:
            case True{}:
              match r:
                case Term.Args.of{+k, +ys, +et, vs}:
                  Term.Values.split.by(bk, Spine.args(Source.Term.unspine(z1, [])), Con{Source.Arg{Source.Q0{}, z2}, Nil{}},
                    Term.Values.cast(bk, ys, List.append(&2, Source.Arg, Spine.args(Source.Term.unspine(z1, [])), Con{Source.Arg{Source.Q0{}, z2}, Nil{}}),
                      Term.snoc_ys(Source.Q0{}, z1, z2, k, ys, et), vs),
                    {Bool.and(Source.Term.is_value(z1, True{}, bk), True{}) == True{} : Bool},
                    vf => vr => Bool.and_intro(Source.Term.is_value(z1, True{}, bk), True{},
                      Term.is_value_complete.go(z1, True{}, bk, Term.Args.of{k, Spine.args(Source.Term.unspine(z1, [])), Term.snoc_f(Source.Q0{}, z1, z2, k, ys, et), vf}),
                      {==}))
            case False{}:
              match r:
                case Spec.Term.Value.lam{r0, r1, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q0{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q0{}, z1, z2}, Source.Term.Lam{r0, r1}, et)))
                case Spec.Term.Value.prj{r0, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q0{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q0{}, z1, z2}, Source.Term.Prj{r0}, et)))
                case Spec.Term.Value.mat{r0, r1, r2, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q0{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q0{}, z1, z2}, Source.Term.Mat{r0, r1, r2}, et)))
                case Spec.Term.Value.efq{et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q0{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q0{}, z1, z2}, Source.Term.Efq{}, et)))
                case Spec.Term.Value.lab{r0, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q0{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q0{}, z1, z2}, Source.Term.Lab{r0}, et)))
                case Spec.Term.Value.rfl{et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q0{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q0{}, z1, z2}, Source.Term.Rfl{}, et)))
                case Spec.Term.Value.typ{r0, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q0{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q0{}, z1, z2}, Source.Term.Typ{r0}, et)))
                case Spec.Term.Value.all{r0, r1, r2, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q0{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q0{}, z1, z2}, Source.Term.All{r0, r1, r2}, et)))
                case Spec.Term.Value.sig{r0, r1, r2, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q0{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q0{}, z1, z2}, Source.Term.Sig{r0, r1, r2}, et)))
                case Spec.Term.Value.enu{r0, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q0{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q0{}, z1, z2}, Source.Term.Enu{r0}, et)))
                case Spec.Term.Value.eql{r0, r1, r2, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q0{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q0{}, z1, z2}, Source.Term.Eql{r0, r1, r2}, et)))
                case Spec.Term.Value.tup{r0, r1, r2, va, vb, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q0{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q0{}, z1, z2}, Source.Term.Tup{r0, r1, r2}, et)))
                case Spec.Term.Value.call{+r0, r1, +r2, g, vs, w, +et}:
                  Bool.and_intro(Bool.and(Source.Term.is_value(z1, True{}, bk), True{}),
                    Source.Term.stops(bk, Source.Term.App{Source.Q0{}, z1, z2}),
                    Term.Values.split.by(bk, Spine.args(Source.Term.unspine(z1, [])), Con{Source.Arg{Source.Q0{}, z2}, Nil{}},
                      Term.Values.cast(bk, r2, List.append(&2, Source.Arg, Spine.args(Source.Term.unspine(z1, [])), Con{Source.Arg{Source.Q0{}, z2}, Nil{}}),
                        Term.snoc_ys(Source.Q0{}, z1, z2, r0, r2, et), vs),
                      {Bool.and(Source.Term.is_value(z1, True{}, bk), True{}) == True{} : Bool},
                      vf => vr => Bool.and_intro(Source.Term.is_value(z1, True{}, bk), True{},
                        Term.is_value_complete.go(z1, True{}, bk, Term.Args.of{r0, Spine.args(Source.Term.unspine(z1, [])), Term.snoc_f(Source.Q0{}, z1, z2, r0, r2, et), vf}),
                        {==})),
                    Equal.trans(Bool, Source.Term.stops(bk, Source.Term.App{Source.Q0{}, z1, z2}),
                      Source.Term.stops(bk, Source.Term.spine(r2, Source.Term.Ref{r0})), True{},
                      Equal.cong(Source.Term, Bool, z => Source.Term.stops(bk, z), Source.Term.App{Source.Q0{}, z1, z2},
                        Source.Term.spine(r2, Source.Term.Ref{r0}), et),
                      Term.stops_of(bk, r0, r2, r1, g, w)))
        case Source.Q1{}:
          match args:
            case True{}:
              match r:
                case Term.Args.of{+k, +ys, +et, vs}:
                  Term.Values.split.by(bk, Spine.args(Source.Term.unspine(z1, [])), Con{Source.Arg{Source.Q1{}, z2}, Nil{}},
                    Term.Values.cast(bk, ys, List.append(&2, Source.Arg, Spine.args(Source.Term.unspine(z1, [])), Con{Source.Arg{Source.Q1{}, z2}, Nil{}}),
                      Term.snoc_ys(Source.Q1{}, z1, z2, k, ys, et), vs),
                    {Bool.and(Source.Term.is_value(z1, True{}, bk), Source.Term.is_value(z2, False{}, bk)) == True{} : Bool},
                    vf => vr => Bool.and_intro(Source.Term.is_value(z1, True{}, bk), Source.Term.is_value(z2, False{}, bk),
                      Term.is_value_complete.go(z1, True{}, bk, Term.Args.of{k, Spine.args(Source.Term.unspine(z1, [])), Term.snoc_f(Source.Q1{}, z1, z2, k, ys, et), vf}),
                      Term.is_value_complete.go(z2, False{}, bk, Term.Values.head(bk, Source.Q1{}, z2, Nil{}, vr))))
            case False{}:
              match r:
                case Spec.Term.Value.lam{r0, r1, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q1{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q1{}, z1, z2}, Source.Term.Lam{r0, r1}, et)))
                case Spec.Term.Value.prj{r0, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q1{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q1{}, z1, z2}, Source.Term.Prj{r0}, et)))
                case Spec.Term.Value.mat{r0, r1, r2, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q1{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q1{}, z1, z2}, Source.Term.Mat{r0, r1, r2}, et)))
                case Spec.Term.Value.efq{et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q1{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q1{}, z1, z2}, Source.Term.Efq{}, et)))
                case Spec.Term.Value.lab{r0, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q1{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q1{}, z1, z2}, Source.Term.Lab{r0}, et)))
                case Spec.Term.Value.rfl{et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q1{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q1{}, z1, z2}, Source.Term.Rfl{}, et)))
                case Spec.Term.Value.typ{r0, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q1{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q1{}, z1, z2}, Source.Term.Typ{r0}, et)))
                case Spec.Term.Value.all{r0, r1, r2, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q1{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q1{}, z1, z2}, Source.Term.All{r0, r1, r2}, et)))
                case Spec.Term.Value.sig{r0, r1, r2, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q1{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q1{}, z1, z2}, Source.Term.Sig{r0, r1, r2}, et)))
                case Spec.Term.Value.enu{r0, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q1{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q1{}, z1, z2}, Source.Term.Enu{r0}, et)))
                case Spec.Term.Value.eql{r0, r1, r2, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q1{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q1{}, z1, z2}, Source.Term.Eql{r0, r1, r2}, et)))
                case Spec.Term.Value.tup{r0, r1, r2, va, vb, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q1{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q1{}, z1, z2}, Source.Term.Tup{r0, r1, r2}, et)))
                case Spec.Term.Value.call{+r0, r1, +r2, g, vs, w, +et}:
                  Bool.and_intro(Bool.and(Source.Term.is_value(z1, True{}, bk), Source.Term.is_value(z2, False{}, bk)),
                    Source.Term.stops(bk, Source.Term.App{Source.Q1{}, z1, z2}),
                    Term.Values.split.by(bk, Spine.args(Source.Term.unspine(z1, [])), Con{Source.Arg{Source.Q1{}, z2}, Nil{}},
                      Term.Values.cast(bk, r2, List.append(&2, Source.Arg, Spine.args(Source.Term.unspine(z1, [])), Con{Source.Arg{Source.Q1{}, z2}, Nil{}}),
                        Term.snoc_ys(Source.Q1{}, z1, z2, r0, r2, et), vs),
                      {Bool.and(Source.Term.is_value(z1, True{}, bk), Source.Term.is_value(z2, False{}, bk)) == True{} : Bool},
                      vf => vr => Bool.and_intro(Source.Term.is_value(z1, True{}, bk), Source.Term.is_value(z2, False{}, bk),
                        Term.is_value_complete.go(z1, True{}, bk, Term.Args.of{r0, Spine.args(Source.Term.unspine(z1, [])), Term.snoc_f(Source.Q1{}, z1, z2, r0, r2, et), vf}),
                        Term.is_value_complete.go(z2, False{}, bk, Term.Values.head(bk, Source.Q1{}, z2, Nil{}, vr)))),
                    Equal.trans(Bool, Source.Term.stops(bk, Source.Term.App{Source.Q1{}, z1, z2}),
                      Source.Term.stops(bk, Source.Term.spine(r2, Source.Term.Ref{r0})), True{},
                      Equal.cong(Source.Term, Bool, z => Source.Term.stops(bk, z), Source.Term.App{Source.Q1{}, z1, z2},
                        Source.Term.spine(r2, Source.Term.Ref{r0}), et),
                      Term.stops_of(bk, r0, r2, r1, g, w)))
        case Source.Q2{}:
          match args:
            case True{}:
              match r:
                case Term.Args.of{+k, +ys, +et, vs}:
                  Term.Values.split.by(bk, Spine.args(Source.Term.unspine(z1, [])), Con{Source.Arg{Source.Q2{}, z2}, Nil{}},
                    Term.Values.cast(bk, ys, List.append(&2, Source.Arg, Spine.args(Source.Term.unspine(z1, [])), Con{Source.Arg{Source.Q2{}, z2}, Nil{}}),
                      Term.snoc_ys(Source.Q2{}, z1, z2, k, ys, et), vs),
                    {Bool.and(Source.Term.is_value(z1, True{}, bk), Source.Term.is_value(z2, False{}, bk)) == True{} : Bool},
                    vf => vr => Bool.and_intro(Source.Term.is_value(z1, True{}, bk), Source.Term.is_value(z2, False{}, bk),
                      Term.is_value_complete.go(z1, True{}, bk, Term.Args.of{k, Spine.args(Source.Term.unspine(z1, [])), Term.snoc_f(Source.Q2{}, z1, z2, k, ys, et), vf}),
                      Term.is_value_complete.go(z2, False{}, bk, Term.Values.head(bk, Source.Q2{}, z2, Nil{}, vr))))
            case False{}:
              match r:
                case Spec.Term.Value.lam{r0, r1, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q2{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q2{}, z1, z2}, Source.Term.Lam{r0, r1}, et)))
                case Spec.Term.Value.prj{r0, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q2{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q2{}, z1, z2}, Source.Term.Prj{r0}, et)))
                case Spec.Term.Value.mat{r0, r1, r2, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q2{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q2{}, z1, z2}, Source.Term.Mat{r0, r1, r2}, et)))
                case Spec.Term.Value.efq{et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q2{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q2{}, z1, z2}, Source.Term.Efq{}, et)))
                case Spec.Term.Value.lab{r0, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q2{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q2{}, z1, z2}, Source.Term.Lab{r0}, et)))
                case Spec.Term.Value.rfl{et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q2{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q2{}, z1, z2}, Source.Term.Rfl{}, et)))
                case Spec.Term.Value.typ{r0, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q2{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q2{}, z1, z2}, Source.Term.Typ{r0}, et)))
                case Spec.Term.Value.all{r0, r1, r2, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q2{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q2{}, z1, z2}, Source.Term.All{r0, r1, r2}, et)))
                case Spec.Term.Value.sig{r0, r1, r2, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q2{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q2{}, z1, z2}, Source.Term.Sig{r0, r1, r2}, et)))
                case Spec.Term.Value.enu{r0, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q2{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q2{}, z1, z2}, Source.Term.Enu{r0}, et)))
                case Spec.Term.Value.eql{r0, r1, r2, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q2{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q2{}, z1, z2}, Source.Term.Eql{r0, r1, r2}, et)))
                case Spec.Term.Value.tup{r0, r1, r2, va, vb, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.App{Source.Q2{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.App{Source.Q2{}, z1, z2}, Source.Term.Tup{r0, r1, r2}, et)))
                case Spec.Term.Value.call{+r0, r1, +r2, g, vs, w, +et}:
                  Bool.and_intro(Bool.and(Source.Term.is_value(z1, True{}, bk), Source.Term.is_value(z2, False{}, bk)),
                    Source.Term.stops(bk, Source.Term.App{Source.Q2{}, z1, z2}),
                    Term.Values.split.by(bk, Spine.args(Source.Term.unspine(z1, [])), Con{Source.Arg{Source.Q2{}, z2}, Nil{}},
                      Term.Values.cast(bk, r2, List.append(&2, Source.Arg, Spine.args(Source.Term.unspine(z1, [])), Con{Source.Arg{Source.Q2{}, z2}, Nil{}}),
                        Term.snoc_ys(Source.Q2{}, z1, z2, r0, r2, et), vs),
                      {Bool.and(Source.Term.is_value(z1, True{}, bk), Source.Term.is_value(z2, False{}, bk)) == True{} : Bool},
                      vf => vr => Bool.and_intro(Source.Term.is_value(z1, True{}, bk), Source.Term.is_value(z2, False{}, bk),
                        Term.is_value_complete.go(z1, True{}, bk, Term.Args.of{r0, Spine.args(Source.Term.unspine(z1, [])), Term.snoc_f(Source.Q2{}, z1, z2, r0, r2, et), vf}),
                        Term.is_value_complete.go(z2, False{}, bk, Term.Values.head(bk, Source.Q2{}, z2, Nil{}, vr)))),
                    Equal.trans(Bool, Source.Term.stops(bk, Source.Term.App{Source.Q2{}, z1, z2}),
                      Source.Term.stops(bk, Source.Term.spine(r2, Source.Term.Ref{r0})), True{},
                      Equal.cong(Source.Term, Bool, z => Source.Term.stops(bk, z), Source.Term.App{Source.Q2{}, z1, z2},
                        Source.Term.spine(r2, Source.Term.Ref{r0}), et),
                      Term.stops_of(bk, r0, r2, r1, g, w)))
    case Source.Term.Sig{+z0, +z1, +z2}:
      match args:
        case True{}:
          match r:
            case Term.Args.of{k, ys, et, vs}:
              Empty.elim({Source.Term.is_value(Source.Term.Sig{z0, z1, z2}, True{}, bk) == True{} : Bool},
                Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Sig{z0, z1, z2}, [])), Source.Term.Ref{k},
                  Term.head_ref(Source.Term.Sig{z0, z1, z2}, ys, k, et))))
        case False{}:
          {==}
    case Source.Term.Tup{+z0, +z1, +z2}:
      match z0:
        case Source.Q0{}:
          match args:
            case True{}:
              match r:
                case Term.Args.of{k, ys, et, vs}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q0{}, z1, z2}, True{}, bk) == True{} : Bool},
                    Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Tup{Source.Q0{}, z1, z2}, [])), Source.Term.Ref{k},
                      Term.head_ref(Source.Term.Tup{Source.Q0{}, z1, z2}, ys, k, et))))
            case False{}:
              match r:
                case Spec.Term.Value.lam{r0, r1, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q0{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q0{}, z1, z2}, Source.Term.Lam{r0, r1}, et)))
                case Spec.Term.Value.prj{r0, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q0{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q0{}, z1, z2}, Source.Term.Prj{r0}, et)))
                case Spec.Term.Value.mat{r0, r1, r2, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q0{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q0{}, z1, z2}, Source.Term.Mat{r0, r1, r2}, et)))
                case Spec.Term.Value.efq{et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q0{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q0{}, z1, z2}, Source.Term.Efq{}, et)))
                case Spec.Term.Value.lab{r0, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q0{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q0{}, z1, z2}, Source.Term.Lab{r0}, et)))
                case Spec.Term.Value.rfl{et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q0{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q0{}, z1, z2}, Source.Term.Rfl{}, et)))
                case Spec.Term.Value.typ{r0, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q0{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q0{}, z1, z2}, Source.Term.Typ{r0}, et)))
                case Spec.Term.Value.all{r0, r1, r2, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q0{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q0{}, z1, z2}, Source.Term.All{r0, r1, r2}, et)))
                case Spec.Term.Value.sig{r0, r1, r2, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q0{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q0{}, z1, z2}, Source.Term.Sig{r0, r1, r2}, et)))
                case Spec.Term.Value.enu{r0, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q0{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q0{}, z1, z2}, Source.Term.Enu{r0}, et)))
                case Spec.Term.Value.eql{r0, r1, r2, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q0{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q0{}, z1, z2}, Source.Term.Eql{r0, r1, r2}, et)))
                case Spec.Term.Value.call{r0, r1, r2, g, vs, w, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q0{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Tup{Source.Q0{}, z1, z2}, [])), Source.Term.Ref{r0}, Term.head_ref(Source.Term.Tup{Source.Q0{}, z1, z2}, r2, r0, et))))
                case Spec.Term.Value.tup{r0, r1, r2, va, vb, +et}:
                  Term.is_value_complete.go(z2, False{}, bk, Term.Value.cast(bk, r2, z2, Equal.cong(Source.Term, Source.Term, Term.tup_b, Source.Term.Tup{r0, r1, r2}, Source.Term.Tup{Source.Q0{}, z1, z2}, Equal.sym(Source.Term, Source.Term.Tup{Source.Q0{}, z1, z2}, Source.Term.Tup{r0, r1, r2}, et)), vb))
        case Source.Q1{}:
          match args:
            case True{}:
              match r:
                case Term.Args.of{k, ys, et, vs}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q1{}, z1, z2}, True{}, bk) == True{} : Bool},
                    Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Tup{Source.Q1{}, z1, z2}, [])), Source.Term.Ref{k},
                      Term.head_ref(Source.Term.Tup{Source.Q1{}, z1, z2}, ys, k, et))))
            case False{}:
              match r:
                case Spec.Term.Value.lam{r0, r1, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q1{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q1{}, z1, z2}, Source.Term.Lam{r0, r1}, et)))
                case Spec.Term.Value.prj{r0, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q1{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q1{}, z1, z2}, Source.Term.Prj{r0}, et)))
                case Spec.Term.Value.mat{r0, r1, r2, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q1{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q1{}, z1, z2}, Source.Term.Mat{r0, r1, r2}, et)))
                case Spec.Term.Value.efq{et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q1{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q1{}, z1, z2}, Source.Term.Efq{}, et)))
                case Spec.Term.Value.lab{r0, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q1{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q1{}, z1, z2}, Source.Term.Lab{r0}, et)))
                case Spec.Term.Value.rfl{et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q1{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q1{}, z1, z2}, Source.Term.Rfl{}, et)))
                case Spec.Term.Value.typ{r0, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q1{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q1{}, z1, z2}, Source.Term.Typ{r0}, et)))
                case Spec.Term.Value.all{r0, r1, r2, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q1{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q1{}, z1, z2}, Source.Term.All{r0, r1, r2}, et)))
                case Spec.Term.Value.sig{r0, r1, r2, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q1{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q1{}, z1, z2}, Source.Term.Sig{r0, r1, r2}, et)))
                case Spec.Term.Value.enu{r0, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q1{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q1{}, z1, z2}, Source.Term.Enu{r0}, et)))
                case Spec.Term.Value.eql{r0, r1, r2, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q1{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q1{}, z1, z2}, Source.Term.Eql{r0, r1, r2}, et)))
                case Spec.Term.Value.call{r0, r1, r2, g, vs, w, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q1{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Tup{Source.Q1{}, z1, z2}, [])), Source.Term.Ref{r0}, Term.head_ref(Source.Term.Tup{Source.Q1{}, z1, z2}, r2, r0, et))))
                case Spec.Term.Value.tup{r0, r1, r2, va, vb, +et}:
                  Bool.and_intro(Source.Term.is_value(z1, False{}, bk), Source.Term.is_value(z2, False{}, bk),
                    Term.is_value_complete.go(z1, False{}, bk, Term.Value.when.cast(bk, Source.Quan.live(r0), Source.Quan.live(Source.Q1{}), r1, z1, Equal.cong(Source.Quan, Bool, Source.Quan.live, r0, Source.Q1{}, Equal.cong(Source.Term, Source.Quan, Term.tup_q, Source.Term.Tup{r0, r1, r2}, Source.Term.Tup{Source.Q1{}, z1, z2}, Equal.sym(Source.Term, Source.Term.Tup{Source.Q1{}, z1, z2}, Source.Term.Tup{r0, r1, r2}, et))), Equal.cong(Source.Term, Source.Term, Term.tup_a, Source.Term.Tup{r0, r1, r2}, Source.Term.Tup{Source.Q1{}, z1, z2}, Equal.sym(Source.Term, Source.Term.Tup{Source.Q1{}, z1, z2}, Source.Term.Tup{r0, r1, r2}, et)), va)), Term.is_value_complete.go(z2, False{}, bk, Term.Value.cast(bk, r2, z2, Equal.cong(Source.Term, Source.Term, Term.tup_b, Source.Term.Tup{r0, r1, r2}, Source.Term.Tup{Source.Q1{}, z1, z2}, Equal.sym(Source.Term, Source.Term.Tup{Source.Q1{}, z1, z2}, Source.Term.Tup{r0, r1, r2}, et)), vb)))
        case Source.Q2{}:
          match args:
            case True{}:
              match r:
                case Term.Args.of{k, ys, et, vs}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q2{}, z1, z2}, True{}, bk) == True{} : Bool},
                    Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Tup{Source.Q2{}, z1, z2}, [])), Source.Term.Ref{k},
                      Term.head_ref(Source.Term.Tup{Source.Q2{}, z1, z2}, ys, k, et))))
            case False{}:
              match r:
                case Spec.Term.Value.lam{r0, r1, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q2{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q2{}, z1, z2}, Source.Term.Lam{r0, r1}, et)))
                case Spec.Term.Value.prj{r0, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q2{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q2{}, z1, z2}, Source.Term.Prj{r0}, et)))
                case Spec.Term.Value.mat{r0, r1, r2, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q2{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q2{}, z1, z2}, Source.Term.Mat{r0, r1, r2}, et)))
                case Spec.Term.Value.efq{et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q2{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q2{}, z1, z2}, Source.Term.Efq{}, et)))
                case Spec.Term.Value.lab{r0, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q2{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q2{}, z1, z2}, Source.Term.Lab{r0}, et)))
                case Spec.Term.Value.rfl{et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q2{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q2{}, z1, z2}, Source.Term.Rfl{}, et)))
                case Spec.Term.Value.typ{r0, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q2{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q2{}, z1, z2}, Source.Term.Typ{r0}, et)))
                case Spec.Term.Value.all{r0, r1, r2, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q2{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q2{}, z1, z2}, Source.Term.All{r0, r1, r2}, et)))
                case Spec.Term.Value.sig{r0, r1, r2, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q2{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q2{}, z1, z2}, Source.Term.Sig{r0, r1, r2}, et)))
                case Spec.Term.Value.enu{r0, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q2{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q2{}, z1, z2}, Source.Term.Enu{r0}, et)))
                case Spec.Term.Value.eql{r0, r1, r2, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q2{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Tup{Source.Q2{}, z1, z2}, Source.Term.Eql{r0, r1, r2}, et)))
                case Spec.Term.Value.call{r0, r1, r2, g, vs, w, et}:
                  Empty.elim({Source.Term.is_value(Source.Term.Tup{Source.Q2{}, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Tup{Source.Q2{}, z1, z2}, [])), Source.Term.Ref{r0}, Term.head_ref(Source.Term.Tup{Source.Q2{}, z1, z2}, r2, r0, et))))
                case Spec.Term.Value.tup{r0, r1, r2, va, vb, +et}:
                  Bool.and_intro(Source.Term.is_value(z1, False{}, bk), Source.Term.is_value(z2, False{}, bk),
                    Term.is_value_complete.go(z1, False{}, bk, Term.Value.when.cast(bk, Source.Quan.live(r0), Source.Quan.live(Source.Q2{}), r1, z1, Equal.cong(Source.Quan, Bool, Source.Quan.live, r0, Source.Q2{}, Equal.cong(Source.Term, Source.Quan, Term.tup_q, Source.Term.Tup{r0, r1, r2}, Source.Term.Tup{Source.Q2{}, z1, z2}, Equal.sym(Source.Term, Source.Term.Tup{Source.Q2{}, z1, z2}, Source.Term.Tup{r0, r1, r2}, et))), Equal.cong(Source.Term, Source.Term, Term.tup_a, Source.Term.Tup{r0, r1, r2}, Source.Term.Tup{Source.Q2{}, z1, z2}, Equal.sym(Source.Term, Source.Term.Tup{Source.Q2{}, z1, z2}, Source.Term.Tup{r0, r1, r2}, et)), va)), Term.is_value_complete.go(z2, False{}, bk, Term.Value.cast(bk, r2, z2, Equal.cong(Source.Term, Source.Term, Term.tup_b, Source.Term.Tup{r0, r1, r2}, Source.Term.Tup{Source.Q2{}, z1, z2}, Equal.sym(Source.Term, Source.Term.Tup{Source.Q2{}, z1, z2}, Source.Term.Tup{r0, r1, r2}, et)), vb)))
    case Source.Term.Prj{+z0}:
      match args:
        case True{}:
          match r:
            case Term.Args.of{k, ys, et, vs}:
              Empty.elim({Source.Term.is_value(Source.Term.Prj{z0}, True{}, bk) == True{} : Bool},
                Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Prj{z0}, [])), Source.Term.Ref{k},
                  Term.head_ref(Source.Term.Prj{z0}, ys, k, et))))
        case False{}:
          {==}
    case Source.Term.Enu{+z0}:
      match args:
        case True{}:
          match r:
            case Term.Args.of{k, ys, et, vs}:
              Empty.elim({Source.Term.is_value(Source.Term.Enu{z0}, True{}, bk) == True{} : Bool},
                Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Enu{z0}, [])), Source.Term.Ref{k},
                  Term.head_ref(Source.Term.Enu{z0}, ys, k, et))))
        case False{}:
          {==}
    case Source.Term.Lab{+z0}:
      match args:
        case True{}:
          match r:
            case Term.Args.of{k, ys, et, vs}:
              Empty.elim({Source.Term.is_value(Source.Term.Lab{z0}, True{}, bk) == True{} : Bool},
                Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Lab{z0}, [])), Source.Term.Ref{k},
                  Term.head_ref(Source.Term.Lab{z0}, ys, k, et))))
        case False{}:
          {==}
    case Source.Term.Mat{+z0, +z1, +z2}:
      match args:
        case True{}:
          match r:
            case Term.Args.of{k, ys, et, vs}:
              Empty.elim({Source.Term.is_value(Source.Term.Mat{z0, z1, z2}, True{}, bk) == True{} : Bool},
                Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Mat{z0, z1, z2}, [])), Source.Term.Ref{k},
                  Term.head_ref(Source.Term.Mat{z0, z1, z2}, ys, k, et))))
        case False{}:
          {==}
    case Source.Term.Efq{}:
      match args:
        case True{}:
          match r:
            case Term.Args.of{k, ys, et, vs}:
              Empty.elim({Source.Term.is_value(Source.Term.Efq{}, True{}, bk) == True{} : Bool},
                Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Efq{}, [])), Source.Term.Ref{k},
                  Term.head_ref(Source.Term.Efq{}, ys, k, et))))
        case False{}:
          {==}
    case Source.Term.Eql{+z0, +z1, +z2}:
      match args:
        case True{}:
          match r:
            case Term.Args.of{k, ys, et, vs}:
              Empty.elim({Source.Term.is_value(Source.Term.Eql{z0, z1, z2}, True{}, bk) == True{} : Bool},
                Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Eql{z0, z1, z2}, [])), Source.Term.Ref{k},
                  Term.head_ref(Source.Term.Eql{z0, z1, z2}, ys, k, et))))
        case False{}:
          {==}
    case Source.Term.Rfl{}:
      match args:
        case True{}:
          match r:
            case Term.Args.of{k, ys, et, vs}:
              Empty.elim({Source.Term.is_value(Source.Term.Rfl{}, True{}, bk) == True{} : Bool},
                Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Rfl{}, [])), Source.Term.Ref{k},
                  Term.head_ref(Source.Term.Rfl{}, ys, k, et))))
        case False{}:
          {==}
    case Source.Term.Rwt{+z0, +z1, +z2}:
      match args:
        case True{}:
          match r:
            case Term.Args.of{k, ys, et, vs}:
              Empty.elim({Source.Term.is_value(Source.Term.Rwt{z0, z1, z2}, True{}, bk) == True{} : Bool},
                Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Rwt{z0, z1, z2}, [])), Source.Term.Ref{k},
                  Term.head_ref(Source.Term.Rwt{z0, z1, z2}, ys, k, et))))
        case False{}:
          match r:
            case Spec.Term.Value.lam{r0, r1, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Rwt{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Rwt{z0, z1, z2}, Source.Term.Lam{r0, r1}, et)))
            case Spec.Term.Value.prj{r0, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Rwt{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Rwt{z0, z1, z2}, Source.Term.Prj{r0}, et)))
            case Spec.Term.Value.mat{r0, r1, r2, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Rwt{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Rwt{z0, z1, z2}, Source.Term.Mat{r0, r1, r2}, et)))
            case Spec.Term.Value.efq{et}:
              Empty.elim({Source.Term.is_value(Source.Term.Rwt{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Rwt{z0, z1, z2}, Source.Term.Efq{}, et)))
            case Spec.Term.Value.lab{r0, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Rwt{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Rwt{z0, z1, z2}, Source.Term.Lab{r0}, et)))
            case Spec.Term.Value.rfl{et}:
              Empty.elim({Source.Term.is_value(Source.Term.Rwt{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Rwt{z0, z1, z2}, Source.Term.Rfl{}, et)))
            case Spec.Term.Value.typ{r0, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Rwt{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Rwt{z0, z1, z2}, Source.Term.Typ{r0}, et)))
            case Spec.Term.Value.all{r0, r1, r2, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Rwt{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Rwt{z0, z1, z2}, Source.Term.All{r0, r1, r2}, et)))
            case Spec.Term.Value.sig{r0, r1, r2, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Rwt{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Rwt{z0, z1, z2}, Source.Term.Sig{r0, r1, r2}, et)))
            case Spec.Term.Value.enu{r0, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Rwt{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Rwt{z0, z1, z2}, Source.Term.Enu{r0}, et)))
            case Spec.Term.Value.eql{r0, r1, r2, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Rwt{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Rwt{z0, z1, z2}, Source.Term.Eql{r0, r1, r2}, et)))
            case Spec.Term.Value.tup{r0, r1, r2, va, vb, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Rwt{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Source.Term.Rwt{z0, z1, z2}, Source.Term.Tup{r0, r1, r2}, et)))
            case Spec.Term.Value.call{r0, r1, r2, g, vs, w, et}:
              Empty.elim({Source.Term.is_value(Source.Term.Rwt{z0, z1, z2}, False{}, bk) == True{} : Bool}, Bool.no(Term.clash(Spine.head(Source.Term.unspine(Source.Term.Rwt{z0, z1, z2}, [])), Source.Term.Ref{r0}, Term.head_ref(Source.Term.Rwt{z0, z1, z2}, r2, r0, et))))

def Spec.Term.is_value_complete(bk, t, v):
  Term.is_value_complete.go(t, False{}, bk, v)

