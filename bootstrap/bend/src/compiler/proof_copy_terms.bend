# compiler: the copy's terms
# ==========================
#
# Lemmas of Term.shift and Term.subst that a round of the copy's walk uses,
# with layer B's bound of free variables (Term.below, the fv of Nd):
#
# - a part whose free variables are all below the cutoff is shared: the
#   shift and the substitution keep it (shift_closed, subst_closed); a shift
#   by 0 keeps any term (shift_zero); a higher bound keeps Term.below
#   (below_mono);
# - the variables of M.copy's part, at the depth d: one of the locals is
#   the local shifted by d (sb.env, with ev.get for the local); one past them
#   is Var(i - |e|) (sb.past);
# - the fv of a node: a part of fv v, under b binders, with v - b at most cm,
#   is below b + cm (below_up).

import Base
import ./impl.bend as C
import ./proof_need.bend as N
import ./proof_mach_defs.bend as PM
import ./proof_copy_kit.bend as K

# Kit
# ---

# no Nat is below 0
def Tz.lt0(i: Nat) -> {Nat.is_lt(i, 0n) == False{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Tz.lt0.no(i: Nat, -G: Type, h: {Nat.is_lt(i, 0n) == True{} : Bool}) -> G:
  match i:
    case 0n:
      K.Bo.tf(G, h)
    case 1n+p:
      K.Bo.tf(G, h)

def Tz.sub0(a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# i < n <= m gives i < m
def Tz.lt_le(i: Nat, n: Nat, m: Nat, h1: {Nat.is_lt(i, n) == True{} : Bool}, h2: {Nat.is_le(n, m) == True{} : Bool}) ->
  {Nat.is_lt(i, m) == True{} : Bool}:
  match i:
    case 0n:
      match n:
        case 0n:
          K.Bo.tf({Nat.is_lt(0n, m) == True{} : Bool}, h1)
        case 1n+np:
          match m:
            case 0n:
              K.Bo.tf({Nat.is_lt(0n, 0n) == True{} : Bool}, h2)
            case 1n+mp:
              {==}
    case 1n+ip:
      match n:
        case 0n:
          K.Bo.tf({Nat.is_lt(1n+ip, m) == True{} : Bool}, h1)
        case 1n+np:
          match m:
            case 0n:
              K.Bo.tf({Nat.is_lt(1n+ip, 0n) == True{} : Bool}, h2)
            case 1n+mp:
              Tz.lt_le(ip, np, mp, h1, h2)

# not i < l gives l <= i
def Tz.nlt_le(i: Nat, l: Nat, h: {Nat.is_lt(i, l) == False{} : Bool}) -> {Nat.is_le(l, i) == True{} : Bool}:
  match l:
    case 0n:
      K.Na.le0(i)
    case 1n+lp:
      match i:
        case 0n:
          K.Bo.ft({Nat.is_le(1n+lp, 0n) == True{} : Bool}, h)
        case 1n+ip:
          Tz.nlt_le(ip, lp, h)

# a - b <= a
def Tz.sub_le(a: Nat, b: Nat) -> {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n++ap:
      match b:
        case 0n:
          K.Na.le_refl(1n+ap)
        case 1n++bp:
          K.Na.le_up(Nat.sub(ap, bp), ap, Tz.sub_le(ap, bp))

# l <= x <= y gives l <= y
def Tz.le_trans(l: Nat, x: Nat, y: Nat, h1: {Nat.is_le(l, x) == True{} : Bool}, h2: {Nat.is_le(x, y) == True{} : Bool}) ->
  {Nat.is_le(l, y) == True{} : Bool}:
  match l:
    case 0n:
      K.Na.le0(y)
    case 1n+lp:
      match x:
        case 0n:
          K.Bo.tf({Nat.is_le(1n+lp, y) == True{} : Bool}, h1)
        case 1n+xp:
          match y:
            case 0n:
              K.Bo.tf({Nat.is_le(1n+lp, 0n) == True{} : Bool}, h2)
            case 1n+yp:
              Tz.le_trans(lp, xp, yp, h1, h2)

# l <= a: (1 + a) - l is 1 + (a - l)
def Tz.sub_succ(a: Nat, l: Nat, h: {Nat.is_le(l, a) == True{} : Bool}) -> {Nat.sub(1n+a, l) == 1n+Nat.sub(a, l) : Nat}:
  match l:
    case 0n:
      %Equal.sym(Nat, Nat.sub(a, 0n), a, Tz.sub0(a)) : {1n+a == 1n+_ : Nat}
      {==}
    case 1n+lp:
      match a:
        case 0n:
          K.Bo.tf({Nat.sub(1n, 1n+lp) == 1n+Nat.sub(0n, 1n+lp) : Nat}, h)
        case 1n+ap:
          Tz.sub_succ(ap, lp, h)

# i - d - l + d is i - l, when d <= i and l <= i - d
def Tz.subsub(i: Nat, d: Nat, +l: Nat, h1: {Nat.is_lt(i, d) == False{} : Bool},
  +h2: {Nat.is_lt(Nat.sub(i, d), l) == False{} : Bool}) -> {Nat.add(Nat.sub(Nat.sub(i, d), l), d) == Nat.sub(i, l) : Nat}:
  match d:
    case 0n:
      %Equal.sym(Nat, Nat.add(Nat.sub(Nat.sub(i, 0n), l), 0n), Nat.sub(Nat.sub(i, 0n), l), N.add_zero(Nat.sub(Nat.sub(i, 0n), l))) : {_ == Nat.sub(i, l) : Nat}
      %Equal.sym(Nat, Nat.sub(i, 0n), i, Tz.sub0(i)) : {Nat.sub(_, l) == Nat.sub(i, l) : Nat}
      {==}
    case 1n++dp:
      match i:
        case 0n:
          K.Bo.ft({Nat.add(Nat.sub(Nat.sub(0n, 1n+dp), l), 1n+dp) == Nat.sub(0n, l) : Nat}, h1)
        case 1n++ip:
          +le = Tz.le_trans(l, Nat.sub(ip, dp), ip, Tz.nlt_le(Nat.sub(ip, dp), l, h2), Tz.sub_le(ip, dp))
          %Equal.sym(Nat, Nat.sub(1n+ip, l), 1n+Nat.sub(ip, l), Tz.sub_succ(ip, l, le)) : {Nat.add(Nat.sub(Nat.sub(ip, dp), l), 1n+dp) == _ : Nat}
          %Equal.sym(Nat, Nat.add(Nat.sub(Nat.sub(ip, dp), l), 1n+dp), 1n+Nat.add(Nat.sub(Nat.sub(ip, dp), l), dp), N.add_succ_r(Nat.sub(Nat.sub(ip, dp), l), dp)) : {_ == 1n+Nat.sub(ip, l) : Nat}
          %Equal.sym(Nat, Nat.add(Nat.sub(Nat.sub(ip, dp), l), dp), Nat.sub(ip, l), Tz.subsub(ip, dp, l, h1, h2)) : {1n+_ == 1n+Nat.sub(ip, l) : Nat}
          {==}

# v - b <= cm gives v <= b + cm
def Tz.sub_add(v: Nat, b: Nat, +cm: Nat, h: {Nat.is_le(Nat.sub(v, b), cm) == True{} : Bool}) ->
  {Nat.is_le(v, Nat.add(b, cm)) == True{} : Bool}:
  match b:
    case 0n:
      %Tz.sub0(v) : {Nat.is_le(_, cm) == True{} : Bool}
      h
    case 1n+bp:
      match v:
        case 0n:
          {==}
        case 1n+vp:
          Tz.sub_add(vp, bp, cm, h)

# congruences of the formers
def Tz.cg1(-k: C.Term -> C.Term, -a: C.Term, -b: C.Term, e: {a == b : C.Term}) -> {k(a) == k(b) : C.Term}:
  %e : {k(a) == k(_) : C.Term}
  {==}

def Tz.cg2(-k: C.Term -> C.Term -> C.Term, -a1: C.Term, -a2: C.Term, -b1: C.Term, -b2: C.Term,
  e1: {a1 == b1 : C.Term}, e2: {a2 == b2 : C.Term}) -> {k(a1, a2) == k(b1, b2) : C.Term}:
  %e1 : {k(a1, a2) == k(_, b2) : C.Term}
  %e2 : {k(a1, a2) == k(a1, _) : C.Term}
  {==}

def Tz.cg3(-k: C.Term -> C.Term -> C.Term -> C.Term, -a1: C.Term, -a2: C.Term, -a3: C.Term, -b1: C.Term, -b2: C.Term,
  -b3: C.Term, e1: {a1 == b1 : C.Term}, e2: {a2 == b2 : C.Term}, e3: {a3 == b3 : C.Term}) ->
  {k(a1, a2, a3) == k(b1, b2, b3) : C.Term}:
  %e1 : {k(a1, a2, a3) == k(_, b2, b3) : C.Term}
  %e2 : {k(a1, a2, a3) == k(a1, _, b3) : C.Term}
  %e3 : {k(a1, a2, a3) == k(a1, a2, _) : C.Term}
  {==}

# Term.below
# ----------

# a higher bound keeps Term.below
def Tz.below_mono(t: C.Term, +n: Nat, +m: Nat, +h: {Nat.is_le(n, m) == True{} : Bool},
  +hb: {PM.Term.below(t, n) == True{} : Bool}) -> {PM.Term.below(t, m) == True{} : Bool}:
  match t:
    case C.Term.Var{i}:
      Tz.lt_le(i, n, m, hb, h)
    case C.Term.Ref{_}:
      {==}
    case C.Term.Ann{+x, +y}:
      K.Bo.and_i(PM.Term.below(x, m), PM.Term.below(y, m),
        Tz.below_mono(x, n, m, h, K.Bo.and_l(PM.Term.below(x, n), PM.Term.below(y, n), hb)),
        Tz.below_mono(y, n, m, h, K.Bo.and_r(PM.Term.below(x, n), PM.Term.below(y, n), hb)))
    case C.Term.Let{_, +v, +f}:
      K.Bo.and_i(PM.Term.below(v, m), PM.Term.below(f, 1n+m),
        Tz.below_mono(v, n, m, h, K.Bo.and_l(PM.Term.below(v, n), PM.Term.below(f, 1n+n), hb)),
        Tz.below_mono(f, 1n+n, 1n+m, h, K.Bo.and_r(PM.Term.below(v, n), PM.Term.below(f, 1n+n), hb)))
    case C.Term.Typ{x}:
      Tz.below_mono(x, n, m, h, hb)
    case C.Term.Min{+x, +y}:
      K.Bo.and_i(PM.Term.below(x, m), PM.Term.below(y, m),
        Tz.below_mono(x, n, m, h, K.Bo.and_l(PM.Term.below(x, n), PM.Term.below(y, n), hb)),
        Tz.below_mono(y, n, m, h, K.Bo.and_r(PM.Term.below(x, n), PM.Term.below(y, n), hb)))
    case C.Term.All{_, +x, +y}:
      K.Bo.and_i(PM.Term.below(x, m), PM.Term.below(y, 1n+m),
        Tz.below_mono(x, n, m, h, K.Bo.and_l(PM.Term.below(x, n), PM.Term.below(y, 1n+n), hb)),
        Tz.below_mono(y, 1n+n, 1n+m, h, K.Bo.and_r(PM.Term.below(x, n), PM.Term.below(y, 1n+n), hb)))
    case C.Term.Lam{_, f}:
      Tz.below_mono(f, 1n+n, 1n+m, h, hb)
    case C.Term.App{_, +x, +y}:
      K.Bo.and_i(PM.Term.below(x, m), PM.Term.below(y, m),
        Tz.below_mono(x, n, m, h, K.Bo.and_l(PM.Term.below(x, n), PM.Term.below(y, n), hb)),
        Tz.below_mono(y, n, m, h, K.Bo.and_r(PM.Term.below(x, n), PM.Term.below(y, n), hb)))
    case C.Term.Sig{_, +x, +y}:
      K.Bo.and_i(PM.Term.below(x, m), PM.Term.below(y, 1n+m),
        Tz.below_mono(x, n, m, h, K.Bo.and_l(PM.Term.below(x, n), PM.Term.below(y, 1n+n), hb)),
        Tz.below_mono(y, 1n+n, 1n+m, h, K.Bo.and_r(PM.Term.below(x, n), PM.Term.below(y, 1n+n), hb)))
    case C.Term.Tup{_, +x, +y}:
      K.Bo.and_i(PM.Term.below(x, m), PM.Term.below(y, m),
        Tz.below_mono(x, n, m, h, K.Bo.and_l(PM.Term.below(x, n), PM.Term.below(y, n), hb)),
        Tz.below_mono(y, n, m, h, K.Bo.and_r(PM.Term.below(x, n), PM.Term.below(y, n), hb)))
    case C.Term.Prj{x}:
      Tz.below_mono(x, n, m, h, hb)
    case C.Term.Enu{_}:
      {==}
    case C.Term.Lab{_}:
      {==}
    case C.Term.Mat{_, +x, +y}:
      K.Bo.and_i(PM.Term.below(x, m), PM.Term.below(y, m),
        Tz.below_mono(x, n, m, h, K.Bo.and_l(PM.Term.below(x, n), PM.Term.below(y, n), hb)),
        Tz.below_mono(y, n, m, h, K.Bo.and_r(PM.Term.below(x, n), PM.Term.below(y, n), hb)))
    case C.Term.Efq{}:
      {==}
    case C.Term.Eql{+x, +y, +z}:
      +r = K.Bo.and_r(PM.Term.below(x, n), Bool.and(PM.Term.below(y, n), PM.Term.below(z, n)), hb)
      K.Bo.and_i(PM.Term.below(x, m), Bool.and(PM.Term.below(y, m), PM.Term.below(z, m)),
        Tz.below_mono(x, n, m, h, K.Bo.and_l(PM.Term.below(x, n), Bool.and(PM.Term.below(y, n), PM.Term.below(z, n)), hb)),
        K.Bo.and_i(PM.Term.below(y, m), PM.Term.below(z, m),
          Tz.below_mono(y, n, m, h, K.Bo.and_l(PM.Term.below(y, n), PM.Term.below(z, n), r)),
          Tz.below_mono(z, n, m, h, K.Bo.and_r(PM.Term.below(y, n), PM.Term.below(z, n), r))))
    case C.Term.Rfl{}:
      {==}
    case C.Term.Rwt{+x, +y, +z}:
      +r = K.Bo.and_r(PM.Term.below(x, n), Bool.and(PM.Term.below(y, 2n+n), PM.Term.below(z, n)), hb)
      K.Bo.and_i(PM.Term.below(x, m), Bool.and(PM.Term.below(y, 2n+m), PM.Term.below(z, m)),
        Tz.below_mono(x, n, m, h, K.Bo.and_l(PM.Term.below(x, n), Bool.and(PM.Term.below(y, 2n+n), PM.Term.below(z, n)), hb)),
        K.Bo.and_i(PM.Term.below(y, 2n+m), PM.Term.below(z, m),
          Tz.below_mono(y, 2n+n, 2n+m, h, K.Bo.and_l(PM.Term.below(y, 2n+n), PM.Term.below(z, n), r)),
          Tz.below_mono(z, n, m, h, K.Bo.and_r(PM.Term.below(y, 2n+n), PM.Term.below(z, n), r))))

# the fv of a node: a part of fv v, under b binders, with v - b at most cm,
# is below b + cm
def Tz.below_up(t: C.Term, +v: Nat, +b: Nat, +cm: Nat, hb: {PM.Term.below(t, v) == True{} : Bool},
  h: {Nat.is_le(Nat.sub(v, b), cm) == True{} : Bool}) -> {PM.Term.below(t, Nat.add(b, cm)) == True{} : Bool}:
  Tz.below_mono(t, v, Nat.add(b, cm), Tz.sub_add(v, b, cm, h), hb)
