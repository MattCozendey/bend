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
def Tz.lt0(i: Nat) -> {Nat.is_lt(i, 0n) == False{}: Bool}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Tz.lt0.no(i: Nat, -G: Type, h: {Nat.is_lt(i, 0n) == True{}: Bool}) -> G:
  match i:
    case 0n:
      K.Bo.tf(G, h)
    case 1n+p:
      K.Bo.tf(G, h)

def Tz.sub0(a: Nat) -> {Nat.sub(a, 0n) == a: Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# i < n <= m gives i < m
def Tz.lt_le(
  i: Nat,
  n: Nat,
  m: Nat,
  h1: {Nat.is_lt(i, n) == True{}: Bool},
  h2: {Nat.is_le(n, m) == True{}: Bool}
) -> {Nat.is_lt(i, m) == True{}: Bool}:
  match i:
    case 0n:
      match n:
        case 0n:
          K.Bo.tf({Nat.is_lt(0n, m) == True{}: Bool}, h1)
        case 1n+np:
          match m:
            case 0n:
              K.Bo.tf({Nat.is_lt(0n, 0n) == True{}: Bool}, h2)
            case 1n+mp:
              {==}
    case 1n+ip:
      match n:
        case 0n:
          K.Bo.tf({Nat.is_lt(1n+ip, m) == True{}: Bool}, h1)
        case 1n+np:
          match m:
            case 0n:
              K.Bo.tf({Nat.is_lt(1n+ip, 0n) == True{}: Bool}, h2)
            case 1n+mp:
              Tz.lt_le(ip, np, mp, h1, h2)

# not i < l gives l <= i
def Tz.nlt_le(
  i: Nat,
  l: Nat,
  h: {Nat.is_lt(i, l) == False{}: Bool}
) -> {Nat.is_le(l, i) == True{}: Bool}:
  match i:
    case 0n:
      match l:
        case 0n:
          {==}
        case 1n+lp:
          K.Bo.ft({Nat.is_le(1n+lp, 0n) == True{}: Bool}, h)
    case 1n+ip:
      match l:
        case 0n:
          {==}
        case 1n+lp:
          Tz.nlt_le(ip, lp, h)

# a - b <= a
def Tz.sub_le(a: Nat, b: Nat) -> {Nat.is_le(Nat.sub(a, b), a) == True{}: Bool}:
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
def Tz.le_trans(
  l: Nat,
  x: Nat,
  y: Nat,
  h1: {Nat.is_le(l, x) == True{}: Bool},
  h2: {Nat.is_le(x, y) == True{}: Bool}
) -> {Nat.is_le(l, y) == True{}: Bool}:
  match l:
    case 0n:
      K.Na.le0(y)
    case 1n+lp:
      match x:
        case 0n:
          K.Bo.tf({Nat.is_le(1n+lp, y) == True{}: Bool}, h1)
        case 1n+xp:
          match y:
            case 0n:
              K.Bo.tf({Nat.is_le(1n+lp, 0n) == True{}: Bool}, h2)
            case 1n+yp:
              Tz.le_trans(lp, xp, yp, h1, h2)

# l <= a: (1 + a) - l is 1 + (a - l)
def Tz.sub_succ(
  a: Nat,
  l: Nat,
  h: {Nat.is_le(l, a) == True{}: Bool}
) -> {Nat.sub(1n+a, l) == 1n+Nat.sub(a, l): Nat}:
  match a:
    case 0n:
      match l:
        case 0n:
          {==}
        case 1n+lp:
          K.Bo.tf({Nat.sub(1n, 1n+lp) == 1n+Nat.sub(0n, 1n+lp): Nat}, h)
    case 1n+ap:
      match l:
        case 0n:
          {==}
        case 1n+lp:
          Tz.sub_succ(ap, lp, h)

# i - d - l + d is i - l, when d <= i and l <= i - d
def Tz.subsub(
  i: Nat,
  d: Nat,
  +l: Nat,
  h1: {Nat.is_lt(i, d) == False{}: Bool},
  +h2: {Nat.is_lt(Nat.sub(i, d), l) == False{}: Bool}
) -> {Nat.add(Nat.sub(Nat.sub(i, d), l), d) == Nat.sub(i, l): Nat}:
  match i:
    case 0n:
      match d:
        case 0n:
          {==}
        case 1n+dp:
          K.Bo.ft({Nat.add(Nat.sub(Nat.sub(0n, 1n+dp), l), 1n+dp) == Nat.sub(0n, l): Nat}, h1)
    case 1n++ip:
      match d:
        case 0n:
          N.add_zero(Nat.sub(1n+ip, l))
        case 1n++dp:
          +le = Tz.le_trans(
            l,
            Nat.sub(ip, dp),
            ip,
            Tz.nlt_le(Nat.sub(ip, dp), l, h2),
            Tz.sub_le(ip, dp)
          )
          %Equal.sym(
            Nat,
            Nat.sub(1n+ip, l),
            1n+Nat.sub(ip, l),
            Tz.sub_succ(ip, l, le)
          ): {Nat.add(Nat.sub(Nat.sub(ip, dp), l), 1n+dp) == _: Nat}
          %Equal.sym(
            Nat,
            Nat.add(Nat.sub(Nat.sub(ip, dp), l), 1n+dp),
            1n+Nat.add(Nat.sub(Nat.sub(ip, dp), l), dp),
            N.add_succ_r(Nat.sub(Nat.sub(ip, dp), l), dp)
          ): {_ == 1n+Nat.sub(ip, l): Nat}
          %Equal.sym(
            Nat,
            Nat.add(Nat.sub(Nat.sub(ip, dp), l), dp),
            Nat.sub(ip, l),
            Tz.subsub(ip, dp, l, h1, h2)
          ): {1n+_ == 1n+Nat.sub(ip, l): Nat}
          {==}

# v - b <= cm gives v <= b + cm
def Tz.sub_add(
  v: Nat,
  b: Nat,
  +cm: Nat,
  h: {Nat.is_le(Nat.sub(v, b), cm) == True{}: Bool}
) -> {Nat.is_le(v, Nat.add(b, cm)) == True{}: Bool}:
  match v:
    case 0n:
      K.Na.le0(Nat.add(b, cm))
    case 1n+vp:
      match b:
        case 0n:
          h
        case 1n+bp:
          Tz.sub_add(vp, bp, cm, h)

# congruences of the formers
def Tz.cg1(
  -k: C.Term -> C.Term,
  -a: C.Term,
  -b: C.Term,
  e: {a == b: C.Term}
) -> {k(a) == k(b): C.Term}:
  %e: {k(a) == k(_): C.Term}
  {==}

def Tz.cg2(
  -k: C.Term -> C.Term -> C.Term,
  -a1: C.Term,
  -a2: C.Term,
  -b1: C.Term,
  -b2: C.Term,
  e1: {a1 == b1: C.Term},
  e2: {a2 == b2: C.Term}
) -> {k(a1, a2) == k(b1, b2): C.Term}:
  %e1: {k(a1, a2) == k(_, b2): C.Term}
  %e2: {k(a1, a2) == k(a1, _): C.Term}
  {==}

def Tz.cg3(
  -k: C.Term -> C.Term -> C.Term -> C.Term,
  -a1: C.Term,
  -a2: C.Term,
  -a3: C.Term,
  -b1: C.Term,
  -b2: C.Term,
  -b3: C.Term,
  e1: {a1 == b1: C.Term},
  e2: {a2 == b2: C.Term},
  e3: {a3 == b3: C.Term}
) -> {k(a1, a2, a3) == k(b1, b2, b3): C.Term}:
  %e1: {k(a1, a2, a3) == k(_, b2, b3): C.Term}
  %e2: {k(a1, a2, a3) == k(a1, _, b3): C.Term}
  %e3: {k(a1, a2, a3) == k(a1, a2, _): C.Term}
  {==}

# Shifts and substitutions
# ------------------------

# a shift keeps a term whose free variables are all below the cutoff c
def Tz.shift_closed(
  t: C.Term,
  +d: Nat,
  +c: Nat,
  +hb: {PM.Term.below(t, c) == True{}: Bool}
) -> {C.Term.shift(t, d, c) == t: C.Term}:
  match t:
    case C.Term.Var{+i}:
      %Equal.sym(
        Bool,
        Nat.is_lt(i, c),
        True{},
        hb
      ): {C.Term.Var{C.Term.shift.at(_, i, d)} == C.Term.Var{i}: C.Term}
      {==}
    case C.Term.Ann{+x, +y}:
      Tz.cg2(
        X0 => Y0 => C.Term.Ann{X0, Y0},
        C.Term.shift(x, d, c),
        C.Term.shift(y, d, c),
        x,
        y,
        Tz.shift_closed(x, d, c, K.Bo.and_l(PM.Term.below(x, c), PM.Term.below(y, c), hb)),
        Tz.shift_closed(y, d, c, K.Bo.and_r(PM.Term.below(x, c), PM.Term.below(y, c), hb))
      )
    case C.Term.Let{+q, +x, +y}:
      Tz.cg2(
        X0 => Y0 => C.Term.Let{q, X0, Y0},
        C.Term.shift(x, d, c),
        C.Term.shift(y, d, 1n+c),
        x,
        y,
        Tz.shift_closed(x, d, c, K.Bo.and_l(PM.Term.below(x, c), PM.Term.below(y, 1n+c), hb)),
        Tz.shift_closed(y, d, 1n+c, K.Bo.and_r(PM.Term.below(x, c), PM.Term.below(y, 1n+c), hb))
      )
    case C.Term.Typ{+x}:
      Tz.cg1(X0 => C.Term.Typ{X0}, C.Term.shift(x, d, c), x, Tz.shift_closed(x, d, c, hb))
    case C.Term.Min{+x, +y}:
      Tz.cg2(
        X0 => Y0 => C.Term.Min{X0, Y0},
        C.Term.shift(x, d, c),
        C.Term.shift(y, d, c),
        x,
        y,
        Tz.shift_closed(x, d, c, K.Bo.and_l(PM.Term.below(x, c), PM.Term.below(y, c), hb)),
        Tz.shift_closed(y, d, c, K.Bo.and_r(PM.Term.below(x, c), PM.Term.below(y, c), hb))
      )
    case C.Term.All{+q, +x, +y}:
      Tz.cg2(
        X0 => Y0 => C.Term.All{q, X0, Y0},
        C.Term.shift(x, d, c),
        C.Term.shift(y, d, 1n+c),
        x,
        y,
        Tz.shift_closed(x, d, c, K.Bo.and_l(PM.Term.below(x, c), PM.Term.below(y, 1n+c), hb)),
        Tz.shift_closed(y, d, 1n+c, K.Bo.and_r(PM.Term.below(x, c), PM.Term.below(y, 1n+c), hb))
      )
    case C.Term.Lam{+q, +x}:
      Tz.cg1(X0 => C.Term.Lam{q, X0}, C.Term.shift(x, d, 1n+c), x, Tz.shift_closed(x, d, 1n+c, hb))
    case C.Term.App{+q, +x, +y}:
      Tz.cg2(
        X0 => Y0 => C.Term.App{q, X0, Y0},
        C.Term.shift(x, d, c),
        C.Term.shift(y, d, c),
        x,
        y,
        Tz.shift_closed(x, d, c, K.Bo.and_l(PM.Term.below(x, c), PM.Term.below(y, c), hb)),
        Tz.shift_closed(y, d, c, K.Bo.and_r(PM.Term.below(x, c), PM.Term.below(y, c), hb))
      )
    case C.Term.Sig{+q, +x, +y}:
      Tz.cg2(
        X0 => Y0 => C.Term.Sig{q, X0, Y0},
        C.Term.shift(x, d, c),
        C.Term.shift(y, d, 1n+c),
        x,
        y,
        Tz.shift_closed(x, d, c, K.Bo.and_l(PM.Term.below(x, c), PM.Term.below(y, 1n+c), hb)),
        Tz.shift_closed(y, d, 1n+c, K.Bo.and_r(PM.Term.below(x, c), PM.Term.below(y, 1n+c), hb))
      )
    case C.Term.Tup{+q, +x, +y}:
      Tz.cg2(
        X0 => Y0 => C.Term.Tup{q, X0, Y0},
        C.Term.shift(x, d, c),
        C.Term.shift(y, d, c),
        x,
        y,
        Tz.shift_closed(x, d, c, K.Bo.and_l(PM.Term.below(x, c), PM.Term.below(y, c), hb)),
        Tz.shift_closed(y, d, c, K.Bo.and_r(PM.Term.below(x, c), PM.Term.below(y, c), hb))
      )
    case C.Term.Prj{+x}:
      Tz.cg1(X0 => C.Term.Prj{X0}, C.Term.shift(x, d, c), x, Tz.shift_closed(x, d, c, hb))
    case C.Term.Mat{+k, +x, +y}:
      Tz.cg2(
        X0 => Y0 => C.Term.Mat{k, X0, Y0},
        C.Term.shift(x, d, c),
        C.Term.shift(y, d, c),
        x,
        y,
        Tz.shift_closed(x, d, c, K.Bo.and_l(PM.Term.below(x, c), PM.Term.below(y, c), hb)),
        Tz.shift_closed(y, d, c, K.Bo.and_r(PM.Term.below(x, c), PM.Term.below(y, c), hb))
      )
    case C.Term.Eql{+x, +y, +z}:
      +r = K.Bo.and_r(PM.Term.below(x, c), Bool.and(PM.Term.below(y, c), PM.Term.below(z, c)), hb)
      Tz.cg3(
        X0 => Y0 => Z0 => C.Term.Eql{X0, Y0, Z0},
        C.Term.shift(x, d, c),
        C.Term.shift(y, d, c),
        C.Term.shift(z, d, c),
        x,
        y,
        z,
        Tz.shift_closed(
          x,
          d,
          c,
          K.Bo.and_l(PM.Term.below(x, c), Bool.and(PM.Term.below(y, c), PM.Term.below(z, c)), hb)
        ),
        Tz.shift_closed(y, d, c, K.Bo.and_l(PM.Term.below(y, c), PM.Term.below(z, c), r)),
        Tz.shift_closed(z, d, c, K.Bo.and_r(PM.Term.below(y, c), PM.Term.below(z, c), r))
      )
    case C.Term.Rwt{+x, +y, +z}:
      +r = K.Bo.and_r(
        PM.Term.below(x, c),
        Bool.and(PM.Term.below(y, 2n+c), PM.Term.below(z, c)),
        hb
      )
      Tz.cg3(
        X0 => Y0 => Z0 => C.Term.Rwt{X0, Y0, Z0},
        C.Term.shift(x, d, c),
        C.Term.shift(y, d, 2n+c),
        C.Term.shift(z, d, c),
        x,
        y,
        z,
        Tz.shift_closed(
          x,
          d,
          c,
          K.Bo.and_l(PM.Term.below(x, c), Bool.and(PM.Term.below(y, 2n+c), PM.Term.below(z, c)), hb)
        ),
        Tz.shift_closed(y, d, 2n+c, K.Bo.and_l(PM.Term.below(y, 2n+c), PM.Term.below(z, c), r)),
        Tz.shift_closed(z, d, c, K.Bo.and_r(PM.Term.below(y, 2n+c), PM.Term.below(z, c), r))
      )
    case C.Term.Ref{_}:
      {==}
    case C.Term.Enu{_}:
      {==}
    case C.Term.Lab{_}:
      {==}
    case C.Term.Efq{}:
      {==}
    case C.Term.Rfl{}:
      {==}

# a shift by 0 keeps any term
def Tz.sz.at(b: Bool, +i: Nat) -> {C.Term.Var{C.Term.shift.at(b, i, 0n)} == C.Term.Var{i}: C.Term}:
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Nat, Nat.add(i, 0n), i, N.add_zero(i)): {C.Term.Var{_} == C.Term.Var{i}: C.Term}
      {==}

def Tz.shift_zero(t: C.Term, +c: Nat) -> {C.Term.shift(t, 0n, c) == t: C.Term}:
  match t:
    case C.Term.Var{+i}:
      Tz.sz.at(Nat.is_lt(i, c), i)
    case C.Term.Ann{+x, +y}:
      Tz.cg2(
        X0 => Y0 => C.Term.Ann{X0, Y0},
        C.Term.shift(x, 0n, c),
        C.Term.shift(y, 0n, c),
        x,
        y,
        Tz.shift_zero(x, c),
        Tz.shift_zero(y, c)
      )
    case C.Term.Let{+q, +x, +y}:
      Tz.cg2(
        X0 => Y0 => C.Term.Let{q, X0, Y0},
        C.Term.shift(x, 0n, c),
        C.Term.shift(y, 0n, 1n+c),
        x,
        y,
        Tz.shift_zero(x, c),
        Tz.shift_zero(y, 1n+c)
      )
    case C.Term.Typ{+x}:
      Tz.cg1(X0 => C.Term.Typ{X0}, C.Term.shift(x, 0n, c), x, Tz.shift_zero(x, c))
    case C.Term.Min{+x, +y}:
      Tz.cg2(
        X0 => Y0 => C.Term.Min{X0, Y0},
        C.Term.shift(x, 0n, c),
        C.Term.shift(y, 0n, c),
        x,
        y,
        Tz.shift_zero(x, c),
        Tz.shift_zero(y, c)
      )
    case C.Term.All{+q, +x, +y}:
      Tz.cg2(
        X0 => Y0 => C.Term.All{q, X0, Y0},
        C.Term.shift(x, 0n, c),
        C.Term.shift(y, 0n, 1n+c),
        x,
        y,
        Tz.shift_zero(x, c),
        Tz.shift_zero(y, 1n+c)
      )
    case C.Term.Lam{+q, +x}:
      Tz.cg1(X0 => C.Term.Lam{q, X0}, C.Term.shift(x, 0n, 1n+c), x, Tz.shift_zero(x, 1n+c))
    case C.Term.App{+q, +x, +y}:
      Tz.cg2(
        X0 => Y0 => C.Term.App{q, X0, Y0},
        C.Term.shift(x, 0n, c),
        C.Term.shift(y, 0n, c),
        x,
        y,
        Tz.shift_zero(x, c),
        Tz.shift_zero(y, c)
      )
    case C.Term.Sig{+q, +x, +y}:
      Tz.cg2(
        X0 => Y0 => C.Term.Sig{q, X0, Y0},
        C.Term.shift(x, 0n, c),
        C.Term.shift(y, 0n, 1n+c),
        x,
        y,
        Tz.shift_zero(x, c),
        Tz.shift_zero(y, 1n+c)
      )
    case C.Term.Tup{+q, +x, +y}:
      Tz.cg2(
        X0 => Y0 => C.Term.Tup{q, X0, Y0},
        C.Term.shift(x, 0n, c),
        C.Term.shift(y, 0n, c),
        x,
        y,
        Tz.shift_zero(x, c),
        Tz.shift_zero(y, c)
      )
    case C.Term.Prj{+x}:
      Tz.cg1(X0 => C.Term.Prj{X0}, C.Term.shift(x, 0n, c), x, Tz.shift_zero(x, c))
    case C.Term.Mat{+k, +x, +y}:
      Tz.cg2(
        X0 => Y0 => C.Term.Mat{k, X0, Y0},
        C.Term.shift(x, 0n, c),
        C.Term.shift(y, 0n, c),
        x,
        y,
        Tz.shift_zero(x, c),
        Tz.shift_zero(y, c)
      )
    case C.Term.Eql{+x, +y, +z}:
      Tz.cg3(
        X0 => Y0 => Z0 => C.Term.Eql{X0, Y0, Z0},
        C.Term.shift(x, 0n, c),
        C.Term.shift(y, 0n, c),
        C.Term.shift(z, 0n, c),
        x,
        y,
        z,
        Tz.shift_zero(x, c),
        Tz.shift_zero(y, c),
        Tz.shift_zero(z, c)
      )
    case C.Term.Rwt{+x, +y, +z}:
      Tz.cg3(
        X0 => Y0 => Z0 => C.Term.Rwt{X0, Y0, Z0},
        C.Term.shift(x, 0n, c),
        C.Term.shift(y, 0n, 2n+c),
        C.Term.shift(z, 0n, c),
        x,
        y,
        z,
        Tz.shift_zero(x, c),
        Tz.shift_zero(y, 2n+c),
        Tz.shift_zero(z, c)
      )
    case C.Term.Ref{_}:
      {==}
    case C.Term.Enu{_}:
      {==}
    case C.Term.Lab{_}:
      {==}
    case C.Term.Efq{}:
      {==}
    case C.Term.Rfl{}:
      {==}

# the variable i below the depth d is kept
def Tz.sc.var(
  +e: List<&2, C.Term>,
  d: Nat,
  +i: Nat,
  h: {Nat.is_lt(i, d) == True{}: Bool}
) -> {C.Term.lift(e, d, i) == C.Term.Var{i}: C.Term}:
  match d:
    case 0n:
      Tz.lt0.no(i, {C.Term.lift(e, 0n, i) == C.Term.Var{i}: C.Term}, h)
    case 1n++p:
      %Equal.sym(
        Bool,
        Nat.is_lt(i, 1n+p),
        True{},
        h
      ): {
        C.Term.lift.at(
          _,
          i,
          C.Term.shift(C.Env.sub(e, Nat.sub(i, 1n+p)), 1n+p, 0n)
        )
          == C.Term.Var{i}: C.Term
      }
      {==}

# a substitution keeps a term whose free variables are all below the depth
def Tz.subst_closed(
  t: C.Term,
  +e: List<&2, C.Term>,
  +c: Nat,
  +hb: {PM.Term.below(t, c) == True{}: Bool}
) -> {C.Term.subst(t, e, c) == t: C.Term}:
  match t:
    case C.Term.Var{+i}:
      Tz.sc.var(e, c, i, hb)
    case C.Term.Ann{+x, +y}:
      Tz.cg2(
        X0 => Y0 => C.Term.Ann{X0, Y0},
        C.Term.subst(x, e, c),
        C.Term.subst(y, e, c),
        x,
        y,
        Tz.subst_closed(x, e, c, K.Bo.and_l(PM.Term.below(x, c), PM.Term.below(y, c), hb)),
        Tz.subst_closed(y, e, c, K.Bo.and_r(PM.Term.below(x, c), PM.Term.below(y, c), hb))
      )
    case C.Term.Let{+q, +x, +y}:
      Tz.cg2(
        X0 => Y0 => C.Term.Let{q, X0, Y0},
        C.Term.subst(x, e, c),
        C.Term.subst(y, e, 1n+c),
        x,
        y,
        Tz.subst_closed(x, e, c, K.Bo.and_l(PM.Term.below(x, c), PM.Term.below(y, 1n+c), hb)),
        Tz.subst_closed(y, e, 1n+c, K.Bo.and_r(PM.Term.below(x, c), PM.Term.below(y, 1n+c), hb))
      )
    case C.Term.Typ{+x}:
      Tz.cg1(X0 => C.Term.Typ{X0}, C.Term.subst(x, e, c), x, Tz.subst_closed(x, e, c, hb))
    case C.Term.Min{+x, +y}:
      Tz.cg2(
        X0 => Y0 => C.Term.Min{X0, Y0},
        C.Term.subst(x, e, c),
        C.Term.subst(y, e, c),
        x,
        y,
        Tz.subst_closed(x, e, c, K.Bo.and_l(PM.Term.below(x, c), PM.Term.below(y, c), hb)),
        Tz.subst_closed(y, e, c, K.Bo.and_r(PM.Term.below(x, c), PM.Term.below(y, c), hb))
      )
    case C.Term.All{+q, +x, +y}:
      Tz.cg2(
        X0 => Y0 => C.Term.All{q, X0, Y0},
        C.Term.subst(x, e, c),
        C.Term.subst(y, e, 1n+c),
        x,
        y,
        Tz.subst_closed(x, e, c, K.Bo.and_l(PM.Term.below(x, c), PM.Term.below(y, 1n+c), hb)),
        Tz.subst_closed(y, e, 1n+c, K.Bo.and_r(PM.Term.below(x, c), PM.Term.below(y, 1n+c), hb))
      )
    case C.Term.Lam{+q, +x}:
      Tz.cg1(X0 => C.Term.Lam{q, X0}, C.Term.subst(x, e, 1n+c), x, Tz.subst_closed(x, e, 1n+c, hb))
    case C.Term.App{+q, +x, +y}:
      Tz.cg2(
        X0 => Y0 => C.Term.App{q, X0, Y0},
        C.Term.subst(x, e, c),
        C.Term.subst(y, e, c),
        x,
        y,
        Tz.subst_closed(x, e, c, K.Bo.and_l(PM.Term.below(x, c), PM.Term.below(y, c), hb)),
        Tz.subst_closed(y, e, c, K.Bo.and_r(PM.Term.below(x, c), PM.Term.below(y, c), hb))
      )
    case C.Term.Sig{+q, +x, +y}:
      Tz.cg2(
        X0 => Y0 => C.Term.Sig{q, X0, Y0},
        C.Term.subst(x, e, c),
        C.Term.subst(y, e, 1n+c),
        x,
        y,
        Tz.subst_closed(x, e, c, K.Bo.and_l(PM.Term.below(x, c), PM.Term.below(y, 1n+c), hb)),
        Tz.subst_closed(y, e, 1n+c, K.Bo.and_r(PM.Term.below(x, c), PM.Term.below(y, 1n+c), hb))
      )
    case C.Term.Tup{+q, +x, +y}:
      Tz.cg2(
        X0 => Y0 => C.Term.Tup{q, X0, Y0},
        C.Term.subst(x, e, c),
        C.Term.subst(y, e, c),
        x,
        y,
        Tz.subst_closed(x, e, c, K.Bo.and_l(PM.Term.below(x, c), PM.Term.below(y, c), hb)),
        Tz.subst_closed(y, e, c, K.Bo.and_r(PM.Term.below(x, c), PM.Term.below(y, c), hb))
      )
    case C.Term.Prj{+x}:
      Tz.cg1(X0 => C.Term.Prj{X0}, C.Term.subst(x, e, c), x, Tz.subst_closed(x, e, c, hb))
    case C.Term.Mat{+k, +x, +y}:
      Tz.cg2(
        X0 => Y0 => C.Term.Mat{k, X0, Y0},
        C.Term.subst(x, e, c),
        C.Term.subst(y, e, c),
        x,
        y,
        Tz.subst_closed(x, e, c, K.Bo.and_l(PM.Term.below(x, c), PM.Term.below(y, c), hb)),
        Tz.subst_closed(y, e, c, K.Bo.and_r(PM.Term.below(x, c), PM.Term.below(y, c), hb))
      )
    case C.Term.Eql{+x, +y, +z}:
      +r = K.Bo.and_r(PM.Term.below(x, c), Bool.and(PM.Term.below(y, c), PM.Term.below(z, c)), hb)
      Tz.cg3(
        X0 => Y0 => Z0 => C.Term.Eql{X0, Y0, Z0},
        C.Term.subst(x, e, c),
        C.Term.subst(y, e, c),
        C.Term.subst(z, e, c),
        x,
        y,
        z,
        Tz.subst_closed(
          x,
          e,
          c,
          K.Bo.and_l(PM.Term.below(x, c), Bool.and(PM.Term.below(y, c), PM.Term.below(z, c)), hb)
        ),
        Tz.subst_closed(y, e, c, K.Bo.and_l(PM.Term.below(y, c), PM.Term.below(z, c), r)),
        Tz.subst_closed(z, e, c, K.Bo.and_r(PM.Term.below(y, c), PM.Term.below(z, c), r))
      )
    case C.Term.Rwt{+x, +y, +z}:
      +r = K.Bo.and_r(
        PM.Term.below(x, c),
        Bool.and(PM.Term.below(y, 2n+c), PM.Term.below(z, c)),
        hb
      )
      Tz.cg3(
        X0 => Y0 => Z0 => C.Term.Rwt{X0, Y0, Z0},
        C.Term.subst(x, e, c),
        C.Term.subst(y, e, 2n+c),
        C.Term.subst(z, e, c),
        x,
        y,
        z,
        Tz.subst_closed(
          x,
          e,
          c,
          K.Bo.and_l(PM.Term.below(x, c), Bool.and(PM.Term.below(y, 2n+c), PM.Term.below(z, c)), hb)
        ),
        Tz.subst_closed(y, e, 2n+c, K.Bo.and_l(PM.Term.below(y, 2n+c), PM.Term.below(z, c), r)),
        Tz.subst_closed(z, e, c, K.Bo.and_r(PM.Term.below(y, 2n+c), PM.Term.below(z, c), r))
      )
    case C.Term.Ref{_}:
      {==}
    case C.Term.Enu{_}:
      {==}
    case C.Term.Lab{_}:
      {==}
    case C.Term.Efq{}:
      {==}
    case C.Term.Rfl{}:
      {==}

# Variables
# ---------

# M.copy's part, a variable i of the source at the depth d, not below it:
# the local i - d, shifted by d
def Tz.sb.env(
  +e: List<&2, C.Term>,
  d: Nat,
  +i: Nat,
  h: {Nat.is_lt(i, d) == False{}: Bool}
) -> {
  C.Term.subst(C.Term.Var{i}, e, d) == C.Term.shift(C.Env.sub(e, Nat.sub(i, d)), d, 0n): C.Term
}:
  match d:
    case 0n:
      %Equal.sym(
        Nat,
        Nat.sub(i, 0n),
        i,
        Tz.sub0(i)
      ): {C.Env.sub(e, i) == C.Term.shift(C.Env.sub(e, _), 0n, 0n): C.Term}
      Equal.sym(
        C.Term,
        C.Term.shift(C.Env.sub(e, i), 0n, 0n),
        C.Env.sub(e, i),
        Tz.shift_zero(C.Env.sub(e, i), 0n)
      )
    case 1n++p:
      %Equal.sym(
        Bool,
        Nat.is_lt(i, 1n+p),
        False{},
        h
      ): {
        C.Term.lift.at(
          _,
          i,
          C.Term.shift(C.Env.sub(e, Nat.sub(i, 1n+p)), 1n+p, 0n)
        )
          == C.Term.shift(C.Env.sub(e, Nat.sub(i, 1n+p)), 1n+p, 0n): C.Term
      }
      {==}

# a local j of the list xs: its element j
def Tz.ev.get(
  xs: List<&2, C.Term>,
  j: Nat,
  h: {Nat.is_lt(j, List.length(&2, C.Term, xs)) == True{}: Bool}
) -> {Some{C.Env.sub(xs, j)} == List.get(&2, C.Term, xs, j): Maybe<&2, C.Term>}:
  match xs:
    case Nil{}:
      Tz.lt0.no(
        j,
        {Some{C.Env.sub(Nil{}, j)} == List.get(&2, C.Term, Nil{}, j): Maybe<&2, C.Term>},
        h
      )
    case Con{x, rest}:
      match j:
        case 0n:
          {==}
        case 1n+jp:
          Tz.ev.get(rest, jp, h)

# a variable j past the list xs: Var(j - |xs|)
def Tz.ev.past(
  xs: List<&2, C.Term>,
  j: Nat,
  h: {Nat.is_lt(j, List.length(&2, C.Term, xs)) == False{}: Bool}
) -> {C.Env.sub(xs, j) == C.Term.Var{Nat.sub(j, List.length(&2, C.Term, xs))}: C.Term}:
  match xs:
    case Nil{}:
      %Equal.sym(Nat, Nat.sub(j, 0n), j, Tz.sub0(j)): {C.Term.Var{j} == C.Term.Var{_}: C.Term}
      {==}
    case Con{x, rest}:
      match j:
        case 0n:
          K.Bo.ft(
            {
              C.Env.sub(
                Con{x, rest},
                0n
              )
                == C.Term.Var{Nat.sub(0n, 1n+List.length(&2, C.Term, rest))}: C.Term
            },
            h
          )
        case 1n+jp:
          Tz.ev.past(rest, jp, h)

# M.copy's part, a variable i of the source at the depth d, past the locals
# e: Var(i - |e|)
def Tz.sb.past(
  +e: List<&2, C.Term>,
  +d: Nat,
  +i: Nat,
  +h1: {Nat.is_lt(i, d) == False{}: Bool},
  +h2: {Nat.is_lt(Nat.sub(i, d), List.length(&2, C.Term, e)) == False{}: Bool}
) -> {
  C.Term.subst(C.Term.Var{i}, e, d) == C.Term.Var{Nat.sub(i, List.length(&2, C.Term, e))}: C.Term
}:
  +L = List.length(&2, C.Term, e)
  +k = Nat.sub(Nat.sub(i, d), L)
  %Equal.sym(
    C.Term,
    C.Term.subst(C.Term.Var{i}, e, d),
    C.Term.shift(C.Env.sub(e, Nat.sub(i, d)), d, 0n),
    Tz.sb.env(e, d, i, h1)
  ): {_ == C.Term.Var{Nat.sub(i, L)}: C.Term}
  %Equal.sym(
    C.Term,
    C.Env.sub(e, Nat.sub(i, d)),
    C.Term.Var{k},
    Tz.ev.past(e, Nat.sub(i, d), h2)
  ): {C.Term.shift(_, d, 0n) == C.Term.Var{Nat.sub(i, L)}: C.Term}
  %Equal.sym(
    Bool,
    Nat.is_lt(k, 0n),
    False{},
    Tz.lt0(k)
  ): {C.Term.Var{C.Term.shift.at(_, k, d)} == C.Term.Var{Nat.sub(i, L)}: C.Term}
  %Equal.sym(
    Nat,
    Nat.add(k, d),
    Nat.sub(i, L),
    Tz.subsub(i, d, L, h1, h2)
  ): {C.Term.Var{_} == C.Term.Var{Nat.sub(i, L)}: C.Term}
  {==}

# Term.below
# ----------

# a higher bound keeps Term.below
def Tz.below_mono(
  t: C.Term,
  +n: Nat,
  +m: Nat,
  +h: {Nat.is_le(n, m) == True{}: Bool},
  +hb: {PM.Term.below(t, n) == True{}: Bool}
) -> {PM.Term.below(t, m) == True{}: Bool}:
  match t:
    case C.Term.Var{i}:
      Tz.lt_le(i, n, m, hb, h)
    case C.Term.Ref{_}:
      {==}
    case C.Term.Ann{+x, +y}:
      K.Bo.and_i(
        PM.Term.below(x, m),
        PM.Term.below(y, m),
        Tz.below_mono(x, n, m, h, K.Bo.and_l(PM.Term.below(x, n), PM.Term.below(y, n), hb)),
        Tz.below_mono(y, n, m, h, K.Bo.and_r(PM.Term.below(x, n), PM.Term.below(y, n), hb))
      )
    case C.Term.Let{_, +v, +f}:
      K.Bo.and_i(
        PM.Term.below(v, m),
        PM.Term.below(f, 1n+m),
        Tz.below_mono(v, n, m, h, K.Bo.and_l(PM.Term.below(v, n), PM.Term.below(f, 1n+n), hb)),
        Tz.below_mono(f, 1n+n, 1n+m, h, K.Bo.and_r(PM.Term.below(v, n), PM.Term.below(f, 1n+n), hb))
      )
    case C.Term.Typ{x}:
      Tz.below_mono(x, n, m, h, hb)
    case C.Term.Min{+x, +y}:
      K.Bo.and_i(
        PM.Term.below(x, m),
        PM.Term.below(y, m),
        Tz.below_mono(x, n, m, h, K.Bo.and_l(PM.Term.below(x, n), PM.Term.below(y, n), hb)),
        Tz.below_mono(y, n, m, h, K.Bo.and_r(PM.Term.below(x, n), PM.Term.below(y, n), hb))
      )
    case C.Term.All{_, +x, +y}:
      K.Bo.and_i(
        PM.Term.below(x, m),
        PM.Term.below(y, 1n+m),
        Tz.below_mono(x, n, m, h, K.Bo.and_l(PM.Term.below(x, n), PM.Term.below(y, 1n+n), hb)),
        Tz.below_mono(y, 1n+n, 1n+m, h, K.Bo.and_r(PM.Term.below(x, n), PM.Term.below(y, 1n+n), hb))
      )
    case C.Term.Lam{_, f}:
      Tz.below_mono(f, 1n+n, 1n+m, h, hb)
    case C.Term.App{_, +x, +y}:
      K.Bo.and_i(
        PM.Term.below(x, m),
        PM.Term.below(y, m),
        Tz.below_mono(x, n, m, h, K.Bo.and_l(PM.Term.below(x, n), PM.Term.below(y, n), hb)),
        Tz.below_mono(y, n, m, h, K.Bo.and_r(PM.Term.below(x, n), PM.Term.below(y, n), hb))
      )
    case C.Term.Sig{_, +x, +y}:
      K.Bo.and_i(
        PM.Term.below(x, m),
        PM.Term.below(y, 1n+m),
        Tz.below_mono(x, n, m, h, K.Bo.and_l(PM.Term.below(x, n), PM.Term.below(y, 1n+n), hb)),
        Tz.below_mono(y, 1n+n, 1n+m, h, K.Bo.and_r(PM.Term.below(x, n), PM.Term.below(y, 1n+n), hb))
      )
    case C.Term.Tup{_, +x, +y}:
      K.Bo.and_i(
        PM.Term.below(x, m),
        PM.Term.below(y, m),
        Tz.below_mono(x, n, m, h, K.Bo.and_l(PM.Term.below(x, n), PM.Term.below(y, n), hb)),
        Tz.below_mono(y, n, m, h, K.Bo.and_r(PM.Term.below(x, n), PM.Term.below(y, n), hb))
      )
    case C.Term.Prj{x}:
      Tz.below_mono(x, n, m, h, hb)
    case C.Term.Enu{_}:
      {==}
    case C.Term.Lab{_}:
      {==}
    case C.Term.Mat{_, +x, +y}:
      K.Bo.and_i(
        PM.Term.below(x, m),
        PM.Term.below(y, m),
        Tz.below_mono(x, n, m, h, K.Bo.and_l(PM.Term.below(x, n), PM.Term.below(y, n), hb)),
        Tz.below_mono(y, n, m, h, K.Bo.and_r(PM.Term.below(x, n), PM.Term.below(y, n), hb))
      )
    case C.Term.Efq{}:
      {==}
    case C.Term.Eql{+x, +y, +z}:
      +r = K.Bo.and_r(PM.Term.below(x, n), Bool.and(PM.Term.below(y, n), PM.Term.below(z, n)), hb)
      K.Bo.and_i(
        PM.Term.below(x, m),
        Bool.and(PM.Term.below(y, m), PM.Term.below(z, m)),
        Tz.below_mono(
          x,
          n,
          m,
          h,
          K.Bo.and_l(PM.Term.below(x, n), Bool.and(PM.Term.below(y, n), PM.Term.below(z, n)), hb)
        ),
        K.Bo.and_i(
          PM.Term.below(y, m),
          PM.Term.below(z, m),
          Tz.below_mono(y, n, m, h, K.Bo.and_l(PM.Term.below(y, n), PM.Term.below(z, n), r)),
          Tz.below_mono(z, n, m, h, K.Bo.and_r(PM.Term.below(y, n), PM.Term.below(z, n), r))
        )
      )
    case C.Term.Rfl{}:
      {==}
    case C.Term.Rwt{+x, +y, +z}:
      +r = K.Bo.and_r(
        PM.Term.below(x, n),
        Bool.and(PM.Term.below(y, 2n+n), PM.Term.below(z, n)),
        hb
      )
      K.Bo.and_i(
        PM.Term.below(x, m),
        Bool.and(PM.Term.below(y, 2n+m), PM.Term.below(z, m)),
        Tz.below_mono(
          x,
          n,
          m,
          h,
          K.Bo.and_l(PM.Term.below(x, n), Bool.and(PM.Term.below(y, 2n+n), PM.Term.below(z, n)), hb)
        ),
        K.Bo.and_i(
          PM.Term.below(y, 2n+m),
          PM.Term.below(z, m),
          Tz.below_mono(
            y,
            2n+n,
            2n+m,
            h,
            K.Bo.and_l(PM.Term.below(y, 2n+n), PM.Term.below(z, n), r)
          ),
          Tz.below_mono(z, n, m, h, K.Bo.and_r(PM.Term.below(y, 2n+n), PM.Term.below(z, n), r))
        )
      )

# the fv of a node: a part of fv v, under b binders, with v - b at most cm,
# is below b + cm
def Tz.below_up(
  t: C.Term,
  +v: Nat,
  +b: Nat,
  +cm: Nat,
  hb: {PM.Term.below(t, v) == True{}: Bool},
  h: {Nat.is_le(Nat.sub(v, b), cm) == True{}: Bool}
) -> {PM.Term.below(t, Nat.add(b, cm)) == True{}: Bool}:
  Tz.below_mono(t, v, Nat.add(b, cm), Tz.sub_add(v, b, cm, h), hb)
