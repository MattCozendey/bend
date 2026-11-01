# compiler: the copy's frames, tag by tag
# =======================================
#
# A frame of the walk (proof_copy_walk.bend) copies a source cell of the tag
# tg, of the term T0 (Fr.src: T.tm.cell with its parts' terms t2, t3, t4).
# Once each part k is copied to Mo.F of its term at the depth d + Tg.b(tg, k),
# the new cell, of the same tag, quantity and name, holds Mo.F(T0, d)
# (Tg.cg). Mo.F commutes with each former by its definition (F.*).
import Base
import ./impl.bend as C
import ./proof_term.bend as T
import ./proof_need.bend as N
import ./proof_copy.bend as D
import ./proof_copy_kit.bend as K
import ./proof_copy_walk.bend as W

def Tg.some(-a: C.Term, -b: C.Term, e: {Some{a} == Some{b}: Maybe<&2, C.Term>}) -> {a == b: C.Term}:
  Equal.cong(Maybe<&2, C.Term>, C.Term, x => Maybe.default(&2, C.Term, x, a), Some{a}, Some{b}, e)

def Tg.ns(-b: C.Term, -G: Type, e: {None{} == Some{b}: Maybe<&2, C.Term>}) -> G:
  Empty.absurd(
    G,
    N.true_ne_false(
      Equal.cong(Maybe<&2, C.Term>, Bool, x => Maybe.is_none(&2, C.Term, x), None{}, Some{b}, e)
    )
  )

def Tg.add1(d: Nat) -> {Nat.add(d, 1n) == 1n+d: Nat}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n), 1n+p, Tg.add1(p)): {1n+_ == 2n+p: Nat}
      {==}

def Tg.add2(d: Nat) -> {Nat.add(d, 2n) == 2n+d: Nat}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 2n), 2n+p, Tg.add2(p)): {1n+_ == 3n+p: Nat}
      {==}

# Mo.F of each former
def F.Ann(
  mo: D.Mo,
  +a2: C.Term,
  +a3: C.Term,
  +d: Nat
) -> {
  D.Mo.F(mo, C.Term.Ann{a2, a3}, d) == C.Term.Ann{D.Mo.F(mo, a2, d), D.Mo.F(mo, a3, d)}: C.Term
}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.Let(
  mo: D.Mo,
  +q: C.Quan,
  +a2: C.Term,
  +a3: C.Term,
  +d: Nat
) -> {
  D.Mo.F(
    mo,
    C.Term.Let{q, a2, a3},
    d
  )
    == C.Term.Let{q, D.Mo.F(mo, a2, d), D.Mo.F(mo, a3, 1n+d)}: C.Term
}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.Typ(
  mo: D.Mo,
  +a2: C.Term,
  +d: Nat
) -> {D.Mo.F(mo, C.Term.Typ{a2}, d) == C.Term.Typ{D.Mo.F(mo, a2, d)}: C.Term}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.Min(
  mo: D.Mo,
  +a2: C.Term,
  +a3: C.Term,
  +d: Nat
) -> {
  D.Mo.F(mo, C.Term.Min{a2, a3}, d) == C.Term.Min{D.Mo.F(mo, a2, d), D.Mo.F(mo, a3, d)}: C.Term
}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.All(
  mo: D.Mo,
  +q: C.Quan,
  +a2: C.Term,
  +a3: C.Term,
  +d: Nat
) -> {
  D.Mo.F(
    mo,
    C.Term.All{q, a2, a3},
    d
  )
    == C.Term.All{q, D.Mo.F(mo, a2, d), D.Mo.F(mo, a3, 1n+d)}: C.Term
}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.Lam(
  mo: D.Mo,
  +q: C.Quan,
  +a2: C.Term,
  +d: Nat
) -> {D.Mo.F(mo, C.Term.Lam{q, a2}, d) == C.Term.Lam{q, D.Mo.F(mo, a2, 1n+d)}: C.Term}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.App(
  mo: D.Mo,
  +q: C.Quan,
  +a2: C.Term,
  +a3: C.Term,
  +d: Nat
) -> {
  D.Mo.F(
    mo,
    C.Term.App{q, a2, a3},
    d
  )
    == C.Term.App{q, D.Mo.F(mo, a2, d), D.Mo.F(mo, a3, d)}: C.Term
}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.Sig(
  mo: D.Mo,
  +q: C.Quan,
  +a2: C.Term,
  +a3: C.Term,
  +d: Nat
) -> {
  D.Mo.F(
    mo,
    C.Term.Sig{q, a2, a3},
    d
  )
    == C.Term.Sig{q, D.Mo.F(mo, a2, d), D.Mo.F(mo, a3, 1n+d)}: C.Term
}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.Tup(
  mo: D.Mo,
  +q: C.Quan,
  +a2: C.Term,
  +a3: C.Term,
  +d: Nat
) -> {
  D.Mo.F(
    mo,
    C.Term.Tup{q, a2, a3},
    d
  )
    == C.Term.Tup{q, D.Mo.F(mo, a2, d), D.Mo.F(mo, a3, d)}: C.Term
}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.Prj(
  mo: D.Mo,
  +a2: C.Term,
  +d: Nat
) -> {D.Mo.F(mo, C.Term.Prj{a2}, d) == C.Term.Prj{D.Mo.F(mo, a2, d)}: C.Term}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.Eql(
  mo: D.Mo,
  +a2: C.Term,
  +a3: C.Term,
  +a4: C.Term,
  +d: Nat
) -> {
  D.Mo.F(
    mo,
    C.Term.Eql{a2, a3, a4},
    d
  )
    == C.Term.Eql{D.Mo.F(mo, a2, d), D.Mo.F(mo, a3, d), D.Mo.F(mo, a4, d)}: C.Term
}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.Rwt(
  mo: D.Mo,
  +a2: C.Term,
  +a3: C.Term,
  +a4: C.Term,
  +d: Nat
) -> {
  D.Mo.F(
    mo,
    C.Term.Rwt{a2, a3, a4},
    d
  )
    == C.Term.Rwt{D.Mo.F(mo, a2, d), D.Mo.F(mo, a3, 2n+d), D.Mo.F(mo, a4, d)}: C.Term
}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.mat(
  mo: D.Mo,
  +k: List<&2, U32>,
  +a3: C.Term,
  +a4: C.Term,
  +d: Nat
) -> {
  D.Mo.F(
    mo,
    C.Term.Mat{k, a3, a4},
    d
  )
    == C.Term.Mat{k, D.Mo.F(mo, a3, d), D.Mo.F(mo, a4, d)}: C.Term
}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.lab(
  mo: D.Mo,
  +k: List<&2, U32>,
  +d: Nat
) -> {D.Mo.F(mo, C.Term.Lab{k}, d) == C.Term.Lab{k}: C.Term}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.efq(mo: D.Mo, +d: Nat) -> {D.Mo.F(mo, C.Term.Efq{}, d) == C.Term.Efq{}: C.Term}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.rfl(mo: D.Mo, +d: Nat) -> {D.Mo.F(mo, C.Term.Rfl{}, d) == C.Term.Rfl{}: C.Term}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

# the frames by tag
def Tg.c2(
  +mo: D.Mo,
  +t2: C.Term,
  +t3: C.Term,
  +d: Nat,
  -T0: C.Term,
  e: {C.Term.Ann{t2, t3} == T0: C.Term}
) -> {
  Some{
    C.Term.Ann{D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 0n))}
  }
    == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>
}:
  %e: {
    Some{
      C.Term.Ann{D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 0n))}
    }
      == Some{D.Mo.F(mo, _, d)}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    C.Term,
    D.Mo.F(mo, C.Term.Ann{t2, t3}, d),
    C.Term.Ann{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d)},
    F.Ann(mo, t2, t3, d)
  ): {
    Some{
      C.Term.Ann{D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 0n))}
    }
      == Some{_}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      C.Term.Ann{D.Mo.F(mo, t2, _), D.Mo.F(mo, t3, Nat.add(d, 0n))}
    }
      == Some{C.Term.Ann{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d)}}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      C.Term.Ann{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, _)}
    }
      == Some{C.Term.Ann{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d)}}: Maybe<&2, C.Term>
  }
  {==}

def Tg.c3(
  +mo: D.Mo,
  +q: C.Quan,
  +t2: C.Term,
  +t3: C.Term,
  +d: Nat,
  -T0: C.Term,
  e: {C.Term.Let{q, t2, t3} == T0: C.Term}
) -> {
  Some{
    C.Term.Let{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 1n))}
  }
    == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>
}:
  %e: {
    Some{
      C.Term.Let{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 1n))}
    }
      == Some{D.Mo.F(mo, _, d)}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    C.Term,
    D.Mo.F(mo, C.Term.Let{q, t2, t3}, d),
    C.Term.Let{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 1n+d)},
    F.Let(mo, q, t2, t3, d)
  ): {
    Some{
      C.Term.Let{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 1n))}
    }
      == Some{_}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      C.Term.Let{q, D.Mo.F(mo, t2, _), D.Mo.F(mo, t3, Nat.add(d, 1n))}
    }
      == Some{C.Term.Let{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 1n+d)}}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 1n),
    1n+d,
    Tg.add1(d)
  ): {
    Some{
      C.Term.Let{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, _)}
    }
      == Some{C.Term.Let{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 1n+d)}}: Maybe<&2, C.Term>
  }
  {==}

def Tg.c4(
  +mo: D.Mo,
  +t2: C.Term,
  +d: Nat,
  -T0: C.Term,
  e: {C.Term.Typ{t2} == T0: C.Term}
) -> {
  Some{C.Term.Typ{D.Mo.F(mo, t2, Nat.add(d, 0n))}} == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>
}:
  %e: {
    Some{C.Term.Typ{D.Mo.F(mo, t2, Nat.add(d, 0n))}} == Some{D.Mo.F(mo, _, d)}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    C.Term,
    D.Mo.F(mo, C.Term.Typ{t2}, d),
    C.Term.Typ{D.Mo.F(mo, t2, d)},
    F.Typ(mo, t2, d)
  ): {Some{C.Term.Typ{D.Mo.F(mo, t2, Nat.add(d, 0n))}} == Some{_}: Maybe<&2, C.Term>}
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {Some{C.Term.Typ{D.Mo.F(mo, t2, _)}} == Some{C.Term.Typ{D.Mo.F(mo, t2, d)}}: Maybe<&2, C.Term>}
  {==}

def Tg.c5(
  +mo: D.Mo,
  +t2: C.Term,
  +t3: C.Term,
  +d: Nat,
  -T0: C.Term,
  e: {C.Term.Min{t2, t3} == T0: C.Term}
) -> {
  Some{
    C.Term.Min{D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 0n))}
  }
    == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>
}:
  %e: {
    Some{
      C.Term.Min{D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 0n))}
    }
      == Some{D.Mo.F(mo, _, d)}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    C.Term,
    D.Mo.F(mo, C.Term.Min{t2, t3}, d),
    C.Term.Min{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d)},
    F.Min(mo, t2, t3, d)
  ): {
    Some{
      C.Term.Min{D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 0n))}
    }
      == Some{_}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      C.Term.Min{D.Mo.F(mo, t2, _), D.Mo.F(mo, t3, Nat.add(d, 0n))}
    }
      == Some{C.Term.Min{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d)}}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      C.Term.Min{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, _)}
    }
      == Some{C.Term.Min{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d)}}: Maybe<&2, C.Term>
  }
  {==}

def Tg.c6(
  +mo: D.Mo,
  +q: C.Quan,
  +t2: C.Term,
  +t3: C.Term,
  +d: Nat,
  -T0: C.Term,
  e: {C.Term.All{q, t2, t3} == T0: C.Term}
) -> {
  Some{
    C.Term.All{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 1n))}
  }
    == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>
}:
  %e: {
    Some{
      C.Term.All{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 1n))}
    }
      == Some{D.Mo.F(mo, _, d)}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    C.Term,
    D.Mo.F(mo, C.Term.All{q, t2, t3}, d),
    C.Term.All{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 1n+d)},
    F.All(mo, q, t2, t3, d)
  ): {
    Some{
      C.Term.All{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 1n))}
    }
      == Some{_}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      C.Term.All{q, D.Mo.F(mo, t2, _), D.Mo.F(mo, t3, Nat.add(d, 1n))}
    }
      == Some{C.Term.All{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 1n+d)}}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 1n),
    1n+d,
    Tg.add1(d)
  ): {
    Some{
      C.Term.All{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, _)}
    }
      == Some{C.Term.All{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 1n+d)}}: Maybe<&2, C.Term>
  }
  {==}

def Tg.c7(
  +mo: D.Mo,
  +q: C.Quan,
  +t2: C.Term,
  +d: Nat,
  -T0: C.Term,
  e: {C.Term.Lam{q, t2} == T0: C.Term}
) -> {
  Some{C.Term.Lam{q, D.Mo.F(mo, t2, Nat.add(d, 1n))}} == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>
}:
  %e: {
    Some{C.Term.Lam{q, D.Mo.F(mo, t2, Nat.add(d, 1n))}} == Some{D.Mo.F(mo, _, d)}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    C.Term,
    D.Mo.F(mo, C.Term.Lam{q, t2}, d),
    C.Term.Lam{q, D.Mo.F(mo, t2, 1n+d)},
    F.Lam(mo, q, t2, d)
  ): {Some{C.Term.Lam{q, D.Mo.F(mo, t2, Nat.add(d, 1n))}} == Some{_}: Maybe<&2, C.Term>}
  %Equal.sym(
    Nat,
    Nat.add(d, 1n),
    1n+d,
    Tg.add1(d)
  ): {
    Some{
      C.Term.Lam{q, D.Mo.F(mo, t2, _)}
    }
      == Some{C.Term.Lam{q, D.Mo.F(mo, t2, 1n+d)}}: Maybe<&2, C.Term>
  }
  {==}

def Tg.c8(
  +mo: D.Mo,
  +q: C.Quan,
  +t2: C.Term,
  +t3: C.Term,
  +d: Nat,
  -T0: C.Term,
  e: {C.Term.App{q, t2, t3} == T0: C.Term}
) -> {
  Some{
    C.Term.App{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 0n))}
  }
    == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>
}:
  %e: {
    Some{
      C.Term.App{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 0n))}
    }
      == Some{D.Mo.F(mo, _, d)}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    C.Term,
    D.Mo.F(mo, C.Term.App{q, t2, t3}, d),
    C.Term.App{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d)},
    F.App(mo, q, t2, t3, d)
  ): {
    Some{
      C.Term.App{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 0n))}
    }
      == Some{_}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      C.Term.App{q, D.Mo.F(mo, t2, _), D.Mo.F(mo, t3, Nat.add(d, 0n))}
    }
      == Some{C.Term.App{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d)}}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      C.Term.App{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, _)}
    }
      == Some{C.Term.App{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d)}}: Maybe<&2, C.Term>
  }
  {==}

def Tg.c9(
  +mo: D.Mo,
  +q: C.Quan,
  +t2: C.Term,
  +t3: C.Term,
  +d: Nat,
  -T0: C.Term,
  e: {C.Term.Sig{q, t2, t3} == T0: C.Term}
) -> {
  Some{
    C.Term.Sig{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 1n))}
  }
    == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>
}:
  %e: {
    Some{
      C.Term.Sig{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 1n))}
    }
      == Some{D.Mo.F(mo, _, d)}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    C.Term,
    D.Mo.F(mo, C.Term.Sig{q, t2, t3}, d),
    C.Term.Sig{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 1n+d)},
    F.Sig(mo, q, t2, t3, d)
  ): {
    Some{
      C.Term.Sig{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 1n))}
    }
      == Some{_}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      C.Term.Sig{q, D.Mo.F(mo, t2, _), D.Mo.F(mo, t3, Nat.add(d, 1n))}
    }
      == Some{C.Term.Sig{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 1n+d)}}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 1n),
    1n+d,
    Tg.add1(d)
  ): {
    Some{
      C.Term.Sig{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, _)}
    }
      == Some{C.Term.Sig{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 1n+d)}}: Maybe<&2, C.Term>
  }
  {==}

def Tg.c10(
  +mo: D.Mo,
  +q: C.Quan,
  +t2: C.Term,
  +t3: C.Term,
  +d: Nat,
  -T0: C.Term,
  e: {C.Term.Tup{q, t2, t3} == T0: C.Term}
) -> {
  Some{
    C.Term.Tup{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 0n))}
  }
    == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>
}:
  %e: {
    Some{
      C.Term.Tup{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 0n))}
    }
      == Some{D.Mo.F(mo, _, d)}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    C.Term,
    D.Mo.F(mo, C.Term.Tup{q, t2, t3}, d),
    C.Term.Tup{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d)},
    F.Tup(mo, q, t2, t3, d)
  ): {
    Some{
      C.Term.Tup{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 0n))}
    }
      == Some{_}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      C.Term.Tup{q, D.Mo.F(mo, t2, _), D.Mo.F(mo, t3, Nat.add(d, 0n))}
    }
      == Some{C.Term.Tup{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d)}}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      C.Term.Tup{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, _)}
    }
      == Some{C.Term.Tup{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d)}}: Maybe<&2, C.Term>
  }
  {==}

def Tg.c11(
  +mo: D.Mo,
  +t2: C.Term,
  +d: Nat,
  -T0: C.Term,
  e: {C.Term.Prj{t2} == T0: C.Term}
) -> {
  Some{C.Term.Prj{D.Mo.F(mo, t2, Nat.add(d, 0n))}} == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>
}:
  %e: {
    Some{C.Term.Prj{D.Mo.F(mo, t2, Nat.add(d, 0n))}} == Some{D.Mo.F(mo, _, d)}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    C.Term,
    D.Mo.F(mo, C.Term.Prj{t2}, d),
    C.Term.Prj{D.Mo.F(mo, t2, d)},
    F.Prj(mo, t2, d)
  ): {Some{C.Term.Prj{D.Mo.F(mo, t2, Nat.add(d, 0n))}} == Some{_}: Maybe<&2, C.Term>}
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {Some{C.Term.Prj{D.Mo.F(mo, t2, _)}} == Some{C.Term.Prj{D.Mo.F(mo, t2, d)}}: Maybe<&2, C.Term>}
  {==}

def Tg.c16(
  +mo: D.Mo,
  +t2: C.Term,
  +t3: C.Term,
  +t4: C.Term,
  +d: Nat,
  -T0: C.Term,
  e: {C.Term.Eql{t2, t3, t4} == T0: C.Term}
) -> {
  Some{
    C.Term.Eql{
      D.Mo.F(mo, t2, Nat.add(d, 0n)),
      D.Mo.F(mo, t3, Nat.add(d, 0n)),
      D.Mo.F(mo, t4, Nat.add(d, 0n))
    }
  }
    == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>
}:
  %e: {
    Some{
      C.Term.Eql{
        D.Mo.F(mo, t2, Nat.add(d, 0n)),
        D.Mo.F(mo, t3, Nat.add(d, 0n)),
        D.Mo.F(mo, t4, Nat.add(d, 0n))
      }
    }
      == Some{D.Mo.F(mo, _, d)}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    C.Term,
    D.Mo.F(mo, C.Term.Eql{t2, t3, t4}, d),
    C.Term.Eql{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d), D.Mo.F(mo, t4, d)},
    F.Eql(mo, t2, t3, t4, d)
  ): {
    Some{
      C.Term.Eql{
        D.Mo.F(mo, t2, Nat.add(d, 0n)),
        D.Mo.F(mo, t3, Nat.add(d, 0n)),
        D.Mo.F(mo, t4, Nat.add(d, 0n))
      }
    }
      == Some{_}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      C.Term.Eql{D.Mo.F(mo, t2, _), D.Mo.F(mo, t3, Nat.add(d, 0n)), D.Mo.F(mo, t4, Nat.add(d, 0n))}
    }
      == Some{
        C.Term.Eql{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d), D.Mo.F(mo, t4, d)}
      }: Maybe<&2, C.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      C.Term.Eql{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, _), D.Mo.F(mo, t4, Nat.add(d, 0n))}
    }
      == Some{
        C.Term.Eql{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d), D.Mo.F(mo, t4, d)}
      }: Maybe<&2, C.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      C.Term.Eql{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d), D.Mo.F(mo, t4, _)}
    }
      == Some{
        C.Term.Eql{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d), D.Mo.F(mo, t4, d)}
      }: Maybe<&2, C.Term>
  }
  {==}

def Tg.c18(
  +mo: D.Mo,
  +t2: C.Term,
  +t3: C.Term,
  +t4: C.Term,
  +d: Nat,
  -T0: C.Term,
  e: {C.Term.Rwt{t2, t3, t4} == T0: C.Term}
) -> {
  Some{
    C.Term.Rwt{
      D.Mo.F(mo, t2, Nat.add(d, 0n)),
      D.Mo.F(mo, t3, Nat.add(d, 2n)),
      D.Mo.F(mo, t4, Nat.add(d, 0n))
    }
  }
    == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>
}:
  %e: {
    Some{
      C.Term.Rwt{
        D.Mo.F(mo, t2, Nat.add(d, 0n)),
        D.Mo.F(mo, t3, Nat.add(d, 2n)),
        D.Mo.F(mo, t4, Nat.add(d, 0n))
      }
    }
      == Some{D.Mo.F(mo, _, d)}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    C.Term,
    D.Mo.F(mo, C.Term.Rwt{t2, t3, t4}, d),
    C.Term.Rwt{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 2n+d), D.Mo.F(mo, t4, d)},
    F.Rwt(mo, t2, t3, t4, d)
  ): {
    Some{
      C.Term.Rwt{
        D.Mo.F(mo, t2, Nat.add(d, 0n)),
        D.Mo.F(mo, t3, Nat.add(d, 2n)),
        D.Mo.F(mo, t4, Nat.add(d, 0n))
      }
    }
      == Some{_}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      C.Term.Rwt{D.Mo.F(mo, t2, _), D.Mo.F(mo, t3, Nat.add(d, 2n)), D.Mo.F(mo, t4, Nat.add(d, 0n))}
    }
      == Some{
        C.Term.Rwt{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 2n+d), D.Mo.F(mo, t4, d)}
      }: Maybe<&2, C.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 2n),
    2n+d,
    Tg.add2(d)
  ): {
    Some{
      C.Term.Rwt{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, _), D.Mo.F(mo, t4, Nat.add(d, 0n))}
    }
      == Some{
        C.Term.Rwt{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 2n+d), D.Mo.F(mo, t4, d)}
      }: Maybe<&2, C.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      C.Term.Rwt{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 2n+d), D.Mo.F(mo, t4, _)}
    }
      == Some{
        C.Term.Rwt{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 2n+d), D.Mo.F(mo, t4, d)}
      }: Maybe<&2, C.Term>
  }
  {==}

def Tg.c0(
  +mo: D.Mo,
  +d: Nat,
  -T0: C.Term,
  +a: C.Term,
  ea: {D.Mo.F(mo, a, d) == a: C.Term},
  e: {a == T0: C.Term}
) -> {Some{a} == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>}:
  %e: {Some{a} == Some{D.Mo.F(mo, _, d)}: Maybe<&2, C.Term>}
  %Equal.sym(C.Term, D.Mo.F(mo, a, d), a, ea): {Some{a} == Some{_}: Maybe<&2, C.Term>}
  {==}

def Tg.c14(
  +mo: D.Mo,
  +k: List<&2, U32>,
  +t3: C.Term,
  +t4: C.Term,
  +d: Nat,
  -T0: C.Term,
  e: {C.Term.Mat{k, t3, t4} == T0: C.Term}
) -> {
  Some{
    C.Term.Mat{k, D.Mo.F(mo, t3, Nat.add(d, 0n)), D.Mo.F(mo, t4, Nat.add(d, 0n))}
  }
    == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>
}:
  %e: {
    Some{
      C.Term.Mat{k, D.Mo.F(mo, t3, Nat.add(d, 0n)), D.Mo.F(mo, t4, Nat.add(d, 0n))}
    }
      == Some{D.Mo.F(mo, _, d)}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    C.Term,
    D.Mo.F(mo, C.Term.Mat{k, t3, t4}, d),
    C.Term.Mat{k, D.Mo.F(mo, t3, d), D.Mo.F(mo, t4, d)},
    F.mat(mo, k, t3, t4, d)
  ): {
    Some{
      C.Term.Mat{k, D.Mo.F(mo, t3, Nat.add(d, 0n)), D.Mo.F(mo, t4, Nat.add(d, 0n))}
    }
      == Some{_}: Maybe<&2, C.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      C.Term.Mat{k, D.Mo.F(mo, t3, _), D.Mo.F(mo, t4, _)}
    }
      == Some{C.Term.Mat{k, D.Mo.F(mo, t3, d), D.Mo.F(mo, t4, d)}}: Maybe<&2, C.Term>
  }
  {==}

# a label: its name, from field 2
def Tg.lab(
  nm: Maybe<&2, List<&2, U32>>,
  +mo: D.Mo,
  +d: Nat,
  -T0: C.Term,
  h: {T.tm.named(nm, k => C.Term.Lab{k}) == Some{T0}: Maybe<&2, C.Term>}
) -> {T.tm.named(nm, k => C.Term.Lab{k}) == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>}:
  match nm:
    case None{}:
      Tg.ns(T0, {None{} == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>}, h)
    case Some{+k}:
      Tg.c0(mo, d, T0, C.Term.Lab{k}, F.lab(mo, k, d), Tg.some(C.Term.Lab{k}, T0, h))

# a λ-match of labels: its name, from field 2, and its parts in fields 3, 4
def Tg.mat(
  nm: Maybe<&2, List<&2, U32>>,
  +mo: D.Mo,
  +t3: C.Term,
  +t4: C.Term,
  +d: Nat,
  -T0: C.Term,
  h: {T.tm.mat(nm, Some{t3}, Some{t4}) == Some{T0}: Maybe<&2, C.Term>}
) -> {
  T.tm.mat(
    nm,
    Some{D.Mo.F(mo, t3, Nat.add(d, 0n))},
    Some{D.Mo.F(mo, t4, Nat.add(d, 0n))}
  )
    == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>
}:
  match nm:
    case None{}:
      Tg.ns(T0, {None{} == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>}, h)
    case Some{+k}:
      Tg.c14(mo, k, t3, t4, d, T0, Tg.some(C.Term.Mat{k, t3, t4}, T0, h))

# The claim
# ---------

# the copy of a frame's source cell, of the term T0, with each part k copied
# at the depth d + Tg.b(tg, k): the same tag and quantity, and the same name
# (field 2) for Lab and Mat, give Mo.F(T0, d)
def Tg.cg(
  +mo: D.Mo,
  tg: Nat,
  +q: C.Quan,
  +n: U32,
  +n2: U32,
  +x2: U32,
  +z2: U32,
  +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>,
  +t2: C.Term,
  +t3: C.Term,
  +t4: C.Term,
  +d: Nat,
  -T0: C.Term,
  ho: {W.Tg.ok(tg) == True{}: Bool},
  hz: {
    Bool.or(Bool.and(Nat.is_ne(tg, 13n), Nat.is_ne(tg, 14n)), U32.is_eq(z2, x2)) == True{}: Bool
  },
  h: {
    T.tm.cell(
      tg,
      q,
      n,
      x2,
      ks,
      img,
      u => Some{t2},
      u => Some{t3},
      u => Some{t4}
    )
      == Some{T0}: Maybe<&2, C.Term>
  }
) -> {
  T.tm.cell(
    tg,
    q,
    n2,
    z2,
    ks,
    img,
    u => Some{D.Mo.F(mo, t2, Nat.add(d, W.Tg.b(tg, 2n)))},
    u => Some{D.Mo.F(mo, t3, Nat.add(d, W.Tg.b(tg, 3n)))},
    u => Some{D.Mo.F(mo, t4, Nat.add(d, W.Tg.b(tg, 4n)))}
  )
    == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>
}:
  match tg:
    case 0n:
      K.Bo.tf(
        {
          T.tm.cell(
            0n,
            q,
            n2,
            z2,
            ks,
            img,
            u => Some{D.Mo.F(mo, t2, Nat.add(d, W.Tg.b(0n, 2n)))},
            u => Some{D.Mo.F(mo, t3, Nat.add(d, W.Tg.b(0n, 3n)))},
            u => Some{D.Mo.F(mo, t4, Nat.add(d, W.Tg.b(0n, 4n)))}
          )
            == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>
        },
        ho
      )
    case 1n:
      K.Bo.tf(
        {
          T.tm.cell(
            1n,
            q,
            n2,
            z2,
            ks,
            img,
            u => Some{D.Mo.F(mo, t2, Nat.add(d, W.Tg.b(1n, 2n)))},
            u => Some{D.Mo.F(mo, t3, Nat.add(d, W.Tg.b(1n, 3n)))},
            u => Some{D.Mo.F(mo, t4, Nat.add(d, W.Tg.b(1n, 4n)))}
          )
            == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>
        },
        ho
      )
    case 2n:
      Tg.c2(mo, t2, t3, d, T0, Tg.some(C.Term.Ann{t2, t3}, T0, h))
    case 3n:
      Tg.c3(mo, q, t2, t3, d, T0, Tg.some(C.Term.Let{q, t2, t3}, T0, h))
    case 4n:
      Tg.c4(mo, t2, d, T0, Tg.some(C.Term.Typ{t2}, T0, h))
    case 5n:
      Tg.c5(mo, t2, t3, d, T0, Tg.some(C.Term.Min{t2, t3}, T0, h))
    case 6n:
      Tg.c6(mo, q, t2, t3, d, T0, Tg.some(C.Term.All{q, t2, t3}, T0, h))
    case 7n:
      Tg.c7(mo, q, t2, d, T0, Tg.some(C.Term.Lam{q, t2}, T0, h))
    case 8n:
      Tg.c8(mo, q, t2, t3, d, T0, Tg.some(C.Term.App{q, t2, t3}, T0, h))
    case 9n:
      Tg.c9(mo, q, t2, t3, d, T0, Tg.some(C.Term.Sig{q, t2, t3}, T0, h))
    case 10n:
      Tg.c10(mo, q, t2, t3, d, T0, Tg.some(C.Term.Tup{q, t2, t3}, T0, h))
    case 11n:
      Tg.c11(mo, t2, d, T0, Tg.some(C.Term.Prj{t2}, T0, h))
    case 12n:
      K.Bo.tf(
        {
          T.tm.cell(
            12n,
            q,
            n2,
            z2,
            ks,
            img,
            u => Some{D.Mo.F(mo, t2, Nat.add(d, W.Tg.b(12n, 2n)))},
            u => Some{D.Mo.F(mo, t3, Nat.add(d, W.Tg.b(12n, 3n)))},
            u => Some{D.Mo.F(mo, t4, Nat.add(d, W.Tg.b(12n, 4n)))}
          )
            == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>
        },
        ho
      )
    case 13n:
      %Equal.sym(
        U32,
        z2,
        x2,
        K.U.eq(z2, x2, hz)
      ): {
        T.tm.named(
          T.tm.name(ks, _),
          k => C.Term.Lab{k}
        )
          == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>
      }
      Tg.lab(T.tm.name(ks, x2), mo, d, T0, h)
    case 14n:
      %Equal.sym(
        U32,
        z2,
        x2,
        K.U.eq(z2, x2, hz)
      ): {
        T.tm.mat(
          T.tm.name(ks, _),
          Some{D.Mo.F(mo, t3, Nat.add(d, 0n))},
          Some{D.Mo.F(mo, t4, Nat.add(d, 0n))}
        )
          == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>
      }
      Tg.mat(T.tm.name(ks, x2), mo, t3, t4, d, T0, h)
    case 15n:
      Tg.c0(mo, d, T0, C.Term.Efq{}, F.efq(mo, d), Tg.some(C.Term.Efq{}, T0, h))
    case 16n:
      Tg.c16(mo, t2, t3, t4, d, T0, Tg.some(C.Term.Eql{t2, t3, t4}, T0, h))
    case 17n:
      Tg.c0(mo, d, T0, C.Term.Rfl{}, F.rfl(mo, d), Tg.some(C.Term.Rfl{}, T0, h))
    case 18n:
      Tg.c18(mo, t2, t3, t4, d, T0, Tg.some(C.Term.Rwt{t2, t3, t4}, T0, h))
    case 19n+r:
      K.Bo.tf(
        {
          T.tm.cell(
            19n+r,
            q,
            n2,
            z2,
            ks,
            img,
            u => Some{D.Mo.F(mo, t2, Nat.add(d, W.Tg.b(19n+r, 2n)))},
            u => Some{D.Mo.F(mo, t3, Nat.add(d, W.Tg.b(19n+r, 3n)))},
            u => Some{D.Mo.F(mo, t4, Nat.add(d, W.Tg.b(19n+r, 4n)))}
          )
            == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, C.Term>
        },
        ho
      )
