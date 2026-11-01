# compiler: the terms of the machine's cells, for layer B
# =======================================================
#
# The term that a cell of the machine (impl.bend, Machine) stands for, and
# the term of a whole state: its frames around its focus, as the Lean
# machine's plugs puts them (bootstrap/lean, Machine.lean). Layer B relates
# these terms to Eval's steps.
#
# A cell's tag (bits 0 to 5 of field 0), its quantity (bits 6 and 7) and
# its parts (fields 2 to 4, by the table of the image) give its term. A
# label's or a λ-match's name is the name of its number in the image's list
# of names ks. A Ref or an Enu has no free variable, so a copy shares it and
# never makes one: its term is the one at its place in the image, in the
# list img (img's first is cell 1).

import Base
import ./impl.bend as C

def tm.quan(+q: U32) -> C.Quan:
  Bool.pick(C.Quan, U32.is_eq(q, 0), C.Quan.Q0{}, Bool.pick(C.Quan, U32.is_eq(q, 1), C.Quan.Q1{}, C.Quan.Q2{}))

# the name of the number i, in the image's list ks
def tm.name(ks: List<&2, List<&2, U32>>, +i: U32) -> Maybe<&2, List<&2, U32>>:
  List.get(&2, List<&2, U32>, ks, U32.to_nat(i))

# the term at the cell c of the image img
def tm.image(img: List<&2, C.Term>, +c: U32) -> Maybe<&2, C.Term>:
  List.get(&2, C.Term, img, U32.to_nat(U32.sub(c, 1)))

def tm.one(k: C.Term -> C.Term, r: Maybe<&2, C.Term>) -> Maybe<&2, C.Term>:
  match r:
    case None{}:
      None{}
    case Some{a}:
      Some{k(a)}

def tm.two(k: C.Term -> C.Term -> C.Term, r: Maybe<&2, C.Term>, s: Maybe<&2, C.Term>) -> Maybe<&2, C.Term>:
  match r s:
    case Some{a} Some{b}:
      Some{k(a, b)}
    case _ _:
      None{}

def tm.three(k: C.Term -> C.Term -> C.Term -> C.Term, r: Maybe<&2, C.Term>, s: Maybe<&2, C.Term>,
  t: Maybe<&2, C.Term>) -> Maybe<&2, C.Term>:
  match r s t:
    case Some{a} Some{b} Some{c}:
      Some{k(a, b, c)}
    case _ _ _:
      None{}

def tm.named(n: Maybe<&2, List<&2, U32>>, k: List<&2, U32> -> C.Term) -> Maybe<&2, C.Term>:
  match n:
    case None{}:
      None{}
    case Some{x}:
      Some{k(x)}

def tm.mat(n: Maybe<&2, List<&2, U32>>, r: Maybe<&2, C.Term>, s: Maybe<&2, C.Term>) -> Maybe<&2, C.Term>:
  match n r s:
    case Some{k} Some{h} Some{m}:
      Some{C.Term.Mat{k, h, m}}
    case _ _ _:
      None{}

# the term of the cell c of the tag tag, the quantity q and field 2 f2; p2,
# p3 and p4 read the terms of its parts, only where the tag has them; none
# for a cell that is no term
def tm.cell(tag: Nat, +q: C.Quan, +c: U32, +f2: U32, ks: List<&2, List<&2, U32>>, img: List<&2, C.Term>,
  p2: Unit -> Maybe<&2, C.Term>, p3: Unit -> Maybe<&2, C.Term>, p4: Unit -> Maybe<&2, C.Term>) -> Maybe<&2, C.Term>:
  match tag:
    case 0n:
      Some{C.Term.Var{U32.to_nat(f2)}}
    case 1n:
      tm.image(img, c)
    case 2n:
      tm.two(a => b => C.Term.Ann{a, b}, p2(Unit{}), p3(Unit{}))
    case 3n:
      tm.two(a => b => C.Term.Let{q, a, b}, p2(Unit{}), p3(Unit{}))
    case 4n:
      tm.one(a => C.Term.Typ{a}, p2(Unit{}))
    case 5n:
      tm.two(a => b => C.Term.Min{a, b}, p2(Unit{}), p3(Unit{}))
    case 6n:
      tm.two(a => b => C.Term.All{q, a, b}, p2(Unit{}), p3(Unit{}))
    case 7n:
      tm.one(a => C.Term.Lam{q, a}, p2(Unit{}))
    case 8n:
      tm.two(a => b => C.Term.App{q, a, b}, p2(Unit{}), p3(Unit{}))
    case 9n:
      tm.two(a => b => C.Term.Sig{q, a, b}, p2(Unit{}), p3(Unit{}))
    case 10n:
      tm.two(a => b => C.Term.Tup{q, a, b}, p2(Unit{}), p3(Unit{}))
    case 11n:
      tm.one(a => C.Term.Prj{a}, p2(Unit{}))
    case 12n:
      tm.image(img, c)
    case 13n:
      tm.named(tm.name(ks, f2), k => C.Term.Lab{k})
    case 14n:
      tm.mat(tm.name(ks, f2), p3(Unit{}), p4(Unit{}))
    case 15n:
      Some{C.Term.Efq{}}
    case 16n:
      tm.three(a => b => t => C.Term.Eql{a, b, t}, p2(Unit{}), p3(Unit{}), p4(Unit{}))
    case 17n:
      Some{C.Term.Rfl{}}
    case 18n:
      tm.three(a => b => t => C.Term.Rwt{a, b, t}, p2(Unit{}), p3(Unit{}), p4(Unit{}))
    case _:
      None{}

# the term of the cell c of the cells m, read at most fuel levels deep; none
# when the fuel ends first, or for a cell that is no term
def tm.of(fuel: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32) ->
  Maybe<&2, C.Term>:
  match fuel:
    case 0n:
      None{}
    case 1n++f:
      +cell = C.Cir.Cells.get(m, c)
      +f0 = C.Cir.Cell.get(0n, cell)
      tm.cell(U32.to_nat(U32.and(f0, 63)), tm.quan(U32.and(U32.shrn(f0, 6n), 3)), c, C.Cir.Cell.get(2n, cell), ks, img,
        u => tm.of(f, m, ks, img, C.Cir.Cell.get(2n, cell)), u => tm.of(f, m, ks, img, C.Cir.Cell.get(3n, cell)),
        u => tm.of(f, m, ks, img, C.Cir.Cell.get(4n, cell)))

def tm.bind(r: Maybe<&2, C.Term>, more: C.Term -> Maybe<&2, C.Term>) -> Maybe<&2, C.Term>:
  match r:
    case None{}:
      None{}
    case Some{u}:
      more(u)

# a frame of the kind kind (K.app_arg to K.min_a) and the quantity q, whose
# fields 2 and 3 have the terms a and b, with t in its hole
def tm.plug(kind: Nat, +q: C.Quan, a: Maybe<&2, C.Term>, b: Maybe<&2, C.Term>, t: C.Term) -> Maybe<&2, C.Term>:
  match kind:
    case 32n:
      tm.one(x => C.Term.App{q, t, x}, a)
    case 33n:
      tm.one(x => C.Term.App{q, t, x}, a)
    case 34n:
      tm.one(x => C.Term.App{q, x, t}, a)
    case 35n:
      tm.one(x => C.Term.Let{q, t, x}, a)
    case 36n:
      tm.one(x => C.Term.Tup{q, t, x}, a)
    case 37n:
      tm.one(x => C.Term.Tup{q, x, t}, a)
    case 38n:
      tm.two(x => y => C.Term.Rwt{t, x, y}, a, b)
    case 39n:
      tm.one(x => C.Term.Min{t, x}, a)
    case 40n:
      tm.one(x => C.Term.Min{x, t}, a)
    case _:
      None{}

def tm.plugs.if(top: Bool, t: C.Term, kind: Nat, +q: C.Quan, a: Maybe<&2, C.Term>, b: Maybe<&2, C.Term>,
  more: C.Term -> Maybe<&2, C.Term>) -> Maybe<&2, C.Term>:
  match top:
    case True{}:
      Some{t}
    case False{}:
      tm.bind(tm.plug(kind, q, a, b, t), more)

# the frames from the cell fr on (each links the next by field 1, the
# innermost first; 0 ends them), with t in the innermost's hole
def tm.plugs(fuel: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +fr: U32,
  t: C.Term) -> Maybe<&2, C.Term>:
  match fuel:
    case 0n:
      None{}
    case 1n++f:
      +cell = C.Cir.Cells.get(m, fr)
      +f0 = C.Cir.Cell.get(0n, cell)
      tm.plugs.if(U32.is_zero(fr), t, U32.to_nat(U32.and(f0, 63)), tm.quan(U32.and(U32.shrn(f0, 6n), 3)),
        tm.of(f, m, ks, img, C.Cir.Cell.get(2n, cell)), tm.of(f, m, ks, img, C.Cir.Cell.get(3n, cell)),
        u => tm.plugs(f, m, ks, img, C.Cir.Cell.get(1n, cell), u))

# the register r of regs, 0 when there is none
def tm.reg(regs: List<&2, U32>, +r: Nat) -> U32:
  Maybe.default(&2, U32, List.get(&2, U32, regs, r), 0)

# the term of a state of the machine: its frames (from register sp) around
# its focus (register focus)
def tm.state(+fuel: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, st: C.Cir.State) ->
  Maybe<&2, C.Term>:
  match st:
    case C.Cir.State{+regs, +cells, _, _, _, _, _, _, _, _}:
      tm.bind(tm.of(fuel, cells, ks, img, tm.reg(regs, C.R.focus())),
        t => tm.plugs(fuel, cells, ks, img, tm.reg(regs, C.R.sp()), t))

# the nodes of t in pre-order, as Img.term lays out their cells, then acc
def tm.pre(+t: C.Term, acc: List<&2, C.Term>) -> List<&2, C.Term>:
  match t:
    case C.Term.Var{_}:
      Con{t, acc}
    case C.Term.Ref{_}:
      Con{t, acc}
    case C.Term.Ann{+x, +T}:
      Con{t, tm.pre(x, tm.pre(T, acc))}
    case C.Term.Let{_, +v, +f}:
      Con{t, tm.pre(v, tm.pre(f, acc))}
    case C.Term.Typ{+q}:
      Con{t, tm.pre(q, acc)}
    case C.Term.Min{+a, +b}:
      Con{t, tm.pre(a, tm.pre(b, acc))}
    case C.Term.All{_, +A, +B}:
      Con{t, tm.pre(A, tm.pre(B, acc))}
    case C.Term.Lam{_, +f}:
      Con{t, tm.pre(f, acc)}
    case C.Term.App{_, +f, +x}:
      Con{t, tm.pre(f, tm.pre(x, acc))}
    case C.Term.Sig{_, +A, +B}:
      Con{t, tm.pre(A, tm.pre(B, acc))}
    case C.Term.Tup{_, +a, +b}:
      Con{t, tm.pre(a, tm.pre(b, acc))}
    case C.Term.Prj{+h}:
      Con{t, tm.pre(h, acc)}
    case C.Term.Enu{_}:
      Con{t, acc}
    case C.Term.Lab{_}:
      Con{t, acc}
    case C.Term.Mat{_, +h, +m}:
      Con{t, tm.pre(h, tm.pre(m, acc))}
    case C.Term.Efq{}:
      Con{t, acc}
    case C.Term.Eql{+a, +b, +T}:
      Con{t, tm.pre(a, tm.pre(b, tm.pre(T, acc)))}
    case C.Term.Rfl{}:
      Con{t, acc}
    case C.Term.Rwt{+e, +P, +f}:
      Con{t, tm.pre(e, tm.pre(P, tm.pre(f, acc)))}

def tm.bodies(ds: List<&2, C.Def>) -> List<&2, C.Term>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{C.Def{_, _, +v, _}, rest}:
      tm.pre(v, tm.bodies(rest))

# the terms of the image's cells, by place: the fixed cells (only the Ref of
# main, cell 88, is a Ref or an Enu; the others never look here), then the
# nodes of the bodies, as Img.cells lays them out
def tm.img(ds: List<&2, C.Def>) -> List<&2, C.Term>:
  List.append(&2, C.Term, List.replicate(C.Term, 87n, C.Term.Efq{}),
    Con{C.Term.Ref{C.Program.name.main()},
      List.append(&2, C.Term, List.replicate(C.Term, 275n, C.Term.Efq{}), tm.bodies(ds))})

# the image's names: the machine's own, then the book's (Img.cells)
def tm.names(ds: List<&2, C.Def>) -> List<&2, List<&2, U32>>:
  C.Img.known(C.Img.names.defs(ds))
