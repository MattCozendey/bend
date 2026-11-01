# compiler: M.out gives the bytes of the focus' term, from Is
# ===========================================================
#
# out.post and out.done of proof_mach.bend, from out.post.of and out.done.of
# of proof_out.bend: the hypotheses of those (the registers, okn and the term
# of the focus' cell) come from the state S, from Is (is.okn) and, until
# proof_is.bend proves it, from is.tm, taken here as a hypothesis htm.

import Base
import ./impl.bend as C
import ./proof_term.bend as T
import ./proof_need.bend as PN
import ./proof_mach_defs.bend as MA
import ./proof_out.bend as O

def add_comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, PN.add_zero(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, b), Nat.add(b, p), add_comm(p, b)) : {1n+_ == Nat.add(b, 1n+p) : Nat}
      Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), PN.add_succ_r(b, p))

# Is gives okn: each node is a cell (Nd), a Ref's or an Enu's image is its
# term, a label holds the number of its name (Nm), and a pair's parts are
# such nodes too
def is.okn(t: C.Term, +ds: List<&2, C.Def>, +m: C.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, +c: U32, +h: MA.Is(ds, m, im, fi, nx, ks, img, c, t)) ->
  {O.okn(C.Term.size(t), m, ks, img, c, im, fi, nx) == True{} : Bool}:
  match t:
    case C.Term.Var{+i}:
      (nd, rr) = h
      (hc, n1) = nd
      (ow, n2) = n1
      (et, n3) = n2
      O.okn.node(0n, m, ks, img, c, im, fi, nx, hc,
        O.oimg.eq(O.Tg(m, c), 0, T.tm.image(img, c), et, {==}),
        O.olab.eq(O.Tg(m, c), 0, ks, O.Fd(2n, m, c), et, {==}),
        O.okids.eq(O.Tg(m, c), 0, Bool.and(O.okn(0n, m, ks, img, O.Fd(2n, m, c), im, fi, nx), O.okn(0n, m, ks, img, O.Fd(3n, m, c), im, fi, nx)), et, {==}))
    case C.Term.Ref{+k}:
      (nd, rr) = h
      (hc, n1) = nd
      (ow, n2) = n1
      (et, n3) = n2
      (eimg, r2) = rr
      O.okn.node(0n, m, ks, img, c, im, fi, nx, hc,
        O.oimg.eq(O.Tg(m, c), 1, T.tm.image(img, c), et, O.oimg.ref(T.tm.image(img, c), k, eimg)),
        O.olab.eq(O.Tg(m, c), 1, ks, O.Fd(2n, m, c), et, {==}),
        O.okids.eq(O.Tg(m, c), 1, Bool.and(O.okn(0n, m, ks, img, O.Fd(2n, m, c), im, fi, nx), O.okn(0n, m, ks, img, O.Fd(3n, m, c), im, fi, nx)), et, {==}))
    case C.Term.Ann{+y, +z}:
      (nd, rr) = h
      (hc, n1) = nd
      (ow, n2) = n1
      (et, n3) = n2
      O.okn.node(Nat.add(C.Term.size(y), C.Term.size(z)), m, ks, img, c, im, fi, nx, hc,
        O.oimg.eq(O.Tg(m, c), 2, T.tm.image(img, c), et, {==}),
        O.olab.eq(O.Tg(m, c), 2, ks, O.Fd(2n, m, c), et, {==}),
        O.okids.eq(O.Tg(m, c), 2, Bool.and(O.okn(Nat.add(C.Term.size(y), C.Term.size(z)), m, ks, img, O.Fd(2n, m, c), im, fi, nx), O.okn(Nat.add(C.Term.size(y), C.Term.size(z)), m, ks, img, O.Fd(3n, m, c), im, fi, nx)), et, {==}))
    case C.Term.Let{+q, +y, +z}:
      (nd, rr) = h
      (hc, n1) = nd
      (ow, n2) = n1
      (et, n3) = n2
      O.okn.node(Nat.add(C.Term.size(y), C.Term.size(z)), m, ks, img, c, im, fi, nx, hc,
        O.oimg.eq(O.Tg(m, c), 3, T.tm.image(img, c), et, {==}),
        O.olab.eq(O.Tg(m, c), 3, ks, O.Fd(2n, m, c), et, {==}),
        O.okids.eq(O.Tg(m, c), 3, Bool.and(O.okn(Nat.add(C.Term.size(y), C.Term.size(z)), m, ks, img, O.Fd(2n, m, c), im, fi, nx), O.okn(Nat.add(C.Term.size(y), C.Term.size(z)), m, ks, img, O.Fd(3n, m, c), im, fi, nx)), et, {==}))
    case C.Term.Typ{+y}:
      (nd, rr) = h
      (hc, n1) = nd
      (ow, n2) = n1
      (et, n3) = n2
      O.okn.node(C.Term.size(y), m, ks, img, c, im, fi, nx, hc,
        O.oimg.eq(O.Tg(m, c), 4, T.tm.image(img, c), et, {==}),
        O.olab.eq(O.Tg(m, c), 4, ks, O.Fd(2n, m, c), et, {==}),
        O.okids.eq(O.Tg(m, c), 4, Bool.and(O.okn(C.Term.size(y), m, ks, img, O.Fd(2n, m, c), im, fi, nx), O.okn(C.Term.size(y), m, ks, img, O.Fd(3n, m, c), im, fi, nx)), et, {==}))
    case C.Term.Min{+y, +z}:
      (nd, rr) = h
      (hc, n1) = nd
      (ow, n2) = n1
      (et, n3) = n2
      O.okn.node(Nat.add(C.Term.size(y), C.Term.size(z)), m, ks, img, c, im, fi, nx, hc,
        O.oimg.eq(O.Tg(m, c), 5, T.tm.image(img, c), et, {==}),
        O.olab.eq(O.Tg(m, c), 5, ks, O.Fd(2n, m, c), et, {==}),
        O.okids.eq(O.Tg(m, c), 5, Bool.and(O.okn(Nat.add(C.Term.size(y), C.Term.size(z)), m, ks, img, O.Fd(2n, m, c), im, fi, nx), O.okn(Nat.add(C.Term.size(y), C.Term.size(z)), m, ks, img, O.Fd(3n, m, c), im, fi, nx)), et, {==}))
    case C.Term.All{+q, +y, +z}:
      (nd, rr) = h
      (hc, n1) = nd
      (ow, n2) = n1
      (et, n3) = n2
      O.okn.node(Nat.add(C.Term.size(y), C.Term.size(z)), m, ks, img, c, im, fi, nx, hc,
        O.oimg.eq(O.Tg(m, c), 6, T.tm.image(img, c), et, {==}),
        O.olab.eq(O.Tg(m, c), 6, ks, O.Fd(2n, m, c), et, {==}),
        O.okids.eq(O.Tg(m, c), 6, Bool.and(O.okn(Nat.add(C.Term.size(y), C.Term.size(z)), m, ks, img, O.Fd(2n, m, c), im, fi, nx), O.okn(Nat.add(C.Term.size(y), C.Term.size(z)), m, ks, img, O.Fd(3n, m, c), im, fi, nx)), et, {==}))
    case C.Term.Lam{+q, +y}:
      (nd, rr) = h
      (hc, n1) = nd
      (ow, n2) = n1
      (et, n3) = n2
      O.okn.node(C.Term.size(y), m, ks, img, c, im, fi, nx, hc,
        O.oimg.eq(O.Tg(m, c), 7, T.tm.image(img, c), et, {==}),
        O.olab.eq(O.Tg(m, c), 7, ks, O.Fd(2n, m, c), et, {==}),
        O.okids.eq(O.Tg(m, c), 7, Bool.and(O.okn(C.Term.size(y), m, ks, img, O.Fd(2n, m, c), im, fi, nx), O.okn(C.Term.size(y), m, ks, img, O.Fd(3n, m, c), im, fi, nx)), et, {==}))
    case C.Term.App{+q, +y, +z}:
      (nd, rr) = h
      (hc, n1) = nd
      (ow, n2) = n1
      (et, n3) = n2
      O.okn.node(Nat.add(C.Term.size(y), C.Term.size(z)), m, ks, img, c, im, fi, nx, hc,
        O.oimg.eq(O.Tg(m, c), 8, T.tm.image(img, c), et, {==}),
        O.olab.eq(O.Tg(m, c), 8, ks, O.Fd(2n, m, c), et, {==}),
        O.okids.eq(O.Tg(m, c), 8, Bool.and(O.okn(Nat.add(C.Term.size(y), C.Term.size(z)), m, ks, img, O.Fd(2n, m, c), im, fi, nx), O.okn(Nat.add(C.Term.size(y), C.Term.size(z)), m, ks, img, O.Fd(3n, m, c), im, fi, nx)), et, {==}))
    case C.Term.Sig{+q, +y, +z}:
      (nd, rr) = h
      (hc, n1) = nd
      (ow, n2) = n1
      (et, n3) = n2
      O.okn.node(Nat.add(C.Term.size(y), C.Term.size(z)), m, ks, img, c, im, fi, nx, hc,
        O.oimg.eq(O.Tg(m, c), 9, T.tm.image(img, c), et, {==}),
        O.olab.eq(O.Tg(m, c), 9, ks, O.Fd(2n, m, c), et, {==}),
        O.okids.eq(O.Tg(m, c), 9, Bool.and(O.okn(Nat.add(C.Term.size(y), C.Term.size(z)), m, ks, img, O.Fd(2n, m, c), im, fi, nx), O.okn(Nat.add(C.Term.size(y), C.Term.size(z)), m, ks, img, O.Fd(3n, m, c), im, fi, nx)), et, {==}))
    case C.Term.Tup{+q, +y, +z}:
      (nd, rr) = h
      (hc, n1) = nd
      (ow, n2) = n1
      (et, n3) = n2
      (qs, r2) = rr
      (pa, pb) = r2
      (spa, ia) = pa
      (spb, ib) = pb
      O.okn.node(Nat.add(C.Term.size(y), C.Term.size(z)), m, ks, img, c, im, fi, nx, hc,
        O.oimg.eq(O.Tg(m, c), 10, T.tm.image(img, c), et, {==}),
        O.olab.eq(O.Tg(m, c), 10, ks, O.Fd(2n, m, c), et, {==}),
        O.okids.tup(O.Tg(m, c), Nat.add(C.Term.size(y), C.Term.size(z)), m, ks, img, c, im, fi, nx,
        O.okn.mono(C.Term.size(y), C.Term.size(z), m, ks, img, O.Fd(2n, m, c), im, fi, nx, is.okn(y, ds, m, im, fi, nx, ks, img, O.Fd(2n, m, c), ia)),
        O.Tr(Nat, w => {O.okn(w, m, ks, img, O.Fd(3n, m, c), im, fi, nx) == True{} : Bool}, Nat.add(C.Term.size(z), C.Term.size(y)), Nat.add(C.Term.size(y), C.Term.size(z)),
          add_comm(C.Term.size(z), C.Term.size(y)), O.okn.mono(C.Term.size(z), C.Term.size(y), m, ks, img, O.Fd(3n, m, c), im, fi, nx,
            is.okn(z, ds, m, im, fi, nx, ks, img, O.Fd(3n, m, c), ib)))))
    case C.Term.Prj{+y}:
      (nd, rr) = h
      (hc, n1) = nd
      (ow, n2) = n1
      (et, n3) = n2
      O.okn.node(C.Term.size(y), m, ks, img, c, im, fi, nx, hc,
        O.oimg.eq(O.Tg(m, c), 11, T.tm.image(img, c), et, {==}),
        O.olab.eq(O.Tg(m, c), 11, ks, O.Fd(2n, m, c), et, {==}),
        O.okids.eq(O.Tg(m, c), 11, Bool.and(O.okn(C.Term.size(y), m, ks, img, O.Fd(2n, m, c), im, fi, nx), O.okn(C.Term.size(y), m, ks, img, O.Fd(3n, m, c), im, fi, nx)), et, {==}))
    case C.Term.Enu{+e}:
      (nd, rr) = h
      (hc, n1) = nd
      (ow, n2) = n1
      (et, n3) = n2
      (eimg, r2) = rr
      O.okn.node(0n, m, ks, img, c, im, fi, nx, hc,
        O.oimg.eq(O.Tg(m, c), 12, T.tm.image(img, c), et, O.oimg.enu(T.tm.image(img, c), e, eimg)),
        O.olab.eq(O.Tg(m, c), 12, ks, O.Fd(2n, m, c), et, {==}),
        O.okids.eq(O.Tg(m, c), 12, Bool.and(O.okn(0n, m, ks, img, O.Fd(2n, m, c), im, fi, nx), O.okn(0n, m, ks, img, O.Fd(3n, m, c), im, fi, nx)), et, {==}))
    case C.Term.Lab{+k}:
      (nd, rr) = h
      (hc, n1) = nd
      (ow, n2) = n1
      (et, n3) = n2
      (en, ej) = rr
      O.okn.node(0n, m, ks, img, c, im, fi, nx, hc,
        O.oimg.eq(O.Tg(m, c), 13, T.tm.image(img, c), et, {==}),
        O.olab.eq(O.Tg(m, c), 13, ks, O.Fd(2n, m, c), et, O.olab.lab(ks, O.Fd(2n, m, c), k, en, ej)),
        O.okids.eq(O.Tg(m, c), 13, Bool.and(O.okn(0n, m, ks, img, O.Fd(2n, m, c), im, fi, nx), O.okn(0n, m, ks, img, O.Fd(3n, m, c), im, fi, nx)), et, {==}))
    case C.Term.Mat{+k, +y, +z}:
      (nd, rr) = h
      (hc, n1) = nd
      (ow, n2) = n1
      (et, n3) = n2
      O.okn.node(Nat.add(C.Term.size(y), C.Term.size(z)), m, ks, img, c, im, fi, nx, hc,
        O.oimg.eq(O.Tg(m, c), 14, T.tm.image(img, c), et, {==}),
        O.olab.eq(O.Tg(m, c), 14, ks, O.Fd(2n, m, c), et, {==}),
        O.okids.eq(O.Tg(m, c), 14, Bool.and(O.okn(Nat.add(C.Term.size(y), C.Term.size(z)), m, ks, img, O.Fd(2n, m, c), im, fi, nx), O.okn(Nat.add(C.Term.size(y), C.Term.size(z)), m, ks, img, O.Fd(3n, m, c), im, fi, nx)), et, {==}))
    case C.Term.Efq{}:
      (hc, n1) = h
      (ow, n2) = n1
      (et, n3) = n2
      O.okn.node(0n, m, ks, img, c, im, fi, nx, hc,
        O.oimg.eq(O.Tg(m, c), 15, T.tm.image(img, c), et, {==}),
        O.olab.eq(O.Tg(m, c), 15, ks, O.Fd(2n, m, c), et, {==}),
        O.okids.eq(O.Tg(m, c), 15, Bool.and(O.okn(0n, m, ks, img, O.Fd(2n, m, c), im, fi, nx), O.okn(0n, m, ks, img, O.Fd(3n, m, c), im, fi, nx)), et, {==}))
    case C.Term.Eql{+y, +z, +w}:
      (nd, rr) = h
      (hc, n1) = nd
      (ow, n2) = n1
      (et, n3) = n2
      O.okn.node(Nat.add(C.Term.size(y), Nat.add(C.Term.size(z), C.Term.size(w))), m, ks, img, c, im, fi, nx, hc,
        O.oimg.eq(O.Tg(m, c), 16, T.tm.image(img, c), et, {==}),
        O.olab.eq(O.Tg(m, c), 16, ks, O.Fd(2n, m, c), et, {==}),
        O.okids.eq(O.Tg(m, c), 16, Bool.and(O.okn(Nat.add(C.Term.size(y), Nat.add(C.Term.size(z), C.Term.size(w))), m, ks, img, O.Fd(2n, m, c), im, fi, nx), O.okn(Nat.add(C.Term.size(y), Nat.add(C.Term.size(z), C.Term.size(w))), m, ks, img, O.Fd(3n, m, c), im, fi, nx)), et, {==}))
    case C.Term.Rfl{}:
      (hc, n1) = h
      (ow, n2) = n1
      (et, n3) = n2
      O.okn.node(0n, m, ks, img, c, im, fi, nx, hc,
        O.oimg.eq(O.Tg(m, c), 17, T.tm.image(img, c), et, {==}),
        O.olab.eq(O.Tg(m, c), 17, ks, O.Fd(2n, m, c), et, {==}),
        O.okids.eq(O.Tg(m, c), 17, Bool.and(O.okn(0n, m, ks, img, O.Fd(2n, m, c), im, fi, nx), O.okn(0n, m, ks, img, O.Fd(3n, m, c), im, fi, nx)), et, {==}))
    case C.Term.Rwt{+y, +z, +w}:
      (nd, rr) = h
      (hc, n1) = nd
      (ow, n2) = n1
      (et, n3) = n2
      O.okn.node(Nat.add(C.Term.size(y), Nat.add(C.Term.size(z), C.Term.size(w))), m, ks, img, c, im, fi, nx, hc,
        O.oimg.eq(O.Tg(m, c), 18, T.tm.image(img, c), et, {==}),
        O.olab.eq(O.Tg(m, c), 18, ks, O.Fd(2n, m, c), et, {==}),
        O.okids.eq(O.Tg(m, c), 18, Bool.and(O.okn(Nat.add(C.Term.size(y), Nat.add(C.Term.size(z), C.Term.size(w))), m, ks, img, O.Fd(2n, m, c), im, fi, nx), O.okn(Nat.add(C.Term.size(y), Nat.add(C.Term.size(z), C.Term.size(w))), m, ks, img, O.Fd(3n, m, c), im, fi, nx)), et, {==}))

# proof_out.bend's OutH, PostO and EndsO are proof_mach.bend's
def map.outh(+v: C.Term, +s: U32, st2: C.Cir.State, h: O.OutH(v, s, st2)) -> MA.OutH(v, s, st2):
  match st2:
    case C.Cir.State{_, _, _, _, _, _, _, _, _, _}:
      h

def map.post(o: C.Cir.Out, +v: C.Term, h: O.PostO(o, v)) -> MA.Post(False{}, o, st => Empty, s => st2 => MA.OutH(v, s, st2)):
  match o:
    case C.Cir.Out.next{st}:
      h
    case C.Cir.Out.halt{+s, st}:
      map.outh(v, s, st, h)
    case C.Cir.Out.out_of_memory{}:
      h
    case C.Cir.Out.trap{}:
      h
    case C.Cir.Out.not_done{}:
      h

def map.ends(o: C.Cir.Out, h: O.EndsO(o)) -> MA.Ends(o):
  match o:
    case C.Cir.Out.next{st}:
      h
    case C.Cir.Out.halt{s, st}:
      h
    case C.Cir.Out.out_of_memory{}:
      h
    case C.Cir.Out.trap{}:
      h
    case C.Cir.Out.not_done{}:
      h

def map.done(+st: C.Cir.State, h: Sigma<&2, &2, Nat, F => O.EndsO(C.Cir.exec(F, C.M.out(), st))>) ->
  MA.Ex(Nat, f => MA.Ends(C.Cir.exec(f, C.M.out(), st))):
  (+f, e) = h
  (f, map.ends(C.Cir.exec(f, C.M.out(), st), e))

# out.post of proof_mach.bend: in mode 1 with no frame, from the focus' cell
# of the value v, for any fuel f, M.out halts as OutH says, runs out of
# memory, or runs out of fuel. htm is is.tm (proof_is.bend) at foc and v.
def out.post(+f: Nat, +ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32,
  +pend: U32, +rest: MA.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>,
  +v: C.Term, +ks2: List<&2, List<&2, U32>>,
  +hv: MA.Is(ds, m, im, fi, nx, ks, img, foc, v),
  +hk: {ks == C.Img.known(ks2) : List<&2, List<&2, U32>>},
  +htm: {T.tm.of(C.Term.size(v), m, ks, img, foc) == Some{v} : Maybe<&2, C.Term>}) ->
  MA.Post(False{}, C.Cir.exec(f, C.M.out(), MA.S(foc, 1, 0, pend, rest, m, nx, fi, im, pg, lim, inp)), st => Empty,
    s => st2 => MA.OutH(v, s, st2)):
  match rest:
    case MA.R60{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62, +r63}:
      map.post(C.Cir.exec(f, C.M.out(), MA.S(foc, 1, 0, pend, rest, m, nx, fi, im, pg, lim, inp)), v,
        O.out.post.of(C.Term.size(v), f, MA.RG(foc, 1, 0, pend, MA.R60.list(rest)), m, nx, fi, im, pg, lim, inp, foc, ks, ks2, img, v,
          {==}, {==}, htm, hk, is.okn(v, ds, m, im, fi, nx, ks, img, foc, hv)))

# out.done of proof_mach.bend: with some fuel, M.out ends
def out.done(+ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +foc: U32,
  +pend: U32, +rest: MA.R60, +m: C.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>,
  +v: C.Term, +ks2: List<&2, List<&2, U32>>,
  +hv: MA.Is(ds, m, im, fi, nx, ks, img, foc, v),
  +hk: {ks == C.Img.known(ks2) : List<&2, List<&2, U32>>},
  +htm: {T.tm.of(C.Term.size(v), m, ks, img, foc) == Some{v} : Maybe<&2, C.Term>}) ->
  MA.Ex(Nat, f => MA.Ends(C.Cir.exec(f, C.M.out(), MA.S(foc, 1, 0, pend, rest, m, nx, fi, im, pg, lim, inp)))):
  match rest:
    case MA.R60{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62, +r63}:
      map.done(MA.S(foc, 1, 0, pend, rest, m, nx, fi, im, pg, lim, inp),
        O.out.done.of(C.Term.size(v), MA.RG(foc, 1, 0, pend, MA.R60.list(rest)), m, nx, fi, im, pg, lim, inp, Nil{}, 0, foc, ks, ks2, img, v,
          {==}, {==}, htm, hk, is.okn(v, ds, m, im, fi, nx, ks, img, foc, hv)))
