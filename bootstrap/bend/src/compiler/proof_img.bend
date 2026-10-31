# compiler: the proof of img.small
# =================================
#
# The image of a book of fewer than 2^26 bytes has fewer than 2^26 cells:
#
#   cells = 363 + the nodes of the bodies <= 363 + W
#   2 W   <= |p| <= 2^26 - 1, so W < 2^25
#
# where W is the number of term nodes of the book that Book.read gives: each
# node comes from its own token of 2 bytes. The reader's invariant: the nodes
# in its stack are at most the tokens read so far.

import Base
import ./impl.bend as C
import ./proof_need.bend as N

# Counting nodes
# --------------

# the nodes of t, plus n
def Nsz(t: C.Term, n: Nat) -> Nat:
  match t:
    case C.Term.Var{_}:
      1n+n
    case C.Term.Ref{_}:
      1n+n
    case C.Term.Ann{x, T}:
      1n+Nsz(x, Nsz(T, n))
    case C.Term.Let{_, v, f}:
      1n+Nsz(v, Nsz(f, n))
    case C.Term.Typ{q}:
      1n+Nsz(q, n)
    case C.Term.Min{a0, b0}:
      1n+Nsz(a0, Nsz(b0, n))
    case C.Term.All{_, A, B}:
      1n+Nsz(A, Nsz(B, n))
    case C.Term.Lam{_, f}:
      1n+Nsz(f, n)
    case C.Term.App{_, f, x}:
      1n+Nsz(f, Nsz(x, n))
    case C.Term.Sig{_, A, B}:
      1n+Nsz(A, Nsz(B, n))
    case C.Term.Tup{_, a0, b0}:
      1n+Nsz(a0, Nsz(b0, n))
    case C.Term.Prj{h}:
      1n+Nsz(h, n)
    case C.Term.Enu{_}:
      1n+n
    case C.Term.Lab{_}:
      1n+n
    case C.Term.Mat{_, h, m}:
      1n+Nsz(h, Nsz(m, n))
    case C.Term.Efq{}:
      1n+n
    case C.Term.Eql{a0, b0, T}:
      1n+Nsz(a0, Nsz(b0, Nsz(T, n)))
    case C.Term.Rfl{}:
      1n+n
    case C.Term.Rwt{e, P, f}:
      1n+Nsz(e, Nsz(P, Nsz(f, n)))

# Nsz moves an addend out
def shift(t: C.Term, +a: Nat, +b: Nat) -> {Nsz(t, Nat.add(a, b)) == Nat.add(Nsz(t, a), b) : Nat}:
  match t:
    case C.Term.Var{_}:
      {==}
    case C.Term.Ref{_}:
      {==}
    case C.Term.Ann{+x, +T}:
      %shift(x, Nsz(T, a), b) : {1n+Nsz(x, Nsz(T, Nat.add(a, b))) == 1n+_ : Nat}
      %shift(T, a, b) : {1n+Nsz(x, Nsz(T, Nat.add(a, b))) == 1n+Nsz(x, _) : Nat}
      {==}
    case C.Term.Let{_, +v, +f}:
      %shift(v, Nsz(f, a), b) : {1n+Nsz(v, Nsz(f, Nat.add(a, b))) == 1n+_ : Nat}
      %shift(f, a, b) : {1n+Nsz(v, Nsz(f, Nat.add(a, b))) == 1n+Nsz(v, _) : Nat}
      {==}
    case C.Term.Typ{+q}:
      %shift(q, a, b) : {1n+Nsz(q, Nat.add(a, b)) == 1n+_ : Nat}
      {==}
    case C.Term.Min{+a0, +b0}:
      %shift(a0, Nsz(b0, a), b) : {1n+Nsz(a0, Nsz(b0, Nat.add(a, b))) == 1n+_ : Nat}
      %shift(b0, a, b) : {1n+Nsz(a0, Nsz(b0, Nat.add(a, b))) == 1n+Nsz(a0, _) : Nat}
      {==}
    case C.Term.All{_, +A, +B}:
      %shift(A, Nsz(B, a), b) : {1n+Nsz(A, Nsz(B, Nat.add(a, b))) == 1n+_ : Nat}
      %shift(B, a, b) : {1n+Nsz(A, Nsz(B, Nat.add(a, b))) == 1n+Nsz(A, _) : Nat}
      {==}
    case C.Term.Lam{_, +f}:
      %shift(f, a, b) : {1n+Nsz(f, Nat.add(a, b)) == 1n+_ : Nat}
      {==}
    case C.Term.App{_, +f, +x}:
      %shift(f, Nsz(x, a), b) : {1n+Nsz(f, Nsz(x, Nat.add(a, b))) == 1n+_ : Nat}
      %shift(x, a, b) : {1n+Nsz(f, Nsz(x, Nat.add(a, b))) == 1n+Nsz(f, _) : Nat}
      {==}
    case C.Term.Sig{_, +A, +B}:
      %shift(A, Nsz(B, a), b) : {1n+Nsz(A, Nsz(B, Nat.add(a, b))) == 1n+_ : Nat}
      %shift(B, a, b) : {1n+Nsz(A, Nsz(B, Nat.add(a, b))) == 1n+Nsz(A, _) : Nat}
      {==}
    case C.Term.Tup{_, +a0, +b0}:
      %shift(a0, Nsz(b0, a), b) : {1n+Nsz(a0, Nsz(b0, Nat.add(a, b))) == 1n+_ : Nat}
      %shift(b0, a, b) : {1n+Nsz(a0, Nsz(b0, Nat.add(a, b))) == 1n+Nsz(a0, _) : Nat}
      {==}
    case C.Term.Prj{+h}:
      %shift(h, a, b) : {1n+Nsz(h, Nat.add(a, b)) == 1n+_ : Nat}
      {==}
    case C.Term.Enu{_}:
      {==}
    case C.Term.Lab{_}:
      {==}
    case C.Term.Mat{_, +h, +m}:
      %shift(h, Nsz(m, a), b) : {1n+Nsz(h, Nsz(m, Nat.add(a, b))) == 1n+_ : Nat}
      %shift(m, a, b) : {1n+Nsz(h, Nsz(m, Nat.add(a, b))) == 1n+Nsz(h, _) : Nat}
      {==}
    case C.Term.Efq{}:
      {==}
    case C.Term.Eql{+a0, +b0, +T}:
      %shift(a0, Nsz(b0, Nsz(T, a)), b) : {1n+Nsz(a0, Nsz(b0, Nsz(T, Nat.add(a, b)))) == 1n+_ : Nat}
      %shift(b0, Nsz(T, a), b) : {1n+Nsz(a0, Nsz(b0, Nsz(T, Nat.add(a, b)))) == 1n+Nsz(a0, _) : Nat}
      %shift(T, a, b) : {1n+Nsz(a0, Nsz(b0, Nsz(T, Nat.add(a, b)))) == 1n+Nsz(a0, Nsz(b0, _)) : Nat}
      {==}
    case C.Term.Rfl{}:
      {==}
    case C.Term.Rwt{+e, +P, +f}:
      %shift(e, Nsz(P, Nsz(f, a)), b) : {1n+Nsz(e, Nsz(P, Nsz(f, Nat.add(a, b)))) == 1n+_ : Nat}
      %shift(P, Nsz(f, a), b) : {1n+Nsz(e, Nsz(P, Nsz(f, Nat.add(a, b)))) == 1n+Nsz(e, _) : Nat}
      %shift(f, a, b) : {1n+Nsz(e, Nsz(P, Nsz(f, Nat.add(a, b)))) == 1n+Nsz(e, Nsz(P, _)) : Nat}
      {==}

# the cells of a term: one per node
def term_len(t: C.Term, +ks: List<&2, List<&2, U32>>, +es: List<&2, C.Img.Def>, +at: U32, +acc: List<&2, C.Cir.Cell>) ->
  {List.length(&2, C.Cir.Cell, C.Img.term(t, ks, es, at, acc)) == Nsz(t, List.length(&2, C.Cir.Cell, acc)) : Nat}:
  match t:
    case C.Term.Var{_}:
      {==}
    case C.Term.Ref{_}:
      {==}
    case C.Term.Ann{+x, +T}:
      %term_len(T, ks, es, U32.add(U32.inc(at), C.Img.size(x)), acc) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.Ann{x, T}, ks, es, at, acc)) == 1n+Nsz(x, _) : Nat}
      %term_len(x, ks, es, U32.inc(at), C.Img.term(T, ks, es, U32.add(U32.inc(at), C.Img.size(x)), acc)) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.Ann{x, T}, ks, es, at, acc)) == 1n+_ : Nat}
      {==}
    case C.Term.Let{+qq, +v, +f}:
      %term_len(f, ks, es, U32.add(U32.inc(at), C.Img.size(v)), acc) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.Let{qq, v, f}, ks, es, at, acc)) == 1n+Nsz(v, _) : Nat}
      %term_len(v, ks, es, U32.inc(at), C.Img.term(f, ks, es, U32.add(U32.inc(at), C.Img.size(v)), acc)) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.Let{qq, v, f}, ks, es, at, acc)) == 1n+_ : Nat}
      {==}
    case C.Term.Typ{+q}:
      %term_len(q, ks, es, U32.inc(at), acc) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.Typ{q}, ks, es, at, acc)) == 1n+_ : Nat}
      {==}
    case C.Term.Min{+a0, +b0}:
      %term_len(b0, ks, es, U32.add(U32.inc(at), C.Img.size(a0)), acc) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.Min{a0, b0}, ks, es, at, acc)) == 1n+Nsz(a0, _) : Nat}
      %term_len(a0, ks, es, U32.inc(at), C.Img.term(b0, ks, es, U32.add(U32.inc(at), C.Img.size(a0)), acc)) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.Min{a0, b0}, ks, es, at, acc)) == 1n+_ : Nat}
      {==}
    case C.Term.All{+qq, +A, +B}:
      %term_len(B, ks, es, U32.add(U32.inc(at), C.Img.size(A)), acc) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.All{qq, A, B}, ks, es, at, acc)) == 1n+Nsz(A, _) : Nat}
      %term_len(A, ks, es, U32.inc(at), C.Img.term(B, ks, es, U32.add(U32.inc(at), C.Img.size(A)), acc)) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.All{qq, A, B}, ks, es, at, acc)) == 1n+_ : Nat}
      {==}
    case C.Term.Lam{+qq, +f}:
      %term_len(f, ks, es, U32.inc(at), acc) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.Lam{qq, f}, ks, es, at, acc)) == 1n+_ : Nat}
      {==}
    case C.Term.App{+qq, +f, +x}:
      %term_len(x, ks, es, U32.add(U32.inc(at), C.Img.size(f)), acc) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.App{qq, f, x}, ks, es, at, acc)) == 1n+Nsz(f, _) : Nat}
      %term_len(f, ks, es, U32.inc(at), C.Img.term(x, ks, es, U32.add(U32.inc(at), C.Img.size(f)), acc)) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.App{qq, f, x}, ks, es, at, acc)) == 1n+_ : Nat}
      {==}
    case C.Term.Sig{+qq, +A, +B}:
      %term_len(B, ks, es, U32.add(U32.inc(at), C.Img.size(A)), acc) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.Sig{qq, A, B}, ks, es, at, acc)) == 1n+Nsz(A, _) : Nat}
      %term_len(A, ks, es, U32.inc(at), C.Img.term(B, ks, es, U32.add(U32.inc(at), C.Img.size(A)), acc)) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.Sig{qq, A, B}, ks, es, at, acc)) == 1n+_ : Nat}
      {==}
    case C.Term.Tup{+qq, +a0, +b0}:
      %term_len(b0, ks, es, U32.add(U32.inc(at), C.Img.size(a0)), acc) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.Tup{qq, a0, b0}, ks, es, at, acc)) == 1n+Nsz(a0, _) : Nat}
      %term_len(a0, ks, es, U32.inc(at), C.Img.term(b0, ks, es, U32.add(U32.inc(at), C.Img.size(a0)), acc)) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.Tup{qq, a0, b0}, ks, es, at, acc)) == 1n+_ : Nat}
      {==}
    case C.Term.Prj{+h}:
      %term_len(h, ks, es, U32.inc(at), acc) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.Prj{h}, ks, es, at, acc)) == 1n+_ : Nat}
      {==}
    case C.Term.Enu{_}:
      {==}
    case C.Term.Lab{_}:
      {==}
    case C.Term.Mat{+qq, +h, +m}:
      %term_len(m, ks, es, U32.add(U32.inc(at), C.Img.size(h)), acc) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.Mat{qq, h, m}, ks, es, at, acc)) == 1n+Nsz(h, _) : Nat}
      %term_len(h, ks, es, U32.inc(at), C.Img.term(m, ks, es, U32.add(U32.inc(at), C.Img.size(h)), acc)) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.Mat{qq, h, m}, ks, es, at, acc)) == 1n+_ : Nat}
      {==}
    case C.Term.Efq{}:
      {==}
    case C.Term.Eql{+a0, +b0, +T}:
      %term_len(T, ks, es, U32.add(U32.add(U32.inc(at), C.Img.size(a0)), C.Img.size(b0)), acc) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.Eql{a0, b0, T}, ks, es, at, acc)) == 1n+Nsz(a0, Nsz(b0, _)) : Nat}
      %term_len(b0, ks, es, U32.add(U32.inc(at), C.Img.size(a0)), C.Img.term(T, ks, es, U32.add(U32.add(U32.inc(at), C.Img.size(a0)), C.Img.size(b0)), acc)) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.Eql{a0, b0, T}, ks, es, at, acc)) == 1n+Nsz(a0, _) : Nat}
      %term_len(a0, ks, es, U32.inc(at), C.Img.term(b0, ks, es, U32.add(U32.inc(at), C.Img.size(a0)), C.Img.term(T, ks, es, U32.add(U32.add(U32.inc(at), C.Img.size(a0)), C.Img.size(b0)), acc))) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.Eql{a0, b0, T}, ks, es, at, acc)) == 1n+_ : Nat}
      {==}
    case C.Term.Rfl{}:
      {==}
    case C.Term.Rwt{+e, +P, +f}:
      %term_len(f, ks, es, U32.add(U32.add(U32.inc(at), C.Img.size(e)), C.Img.size(P)), acc) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.Rwt{e, P, f}, ks, es, at, acc)) == 1n+Nsz(e, Nsz(P, _)) : Nat}
      %term_len(P, ks, es, U32.add(U32.inc(at), C.Img.size(e)), C.Img.term(f, ks, es, U32.add(U32.add(U32.inc(at), C.Img.size(e)), C.Img.size(P)), acc)) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.Rwt{e, P, f}, ks, es, at, acc)) == 1n+Nsz(e, _) : Nat}
      %term_len(e, ks, es, U32.inc(at), C.Img.term(P, ks, es, U32.add(U32.inc(at), C.Img.size(e)), C.Img.term(f, ks, es, U32.add(U32.add(U32.inc(at), C.Img.size(e)), C.Img.size(P)), acc))) : {List.length(&2, C.Cir.Cell, C.Img.term(C.Term.Rwt{e, P, f}, ks, es, at, acc)) == 1n+_ : Nat}
      {==}

# Nsz with no addend, the addend added after
def dec_r(t: C.Term, +b: Nat) -> {Nat.add(Nsz(t, 0n), b) == Nsz(t, b) : Nat}:
  Equal.sym(Nat, Nsz(t, b), Nat.add(Nsz(t, 0n), b), shift(t, 0n, b))

# a + (b + c) = b + (a + c)
def add_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+Nat.add(p, c)), 1n+Nat.add(b, Nat.add(p, c)), N.add_succ_r(b, Nat.add(p, c))) : {1n+Nat.add(p, Nat.add(b, c)) == _ : Nat}
      %add_swap(p, b, c) : {1n+Nat.add(p, Nat.add(b, c)) == 1n+_ : Nat}
      {==}

# 2 + (a + l) = a + (2 + l)
def add_two(+a: Nat, +l: Nat) -> {2n+Nat.add(a, l) == Nat.add(a, 2n+l) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_two(p, l) : {3n+Nat.add(p, l) == 1n+_ : Nat}
      {==}

# x + x = 2x
def add_self(+x: Nat) -> {Nat.add(x, x) == Nat.double(x) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), N.add_succ_r(p, p)) : {1n+_ == Nat.double(1n+p) : Nat}
      %add_self(p) : {2n+Nat.add(p, p) == 2n+_ : Nat}
      {==}

# 1 + Nsz(t, n) = Nsz(t, 1 + n)
def Nsz_succ(+t: C.Term, +n: Nat) -> {1n+Nsz(t, n) == Nsz(t, 1n+n) : Nat}:
  %dec_r(t, n) : {1n+_ == Nsz(t, 1n+n) : Nat}
  %dec_r(t, 1n+n) : {1n+Nat.add(Nsz(t, 0n), n) == _ : Nat}
  Equal.sym(Nat, Nat.add(Nsz(t, 0n), 1n+n), 1n+Nat.add(Nsz(t, 0n), n), N.add_succ_r(Nsz(t, 0n), n))

# Nsz is monotone in its addend
def Nsz_mono(+t: C.Term, +a: Nat, +b: Nat, h: N.Le(a, b)) -> N.Le(Nsz(t, a), Nsz(t, b)):
  %dec_r(t, a) : N.Le(_, Nsz(t, b))
  %dec_r(t, b) : N.Le(Nat.add(Nsz(t, 0n), a), _)
  N.add_mono(Nsz(t, 0n), Nsz(t, 0n), a, b, N.le_refl(Nsz(t, 0n)), h)

# the addend is at most Nsz
def Nsz_ge(+t: C.Term, +m: Nat) -> N.Le(m, Nsz(t, m)):
  %dec_r(t, m) : N.Le(m, _)
  N.le_add_l(Nsz(t, 0n), m)

# two Nsz commute
def Nsz_swap(+v: C.Term, +w: C.Term, +m: Nat) -> {Nsz(w, Nsz(v, m)) == Nsz(v, Nsz(w, m)) : Nat}:
  %dec_r(v, m) : {Nsz(w, _) == Nsz(v, Nsz(w, m)) : Nat}
  %dec_r(w, Nat.add(Nsz(v, 0n), m)) : {_ == Nsz(v, Nsz(w, m)) : Nat}
  %dec_r(w, m) : {Nat.add(Nsz(w, 0n), Nat.add(Nsz(v, 0n), m)) == Nsz(v, _) : Nat}
  %dec_r(v, Nat.add(Nsz(w, 0n), m)) : {Nat.add(Nsz(w, 0n), Nat.add(Nsz(v, 0n), m)) == _ : Nat}
  add_swap(Nsz(w, 0n), Nsz(v, 0n), m)

# The reader's stack
# ------------------

# the nodes of a def, plus n
def Wdef(d: C.Def, n: Nat) -> Nat:
  match d:
    case C.Def{_, T, v, _}:
      Nsz(T, Nsz(v, n))

# the nodes of defs, plus n
def Wd(ds: List<&2, C.Def>, n: Nat) -> Nat:
  match ds:
    case Nil{}:
      n
    case Con{d, rest}:
      Wd(rest, Wdef(d, n))

# the nodes of an item, plus n
def Wi(it: C.Item, n: Nat) -> Nat:
  match it:
    case C.Item.term{t}:
      Nsz(t, n)
    case C.Item.def{d}:
      Wdef(d, n)
    case C.Item.defs{ds}:
      Wd(ds, n)
    case _:
      n

# the nodes of a stack, plus n
def Ws(st: List<&2, C.Item>, n: Nat) -> Nat:
  match st:
    case Nil{}:
      n
    case Con{it, rest}:
      Ws(rest, Wi(it, n))

# the nodes of a reader's state
def Wm(m: Maybe<List<&2, C.Item>>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{s}:
      Ws(s, 0n)

def Wdef_succ(d: C.Def, +n: Nat) -> {1n+Wdef(d, n) == Wdef(d, 1n+n) : Nat}:
  match d:
    case C.Def{_, +T, +v, _}:
      %Nsz_succ(v, n) : {1n+Nsz(T, Nsz(v, n)) == Nsz(T, _) : Nat}
      Nsz_succ(T, Nsz(v, n))

def Wd_succ(ds: List<&2, C.Def>, +n: Nat) -> {1n+Wd(ds, n) == Wd(ds, 1n+n) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +rest}:
      %Wdef_succ(d, n) : {1n+Wd(rest, Wdef(d, n)) == Wd(rest, _) : Nat}
      Wd_succ(rest, Wdef(d, n))

def Wi_succ(it: C.Item, +n: Nat) -> {1n+Wi(it, n) == Wi(it, 1n+n) : Nat}:
  match it:
    case C.Item.term{+t}:
      Nsz_succ(t, n)
    case C.Item.def{+d}:
      Wdef_succ(d, n)
    case C.Item.defs{+ds}:
      Wd_succ(ds, n)
    case C.Item.quan{_}:
      {==}
    case C.Item.nat{_}:
      {==}
    case C.Item.name{_}:
      {==}
    case C.Item.names{_}:
      {==}
    case C.Item.bool{_}:
      {==}

def Ws_succ(st: List<&2, C.Item>, +n: Nat) -> {Ws(st, 1n+n) == 1n+Ws(st, n) : Nat}:
  match st:
    case Nil{}:
      {==}
    case Con{+it, +rest}:
      %Wi_succ(it, n) : {Ws(rest, _) == 1n+Ws(rest, Wi(it, n)) : Nat}
      Ws_succ(rest, Wi(it, n))

# a node more on the stack
def bump(+rest: List<&2, C.Item>, +x: Nat) -> N.Le(Ws(rest, 1n+x), 1n+Ws(rest, x)):
  %Ws_succ(rest, x) : N.Le(Ws(rest, 1n+x), _)
  N.le_refl(Ws(rest, 1n+x))

# x <= 1 + x
def le_up(+x: Nat) -> N.Le(x, 1n+x):
  N.le_succ(x, x, N.le_refl(x))

# Each token adds at most one node
# --------------------------------

def succ.le(s0: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.succ(s0)), 1n+Ws(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{C.Item.quan{_}, _}:
      Unit{}
    case Con{C.Item.nat{_}, +rest}:
      le_up(Ws(rest, 0n))
    case Con{C.Item.name{_}, _}:
      Unit{}
    case Con{C.Item.names{_}, _}:
      Unit{}
    case Con{C.Item.bool{_}, _}:
      Unit{}
    case Con{C.Item.term{_}, _}:
      Unit{}
    case Con{C.Item.def{_}, _}:
      Unit{}
    case Con{C.Item.defs{_}, _}:
      Unit{}

def names.le(s0: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.names(s0)), 1n+Ws(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{C.Item.quan{_}, _}:
      Unit{}
    case Con{C.Item.nat{_}, _}:
      Unit{}
    case Con{C.Item.name{_}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{C.Item.quan{_}, _}:
          Unit{}
        case Con{C.Item.nat{_}, _}:
          Unit{}
        case Con{C.Item.name{_}, _}:
          Unit{}
        case Con{C.Item.names{_}, +rest}:
          le_up(Ws(rest, 0n))
        case Con{C.Item.bool{_}, _}:
          Unit{}
        case Con{C.Item.term{_}, _}:
          Unit{}
        case Con{C.Item.def{_}, _}:
          Unit{}
        case Con{C.Item.defs{_}, _}:
          Unit{}
    case Con{C.Item.names{_}, _}:
      Unit{}
    case Con{C.Item.bool{_}, _}:
      Unit{}
    case Con{C.Item.term{_}, _}:
      Unit{}
    case Con{C.Item.def{_}, _}:
      Unit{}
    case Con{C.Item.defs{_}, _}:
      Unit{}

def defs.le(s0: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.defs(s0)), 1n+Ws(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{C.Item.quan{_}, _}:
      Unit{}
    case Con{C.Item.nat{_}, _}:
      Unit{}
    case Con{C.Item.name{_}, _}:
      Unit{}
    case Con{C.Item.names{_}, _}:
      Unit{}
    case Con{C.Item.bool{_}, _}:
      Unit{}
    case Con{C.Item.term{_}, _}:
      Unit{}
    case Con{C.Item.def{+d}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{C.Item.quan{_}, _}:
          Unit{}
        case Con{C.Item.nat{_}, _}:
          Unit{}
        case Con{C.Item.name{_}, _}:
          Unit{}
        case Con{C.Item.names{_}, _}:
          Unit{}
        case Con{C.Item.bool{_}, _}:
          Unit{}
        case Con{C.Item.term{_}, _}:
          Unit{}
        case Con{C.Item.def{_}, _}:
          Unit{}
        case Con{C.Item.defs{+ds}, +rest}:
          le_up(Ws(rest, Wd(ds, Wdef(d, 0n))))
    case Con{C.Item.defs{_}, _}:
      Unit{}

def def.le(s0: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.def(s0)), 1n+Ws(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{C.Item.quan{_}, _}:
      Unit{}
    case Con{C.Item.nat{_}, _}:
      Unit{}
    case Con{C.Item.name{_}, _}:
      Unit{}
    case Con{C.Item.names{_}, _}:
      Unit{}
    case Con{C.Item.bool{_}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{C.Item.quan{_}, _}:
          Unit{}
        case Con{C.Item.nat{_}, _}:
          Unit{}
        case Con{C.Item.name{_}, _}:
          Unit{}
        case Con{C.Item.names{_}, _}:
          Unit{}
        case Con{C.Item.bool{_}, _}:
          Unit{}
        case Con{C.Item.term{+v}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{C.Item.quan{_}, _}:
              Unit{}
            case Con{C.Item.nat{_}, _}:
              Unit{}
            case Con{C.Item.name{_}, _}:
              Unit{}
            case Con{C.Item.names{_}, _}:
              Unit{}
            case Con{C.Item.bool{_}, _}:
              Unit{}
            case Con{C.Item.term{+T}, +s3}:
              match s3:
                case Nil{}:
                  Unit{}
                case Con{C.Item.quan{_}, _}:
                  Unit{}
                case Con{C.Item.nat{_}, _}:
                  Unit{}
                case Con{C.Item.name{_}, +rest}:
                  le_up(Ws(rest, Nsz(T, Nsz(v, 0n))))
                case Con{C.Item.names{_}, _}:
                  Unit{}
                case Con{C.Item.bool{_}, _}:
                  Unit{}
                case Con{C.Item.term{_}, _}:
                  Unit{}
                case Con{C.Item.def{_}, _}:
                  Unit{}
                case Con{C.Item.defs{_}, _}:
                  Unit{}
            case Con{C.Item.def{_}, _}:
              Unit{}
            case Con{C.Item.defs{_}, _}:
              Unit{}
        case Con{C.Item.def{_}, _}:
          Unit{}
        case Con{C.Item.defs{_}, _}:
          Unit{}
    case Con{C.Item.term{_}, _}:
      Unit{}
    case Con{C.Item.def{_}, _}:
      Unit{}
    case Con{C.Item.defs{_}, _}:
      Unit{}

def var.le(s0: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.var(s0)), 1n+Ws(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{C.Item.quan{_}, _}:
      Unit{}
    case Con{C.Item.nat{_}, +rest}:
      bump(rest, 0n)
    case Con{C.Item.name{_}, _}:
      Unit{}
    case Con{C.Item.names{_}, _}:
      Unit{}
    case Con{C.Item.bool{_}, _}:
      Unit{}
    case Con{C.Item.term{_}, _}:
      Unit{}
    case Con{C.Item.def{_}, _}:
      Unit{}
    case Con{C.Item.defs{_}, _}:
      Unit{}

def ref.le(s0: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.ref(s0)), 1n+Ws(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{C.Item.quan{_}, _}:
      Unit{}
    case Con{C.Item.nat{_}, _}:
      Unit{}
    case Con{C.Item.name{_}, +rest}:
      bump(rest, 0n)
    case Con{C.Item.names{_}, _}:
      Unit{}
    case Con{C.Item.bool{_}, _}:
      Unit{}
    case Con{C.Item.term{_}, _}:
      Unit{}
    case Con{C.Item.def{_}, _}:
      Unit{}
    case Con{C.Item.defs{_}, _}:
      Unit{}

def ann.le(s0: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.ann(s0)), 1n+Ws(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{C.Item.quan{_}, _}:
      Unit{}
    case Con{C.Item.nat{_}, _}:
      Unit{}
    case Con{C.Item.name{_}, _}:
      Unit{}
    case Con{C.Item.names{_}, _}:
      Unit{}
    case Con{C.Item.bool{_}, _}:
      Unit{}
    case Con{C.Item.term{+T}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{C.Item.quan{_}, _}:
          Unit{}
        case Con{C.Item.nat{_}, _}:
          Unit{}
        case Con{C.Item.name{_}, _}:
          Unit{}
        case Con{C.Item.names{_}, _}:
          Unit{}
        case Con{C.Item.bool{_}, _}:
          Unit{}
        case Con{C.Item.term{+x}, +rest}:
          bump(rest, Nsz(x, Nsz(T, 0n)))
        case Con{C.Item.def{_}, _}:
          Unit{}
        case Con{C.Item.defs{_}, _}:
          Unit{}
    case Con{C.Item.def{_}, _}:
      Unit{}
    case Con{C.Item.defs{_}, _}:
      Unit{}

def let.le(s0: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.let(s0)), 1n+Ws(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{C.Item.quan{_}, _}:
      Unit{}
    case Con{C.Item.nat{_}, _}:
      Unit{}
    case Con{C.Item.name{_}, _}:
      Unit{}
    case Con{C.Item.names{_}, _}:
      Unit{}
    case Con{C.Item.bool{_}, _}:
      Unit{}
    case Con{C.Item.term{+f}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{C.Item.quan{_}, _}:
          Unit{}
        case Con{C.Item.nat{_}, _}:
          Unit{}
        case Con{C.Item.name{_}, _}:
          Unit{}
        case Con{C.Item.names{_}, _}:
          Unit{}
        case Con{C.Item.bool{_}, _}:
          Unit{}
        case Con{C.Item.term{+v}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{C.Item.quan{_}, +rest}:
              bump(rest, Nsz(v, Nsz(f, 0n)))
            case Con{C.Item.nat{_}, _}:
              Unit{}
            case Con{C.Item.name{_}, _}:
              Unit{}
            case Con{C.Item.names{_}, _}:
              Unit{}
            case Con{C.Item.bool{_}, _}:
              Unit{}
            case Con{C.Item.term{_}, _}:
              Unit{}
            case Con{C.Item.def{_}, _}:
              Unit{}
            case Con{C.Item.defs{_}, _}:
              Unit{}
        case Con{C.Item.def{_}, _}:
          Unit{}
        case Con{C.Item.defs{_}, _}:
          Unit{}
    case Con{C.Item.def{_}, _}:
      Unit{}
    case Con{C.Item.defs{_}, _}:
      Unit{}

def typ.le(s0: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.typ(s0)), 1n+Ws(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{C.Item.quan{_}, _}:
      Unit{}
    case Con{C.Item.nat{_}, _}:
      Unit{}
    case Con{C.Item.name{_}, _}:
      Unit{}
    case Con{C.Item.names{_}, _}:
      Unit{}
    case Con{C.Item.bool{_}, _}:
      Unit{}
    case Con{C.Item.term{+q}, +rest}:
      bump(rest, Nsz(q, 0n))
    case Con{C.Item.def{_}, _}:
      Unit{}
    case Con{C.Item.defs{_}, _}:
      Unit{}

def min.le(s0: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.min(s0)), 1n+Ws(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{C.Item.quan{_}, _}:
      Unit{}
    case Con{C.Item.nat{_}, _}:
      Unit{}
    case Con{C.Item.name{_}, _}:
      Unit{}
    case Con{C.Item.names{_}, _}:
      Unit{}
    case Con{C.Item.bool{_}, _}:
      Unit{}
    case Con{C.Item.term{+b}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{C.Item.quan{_}, _}:
          Unit{}
        case Con{C.Item.nat{_}, _}:
          Unit{}
        case Con{C.Item.name{_}, _}:
          Unit{}
        case Con{C.Item.names{_}, _}:
          Unit{}
        case Con{C.Item.bool{_}, _}:
          Unit{}
        case Con{C.Item.term{+a}, +rest}:
          bump(rest, Nsz(a, Nsz(b, 0n)))
        case Con{C.Item.def{_}, _}:
          Unit{}
        case Con{C.Item.defs{_}, _}:
          Unit{}
    case Con{C.Item.def{_}, _}:
      Unit{}
    case Con{C.Item.defs{_}, _}:
      Unit{}

def all.le(s0: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.all(s0)), 1n+Ws(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{C.Item.quan{_}, _}:
      Unit{}
    case Con{C.Item.nat{_}, _}:
      Unit{}
    case Con{C.Item.name{_}, _}:
      Unit{}
    case Con{C.Item.names{_}, _}:
      Unit{}
    case Con{C.Item.bool{_}, _}:
      Unit{}
    case Con{C.Item.term{+B}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{C.Item.quan{_}, _}:
          Unit{}
        case Con{C.Item.nat{_}, _}:
          Unit{}
        case Con{C.Item.name{_}, _}:
          Unit{}
        case Con{C.Item.names{_}, _}:
          Unit{}
        case Con{C.Item.bool{_}, _}:
          Unit{}
        case Con{C.Item.term{+A}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{C.Item.quan{_}, +rest}:
              bump(rest, Nsz(A, Nsz(B, 0n)))
            case Con{C.Item.nat{_}, _}:
              Unit{}
            case Con{C.Item.name{_}, _}:
              Unit{}
            case Con{C.Item.names{_}, _}:
              Unit{}
            case Con{C.Item.bool{_}, _}:
              Unit{}
            case Con{C.Item.term{_}, _}:
              Unit{}
            case Con{C.Item.def{_}, _}:
              Unit{}
            case Con{C.Item.defs{_}, _}:
              Unit{}
        case Con{C.Item.def{_}, _}:
          Unit{}
        case Con{C.Item.defs{_}, _}:
          Unit{}
    case Con{C.Item.def{_}, _}:
      Unit{}
    case Con{C.Item.defs{_}, _}:
      Unit{}

def lam.le(s0: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.lam(s0)), 1n+Ws(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{C.Item.quan{_}, _}:
      Unit{}
    case Con{C.Item.nat{_}, _}:
      Unit{}
    case Con{C.Item.name{_}, _}:
      Unit{}
    case Con{C.Item.names{_}, _}:
      Unit{}
    case Con{C.Item.bool{_}, _}:
      Unit{}
    case Con{C.Item.term{+f}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{C.Item.quan{_}, +rest}:
          bump(rest, Nsz(f, 0n))
        case Con{C.Item.nat{_}, _}:
          Unit{}
        case Con{C.Item.name{_}, _}:
          Unit{}
        case Con{C.Item.names{_}, _}:
          Unit{}
        case Con{C.Item.bool{_}, _}:
          Unit{}
        case Con{C.Item.term{_}, _}:
          Unit{}
        case Con{C.Item.def{_}, _}:
          Unit{}
        case Con{C.Item.defs{_}, _}:
          Unit{}
    case Con{C.Item.def{_}, _}:
      Unit{}
    case Con{C.Item.defs{_}, _}:
      Unit{}

def app.le(s0: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.app(s0)), 1n+Ws(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{C.Item.quan{_}, _}:
      Unit{}
    case Con{C.Item.nat{_}, _}:
      Unit{}
    case Con{C.Item.name{_}, _}:
      Unit{}
    case Con{C.Item.names{_}, _}:
      Unit{}
    case Con{C.Item.bool{_}, _}:
      Unit{}
    case Con{C.Item.term{+x}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{C.Item.quan{_}, _}:
          Unit{}
        case Con{C.Item.nat{_}, _}:
          Unit{}
        case Con{C.Item.name{_}, _}:
          Unit{}
        case Con{C.Item.names{_}, _}:
          Unit{}
        case Con{C.Item.bool{_}, _}:
          Unit{}
        case Con{C.Item.term{+f}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{C.Item.quan{_}, +rest}:
              bump(rest, Nsz(f, Nsz(x, 0n)))
            case Con{C.Item.nat{_}, _}:
              Unit{}
            case Con{C.Item.name{_}, _}:
              Unit{}
            case Con{C.Item.names{_}, _}:
              Unit{}
            case Con{C.Item.bool{_}, _}:
              Unit{}
            case Con{C.Item.term{_}, _}:
              Unit{}
            case Con{C.Item.def{_}, _}:
              Unit{}
            case Con{C.Item.defs{_}, _}:
              Unit{}
        case Con{C.Item.def{_}, _}:
          Unit{}
        case Con{C.Item.defs{_}, _}:
          Unit{}
    case Con{C.Item.def{_}, _}:
      Unit{}
    case Con{C.Item.defs{_}, _}:
      Unit{}

def sig.le(s0: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.sig(s0)), 1n+Ws(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{C.Item.quan{_}, _}:
      Unit{}
    case Con{C.Item.nat{_}, _}:
      Unit{}
    case Con{C.Item.name{_}, _}:
      Unit{}
    case Con{C.Item.names{_}, _}:
      Unit{}
    case Con{C.Item.bool{_}, _}:
      Unit{}
    case Con{C.Item.term{+B}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{C.Item.quan{_}, _}:
          Unit{}
        case Con{C.Item.nat{_}, _}:
          Unit{}
        case Con{C.Item.name{_}, _}:
          Unit{}
        case Con{C.Item.names{_}, _}:
          Unit{}
        case Con{C.Item.bool{_}, _}:
          Unit{}
        case Con{C.Item.term{+A}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{C.Item.quan{_}, +rest}:
              bump(rest, Nsz(A, Nsz(B, 0n)))
            case Con{C.Item.nat{_}, _}:
              Unit{}
            case Con{C.Item.name{_}, _}:
              Unit{}
            case Con{C.Item.names{_}, _}:
              Unit{}
            case Con{C.Item.bool{_}, _}:
              Unit{}
            case Con{C.Item.term{_}, _}:
              Unit{}
            case Con{C.Item.def{_}, _}:
              Unit{}
            case Con{C.Item.defs{_}, _}:
              Unit{}
        case Con{C.Item.def{_}, _}:
          Unit{}
        case Con{C.Item.defs{_}, _}:
          Unit{}
    case Con{C.Item.def{_}, _}:
      Unit{}
    case Con{C.Item.defs{_}, _}:
      Unit{}

def tup.le(s0: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.tup(s0)), 1n+Ws(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{C.Item.quan{_}, _}:
      Unit{}
    case Con{C.Item.nat{_}, _}:
      Unit{}
    case Con{C.Item.name{_}, _}:
      Unit{}
    case Con{C.Item.names{_}, _}:
      Unit{}
    case Con{C.Item.bool{_}, _}:
      Unit{}
    case Con{C.Item.term{+b}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{C.Item.quan{_}, _}:
          Unit{}
        case Con{C.Item.nat{_}, _}:
          Unit{}
        case Con{C.Item.name{_}, _}:
          Unit{}
        case Con{C.Item.names{_}, _}:
          Unit{}
        case Con{C.Item.bool{_}, _}:
          Unit{}
        case Con{C.Item.term{+a}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{C.Item.quan{_}, +rest}:
              bump(rest, Nsz(a, Nsz(b, 0n)))
            case Con{C.Item.nat{_}, _}:
              Unit{}
            case Con{C.Item.name{_}, _}:
              Unit{}
            case Con{C.Item.names{_}, _}:
              Unit{}
            case Con{C.Item.bool{_}, _}:
              Unit{}
            case Con{C.Item.term{_}, _}:
              Unit{}
            case Con{C.Item.def{_}, _}:
              Unit{}
            case Con{C.Item.defs{_}, _}:
              Unit{}
        case Con{C.Item.def{_}, _}:
          Unit{}
        case Con{C.Item.defs{_}, _}:
          Unit{}
    case Con{C.Item.def{_}, _}:
      Unit{}
    case Con{C.Item.defs{_}, _}:
      Unit{}

def prj.le(s0: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.prj(s0)), 1n+Ws(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{C.Item.quan{_}, _}:
      Unit{}
    case Con{C.Item.nat{_}, _}:
      Unit{}
    case Con{C.Item.name{_}, _}:
      Unit{}
    case Con{C.Item.names{_}, _}:
      Unit{}
    case Con{C.Item.bool{_}, _}:
      Unit{}
    case Con{C.Item.term{+h}, +rest}:
      bump(rest, Nsz(h, 0n))
    case Con{C.Item.def{_}, _}:
      Unit{}
    case Con{C.Item.defs{_}, _}:
      Unit{}

def enu.le(s0: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.enu(s0)), 1n+Ws(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{C.Item.quan{_}, _}:
      Unit{}
    case Con{C.Item.nat{_}, _}:
      Unit{}
    case Con{C.Item.name{_}, _}:
      Unit{}
    case Con{C.Item.names{_}, +rest}:
      bump(rest, 0n)
    case Con{C.Item.bool{_}, _}:
      Unit{}
    case Con{C.Item.term{_}, _}:
      Unit{}
    case Con{C.Item.def{_}, _}:
      Unit{}
    case Con{C.Item.defs{_}, _}:
      Unit{}

def lab.le(s0: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.lab(s0)), 1n+Ws(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{C.Item.quan{_}, _}:
      Unit{}
    case Con{C.Item.nat{_}, _}:
      Unit{}
    case Con{C.Item.name{_}, +rest}:
      bump(rest, 0n)
    case Con{C.Item.names{_}, _}:
      Unit{}
    case Con{C.Item.bool{_}, _}:
      Unit{}
    case Con{C.Item.term{_}, _}:
      Unit{}
    case Con{C.Item.def{_}, _}:
      Unit{}
    case Con{C.Item.defs{_}, _}:
      Unit{}

def mat.le(s0: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.mat(s0)), 1n+Ws(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{C.Item.quan{_}, _}:
      Unit{}
    case Con{C.Item.nat{_}, _}:
      Unit{}
    case Con{C.Item.name{_}, _}:
      Unit{}
    case Con{C.Item.names{_}, _}:
      Unit{}
    case Con{C.Item.bool{_}, _}:
      Unit{}
    case Con{C.Item.term{+m}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{C.Item.quan{_}, _}:
          Unit{}
        case Con{C.Item.nat{_}, _}:
          Unit{}
        case Con{C.Item.name{_}, _}:
          Unit{}
        case Con{C.Item.names{_}, _}:
          Unit{}
        case Con{C.Item.bool{_}, _}:
          Unit{}
        case Con{C.Item.term{+h}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{C.Item.quan{_}, _}:
              Unit{}
            case Con{C.Item.nat{_}, _}:
              Unit{}
            case Con{C.Item.name{_}, +rest}:
              bump(rest, Nsz(h, Nsz(m, 0n)))
            case Con{C.Item.names{_}, _}:
              Unit{}
            case Con{C.Item.bool{_}, _}:
              Unit{}
            case Con{C.Item.term{_}, _}:
              Unit{}
            case Con{C.Item.def{_}, _}:
              Unit{}
            case Con{C.Item.defs{_}, _}:
              Unit{}
        case Con{C.Item.def{_}, _}:
          Unit{}
        case Con{C.Item.defs{_}, _}:
          Unit{}
    case Con{C.Item.def{_}, _}:
      Unit{}
    case Con{C.Item.defs{_}, _}:
      Unit{}

def eql.le(s0: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.eql(s0)), 1n+Ws(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{C.Item.quan{_}, _}:
      Unit{}
    case Con{C.Item.nat{_}, _}:
      Unit{}
    case Con{C.Item.name{_}, _}:
      Unit{}
    case Con{C.Item.names{_}, _}:
      Unit{}
    case Con{C.Item.bool{_}, _}:
      Unit{}
    case Con{C.Item.term{+T}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{C.Item.quan{_}, _}:
          Unit{}
        case Con{C.Item.nat{_}, _}:
          Unit{}
        case Con{C.Item.name{_}, _}:
          Unit{}
        case Con{C.Item.names{_}, _}:
          Unit{}
        case Con{C.Item.bool{_}, _}:
          Unit{}
        case Con{C.Item.term{+b}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{C.Item.quan{_}, _}:
              Unit{}
            case Con{C.Item.nat{_}, _}:
              Unit{}
            case Con{C.Item.name{_}, _}:
              Unit{}
            case Con{C.Item.names{_}, _}:
              Unit{}
            case Con{C.Item.bool{_}, _}:
              Unit{}
            case Con{C.Item.term{+a}, +rest}:
              bump(rest, Nsz(a, Nsz(b, Nsz(T, 0n))))
            case Con{C.Item.def{_}, _}:
              Unit{}
            case Con{C.Item.defs{_}, _}:
              Unit{}
        case Con{C.Item.def{_}, _}:
          Unit{}
        case Con{C.Item.defs{_}, _}:
          Unit{}
    case Con{C.Item.def{_}, _}:
      Unit{}
    case Con{C.Item.defs{_}, _}:
      Unit{}

def rwt.le(s0: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.rwt(s0)), 1n+Ws(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{C.Item.quan{_}, _}:
      Unit{}
    case Con{C.Item.nat{_}, _}:
      Unit{}
    case Con{C.Item.name{_}, _}:
      Unit{}
    case Con{C.Item.names{_}, _}:
      Unit{}
    case Con{C.Item.bool{_}, _}:
      Unit{}
    case Con{C.Item.term{+f}, +s1}:
      match s1:
        case Nil{}:
          Unit{}
        case Con{C.Item.quan{_}, _}:
          Unit{}
        case Con{C.Item.nat{_}, _}:
          Unit{}
        case Con{C.Item.name{_}, _}:
          Unit{}
        case Con{C.Item.names{_}, _}:
          Unit{}
        case Con{C.Item.bool{_}, _}:
          Unit{}
        case Con{C.Item.term{+P}, +s2}:
          match s2:
            case Nil{}:
              Unit{}
            case Con{C.Item.quan{_}, _}:
              Unit{}
            case Con{C.Item.nat{_}, _}:
              Unit{}
            case Con{C.Item.name{_}, _}:
              Unit{}
            case Con{C.Item.names{_}, _}:
              Unit{}
            case Con{C.Item.bool{_}, _}:
              Unit{}
            case Con{C.Item.term{+e}, +rest}:
              bump(rest, Nsz(e, Nsz(P, Nsz(f, 0n))))
            case Con{C.Item.def{_}, _}:
              Unit{}
            case Con{C.Item.defs{_}, _}:
              Unit{}
        case Con{C.Item.def{_}, _}:
          Unit{}
        case Con{C.Item.defs{_}, _}:
          Unit{}
    case Con{C.Item.def{_}, _}:
      Unit{}
    case Con{C.Item.defs{_}, _}:
      Unit{}

def byte.le(s0: List<&2, C.Item>, b: U32) -> N.Le(Wm(C.Book.read.byte(s0, b)), 1n+Ws(s0, 0n)):
  match s0:
    case Nil{}:
      Unit{}
    case Con{C.Item.quan{_}, _}:
      Unit{}
    case Con{C.Item.nat{_}, _}:
      Unit{}
    case Con{C.Item.name{_}, +rest}:
      le_up(Ws(rest, 0n))
    case Con{C.Item.names{_}, _}:
      Unit{}
    case Con{C.Item.bool{_}, _}:
      Unit{}
    case Con{C.Item.term{_}, _}:
      Unit{}
    case Con{C.Item.def{_}, _}:
      Unit{}
    case Con{C.Item.defs{_}, _}:
      Unit{}

def token32.le(n: Nat, +st: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.token32(n, st)), 1n+Ws(st, 0n)):
  match n:
    case 0n:
      rwt.le(st)
    case 1n+_:
      Unit{}

def token24.le(n: Nat, +st: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.token24(n, st)), 1n+Ws(st, 0n)):
  match n:
    case 0n:
      tup.le(st)
    case 1n:
      prj.le(st)
    case 2n:
      enu.le(st)
    case 3n:
      lab.le(st)
    case 4n:
      mat.le(st)
    case 5n:
      bump(st, 0n)
    case 6n:
      eql.le(st)
    case 7n:
      bump(st, 0n)
    case 8n+p:
      token32.le(p, st)

def token16.le(n: Nat, +st: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.token16(n, st)), 1n+Ws(st, 0n)):
  match n:
    case 0n:
      ann.le(st)
    case 1n:
      let.le(st)
    case 2n:
      typ.le(st)
    case 3n:
      min.le(st)
    case 4n:
      all.le(st)
    case 5n:
      lam.le(st)
    case 6n:
      app.le(st)
    case 7n:
      sig.le(st)
    case 8n+p:
      token24.le(p, st)

def token8.le(n: Nat, +st: List<&2, C.Item>) -> N.Le(Wm(C.Book.read.token8(n, st)), 1n+Ws(st, 0n)):
  match n:
    case 0n:
      names.le(st)
    case 1n:
      le_up(Ws(st, 0n))
    case 2n:
      le_up(Ws(st, 0n))
    case 3n:
      le_up(Ws(st, 0n))
    case 4n:
      defs.le(st)
    case 5n:
      def.le(st)
    case 6n:
      var.le(st)
    case 7n:
      ref.le(st)
    case 8n+p:
      token16.le(p, st)

def token.le(n: Nat, +st: List<&2, C.Item>, b: U32) -> N.Le(Wm(C.Book.read.token(n, st, b)), 1n+Ws(st, 0n)):
  match n:
    case 0n:
      le_up(Ws(st, 0n))
    case 1n:
      le_up(Ws(st, 0n))
    case 2n:
      le_up(Ws(st, 0n))
    case 3n:
      le_up(Ws(st, 0n))
    case 4n:
      succ.le(st)
    case 5n:
      le_up(Ws(st, 0n))
    case 6n:
      byte.le(st, b)
    case 7n:
      le_up(Ws(st, 0n))
    case 8n+p:
      token8.le(p, st)

def step.le(st: Maybe<List<&2, C.Item>>, tag: U32, b: U32) -> N.Le(Wm(C.Book.read.step(st, tag, b)), 1n+Wm(st)):
  match st:
    case None{}:
      Unit{}
    case Some{+s}:
      token.le(U32.to_nat(tag), s, b)


# Reading a book
# --------------

# None is not Some
def IsNone(m: Maybe<List<&2, C.Def>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{_}:
      Empty

def none_ne_some(-ds: List<&2, C.Def>, e: {None{} == Some{ds} : Maybe<List<&2, C.Def>>}) -> Empty:
  %e : IsNone(_)
  Unit{}

# the nodes of a read book
def Vd(m: Maybe<List<&2, C.Def>>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{ds}:
      Wd(ds, 0n)

# the end of the reading: the book's nodes are the stack's
def done.le(st: Maybe<List<&2, C.Item>>, +ds: List<&2, C.Def>, e: {C.Book.read.done(st) == Some{ds} : Maybe<List<&2, C.Def>>}) ->
  N.Le(Nat.double(Wd(ds, 0n)), Nat.add(Nat.double(Wm(st)), 0n)):
  match st:
    case None{}:
      Empty.absurd(N.Le(Nat.double(Wd(ds, 0n)), Nat.add(Nat.double(Wm(st)), 0n)), none_ne_some(ds, e))
    case Some{s}:
      match s:
        case Nil{}:
          Empty.absurd(N.Le(Nat.double(Wd(ds, 0n)), Nat.add(Nat.double(Wm(st)), 0n)), none_ne_some(ds, e))
        case Con{C.Item.quan{_}, _}:
          Empty.absurd(N.Le(Nat.double(Wd(ds, 0n)), Nat.add(Nat.double(Wm(st)), 0n)), none_ne_some(ds, e))
        case Con{C.Item.nat{_}, _}:
          Empty.absurd(N.Le(Nat.double(Wd(ds, 0n)), Nat.add(Nat.double(Wm(st)), 0n)), none_ne_some(ds, e))
        case Con{C.Item.name{_}, _}:
          Empty.absurd(N.Le(Nat.double(Wd(ds, 0n)), Nat.add(Nat.double(Wm(st)), 0n)), none_ne_some(ds, e))
        case Con{C.Item.names{_}, _}:
          Empty.absurd(N.Le(Nat.double(Wd(ds, 0n)), Nat.add(Nat.double(Wm(st)), 0n)), none_ne_some(ds, e))
        case Con{C.Item.bool{_}, _}:
          Empty.absurd(N.Le(Nat.double(Wd(ds, 0n)), Nat.add(Nat.double(Wm(st)), 0n)), none_ne_some(ds, e))
        case Con{C.Item.term{_}, _}:
          Empty.absurd(N.Le(Nat.double(Wd(ds, 0n)), Nat.add(Nat.double(Wm(st)), 0n)), none_ne_some(ds, e))
        case Con{C.Item.def{_}, _}:
          Empty.absurd(N.Le(Nat.double(Wd(ds, 0n)), Nat.add(Nat.double(Wm(st)), 0n)), none_ne_some(ds, e))
        case Con{C.Item.defs{+ds0}, t}:
          match t:
            case Nil{}:
              %e : N.Le(Nat.double(Vd(_)), Nat.add(Nat.double(Wd(ds0, 0n)), 0n))
              N.le_add_r(Nat.double(Wd(ds0, 0n)), 0n)
            case Con{_, _}:
              Empty.absurd(N.Le(Nat.double(Wd(ds, 0n)), Nat.add(Nat.double(Wm(st)), 0n)), none_ne_some(ds, e))

# the reading: twice the book's nodes are at most twice the stack's plus the
# bytes left
def go.le(xs: List<&2, U32>, st: Maybe<List<&2, C.Item>>, +ds: List<&2, C.Def>,
  e: {C.Book.read.go(xs, st) == Some{ds} : Maybe<List<&2, C.Def>>}
) -> N.Le(Nat.double(Wd(ds, 0n)), Nat.add(Nat.double(Wm(st)), List.length(&2, U32, xs))):
  match xs:
    case Nil{}:
      done.le(st, ds, e)
    case Con{_, Nil{}}:
      Empty.absurd(N.Le(Nat.double(Wd(ds, 0n)), Nat.add(Nat.double(Wm(st)), 1n)), none_ne_some(ds, e))
    case Con{+tag, Con{+b, +rest}}:
      match st:
        case None{}:
          +l = List.length(&2, U32, rest)
          +dw = Nat.double(Wd(ds, 0n))
          N.le_succ(dw, 1n+l, N.le_succ(dw, l, go.le(rest, None{}, ds, e)))
        case Some{+s}:
          +w1 = Nat.double(Wm(C.Book.read.token(U32.to_nat(tag), s, b)))
          +w0 = Nat.double(Ws(s, 0n))
          +l = List.length(&2, U32, rest)
          +ih = go.le(rest, C.Book.read.token(U32.to_nat(tag), s, b), ds, e)
          +hs = N.double_mono(Wm(C.Book.read.token(U32.to_nat(tag), s, b)), 1n+Ws(s, 0n), token.le(U32.to_nat(tag), s, b))
          +h = N.le_trans(Nat.double(Wd(ds, 0n)), Nat.add(w1, l), 2n+Nat.add(w0, l), ih,
            N.add_mono(w1, 2n+w0, l, l, hs, N.le_refl(l)))
          N.le_rw_r(Nat.double(Wd(ds, 0n)), 2n+Nat.add(w0, l), Nat.add(w0, 2n+l), add_two(w0, l), h)

# a book read from p has at most |p| / 2 nodes
def read.le(+p: List<&2, U32>, +ds: List<&2, C.Def>, rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>}) ->
  N.Le(Nat.double(Wd(ds, 0n)), List.length(&2, U32, p)):
  go.le(p, Some{Nil{}}, ds, rd)

# The image's length
# ------------------

# the 363 cells of the prefix
def prefix_len(+main: U32, +acc: List<&2, C.Cir.Cell>) ->
  {List.length(&2, C.Cir.Cell, C.Img.prefix(main, acc)) == Nat.add(363n, List.length(&2, C.Cir.Cell, acc)) : Nat}:
  {==}

# the nodes of the bodies of ds, plus n
def Bl(ds: List<&2, C.Def>, n: Nat) -> Nat:
  match ds:
    case Nil{}:
      n
    case Con{C.Def{_, _, v, _}, rest}:
      Nsz(v, Bl(rest, n))

# the cells of the bodies: one per node
def bodies_len(ds: List<&2, C.Def>, +ks: List<&2, List<&2, U32>>, +es: List<&2, C.Img.Def>, +at: U32) ->
  {List.length(&2, C.Cir.Cell, C.Img.bodies(ds, ks, es, at)) == Bl(ds, 0n) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case Con{C.Def{+kk, +TT, +v, +oo}, +rest}:
      %bodies_len(rest, ks, es, U32.add(at, C.Img.size(v))) : {List.length(&2, C.Cir.Cell, C.Img.bodies(Con{C.Def{kk, TT, v, oo}, rest}, ks, es, at)) == Nsz(v, _) : Nat}
      term_len(v, ks, es, at, C.Img.bodies(rest, ks, es, U32.add(at, C.Img.size(v))))

# the cells of the image: 363, then one per node of the bodies
def cells_len(+ds: List<&2, C.Def>) -> {List.length(&2, C.Cir.Cell, C.Img.cells(ds)) == Nat.add(363n, Bl(ds, 0n)) : Nat}:
  +ks = C.Img.known(C.Img.names.defs(ds))
  +es = C.Img.defs(ds, C.I.book())
  %bodies_len(ds, ks, es, C.I.book()) : {List.length(&2, C.Cir.Cell, C.Img.cells(ds)) == Nat.add(363n, _) : Nat}
  prefix_len(C.Img.ref(es, C.Program.name.main()), C.Img.bodies(ds, ks, es, C.I.book()))

# a node of a body moves through the bodies
def bl_swap(ds: List<&2, C.Def>, +v: C.Term, +a: Nat) -> {Bl(ds, Nsz(v, a)) == Nsz(v, Bl(ds, a)) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case Con{C.Def{_, _, +w, _}, +rest}:
      %Nsz_swap(v, w, Bl(rest, a)) : {Nsz(w, Bl(rest, Nsz(v, a))) == _ : Nat}
      %bl_swap(rest, v, a) : {Nsz(w, Bl(rest, Nsz(v, a))) == Nsz(w, _) : Nat}
      {==}

# the nodes of the bodies are at most the nodes of the defs
def blwd(ds: List<&2, C.Def>, +a: Nat, +b: Nat, h: N.Le(a, b)) -> N.Le(Bl(ds, a), Wd(ds, b)):
  match ds:
    case Nil{}:
      h
    case Con{C.Def{_, +T, +v, _}, +rest}:
      %bl_swap(rest, v, a) : N.Le(_, Wd(rest, Nsz(T, Nsz(v, b))))
      blwd(rest, Nsz(v, a), Nsz(T, Nsz(v, b)),
        N.le_trans(Nsz(v, a), Nsz(v, b), Nsz(T, Nsz(v, b)), Nsz_mono(v, a, b, h), Nsz_ge(T, Nsz(v, b))))

# the U32 count of a list is at most its length
def enc_len_le(xs: List<&2, C.Cir.Cell>) -> N.Le(U32.to_nat(C.Wasm.encode.len(C.Cir.Cell, xs)), List.length(&2, C.Cir.Cell, xs)):
  match xs:
    case Nil{}:
      Unit{}
    case Con{_, +rest}:
      N.le_trans(U32.to_nat(U32.inc(C.Wasm.encode.len(C.Cir.Cell, rest))), 1n+U32.to_nat(C.Wasm.encode.len(C.Cir.Cell, rest)),
        1n+List.length(&2, C.Cir.Cell, rest), N.U32.inc_le(C.Wasm.encode.len(C.Cir.Cell, rest)), enc_len_le(rest))

# Halves and powers
# -----------------

# 2a <= 2b gives a <= b
def half_le(+a: Nat, +b: Nat, h: N.Le(Nat.double(a), Nat.double(b))) -> N.Le(a, b):
  match a:
    case 0n:
      N.le_zero(b)
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(N.Le(1n+p, 0n), h)
        case 1n+q:
          half_le(p, q, h)

# 1 + 2a <= 2b gives 1 + a <= b
def half_lt(+a: Nat, +b: Nat, h: N.Le(1n+Nat.double(a), Nat.double(b))) -> N.Le(1n+a, b):
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd(N.Le(1n, 0n), h)
        case 1n+q:
          N.le_zero(q)
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(N.Le(2n+p, 0n), h)
        case 1n+q:
          half_lt(p, q, h)

# y <= 2y
def le_double(+y: Nat) -> N.Le(y, Nat.double(y)):
  match y:
    case 0n:
      Unit{}
    case 1n+p:
      N.le_succ(p, Nat.double(p), le_double(p))

# x <= 2^k x
def D_ge(+k: Nat, +x: Nat) -> N.Le(x, N.D(k, x)):
  match k:
    case 0n:
      N.le_refl(x)
    case 1n+q:
      N.le_trans(x, N.D(q, x), Nat.double(N.D(q, x)), D_ge(q, x), le_double(N.D(q, x)))

# 67108864 is the word of bit 26
def lit_M2() -> {67108864 == U32{N.bit(32n, 26n)} : U32}:
  {==}

# 67108864 = 2^26
def val_M2() -> {U32.to_nat(67108864) == N.D(26n, 1n) : Nat}:
  %Equal.sym(U32, 67108864, U32{N.bit(32n, 26n)}, lit_M2()) : {U32.to_nat(_) == N.D(26n, 1n) : Nat}
  %Equal.sym(Nat, U32.to_nat(U32{N.bit(32n, 26n)}), Word.to_nat(32n, N.bit(32n, 26n)), N.u32_to_nat(N.bit(32n, 26n))) : {_ == N.D(26n, 1n) : Nat}
  N.bit_val(32n, 26n, Unit{})

# The counter of Img.small
# ------------------------

# an increment below a bigger word adds 1
def Word.inc_ge(+n: Nat, w: Word(n), w2: Word(n), h: N.Le(1n+Word.to_nat(n, w), Word.to_nat(n, w2))) ->
  N.Le(1n+Word.to_nat(n, w), Word.to_nat(n, Word.inc(n, w))):
  match n:
    case 0n:
      match w w2:
        case WNil{} WNil{}:
          h
    case 1n+p:
      match w w2:
        case WCon{False{}, +t} WCon{False{}, _}:
          N.le_refl(1n+Nat.double(Word.to_nat(p, t)))
        case WCon{False{}, +t} WCon{True{}, _}:
          N.le_refl(1n+Nat.double(Word.to_nat(p, t)))
        case WCon{True{}, +t} WCon{False{}, +t2}:
          N.double_mono(1n+Word.to_nat(p, t), Word.to_nat(p, Word.inc(p, t)),
            Word.inc_ge(p, t, t2, half_le(1n+Word.to_nat(p, t), Word.to_nat(p, t2), h)))
        case WCon{True{}, +t} WCon{True{}, +t2}:
          N.double_mono(1n+Word.to_nat(p, t), Word.to_nat(p, Word.inc(p, t)),
            Word.inc_ge(p, t, t2, half_lt(Word.to_nat(p, t), Word.to_nat(p, t2), h)))

def U32.inc_ge(a: U32, b: U32, h: N.Le(1n+U32.to_nat(a), U32.to_nat(b))) -> N.Le(1n+U32.to_nat(a), U32.to_nat(U32.inc(a))):
  match a b:
    case U32{x} U32{y}:
      Word.inc_ge(32n, x, y, h)

# a comparison other than EQ, with x <= y, gives x < y
def lt_of_ne(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), ne: {Cmp.is_eq(c) == False{} : Bool}, le: N.Le(x, y)) -> N.Le(1n+x, y):
  match c:
    case LT{}:
      r
    case EQ{}:
      Empty.absurd(N.Le(1n+x, y), N.true_ne_false(ne))
    case GT{}:
      Empty.absurd(N.Le(1n+x, y), N.not_succ_le(y, N.le_trans(1n+y, x, y, r, le)))

# one step of Img.small, for any limit M, by the branch of U32.is_eq(n, M)
def small.step2(
  b: Bool, +n: U32, +M: U32, +h: U32, +rest: List<&2, U32>,
  eb: {U32.is_eq(n, M) == b : Bool},
  e: {C.Img.small.if(b, u => C.Img.small(rest, U32.inc(n))) == True{} : Bool},
  hn: N.Le(U32.to_nat(n), U32.to_nat(M)),
  ih: {C.Img.small(rest, U32.inc(n)) == True{} : Bool} -> N.Le(U32.to_nat(U32.inc(n)), U32.to_nat(M)) ->
    N.Le(Nat.add(U32.to_nat(U32.inc(n)), List.length(&2, U32, rest)), U32.to_nat(M))
) -> N.Le(Nat.add(U32.to_nat(n), List.length(&2, U32, Con{h, rest})), U32.to_nat(M)):
  match b:
    case True{}:
      Empty.absurd(N.Le(Nat.add(U32.to_nat(n), List.length(&2, U32, Con{h, rest})), U32.to_nat(M)), N.false_ne_true(e))
    case False{}:
      +x = U32.to_nat(n)
      +m = U32.to_nat(M)
      +l = List.length(&2, U32, rest)
      +lt = lt_of_ne(U32.cmp(n, M), x, m, N.U32.rel(n, M), eb, hn)
      +hi = U32.inc_ge(n, M, lt)
      +hn2 = N.le_trans(U32.to_nat(U32.inc(n)), 1n+x, m, N.U32.inc_le(n), lt)
      N.le_rw_l(1n+Nat.add(x, l), Nat.add(x, 1n+l), m, Equal.sym(Nat, Nat.add(x, 1n+l), 1n+Nat.add(x, l), N.add_succ_r(x, l)),
        N.le_trans(1n+Nat.add(x, l), Nat.add(U32.to_nat(U32.inc(n)), l), m,
          N.add_mono(1n+x, U32.to_nat(U32.inc(n)), l, l, hi, N.le_refl(l)), ih(e, hn2)))

# Img.small(xs, n) true, n <= M = 67108863: n + |xs| <= M
def small.le(xs: List<&2, U32>, +n: U32, +M: U32, +eM: {M == 67108863 : U32}, hn: N.Le(U32.to_nat(n), U32.to_nat(M)),
  e: {C.Img.small(xs, n) == True{} : Bool}
) -> N.Le(Nat.add(U32.to_nat(n), List.length(&2, U32, xs)), U32.to_nat(M)):
  match xs:
    case Nil{}:
      %Equal.sym(Nat, Nat.add(U32.to_nat(n), 0n), U32.to_nat(n), N.add_zero(U32.to_nat(n))) : N.Le(_, U32.to_nat(M))
      hn
    case Con{+h, +rest}:
      +eb = {(%eM : {U32.is_eq(n, M) == U32.is_eq(n, _) : Bool}; {==}) : {U32.is_eq(n, M) == U32.is_eq(n, 67108863) : Bool}}
      small.step2(U32.is_eq(n, 67108863), n, M, h, rest, eb, e, hn, e2 => h2 => small.le(rest, U32.inc(n), M, eM, h2, e2))

# The image
# ---------

# x < y makes the comparison LT
def lt_true(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(1n+x, y)) -> {Cmp.is_lt(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(x, N.le_rw_r(1n+x, y, x, Equal.sym(Nat, x, y, r), h)))
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(y, N.le_trans(1n+y, x, y, r, N.weaken(x, y, h))))

# a < c rewritten on the left
def lt_rw_l(-a: Nat, -b: Nat, -c: Nat, e: {a == b : Nat}, h: N.Le(1n+a, c)) -> N.Le(1n+b, c):
  %e : N.Le(1n+_, c)
  h

# 0 is at most every U32
def le_zero_u32(+M: U32) -> N.Le(U32.to_nat(0), U32.to_nat(M)):
  N.le_zero(U32.to_nat(M))

# 2^(1 + q) x = 2 (2^q x)
def D_succ(+q: Nat, +x: Nat) -> {N.D(1n+q, x) == Nat.double(N.D(q, x)) : Nat}:
  {==}

# a book of at most m bytes, 1 + m = 2h, 363 <= h, has an image of fewer
# than 2h cells (m and h stay variables: the checker never expands them)
def core.len(+p: List<&2, U32>, +ds: List<&2, C.Def>, +m: Nat, +h25: Nat,
  rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  hl: N.Le(List.length(&2, U32, p), m),
  vm: {1n+m == Nat.double(h25) : Nat},
  h363: N.Le(363n, h25)
) -> N.Le(1n+List.length(&2, C.Cir.Cell, C.Img.cells(ds)), Nat.double(h25)):
  +l = List.length(&2, U32, p)
  +w = Wd(ds, 0n)
  +b = Bl(ds, 0n)
  +cells = C.Img.cells(ds)
  +h2 = N.le_trans(Nat.double(w), l, m, read.le(p, ds, rd), hl)
  +h3 = N.le_rw_r(1n+Nat.double(w), 1n+m, Nat.double(h25), vm, h2)
  +h4 = half_lt(w, h25, h3)
  +h5 = N.le_trans(1n+b, 1n+w, h25, blwd(ds, 0n, 0n, Unit{}), h4)
  +h6 = N.add_mono(363n, h25, 1n+b, h25, h363, h5)
  +h7 = N.le_rw_r(Nat.add(363n, 1n+b), Nat.add(h25, h25), Nat.double(h25), add_self(h25), h6)
  +h8 = N.le_rw_l(Nat.add(363n, 1n+b), 1n+Nat.add(363n, b), Nat.double(h25), N.add_succ_r(363n, b), h7)
  lt_rw_l(Nat.add(363n, b), List.length(&2, C.Cir.Cell, cells), Nat.double(h25),
    Equal.sym(Nat, List.length(&2, C.Cir.Cell, cells), Nat.add(363n, b), cells_len(ds)), h8)

# the same, for the U32 count of the cells
def core(+p: List<&2, U32>, +ds: List<&2, C.Def>, +m: Nat, +h25: Nat,
  rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  hl: N.Le(List.length(&2, U32, p), m),
  vm: {1n+m == Nat.double(h25) : Nat},
  h363: N.Le(363n, h25)
) -> N.Le(1n+U32.to_nat(C.Wasm.encode.len(C.Cir.Cell, C.Img.cells(ds))), Nat.double(h25)):
  +cells = C.Img.cells(ds)
  +len = C.Wasm.encode.len(C.Cir.Cell, cells)
  N.le_trans(1n+U32.to_nat(len), 1n+List.length(&2, C.Cir.Cell, cells), Nat.double(h25), enc_len_le(cells),
    core.len(p, ds, m, h25, rd, hl, vm, h363))

# the image of a book of fewer than 2^26 bytes has fewer than 2^26 cells
def img.small.proof(
  +p: List<&2, U32>, +ds: List<&2, C.Def>,
  rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  small: {C.Img.small(p, 0) == True{} : Bool}
) -> {U32.is_lt(C.Wasm.encode.len(C.Cir.Cell, C.Img.cells(ds)), 67108864) == True{} : Bool}:
  +l = List.length(&2, U32, p)
  +m = U32.to_nat(67108863)
  +d9 = N.D(9n, 1n)
  +h25 = N.D(25n, 1n)
  +h26 = N.D(26n, 1n)
  +len = C.Wasm.encode.len(C.Cir.Cell, C.Img.cells(ds))
  +h0 = small.le(p, 0, 67108863, {==}, le_zero_u32(67108863), small)
  +h1 = N.le_rw_l(Nat.add(U32.to_nat(0), l), l, m, N.zero_add(l), h0)
  +vm = Equal.trans(Nat, 1n+m, h26, Nat.double(h25), N.val_M(), D_succ(25n, 1n))
  +h363 = N.le_trans(363n, d9, h25, Unit{},
    N.le_rw_r(d9, N.D(16n, d9), h25, N.D_add(16n, 9n, 25n, 1n, {==}), D_ge(16n, d9)))
  +h10 = core(p, ds, m, h25, rd, h1, vm, h363)
  +e = Equal.trans(Nat, Nat.double(h25), h26, U32.to_nat(67108864),
    Equal.sym(Nat, h26, Nat.double(h25), D_succ(25n, 1n)), Equal.sym(Nat, U32.to_nat(67108864), h26, val_M2()))
  +h11 = N.le_rw_r(1n+U32.to_nat(len), Nat.double(h25), U32.to_nat(67108864), e, h10)
  lt_true(U32.cmp(len, 67108864), U32.to_nat(len), U32.to_nat(67108864), N.U32.rel(len, 67108864), h11)

# 1 + a <= b makes a < b
def lt_nat(+a: Nat, +b: Nat, h: N.Le(1n+a, b)) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, h)
        case 1n+q:
          {==}
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, h)
        case 1n+q:
          lt_nat(p, q, h)

# the image of a book of fewer than 2^26 bytes has fewer than 2^26 cells,
# counted as a Nat
def img.small.nat(
  +p: List<&2, U32>, +ds: List<&2, C.Def>,
  rd: {C.Book.read(p) == Some{ds} : Maybe<List<&2, C.Def>>},
  small: {C.Img.small(p, 0) == True{} : Bool}
) -> {Nat.is_lt(List.length(&2, C.Cir.Cell, C.Img.cells(ds)), U32.to_nat(67108864)) == True{} : Bool}:
  +l = List.length(&2, U32, p)
  +m = U32.to_nat(67108863)
  +d9 = N.D(9n, 1n)
  +h25 = N.D(25n, 1n)
  +h26 = N.D(26n, 1n)
  +n = List.length(&2, C.Cir.Cell, C.Img.cells(ds))
  +h0 = small.le(p, 0, 67108863, {==}, le_zero_u32(67108863), small)
  +h1 = N.le_rw_l(Nat.add(U32.to_nat(0), l), l, m, N.zero_add(l), h0)
  +vm = Equal.trans(Nat, 1n+m, h26, Nat.double(h25), N.val_M(), D_succ(25n, 1n))
  +h363 = N.le_trans(363n, d9, h25, Unit{},
    N.le_rw_r(d9, N.D(16n, d9), h25, N.D_add(16n, 9n, 25n, 1n, {==}), D_ge(16n, d9)))
  +h10 = core.len(p, ds, m, h25, rd, h1, vm, h363)
  +e = Equal.trans(Nat, Nat.double(h25), h26, U32.to_nat(67108864),
    Equal.sym(Nat, h26, Nat.double(h25), D_succ(25n, 1n)), Equal.sym(Nat, U32.to_nat(67108864), h26, val_M2()))
  +h11 = N.le_rw_r(1n+n, Nat.double(h25), U32.to_nat(67108864), e, h10)
  lt_nat(n, U32.to_nat(67108864), h11)
