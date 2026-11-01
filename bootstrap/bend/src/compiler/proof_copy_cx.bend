# compiler: counterexamples to layer B's copy.post, by runs
# ===========================================================
#
# Small states, run by the checker, that show what M.copy does on them.
# Each state holds what HS, Ag and the other premises of copy.post read of
# the machine's cells (the image's cells but the table's rows that the runs
# read are left out: the runs never read them).
#
# A. A borrowed cell held only by a cell of the pend list (HS's Held counts
#    the pend list's pointers). p = 400 is in the pend list, a Typ whose part
#    is c = 401, a Rfl of count 1; c is the borrowed source (register 13).
#    The copy's first M.alloc (its root) takes p and drops c's count to 0: c
#    goes to the pend list. The copy then shares c (M.inc), which bumps c's
#    link field: the result r = c is in the pend list (p -> c -> 1), so
#    CopyQ's HS (PendOK: Ptr(c) = 0, yet c is an owned root) cannot hold.
#    M.alloc alone (alloc.post) already loses Held of c: c is pended with
#    Ptr 0.
#
# B. A local of the chain, not OWNED, whose term is held only by a cell of
#    the pend list (Ag says nothing of its count). x = 401 is the term of the
#    K.arg a = 402; the source is Var 0 (c = 403, owned by register 0). The
#    root's M.alloc pends x; the copy puts in x, which ends in the pend list
#    (p -> x -> 1): Ag's {Mem(ps2, x) == False} fails.
#
# C. r = 39 (croot): M.copy.end writes K.root (45) into field 0 of the
#    result. r = 3 (pend): register r ends with the root, tag 45. r = 64: a
#    trap. src = 39: the root's part is the root itself.
#
# D. A local whose term has a free variable near 2^32 (CopyPost, as fixed,
#    still false). The source c = 400 is Lam{Q0, Var 1} (fv 1; its part 401
#    is Var 1, fv 2), owned by register 0 and borrowed in register 13; the
#    chain cenv = 402 is one K.arg, OWNED (4096), last, whose term 403 is
#    Var 4294967295 with fv fv_max (a Var's term may be OWNED). HS, Held, Ag
#    and the registers' premises hold (counts: 400 by the root, 401 by 400,
#    403 by the OWNED 402; no pend list; no frames). Term.subst gives
#    Lam{Q0, Term.shift(Var 4294967295, 1n, 0n)} = Lam{Q0, Var 4294967296},
#    which no cell stands for (Is of a Var asks to_nat(field 2) == i), but
#    the run ends in next{_} (4 cells, room to spare): M.shift's M.var adds
#    samt = 1 to 4294967295 as a U32, so the result 405 is Lam{Q0, Var 0}
#    (cell 407, field 2 = 0), and CopyQ cannot hold. The run makes no other
#    mistake: a premise that bounds the locals' variables (each local's term
#    below 2^25, the book's own bound) makes the sum fit.
import Base
import ./impl.bend as C

def Cx.z(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{0, Cx.z(p)}

# the table's rows that the runs read: Var 0, Typ 4, Prj 11, Rfl 17
def Cx.tbl() -> C.Cir.Cells:
  C.Cir.Cells.set(
    C.Cir.Cells.set(
      C.Cir.Cells.set(C.Cir.Cells.none{}, 349, C.Cir.Cell{0, 0, 1, 0, 1}),
      356,
      C.Cir.Cell{0, 0, 1, 0, 1}
    ),
    362,
    C.Cir.Cell{0, 0, 0, 0, 1}
  )

def Cx.st(regs: List<&2, U32>, m: C.Cir.Cells, nx: U32) -> C.Cir.State:
  C.Cir.State{regs, m, nx, 400, 363, 1, 1, Nil{}, Nil{}, 0}

def Cx.reg(o: C.Cir.Out, r: Nat) -> Maybe<&2, U32>:
  match o:
    case C.Cir.Out.next{C.Cir.State{regs, _, _, _, _, _, _, _, _, _}}:
      List.get(&2, U32, regs, r)
    case _:
      None{}

def Cx.fd(o: C.Cir.Out, k: Nat, c: U32) -> U32:
  match o:
    case C.Cir.Out.next{C.Cir.State{_, m, _, _, _, _, _, _, _, _}}:
      C.Cir.Cell.get(k, C.Cir.Cells.get(m, c))
    case _:
      77777

def Cx.trap(o: C.Cir.Out) -> Bool:
  match o:
    case C.Cir.Out.trap{}:
      True{}
    case _:
      False{}

# A
# -

# p = 400: Typ (4), in the pend list (link 0), its part c; c = 401: Rfl
# (17), fv 0, count 1
def A.m() -> C.Cir.Cells:
  C.Cir.Cells.set(
    C.Cir.Cells.set(Cx.tbl(), 400, C.Cir.Cell{4, 0, 401, 0, 0}),
    401,
    C.Cir.Cell{17, 1, 0, 0, 0}
  )

# src = 13 holds c, pend = p, cenv = 0, clen = 0
def A.regs() -> List<&2, U32>:
  List.set(&2, U32, List.set(&2, U32, Cx.z(64n), 13n, 401), 3n, 400)

def A.copy() -> C.Cir.Out:
  C.Cir.exec(4n, C.M.copy(15n, 13n), Cx.st(A.regs(), A.m(), 402))

# the result is c; pend is the root p, then c, then cell 1
def A.r15() -> {Cx.reg(A.copy(), 15n) == Some{401}: Maybe<&2, U32>}:
  {==}

def A.r3() -> {Cx.reg(A.copy(), 3n) == Some{400}: Maybe<&2, U32>}:
  {==}

def A.link_p() -> {Cx.fd(A.copy(), 1n, 400) == 401: U32}:
  {==}

def A.link_c() -> {Cx.fd(A.copy(), 1n, 401) == 1: U32}:
  {==}

# M.alloc alone: c is pended (pend = c, its link 0), p is taken
def A.alloc() -> C.Cir.Out:
  C.Cir.exec(1n, C.M.alloc(15n), Cx.st(A.regs(), A.m(), 402))

def A.alloc_r3() -> {Cx.reg(A.alloc(), 3n) == Some{401}: Maybe<&2, U32>}:
  {==}

def A.alloc_r15() -> {Cx.reg(A.alloc(), 15n) == Some{400}: Maybe<&2, U32>}:
  {==}

def A.alloc_cnt() -> {Cx.fd(A.alloc(), 1n, 401) == 0: U32}:
  {==}

# B
# -

# p = 400: Typ in the pend list, part x; x = 401: Rfl, count 1; a = 402: a
# K.arg (41), not OWNED, quantity 0, term x, last; c = 403: Var 0, fv 1,
# count 1 (register 0 owns it)
def B.m() -> C.Cir.Cells:
  C.Cir.Cells.set(
    C.Cir.Cells.set(
      C.Cir.Cells.set(
        C.Cir.Cells.set(Cx.tbl(), 400, C.Cir.Cell{4, 0, 401, 0, 0}),
        401,
        C.Cir.Cell{17, 1, 0, 0, 0}
      ),
      402,
      C.Cir.Cell{41, 0, 401, 0, 0}
    ),
    403,
    C.Cir.Cell{8192, 1, 0, 0, 0}
  )

def B.regs() -> List<&2, U32>:
  List.set(
    &2,
    U32,
    List.set(
      &2,
      U32,
      List.set(
        &2,
        U32,
        List.set(&2, U32, List.set(&2, U32, Cx.z(64n), 0n, 403), 13n, 403),
        3n,
        400
      ),
      36n,
      402
    ),
    37n,
    1
  )

def B.copy() -> C.Cir.Out:
  C.Cir.exec(4n, C.M.copy(15n, 13n), Cx.st(B.regs(), B.m(), 404))

def B.r15() -> {Cx.reg(B.copy(), 15n) == Some{401}: Maybe<&2, U32>}:
  {==}

def B.r3() -> {Cx.reg(B.copy(), 3n) == Some{400}: Maybe<&2, U32>}:
  {==}

def B.link_p() -> {Cx.fd(B.copy(), 1n, 400) == 401: U32}:
  {==}

def B.link_x() -> {Cx.fd(B.copy(), 1n, 401) == 1: U32}:
  {==}

# C
# -

# c = 400: Rfl, count 1, owned by register 0; pend empty; a new root 401
def C2.m() -> C.Cir.Cells:
  C.Cir.Cells.set(Cx.tbl(), 400, C.Cir.Cell{17, 1, 0, 0, 0})

def C2.regs(+src: Nat) -> List<&2, U32>:
  List.set(&2, U32, List.set(&2, U32, Cx.z(64n), 0n, 400), src, 400)

def C2.copy(r: Nat, +src: Nat) -> C.Cir.Out:
  C.Cir.exec(4n, C.M.copy(r, src), Cx.st(C2.regs(src), C2.m(), 401))

# r = 39: the result is c, whose field 0 is now K.root
def C2.r39_reg() -> {Cx.reg(C2.copy(39n, 13n), 39n) == Some{400}: Maybe<&2, U32>}:
  {==}

def C2.r39_tag() -> {Cx.fd(C2.copy(39n, 13n), 0n, 400) == 45: U32}:
  {==}

# r = 3: register 3 ends with the root, 401, of tag K.root
def C2.r3_reg() -> {Cx.reg(C2.copy(3n, 13n), 3n) == Some{401}: Maybe<&2, U32>}:
  {==}

def C2.r3_tag() -> {Cx.fd(C2.copy(3n, 13n), 0n, 401) == 45: U32}:
  {==}

# r = 64: a trap
def C2.r64() -> {Cx.trap(C2.copy(64n, 13n)) == True{}: Bool}:
  {==}

# src = 39: the result is the root itself, of tag K.root
def C2.s39_reg() -> {Cx.reg(C2.copy(15n, 39n), 15n) == Some{401}: Maybe<&2, U32>}:
  {==}

def C2.s39_tag() -> {Cx.fd(C2.copy(15n, 39n), 0n, 401) == 45: U32}:
  {==}

# D
# -

# the table's row of Lam (7) too
def D.tbl() -> C.Cir.Cells:
  C.Cir.Cells.set(Cx.tbl(), 352, C.Cir.Cell{0, 0, 1, 1, 1})

# c = 400: Lam (7), fv 1, count 1, part 401; 401: Var 1, fv 2, count 1;
# a = 402: K.arg (41), OWNED, last, term 403; 403: Var 4294967295, fv fv_max
# (524287 << 13 = 4294959104), count 1
def D.m() -> C.Cir.Cells:
  C.Cir.Cells.set(
    C.Cir.Cells.set(
      C.Cir.Cells.set(
        C.Cir.Cells.set(D.tbl(), 400, C.Cir.Cell{8199, 1, 401, 0, 0}),
        401,
        C.Cir.Cell{16384, 1, 1, 0, 0}
      ),
      402,
      C.Cir.Cell{4137, 0, 403, 0, 0}
    ),
    403,
    C.Cir.Cell{4294959104, 1, 4294967295, 0, 0}
  )

# focus 0 and src 13 hold c, pend 0, cenv 402, clen 1
def D.regs() -> List<&2, U32>:
  List.set(
    &2,
    U32,
    List.set(
      &2,
      U32,
      List.set(&2, U32, List.set(&2, U32, Cx.z(64n), 0n, 400), 13n, 400),
      36n,
      402
    ),
    37n,
    1
  )

def D.copy() -> C.Cir.Out:
  C.Cir.exec(8n, C.M.copy(15n, 13n), Cx.st(D.regs(), D.m(), 404))

# the run ends with a state: register 15 holds 405
def D.r15() -> {Cx.reg(D.copy(), 15n) == Some{405}: Maybe<&2, U32>}:
  {==}

# 405 is a Lam (tag 7, no fv) whose part is 407
def D.lam_f0() -> {Cx.fd(D.copy(), 0n, 405) == 7: U32}:
  {==}

def D.lam_f2() -> {Cx.fd(D.copy(), 2n, 405) == 407: U32}:
  {==}

# 407 is Var 0 (tag 0, fv 1): the shift's 4294967295 + 1 wrapped
def D.var_f0() -> {Cx.fd(D.copy(), 0n, 407) == 8192: U32}:
  {==}

def D.var_f2() -> {Cx.fd(D.copy(), 2n, 407) == 0: U32}:
  {==}

# what Term.subst gives, for the local Var i = 1 + p: Lam{Q0, Var i + 1}; for
# i = 4294967295, Var 4294967296, of which no cell stands
def D.subst(+p: Nat) -> {C.Term.subst(C.Term.Lam{C.Quan.Q0{}, C.Term.Var{1n}}, [C.Term.Var{1n+p}], 0n) ==
  C.Term.Lam{C.Quan.Q0{}, C.Term.Var{Nat.add(1n+p, 1n)}} : C.Term}:
  {==}
