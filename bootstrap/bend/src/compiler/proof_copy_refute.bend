# compiler: copy.post and alloc.post, as layer B states them, are false
# ====================================================================
#
# A state of the machine with all of HS (the image's table and labels,
# ImgOK; no def), in which a borrowed cell c (401, a Rfl of count 1) is held
# only by a cell of the pend list (p = 400, a Typ whose part is c): Held
# counts the pend list's pointers. Each of copy.post and alloc.post, applied
# to it, gives Empty:
#
# - alloc.post: M.alloc takes p and drops c's count to 0, so c joins the
#   pend list with no pointer, and Held of c is lost.
# - copy.post (r = 15, src = 13, no locals; its conclusion is CopyPost of
#   proof_mach_defs.bend): the root's M.alloc does the same; the copy then
#   shares c (M.inc bumps its link field): the result c is the second cell of
#   the pend list (p -> c -> 1), while it is an owned root, against PendOK.
#
# A second state (RB.*, at the end) refutes copy.post with the source held by
# an owned root: there the term of a local that is not OWNED is the cell
# that only the pend list holds (Ag says nothing of who holds it).
import Base
import ./impl.bend as C
import ./proof_mach_defs.bend as PM
import ./proof_need.bend as N

# The state
# ---------
def R.z(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{0, R.z(p)}

def R.rows(rs: List<&2, C.Cir.Cell>, m: C.Cir.Cells, +at: U32) -> C.Cir.Cells:
  match rs:
    case Nil{}:
      m
    case Con{x, rest}:
      R.rows(rest, C.Cir.Cells.set(m, at, x), U32.inc(at))

# the rows of Tbl.rows(), as cells
def R.tbl() -> List<&2, C.Cir.Cell>:
  [
    C.Cir.Cell{0, 0, 0, 0, 0},
    C.Cir.Cell{0, 0, 0, 0, 0},
    C.Cir.Cell{0, 0, 3, 0, 0},
    C.Cir.Cell{0, 0, 3, 4, 0},
    C.Cir.Cell{0, 0, 1, 0, 1},
    C.Cir.Cell{0, 0, 3, 0, 0},
    C.Cir.Cell{0, 0, 3, 4, 1},
    C.Cir.Cell{0, 0, 1, 1, 1},
    C.Cir.Cell{0, 0, 3, 0, 0},
    C.Cir.Cell{0, 0, 3, 4, 1},
    C.Cir.Cell{0, 0, 3, 0, 0},
    C.Cir.Cell{0, 0, 1, 0, 1},
    C.Cir.Cell{0, 0, 0, 0, 1},
    C.Cir.Cell{0, 0, 0, 0, 1},
    C.Cir.Cell{0, 0, 6, 0, 1},
    C.Cir.Cell{0, 0, 0, 0, 1},
    C.Cir.Cell{0, 0, 7, 0, 1},
    C.Cir.Cell{0, 0, 0, 0, 1},
    C.Cir.Cell{0, 0, 7, 8, 0}
  ]

# the image: the table by tag from 345 (Img.table), the labels of Q0, Q1 and
# Q2 in cells 9 to 11 (STATIC Lab cells of the names 8, 9 and 10)
def R.img() -> C.Cir.Cells:
  C.Cir.Cells.set(
    C.Cir.Cells.set(
      C.Cir.Cells.set(R.rows(R.tbl(), C.Cir.Cells.none{}, 345), 9, C.Cir.Cell{1037, 0, 8, 0, 0}),
      10,
      C.Cir.Cell{1037, 0, 9, 0, 0}
    ),
    11,
    C.Cir.Cell{1037, 0, 10, 0, 0}
  )

def R.ks() -> List<&2, List<&2, U32>>:
  C.Img.known(Nil{})

# p = 400: Typ (4), the pend list's only cell, its part c; c = 401: Rfl (17),
# fv 0, count 1; the machine's cells are 400 and 401
def R.m() -> C.Cir.Cells:
  C.Cir.Cells.set(
    C.Cir.Cells.set(R.img(), 400, C.Cir.Cell{4, 0, 401, 0, 0}),
    401,
    C.Cir.Cell{17, 1, 0, 0, 0}
  )

# register 13 holds c, pend holds p, cenv and clen 0
def R.regs() -> List<&2, U32>:
  List.set(&2, U32, List.set(&2, U32, R.z(64n), 13n, 401), 3n, 400)

def R.st() -> C.Cir.State:
  C.Cir.State{R.regs(), R.m(), 402, 400, 363, 1, 1, Nil{}, Nil{}, 0}

def R.bs() -> List<&2, PM.Rt>:
  [PM.Rt{401, C.Term.Rfl{}}]

# HS holds, with no owned root, c borrowed, no frame
def R.hs() -> PM.HS(
  Nil{},
  R.ks(),
  Nil{},
  R.m(),
  402,
  400,
  363,
  Nil{},
  R.bs(),
  Nil{},
  0,
  400,
  [400]
):
  Tuple{
    Unit{},
    Tuple{
      Tuple{Tuple{{==}, Tuple{{==}, Tuple{{==}, Tuple{{==}, Tuple{{==}, {==}}}}}}, Unit{}},
      Tuple{
        Tuple{{==}, Unit{}},
        Tuple{
          {==},
          Tuple{
            Tuple{
              Tuple{{==}, Tuple{{==}, {==}}},
              Tuple{Tuple{{==}, Tuple{{==}, Tuple{{==}, Unit{}}}}, Tuple{{==}, Tuple{{==}, {==}}}}
            },
            Tuple{
              Tuple{
                {==},
                Tuple{
                  {==},
                  Tuple{
                    {==},
                    Tuple{
                      {==},
                      Tuple{
                        {==},
                        Tuple{
                          {==},
                          Tuple{
                            {==},
                            Tuple{
                              {==},
                              Tuple{
                                {==},
                                Tuple{
                                  {==},
                                  Tuple{
                                    {==},
                                    Tuple{
                                      {==},
                                      Tuple{
                                        {==},
                                        Tuple{
                                          {==},
                                          Tuple{
                                            {==},
                                            Tuple{
                                              {==},
                                              Tuple{
                                                {==},
                                                Tuple{
                                                  {==},
                                                  Tuple{
                                                    {==},
                                                    Tuple{
                                                      {==},
                                                      Tuple{
                                                        {==},
                                                        Tuple{
                                                          {==},
                                                          Tuple{
                                                            {==},
                                                            Tuple{
                                                              {==},
                                                              Tuple{
                                                                {==},
                                                                Tuple{
                                                                  {==},
                                                                  Tuple{
                                                                    {==},
                                                                    Tuple{
                                                                      {==},
                                                                      Tuple{
                                                                        {==},
                                                                        Tuple{
                                                                          {==},
                                                                          Tuple{
                                                                            {==},
                                                                            Tuple{
                                                                              {==},
                                                                              Tuple{
                                                                                {==},
                                                                                Tuple{
                                                                                  {==},
                                                                                  Tuple{
                                                                                    {==},
                                                                                    Tuple{
                                                                                      {==},
                                                                                      Tuple{
                                                                                        {==},
                                                                                        Tuple{
                                                                                          {==},
                                                                                          Tuple{
                                                                                            {==},
                                                                                            Tuple{
                                                                                              {==},
                                                                                              Tuple{
                                                                                                {
                                                                                                  ==
                                                                                                },
                                                                                                Tuple{
                                                                                                  {
                                                                                                    ==
                                                                                                  },
                                                                                                  Tuple{
                                                                                                    {
                                                                                                      ==
                                                                                                    },
                                                                                                    Tuple{
                                                                                                      {
                                                                                                        ==
                                                                                                      },
                                                                                                      Tuple{
                                                                                                        {
                                                                                                          ==
                                                                                                        },
                                                                                                        Tuple{
                                                                                                          {
                                                                                                            ==
                                                                                                          },
                                                                                                          Tuple{
                                                                                                            {
                                                                                                              ==
                                                                                                            },
                                                                                                            Tuple{
                                                                                                              {
                                                                                                                ==
                                                                                                              },
                                                                                                              Tuple{
                                                                                                                {
                                                                                                                  ==
                                                                                                                },
                                                                                                                Tuple{
                                                                                                                  {
                                                                                                                    ==
                                                                                                                  },
                                                                                                                  Tuple{
                                                                                                                    {
                                                                                                                      ==
                                                                                                                    },
                                                                                                                    Tuple{
                                                                                                                      {
                                                                                                                        ==
                                                                                                                      },
                                                                                                                      Tuple{
                                                                                                                        {
                                                                                                                          ==
                                                                                                                        },
                                                                                                                        Tuple{
                                                                                                                          {
                                                                                                                            ==
                                                                                                                          },
                                                                                                                          Tuple{
                                                                                                                            {
                                                                                                                              ==
                                                                                                                            },
                                                                                                                            Tuple{
                                                                                                                              {
                                                                                                                                ==
                                                                                                                              },
                                                                                                                              Tuple{
                                                                                                                                {
                                                                                                                                  ==
                                                                                                                                },
                                                                                                                                Tuple{
                                                                                                                                  {
                                                                                                                                    ==
                                                                                                                                  },
                                                                                                                                  Tuple{
                                                                                                                                    {
                                                                                                                                      ==
                                                                                                                                    },
                                                                                                                                    Tuple{
                                                                                                                                      {
                                                                                                                                        ==
                                                                                                                                      },
                                                                                                                                      Tuple{
                                                                                                                                        {
                                                                                                                                          ==
                                                                                                                                        },
                                                                                                                                        Tuple{
                                                                                                                                          {
                                                                                                                                            ==
                                                                                                                                          },
                                                                                                                                          Tuple{
                                                                                                                                            {
                                                                                                                                              ==
                                                                                                                                            },
                                                                                                                                            Tuple{
                                                                                                                                              {
                                                                                                                                                ==
                                                                                                                                              },
                                                                                                                                              Tuple{
                                                                                                                                                {
                                                                                                                                                  ==
                                                                                                                                                },
                                                                                                                                                Tuple{
                                                                                                                                                  {
                                                                                                                                                    ==
                                                                                                                                                  },
                                                                                                                                                  Tuple{
                                                                                                                                                    {
                                                                                                                                                      ==
                                                                                                                                                    },
                                                                                                                                                    Tuple{
                                                                                                                                                      {
                                                                                                                                                        ==
                                                                                                                                                      },
                                                                                                                                                      Tuple{
                                                                                                                                                        {
                                                                                                                                                          ==
                                                                                                                                                        },
                                                                                                                                                        Tuple{
                                                                                                                                                          {
                                                                                                                                                            ==
                                                                                                                                                          },
                                                                                                                                                          Tuple{
                                                                                                                                                            {
                                                                                                                                                              ==
                                                                                                                                                            },
                                                                                                                                                            Tuple{
                                                                                                                                                              {
                                                                                                                                                                ==
                                                                                                                                                              },
                                                                                                                                                              Tuple{
                                                                                                                                                                {
                                                                                                                                                                  ==
                                                                                                                                                                },
                                                                                                                                                                Tuple{
                                                                                                                                                                  {
                                                                                                                                                                    ==
                                                                                                                                                                  },
                                                                                                                                                                  Tuple{
                                                                                                                                                                    {
                                                                                                                                                                      ==
                                                                                                                                                                    },
                                                                                                                                                                    Tuple{
                                                                                                                                                                      {
                                                                                                                                                                        ==
                                                                                                                                                                      },
                                                                                                                                                                      Unit{}
                                                                                                                                                                    }
                                                                                                                                                                  }
                                                                                                                                                                }
                                                                                                                                                              }
                                                                                                                                                            }
                                                                                                                                                          }
                                                                                                                                                        }
                                                                                                                                                      }
                                                                                                                                                    }
                                                                                                                                                  }
                                                                                                                                                }
                                                                                                                                              }
                                                                                                                                            }
                                                                                                                                          }
                                                                                                                                        }
                                                                                                                                      }
                                                                                                                                    }
                                                                                                                                  }
                                                                                                                                }
                                                                                                                              }
                                                                                                                            }
                                                                                                                          }
                                                                                                                        }
                                                                                                                      }
                                                                                                                    }
                                                                                                                  }
                                                                                                                }
                                                                                                              }
                                                                                                            }
                                                                                                          }
                                                                                                        }
                                                                                                      }
                                                                                                    }
                                                                                                  }
                                                                                                }
                                                                                              }
                                                                                            }
                                                                                          }
                                                                                        }
                                                                                      }
                                                                                    }
                                                                                  }
                                                                                }
                                                                              }
                                                                            }
                                                                          }
                                                                        }
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              },
              Tuple{
                Unit{},
                Tuple{
                  Tuple{
                    Tuple{{==}, Tuple{{==}, Tuple{{==}, Tuple{{==}, Tuple{{==}, {==}}}}}},
                    Tuple{{==}, {==}}
                  },
                  Tuple{
                    Tuple{
                      Tuple{{==}, Tuple{{==}, Tuple{{==}, Tuple{{==}, Tuple{{==}, {==}}}}}},
                      Tuple{{==}, {==}}
                    },
                    Tuple{
                      Tuple{
                        Tuple{{==}, Tuple{{==}, Tuple{{==}, Tuple{{==}, Tuple{{==}, {==}}}}}},
                        Tuple{{==}, {==}}
                      },
                      Tuple{Tuple{Nil{}, {==}}, Tuple{{==}, {==}}}
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }

# alloc.post is false
# -------------------
def R.alloc() -> C.Cir.Out:
  C.Cir.exec(1n, C.M.alloc(15n), R.st())

def R.alloc.no(
  h: PM.Post(
    False{},
    R.alloc(),
    st2 => PM.P2(
      PM.Same(R.regs(), 400, 363, 1, Nil{}, Nil{}, st2),
      PM.Ex(
        U32,
        z => PM.Ex(
          U32,
          pend2 => PM.Ex(
            List<&2, U32>,
            ps2 => PM.P2(
              PM.Reg(st2, 15n, z),
              PM.P2(
                PM.Reg(st2, 3n, pend2),
                PM.P2(
                  {C.Cir.Cells.get(PM.St.cells(st2), z) == C.Cir.Cell.zero(): C.Cir.Cell},
                  PM.P2(
                    {PM.Own(400, PM.St.next(st2), z) == True{}: Bool},
                    PM.P2(
                      {PM.Mem(ps2, z) == False{}: Bool},
                      PM.P2(
                        {
                          PM.Ptr(
                            Nat.sub(U32.to_nat(PM.St.next(st2)), U32.to_nat(400)),
                            PM.St.cells(st2),
                            400,
                            ps2,
                            Nil{},
                            z
                          )
                            == 0n: Nat
                        },
                        PM.HS(
                          Nil{},
                          R.ks(),
                          Nil{},
                          PM.St.cells(st2),
                          PM.St.next(st2),
                          400,
                          363,
                          Nil{},
                          R.bs(),
                          Nil{},
                          0,
                          pend2,
                          ps2
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    ),
    s => st2 => Empty
  )
) -> Empty:
  match h:
    case Tuple{
      _,
      Tuple{
        _,
        Tuple{
          _,
          Tuple{
            _,
            Tuple{
              _,
              Tuple{
                _,
                Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{Tuple{hh, _}, _}}}}}}}
              }
            }
          }
        }
      }
    }:
      N.false_ne_true(hh)

def alloc.post.false() -> Empty:
  R.alloc.no(
    PM.alloc.post(
      1n,
      Nil{},
      R.ks(),
      Nil{},
      R.regs(),
      R.m(),
      402,
      400,
      363,
      1,
      1,
      Nil{},
      15n,
      Nil{},
      Nil{},
      R.bs(),
      Nil{},
      0,
      400,
      [400],
      R.hs(),
      {==},
      {==},
      {==}
    )
  )

# copy.post is false
# ------------------
def R.copy() -> C.Cir.Out:
  C.Cir.exec(4n, C.M.copy(15n, 13n), R.st())

def R.cells(o: C.Cir.Out) -> C.Cir.Cells:
  match o:
    case C.Cir.Out.next{C.Cir.State{_, m, _, _, _, _, _, _, _, _}}:
      m
    case _:
      C.Cir.Cells.none{}

# the cells after the copy
def R.m2() -> C.Cir.Cells:
  R.cells(R.copy())

# 401 is an owned root: it has a pointer, so it is in no pend list
def R.pend.no.ptr(
  -rest2: List<&2, U32>,
  hp: PM.PendOK(Con{401, rest2}, Con{400, Con{401, rest2}}, R.m2(), 400, 402, [401])
) -> Empty:
  match hp:
    case Tuple{_, Tuple{_, Tuple{h0, _}}}:
      N.true_ne_false(Equal.cong(Nat, Bool, x => Nat.is_eq(x, 1n), 1n, 0n, h0))

def R.pend.no.y(
  +y: U32,
  -rest2: List<&2, U32>,
  e: {401 == y: U32}
) -> PM.PendOK(Con{y, rest2}, Con{400, Con{y, rest2}}, R.m2(), 400, 402, [401]) -> Empty:
  %e: PM.PendOK(Con{_, rest2}, Con{400, Con{_, rest2}}, R.m2(), 400, 402, [401]) -> Empty
  hp => R.pend.no.ptr(rest2, hp)

# after 400, the pend list goes on to 401 (its link field)
def R.pend.no.c(
  rest: List<&2, U32>
) -> PM.Chain(
  rest,
  R.m2(),
  401
) -> PM.PendOK(rest, Con{400, rest}, R.m2(), 400, 402, [401]) -> Empty:
  match rest:
    case Nil{}:
      hc => hp => N.false_ne_true(Equal.cong(U32, Bool, x => U32.is_eq(x, 0), 401, 0, hc))
    case Con{+y, rest2}:
      hc => hp => R.pend.no.y(
        y,
        rest2,
        PM.Ex.fst(
          {401 == y: U32},
          _ => PM.P2(
            {U32.is_eq(y, 0) == False{}: Bool},
            PM.Chain(rest2, R.m2(), PM.Fd(1n, R.m2(), y))
          ),
          hc
        )
      )(hp)

def R.pend.no.x(
  +x: U32,
  rest: List<&2, U32>,
  e: {400 == x: U32}
) -> PM.Chain(
  rest,
  R.m2(),
  PM.Fd(1n, R.m2(), x)
) -> PM.PendOK(rest, Con{x, rest}, R.m2(), 400, 402, [401]) -> Empty:
  %e: PM.Chain(
    rest,
    R.m2(),
    PM.Fd(1n, R.m2(), _)
  ) -> PM.PendOK(rest, Con{_, rest}, R.m2(), 400, 402, [401]) -> Empty
  R.pend.no.c(rest)

# the pend list from 400 after the copy holds 401, a root: none
def R.pend.no(
  ps2: List<&2, U32>,
  hc: PM.Chain(ps2, R.m2(), 400),
  hp: PM.PendOK(ps2, ps2, R.m2(), 400, 402, [401])
) -> Empty:
  match ps2:
    case Nil{}:
      N.false_ne_true(Equal.cong(U32, Bool, x => U32.is_eq(x, 0), 400, 0, hc))
    case Con{+x, rest}:
      match hc hp:
        case Tuple{ex, Tuple{_, hc2}} Tuple{_, Tuple{_, Tuple{_, hp2}}}:
          R.pend.no.x(x, rest, ex)(hc2, hp2)

def R.some(+a: U32, +b: U32, e: {Some{a} == Some{b}: Maybe<&2, U32>}) -> {a == b: U32}:
  Equal.cong(Maybe<&2, U32>, U32, x => Maybe.default(&2, U32, x, 0), Some{a}, Some{b}, e)

def R.heap.no(
  +n: U32,
  +pend2: U32,
  ps2: List<&2, U32>,
  e1: {401 == n: U32},
  e2: {400 == pend2: U32}
) -> PM.Chain(ps2, R.m2(), pend2) -> PM.PendOK(ps2, ps2, R.m2(), 400, 402, [n]) -> Empty:
  %e1: PM.Chain(ps2, R.m2(), pend2) -> PM.PendOK(ps2, ps2, R.m2(), 400, 402, [_]) -> Empty
  %e2: PM.Chain(ps2, R.m2(), _) -> PM.PendOK(ps2, ps2, R.m2(), 400, 402, [401]) -> Empty
  hc => hp => R.pend.no(ps2, hc, hp)

# the conclusion of copy.post on this state has no inhabitant
def R.copy.no(
  h: PM.CopyPost(
    4n,
    Nil{},
    R.ks(),
    Nil{},
    R.regs(),
    R.m(),
    402,
    400,
    363,
    1,
    1,
    Nil{},
    15n,
    13n,
    Nil{},
    Nil{},
    Nil{},
    Nil{},
    0,
    400,
    [400],
    401,
    C.Term.Rfl{},
    0,
    Nil{},
    R.hs(),
    {==},
    {==},
    {==},
    {==},
    {==},
    {==},
    {==}
  )
) -> Empty:
  match h:
    case Tuple{
      _,
      Tuple{
        +n,
        Tuple{
          +pend2,
          Tuple{
            ps2,
            Tuple{
              hr,
              Tuple{
                h3,
                Tuple{Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{Tuple{hc, Tuple{hp, _}}, _}}}}}, _}
              }
            }
          }
        }
      }
    }:
      R.heap.no(n, pend2, ps2, R.some(401, n, hr), R.some(400, pend2, h3))(hc, hp)

# so copy.post, of the type CopyPost, gives Empty: its premises hold here
def copy.post.false(
  cp: PM.CopyPost(
    4n,
    Nil{},
    R.ks(),
    Nil{},
    R.regs(),
    R.m(),
    402,
    400,
    363,
    1,
    1,
    Nil{},
    15n,
    13n,
    Nil{},
    Nil{},
    Nil{},
    Nil{},
    0,
    400,
    [400],
    401,
    C.Term.Rfl{},
    0,
    Nil{},
    R.hs(),
    {==},
    {==},
    {==},
    {==},
    {==},
    {==},
    {==}
  )
) -> Empty:
  R.copy.no(cp)

# A local that no root holds
# --------------------------
#
# The borrowed source c = 403 (Var 0) is an owned root too (register 0), so
# Held holds of it in any reading; the one local is the K.arg a = 402, not
# OWNED, whose term x = 401 (a Rfl of count 1) is held only by the pend
# list's p = 400 (a Typ). The root's M.alloc pends x; the copy puts x in (it
# is closed): the result x is in the pend list (p -> x -> 1), against PendOK.
def RB.m() -> C.Cir.Cells:
  C.Cir.Cells.set(
    C.Cir.Cells.set(
      C.Cir.Cells.set(
        C.Cir.Cells.set(R.img(), 400, C.Cir.Cell{4, 0, 401, 0, 0}),
        401,
        C.Cir.Cell{17, 1, 0, 0, 0}
      ),
      402,
      C.Cir.Cell{41, 0, 401, 0, 0}
    ),
    403,
    C.Cir.Cell{8192, 1, 0, 0, 0}
  )

def RB.regs() -> List<&2, U32>:
  List.set(
    &2,
    U32,
    List.set(
      &2,
      U32,
      List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, R.z(64n), 0n, 403), 13n, 403), 3n, 400),
      36n,
      402
    ),
    37n,
    1
  )

def RB.st() -> C.Cir.State:
  C.Cir.State{RB.regs(), RB.m(), 404, 400, 363, 1, 1, Nil{}, Nil{}, 0}

def RB.os() -> List<&2, PM.Rt>:
  [PM.Rt{403, C.Term.Var{0n}}]

def RB.es() -> List<&2, C.Arg>:
  [C.Arg{C.Quan.Q0{}, C.Term.Rfl{}}]

def RB.hs() -> PM.HS(
  Nil{},
  R.ks(),
  Nil{},
  RB.m(),
  404,
  400,
  363,
  RB.os(),
  RB.os(),
  Nil{},
  0,
  400,
  [400]
):
  Tuple{
    Tuple{
      Tuple{Tuple{{==}, Tuple{{==}, Tuple{{==}, Tuple{{==}, Tuple{{==}, {==}}}}}}, {==}},
      Unit{}
    },
    Tuple{
      Tuple{
        Tuple{Tuple{{==}, Tuple{{==}, Tuple{{==}, Tuple{{==}, Tuple{{==}, {==}}}}}}, {==}},
        Unit{}
      },
      Tuple{
        Tuple{{==}, Unit{}},
        Tuple{
          {==},
          Tuple{
            Tuple{
              Tuple{{==}, Tuple{{==}, {==}}},
              Tuple{Tuple{{==}, Tuple{{==}, Tuple{{==}, Unit{}}}}, Tuple{{==}, Tuple{{==}, {==}}}}
            },
            Tuple{
              Tuple{
                {==},
                Tuple{
                  {==},
                  Tuple{
                    {==},
                    Tuple{
                      {==},
                      Tuple{
                        {==},
                        Tuple{
                          {==},
                          Tuple{
                            {==},
                            Tuple{
                              {==},
                              Tuple{
                                {==},
                                Tuple{
                                  {==},
                                  Tuple{
                                    {==},
                                    Tuple{
                                      {==},
                                      Tuple{
                                        {==},
                                        Tuple{
                                          {==},
                                          Tuple{
                                            {==},
                                            Tuple{
                                              {==},
                                              Tuple{
                                                {==},
                                                Tuple{
                                                  {==},
                                                  Tuple{
                                                    {==},
                                                    Tuple{
                                                      {==},
                                                      Tuple{
                                                        {==},
                                                        Tuple{
                                                          {==},
                                                          Tuple{
                                                            {==},
                                                            Tuple{
                                                              {==},
                                                              Tuple{
                                                                {==},
                                                                Tuple{
                                                                  {==},
                                                                  Tuple{
                                                                    {==},
                                                                    Tuple{
                                                                      {==},
                                                                      Tuple{
                                                                        {==},
                                                                        Tuple{
                                                                          {==},
                                                                          Tuple{
                                                                            {==},
                                                                            Tuple{
                                                                              {==},
                                                                              Tuple{
                                                                                {==},
                                                                                Tuple{
                                                                                  {==},
                                                                                  Tuple{
                                                                                    {==},
                                                                                    Tuple{
                                                                                      {==},
                                                                                      Tuple{
                                                                                        {==},
                                                                                        Tuple{
                                                                                          {==},
                                                                                          Tuple{
                                                                                            {==},
                                                                                            Tuple{
                                                                                              {==},
                                                                                              Tuple{
                                                                                                {
                                                                                                  ==
                                                                                                },
                                                                                                Tuple{
                                                                                                  {
                                                                                                    ==
                                                                                                  },
                                                                                                  Tuple{
                                                                                                    {
                                                                                                      ==
                                                                                                    },
                                                                                                    Tuple{
                                                                                                      {
                                                                                                        ==
                                                                                                      },
                                                                                                      Tuple{
                                                                                                        {
                                                                                                          ==
                                                                                                        },
                                                                                                        Tuple{
                                                                                                          {
                                                                                                            ==
                                                                                                          },
                                                                                                          Tuple{
                                                                                                            {
                                                                                                              ==
                                                                                                            },
                                                                                                            Tuple{
                                                                                                              {
                                                                                                                ==
                                                                                                              },
                                                                                                              Tuple{
                                                                                                                {
                                                                                                                  ==
                                                                                                                },
                                                                                                                Tuple{
                                                                                                                  {
                                                                                                                    ==
                                                                                                                  },
                                                                                                                  Tuple{
                                                                                                                    {
                                                                                                                      ==
                                                                                                                    },
                                                                                                                    Tuple{
                                                                                                                      {
                                                                                                                        ==
                                                                                                                      },
                                                                                                                      Tuple{
                                                                                                                        {
                                                                                                                          ==
                                                                                                                        },
                                                                                                                        Tuple{
                                                                                                                          {
                                                                                                                            ==
                                                                                                                          },
                                                                                                                          Tuple{
                                                                                                                            {
                                                                                                                              ==
                                                                                                                            },
                                                                                                                            Tuple{
                                                                                                                              {
                                                                                                                                ==
                                                                                                                              },
                                                                                                                              Tuple{
                                                                                                                                {
                                                                                                                                  ==
                                                                                                                                },
                                                                                                                                Tuple{
                                                                                                                                  {
                                                                                                                                    ==
                                                                                                                                  },
                                                                                                                                  Tuple{
                                                                                                                                    {
                                                                                                                                      ==
                                                                                                                                    },
                                                                                                                                    Tuple{
                                                                                                                                      {
                                                                                                                                        ==
                                                                                                                                      },
                                                                                                                                      Tuple{
                                                                                                                                        {
                                                                                                                                          ==
                                                                                                                                        },
                                                                                                                                        Tuple{
                                                                                                                                          {
                                                                                                                                            ==
                                                                                                                                          },
                                                                                                                                          Tuple{
                                                                                                                                            {
                                                                                                                                              ==
                                                                                                                                            },
                                                                                                                                            Tuple{
                                                                                                                                              {
                                                                                                                                                ==
                                                                                                                                              },
                                                                                                                                              Tuple{
                                                                                                                                                {
                                                                                                                                                  ==
                                                                                                                                                },
                                                                                                                                                Tuple{
                                                                                                                                                  {
                                                                                                                                                    ==
                                                                                                                                                  },
                                                                                                                                                  Tuple{
                                                                                                                                                    {
                                                                                                                                                      ==
                                                                                                                                                    },
                                                                                                                                                    Tuple{
                                                                                                                                                      {
                                                                                                                                                        ==
                                                                                                                                                      },
                                                                                                                                                      Tuple{
                                                                                                                                                        {
                                                                                                                                                          ==
                                                                                                                                                        },
                                                                                                                                                        Tuple{
                                                                                                                                                          {
                                                                                                                                                            ==
                                                                                                                                                          },
                                                                                                                                                          Tuple{
                                                                                                                                                            {
                                                                                                                                                              ==
                                                                                                                                                            },
                                                                                                                                                            Tuple{
                                                                                                                                                              {
                                                                                                                                                                ==
                                                                                                                                                              },
                                                                                                                                                              Tuple{
                                                                                                                                                                {
                                                                                                                                                                  ==
                                                                                                                                                                },
                                                                                                                                                                Tuple{
                                                                                                                                                                  {
                                                                                                                                                                    ==
                                                                                                                                                                  },
                                                                                                                                                                  Tuple{
                                                                                                                                                                    {
                                                                                                                                                                      ==
                                                                                                                                                                    },
                                                                                                                                                                    Tuple{
                                                                                                                                                                      {
                                                                                                                                                                        ==
                                                                                                                                                                      },
                                                                                                                                                                      Unit{}
                                                                                                                                                                    }
                                                                                                                                                                  }
                                                                                                                                                                }
                                                                                                                                                              }
                                                                                                                                                            }
                                                                                                                                                          }
                                                                                                                                                        }
                                                                                                                                                      }
                                                                                                                                                    }
                                                                                                                                                  }
                                                                                                                                                }
                                                                                                                                              }
                                                                                                                                            }
                                                                                                                                          }
                                                                                                                                        }
                                                                                                                                      }
                                                                                                                                    }
                                                                                                                                  }
                                                                                                                                }
                                                                                                                              }
                                                                                                                            }
                                                                                                                          }
                                                                                                                        }
                                                                                                                      }
                                                                                                                    }
                                                                                                                  }
                                                                                                                }
                                                                                                              }
                                                                                                            }
                                                                                                          }
                                                                                                        }
                                                                                                      }
                                                                                                    }
                                                                                                  }
                                                                                                }
                                                                                              }
                                                                                            }
                                                                                          }
                                                                                        }
                                                                                      }
                                                                                    }
                                                                                  }
                                                                                }
                                                                              }
                                                                            }
                                                                          }
                                                                        }
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              },
              Tuple{
                Unit{},
                Tuple{
                  Tuple{
                    Tuple{{==}, Tuple{{==}, Tuple{{==}, Tuple{{==}, Tuple{{==}, {==}}}}}},
                    Tuple{{==}, {==}}
                  },
                  Tuple{
                    Tuple{
                      Tuple{{==}, Tuple{{==}, Tuple{{==}, Tuple{{==}, Tuple{{==}, {==}}}}}},
                      Tuple{{==}, {==}}
                    },
                    Tuple{
                      Tuple{
                        Tuple{{==}, Tuple{{==}, Tuple{{==}, Tuple{{==}, Tuple{{==}, {==}}}}}},
                        Tuple{{==}, {==}}
                      },
                      Tuple{Tuple{Nil{}, {==}}, Tuple{{==}, {==}}}
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }

def RB.env() -> PM.Ag(Nil{}, RB.m(), 363, 400, 404, R.ks(), Nil{}, [400], 402, RB.es()):
  Tuple{
    {==},
    Tuple{
      {==},
      Tuple{
        {==},
        Tuple{
          {==},
          Tuple{
            {==},
            Tuple{
              {==},
              Tuple{
                {==},
                Tuple{
                  Tuple{{==}, Tuple{{==}, Tuple{{==}, Tuple{{==}, Tuple{{==}, {==}}}}}},
                  Tuple{{==}, {==}}
                }
              }
            }
          }
        }
      }
    }
  }

def RB.copy() -> C.Cir.Out:
  C.Cir.exec(4n, C.M.copy(15n, 13n), RB.st())

def RB.cells(o: C.Cir.Out) -> C.Cir.Cells:
  match o:
    case C.Cir.Out.next{C.Cir.State{_, m, _, _, _, _, _, _, _, _}}:
      m
    case _:
      C.Cir.Cells.none{}

# the cells after the copy
def RB.m2() -> C.Cir.Cells:
  RB.cells(RB.copy())

# 401 is an owned root: it has a pointer, so it is in no pend list
def RB.pend.no.ptr(
  -rest2: List<&2, U32>,
  hp: PM.PendOK(Con{401, rest2}, Con{400, Con{401, rest2}}, RB.m2(), 400, 404, [401, 403])
) -> Empty:
  match hp:
    case Tuple{_, Tuple{_, Tuple{h0, _}}}:
      N.true_ne_false(Equal.cong(Nat, Bool, x => Nat.is_eq(x, 1n), 1n, 0n, h0))

def RB.pend.no.y(
  +y: U32,
  -rest2: List<&2, U32>,
  e: {401 == y: U32}
) -> PM.PendOK(Con{y, rest2}, Con{400, Con{y, rest2}}, RB.m2(), 400, 404, [401, 403]) -> Empty:
  %e: PM.PendOK(Con{_, rest2}, Con{400, Con{_, rest2}}, RB.m2(), 400, 404, [401, 403]) -> Empty
  hp => RB.pend.no.ptr(rest2, hp)

# after 400, the pend list goes on to 401 (its link field)
def RB.pend.no.c(
  rest: List<&2, U32>
) -> PM.Chain(
  rest,
  RB.m2(),
  401
) -> PM.PendOK(rest, Con{400, rest}, RB.m2(), 400, 404, [401, 403]) -> Empty:
  match rest:
    case Nil{}:
      hc => hp => N.false_ne_true(Equal.cong(U32, Bool, x => U32.is_eq(x, 0), 401, 0, hc))
    case Con{+y, rest2}:
      hc => hp => RB.pend.no.y(
        y,
        rest2,
        PM.Ex.fst(
          {401 == y: U32},
          _ => PM.P2(
            {U32.is_eq(y, 0) == False{}: Bool},
            PM.Chain(rest2, RB.m2(), PM.Fd(1n, RB.m2(), y))
          ),
          hc
        )
      )(hp)

def RB.pend.no.x(
  +x: U32,
  rest: List<&2, U32>,
  e: {400 == x: U32}
) -> PM.Chain(
  rest,
  RB.m2(),
  PM.Fd(1n, RB.m2(), x)
) -> PM.PendOK(rest, Con{x, rest}, RB.m2(), 400, 404, [401, 403]) -> Empty:
  %e: PM.Chain(
    rest,
    RB.m2(),
    PM.Fd(1n, RB.m2(), _)
  ) -> PM.PendOK(rest, Con{_, rest}, RB.m2(), 400, 404, [401, 403]) -> Empty
  RB.pend.no.c(rest)

# the pend list from 400 after the copy holds 401, a root: none
def RB.pend.no(
  ps2: List<&2, U32>,
  hc: PM.Chain(ps2, RB.m2(), 400),
  hp: PM.PendOK(ps2, ps2, RB.m2(), 400, 404, [401, 403])
) -> Empty:
  match ps2:
    case Nil{}:
      N.false_ne_true(Equal.cong(U32, Bool, x => U32.is_eq(x, 0), 400, 0, hc))
    case Con{+x, rest}:
      match hc hp:
        case Tuple{ex, Tuple{_, hc2}} Tuple{_, Tuple{_, Tuple{_, hp2}}}:
          RB.pend.no.x(x, rest, ex)(hc2, hp2)

def RB.some(+a: U32, +b: U32, e: {Some{a} == Some{b}: Maybe<&2, U32>}) -> {a == b: U32}:
  Equal.cong(Maybe<&2, U32>, U32, x => Maybe.default(&2, U32, x, 0), Some{a}, Some{b}, e)

def RB.heap.no(
  +n: U32,
  +pend2: U32,
  ps2: List<&2, U32>,
  e1: {401 == n: U32},
  e2: {400 == pend2: U32}
) -> PM.Chain(ps2, RB.m2(), pend2) -> PM.PendOK(ps2, ps2, RB.m2(), 400, 404, [n, 403]) -> Empty:
  %e1: PM.Chain(ps2, RB.m2(), pend2) -> PM.PendOK(ps2, ps2, RB.m2(), 400, 404, [_, 403]) -> Empty
  %e2: PM.Chain(ps2, RB.m2(), _) -> PM.PendOK(ps2, ps2, RB.m2(), 400, 404, [401, 403]) -> Empty
  hc => hp => RB.pend.no(ps2, hc, hp)

# the conclusion of copy.post on this state has no inhabitant
def RB.copy.no(
  h: PM.CopyPost(
    4n,
    Nil{},
    R.ks(),
    Nil{},
    RB.regs(),
    RB.m(),
    404,
    400,
    363,
    1,
    1,
    Nil{},
    15n,
    13n,
    Nil{},
    RB.os(),
    Nil{},
    Nil{},
    0,
    400,
    [400],
    403,
    C.Term.Var{0n},
    402,
    RB.es(),
    RB.hs(),
    {==},
    {==},
    {==},
    {==},
    {==},
    RB.env(),
    {==}
  )
) -> Empty:
  match h:
    case Tuple{
      _,
      Tuple{
        +n,
        Tuple{
          +pend2,
          Tuple{
            ps2,
            Tuple{
              hr,
              Tuple{
                h3,
                Tuple{Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{Tuple{hc, Tuple{hp, _}}, _}}}}}, _}
              }
            }
          }
        }
      }
    }:
      RB.heap.no(n, pend2, ps2, RB.some(401, n, hr), RB.some(400, pend2, h3))(hc, hp)

# so copy.post gives Empty here too
def copy.post.false.local(
  cp: PM.CopyPost(
    4n,
    Nil{},
    R.ks(),
    Nil{},
    RB.regs(),
    RB.m(),
    404,
    400,
    363,
    1,
    1,
    Nil{},
    15n,
    13n,
    Nil{},
    RB.os(),
    Nil{},
    Nil{},
    0,
    400,
    [400],
    403,
    C.Term.Var{0n},
    402,
    RB.es(),
    RB.hs(),
    {==},
    {==},
    {==},
    {==},
    {==},
    RB.env(),
    {==}
  )
) -> Empty:
  RB.copy.no(cp)
