# compiler: the copy's headers, bit by bit
# ========================================
#
# Field 0 of a cell holds its tag (bits 0 to 5), quantity (6, 7), flags or,
# in a copy's new cell, the parts still to copy (8 to 10), and fv (13 up).
# M.copy.push makes a header or(and(f0, 255), shl(e, 8)) (Hp below, e the
# mask of the parts), M.finish one or(and(x, 255), shl(cm, 13)) (Hf, cm the
# fv); a frame of the walk has or(h, shl(T, 8)), with h its low byte (Hw).
# Their tag, quantity, low byte, todo bits and fv, as M.tag, M.q, M.todo and
# M.fv read them.
#
# The proofs turn and/or into forms that match the mask first (Word.andm of
# proof_leb.bend, sel, blend), which compute once the variables are split
# into their bits (the .f lemmas).
import Base
import ./impl.bend as C
import ./proof_leb.bend as L

# The forms
# ---------
def U.w(x: U32) -> Word(32n):
  match x:
    case U32{w}:
      w

def U.andm(+x: U32, +m: U32) -> U32:
  U32{L.Word.andm(32n, U.w(x), U.w(m))}

def U.sel(+x: U32, +m: U32) -> U32:
  U32{L.Word.sel(32n, U.w(x), U.w(m))}

# w's bits where m is set, v's where it is clear
def Wb.blend(n: Nat, w: Word(n), v: Word(n), m: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w v m:
        case WCon{a, t} WCon{_, s} WCon{True{}, mt}:
          WCon{a, Wb.blend(p, t, s, mt)}
        case WCon{_, t} WCon{b, s} WCon{False{}, mt}:
          WCon{b, Wb.blend(p, t, s, mt)}

def U.blend(+x: U32, +v: U32, +m: U32) -> U32:
  U32{Wb.blend(32n, U.w(x), U.w(v), U.w(m))}

def Wb.or_blend(
  n: Nat,
  w: Word(n),
  v: Word(n),
  m: Word(n)
) -> {Word.or(n, L.Word.andm(n, w, m), L.Word.sel(n, v, m)) == Wb.blend(n, w, v, m): Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w v m:
        case WCon{True{}, t} WCon{_, s} WCon{True{}, mt}:
          %Wb.or_blend(
            p,
            t,
            s,
            mt
          ): {
            WCon{
              True{},
              Word.or(p, L.Word.andm(p, t, mt), L.Word.sel(p, s, mt))
            }
              == WCon{True{}, _}: Word(1n+p)
          }
          {==}
        case WCon{False{}, t} WCon{_, s} WCon{True{}, mt}:
          %Wb.or_blend(
            p,
            t,
            s,
            mt
          ): {
            WCon{
              False{},
              Word.or(p, L.Word.andm(p, t, mt), L.Word.sel(p, s, mt))
            }
              == WCon{False{}, _}: Word(1n+p)
          }
          {==}
        case WCon{_, t} WCon{b, s} WCon{False{}, mt}:
          %Wb.or_blend(
            p,
            t,
            s,
            mt
          ): {
            WCon{
              b,
              Word.or(p, L.Word.andm(p, t, mt), L.Word.sel(p, s, mt))
            }
              == WCon{b, _}: Word(1n+p)
          }
          {==}

def U.am(x: U32, m: U32) -> {U32.and(x, m) == U.andm(x, m): U32}:
  match x m:
    case U32{a} U32{b}:
      Equal.cong(
        Word(32n),
        U32,
        u => U32{u},
        Word.and(32n, a, b),
        L.Word.andm(32n, a, b),
        L.Word.and_is_andm(32n, a, b)
      )

def U.bl(x: U32, v: U32, m: U32) -> {U32.or(U.andm(x, m), U.sel(v, m)) == U.blend(x, v, m): U32}:
  match x v m:
    case U32{a} U32{b} U32{c}:
      Equal.cong(
        Word(32n),
        U32,
        u => U32{u},
        Word.or(32n, L.Word.andm(32n, a, c), L.Word.sel(32n, b, c)),
        Wb.blend(32n, a, b, c),
        Wb.or_blend(32n, a, b, c)
      )

def U.s8(x: U32) -> {U32.shln(x, 8n) == U.sel(U32.shln(x, 8n), 255): U32}:
  match x:
    case U32{
      WCon{
        +b0,
        WCon{
          +b1,
          WCon{
            +b2,
            WCon{
              +b3,
              WCon{
                +b4,
                WCon{
                  +b5,
                  WCon{
                    +b6,
                    WCon{
                      +b7,
                      WCon{
                        +b8,
                        WCon{
                          +b9,
                          WCon{
                            +b10,
                            WCon{
                              +b11,
                              WCon{
                                +b12,
                                WCon{
                                  +b13,
                                  WCon{
                                    +b14,
                                    WCon{
                                      +b15,
                                      WCon{
                                        +b16,
                                        WCon{
                                          +b17,
                                          WCon{
                                            +b18,
                                            WCon{
                                              +b19,
                                              WCon{
                                                +b20,
                                                WCon{
                                                  +b21,
                                                  WCon{
                                                    +b22,
                                                    WCon{
                                                      +b23,
                                                      WCon{
                                                        +b24,
                                                        WCon{
                                                          +b25,
                                                          WCon{
                                                            +b26,
                                                            WCon{
                                                              +b27,
                                                              WCon{
                                                                +b28,
                                                                WCon{
                                                                  +b29,
                                                                  WCon{+b30, WCon{+b31, WNil{}}}
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
    }:
      {==}

def U.s13(x: U32) -> {U32.shln(x, 13n) == U.sel(U32.shln(x, 13n), 255): U32}:
  match x:
    case U32{
      WCon{
        +b0,
        WCon{
          +b1,
          WCon{
            +b2,
            WCon{
              +b3,
              WCon{
                +b4,
                WCon{
                  +b5,
                  WCon{
                    +b6,
                    WCon{
                      +b7,
                      WCon{
                        +b8,
                        WCon{
                          +b9,
                          WCon{
                            +b10,
                            WCon{
                              +b11,
                              WCon{
                                +b12,
                                WCon{
                                  +b13,
                                  WCon{
                                    +b14,
                                    WCon{
                                      +b15,
                                      WCon{
                                        +b16,
                                        WCon{
                                          +b17,
                                          WCon{
                                            +b18,
                                            WCon{
                                              +b19,
                                              WCon{
                                                +b20,
                                                WCon{
                                                  +b21,
                                                  WCon{
                                                    +b22,
                                                    WCon{
                                                      +b23,
                                                      WCon{
                                                        +b24,
                                                        WCon{
                                                          +b25,
                                                          WCon{
                                                            +b26,
                                                            WCon{
                                                              +b27,
                                                              WCon{
                                                                +b28,
                                                                WCon{
                                                                  +b29,
                                                                  WCon{+b30, WCon{+b31, WNil{}}}
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
    }:
      {==}

# the header, blended
def U.hp(
  +x: U32,
  +e: U32
) -> {U32.or(U32.and(x, 255), U32.shln(e, 8n)) == U.blend(x, U32.shln(e, 8n), 255): U32}:
  %Equal.sym(
    U32,
    U32.and(x, 255),
    U.andm(x, 255),
    U.am(x, 255)
  ): {U32.or(_, U32.shln(e, 8n)) == U.blend(x, U32.shln(e, 8n), 255): U32}
  %Equal.sym(
    U32,
    U32.shln(e, 8n),
    U.sel(U32.shln(e, 8n), 255),
    U.s8(e)
  ): {U32.or(U.andm(x, 255), _) == U.blend(x, U32.shln(e, 8n), 255): U32}
  U.bl(x, U32.shln(e, 8n), 255)

# the header, blended
def U.hf(
  +x: U32,
  +e: U32
) -> {U32.or(U32.and(x, 255), U32.shln(e, 13n)) == U.blend(x, U32.shln(e, 13n), 255): U32}:
  %Equal.sym(
    U32,
    U32.and(x, 255),
    U.andm(x, 255),
    U.am(x, 255)
  ): {U32.or(_, U32.shln(e, 13n)) == U.blend(x, U32.shln(e, 13n), 255): U32}
  %Equal.sym(
    U32,
    U32.shln(e, 13n),
    U.sel(U32.shln(e, 13n), 255),
    U.s13(e)
  ): {U32.or(U.andm(x, 255), _) == U.blend(x, U32.shln(e, 13n), 255): U32}
  U.bl(x, U32.shln(e, 13n), 255)

# The push header: or(and(f0, 255), shl(e, 8))
# ---------------------------------------------
def Hp.tag.f(
  f0: U32,
  e: U32
) -> {U.andm(U.blend(f0, U32.shln(e, 8n), 255), 63) == U.andm(f0, 63): U32}:
  match f0:
    case U32{
      WCon{
        +a0,
        WCon{
          +a1,
          WCon{
            +a2,
            WCon{
              +a3,
              WCon{
                +a4,
                WCon{
                  +a5,
                  WCon{
                    +a6,
                    WCon{
                      +a7,
                      WCon{
                        +a8,
                        WCon{
                          +a9,
                          WCon{
                            +a10,
                            WCon{
                              +a11,
                              WCon{
                                +a12,
                                WCon{
                                  +a13,
                                  WCon{
                                    +a14,
                                    WCon{
                                      +a15,
                                      WCon{
                                        +a16,
                                        WCon{
                                          +a17,
                                          WCon{
                                            +a18,
                                            WCon{
                                              +a19,
                                              WCon{
                                                +a20,
                                                WCon{
                                                  +a21,
                                                  WCon{
                                                    +a22,
                                                    WCon{
                                                      +a23,
                                                      WCon{
                                                        +a24,
                                                        WCon{
                                                          +a25,
                                                          WCon{
                                                            +a26,
                                                            WCon{
                                                              +a27,
                                                              WCon{
                                                                +a28,
                                                                WCon{
                                                                  +a29,
                                                                  WCon{+a30, WCon{+a31, WNil{}}}
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
    }:
      match e:
        case U32{
          WCon{
            +b0,
            WCon{
              +b1,
              WCon{
                +b2,
                WCon{
                  +b3,
                  WCon{
                    +b4,
                    WCon{
                      +b5,
                      WCon{
                        +b6,
                        WCon{
                          +b7,
                          WCon{
                            +b8,
                            WCon{
                              +b9,
                              WCon{
                                +b10,
                                WCon{
                                  +b11,
                                  WCon{
                                    +b12,
                                    WCon{
                                      +b13,
                                      WCon{
                                        +b14,
                                        WCon{
                                          +b15,
                                          WCon{
                                            +b16,
                                            WCon{
                                              +b17,
                                              WCon{
                                                +b18,
                                                WCon{
                                                  +b19,
                                                  WCon{
                                                    +b20,
                                                    WCon{
                                                      +b21,
                                                      WCon{
                                                        +b22,
                                                        WCon{
                                                          +b23,
                                                          WCon{
                                                            +b24,
                                                            WCon{
                                                              +b25,
                                                              WCon{
                                                                +b26,
                                                                WCon{
                                                                  +b27,
                                                                  WCon{
                                                                    +b28,
                                                                    WCon{
                                                                      +b29,
                                                                      WCon{+b30, WCon{+b31, WNil{}}}
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
        }:
          {==}

def Hp.tag(
  +f0: U32,
  +e: U32
) -> {U32.and(U32.or(U32.and(f0, 255), U32.shln(e, 8n)), 63) == U32.and(f0, 63): U32}:
  %Equal.sym(
    U32,
    U32.or(U32.and(f0, 255), U32.shln(e, 8n)),
    U.blend(f0, U32.shln(e, 8n), 255),
    U.hp(f0, e)
  ): {U32.and(_, 63) == U32.and(f0, 63): U32}
  %Equal.sym(
    U32,
    U32.and(U.blend(f0, U32.shln(e, 8n), 255), 63),
    U.andm(U.blend(f0, U32.shln(e, 8n), 255), 63),
    U.am(U.blend(f0, U32.shln(e, 8n), 255), 63)
  ): {_ == U32.and(f0, 63): U32}
  %Equal.sym(
    U32,
    U32.and(f0, 63),
    U.andm(f0, 63),
    U.am(f0, 63)
  ): {U.andm(U.blend(f0, U32.shln(e, 8n), 255), 63) == _: U32}
  Hp.tag.f(f0, e)

def Hp.low.f(
  f0: U32,
  e: U32
) -> {U.andm(U.blend(f0, U32.shln(e, 8n), 255), 255) == U.andm(f0, 255): U32}:
  match f0:
    case U32{
      WCon{
        +a0,
        WCon{
          +a1,
          WCon{
            +a2,
            WCon{
              +a3,
              WCon{
                +a4,
                WCon{
                  +a5,
                  WCon{
                    +a6,
                    WCon{
                      +a7,
                      WCon{
                        +a8,
                        WCon{
                          +a9,
                          WCon{
                            +a10,
                            WCon{
                              +a11,
                              WCon{
                                +a12,
                                WCon{
                                  +a13,
                                  WCon{
                                    +a14,
                                    WCon{
                                      +a15,
                                      WCon{
                                        +a16,
                                        WCon{
                                          +a17,
                                          WCon{
                                            +a18,
                                            WCon{
                                              +a19,
                                              WCon{
                                                +a20,
                                                WCon{
                                                  +a21,
                                                  WCon{
                                                    +a22,
                                                    WCon{
                                                      +a23,
                                                      WCon{
                                                        +a24,
                                                        WCon{
                                                          +a25,
                                                          WCon{
                                                            +a26,
                                                            WCon{
                                                              +a27,
                                                              WCon{
                                                                +a28,
                                                                WCon{
                                                                  +a29,
                                                                  WCon{+a30, WCon{+a31, WNil{}}}
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
    }:
      match e:
        case U32{
          WCon{
            +b0,
            WCon{
              +b1,
              WCon{
                +b2,
                WCon{
                  +b3,
                  WCon{
                    +b4,
                    WCon{
                      +b5,
                      WCon{
                        +b6,
                        WCon{
                          +b7,
                          WCon{
                            +b8,
                            WCon{
                              +b9,
                              WCon{
                                +b10,
                                WCon{
                                  +b11,
                                  WCon{
                                    +b12,
                                    WCon{
                                      +b13,
                                      WCon{
                                        +b14,
                                        WCon{
                                          +b15,
                                          WCon{
                                            +b16,
                                            WCon{
                                              +b17,
                                              WCon{
                                                +b18,
                                                WCon{
                                                  +b19,
                                                  WCon{
                                                    +b20,
                                                    WCon{
                                                      +b21,
                                                      WCon{
                                                        +b22,
                                                        WCon{
                                                          +b23,
                                                          WCon{
                                                            +b24,
                                                            WCon{
                                                              +b25,
                                                              WCon{
                                                                +b26,
                                                                WCon{
                                                                  +b27,
                                                                  WCon{
                                                                    +b28,
                                                                    WCon{
                                                                      +b29,
                                                                      WCon{+b30, WCon{+b31, WNil{}}}
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
        }:
          {==}

def Hp.low(
  +f0: U32,
  +e: U32
) -> {U32.and(U32.or(U32.and(f0, 255), U32.shln(e, 8n)), 255) == U32.and(f0, 255): U32}:
  %Equal.sym(
    U32,
    U32.or(U32.and(f0, 255), U32.shln(e, 8n)),
    U.blend(f0, U32.shln(e, 8n), 255),
    U.hp(f0, e)
  ): {U32.and(_, 255) == U32.and(f0, 255): U32}
  %Equal.sym(
    U32,
    U32.and(U.blend(f0, U32.shln(e, 8n), 255), 255),
    U.andm(U.blend(f0, U32.shln(e, 8n), 255), 255),
    U.am(U.blend(f0, U32.shln(e, 8n), 255), 255)
  ): {_ == U32.and(f0, 255): U32}
  %Equal.sym(
    U32,
    U32.and(f0, 255),
    U.andm(f0, 255),
    U.am(f0, 255)
  ): {U.andm(U.blend(f0, U32.shln(e, 8n), 255), 255) == _: U32}
  Hp.low.f(f0, e)

def Hp.q.f(
  f0: U32,
  e: U32
) -> {
  U.andm(U32.shrn(U.blend(f0, U32.shln(e, 8n), 255), 6n), 3) == U.andm(U32.shrn(f0, 6n), 3): U32
}:
  match f0:
    case U32{
      WCon{
        +a0,
        WCon{
          +a1,
          WCon{
            +a2,
            WCon{
              +a3,
              WCon{
                +a4,
                WCon{
                  +a5,
                  WCon{
                    +a6,
                    WCon{
                      +a7,
                      WCon{
                        +a8,
                        WCon{
                          +a9,
                          WCon{
                            +a10,
                            WCon{
                              +a11,
                              WCon{
                                +a12,
                                WCon{
                                  +a13,
                                  WCon{
                                    +a14,
                                    WCon{
                                      +a15,
                                      WCon{
                                        +a16,
                                        WCon{
                                          +a17,
                                          WCon{
                                            +a18,
                                            WCon{
                                              +a19,
                                              WCon{
                                                +a20,
                                                WCon{
                                                  +a21,
                                                  WCon{
                                                    +a22,
                                                    WCon{
                                                      +a23,
                                                      WCon{
                                                        +a24,
                                                        WCon{
                                                          +a25,
                                                          WCon{
                                                            +a26,
                                                            WCon{
                                                              +a27,
                                                              WCon{
                                                                +a28,
                                                                WCon{
                                                                  +a29,
                                                                  WCon{+a30, WCon{+a31, WNil{}}}
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
    }:
      match e:
        case U32{
          WCon{
            +b0,
            WCon{
              +b1,
              WCon{
                +b2,
                WCon{
                  +b3,
                  WCon{
                    +b4,
                    WCon{
                      +b5,
                      WCon{
                        +b6,
                        WCon{
                          +b7,
                          WCon{
                            +b8,
                            WCon{
                              +b9,
                              WCon{
                                +b10,
                                WCon{
                                  +b11,
                                  WCon{
                                    +b12,
                                    WCon{
                                      +b13,
                                      WCon{
                                        +b14,
                                        WCon{
                                          +b15,
                                          WCon{
                                            +b16,
                                            WCon{
                                              +b17,
                                              WCon{
                                                +b18,
                                                WCon{
                                                  +b19,
                                                  WCon{
                                                    +b20,
                                                    WCon{
                                                      +b21,
                                                      WCon{
                                                        +b22,
                                                        WCon{
                                                          +b23,
                                                          WCon{
                                                            +b24,
                                                            WCon{
                                                              +b25,
                                                              WCon{
                                                                +b26,
                                                                WCon{
                                                                  +b27,
                                                                  WCon{
                                                                    +b28,
                                                                    WCon{
                                                                      +b29,
                                                                      WCon{+b30, WCon{+b31, WNil{}}}
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
        }:
          {==}

def Hp.q(
  +f0: U32,
  +e: U32
) -> {
  U32.and(
    U32.shrn(U32.or(U32.and(f0, 255), U32.shln(e, 8n)), 6n),
    3
  )
    == U32.and(U32.shrn(f0, 6n), 3): U32
}:
  %Equal.sym(
    U32,
    U32.or(U32.and(f0, 255), U32.shln(e, 8n)),
    U.blend(f0, U32.shln(e, 8n), 255),
    U.hp(f0, e)
  ): {U32.and(U32.shrn(_, 6n), 3) == U32.and(U32.shrn(f0, 6n), 3): U32}
  %Equal.sym(
    U32,
    U32.and(U32.shrn(U.blend(f0, U32.shln(e, 8n), 255), 6n), 3),
    U.andm(U32.shrn(U.blend(f0, U32.shln(e, 8n), 255), 6n), 3),
    U.am(U32.shrn(U.blend(f0, U32.shln(e, 8n), 255), 6n), 3)
  ): {_ == U32.and(U32.shrn(f0, 6n), 3): U32}
  %Equal.sym(
    U32,
    U32.and(U32.shrn(f0, 6n), 3),
    U.andm(U32.shrn(f0, 6n), 3),
    U.am(U32.shrn(f0, 6n), 3)
  ): {U.andm(U32.shrn(U.blend(f0, U32.shln(e, 8n), 255), 6n), 3) == _: U32}
  Hp.q.f(f0, e)

def Hp.todo.f(
  f0: U32,
  e: U32
) -> {U.andm(U.blend(f0, U32.shln(e, 8n), 255), 1792) == U32.shln(U.andm(e, 7), 8n): U32}:
  match f0:
    case U32{
      WCon{
        +a0,
        WCon{
          +a1,
          WCon{
            +a2,
            WCon{
              +a3,
              WCon{
                +a4,
                WCon{
                  +a5,
                  WCon{
                    +a6,
                    WCon{
                      +a7,
                      WCon{
                        +a8,
                        WCon{
                          +a9,
                          WCon{
                            +a10,
                            WCon{
                              +a11,
                              WCon{
                                +a12,
                                WCon{
                                  +a13,
                                  WCon{
                                    +a14,
                                    WCon{
                                      +a15,
                                      WCon{
                                        +a16,
                                        WCon{
                                          +a17,
                                          WCon{
                                            +a18,
                                            WCon{
                                              +a19,
                                              WCon{
                                                +a20,
                                                WCon{
                                                  +a21,
                                                  WCon{
                                                    +a22,
                                                    WCon{
                                                      +a23,
                                                      WCon{
                                                        +a24,
                                                        WCon{
                                                          +a25,
                                                          WCon{
                                                            +a26,
                                                            WCon{
                                                              +a27,
                                                              WCon{
                                                                +a28,
                                                                WCon{
                                                                  +a29,
                                                                  WCon{+a30, WCon{+a31, WNil{}}}
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
    }:
      match e:
        case U32{
          WCon{
            +b0,
            WCon{
              +b1,
              WCon{
                +b2,
                WCon{
                  +b3,
                  WCon{
                    +b4,
                    WCon{
                      +b5,
                      WCon{
                        +b6,
                        WCon{
                          +b7,
                          WCon{
                            +b8,
                            WCon{
                              +b9,
                              WCon{
                                +b10,
                                WCon{
                                  +b11,
                                  WCon{
                                    +b12,
                                    WCon{
                                      +b13,
                                      WCon{
                                        +b14,
                                        WCon{
                                          +b15,
                                          WCon{
                                            +b16,
                                            WCon{
                                              +b17,
                                              WCon{
                                                +b18,
                                                WCon{
                                                  +b19,
                                                  WCon{
                                                    +b20,
                                                    WCon{
                                                      +b21,
                                                      WCon{
                                                        +b22,
                                                        WCon{
                                                          +b23,
                                                          WCon{
                                                            +b24,
                                                            WCon{
                                                              +b25,
                                                              WCon{
                                                                +b26,
                                                                WCon{
                                                                  +b27,
                                                                  WCon{
                                                                    +b28,
                                                                    WCon{
                                                                      +b29,
                                                                      WCon{+b30, WCon{+b31, WNil{}}}
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
        }:
          {==}

def Hp.todo(
  +f0: U32,
  +e: U32
) -> {U32.and(U32.or(U32.and(f0, 255), U32.shln(e, 8n)), 1792) == U32.shln(U32.and(e, 7), 8n): U32}:
  %Equal.sym(
    U32,
    U32.or(U32.and(f0, 255), U32.shln(e, 8n)),
    U.blend(f0, U32.shln(e, 8n), 255),
    U.hp(f0, e)
  ): {U32.and(_, 1792) == U32.shln(U32.and(e, 7), 8n): U32}
  %Equal.sym(
    U32,
    U32.and(U.blend(f0, U32.shln(e, 8n), 255), 1792),
    U.andm(U.blend(f0, U32.shln(e, 8n), 255), 1792),
    U.am(U.blend(f0, U32.shln(e, 8n), 255), 1792)
  ): {_ == U32.shln(U32.and(e, 7), 8n): U32}
  %Equal.sym(
    U32,
    U32.and(e, 7),
    U.andm(e, 7),
    U.am(e, 7)
  ): {U.andm(U.blend(f0, U32.shln(e, 8n), 255), 1792) == U32.shln(_, 8n): U32}
  Hp.todo.f(f0, e)

def Hp.b8.f(
  f0: U32,
  e: U32
) -> {U.andm(U.blend(f0, U32.shln(e, 8n), 255), 256) == U32.shln(U.andm(e, 1), 8n): U32}:
  match f0:
    case U32{
      WCon{
        +a0,
        WCon{
          +a1,
          WCon{
            +a2,
            WCon{
              +a3,
              WCon{
                +a4,
                WCon{
                  +a5,
                  WCon{
                    +a6,
                    WCon{
                      +a7,
                      WCon{
                        +a8,
                        WCon{
                          +a9,
                          WCon{
                            +a10,
                            WCon{
                              +a11,
                              WCon{
                                +a12,
                                WCon{
                                  +a13,
                                  WCon{
                                    +a14,
                                    WCon{
                                      +a15,
                                      WCon{
                                        +a16,
                                        WCon{
                                          +a17,
                                          WCon{
                                            +a18,
                                            WCon{
                                              +a19,
                                              WCon{
                                                +a20,
                                                WCon{
                                                  +a21,
                                                  WCon{
                                                    +a22,
                                                    WCon{
                                                      +a23,
                                                      WCon{
                                                        +a24,
                                                        WCon{
                                                          +a25,
                                                          WCon{
                                                            +a26,
                                                            WCon{
                                                              +a27,
                                                              WCon{
                                                                +a28,
                                                                WCon{
                                                                  +a29,
                                                                  WCon{+a30, WCon{+a31, WNil{}}}
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
    }:
      match e:
        case U32{
          WCon{
            +b0,
            WCon{
              +b1,
              WCon{
                +b2,
                WCon{
                  +b3,
                  WCon{
                    +b4,
                    WCon{
                      +b5,
                      WCon{
                        +b6,
                        WCon{
                          +b7,
                          WCon{
                            +b8,
                            WCon{
                              +b9,
                              WCon{
                                +b10,
                                WCon{
                                  +b11,
                                  WCon{
                                    +b12,
                                    WCon{
                                      +b13,
                                      WCon{
                                        +b14,
                                        WCon{
                                          +b15,
                                          WCon{
                                            +b16,
                                            WCon{
                                              +b17,
                                              WCon{
                                                +b18,
                                                WCon{
                                                  +b19,
                                                  WCon{
                                                    +b20,
                                                    WCon{
                                                      +b21,
                                                      WCon{
                                                        +b22,
                                                        WCon{
                                                          +b23,
                                                          WCon{
                                                            +b24,
                                                            WCon{
                                                              +b25,
                                                              WCon{
                                                                +b26,
                                                                WCon{
                                                                  +b27,
                                                                  WCon{
                                                                    +b28,
                                                                    WCon{
                                                                      +b29,
                                                                      WCon{+b30, WCon{+b31, WNil{}}}
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
        }:
          {==}

def Hp.b8(
  +f0: U32,
  +e: U32
) -> {U32.and(U32.or(U32.and(f0, 255), U32.shln(e, 8n)), 256) == U32.shln(U32.and(e, 1), 8n): U32}:
  %Equal.sym(
    U32,
    U32.or(U32.and(f0, 255), U32.shln(e, 8n)),
    U.blend(f0, U32.shln(e, 8n), 255),
    U.hp(f0, e)
  ): {U32.and(_, 256) == U32.shln(U32.and(e, 1), 8n): U32}
  %Equal.sym(
    U32,
    U32.and(U.blend(f0, U32.shln(e, 8n), 255), 256),
    U.andm(U.blend(f0, U32.shln(e, 8n), 255), 256),
    U.am(U.blend(f0, U32.shln(e, 8n), 255), 256)
  ): {_ == U32.shln(U32.and(e, 1), 8n): U32}
  %Equal.sym(
    U32,
    U32.and(e, 1),
    U.andm(e, 1),
    U.am(e, 1)
  ): {U.andm(U.blend(f0, U32.shln(e, 8n), 255), 256) == U32.shln(_, 8n): U32}
  Hp.b8.f(f0, e)

def Hp.b9.f(
  f0: U32,
  e: U32
) -> {U.andm(U.blend(f0, U32.shln(e, 8n), 255), 512) == U32.shln(U.andm(e, 2), 8n): U32}:
  match f0:
    case U32{
      WCon{
        +a0,
        WCon{
          +a1,
          WCon{
            +a2,
            WCon{
              +a3,
              WCon{
                +a4,
                WCon{
                  +a5,
                  WCon{
                    +a6,
                    WCon{
                      +a7,
                      WCon{
                        +a8,
                        WCon{
                          +a9,
                          WCon{
                            +a10,
                            WCon{
                              +a11,
                              WCon{
                                +a12,
                                WCon{
                                  +a13,
                                  WCon{
                                    +a14,
                                    WCon{
                                      +a15,
                                      WCon{
                                        +a16,
                                        WCon{
                                          +a17,
                                          WCon{
                                            +a18,
                                            WCon{
                                              +a19,
                                              WCon{
                                                +a20,
                                                WCon{
                                                  +a21,
                                                  WCon{
                                                    +a22,
                                                    WCon{
                                                      +a23,
                                                      WCon{
                                                        +a24,
                                                        WCon{
                                                          +a25,
                                                          WCon{
                                                            +a26,
                                                            WCon{
                                                              +a27,
                                                              WCon{
                                                                +a28,
                                                                WCon{
                                                                  +a29,
                                                                  WCon{+a30, WCon{+a31, WNil{}}}
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
    }:
      match e:
        case U32{
          WCon{
            +b0,
            WCon{
              +b1,
              WCon{
                +b2,
                WCon{
                  +b3,
                  WCon{
                    +b4,
                    WCon{
                      +b5,
                      WCon{
                        +b6,
                        WCon{
                          +b7,
                          WCon{
                            +b8,
                            WCon{
                              +b9,
                              WCon{
                                +b10,
                                WCon{
                                  +b11,
                                  WCon{
                                    +b12,
                                    WCon{
                                      +b13,
                                      WCon{
                                        +b14,
                                        WCon{
                                          +b15,
                                          WCon{
                                            +b16,
                                            WCon{
                                              +b17,
                                              WCon{
                                                +b18,
                                                WCon{
                                                  +b19,
                                                  WCon{
                                                    +b20,
                                                    WCon{
                                                      +b21,
                                                      WCon{
                                                        +b22,
                                                        WCon{
                                                          +b23,
                                                          WCon{
                                                            +b24,
                                                            WCon{
                                                              +b25,
                                                              WCon{
                                                                +b26,
                                                                WCon{
                                                                  +b27,
                                                                  WCon{
                                                                    +b28,
                                                                    WCon{
                                                                      +b29,
                                                                      WCon{+b30, WCon{+b31, WNil{}}}
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
        }:
          {==}

def Hp.b9(
  +f0: U32,
  +e: U32
) -> {U32.and(U32.or(U32.and(f0, 255), U32.shln(e, 8n)), 512) == U32.shln(U32.and(e, 2), 8n): U32}:
  %Equal.sym(
    U32,
    U32.or(U32.and(f0, 255), U32.shln(e, 8n)),
    U.blend(f0, U32.shln(e, 8n), 255),
    U.hp(f0, e)
  ): {U32.and(_, 512) == U32.shln(U32.and(e, 2), 8n): U32}
  %Equal.sym(
    U32,
    U32.and(U.blend(f0, U32.shln(e, 8n), 255), 512),
    U.andm(U.blend(f0, U32.shln(e, 8n), 255), 512),
    U.am(U.blend(f0, U32.shln(e, 8n), 255), 512)
  ): {_ == U32.shln(U32.and(e, 2), 8n): U32}
  %Equal.sym(
    U32,
    U32.and(e, 2),
    U.andm(e, 2),
    U.am(e, 2)
  ): {U.andm(U.blend(f0, U32.shln(e, 8n), 255), 512) == U32.shln(_, 8n): U32}
  Hp.b9.f(f0, e)

def Hp.b10.f(
  f0: U32,
  e: U32
) -> {U.andm(U.blend(f0, U32.shln(e, 8n), 255), 1024) == U32.shln(U.andm(e, 4), 8n): U32}:
  match f0:
    case U32{
      WCon{
        +a0,
        WCon{
          +a1,
          WCon{
            +a2,
            WCon{
              +a3,
              WCon{
                +a4,
                WCon{
                  +a5,
                  WCon{
                    +a6,
                    WCon{
                      +a7,
                      WCon{
                        +a8,
                        WCon{
                          +a9,
                          WCon{
                            +a10,
                            WCon{
                              +a11,
                              WCon{
                                +a12,
                                WCon{
                                  +a13,
                                  WCon{
                                    +a14,
                                    WCon{
                                      +a15,
                                      WCon{
                                        +a16,
                                        WCon{
                                          +a17,
                                          WCon{
                                            +a18,
                                            WCon{
                                              +a19,
                                              WCon{
                                                +a20,
                                                WCon{
                                                  +a21,
                                                  WCon{
                                                    +a22,
                                                    WCon{
                                                      +a23,
                                                      WCon{
                                                        +a24,
                                                        WCon{
                                                          +a25,
                                                          WCon{
                                                            +a26,
                                                            WCon{
                                                              +a27,
                                                              WCon{
                                                                +a28,
                                                                WCon{
                                                                  +a29,
                                                                  WCon{+a30, WCon{+a31, WNil{}}}
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
    }:
      match e:
        case U32{
          WCon{
            +b0,
            WCon{
              +b1,
              WCon{
                +b2,
                WCon{
                  +b3,
                  WCon{
                    +b4,
                    WCon{
                      +b5,
                      WCon{
                        +b6,
                        WCon{
                          +b7,
                          WCon{
                            +b8,
                            WCon{
                              +b9,
                              WCon{
                                +b10,
                                WCon{
                                  +b11,
                                  WCon{
                                    +b12,
                                    WCon{
                                      +b13,
                                      WCon{
                                        +b14,
                                        WCon{
                                          +b15,
                                          WCon{
                                            +b16,
                                            WCon{
                                              +b17,
                                              WCon{
                                                +b18,
                                                WCon{
                                                  +b19,
                                                  WCon{
                                                    +b20,
                                                    WCon{
                                                      +b21,
                                                      WCon{
                                                        +b22,
                                                        WCon{
                                                          +b23,
                                                          WCon{
                                                            +b24,
                                                            WCon{
                                                              +b25,
                                                              WCon{
                                                                +b26,
                                                                WCon{
                                                                  +b27,
                                                                  WCon{
                                                                    +b28,
                                                                    WCon{
                                                                      +b29,
                                                                      WCon{+b30, WCon{+b31, WNil{}}}
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
        }:
          {==}

def Hp.b10(
  +f0: U32,
  +e: U32
) -> {U32.and(U32.or(U32.and(f0, 255), U32.shln(e, 8n)), 1024) == U32.shln(U32.and(e, 4), 8n): U32}:
  %Equal.sym(
    U32,
    U32.or(U32.and(f0, 255), U32.shln(e, 8n)),
    U.blend(f0, U32.shln(e, 8n), 255),
    U.hp(f0, e)
  ): {U32.and(_, 1024) == U32.shln(U32.and(e, 4), 8n): U32}
  %Equal.sym(
    U32,
    U32.and(U.blend(f0, U32.shln(e, 8n), 255), 1024),
    U.andm(U.blend(f0, U32.shln(e, 8n), 255), 1024),
    U.am(U.blend(f0, U32.shln(e, 8n), 255), 1024)
  ): {_ == U32.shln(U32.and(e, 4), 8n): U32}
  %Equal.sym(
    U32,
    U32.and(e, 4),
    U.andm(e, 4),
    U.am(e, 4)
  ): {U.andm(U.blend(f0, U32.shln(e, 8n), 255), 1024) == U32.shln(_, 8n): U32}
  Hp.b10.f(f0, e)

def Hp.fv.f(
  f0: U32,
  e: U32
) -> {U32.shrn(U.blend(f0, U32.shln(e, 8n), 255), 13n) == U.andm(U32.shrn(e, 5n), 524287): U32}:
  match f0:
    case U32{
      WCon{
        +a0,
        WCon{
          +a1,
          WCon{
            +a2,
            WCon{
              +a3,
              WCon{
                +a4,
                WCon{
                  +a5,
                  WCon{
                    +a6,
                    WCon{
                      +a7,
                      WCon{
                        +a8,
                        WCon{
                          +a9,
                          WCon{
                            +a10,
                            WCon{
                              +a11,
                              WCon{
                                +a12,
                                WCon{
                                  +a13,
                                  WCon{
                                    +a14,
                                    WCon{
                                      +a15,
                                      WCon{
                                        +a16,
                                        WCon{
                                          +a17,
                                          WCon{
                                            +a18,
                                            WCon{
                                              +a19,
                                              WCon{
                                                +a20,
                                                WCon{
                                                  +a21,
                                                  WCon{
                                                    +a22,
                                                    WCon{
                                                      +a23,
                                                      WCon{
                                                        +a24,
                                                        WCon{
                                                          +a25,
                                                          WCon{
                                                            +a26,
                                                            WCon{
                                                              +a27,
                                                              WCon{
                                                                +a28,
                                                                WCon{
                                                                  +a29,
                                                                  WCon{+a30, WCon{+a31, WNil{}}}
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
    }:
      match e:
        case U32{
          WCon{
            +b0,
            WCon{
              +b1,
              WCon{
                +b2,
                WCon{
                  +b3,
                  WCon{
                    +b4,
                    WCon{
                      +b5,
                      WCon{
                        +b6,
                        WCon{
                          +b7,
                          WCon{
                            +b8,
                            WCon{
                              +b9,
                              WCon{
                                +b10,
                                WCon{
                                  +b11,
                                  WCon{
                                    +b12,
                                    WCon{
                                      +b13,
                                      WCon{
                                        +b14,
                                        WCon{
                                          +b15,
                                          WCon{
                                            +b16,
                                            WCon{
                                              +b17,
                                              WCon{
                                                +b18,
                                                WCon{
                                                  +b19,
                                                  WCon{
                                                    +b20,
                                                    WCon{
                                                      +b21,
                                                      WCon{
                                                        +b22,
                                                        WCon{
                                                          +b23,
                                                          WCon{
                                                            +b24,
                                                            WCon{
                                                              +b25,
                                                              WCon{
                                                                +b26,
                                                                WCon{
                                                                  +b27,
                                                                  WCon{
                                                                    +b28,
                                                                    WCon{
                                                                      +b29,
                                                                      WCon{+b30, WCon{+b31, WNil{}}}
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
        }:
          {==}

def Hp.fv(
  +f0: U32,
  +e: U32
) -> {
  U32.shrn(U32.or(U32.and(f0, 255), U32.shln(e, 8n)), 13n) == U32.and(U32.shrn(e, 5n), 524287): U32
}:
  %Equal.sym(
    U32,
    U32.or(U32.and(f0, 255), U32.shln(e, 8n)),
    U.blend(f0, U32.shln(e, 8n), 255),
    U.hp(f0, e)
  ): {U32.shrn(_, 13n) == U32.and(U32.shrn(e, 5n), 524287): U32}
  %Equal.sym(
    U32,
    U32.and(U32.shrn(e, 5n), 524287),
    U.andm(U32.shrn(e, 5n), 524287),
    U.am(U32.shrn(e, 5n), 524287)
  ): {U32.shrn(U.blend(f0, U32.shln(e, 8n), 255), 13n) == _: U32}
  Hp.fv.f(f0, e)

# The finished header: or(and(x, 255), shl(cm, 13))
# -------------------------------------------------
def Hf.tag.f(
  x: U32,
  cm: U32
) -> {U.andm(U.blend(x, U32.shln(cm, 13n), 255), 63) == U.andm(x, 63): U32}:
  match x:
    case U32{
      WCon{
        +a0,
        WCon{
          +a1,
          WCon{
            +a2,
            WCon{
              +a3,
              WCon{
                +a4,
                WCon{
                  +a5,
                  WCon{
                    +a6,
                    WCon{
                      +a7,
                      WCon{
                        +a8,
                        WCon{
                          +a9,
                          WCon{
                            +a10,
                            WCon{
                              +a11,
                              WCon{
                                +a12,
                                WCon{
                                  +a13,
                                  WCon{
                                    +a14,
                                    WCon{
                                      +a15,
                                      WCon{
                                        +a16,
                                        WCon{
                                          +a17,
                                          WCon{
                                            +a18,
                                            WCon{
                                              +a19,
                                              WCon{
                                                +a20,
                                                WCon{
                                                  +a21,
                                                  WCon{
                                                    +a22,
                                                    WCon{
                                                      +a23,
                                                      WCon{
                                                        +a24,
                                                        WCon{
                                                          +a25,
                                                          WCon{
                                                            +a26,
                                                            WCon{
                                                              +a27,
                                                              WCon{
                                                                +a28,
                                                                WCon{
                                                                  +a29,
                                                                  WCon{+a30, WCon{+a31, WNil{}}}
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
    }:
      match cm:
        case U32{
          WCon{
            +b0,
            WCon{
              +b1,
              WCon{
                +b2,
                WCon{
                  +b3,
                  WCon{
                    +b4,
                    WCon{
                      +b5,
                      WCon{
                        +b6,
                        WCon{
                          +b7,
                          WCon{
                            +b8,
                            WCon{
                              +b9,
                              WCon{
                                +b10,
                                WCon{
                                  +b11,
                                  WCon{
                                    +b12,
                                    WCon{
                                      +b13,
                                      WCon{
                                        +b14,
                                        WCon{
                                          +b15,
                                          WCon{
                                            +b16,
                                            WCon{
                                              +b17,
                                              WCon{
                                                +b18,
                                                WCon{
                                                  +b19,
                                                  WCon{
                                                    +b20,
                                                    WCon{
                                                      +b21,
                                                      WCon{
                                                        +b22,
                                                        WCon{
                                                          +b23,
                                                          WCon{
                                                            +b24,
                                                            WCon{
                                                              +b25,
                                                              WCon{
                                                                +b26,
                                                                WCon{
                                                                  +b27,
                                                                  WCon{
                                                                    +b28,
                                                                    WCon{
                                                                      +b29,
                                                                      WCon{+b30, WCon{+b31, WNil{}}}
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
        }:
          {==}

def Hf.tag(
  +x: U32,
  +cm: U32
) -> {U32.and(U32.or(U32.and(x, 255), U32.shln(cm, 13n)), 63) == U32.and(x, 63): U32}:
  %Equal.sym(
    U32,
    U32.or(U32.and(x, 255), U32.shln(cm, 13n)),
    U.blend(x, U32.shln(cm, 13n), 255),
    U.hf(x, cm)
  ): {U32.and(_, 63) == U32.and(x, 63): U32}
  %Equal.sym(
    U32,
    U32.and(U.blend(x, U32.shln(cm, 13n), 255), 63),
    U.andm(U.blend(x, U32.shln(cm, 13n), 255), 63),
    U.am(U.blend(x, U32.shln(cm, 13n), 255), 63)
  ): {_ == U32.and(x, 63): U32}
  %Equal.sym(
    U32,
    U32.and(x, 63),
    U.andm(x, 63),
    U.am(x, 63)
  ): {U.andm(U.blend(x, U32.shln(cm, 13n), 255), 63) == _: U32}
  Hf.tag.f(x, cm)

def Hf.low.f(
  x: U32,
  cm: U32
) -> {U.andm(U.blend(x, U32.shln(cm, 13n), 255), 255) == U.andm(x, 255): U32}:
  match x:
    case U32{
      WCon{
        +a0,
        WCon{
          +a1,
          WCon{
            +a2,
            WCon{
              +a3,
              WCon{
                +a4,
                WCon{
                  +a5,
                  WCon{
                    +a6,
                    WCon{
                      +a7,
                      WCon{
                        +a8,
                        WCon{
                          +a9,
                          WCon{
                            +a10,
                            WCon{
                              +a11,
                              WCon{
                                +a12,
                                WCon{
                                  +a13,
                                  WCon{
                                    +a14,
                                    WCon{
                                      +a15,
                                      WCon{
                                        +a16,
                                        WCon{
                                          +a17,
                                          WCon{
                                            +a18,
                                            WCon{
                                              +a19,
                                              WCon{
                                                +a20,
                                                WCon{
                                                  +a21,
                                                  WCon{
                                                    +a22,
                                                    WCon{
                                                      +a23,
                                                      WCon{
                                                        +a24,
                                                        WCon{
                                                          +a25,
                                                          WCon{
                                                            +a26,
                                                            WCon{
                                                              +a27,
                                                              WCon{
                                                                +a28,
                                                                WCon{
                                                                  +a29,
                                                                  WCon{+a30, WCon{+a31, WNil{}}}
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
    }:
      match cm:
        case U32{
          WCon{
            +b0,
            WCon{
              +b1,
              WCon{
                +b2,
                WCon{
                  +b3,
                  WCon{
                    +b4,
                    WCon{
                      +b5,
                      WCon{
                        +b6,
                        WCon{
                          +b7,
                          WCon{
                            +b8,
                            WCon{
                              +b9,
                              WCon{
                                +b10,
                                WCon{
                                  +b11,
                                  WCon{
                                    +b12,
                                    WCon{
                                      +b13,
                                      WCon{
                                        +b14,
                                        WCon{
                                          +b15,
                                          WCon{
                                            +b16,
                                            WCon{
                                              +b17,
                                              WCon{
                                                +b18,
                                                WCon{
                                                  +b19,
                                                  WCon{
                                                    +b20,
                                                    WCon{
                                                      +b21,
                                                      WCon{
                                                        +b22,
                                                        WCon{
                                                          +b23,
                                                          WCon{
                                                            +b24,
                                                            WCon{
                                                              +b25,
                                                              WCon{
                                                                +b26,
                                                                WCon{
                                                                  +b27,
                                                                  WCon{
                                                                    +b28,
                                                                    WCon{
                                                                      +b29,
                                                                      WCon{+b30, WCon{+b31, WNil{}}}
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
        }:
          {==}

def Hf.low(
  +x: U32,
  +cm: U32
) -> {U32.and(U32.or(U32.and(x, 255), U32.shln(cm, 13n)), 255) == U32.and(x, 255): U32}:
  %Equal.sym(
    U32,
    U32.or(U32.and(x, 255), U32.shln(cm, 13n)),
    U.blend(x, U32.shln(cm, 13n), 255),
    U.hf(x, cm)
  ): {U32.and(_, 255) == U32.and(x, 255): U32}
  %Equal.sym(
    U32,
    U32.and(U.blend(x, U32.shln(cm, 13n), 255), 255),
    U.andm(U.blend(x, U32.shln(cm, 13n), 255), 255),
    U.am(U.blend(x, U32.shln(cm, 13n), 255), 255)
  ): {_ == U32.and(x, 255): U32}
  %Equal.sym(
    U32,
    U32.and(x, 255),
    U.andm(x, 255),
    U.am(x, 255)
  ): {U.andm(U.blend(x, U32.shln(cm, 13n), 255), 255) == _: U32}
  Hf.low.f(x, cm)

def Hf.q.f(
  x: U32,
  cm: U32
) -> {
  U.andm(U32.shrn(U.blend(x, U32.shln(cm, 13n), 255), 6n), 3) == U.andm(U32.shrn(x, 6n), 3): U32
}:
  match x:
    case U32{
      WCon{
        +a0,
        WCon{
          +a1,
          WCon{
            +a2,
            WCon{
              +a3,
              WCon{
                +a4,
                WCon{
                  +a5,
                  WCon{
                    +a6,
                    WCon{
                      +a7,
                      WCon{
                        +a8,
                        WCon{
                          +a9,
                          WCon{
                            +a10,
                            WCon{
                              +a11,
                              WCon{
                                +a12,
                                WCon{
                                  +a13,
                                  WCon{
                                    +a14,
                                    WCon{
                                      +a15,
                                      WCon{
                                        +a16,
                                        WCon{
                                          +a17,
                                          WCon{
                                            +a18,
                                            WCon{
                                              +a19,
                                              WCon{
                                                +a20,
                                                WCon{
                                                  +a21,
                                                  WCon{
                                                    +a22,
                                                    WCon{
                                                      +a23,
                                                      WCon{
                                                        +a24,
                                                        WCon{
                                                          +a25,
                                                          WCon{
                                                            +a26,
                                                            WCon{
                                                              +a27,
                                                              WCon{
                                                                +a28,
                                                                WCon{
                                                                  +a29,
                                                                  WCon{+a30, WCon{+a31, WNil{}}}
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
    }:
      match cm:
        case U32{
          WCon{
            +b0,
            WCon{
              +b1,
              WCon{
                +b2,
                WCon{
                  +b3,
                  WCon{
                    +b4,
                    WCon{
                      +b5,
                      WCon{
                        +b6,
                        WCon{
                          +b7,
                          WCon{
                            +b8,
                            WCon{
                              +b9,
                              WCon{
                                +b10,
                                WCon{
                                  +b11,
                                  WCon{
                                    +b12,
                                    WCon{
                                      +b13,
                                      WCon{
                                        +b14,
                                        WCon{
                                          +b15,
                                          WCon{
                                            +b16,
                                            WCon{
                                              +b17,
                                              WCon{
                                                +b18,
                                                WCon{
                                                  +b19,
                                                  WCon{
                                                    +b20,
                                                    WCon{
                                                      +b21,
                                                      WCon{
                                                        +b22,
                                                        WCon{
                                                          +b23,
                                                          WCon{
                                                            +b24,
                                                            WCon{
                                                              +b25,
                                                              WCon{
                                                                +b26,
                                                                WCon{
                                                                  +b27,
                                                                  WCon{
                                                                    +b28,
                                                                    WCon{
                                                                      +b29,
                                                                      WCon{+b30, WCon{+b31, WNil{}}}
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
        }:
          {==}

def Hf.q(
  +x: U32,
  +cm: U32
) -> {
  U32.and(
    U32.shrn(U32.or(U32.and(x, 255), U32.shln(cm, 13n)), 6n),
    3
  )
    == U32.and(U32.shrn(x, 6n), 3): U32
}:
  %Equal.sym(
    U32,
    U32.or(U32.and(x, 255), U32.shln(cm, 13n)),
    U.blend(x, U32.shln(cm, 13n), 255),
    U.hf(x, cm)
  ): {U32.and(U32.shrn(_, 6n), 3) == U32.and(U32.shrn(x, 6n), 3): U32}
  %Equal.sym(
    U32,
    U32.and(U32.shrn(U.blend(x, U32.shln(cm, 13n), 255), 6n), 3),
    U.andm(U32.shrn(U.blend(x, U32.shln(cm, 13n), 255), 6n), 3),
    U.am(U32.shrn(U.blend(x, U32.shln(cm, 13n), 255), 6n), 3)
  ): {_ == U32.and(U32.shrn(x, 6n), 3): U32}
  %Equal.sym(
    U32,
    U32.and(U32.shrn(x, 6n), 3),
    U.andm(U32.shrn(x, 6n), 3),
    U.am(U32.shrn(x, 6n), 3)
  ): {U.andm(U32.shrn(U.blend(x, U32.shln(cm, 13n), 255), 6n), 3) == _: U32}
  Hf.q.f(x, cm)

def Hf.todo.f(x: U32, cm: U32) -> {U.andm(U.blend(x, U32.shln(cm, 13n), 255), 1792) == 0: U32}:
  match x:
    case U32{
      WCon{
        +a0,
        WCon{
          +a1,
          WCon{
            +a2,
            WCon{
              +a3,
              WCon{
                +a4,
                WCon{
                  +a5,
                  WCon{
                    +a6,
                    WCon{
                      +a7,
                      WCon{
                        +a8,
                        WCon{
                          +a9,
                          WCon{
                            +a10,
                            WCon{
                              +a11,
                              WCon{
                                +a12,
                                WCon{
                                  +a13,
                                  WCon{
                                    +a14,
                                    WCon{
                                      +a15,
                                      WCon{
                                        +a16,
                                        WCon{
                                          +a17,
                                          WCon{
                                            +a18,
                                            WCon{
                                              +a19,
                                              WCon{
                                                +a20,
                                                WCon{
                                                  +a21,
                                                  WCon{
                                                    +a22,
                                                    WCon{
                                                      +a23,
                                                      WCon{
                                                        +a24,
                                                        WCon{
                                                          +a25,
                                                          WCon{
                                                            +a26,
                                                            WCon{
                                                              +a27,
                                                              WCon{
                                                                +a28,
                                                                WCon{
                                                                  +a29,
                                                                  WCon{+a30, WCon{+a31, WNil{}}}
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
    }:
      match cm:
        case U32{
          WCon{
            +b0,
            WCon{
              +b1,
              WCon{
                +b2,
                WCon{
                  +b3,
                  WCon{
                    +b4,
                    WCon{
                      +b5,
                      WCon{
                        +b6,
                        WCon{
                          +b7,
                          WCon{
                            +b8,
                            WCon{
                              +b9,
                              WCon{
                                +b10,
                                WCon{
                                  +b11,
                                  WCon{
                                    +b12,
                                    WCon{
                                      +b13,
                                      WCon{
                                        +b14,
                                        WCon{
                                          +b15,
                                          WCon{
                                            +b16,
                                            WCon{
                                              +b17,
                                              WCon{
                                                +b18,
                                                WCon{
                                                  +b19,
                                                  WCon{
                                                    +b20,
                                                    WCon{
                                                      +b21,
                                                      WCon{
                                                        +b22,
                                                        WCon{
                                                          +b23,
                                                          WCon{
                                                            +b24,
                                                            WCon{
                                                              +b25,
                                                              WCon{
                                                                +b26,
                                                                WCon{
                                                                  +b27,
                                                                  WCon{
                                                                    +b28,
                                                                    WCon{
                                                                      +b29,
                                                                      WCon{+b30, WCon{+b31, WNil{}}}
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
        }:
          {==}

def Hf.todo(
  +x: U32,
  +cm: U32
) -> {U32.and(U32.or(U32.and(x, 255), U32.shln(cm, 13n)), 1792) == 0: U32}:
  %Equal.sym(
    U32,
    U32.or(U32.and(x, 255), U32.shln(cm, 13n)),
    U.blend(x, U32.shln(cm, 13n), 255),
    U.hf(x, cm)
  ): {U32.and(_, 1792) == 0: U32}
  %Equal.sym(
    U32,
    U32.and(U.blend(x, U32.shln(cm, 13n), 255), 1792),
    U.andm(U.blend(x, U32.shln(cm, 13n), 255), 1792),
    U.am(U.blend(x, U32.shln(cm, 13n), 255), 1792)
  ): {_ == 0: U32}
  Hf.todo.f(x, cm)

def Hf.fv.f(
  x: U32,
  cm: U32
) -> {U32.shrn(U.blend(x, U32.shln(cm, 13n), 255), 13n) == U.andm(cm, 524287): U32}:
  match x:
    case U32{
      WCon{
        +a0,
        WCon{
          +a1,
          WCon{
            +a2,
            WCon{
              +a3,
              WCon{
                +a4,
                WCon{
                  +a5,
                  WCon{
                    +a6,
                    WCon{
                      +a7,
                      WCon{
                        +a8,
                        WCon{
                          +a9,
                          WCon{
                            +a10,
                            WCon{
                              +a11,
                              WCon{
                                +a12,
                                WCon{
                                  +a13,
                                  WCon{
                                    +a14,
                                    WCon{
                                      +a15,
                                      WCon{
                                        +a16,
                                        WCon{
                                          +a17,
                                          WCon{
                                            +a18,
                                            WCon{
                                              +a19,
                                              WCon{
                                                +a20,
                                                WCon{
                                                  +a21,
                                                  WCon{
                                                    +a22,
                                                    WCon{
                                                      +a23,
                                                      WCon{
                                                        +a24,
                                                        WCon{
                                                          +a25,
                                                          WCon{
                                                            +a26,
                                                            WCon{
                                                              +a27,
                                                              WCon{
                                                                +a28,
                                                                WCon{
                                                                  +a29,
                                                                  WCon{+a30, WCon{+a31, WNil{}}}
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
    }:
      match cm:
        case U32{
          WCon{
            +b0,
            WCon{
              +b1,
              WCon{
                +b2,
                WCon{
                  +b3,
                  WCon{
                    +b4,
                    WCon{
                      +b5,
                      WCon{
                        +b6,
                        WCon{
                          +b7,
                          WCon{
                            +b8,
                            WCon{
                              +b9,
                              WCon{
                                +b10,
                                WCon{
                                  +b11,
                                  WCon{
                                    +b12,
                                    WCon{
                                      +b13,
                                      WCon{
                                        +b14,
                                        WCon{
                                          +b15,
                                          WCon{
                                            +b16,
                                            WCon{
                                              +b17,
                                              WCon{
                                                +b18,
                                                WCon{
                                                  +b19,
                                                  WCon{
                                                    +b20,
                                                    WCon{
                                                      +b21,
                                                      WCon{
                                                        +b22,
                                                        WCon{
                                                          +b23,
                                                          WCon{
                                                            +b24,
                                                            WCon{
                                                              +b25,
                                                              WCon{
                                                                +b26,
                                                                WCon{
                                                                  +b27,
                                                                  WCon{
                                                                    +b28,
                                                                    WCon{
                                                                      +b29,
                                                                      WCon{+b30, WCon{+b31, WNil{}}}
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
        }:
          {==}

def Hf.fv(
  +x: U32,
  +cm: U32
) -> {U32.shrn(U32.or(U32.and(x, 255), U32.shln(cm, 13n)), 13n) == U32.and(cm, 524287): U32}:
  %Equal.sym(
    U32,
    U32.or(U32.and(x, 255), U32.shln(cm, 13n)),
    U.blend(x, U32.shln(cm, 13n), 255),
    U.hf(x, cm)
  ): {U32.shrn(_, 13n) == U32.and(cm, 524287): U32}
  %Equal.sym(
    U32,
    U32.and(cm, 524287),
    U.andm(cm, 524287),
    U.am(cm, 524287)
  ): {U32.shrn(U.blend(x, U32.shln(cm, 13n), 255), 13n) == _: U32}
  Hf.fv.f(x, cm)

# A frame's header: or(h, shl(T, 8)), h its low byte
# --------------------------------------------------
def Hw.tag(
  +h: U32,
  +T: U32,
  +hh: {U32.and(h, 255) == h: U32}
) -> {U32.and(U32.or(h, U32.shln(T, 8n)), 63) == U32.and(h, 63): U32}:
  %hh: {U32.and(U32.or(_, U32.shln(T, 8n)), 63) == U32.and(h, 63): U32}
  Hp.tag(h, T)

def Hw.low(
  +h: U32,
  +T: U32,
  +hh: {U32.and(h, 255) == h: U32}
) -> {U32.and(U32.or(h, U32.shln(T, 8n)), 255) == h: U32}:
  %hh: {U32.and(U32.or(h, U32.shln(T, 8n)), 255) == _: U32}
  %hh: {U32.and(U32.or(_, U32.shln(T, 8n)), 255) == U32.and(h, 255): U32}
  Hp.low(h, T)

def Hw.q(
  +h: U32,
  +T: U32,
  +hh: {U32.and(h, 255) == h: U32}
) -> {U32.and(U32.shrn(U32.or(h, U32.shln(T, 8n)), 6n), 3) == U32.and(U32.shrn(h, 6n), 3): U32}:
  %hh: {U32.and(U32.shrn(U32.or(_, U32.shln(T, 8n)), 6n), 3) == U32.and(U32.shrn(h, 6n), 3): U32}
  Hp.q(h, T)

def Hw.todo(
  +h: U32,
  +T: U32,
  +hh: {U32.and(h, 255) == h: U32}
) -> {U32.and(U32.or(h, U32.shln(T, 8n)), 1792) == U32.shln(U32.and(T, 7), 8n): U32}:
  %hh: {U32.and(U32.or(_, U32.shln(T, 8n)), 1792) == U32.shln(U32.and(T, 7), 8n): U32}
  Hp.todo(h, T)

def Hw.b8(
  +h: U32,
  +T: U32,
  +hh: {U32.and(h, 255) == h: U32}
) -> {U32.and(U32.or(h, U32.shln(T, 8n)), 256) == U32.shln(U32.and(T, 1), 8n): U32}:
  %hh: {U32.and(U32.or(_, U32.shln(T, 8n)), 256) == U32.shln(U32.and(T, 1), 8n): U32}
  Hp.b8(h, T)

def Hw.b9(
  +h: U32,
  +T: U32,
  +hh: {U32.and(h, 255) == h: U32}
) -> {U32.and(U32.or(h, U32.shln(T, 8n)), 512) == U32.shln(U32.and(T, 2), 8n): U32}:
  %hh: {U32.and(U32.or(_, U32.shln(T, 8n)), 512) == U32.shln(U32.and(T, 2), 8n): U32}
  Hp.b9(h, T)

def Hw.b10(
  +h: U32,
  +T: U32,
  +hh: {U32.and(h, 255) == h: U32}
) -> {U32.and(U32.or(h, U32.shln(T, 8n)), 1024) == U32.shln(U32.and(T, 4), 8n): U32}:
  %hh: {U32.and(U32.or(_, U32.shln(T, 8n)), 1024) == U32.shln(U32.and(T, 4), 8n): U32}
  Hp.b10(h, T)

def Hw.fv(
  +h: U32,
  +T: U32,
  +hh: {U32.and(h, 255) == h: U32}
) -> {U32.shrn(U32.or(h, U32.shln(T, 8n)), 13n) == U32.and(U32.shrn(T, 5n), 524287): U32}:
  %hh: {U32.shrn(U32.or(_, U32.shln(T, 8n)), 13n) == U32.and(U32.shrn(T, 5n), 524287): U32}
  Hp.fv(h, T)

# M.pick
# ------
def U.orm(+x: U32, +m: U32) -> U32:
  U32{L.Word.orm(32n, U.w(x), U.w(m))}

def U.om(x: U32, m: U32) -> {U32.or(x, m) == U.orm(x, m): U32}:
  match x m:
    case U32{a} U32{b}:
      Equal.cong(
        Word(32n),
        U32,
        u => U32{u},
        Word.or(32n, a, b),
        L.Word.orm(32n, a, b),
        L.Word.or_is_orm(32n, a, b)
      )

def Pk.f1(a: U32, b: U32) -> {U.orm(U.andm(a, U32.sub(0, 1)), U.andm(b, U32.sub(1, 1))) == a: U32}:
  match a:
    case U32{
      WCon{
        +a0,
        WCon{
          +a1,
          WCon{
            +a2,
            WCon{
              +a3,
              WCon{
                +a4,
                WCon{
                  +a5,
                  WCon{
                    +a6,
                    WCon{
                      +a7,
                      WCon{
                        +a8,
                        WCon{
                          +a9,
                          WCon{
                            +a10,
                            WCon{
                              +a11,
                              WCon{
                                +a12,
                                WCon{
                                  +a13,
                                  WCon{
                                    +a14,
                                    WCon{
                                      +a15,
                                      WCon{
                                        +a16,
                                        WCon{
                                          +a17,
                                          WCon{
                                            +a18,
                                            WCon{
                                              +a19,
                                              WCon{
                                                +a20,
                                                WCon{
                                                  +a21,
                                                  WCon{
                                                    +a22,
                                                    WCon{
                                                      +a23,
                                                      WCon{
                                                        +a24,
                                                        WCon{
                                                          +a25,
                                                          WCon{
                                                            +a26,
                                                            WCon{
                                                              +a27,
                                                              WCon{
                                                                +a28,
                                                                WCon{
                                                                  +a29,
                                                                  WCon{+a30, WCon{+a31, WNil{}}}
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
    }:
      match b:
        case U32{
          WCon{
            +b0,
            WCon{
              +b1,
              WCon{
                +b2,
                WCon{
                  +b3,
                  WCon{
                    +b4,
                    WCon{
                      +b5,
                      WCon{
                        +b6,
                        WCon{
                          +b7,
                          WCon{
                            +b8,
                            WCon{
                              +b9,
                              WCon{
                                +b10,
                                WCon{
                                  +b11,
                                  WCon{
                                    +b12,
                                    WCon{
                                      +b13,
                                      WCon{
                                        +b14,
                                        WCon{
                                          +b15,
                                          WCon{
                                            +b16,
                                            WCon{
                                              +b17,
                                              WCon{
                                                +b18,
                                                WCon{
                                                  +b19,
                                                  WCon{
                                                    +b20,
                                                    WCon{
                                                      +b21,
                                                      WCon{
                                                        +b22,
                                                        WCon{
                                                          +b23,
                                                          WCon{
                                                            +b24,
                                                            WCon{
                                                              +b25,
                                                              WCon{
                                                                +b26,
                                                                WCon{
                                                                  +b27,
                                                                  WCon{
                                                                    +b28,
                                                                    WCon{
                                                                      +b29,
                                                                      WCon{+b30, WCon{+b31, WNil{}}}
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
        }:
          {==}

def Pk.f0z(
  a: U32,
  b: U32
) -> {U32.or(U.andm(a, U32.sub(0, 0)), U.andm(b, U32.sub(0, 1))) == b: U32}:
  match a:
    case U32{
      WCon{
        +a0,
        WCon{
          +a1,
          WCon{
            +a2,
            WCon{
              +a3,
              WCon{
                +a4,
                WCon{
                  +a5,
                  WCon{
                    +a6,
                    WCon{
                      +a7,
                      WCon{
                        +a8,
                        WCon{
                          +a9,
                          WCon{
                            +a10,
                            WCon{
                              +a11,
                              WCon{
                                +a12,
                                WCon{
                                  +a13,
                                  WCon{
                                    +a14,
                                    WCon{
                                      +a15,
                                      WCon{
                                        +a16,
                                        WCon{
                                          +a17,
                                          WCon{
                                            +a18,
                                            WCon{
                                              +a19,
                                              WCon{
                                                +a20,
                                                WCon{
                                                  +a21,
                                                  WCon{
                                                    +a22,
                                                    WCon{
                                                      +a23,
                                                      WCon{
                                                        +a24,
                                                        WCon{
                                                          +a25,
                                                          WCon{
                                                            +a26,
                                                            WCon{
                                                              +a27,
                                                              WCon{
                                                                +a28,
                                                                WCon{
                                                                  +a29,
                                                                  WCon{+a30, WCon{+a31, WNil{}}}
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
    }:
      match b:
        case U32{
          WCon{
            +b0,
            WCon{
              +b1,
              WCon{
                +b2,
                WCon{
                  +b3,
                  WCon{
                    +b4,
                    WCon{
                      +b5,
                      WCon{
                        +b6,
                        WCon{
                          +b7,
                          WCon{
                            +b8,
                            WCon{
                              +b9,
                              WCon{
                                +b10,
                                WCon{
                                  +b11,
                                  WCon{
                                    +b12,
                                    WCon{
                                      +b13,
                                      WCon{
                                        +b14,
                                        WCon{
                                          +b15,
                                          WCon{
                                            +b16,
                                            WCon{
                                              +b17,
                                              WCon{
                                                +b18,
                                                WCon{
                                                  +b19,
                                                  WCon{
                                                    +b20,
                                                    WCon{
                                                      +b21,
                                                      WCon{
                                                        +b22,
                                                        WCon{
                                                          +b23,
                                                          WCon{
                                                            +b24,
                                                            WCon{
                                                              +b25,
                                                              WCon{
                                                                +b26,
                                                                WCon{
                                                                  +b27,
                                                                  WCon{
                                                                    +b28,
                                                                    WCon{
                                                                      +b29,
                                                                      WCon{+b30, WCon{+b31, WNil{}}}
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
        }:
          {==}

# M.pick(1, a, b) is a: or(and(a, 0 - 1), and(b, 1 - 1))
def Pk.one(
  +a: U32,
  +b: U32
) -> {U32.or(U32.and(a, U32.sub(0, 1)), U32.and(b, U32.sub(1, 1))) == a: U32}:
  %Equal.sym(
    U32,
    U32.and(a, U32.sub(0, 1)),
    U.andm(a, U32.sub(0, 1)),
    U.am(a, U32.sub(0, 1))
  ): {U32.or(_, U32.and(b, U32.sub(1, 1))) == a: U32}
  %Equal.sym(
    U32,
    U32.and(b, U32.sub(1, 1)),
    U.andm(b, U32.sub(1, 1)),
    U.am(b, U32.sub(1, 1))
  ): {U32.or(U.andm(a, U32.sub(0, 1)), _) == a: U32}
  %Equal.sym(
    U32,
    U32.or(U.andm(a, U32.sub(0, 1)), U.andm(b, U32.sub(1, 1))),
    U.orm(U.andm(a, U32.sub(0, 1)), U.andm(b, U32.sub(1, 1))),
    U.om(U.andm(a, U32.sub(0, 1)), U.andm(b, U32.sub(1, 1)))
  ): {_ == a: U32}
  Pk.f1(a, b)

# M.pick(0, a, b) is b: or(and(a, 0 - 0), and(b, 0 - 1))
def Pk.zero(
  +a: U32,
  +b: U32
) -> {U32.or(U32.and(a, U32.sub(0, 0)), U32.and(b, U32.sub(0, 1))) == b: U32}:
  %Equal.sym(
    U32,
    U32.and(a, U32.sub(0, 0)),
    U.andm(a, U32.sub(0, 0)),
    U.am(a, U32.sub(0, 0))
  ): {U32.or(_, U32.and(b, U32.sub(0, 1))) == b: U32}
  %Equal.sym(
    U32,
    U32.and(b, U32.sub(0, 1)),
    U.andm(b, U32.sub(0, 1)),
    U.am(b, U32.sub(0, 1))
  ): {U32.or(U.andm(a, U32.sub(0, 0)), _) == b: U32}
  Pk.f0z(a, b)
