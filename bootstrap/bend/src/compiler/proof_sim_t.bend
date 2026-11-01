import Base
import ./impl.bend as C

def recomp(+v: U32) -> U32:
  U32.or(U32.or(U32.or(U32.and(v, 255), U32.shln(U32.and(U32.shrn(v, 8n), 255), 8n)),
    U32.shln(U32.and(U32.shrn(v, 16n), 255), 16n)), U32.shln(U32.shrn(v, 24n), 24n))

def t(+w: Word(32n)) -> {recomp(U32{w}) == U32{w} : U32}:
  match w:
    case WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, WCon{+b6, WCon{+b7, WCon{+b8, WCon{+b9, WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WCon{+b16, WCon{+b17, WCon{+b18, WCon{+b19, WCon{+b20, WCon{+b21, WCon{+b22, WCon{+b23, WCon{+b24, WCon{+b25, WCon{+b26, WCon{+b27, WCon{+b28, WCon{+b29, WCon{+b30, WCon{+b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}
