import Base
import ./impl.bend as C
import ./proof_term.bend as T
import ./proof_need.bend as PN

# Kit
# ---

def isQ1(q: C.Quan) -> Bool:
  match q:
    case C.Quan.Q1{}:
      True{}
    case _:
      False{}

# the test of M.pair on field 0 of a cell
def FP.l(+f0: U32) -> Bool:
  U32.is_eq(U32.and(f0, 255), 74)

# tag 10 at quantity 1
def FP.r(+f0: U32) -> Bool:
  Bool.and(isQ1(T.tm.quan(U32.and(U32.shrn(f0, 6n), 3))), U32.is_eq(U32.and(f0, 63), 10))

def FPS(+f0: U32) -> Type:
  {FP.l(f0) == FP.r(f0) : Bool}

def fp.h7(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b6 b7:
    case _ True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      {==}

def fp.h8(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b8:
    case True{}:
      fp.h7(b0, b1, b2, b3, b4, b5, b6, b7)
    case False{}:
      fp.h7(b0, b1, b2, b3, b4, b5, b6, b7)

def fp.h9(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b9:
    case True{}:
      fp.h8(b0, b1, b2, b3, b4, b5, b6, b7, b8)
    case False{}:
      fp.h8(b0, b1, b2, b3, b4, b5, b6, b7, b8)

def fp.h10(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b10:
    case True{}:
      fp.h9(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9)
    case False{}:
      fp.h9(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9)

def fp.h11(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b11:
    case True{}:
      fp.h10(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10)
    case False{}:
      fp.h10(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10)

def fp.h12(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b12:
    case True{}:
      fp.h11(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11)
    case False{}:
      fp.h11(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11)

def fp.h13(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b13:
    case True{}:
      fp.h12(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12)
    case False{}:
      fp.h12(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12)

def fp.h14(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b14:
    case True{}:
      fp.h13(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13)
    case False{}:
      fp.h13(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13)

def fp.h15(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b15:
    case True{}:
      fp.h14(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14)
    case False{}:
      fp.h14(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14)

def fp.h16(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b16:
    case True{}:
      fp.h15(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15)
    case False{}:
      fp.h15(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15)

def fp.h17(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b17:
    case True{}:
      fp.h16(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16)
    case False{}:
      fp.h16(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16)

def fp.h18(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b18:
    case True{}:
      fp.h17(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17)
    case False{}:
      fp.h17(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17)

def fp.h19(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b19:
    case True{}:
      fp.h18(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18)
    case False{}:
      fp.h18(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18)

def fp.h20(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b20:
    case True{}:
      fp.h19(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19)
    case False{}:
      fp.h19(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19)

def fp.h21(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b21:
    case True{}:
      fp.h20(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20)
    case False{}:
      fp.h20(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20)

def fp.h22(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b22:
    case True{}:
      fp.h21(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21)
    case False{}:
      fp.h21(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21)

def fp.h23(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b23:
    case True{}:
      fp.h22(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22)
    case False{}:
      fp.h22(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22)

def fp.h24(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b24:
    case True{}:
      fp.h23(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23)
    case False{}:
      fp.h23(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23)

def fp.h25(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b25:
    case True{}:
      fp.h24(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24)
    case False{}:
      fp.h24(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24)

def fp.h26(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b26:
    case True{}:
      fp.h25(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25)
    case False{}:
      fp.h25(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25)

def fp.h27(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b27:
    case True{}:
      fp.h26(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26)
    case False{}:
      fp.h26(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26)

def fp.h28(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, +b28: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b28:
    case True{}:
      fp.h27(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27)
    case False{}:
      fp.h27(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27)

def fp.h29(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, +b28: Bool, +b29: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b29:
    case True{}:
      fp.h28(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28)
    case False{}:
      fp.h28(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28)

def fp.h30(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, +b28: Bool, +b29: Bool, +b30: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b30:
    case True{}:
      fp.h29(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29)
    case False{}:
      fp.h29(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29)

def fp.h31(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, +b28: Bool, +b29: Bool, +b30: Bool, +b31: Bool) -> FPS(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b31:
    case True{}:
      fp.h30(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30)
    case False{}:
      fp.h30(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30)

# the pair test of a cell's field 0 is its tag's and its quantity's
def fp(+f0: U32) -> FPS(f0):
  match f0:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, WCon{+b6, WCon{+b7, WCon{+b8, WCon{+b9, WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WCon{+b16, WCon{+b17, WCon{+b18, WCon{+b19, WCon{+b20, WCon{+b21, WCon{+b22, WCon{+b23, WCon{+b24, WCon{+b25, WCon{+b26, WCon{+b27, WCon{+b28, WCon{+b29, WCon{+b30, WCon{+b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      fp.h31(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31)
# Words
# -----

# the word of n bits all 0
def zeros(n: Nat) -> Word(n):
  PN.ones(n, 0n)

# the k bits a below the n bits b
def cat(k: Nat, -n: Nat, a: Word(k), b: Word(n)) -> Word(Nat.add(k, n)):
  match k:
    case 0n:
      b
    case 1n+p:
      match a:
        case WCon{x, t}:
          WCon{x, cat(p, n, t, b)}

def or_false(b: Bool) -> {b == Bool.or(b, False{}) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def and_true(b: Bool) -> {b == Bool.and(b, True{}) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def and_false(b: Bool) -> {False{} == Bool.and(b, False{}) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# an or with 0 below keeps the low bits
def or_cat(k: Nat, +n: Nat, a: Word(k), +b: Word(n), +c: Word(n)) ->
  {Word.or(Nat.add(k, n), cat(k, n, a, b), cat(k, n, zeros(k), c)) == cat(k, n, a, Word.or(n, b, c)) : Word(Nat.add(k, n))}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      match a:
        case WCon{+x, +t}:
          %or_false(x) : {WCon{_, Word.or(Nat.add(p, n), cat(p, n, t, b), cat(p, n, zeros(p), c))} == WCon{x, cat(p, n, t, Word.or(n, b, c))} : Word(1n+Nat.add(p, n))}
          %Equal.sym(Word(Nat.add(p, n)), Word.or(Nat.add(p, n), cat(p, n, t, b), cat(p, n, zeros(p), c)), cat(p, n, t, Word.or(n, b, c)), or_cat(p, n, t, b, c)) : {WCon{x, _} == WCon{x, cat(p, n, t, Word.or(n, b, c))} : Word(1n+Nat.add(p, n))}
          {==}

# 0 and anything is 0
def zeros_and(+n: Nat, w: Word(n)) -> {Word.and(n, zeros(n), w) == zeros(n) : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{x, t}:
          %Equal.sym(Word(p), Word.and(p, zeros(p), t), zeros(p), zeros_and(p, t)) : {WCon{False{}, _} == zeros(1n+p) : Word(1n+p)}
          {==}

# an and with the k low bits set keeps the k low bits, above 0
def and_cat(k: Nat, +n: Nat, a: Word(k)) ->
  {Word.and(Nat.add(k, n), cat(k, n, a, zeros(n)), PN.ones(Nat.add(k, n), k)) == cat(k, n, a, zeros(n)) : Word(Nat.add(k, n))}:
  match k:
    case 0n:
      zeros_and(n, PN.ones(n, 0n))
    case 1n+p:
      match a:
        case WCon{+x, +t}:
          %and_true(x) : {WCon{_, Word.and(Nat.add(p, n), cat(p, n, t, zeros(n)), PN.ones(Nat.add(p, n), p))} == WCon{x, cat(p, n, t, zeros(n))} : Word(1n+Nat.add(p, n))}
          %Equal.sym(Word(Nat.add(p, n)), Word.and(Nat.add(p, n), cat(p, n, t, zeros(n)), PN.ones(Nat.add(p, n), p)), cat(p, n, t, zeros(n)), and_cat(p, n, t)) : {WCon{x, _} == WCon{x, cat(p, n, t, zeros(n))} : Word(1n+Nat.add(p, n))}
          {==}

# a comparison with 0 is never LT
def nolt.fin(c: Cmp, +b: Bool, +e: {Cmp.is_lt(c) == False{} : Bool}) -> {Cmp.is_lt(Word.cmp.fin(b, False{}, c)) == False{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({Cmp.is_lt(Word.cmp.fin(b, False{}, LT{})) == False{} : Bool}, PN.true_ne_false(e))
    case EQ{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case GT{}:
      {==}

def nolt(+n: Nat, w: Word(n)) -> {Cmp.is_lt(Word.cmp(n, w, zeros(n))) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{+x, +t}:
          nolt.fin(Word.cmp(p, t, zeros(p)), x, nolt(p, t))

# The term side
# -------------
#
# Program.unbytes and Program.unword read a term by one nested pattern. U and
# Wd read it as the machine does, one cell at a time, in the machine's order:
# V1 views a pair at quantity 1, VL a label.

type TP is Data:
  TP{a: C.Term, b: C.Term}

def V1(t: C.Term) -> Maybe<&2, TP>:
  match t:
    case C.Term.Tup{C.Quan.Q1{}, a, b}:
      Some{TP{a, b}}
    case _:
      None{}

def VL(t: C.Term) -> Maybe<&2, List<&2, U32>>:
  match t:
    case C.Term.Lab{k}:
      Some{k}
    case _:
      None{}

def U.c12(v: U32, mr: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match mr:
    case Some{bs}:
      Some{Con{v, bs}}
    case None{}:
      None{}

def U.c11(lt: Bool, v: U32, mr: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match lt:
    case True{}:
      U.c12(v, mr)
    case False{}:
      None{}

def U.c10(mw: Maybe<&2, Word(32n)>, rest: C.Term) -> Maybe<&2, List<&2, U32>>:
  match mw:
    case Some{+x}:
      U.c11(U32.is_lt(U32{x}, 256), U32{x}, C.Program.unbytes(rest))
    case None{}:
      None{}

def U.c9(ok: Bool, w: C.Term, rest: C.Term) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      U.c10(C.Program.unword(32n, w), rest)
    case False{}:
      None{}

def U.c8(m: Maybe<&2, List<&2, U32>>, w: C.Term, rest: C.Term) -> Maybe<&2, List<&2, U32>>:
  match m:
    case Some{u1}:
      U.c9(C.Name.is_eq(u1, C.Program.name.unit()), w, rest)
    case None{}:
      None{}

def U.c7(m: Maybe<&2, TP>, rest: C.Term) -> Maybe<&2, List<&2, U32>>:
  match m:
    case Some{TP{w, l1}}:
      U.c8(VL(l1), w, rest)
    case None{}:
      None{}

def U.c6(ok: Bool, wt: C.Term, rest: C.Term) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      U.c7(V1(wt), rest)
    case False{}:
      None{}

def U.c5(m: Maybe<&2, List<&2, U32>>, wt: C.Term, rest: C.Term) -> Maybe<&2, List<&2, U32>>:
  match m:
    case Some{c}:
      U.c6(C.Name.is_eq(c, C.Program.name.u32()), wt, rest)
    case None{}:
      None{}

def U.c4(m: Maybe<&2, TP>, rest: C.Term) -> Maybe<&2, List<&2, U32>>:
  match m:
    case Some{TP{cl, wt}}:
      U.c5(VL(cl), wt, rest)
    case None{}:
      None{}

def U.c3(ok: Bool, x: C.Term, rest: C.Term) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      U.c4(V1(x), rest)
    case False{}:
      None{}

def U.c2(x: C.Term, rest: C.Term, m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case Some{u2}:
      U.c3(C.Name.is_eq(u2, C.Program.name.unit()), x, rest)
    case None{}:
      None{}

def U.c1(x: C.Term, m: Maybe<&2, TP>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case Some{TP{rest, z}}:
      U.c2(x, rest, VL(z))
    case None{}:
      None{}

def U.con(m: Maybe<&2, TP>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case Some{TP{x, y}}:
      U.c1(x, V1(y))
    case None{}:
      None{}

def U.nil(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case Some{u}:
      C.Program.unbytes.nil(C.Name.is_eq(u, C.Program.name.unit()))
    case None{}:
      None{}

def U.k2(iscon: Bool, b: C.Term) -> Maybe<&2, List<&2, U32>>:
  match iscon:
    case True{}:
      U.con(V1(b))
    case False{}:
      None{}

def U.k(isnil: Bool, iscon: Bool, b: C.Term) -> Maybe<&2, List<&2, U32>>:
  match isnil:
    case True{}:
      U.nil(VL(b))
    case False{}:
      U.k2(iscon, b)

def U.a(m: Maybe<&2, List<&2, U32>>, b: C.Term) -> Maybe<&2, List<&2, U32>>:
  match m:
    case Some{+k}:
      U.k(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b)
    case None{}:
      None{}

def U.r(m: Maybe<&2, TP>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case Some{TP{a, b}}:
      U.a(VL(a), b)
    case None{}:
      None{}

# the bytes of t, read in the machine's order
def U(t: C.Term) -> Maybe<&2, List<&2, U32>>:
  U.r(V1(t))

# a bit, read in the machine's order
def Ub.x(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Bool>:
  match m:
    case Some{b}:
      C.Program.unbit(b)
    case None{}:
      None{}

def Ub.u(ok: Bool, x: C.Term) -> Maybe<&2, Bool>:
  match ok:
    case True{}:
      Ub.x(VL(x))
    case False{}:
      None{}

def Ub.y(m: Maybe<&2, List<&2, U32>>, x: C.Term) -> Maybe<&2, Bool>:
  match m:
    case Some{u}:
      Ub.u(C.Name.is_eq(u, C.Program.name.unit()), x)
    case None{}:
      None{}

def Ub.r(m: Maybe<&2, TP>) -> Maybe<&2, Bool>:
  match m:
    case Some{TP{x, y}}:
      Ub.y(VL(y), x)
    case None{}:
      None{}

def Ub(t: C.Term) -> Maybe<&2, Bool>:
  Ub.r(V1(t))

# a word, read in the machine's order
def W0.z(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Word(0n)>:
  match m:
    case Some{u}:
      C.Program.unword.nil(C.Name.is_eq(u, C.Program.name.unit()))
    case None{}:
      None{}

def W0.k(ok: Bool, z: C.Term) -> Maybe<&2, Word(0n)>:
  match ok:
    case True{}:
      W0.z(VL(z))
    case False{}:
      None{}

def W0.a(m: Maybe<&2, List<&2, U32>>, z: C.Term) -> Maybe<&2, Word(0n)>:
  match m:
    case Some{k}:
      W0.k(C.Name.is_eq(k, C.Program.name.wnil()), z)
    case None{}:
      None{}

def W0.r(m: Maybe<&2, TP>) -> Maybe<&2, Word(0n)>:
  match m:
    case Some{TP{a, z}}:
      W0.a(VL(a), z)
    case None{}:
      None{}

def W1.w(-p: Nat, b: Bool, m: Maybe<&2, Word(p)>) -> Maybe<&2, Word(1n+p)>:
  match m:
    case Some{y}:
      Some{WCon{b, y}}
    case None{}:
      None{}

def W1.u(p: Nat, b: Bool, ok: Bool, w: C.Term) -> Maybe<&2, Word(1n+p)>:
  match ok:
    case True{}:
      W1.w(p, b, C.Program.unword(p, w))
    case False{}:
      None{}

def W1.z(p: Nat, b: Bool, w: C.Term, m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Word(1n+p)>:
  match m:
    case Some{u2}:
      W1.u(p, b, C.Name.is_eq(u2, C.Program.name.unit()), w)
    case None{}:
      None{}

def W1.r2(p: Nat, b: Bool, m: Maybe<&2, TP>) -> Maybe<&2, Word(1n+p)>:
  match m:
    case Some{TP{w, z}}:
      W1.z(p, b, w, VL(z))
    case None{}:
      None{}

def W1.b(p: Nat, mb: Maybe<&2, Bool>, r: C.Term) -> Maybe<&2, Word(1n+p)>:
  match mb:
    case Some{b}:
      W1.r2(p, b, V1(r))
    case None{}:
      None{}

def W1.f(p: Nat, m: Maybe<&2, TP>) -> Maybe<&2, Word(1n+p)>:
  match m:
    case Some{TP{bt, r}}:
      W1.b(p, Ub(bt), r)
    case None{}:
      None{}

def W1.k(p: Nat, ok: Bool, f: C.Term) -> Maybe<&2, Word(1n+p)>:
  match ok:
    case True{}:
      W1.f(p, V1(f))
    case False{}:
      None{}

def W1.a(p: Nat, m: Maybe<&2, List<&2, U32>>, f: C.Term) -> Maybe<&2, Word(1n+p)>:
  match m:
    case Some{k}:
      W1.k(p, C.Name.is_eq(k, C.Program.name.wcon()), f)
    case None{}:
      None{}

def W1.r(p: Nat, m: Maybe<&2, TP>) -> Maybe<&2, Word(1n+p)>:
  match m:
    case Some{TP{a, f}}:
      W1.a(p, VL(a), f)
    case None{}:
      None{}

# the word of n bits of t, read in the machine's order
def Wd(n: Nat, t: C.Term) -> Maybe<&2, Word(n)>:
  match n:
    case 0n:
      W0.r(V1(t))
    case 1n+p:
      W1.r(p, V1(t))

# U reads what Program.unbytes reads
# ----------------------------------

# a and b true gives a true
def and_l(a: Bool, b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, PN.false_ne_true(e))

def and_r(a: Bool, b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, PN.false_ne_true(e))

# a U32 equal to n has the number of n
def eq_nat(+x: U32, +n: U32, +e: {U32.is_eq(x, n) == True{} : Bool}) -> {U32.to_nat(x) == U32.to_nat(n) : Nat}:
  PN.rel_eq(U32.cmp(x, n), U32.to_nat(x), U32.to_nat(n), PN.U32.rel(x, n), PN.toT(U32.is_eq(x, n), e))

def ne_78_67(+e: {78n == 67n : Nat}) -> Empty:
  %e : PN.T(Nat.is_eq(_, 78n))
  Unit{}

def nilcon.c(b: Bool, +x: U32, +xs: List<&2, U32>, +e78: {U32.to_nat(x) == 78n : Nat},
  +eb: {U32.is_eq(x, 67) == b : Bool}) -> {False{} == Bool.and(b, C.Name.is_eq(xs, [111, 110])) : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({False{} == Bool.and(True{}, C.Name.is_eq(xs, [111, 110])) : Bool},
        ne_78_67(Equal.trans(Nat, 78n, U32.to_nat(x), 67n, Equal.sym(Nat, U32.to_nat(x), 78n, e78), eq_nat(x, 67, eb))))

# a name that is Nil is not Con
def nilcon(k: List<&2, U32>, +e: {C.Name.is_eq(k, C.Program.name.nil()) == True{} : Bool}) ->
  {False{} == C.Name.is_eq(k, C.Program.name.con()) : Bool}:
  match k:
    case Nil{}:
      Empty.absurd({False{} == C.Name.is_eq(Nil{}, C.Program.name.con()) : Bool}, PN.false_ne_true(e))
    case Con{+x, +xs}:
      nilcon.c(U32.is_eq(x, 67), x, xs,
        eq_nat(x, 78, and_l(U32.is_eq(x, 78), C.Name.is_eq(xs, [105, 108]), e)), {==})

def Uk_none(isnil: Bool, iscon: Bool, -b: C.Term, +h1: {None{} == U.nil(VL(b)) : Maybe<&2, List<&2, U32>>},
  +h2: {None{} == U.con(V1(b)) : Maybe<&2, List<&2, U32>>}) -> {None{} == U.k(isnil, iscon, b) : Maybe<&2, List<&2, U32>>}:
  match isnil:
    case True{}:
      h1
    case False{}:
      match iscon:
        case True{}:
          h2
        case False{}:
          {==}

def Uc3_none(ok: Bool, -x: C.Term, -rest: C.Term, +h: {None{} == U.c4(V1(x), rest) : Maybe<&2, List<&2, U32>>}) ->
  {None{} == U.c3(ok, x, rest) : Maybe<&2, List<&2, U32>>}:
  match ok:
    case True{}:
      h
    case False{}:
      {==}

def Uc2_none(-x: C.Term, -rest: C.Term, m: Maybe<&2, List<&2, U32>>, +h: {None{} == U.c4(V1(x), rest) : Maybe<&2, List<&2, U32>>}) ->
  {None{} == U.c2(x, rest, m) : Maybe<&2, List<&2, U32>>}:
  match m:
    case Some{u2}:
      Uc3_none(C.Name.is_eq(u2, C.Program.name.unit()), x, rest, h)
    case None{}:
      {==}

def Uc1_none(-x: C.Term, m: Maybe<&2, TP>, h: @rest: C.Term -> {None{} == U.c4(V1(x), rest) : Maybe<&2, List<&2, U32>>}) ->
  {None{} == U.c1(x, m) : Maybe<&2, List<&2, U32>>}:
  match m:
    case Some{TP{+rest, z}}:
      Uc2_none(x, rest, VL(z), h(rest))
    case None{}:
      {==}

def Uc6_none(ok: Bool, -wt: C.Term, -rest: C.Term, +h: {None{} == U.c7(V1(wt), rest) : Maybe<&2, List<&2, U32>>}) ->
  {None{} == U.c6(ok, wt, rest) : Maybe<&2, List<&2, U32>>}:
  match ok:
    case True{}:
      h
    case False{}:
      {==}

def LN(isnil: Bool, iscon: Bool, +u: List<&2, U32>) ->
  {C.Program.unbytes.nil(Bool.and(isnil, C.Name.is_eq(u, C.Program.name.unit()))) == U.k(isnil, iscon, C.Term.Lab{u}) : Maybe<&2, List<&2, U32>>}:
  match isnil:
    case True{}:
      {==}
    case False{}:
      match iscon:
        case True{}:
          {==}
        case False{}:
          {==}

def LF.l0(lt: Bool, +v: U32) -> {None{} == U.c11(lt, v, None{}) : Maybe<&2, List<&2, U32>>}:
  match lt:
    case True{}:
      {==}
    case False{}:
      {==}

def LF.l1(lt: Bool, +v: U32, +bs: List<&2, U32>) ->
  {C.Program.unbytes.byte(lt, v, bs) == U.c11(lt, v, Some{bs}) : Maybe<&2, List<&2, U32>>}:
  match lt:
    case True{}:
      {==}
    case False{}:
      {==}

def LF.r(+x: Word(32n), mr: Maybe<&2, List<&2, U32>>) ->
  {C.Program.unbytes.con(True{}, Some{x}, mr) == U.c11(U32.is_lt(U32{x}, 256), U32{x}, mr) : Maybe<&2, List<&2, U32>>}:
  match mr:
    case None{}:
      LF.l0(U32.is_lt(U32{x}, 256), U32{x})
    case Some{+bs}:
      LF.l1(U32.is_lt(U32{x}, 256), U32{x}, bs)

def LF.w(mw: Maybe<&2, Word(32n)>, +rest: C.Term) ->
  {C.Program.unbytes.con(True{}, mw, C.Program.unbytes(rest)) == U.c10(mw, rest) : Maybe<&2, List<&2, U32>>}:
  match mw:
    case None{}:
      {==}
    case Some{+x}:
      LF.r(x, C.Program.unbytes(rest))

def LF.o1(o1: Bool, +w: C.Term, +rest: C.Term) ->
  {C.Program.unbytes.con(Bool.and(Bool.and(True{}, o1), True{}), C.Program.unword(32n, w), C.Program.unbytes(rest)) == U.c9(o1, w, rest) : Maybe<&2, List<&2, U32>>}:
  match o1:
    case False{}:
      {==}
    case True{}:
      LF.w(C.Program.unword(32n, w), rest)

def LF.oc(oc: Bool, +w: C.Term, +u1: List<&2, U32>, +rest: C.Term) ->
  {C.Program.unbytes.con(Bool.and(Bool.and(oc, C.Name.is_eq(u1, C.Program.name.unit())), True{}), C.Program.unword(32n, w), C.Program.unbytes(rest)) ==
   U.c6(oc, C.Term.Tup{C.Quan.Q1{}, w, C.Term.Lab{u1}}, rest) : Maybe<&2, List<&2, U32>>}:
  match oc:
    case False{}:
      {==}
    case True{}:
      LF.o1(C.Name.is_eq(u1, C.Program.name.unit()), w, rest)

def LF.o2(o2: Bool, +c: List<&2, U32>, +w: C.Term, +u1: List<&2, U32>, +rest: C.Term) ->
  {C.Program.unbytes.con(Bool.and(Bool.and(C.Name.is_eq(c, C.Program.name.u32()), C.Name.is_eq(u1, C.Program.name.unit())), o2), C.Program.unword(32n, w), C.Program.unbytes(rest)) ==
   U.c3(o2, C.Term.Tup{C.Quan.Q1{}, C.Term.Lab{c}, C.Term.Tup{C.Quan.Q1{}, w, C.Term.Lab{u1}}}, rest) : Maybe<&2, List<&2, U32>>}:
  match o2:
    case False{}:
      %and_false(Bool.and(C.Name.is_eq(c, C.Program.name.u32()), C.Name.is_eq(u1, C.Program.name.unit()))) : {C.Program.unbytes.con(_, C.Program.unword(32n, w), C.Program.unbytes(rest)) ==
        U.c3(False{}, C.Term.Tup{C.Quan.Q1{}, C.Term.Lab{c}, C.Term.Tup{C.Quan.Q1{}, w, C.Term.Lab{u1}}}, rest) : Maybe<&2, List<&2, U32>>}
      {==}
    case True{}:
      LF.oc(C.Name.is_eq(c, C.Program.name.u32()), w, u1, rest)

def LF.k2(iscon: Bool, +c: List<&2, U32>, +w: C.Term, +u1: List<&2, U32>, +rest: C.Term, +u2: List<&2, U32>) ->
  {C.Program.unbytes.con(Bool.and(Bool.and(Bool.and(iscon, C.Name.is_eq(c, C.Program.name.u32())), C.Name.is_eq(u1, C.Program.name.unit())), C.Name.is_eq(u2, C.Program.name.unit())), C.Program.unword(32n, w), C.Program.unbytes(rest)) ==
   U.k2(iscon, C.Term.Tup{C.Quan.Q1{}, C.Term.Tup{C.Quan.Q1{}, C.Term.Lab{c}, C.Term.Tup{C.Quan.Q1{}, w, C.Term.Lab{u1}}}, C.Term.Tup{C.Quan.Q1{}, rest, C.Term.Lab{u2}}}) : Maybe<&2, List<&2, U32>>}:
  match iscon:
    case False{}:
      {==}
    case True{}:
      LF.o2(C.Name.is_eq(u2, C.Program.name.unit()), c, w, u1, rest)

def LF.n(isnil: Bool, +k: List<&2, U32>, +c: List<&2, U32>, +w: C.Term, +u1: List<&2, U32>, +rest: C.Term, +u2: List<&2, U32>,
  +e: {C.Name.is_eq(k, C.Program.name.nil()) == isnil : Bool}) ->
  {C.Program.unbytes.con(Bool.and(Bool.and(Bool.and(C.Name.is_eq(k, C.Program.name.con()), C.Name.is_eq(c, C.Program.name.u32())), C.Name.is_eq(u1, C.Program.name.unit())), C.Name.is_eq(u2, C.Program.name.unit())), C.Program.unword(32n, w), C.Program.unbytes(rest)) ==
   U.k(isnil, C.Name.is_eq(k, C.Program.name.con()), C.Term.Tup{C.Quan.Q1{}, C.Term.Tup{C.Quan.Q1{}, C.Term.Lab{c}, C.Term.Tup{C.Quan.Q1{}, w, C.Term.Lab{u1}}}, C.Term.Tup{C.Quan.Q1{}, rest, C.Term.Lab{u2}}}) : Maybe<&2, List<&2, U32>>}:
  match isnil:
    case True{}:
      %nilcon(k, e) : {C.Program.unbytes.con(Bool.and(Bool.and(Bool.and(_, C.Name.is_eq(c, C.Program.name.u32())), C.Name.is_eq(u1, C.Program.name.unit())), C.Name.is_eq(u2, C.Program.name.unit())), C.Program.unword(32n, w), C.Program.unbytes(rest)) ==
        U.k(True{}, C.Name.is_eq(k, C.Program.name.con()), C.Term.Tup{C.Quan.Q1{}, C.Term.Tup{C.Quan.Q1{}, C.Term.Lab{c}, C.Term.Tup{C.Quan.Q1{}, w, C.Term.Lab{u1}}}, C.Term.Tup{C.Quan.Q1{}, rest, C.Term.Lab{u2}}}) : Maybe<&2, List<&2, U32>>}
      {==}
    case False{}:
      LF.k2(C.Name.is_eq(k, C.Program.name.con()), c, w, u1, rest, u2)

def LF(+k: List<&2, U32>, +c: List<&2, U32>, +w: C.Term, +u1: List<&2, U32>, +rest: C.Term, +u2: List<&2, U32>) ->
  {C.Program.unbytes(C.Term.Tup{C.Quan.Q1{}, C.Term.Lab{k}, C.Term.Tup{C.Quan.Q1{}, C.Term.Tup{C.Quan.Q1{}, C.Term.Lab{c}, C.Term.Tup{C.Quan.Q1{}, w, C.Term.Lab{u1}}}, C.Term.Tup{C.Quan.Q1{}, rest, C.Term.Lab{u2}}}}) ==
   U(C.Term.Tup{C.Quan.Q1{}, C.Term.Lab{k}, C.Term.Tup{C.Quan.Q1{}, C.Term.Tup{C.Quan.Q1{}, C.Term.Lab{c}, C.Term.Tup{C.Quan.Q1{}, w, C.Term.Lab{u1}}}, C.Term.Tup{C.Quan.Q1{}, rest, C.Term.Lab{u2}}}}) : Maybe<&2, List<&2, U32>>}:
  LF.n(C.Name.is_eq(k, C.Program.name.nil()), k, c, w, u1, rest, u2, {==})

# Cells
# -----

# field k of the cell c
def Fd(k: Nat, +m: C.Cir.Cells, +c: U32) -> U32:
  C.Cir.Cell.get(k, C.Cir.Cells.get(m, c))

# the tag of the cell c (bits 0 to 5 of field 0)
def Tg(+m: C.Cir.Cells, +c: U32) -> U32:
  U32.and(Fd(0n, m, c), 63)

# M.pair holds of the cell c: a pair at quantity 1
def Pm(+m: C.Cir.Cells, +c: U32) -> Bool:
  FP.l(Fd(0n, m, c))

# the cell c is a label
def Lm(+m: C.Cir.Cells, +c: U32) -> Bool:
  U32.is_eq(Tg(m, c), 13)

# M.last holds of the cell c: its field 3 is the label of the name 0, ()
def LAST(+m: C.Cir.Cells, +c: U32) -> Bool:
  Bool.and(Lm(m, Fd(3n, m, c)), U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0))

# M.is_lab holds of field 2 of the cell c and the name n
def ISLAB(+m: C.Cir.Cells, +c: U32, +n: U32) -> Bool:
  Bool.and(Lm(m, Fd(2n, m, c)), U32.is_eq(Fd(2n, m, Fd(2n, m, c)), n))

def iff(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case True{} False{}:
      False{}
    case False{} True{}:
      False{}

def iff_eq(a: Bool, b: Bool, +e: {iff(a, b) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, PN.false_ne_true(e))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, PN.false_ne_true(e))

# the name b of the number j compares with the machine's names 0 to 7 as j
# compares with their numbers
def known.ok(+j: U32, +b: List<&2, U32>) -> Bool:
  iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)) &&
  iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1)) &&
  iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2)) &&
  iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3)) &&
  iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4)) &&
  iff(C.Name.is_eq(b, C.Program.name.wcon()), U32.is_eq(j, 5)) &&
  iff(C.Name.is_eq(b, C.Program.name.true()), U32.is_eq(j, 6)) &&
  iff(C.Name.is_eq(b, C.Program.name.false()), U32.is_eq(j, 7))

def labok.of(n: Maybe<&2, List<&2, U32>>, +j: U32) -> Bool:
  match n:
    case None{}:
      True{}
    case Some{b}:
      known.ok(j, b)

# the number j of a label is one whose name compares as known.ok says
def labok(+ks: List<&2, List<&2, U32>>, +j: U32) -> Bool:
  labok.of(T.tm.name(ks, j), j)

def noT1(r: Maybe<&2, C.Term>) -> Bool:
  match r:
    case None{}:
      True{}
    case Some{v}:
      Maybe.is_none(&2, TP, V1(v))

def noL(r: Maybe<&2, C.Term>) -> Bool:
  match r:
    case None{}:
      True{}
    case Some{v}:
      Maybe.is_none(&2, List<&2, U32>, VL(v))

def ok.img(+t: U32, +r: Maybe<&2, C.Term>) -> Bool:
  Bool.or(Bool.not(Bool.or(U32.is_eq(t, 1), U32.is_eq(t, 12))), Bool.and(noT1(r), noL(r)))

def ok.lab(+t: U32, +ks: List<&2, List<&2, U32>>, +j: U32) -> Bool:
  Bool.or(Bool.not(U32.is_eq(t, 13)), labok(ks, j))

# the cells that the walk of M.out reads from c, within fuel levels: each is
# a cell of the state (Cir.is_cell), a Ref or an Enu has an image's term
# that is no pair nor label, a label's number names it (labok), and the
# parts of a pair (tag 10) are such cells too, a level less deep
def ok(+fuel: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, +im: U32,
  +fs: U32, +nx: U32) -> Bool:
  match fuel:
    case 0n:
      False{}
    case 1n+f:
      +t = Tg(m, c)
      Bool.and(Bool.and(Bool.and(C.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c))), ok.lab(t, ks, Fd(2n, m, c))),
        Bool.or(Bool.not(U32.is_eq(t, 10)),
          Bool.and(ok(f, m, ks, img, Fd(2n, m, c), im, fs, nx), ok(f, m, ks, img, Fd(3n, m, c), im, fs, nx))))

def or_not(x: Bool, y: Bool, +e1: {Bool.or(Bool.not(x), y) == True{} : Bool}, +e2: {x == True{} : Bool}) -> {y == True{} : Bool}:
  match x:
    case True{}:
      e1
    case False{}:
      Empty.absurd({y == True{} : Bool}, PN.false_ne_true(e2))

def ok.cell(+f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +h: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool}) -> {C.Cir.is_cell(c, im, fs, nx) == True{} : Bool}:
  +t = Tg(m, c)
  +h1 = and_l(Bool.and(Bool.and(C.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c))), ok.lab(t, ks, Fd(2n, m, c))),
        Bool.or(Bool.not(U32.is_eq(t, 10)),
          Bool.and(ok(f, m, ks, img, Fd(2n, m, c), im, fs, nx), ok(f, m, ks, img, Fd(3n, m, c), im, fs, nx))), h)
  +h2 = and_l(Bool.and(C.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c))), ok.lab(t, ks, Fd(2n, m, c)), h1)
  and_l(C.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c)), h2)

def ok.im(+f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +h: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool},
  +e: {Bool.or(U32.is_eq(Tg(m, c), 1), U32.is_eq(Tg(m, c), 12)) == True{} : Bool}) ->
  {Bool.and(noT1(T.tm.image(img, c)), noL(T.tm.image(img, c))) == True{} : Bool}:
  +t = Tg(m, c)
  +h1 = and_l(Bool.and(Bool.and(C.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c))), ok.lab(t, ks, Fd(2n, m, c))),
        Bool.or(Bool.not(U32.is_eq(t, 10)),
          Bool.and(ok(f, m, ks, img, Fd(2n, m, c), im, fs, nx), ok(f, m, ks, img, Fd(3n, m, c), im, fs, nx))), h)
  +h2 = and_l(Bool.and(C.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c))), ok.lab(t, ks, Fd(2n, m, c)), h1)
  or_not(Bool.or(U32.is_eq(t, 1), U32.is_eq(t, 12)), Bool.and(noT1(T.tm.image(img, c)), noL(T.tm.image(img, c))),
    and_r(C.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c)), h2), e)

def ok.lb(+f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +h: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool},
  +e: {U32.is_eq(Tg(m, c), 13) == True{} : Bool}) -> {labok(ks, Fd(2n, m, c)) == True{} : Bool}:
  +t = Tg(m, c)
  +h1 = and_l(Bool.and(Bool.and(C.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c))), ok.lab(t, ks, Fd(2n, m, c))),
        Bool.or(Bool.not(U32.is_eq(t, 10)),
          Bool.and(ok(f, m, ks, img, Fd(2n, m, c), im, fs, nx), ok(f, m, ks, img, Fd(3n, m, c), im, fs, nx))), h)
  or_not(U32.is_eq(t, 13), labok(ks, Fd(2n, m, c)),
    and_r(Bool.and(C.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c))), ok.lab(t, ks, Fd(2n, m, c)), h1), e)

def ok.kids(+f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +h: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool},
  +e: {U32.is_eq(Tg(m, c), 10) == True{} : Bool}) ->
  {Bool.and(ok(f, m, ks, img, Fd(2n, m, c), im, fs, nx), ok(f, m, ks, img, Fd(3n, m, c), im, fs, nx)) == True{} : Bool}:
  +t = Tg(m, c)
  or_not(U32.is_eq(t, 10), Bool.and(ok(f, m, ks, img, Fd(2n, m, c), im, fs, nx), ok(f, m, ks, img, Fd(3n, m, c), im, fs, nx)),
    and_r(Bool.and(Bool.and(C.Cir.is_cell(c, im, fs, nx), ok.img(t, T.tm.image(img, c))), ok.lab(t, ks, Fd(2n, m, c))),
        Bool.or(Bool.not(U32.is_eq(t, 10)),
          Bool.and(ok(f, m, ks, img, Fd(2n, m, c), im, fs, nx), ok(f, m, ks, img, Fd(3n, m, c), im, fs, nx))), h), e)

# a U32 of the number of n is equal to n
def ion(c: Cmp, +x: Nat, +y: Nat, h: PN.Rel(c, x, y), +e: {x == y : Nat}) -> {Cmp.is_eq(c) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({Cmp.is_eq(LT{}) == True{} : Bool},
        PN.not_succ_le(x, PN.le_rw_r(1n+x, y, x, Equal.sym(Nat, x, y, e), h)))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({Cmp.is_eq(GT{}) == True{} : Bool},
        PN.not_succ_le(y, PN.le_rw_r(1n+y, x, y, e, h)))

def nat_eq(+x: U32, +n: U32, +e: {U32.to_nat(x) == U32.to_nat(n) : Nat}) -> {U32.is_eq(x, n) == True{} : Bool}:
  ion(U32.cmp(x, n), U32.to_nat(x), U32.to_nat(n), PN.U32.rel(x, n), e)

# the term of a Maybe, when there is one, has the property K
def SpecM(r: Maybe<&2, C.Term>, K: C.Term -> Type) -> Type:
  match r:
    case None{}:
      Unit
    case Some{v}:
      K(v)

def SpecM.all(r: Maybe<&2, C.Term>, -K: C.Term -> Type, h: @v: C.Term -> K(v)) -> SpecM(r, K):
  match r:
    case None{}:
      Unit{}
    case Some{v}:
      h(v)

def SpecM.map(r: Maybe<&2, C.Term>, -K1: C.Term -> Type, -K2: C.Term -> Type, h1: SpecM(r, K1), h: @v: C.Term -> K1(v) -> K2(v)) -> SpecM(r, K2):
  match r:
    case None{}:
      Unit{}
    case Some{v}:
      h(v, h1)

def SpecM.swap(r: Maybe<&2, C.Term>, s: Maybe<&2, C.Term>, -K: C.Term -> C.Term -> Type,
  h: SpecM(s, b => SpecM(r, a => K(a, b)))) -> SpecM(r, a => SpecM(s, b => K(a, b))):
  match r s:
    case None{} _:
      Unit{}
    case Some{a} None{}:
      Unit{}
    case Some{a} Some{b}:
      h

def sp.one(k: C.Term -> C.Term, r: Maybe<&2, C.Term>, -K: C.Term -> Type, h: @a: C.Term -> K(k(a))) -> SpecM(T.tm.one(k, r), K):
  match r:
    case None{}:
      Unit{}
    case Some{a}:
      h(a)

def sp.two(k: C.Term -> C.Term -> C.Term, r: Maybe<&2, C.Term>, s: Maybe<&2, C.Term>, -K: C.Term -> Type,
  h: @a: C.Term -> @b: C.Term -> K(k(a, b))) -> SpecM(T.tm.two(k, r, s), K):
  match r s:
    case Some{a} Some{b}:
      h(a, b)
    case Some{a} None{}:
      Unit{}
    case None{} _:
      Unit{}

def sp.three(k: C.Term -> C.Term -> C.Term -> C.Term, r: Maybe<&2, C.Term>, s: Maybe<&2, C.Term>, t: Maybe<&2, C.Term>,
  -K: C.Term -> Type, h: @a: C.Term -> @b: C.Term -> @c: C.Term -> K(k(a, b, c))) -> SpecM(T.tm.three(k, r, s, t), K):
  match r s t:
    case Some{a} Some{b} Some{c}:
      h(a, b, c)
    case Some{a} Some{b} None{}:
      Unit{}
    case Some{a} None{} _:
      Unit{}
    case None{} _ _:
      Unit{}

def sp.named(n: Maybe<&2, List<&2, U32>>, k: List<&2, U32> -> C.Term, -K: C.Term -> Type, h: @x: List<&2, U32> -> K(k(x))) ->
  SpecM(T.tm.named(n, k), K):
  match n:
    case None{}:
      Unit{}
    case Some{x}:
      h(x)

def sp.mat(n: Maybe<&2, List<&2, U32>>, r: Maybe<&2, C.Term>, s: Maybe<&2, C.Term>, -K: C.Term -> Type,
  h: @x: List<&2, U32> -> @a: C.Term -> @b: C.Term -> K(C.Term.Mat{x, a, b})) -> SpecM(T.tm.mat(n, r, s), K):
  match n r s:
    case Some{x} Some{a} Some{b}:
      h(x, a, b)
    case Some{x} Some{a} None{}:
      Unit{}
    case Some{x} None{} _:
      Unit{}
    case None{} _ _:
      Unit{}

def isnone(m: Maybe<&2, TP>, +e: {Maybe.is_none(&2, TP, m) == True{} : Bool}) -> {m == None{} : Maybe<&2, TP>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      Empty.absurd({Some{x} == None{} : Maybe<&2, TP>}, PN.false_ne_true(e))

def isnoneL(m: Maybe<&2, List<&2, U32>>, +e: {Maybe.is_none(&2, List<&2, U32>, m) == True{} : Bool}) -> {m == None{} : Maybe<&2, List<&2, U32>>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      Empty.absurd({Some{x} == None{} : Maybe<&2, List<&2, U32>>}, PN.false_ne_true(e))

# an image's term that is no pair at quantity 1
def sp.imgT(r: Maybe<&2, C.Term>, -K: C.Term -> Type, +e: {Bool.and(noT1(r), noL(r)) == True{} : Bool},
  h: @v: C.Term -> {V1(v) == None{} : Maybe<&2, TP>} -> K(v)) -> SpecM(r, K):
  match r:
    case None{}:
      Unit{}
    case Some{+v}:
      h(v, isnone(V1(v), and_l(Maybe.is_none(&2, TP, V1(v)), Maybe.is_none(&2, List<&2, U32>, VL(v)), e)))

def sp.imgL(r: Maybe<&2, C.Term>, -K: C.Term -> Type, +e: {Bool.and(noT1(r), noL(r)) == True{} : Bool},
  h: @v: C.Term -> {VL(v) == None{} : Maybe<&2, List<&2, U32>>} -> K(v)) -> SpecM(r, K):
  match r:
    case None{}:
      Unit{}
    case Some{+v}:
      h(v, isnoneL(VL(v), and_r(Maybe.is_none(&2, TP, V1(v)), Maybe.is_none(&2, List<&2, U32>, VL(v)), e)))

def or_true_r(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# the goal of a cell's term, by its tag and quantity
def CG(tag: Nat, +q: C.Quan, +f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32,
  K: C.Term -> Type) -> Type:
  SpecM(T.tm.cell(tag, q, c, Fd(2n, m, c), ks, img, u => T.tm.of(f, m, ks, img, Fd(2n, m, c)),
    u => T.tm.of(f, m, ks, img, Fd(3n, m, c)), u => T.tm.of(f, m, ks, img, Fd(4n, m, c))), K)

def or_l_true(a: Bool, b: Bool, +e: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Bool.or(False{}, b) == True{} : Bool}, PN.false_ne_true(e))

def or_r_true(a: Bool, b: Bool, +e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def sp.two2(k: C.Term -> C.Term -> C.Term, r: Maybe<&2, C.Term>, s: Maybe<&2, C.Term>, -K: C.Term -> Type,
  h: SpecM(r, a => SpecM(s, b => K(k(a, b))))) -> SpecM(T.tm.two(k, r, s), K):
  match r s:
    case Some{a} Some{b}:
      h
    case Some{a} None{}:
      Unit{}
    case None{} _:
      Unit{}

def sp.namedE(n: Maybe<&2, List<&2, U32>>, -K: C.Term -> Type, h: @k: List<&2, U32> -> {n == Some{k} : Maybe<&2, List<&2, U32>>} -> K(C.Term.Lab{k})) ->
  SpecM(T.tm.named(n, k => C.Term.Lab{k}), K):
  match n:
    case None{}:
      Unit{}
    case Some{+k}:
      h(k, {==})

def cellT1.go(tag: Nat, q: C.Quan, +f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32,
  -K: C.Term -> Type, +et: {10n == tag : Nat}, +eq: {isQ1(q) == True{} : Bool},
  h: SpecM(T.tm.of(f, m, ks, img, Fd(2n, m, c)), a => SpecM(T.tm.of(f, m, ks, img, Fd(3n, m, c)), b => K(C.Term.Tup{C.Quan.Q1{}, a, b})))) ->
  CG(tag, q, f, m, ks, img, c, K):
  match q:
    case C.Quan.Q1{}:
      %et : CG(_, C.Quan.Q1{}, f, m, ks, img, c, K)
      sp.two2(a => b => C.Term.Tup{C.Quan.Q1{}, a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, h)
    case C.Quan.Q0{}:
      Empty.absurd(CG(tag, C.Quan.Q0{}, f, m, ks, img, c, K), PN.false_ne_true(eq))
    case C.Quan.Q2{}:
      Empty.absurd(CG(tag, C.Quan.Q2{}, f, m, ks, img, c, K), PN.false_ne_true(eq))

# the term of a cell that M.pair accepts is a pair at quantity 1 of the terms
# of its fields 2 and 3
def cellT1(+f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, -K: C.Term -> Type,
  +eP: {Pm(m, c) == True{} : Bool},
  h: SpecM(T.tm.of(f, m, ks, img, Fd(2n, m, c)), a => SpecM(T.tm.of(f, m, ks, img, Fd(3n, m, c)), b => K(C.Term.Tup{C.Quan.Q1{}, a, b})))) ->
  SpecM(T.tm.of(1n+f, m, ks, img, c), K):
  +f0 = Fd(0n, m, c)
  +q = T.tm.quan(U32.and(U32.shrn(f0, 6n), 3))
  +fr = Equal.trans(Bool, FP.r(f0), FP.l(f0), True{}, Equal.sym(Bool, FP.l(f0), FP.r(f0), fp(f0)), eP)
  +e10 = and_r(isQ1(q), U32.is_eq(U32.and(f0, 63), 10), fr)
  cellT1.go(U32.to_nat(U32.and(f0, 63)), q, f, m, ks, img, c, K,
    Equal.sym(Nat, U32.to_nat(U32.and(f0, 63)), 10n, eq_nat(U32.and(f0, 63), 10, e10)),
    and_l(isQ1(q), U32.is_eq(U32.and(f0, 63), 10), fr), h)

def cellLab.go(tag: Nat, +q: C.Quan, +f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32,
  -K: C.Term -> Type, +et: {13n == tag : Nat},
  h: @k: List<&2, U32> -> {T.tm.name(ks, Fd(2n, m, c)) == Some{k} : Maybe<&2, List<&2, U32>>} -> K(C.Term.Lab{k})) ->
  CG(tag, q, f, m, ks, img, c, K):
  %et : CG(_, q, f, m, ks, img, c, K)
  sp.namedE(T.tm.name(ks, Fd(2n, m, c)), K, h)

# the term of a label cell is the label of the name of its number
def cellLab(+f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, -K: C.Term -> Type,
  +eL: {Lm(m, c) == True{} : Bool},
  h: @k: List<&2, U32> -> {T.tm.name(ks, Fd(2n, m, c)) == Some{k} : Maybe<&2, List<&2, U32>>} -> K(C.Term.Lab{k})) ->
  SpecM(T.tm.of(1n+f, m, ks, img, c), K):
  +f0 = Fd(0n, m, c)
  cellLab.go(U32.to_nat(U32.and(f0, 63)), T.tm.quan(U32.and(U32.shrn(f0, 6n), 3)), f, m, ks, img, c, K,
    Equal.sym(Nat, U32.to_nat(U32.and(f0, 63)), 13n, eq_nat(U32.and(f0, 63), 13, eL)), h)

def cellNotT1.go(tag: Nat, +q: C.Quan, +f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, -K: C.Term -> Type, +et: {U32.to_nat(Tg(m, c)) == tag : Nat},
  +eF: {Bool.and(isQ1(q), U32.is_eq(Tg(m, c), 10)) == False{} : Bool}, +hok: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool},
  h: @v: C.Term -> {V1(v) == None{} : Maybe<&2, TP>} -> K(v)) -> CG(tag, q, f, m, ks, img, c, K):
  match tag:
    case 0n:
      h(C.Term.Var{U32.to_nat(Fd(2n, m, c))}, {==})
    case 1n+t1:
      match t1:
        case 0n:
          sp.imgT(T.tm.image(img, c), K, ok.im(f, m, ks, img, c, im, fs, nx, hok, or_l_true(U32.is_eq(Tg(m, c), 1), U32.is_eq(Tg(m, c), 12), nat_eq(Tg(m, c), 1, et))), h)
        case 1n+t2:
          match t2:
            case 0n:
              sp.two(a => b => C.Term.Ann{a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(C.Term.Ann{a, b}, {==}))
            case 1n+t3:
              match t3:
                case 0n:
                  sp.two(a => b => C.Term.Let{q, a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(C.Term.Let{q, a, b}, {==}))
                case 1n+t4:
                  match t4:
                    case 0n:
                      sp.one(a => C.Term.Typ{a}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), K, a => h(C.Term.Typ{a}, {==}))
                    case 1n+t5:
                      match t5:
                        case 0n:
                          sp.two(a => b => C.Term.Min{a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(C.Term.Min{a, b}, {==}))
                        case 1n+t6:
                          match t6:
                            case 0n:
                              sp.two(a => b => C.Term.All{q, a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(C.Term.All{q, a, b}, {==}))
                            case 1n+t7:
                              match t7:
                                case 0n:
                                  sp.one(a => C.Term.Lam{q, a}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), K, a => h(C.Term.Lam{q, a}, {==}))
                                case 1n+t8:
                                  match t8:
                                    case 0n:
                                      sp.two(a => b => C.Term.App{q, a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(C.Term.App{q, a, b}, {==}))
                                    case 1n+t9:
                                      match t9:
                                        case 0n:
                                          sp.two(a => b => C.Term.Sig{q, a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(C.Term.Sig{q, a, b}, {==}))
                                        case 1n+t10:
                                          match t10:
                                            case 0n:
                                              match q:
                                                case C.Quan.Q0{}:
                                                  sp.two(a => b => C.Term.Tup{C.Quan.Q0{}, a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(C.Term.Tup{C.Quan.Q0{}, a, b}, {==}))
                                                case C.Quan.Q2{}:
                                                  sp.two(a => b => C.Term.Tup{C.Quan.Q2{}, a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(C.Term.Tup{C.Quan.Q2{}, a, b}, {==}))
                                                case C.Quan.Q1{}:
                                                  Empty.absurd(CG(10n, C.Quan.Q1{}, f, m, ks, img, c, K), PN.true_ne_false(Equal.trans(Bool, True{}, U32.is_eq(Tg(m, c), 10), False{}, Equal.sym(Bool, U32.is_eq(Tg(m, c), 10), True{}, nat_eq(Tg(m, c), 10, et)), eF)))
                                            case 1n+t11:
                                              match t11:
                                                case 0n:
                                                  sp.one(a => C.Term.Prj{a}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), K, a => h(C.Term.Prj{a}, {==}))
                                                case 1n+t12:
                                                  match t12:
                                                    case 0n:
                                                      sp.imgT(T.tm.image(img, c), K, ok.im(f, m, ks, img, c, im, fs, nx, hok, or_r_true(U32.is_eq(Tg(m, c), 1), U32.is_eq(Tg(m, c), 12), nat_eq(Tg(m, c), 12, et))), h)
                                                    case 1n+t13:
                                                      match t13:
                                                        case 0n:
                                                          sp.named(T.tm.name(ks, Fd(2n, m, c)), k => C.Term.Lab{k}, K, x => h(C.Term.Lab{x}, {==}))
                                                        case 1n+t14:
                                                          match t14:
                                                            case 0n:
                                                              sp.mat(T.tm.name(ks, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), T.tm.of(f, m, ks, img, Fd(4n, m, c)), K, x => a => b => h(C.Term.Mat{x, a, b}, {==}))
                                                            case 1n+t15:
                                                              match t15:
                                                                case 0n:
                                                                  h(C.Term.Efq{}, {==})
                                                                case 1n+t16:
                                                                  match t16:
                                                                    case 0n:
                                                                      sp.three(a => b => d => C.Term.Eql{a, b, d}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), T.tm.of(f, m, ks, img, Fd(4n, m, c)), K, a => b => d => h(C.Term.Eql{a, b, d}, {==}))
                                                                    case 1n+t17:
                                                                      match t17:
                                                                        case 0n:
                                                                          h(C.Term.Rfl{}, {==})
                                                                        case 1n+t18:
                                                                          match t18:
                                                                            case 0n:
                                                                              sp.three(a => b => d => C.Term.Rwt{a, b, d}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), T.tm.of(f, m, ks, img, Fd(4n, m, c)), K, a => b => d => h(C.Term.Rwt{a, b, d}, {==}))
                                                                            case 1n+t19:
                                                                              Unit{}

def cellNotL.go(tag: Nat, +q: C.Quan, +f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, -K: C.Term -> Type, +et: {U32.to_nat(Tg(m, c)) == tag : Nat},
  +eF: {U32.is_eq(Tg(m, c), 13) == False{} : Bool}, +hok: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool},
  h: @v: C.Term -> {VL(v) == None{} : Maybe<&2, List<&2, U32>>} -> K(v)) -> CG(tag, q, f, m, ks, img, c, K):
  match tag:
    case 0n:
      h(C.Term.Var{U32.to_nat(Fd(2n, m, c))}, {==})
    case 1n+t1:
      match t1:
        case 0n:
          sp.imgL(T.tm.image(img, c), K, ok.im(f, m, ks, img, c, im, fs, nx, hok, or_l_true(U32.is_eq(Tg(m, c), 1), U32.is_eq(Tg(m, c), 12), nat_eq(Tg(m, c), 1, et))), h)
        case 1n+t2:
          match t2:
            case 0n:
              sp.two(a => b => C.Term.Ann{a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(C.Term.Ann{a, b}, {==}))
            case 1n+t3:
              match t3:
                case 0n:
                  sp.two(a => b => C.Term.Let{q, a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(C.Term.Let{q, a, b}, {==}))
                case 1n+t4:
                  match t4:
                    case 0n:
                      sp.one(a => C.Term.Typ{a}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), K, a => h(C.Term.Typ{a}, {==}))
                    case 1n+t5:
                      match t5:
                        case 0n:
                          sp.two(a => b => C.Term.Min{a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(C.Term.Min{a, b}, {==}))
                        case 1n+t6:
                          match t6:
                            case 0n:
                              sp.two(a => b => C.Term.All{q, a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(C.Term.All{q, a, b}, {==}))
                            case 1n+t7:
                              match t7:
                                case 0n:
                                  sp.one(a => C.Term.Lam{q, a}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), K, a => h(C.Term.Lam{q, a}, {==}))
                                case 1n+t8:
                                  match t8:
                                    case 0n:
                                      sp.two(a => b => C.Term.App{q, a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(C.Term.App{q, a, b}, {==}))
                                    case 1n+t9:
                                      match t9:
                                        case 0n:
                                          sp.two(a => b => C.Term.Sig{q, a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(C.Term.Sig{q, a, b}, {==}))
                                        case 1n+t10:
                                          match t10:
                                            case 0n:
                                              sp.two(a => b => C.Term.Tup{q, a, b}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), K, a => b => h(C.Term.Tup{q, a, b}, {==}))
                                            case 1n+t11:
                                              match t11:
                                                case 0n:
                                                  sp.one(a => C.Term.Prj{a}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), K, a => h(C.Term.Prj{a}, {==}))
                                                case 1n+t12:
                                                  match t12:
                                                    case 0n:
                                                      sp.imgL(T.tm.image(img, c), K, ok.im(f, m, ks, img, c, im, fs, nx, hok, or_r_true(U32.is_eq(Tg(m, c), 1), U32.is_eq(Tg(m, c), 12), nat_eq(Tg(m, c), 12, et))), h)
                                                    case 1n+t13:
                                                      match t13:
                                                        case 0n:
                                                          Empty.absurd(CG(13n, q, f, m, ks, img, c, K), PN.true_ne_false(Equal.trans(Bool, True{}, U32.is_eq(Tg(m, c), 13), False{}, Equal.sym(Bool, U32.is_eq(Tg(m, c), 13), True{}, nat_eq(Tg(m, c), 13, et)), eF)))
                                                        case 1n+t14:
                                                          match t14:
                                                            case 0n:
                                                              sp.mat(T.tm.name(ks, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), T.tm.of(f, m, ks, img, Fd(4n, m, c)), K, x => a => b => h(C.Term.Mat{x, a, b}, {==}))
                                                            case 1n+t15:
                                                              match t15:
                                                                case 0n:
                                                                  h(C.Term.Efq{}, {==})
                                                                case 1n+t16:
                                                                  match t16:
                                                                    case 0n:
                                                                      sp.three(a => b => d => C.Term.Eql{a, b, d}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), T.tm.of(f, m, ks, img, Fd(4n, m, c)), K, a => b => d => h(C.Term.Eql{a, b, d}, {==}))
                                                                    case 1n+t17:
                                                                      match t17:
                                                                        case 0n:
                                                                          h(C.Term.Rfl{}, {==})
                                                                        case 1n+t18:
                                                                          match t18:
                                                                            case 0n:
                                                                              sp.three(a => b => d => C.Term.Rwt{a, b, d}, T.tm.of(f, m, ks, img, Fd(2n, m, c)), T.tm.of(f, m, ks, img, Fd(3n, m, c)), T.tm.of(f, m, ks, img, Fd(4n, m, c)), K, a => b => d => h(C.Term.Rwt{a, b, d}, {==}))
                                                                            case 1n+t19:
                                                                              Unit{}
# the term of a cell that M.pair rejects is no pair at quantity 1
def cellNotT1(+f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  -K: C.Term -> Type, +eP: {Pm(m, c) == False{} : Bool}, +hok: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool},
  h: @v: C.Term -> {V1(v) == None{} : Maybe<&2, TP>} -> K(v)) -> SpecM(T.tm.of(1n+f, m, ks, img, c), K):
  +f0 = Fd(0n, m, c)
  cellNotT1.go(U32.to_nat(U32.and(f0, 63)), T.tm.quan(U32.and(U32.shrn(f0, 6n), 3)), f, m, ks, img, c, im, fs, nx, K, {==},
    Equal.trans(Bool, FP.r(f0), FP.l(f0), False{}, Equal.sym(Bool, FP.l(f0), FP.r(f0), fp(f0)), eP), hok, h)

# the term of a cell whose tag is not 13 is no label
def cellNotL(+f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  -K: C.Term -> Type, +eL: {Lm(m, c) == False{} : Bool}, +hok: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool},
  h: @v: C.Term -> {VL(v) == None{} : Maybe<&2, List<&2, U32>>} -> K(v)) -> SpecM(T.tm.of(1n+f, m, ks, img, c), K):
  +f0 = Fd(0n, m, c)
  cellNotL.go(U32.to_nat(U32.and(f0, 63)), T.tm.quan(U32.and(U32.shrn(f0, 6n), 3)), f, m, ks, img, c, im, fs, nx, K, {==}, eL, hok, h)

# The cells, read as the machine reads them
# -----------------------------------------
#
# CB, CW and Step read the cells by the machine's tests, in its order; CU
# reads a list. They take each test's value as a Bool: Pm (M.pair), Lm (a
# label's tag), LAST (M.last), ISLAB (M.is_lab).

# a bit: Some of whether its name is True (number 6)
def CB.t(b: Bool, x6: Bool) -> Maybe<&2, Bool>:
  match b:
    case True{}:
      Some{x6}
    case False{}:
      None{}

def CB.x(b: Bool, +t2: U32) -> Maybe<&2, Bool>:
  match b:
    case True{}:
      CB.t(Bool.or(U32.is_eq(t2, 6), U32.is_eq(t2, 7)), U32.is_eq(t2, 6))
    case False{}:
      None{}

def CB.l(b: Bool, +m: C.Cir.Cells, +c: U32) -> Maybe<&2, Bool>:
  match b:
    case True{}:
      CB.x(Lm(m, Fd(2n, m, c)), Fd(2n, m, Fd(2n, m, c)))
    case False{}:
      None{}

def CB.p(b: Bool, +m: C.Cir.Cells, +c: U32) -> Maybe<&2, Bool>:
  match b:
    case True{}:
      CB.l(LAST(m, c), m, c)
    case False{}:
      None{}

def CB(+m: C.Cir.Cells, +c: U32) -> Maybe<&2, Bool>:
  CB.p(Pm(m, c), m, c)

# a word of n bits
def CW0.z(b: Bool) -> Maybe<&2, Word(0n)>:
  match b:
    case True{}:
      Some{WNil{}}
    case False{}:
      None{}

def CW0.l(b: Bool, +m: C.Cir.Cells, +c: U32) -> Maybe<&2, Word(0n)>:
  match b:
    case True{}:
      CW0.z(LAST(m, c))
    case False{}:
      None{}

def CW0.p(b: Bool, +m: C.Cir.Cells, +c: U32) -> Maybe<&2, Word(0n)>:
  match b:
    case True{}:
      CW0.l(ISLAB(m, c, 4), m, c)
    case False{}:
      None{}

def CW1.z(-q: Nat, b: Bool, x: Bool, rec: Maybe<&2, Word(q)>) -> Maybe<&2, Word(1n+q)>:
  match b:
    case True{}:
      W1.w(q, x, rec)
    case False{}:
      None{}

def CW1.r(-q: Nat, x: Bool, b: Bool, +m: C.Cir.Cells, +rc: U32, rec: Maybe<&2, Word(q)>) -> Maybe<&2, Word(1n+q)>:
  match b:
    case True{}:
      CW1.z(q, x, LAST(m, rc), rec)
    case False{}:
      None{}

def CW1.b(-q: Nat, mb: Maybe<&2, Bool>, +m: C.Cir.Cells, +rc: U32, rec: Maybe<&2, Word(q)>) -> Maybe<&2, Word(1n+q)>:
  match mb:
    case Some{x}:
      CW1.r(q, x, Pm(m, rc), m, rc, rec)
    case None{}:
      None{}

def CW1.f(-q: Nat, b: Bool, +m: C.Cir.Cells, +fc: U32, rec: Maybe<&2, Word(q)>) -> Maybe<&2, Word(1n+q)>:
  match b:
    case True{}:
      CW1.b(q, CB(m, Fd(2n, m, fc)), m, Fd(3n, m, fc), rec)
    case False{}:
      None{}

def CW1.l(-q: Nat, b: Bool, +m: C.Cir.Cells, +fc: U32, rec: Maybe<&2, Word(q)>) -> Maybe<&2, Word(1n+q)>:
  match b:
    case True{}:
      CW1.f(q, Pm(m, fc), m, fc, rec)
    case False{}:
      None{}

def CW1.p(-q: Nat, b: Bool, +m: C.Cir.Cells, +c: U32, rec: Maybe<&2, Word(q)>) -> Maybe<&2, Word(1n+q)>:
  match b:
    case True{}:
      CW1.l(q, ISLAB(m, c, 5), m, Fd(3n, m, c), rec)
    case False{}:
      None{}

# the cell of the word after the word of the cell c
def CW.next(+m: C.Cir.Cells, +c: U32) -> U32:
  Fd(2n, m, Fd(3n, m, Fd(3n, m, c)))

def CW(p: Nat, +m: C.Cir.Cells, +c: U32) -> Maybe<&2, Word(p)>:
  match p:
    case 0n:
      CW0.p(Pm(m, c), m, c)
    case 1n+q:
      CW1.p(q, Pm(m, c), m, c, CW(q, m, CW.next(m, c)))

# a step of the list: its end, with its result, or a byte and the cell of
# the rest
type SR is Data:
  SR.done{r: Maybe<&2, List<&2, U32>>}
  SR.more{v: U32, rest: U32}

def S.c8(lt: Bool, v: U32, +restc: U32) -> SR:
  match lt:
    case True{}:
      SR.more{v, restc}
    case False{}:
      SR.done{None{}}

def S.c7(mw: Maybe<&2, Word(32n)>, +restc: U32) -> SR:
  match mw:
    case Some{+x}:
      S.c8(U32.is_lt(U32{x}, 256), U32{x}, restc)
    case None{}:
      SR.done{None{}}

def S.c6(b: Bool, +m: C.Cir.Cells, +wc: U32, +restc: U32) -> SR:
  match b:
    case True{}:
      S.c7(CW(32n, m, wc), restc)
    case False{}:
      SR.done{None{}}

def S.c5(b: Bool, +m: C.Cir.Cells, +wtc: U32, +restc: U32) -> SR:
  match b:
    case True{}:
      S.c6(LAST(m, wtc), m, Fd(2n, m, wtc), restc)
    case False{}:
      SR.done{None{}}

def S.c4(b: Bool, +m: C.Cir.Cells, +wtc: U32, +restc: U32) -> SR:
  match b:
    case True{}:
      S.c5(Pm(m, wtc), m, wtc, restc)
    case False{}:
      SR.done{None{}}

def S.c3(b: Bool, +m: C.Cir.Cells, +xc: U32, +restc: U32) -> SR:
  match b:
    case True{}:
      S.c4(ISLAB(m, xc, 3), m, Fd(3n, m, xc), restc)
    case False{}:
      SR.done{None{}}

def S.c2(b: Bool, +m: C.Cir.Cells, +xc: U32, +restc: U32) -> SR:
  match b:
    case True{}:
      S.c3(Pm(m, xc), m, xc, restc)
    case False{}:
      SR.done{None{}}

def S.c1(b: Bool, +m: C.Cir.Cells, +xc: U32, +yc: U32) -> SR:
  match b:
    case True{}:
      S.c2(LAST(m, yc), m, xc, Fd(2n, m, yc))
    case False{}:
      SR.done{None{}}

def S.c0(b: Bool, +m: C.Cir.Cells, +bc: U32) -> SR:
  match b:
    case True{}:
      S.c1(Pm(m, Fd(3n, m, bc)), m, Fd(2n, m, bc), Fd(3n, m, bc))
    case False{}:
      SR.done{None{}}

def S.k2(iscon: Bool, +m: C.Cir.Cells, +bc: U32) -> SR:
  match iscon:
    case True{}:
      S.c0(Pm(m, bc), m, bc)
    case False{}:
      SR.done{None{}}

def S.nil(b: Bool) -> SR:
  match b:
    case True{}:
      SR.done{Some{Nil{}}}
    case False{}:
      SR.done{None{}}

def S.w(isnil: Bool, iscon: Bool, +m: C.Cir.Cells, +c: U32) -> SR:
  match isnil:
    case True{}:
      S.nil(LAST(m, c))
    case False{}:
      S.k2(iscon, m, Fd(3n, m, c))

def S.l(b: Bool, +m: C.Cir.Cells, +c: U32) -> SR:
  match b:
    case True{}:
      S.w(U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 1), U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 2), m, c)
    case False{}:
      SR.done{None{}}

def S.p(b: Bool, +m: C.Cir.Cells, +c: U32) -> SR:
  match b:
    case True{}:
      S.l(Lm(m, Fd(2n, m, c)), m, c)
    case False{}:
      SR.done{None{}}

def Step(+m: C.Cir.Cells, +c: U32) -> SR:
  S.p(Pm(m, c), m, c)

# the list from a step, with fuel levels as T.tm.of reads them: its rest is
# 3 levels below its cell
def CU.d(s: SR) -> Maybe<&2, List<&2, U32>>:
  match s:
    case SR.done{r}:
      r
    case SR.more{v, rest}:
      None{}

def CU(n: Nat, +m: C.Cir.Cells, s: SR) -> Maybe<&2, List<&2, U32>>:
  match n:
    case 0n:
      None{}
    case 1n+a:
      match a:
        case 0n:
          CU.d(s)
        case 1n+b:
          match b:
            case 0n:
              CU.d(s)
            case 1n+d:
              match s:
                case SR.done{r}:
                  r
                case SR.more{v, rest}:
                  U.c12(v, CU(d, m, Step(m, rest)))

# the names of the machine's numbers 0 to 7 compare as their numbers
def kn0(+j: U32, +b: List<&2, U32>, +h: {known.ok(j, b) == True{} : Bool}) ->
  {C.Name.is_eq(b, C.Program.name.unit()) == U32.is_eq(j, 0) : Bool}:
  iff_eq(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0), and_l(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1)), and_l(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2)), and_l(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3)), and_l(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4))), iff(C.Name.is_eq(b, C.Program.name.wcon()), U32.is_eq(j, 5)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4))), iff(C.Name.is_eq(b, C.Program.name.wcon()), U32.is_eq(j, 5))), iff(C.Name.is_eq(b, C.Program.name.true()), U32.is_eq(j, 6)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4))), iff(C.Name.is_eq(b, C.Program.name.wcon()), U32.is_eq(j, 5))), iff(C.Name.is_eq(b, C.Program.name.true()), U32.is_eq(j, 6))), iff(C.Name.is_eq(b, C.Program.name.false()), U32.is_eq(j, 7)), h))))))))

def kn1(+j: U32, +b: List<&2, U32>, +h: {known.ok(j, b) == True{} : Bool}) ->
  {C.Name.is_eq(b, C.Program.name.nil()) == U32.is_eq(j, 1) : Bool}:
  iff_eq(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1), and_r(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1)), and_l(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2)), and_l(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3)), and_l(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4))), iff(C.Name.is_eq(b, C.Program.name.wcon()), U32.is_eq(j, 5)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4))), iff(C.Name.is_eq(b, C.Program.name.wcon()), U32.is_eq(j, 5))), iff(C.Name.is_eq(b, C.Program.name.true()), U32.is_eq(j, 6)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4))), iff(C.Name.is_eq(b, C.Program.name.wcon()), U32.is_eq(j, 5))), iff(C.Name.is_eq(b, C.Program.name.true()), U32.is_eq(j, 6))), iff(C.Name.is_eq(b, C.Program.name.false()), U32.is_eq(j, 7)), h))))))))

def kn2(+j: U32, +b: List<&2, U32>, +h: {known.ok(j, b) == True{} : Bool}) ->
  {C.Name.is_eq(b, C.Program.name.con()) == U32.is_eq(j, 2) : Bool}:
  iff_eq(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2), and_r(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2)), and_l(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3)), and_l(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4))), iff(C.Name.is_eq(b, C.Program.name.wcon()), U32.is_eq(j, 5)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4))), iff(C.Name.is_eq(b, C.Program.name.wcon()), U32.is_eq(j, 5))), iff(C.Name.is_eq(b, C.Program.name.true()), U32.is_eq(j, 6)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4))), iff(C.Name.is_eq(b, C.Program.name.wcon()), U32.is_eq(j, 5))), iff(C.Name.is_eq(b, C.Program.name.true()), U32.is_eq(j, 6))), iff(C.Name.is_eq(b, C.Program.name.false()), U32.is_eq(j, 7)), h)))))))

def kn3(+j: U32, +b: List<&2, U32>, +h: {known.ok(j, b) == True{} : Bool}) ->
  {C.Name.is_eq(b, C.Program.name.u32()) == U32.is_eq(j, 3) : Bool}:
  iff_eq(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3), and_r(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3)), and_l(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4))), iff(C.Name.is_eq(b, C.Program.name.wcon()), U32.is_eq(j, 5)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4))), iff(C.Name.is_eq(b, C.Program.name.wcon()), U32.is_eq(j, 5))), iff(C.Name.is_eq(b, C.Program.name.true()), U32.is_eq(j, 6)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4))), iff(C.Name.is_eq(b, C.Program.name.wcon()), U32.is_eq(j, 5))), iff(C.Name.is_eq(b, C.Program.name.true()), U32.is_eq(j, 6))), iff(C.Name.is_eq(b, C.Program.name.false()), U32.is_eq(j, 7)), h))))))

def kn4(+j: U32, +b: List<&2, U32>, +h: {known.ok(j, b) == True{} : Bool}) ->
  {C.Name.is_eq(b, C.Program.name.wnil()) == U32.is_eq(j, 4) : Bool}:
  iff_eq(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4), and_r(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4))), iff(C.Name.is_eq(b, C.Program.name.wcon()), U32.is_eq(j, 5)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4))), iff(C.Name.is_eq(b, C.Program.name.wcon()), U32.is_eq(j, 5))), iff(C.Name.is_eq(b, C.Program.name.true()), U32.is_eq(j, 6)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4))), iff(C.Name.is_eq(b, C.Program.name.wcon()), U32.is_eq(j, 5))), iff(C.Name.is_eq(b, C.Program.name.true()), U32.is_eq(j, 6))), iff(C.Name.is_eq(b, C.Program.name.false()), U32.is_eq(j, 7)), h)))))

def kn5(+j: U32, +b: List<&2, U32>, +h: {known.ok(j, b) == True{} : Bool}) ->
  {C.Name.is_eq(b, C.Program.name.wcon()) == U32.is_eq(j, 5) : Bool}:
  iff_eq(C.Name.is_eq(b, C.Program.name.wcon()), U32.is_eq(j, 5), and_r(Bool.and(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4))), iff(C.Name.is_eq(b, C.Program.name.wcon()), U32.is_eq(j, 5)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4))), iff(C.Name.is_eq(b, C.Program.name.wcon()), U32.is_eq(j, 5))), iff(C.Name.is_eq(b, C.Program.name.true()), U32.is_eq(j, 6)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4))), iff(C.Name.is_eq(b, C.Program.name.wcon()), U32.is_eq(j, 5))), iff(C.Name.is_eq(b, C.Program.name.true()), U32.is_eq(j, 6))), iff(C.Name.is_eq(b, C.Program.name.false()), U32.is_eq(j, 7)), h))))

def kn6(+j: U32, +b: List<&2, U32>, +h: {known.ok(j, b) == True{} : Bool}) ->
  {C.Name.is_eq(b, C.Program.name.true()) == U32.is_eq(j, 6) : Bool}:
  iff_eq(C.Name.is_eq(b, C.Program.name.true()), U32.is_eq(j, 6), and_r(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4))), iff(C.Name.is_eq(b, C.Program.name.wcon()), U32.is_eq(j, 5))), iff(C.Name.is_eq(b, C.Program.name.true()), U32.is_eq(j, 6)), and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4))), iff(C.Name.is_eq(b, C.Program.name.wcon()), U32.is_eq(j, 5))), iff(C.Name.is_eq(b, C.Program.name.true()), U32.is_eq(j, 6))), iff(C.Name.is_eq(b, C.Program.name.false()), U32.is_eq(j, 7)), h)))

def kn7(+j: U32, +b: List<&2, U32>, +h: {known.ok(j, b) == True{} : Bool}) ->
  {C.Name.is_eq(b, C.Program.name.false()) == U32.is_eq(j, 7) : Bool}:
  iff_eq(C.Name.is_eq(b, C.Program.name.false()), U32.is_eq(j, 7), and_r(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(iff(C.Name.is_eq(b, C.Program.name.unit()), U32.is_eq(j, 0)), iff(C.Name.is_eq(b, C.Program.name.nil()), U32.is_eq(j, 1))), iff(C.Name.is_eq(b, C.Program.name.con()), U32.is_eq(j, 2))), iff(C.Name.is_eq(b, C.Program.name.u32()), U32.is_eq(j, 3))), iff(C.Name.is_eq(b, C.Program.name.wnil()), U32.is_eq(j, 4))), iff(C.Name.is_eq(b, C.Program.name.wcon()), U32.is_eq(j, 5))), iff(C.Name.is_eq(b, C.Program.name.true()), U32.is_eq(j, 6))), iff(C.Name.is_eq(b, C.Program.name.false()), U32.is_eq(j, 7)), h))

def lk(n: Maybe<&2, List<&2, U32>>, +j: U32, -k: List<&2, U32>, +e: {n == Some{k} : Maybe<&2, List<&2, U32>>},
  +h: {labok.of(n, j) == True{} : Bool}) -> {known.ok(j, k) == True{} : Bool}:
  %e : {labok.of(_, j) == True{} : Bool}
  h

# the name of a label cell compares as known.ok says
def LK(+f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +hok: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool}, +eL: {Lm(m, c) == True{} : Bool},
  -k: List<&2, U32>, +e: {T.tm.name(ks, Fd(2n, m, c)) == Some{k} : Maybe<&2, List<&2, U32>>}) ->
  {known.ok(Fd(2n, m, c), k) == True{} : Bool}:
  lk(T.tm.name(ks, Fd(2n, m, c)), Fd(2n, m, c), k, e, ok.lb(f, m, ks, img, c, im, fs, nx, hok, eL))

# a pair cell has the tag 10
def P_tag(+m: C.Cir.Cells, +c: U32, +eP: {Pm(m, c) == True{} : Bool}) -> {U32.is_eq(Tg(m, c), 10) == True{} : Bool}:
  +f0 = Fd(0n, m, c)
  +q = T.tm.quan(U32.and(U32.shrn(f0, 6n), 3))
  and_r(isQ1(q), U32.is_eq(U32.and(f0, 63), 10), Equal.trans(Bool, FP.r(f0), FP.l(f0), True{}, Equal.sym(Bool, FP.l(f0), FP.r(f0), fp(f0)), eP))

# the parts of a pair cell are cells that ok accepts, a level less deep
def ok.l(+f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +hok: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool}, +eP: {Pm(m, c) == True{} : Bool}) ->
  {ok(f, m, ks, img, Fd(2n, m, c), im, fs, nx) == True{} : Bool}:
  and_l(ok(f, m, ks, img, Fd(2n, m, c), im, fs, nx), ok(f, m, ks, img, Fd(3n, m, c), im, fs, nx), ok.kids(f, m, ks, img, c, im, fs, nx, hok, P_tag(m, c, eP)))

def ok.r(+f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +hok: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool}, +eP: {Pm(m, c) == True{} : Bool}) ->
  {ok(f, m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool}:
  and_r(ok(f, m, ks, img, Fd(2n, m, c), im, fs, nx), ok(f, m, ks, img, Fd(3n, m, c), im, fs, nx), ok.kids(f, m, ks, img, c, im, fs, nx, hok, P_tag(m, c, eP)))

# ok fails with no fuel
def ok.zero(-m: C.Cir.Cells, -ks: List<&2, List<&2, U32>>, -img: List<&2, C.Term>, -c: U32, -im: U32, -fs: U32, -nx: U32,
  +h: {ok(0n, m, ks, img, c, im, fs, nx) == True{} : Bool}) -> Empty:
  PN.false_ne_true(h)
# A bit's term is what CB reads
# ------------------------------

def unbit_eq(x6: Bool, x7: Bool) -> {C.Program.unbit.if(x6, x7) == CB.t(Bool.or(x6, x7), x6) : Maybe<&2, Bool>}:
  match x6 x7:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def BB.b(+k: List<&2, U32>, +g: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok2: {ok(1n+g, m, ks, img, Fd(2n, m, c), im, fs, nx) == True{} : Bool}, +eL: {Lm(m, Fd(2n, m, c)) == True{} : Bool},
  +ek: {T.tm.name(ks, Fd(2n, m, Fd(2n, m, c))) == Some{k} : Maybe<&2, List<&2, U32>>}) -> {Ub.x(Some{k}) == CB.x(True{}, Fd(2n, m, Fd(2n, m, c))) : Maybe<&2, Bool>}:
  +h = LK(g, m, ks, img, Fd(2n, m, c), im, fs, nx, hok2, eL, k, ek)
  %Equal.sym(Bool, C.Name.is_eq(k, C.Program.name.true()), U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 6), kn6(Fd(2n, m, Fd(2n, m, c)), k, h)) : {C.Program.unbit.if(_, C.Name.is_eq(k, C.Program.name.false())) == CB.x(True{}, Fd(2n, m, Fd(2n, m, c))) : Maybe<&2, Bool>}
  %Equal.sym(Bool, C.Name.is_eq(k, C.Program.name.false()), U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 7), kn7(Fd(2n, m, Fd(2n, m, c)), k, h)) : {C.Program.unbit.if(U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 6), _) == CB.x(True{}, Fd(2n, m, Fd(2n, m, c))) : Maybe<&2, Bool>}
  unbit_eq(U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 6), U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 7))

def BB.x(bx: Bool, +g: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok2: {ok(1n+g, m, ks, img, Fd(2n, m, c), im, fs, nx) == True{} : Bool}, +e: {Lm(m, Fd(2n, m, c)) == bx : Bool}) ->
  SpecM(T.tm.of(1n+g, m, ks, img, Fd(2n, m, c)), x => {Ub.x(VL(x)) == CB.x(bx, Fd(2n, m, Fd(2n, m, c))) : Maybe<&2, Bool>}):
  match bx:
    case False{}:
      cellNotL(g, m, ks, img, Fd(2n, m, c), im, fs, nx, x => {Ub.x(VL(x)) == CB.x(False{}, Fd(2n, m, Fd(2n, m, c))) : Maybe<&2, Bool>}, e, hok2,
        v => ev => Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, Bool>, mm => Ub.x(mm), VL(v), None{}, ev))
    case True{}:
      cellLab(g, m, ks, img, Fd(2n, m, c), x => {Ub.x(VL(x)) == CB.x(True{}, Fd(2n, m, Fd(2n, m, c))) : Maybe<&2, Bool>}, e,
        k => ek => BB.b(k, g, m, ks, img, c, im, fs, nx, hok2, e, ek))

def BB.u(o: Bool, +g: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok2: {ok(1n+g, m, ks, img, Fd(2n, m, c), im, fs, nx) == True{} : Bool}) ->
  SpecM(T.tm.of(1n+g, m, ks, img, Fd(2n, m, c)), x => {Ub.u(o, x) == CB.l(o, m, c) : Maybe<&2, Bool>}):
  match o:
    case False{}:
      SpecM.all(T.tm.of(1n+g, m, ks, img, Fd(2n, m, c)), x => {Ub.u(False{}, x) == CB.l(False{}, m, c) : Maybe<&2, Bool>}, x => {==})
    case True{}:
      BB.x(Lm(m, Fd(2n, m, c)), g, m, ks, img, c, im, fs, nx, hok2, {==})

def BB.k(+k: List<&2, U32>, +g: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok3: {ok(1n+g, m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool}, +hok2: {ok(1n+g, m, ks, img, Fd(2n, m, c), im, fs, nx) == True{} : Bool},
  +eL: {Lm(m, Fd(3n, m, c)) == True{} : Bool}, +ek: {T.tm.name(ks, Fd(2n, m, Fd(3n, m, c))) == Some{k} : Maybe<&2, List<&2, U32>>}) ->
  SpecM(T.tm.of(1n+g, m, ks, img, Fd(2n, m, c)), x => {Ub.y(Some{k}, x) == CB.l(Bool.and(True{}, U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0)), m, c) : Maybe<&2, Bool>}):
  %Equal.sym(Bool, C.Name.is_eq(k, C.Program.name.unit()), U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0), kn0(Fd(2n, m, Fd(3n, m, c)), k, LK(g, m, ks, img, Fd(3n, m, c), im, fs, nx, hok3, eL, k, ek))) :
    SpecM(T.tm.of(1n+g, m, ks, img, Fd(2n, m, c)), x => {Ub.u(_, x) == CB.l(U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0), m, c) : Maybe<&2, Bool>})
  BB.u(U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0), g, m, ks, img, c, im, fs, nx, hok2)

def BB.y(by: Bool, +g: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok3: {ok(1n+g, m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool}, +hok2: {ok(1n+g, m, ks, img, Fd(2n, m, c), im, fs, nx) == True{} : Bool}, +e: {Lm(m, Fd(3n, m, c)) == by : Bool}) ->
  SpecM(T.tm.of(1n+g, m, ks, img, Fd(3n, m, c)), y => SpecM(T.tm.of(1n+g, m, ks, img, Fd(2n, m, c)), x => {Ub.y(VL(y), x) == CB.l(Bool.and(by, U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0)), m, c) : Maybe<&2, Bool>})):
  match by:
    case False{}:
      cellNotL(g, m, ks, img, Fd(3n, m, c), im, fs, nx, y => SpecM(T.tm.of(1n+g, m, ks, img, Fd(2n, m, c)), x => {Ub.y(VL(y), x) == CB.l(Bool.and(False{}, U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0)), m, c) : Maybe<&2, Bool>}), e, hok3,
        v => ev => SpecM.all(T.tm.of(1n+g, m, ks, img, Fd(2n, m, c)), x => {Ub.y(VL(v), x) == CB.l(Bool.and(False{}, U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0)), m, c) : Maybe<&2, Bool>},
          x => Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, Bool>, mm => Ub.y(mm, x), VL(v), None{}, ev)))
    case True{}:
      cellLab(g, m, ks, img, Fd(3n, m, c), y => SpecM(T.tm.of(1n+g, m, ks, img, Fd(2n, m, c)), x => {Ub.y(VL(y), x) == CB.l(Bool.and(True{}, U32.is_eq(Fd(2n, m, Fd(3n, m, c)), 0)), m, c) : Maybe<&2, Bool>}), e,
        k => ek => BB.k(k, g, m, ks, img, c, im, fs, nx, hok3, hok2, e, ek))

def BB.p(b: Bool, +f: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok: {ok(1n+f, m, ks, img, c, im, fs, nx) == True{} : Bool}, +eb: {Pm(m, c) == b : Bool}) ->
  SpecM(T.tm.of(1n+f, m, ks, img, c), t => {Ub(t) == CB.p(b, m, c) : Maybe<&2, Bool>}):
  match b:
    case False{}:
      cellNotT1(f, m, ks, img, c, im, fs, nx, t => {Ub(t) == CB.p(False{}, m, c) : Maybe<&2, Bool>}, eb, hok,
        v => ev => Equal.cong(Maybe<&2, TP>, Maybe<&2, Bool>, mm => Ub.r(mm), V1(v), None{}, ev))
    case True{}:
      match f:
        case 0n:
          cellT1(0n, m, ks, img, c, t => {Ub(t) == CB.p(True{}, m, c) : Maybe<&2, Bool>}, eb, Unit{})
        case 1n+g:
          cellT1(1n+g, m, ks, img, c, t => {Ub(t) == CB.p(True{}, m, c) : Maybe<&2, Bool>}, eb,
            SpecM.swap(T.tm.of(1n+g, m, ks, img, Fd(2n, m, c)), T.tm.of(1n+g, m, ks, img, Fd(3n, m, c)), x => y => {Ub(C.Term.Tup{C.Quan.Q1{}, x, y}) == CB.p(True{}, m, c) : Maybe<&2, Bool>},
              BB.y(Lm(m, Fd(3n, m, c)), g, m, ks, img, c, im, fs, nx, ok.r(1n+g, m, ks, img, c, im, fs, nx, hok, eb), ok.l(1n+g, m, ks, img, c, im, fs, nx, hok, eb), {==})))

# the term of a cell is a bit as CB reads it
def BB(+fb: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32, +hok: {ok(fb, m, ks, img, c, im, fs, nx) == True{} : Bool}) -> SpecM(T.tm.of(fb, m, ks, img, c), t => {Ub(t) == CB(m, c) : Maybe<&2, Bool>}):
  match fb:
    case 0n:
      Empty.absurd(SpecM(T.tm.of(0n, m, ks, img, c), t => {Ub(t) == CB(m, c) : Maybe<&2, Bool>}), ok.zero(m, ks, img, c, im, fs, nx, hok))
    case 1n+f:
      BB.p(Pm(m, c), f, m, ks, img, c, im, fs, nx, hok, {==})
