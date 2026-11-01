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

# a bit of a word, the cell c holding WCon: Some of its bit when the cells
# have the form that the machine reads
def GB.z(x: Bool, b: Bool) -> Maybe<&2, Bool>:
  match b:
    case True{}:
      Some{x}
    case False{}:
      None{}

def GB.r(x: Bool, b: Bool, +m: C.Cir.Cells, +rc: U32) -> Maybe<&2, Bool>:
  match b:
    case True{}:
      GB.z(x, LAST(m, rc))
    case False{}:
      None{}

def GB.b(mb: Maybe<&2, Bool>, +m: C.Cir.Cells, +rc: U32) -> Maybe<&2, Bool>:
  match mb:
    case Some{x}:
      GB.r(x, Pm(m, rc), m, rc)
    case None{}:
      None{}

def GB.f(b: Bool, +m: C.Cir.Cells, +fc: U32) -> Maybe<&2, Bool>:
  match b:
    case True{}:
      GB.b(CB(m, Fd(2n, m, fc)), m, Fd(3n, m, fc))
    case False{}:
      None{}

def GB.l(b: Bool, +m: C.Cir.Cells, +fc: U32) -> Maybe<&2, Bool>:
  match b:
    case True{}:
      GB.f(Pm(m, fc), m, fc)
    case False{}:
      None{}

def GB.p(b: Bool, +m: C.Cir.Cells, +c: U32) -> Maybe<&2, Bool>:
  match b:
    case True{}:
      GB.l(ISLAB(m, c, 5), m, Fd(3n, m, c))
    case False{}:
      None{}

def GB(+m: C.Cir.Cells, +c: U32) -> Maybe<&2, Bool>:
  GB.p(Pm(m, c), m, c)

# the bit g, below the word rec
def W1.g(-q: Nat, g: Maybe<&2, Bool>, rec: Maybe<&2, Word(q)>) -> Maybe<&2, Word(1n+q)>:
  match g:
    case Some{x}:
      W1.w(q, x, rec)
    case None{}:
      None{}

# the cell of the word after the word of the cell c
def CW.next(+m: C.Cir.Cells, +c: U32) -> U32:
  Fd(2n, m, Fd(3n, m, Fd(3n, m, c)))

def CW(p: Nat, +m: C.Cir.Cells, +c: U32) -> Maybe<&2, Word(p)>:
  match p:
    case 0n:
      CW0.p(Pm(m, c), m, c)
    case 1n+q:
      W1.g(q, GB(m, c), CW(q, m, CW.next(m, c)))

# the p bits of the word of the cell c, with no WNil after them
def CWb(p: Nat, +m: C.Cir.Cells, +c: U32) -> Maybe<&2, Word(p)>:
  match p:
    case 0n:
      Some{WNil{}}
    case 1n+q:
      W1.g(q, GB(m, c), CWb(q, m, CW.next(m, c)))

# the cell after p bits of the word of the cell c
def Nx(p: Nat, +m: C.Cir.Cells, +c: U32) -> U32:
  match p:
    case 0n:
      c
    case 1n+q:
      Nx(q, m, CW.next(m, c))

# the word r, when the end t is there
def CWt(-p: Nat, r: Maybe<&2, Word(p)>, t: Maybe<&2, Word(0n)>) -> Maybe<&2, Word(p)>:
  match r t:
    case Some{w} Some{_}:
      Some{w}
    case _ _:
      None{}

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

# Runs
# ----
#
# Wp(o, K, H): the run o goes on with a state of which K holds, halts with a
# status and a state of which H holds, or runs out of memory; it never traps
# and never runs out of fuel. A run needs fuel of the form 1 + f to take a
# step. The registers of a state are RG: the registers xs with the spine of
# their first 64 made explicit, and those that M.out sets (oc, ow, ov, oi,
# t1, t2) put in, so that reading and setting a register computes.

def Wp(o: C.Cir.Out, K: C.Cir.State -> Type, H: U32 -> C.Cir.State -> Type) -> Type:
  match o:
    case C.Cir.Out.next{st}:
      K(st)
    case C.Cir.Out.halt{s, st}:
      H(s, st)
    case C.Cir.Out.out_of_memory{}:
      Unit
    case C.Cir.Out.trap{}:
      Empty
    case C.Cir.Out.not_done{}:
      Empty

def Wp.then(o: C.Cir.Out, -k: C.Cir.State -> C.Cir.Out, -K: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type,
  h: Wp(o, t => Wp(k(t), K, H), H)) -> Wp(C.Cir.exec.then(o, k), K, H):
  match o:
    case C.Cir.Out.next{st}:
      h
    case C.Cir.Out.halt{s, st}:
      h
    case C.Cir.Out.out_of_memory{}:
      Unit{}
    case C.Cir.Out.trap{}:
      match h:
    case C.Cir.Out.not_done{}:
      match h:

# a then b
def Wp.seq(+f: Nat, +a: C.Cir.Stmt, +b: C.Cir.Stmt, +st: C.Cir.State, -K: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type,
  h: Wp(C.Cir.exec(1n+f, a, st), t => Wp(C.Cir.exec(1n+f, b, t), K, H), H)) -> Wp(C.Cir.exec(1n+f, C.Cir.Stmt.seq{a, b}, st), K, H):
  Wp.then(C.Cir.exec(1n+f, a, st), t => C.Cir.exec(1n+f, b, t), K, H, h)

# the parts of a state
def St.rg(st: C.Cir.State) -> List<&2, U32>:
  match st:
    case C.Cir.State{x, _, _, _, _, _, _, _, _, _}:
      x

def St.cl(st: C.Cir.State) -> C.Cir.Cells:
  match st:
    case C.Cir.State{_, x, _, _, _, _, _, _, _, _}:
      x

def St.nx(st: C.Cir.State) -> U32:
  match st:
    case C.Cir.State{_, _, x, _, _, _, _, _, _, _}:
      x

def St.fs(st: C.Cir.State) -> U32:
  match st:
    case C.Cir.State{_, _, _, x, _, _, _, _, _, _}:
      x

def St.im(st: C.Cir.State) -> U32:
  match st:
    case C.Cir.State{_, _, _, _, x, _, _, _, _, _}:
      x

def St.lim(st: C.Cir.State) -> U32:
  match st:
    case C.Cir.State{_, _, _, _, _, _, x, _, _, _}:
      x

def St.inp(st: C.Cir.State) -> List<&2, U32>:
  match st:
    case C.Cir.State{_, _, _, _, _, _, _, x, _, _}:
      x

def St.out(st: C.Cir.State) -> List<&2, U32>:
  match st:
    case C.Cir.State{_, _, _, _, _, _, _, _, x, _}:
      x

def St.outn(st: C.Cir.State) -> U32:
  match st:
    case C.Cir.State{_, _, _, _, _, _, _, _, _, x}:
      x

# the cell i is one that the state lets the machine read
def St.ok(+i: U32, +st: C.Cir.State) -> Bool:
  C.Cir.is_cell(i, St.im(st), St.fs(st), St.nx(st))

# the registers
def Rg.hd(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{h, _}:
      h

def Rg.tl(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{_, t}:
      t

def Rg.pre(n: Nat, +xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{Rg.hd(xs), Rg.pre(p, Rg.tl(xs))}

def Rg.drop(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      xs
    case 1n+p:
      Rg.drop(p, Rg.tl(xs))

def Rg.sp(+xs: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, Rg.pre(64n, xs), Rg.drop(64n, xs))

# a list of n registers or more is its first n, then the rest
def Rg.sp_eq(n: Nat, +xs: List<&2, U32>, h: PN.Le(n, List.length(&2, U32, xs))) ->
  {List.append(&2, U32, Rg.pre(n, xs), Rg.drop(n, xs)) == xs : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match xs:
        case Nil{}:
          Empty.absurd({List.append(&2, U32, Rg.pre(1n+p, Nil{}), Rg.drop(1n+p, Nil{})) == Nil{} : List<&2, U32>}, h)
        case Con{+x, +t}:
          %Rg.sp_eq(p, t, h) : {Con{x, List.append(&2, U32, Rg.pre(p, t), Rg.drop(p, t))} == Con{x, _} : List<&2, U32>}
          {==}

def RG(+xs: List<&2, U32>, +oc: U32, +ow: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32) -> List<&2, U32>:
  List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32,
    Rg.sp(xs), 45n, oc), 46n, ow), 47n, ov), 48n, oi), 62n, t1), 63n, t2)

# the state b with the registers of M.out, the pages and the output
def ST(+b: C.Cir.State, +oc: U32, +ow: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32, +pg: U32, +out: List<&2, U32>, +outn: U32) ->
  C.Cir.State:
  C.Cir.State{RG(St.rg(b), oc, ow, ov, oi, t1, t2), St.cl(b), St.nx(b), St.fs(b), St.im(b), pg, St.lim(b), St.inp(b), out, outn}

# the state after the byte v goes out, with p pages
def St.emit(st: C.Cir.State, +p: U32, +v: U32) -> C.Cir.State:
  match st:
    case C.Cir.State{rg, cl, nx, fs, im, _, lim, inp, out, outn}:
      C.Cir.State{rg, cl, nx, fs, im, p, lim, inp, Con{U32.and(v, 255), out}, U32.inc(outn)}

# the field k of the cell that e gives
def ev.f(+k: Nat, +e: C.Cir.Expr, +st: C.Cir.State, +i: U32, +ei: {Some{i} == C.Cir.eval(e, st) : Maybe<&2, U32>},
  +ec: {True{} == St.ok(i, st) : Bool}) -> {Some{Fd(k, St.cl(st), i)} == C.Cir.eval(C.Cir.Expr.field{k, e}, st) : Maybe<&2, U32>}:
  match st:
    case C.Cir.State{+rg, +cl, +nx, +fs, +im, +pg, +lim, +inp, +out, +outn}:
      %ei : {Some{Fd(k, cl, i)} == C.Cir.eval.field(k, _, C.Cir.State{rg, cl, nx, fs, im, pg, lim, inp, out, outn}) : Maybe<&2, U32>}
      %ec : {Some{Fd(k, cl, i)} == C.Cir.eval.field.if(_, k, cl, i) : Maybe<&2, U32>}
      {==}

def and_u32(a: Bool, b: Bool) -> {Bool.to_u32(Bool.and(a, b)) == U32.and(Bool.to_u32(a), Bool.to_u32(b)) : U32}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def or_u32(a: Bool, b: Bool) -> {Bool.to_u32(Bool.or(a, b)) == U32.or(Bool.to_u32(a), Bool.to_u32(b)) : U32}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# M.pair on the cell of register r
def ev.pair(+r: Nat, +st: C.Cir.State, +i: U32, +er: {Some{i} == C.Cir.eval(C.M.g(r), st) : Maybe<&2, U32>},
  +ec: {True{} == St.ok(i, st) : Bool}) -> {Some{Bool.to_u32(Pm(St.cl(st), i))} == C.Cir.eval(C.M.pair(r), st) : Maybe<&2, U32>}:
  %ev.f(0n, C.M.g(r), st, i, er, ec) :
    {Some{Bool.to_u32(Pm(St.cl(st), i))} == C.Cir.eval.op(C.Wasm.Op.eq{}, C.Cir.eval.op(C.Wasm.Op.and{}, _, Some{255}), Some{74}) : Maybe<&2, U32>}
  {==}

# M.is_lab on field k of the cell of register r
def ev.islab(+k: Nat, +r: Nat, +n: U32, +st: C.Cir.State, +i: U32, +er: {Some{i} == C.Cir.eval(C.M.g(r), st) : Maybe<&2, U32>},
  +ec: {True{} == St.ok(i, st) : Bool}, +eck: {True{} == St.ok(Fd(k, St.cl(st), i), st) : Bool}) ->
  {Some{Bool.to_u32(Bool.and(Lm(St.cl(st), Fd(k, St.cl(st), i)), U32.is_eq(Fd(2n, St.cl(st), Fd(k, St.cl(st), i)), n)))} == C.Cir.eval(C.M.is_lab(C.M.f(k, C.M.g(r)), n), st) : Maybe<&2, U32>}:
  +m = St.cl(st)
  +j = Fd(k, m, i)
  +ej = ev.f(k, C.M.g(r), st, i, er, ec)
  %ev.f(0n, C.M.f(k, C.M.g(r)), st, j, ej, eck) :
    {Some{Bool.to_u32(Bool.and(Lm(m, j), U32.is_eq(Fd(2n, m, j), n)))} == C.Cir.eval.op(C.Wasm.Op.and{}, C.Cir.eval.op(C.Wasm.Op.eq{}, C.Cir.eval.op(C.Wasm.Op.and{}, _, Some{63}), Some{13}),
      C.Cir.eval.op(C.Wasm.Op.eq{}, C.Cir.eval(C.M.f(2n, C.M.f(k, C.M.g(r))), st), Some{n})) : Maybe<&2, U32>}
  %ev.f(2n, C.M.f(k, C.M.g(r)), st, j, ej, eck) :
    {Some{Bool.to_u32(Bool.and(Lm(m, j), U32.is_eq(Fd(2n, m, j), n)))} == C.Cir.eval.op(C.Wasm.Op.and{}, Some{Bool.to_u32(Lm(m, j))},
      C.Cir.eval.op(C.Wasm.Op.eq{}, _, Some{n})) : Maybe<&2, U32>}
  %and_u32(Lm(m, j), U32.is_eq(Fd(2n, m, j), n)) : {Some{Bool.to_u32(Bool.and(Lm(m, j), U32.is_eq(Fd(2n, m, j), n)))} == Some{_} : Maybe<&2, U32>}
  {==}

# M.eq(M.tag(field k), lab) on the cell of register r
def ev.tag(+k: Nat, +r: Nat, +st: C.Cir.State, +i: U32, +er: {Some{i} == C.Cir.eval(C.M.g(r), st) : Maybe<&2, U32>},
  +ec: {True{} == St.ok(i, st) : Bool}, +eck: {True{} == St.ok(Fd(k, St.cl(st), i), st) : Bool}) ->
  {Some{Bool.to_u32(Lm(St.cl(st), Fd(k, St.cl(st), i)))} == C.Cir.eval(C.M.eq(C.M.tag(C.M.f(k, C.M.g(r))), C.M.c(13)), st) : Maybe<&2, U32>}:
  +m = St.cl(st)
  +j = Fd(k, m, i)
  %ev.f(0n, C.M.f(k, C.M.g(r)), st, j, ev.f(k, C.M.g(r), st, i, er, ec), eck) :
    {Some{Bool.to_u32(Lm(m, j))} == C.Cir.eval.op(C.Wasm.Op.eq{}, C.Cir.eval.op(C.Wasm.Op.and{}, _, Some{63}), Some{13}) : Maybe<&2, U32>}
  {==}

# field k2 of field k1 of the cell of register r
def ev.ff(+k1: Nat, +k2: Nat, +r: Nat, +st: C.Cir.State, +i: U32, +er: {Some{i} == C.Cir.eval(C.M.g(r), st) : Maybe<&2, U32>},
  +ec: {True{} == St.ok(i, st) : Bool}, +eck: {True{} == St.ok(Fd(k1, St.cl(st), i), st) : Bool}) ->
  {Some{Fd(k2, St.cl(st), Fd(k1, St.cl(st), i))} == C.Cir.eval(C.M.f(k2, C.M.f(k1, C.M.g(r))), st) : Maybe<&2, U32>}:
  ev.f(k2, C.M.f(k1, C.M.g(r)), st, Fd(k1, St.cl(st), i), ev.f(k1, C.M.g(r), st, i, er, ec), eck)

# Statements
def Wp.set(+f: Nat, +r: Nat, +e: C.Cir.Expr, +st: C.Cir.State, -K: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type, +v: U32,
  +ev: {Some{v} == C.Cir.eval(e, st) : Maybe<&2, U32>}, h: Wp(C.Cir.exec.set(r, Some{v}, st), K, H)) ->
  Wp(C.Cir.exec(1n+f, C.Cir.Stmt.set{r, e}, st), K, H):
  %ev : Wp(C.Cir.exec.set(r, _, st), K, H)
  h

# X when b holds, else Y
def IFT(b: Bool, X: Type, Y: Type) -> Type:
  match b:
    case True{}:
      X
    case False{}:
      Y

# the case of b, with a passed to it
def CasesK(b: Bool, -A: Type, a: A, -X: Type, -Y: Type, t: A -> {b == True{} : Bool} -> X, e: A -> {b == False{} : Bool} -> Y) ->
  IFT(b, X, Y):
  match b:
    case True{}:
      t(a, {==})
    case False{}:
      e(a, {==})

def Wp.if(+f: Nat, +c: C.Cir.Expr, +t: C.Cir.Stmt, +e: C.Cir.Stmt, +st: C.Cir.State, -K: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type,
  b: Bool, +ev: {Some{Bool.to_u32(b)} == C.Cir.eval(c, st) : Maybe<&2, U32>},
  g: IFT(b, Wp(C.Cir.exec(1n+f, t, st), K, H), Wp(C.Cir.exec(1n+f, e, st), K, H))) ->
  Wp(C.Cir.exec(1n+f, C.Cir.Stmt.if{c, t, e}, st), K, H):
  match b:
    case True{}:
      %ev : Wp(C.Cir.exec.if(_, u => C.Cir.exec(1n+f, t, st), u => C.Cir.exec(1n+f, e, st)), K, H)
      g
    case False{}:
      %ev : Wp(C.Cir.exec.if(_, u => C.Cir.exec(1n+f, t, st), u => C.Cir.exec(1n+f, e, st)), K, H)
      g

def Wp.need(+f: Nat, +c: C.Cir.Expr, +t: C.Cir.Stmt, +st: C.Cir.State, -K: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type,
  b: Bool, +ev: {Some{Bool.to_u32(b)} == C.Cir.eval(c, st) : Maybe<&2, U32>},
  g: IFT(b, Wp(C.Cir.exec(1n+f, t, st), K, H), H(2, st))) ->
  Wp(C.Cir.exec(1n+f, C.M.need(c, t), st), K, H):
  Wp.if(f, c, t, C.M.halt(2), st, K, H, b, ev, g)

def Wp.emit.of(pages: Maybe<&2, U32>, +v: U32, +st: C.Cir.State, -K: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type,
  h: @p: U32 -> K(St.emit(st, p, v))) -> Wp(C.Cir.exec.emit.of(pages, v, st), K, H):
  match pages:
    case None{}:
      Unit{}
    case Some{+p}:
      match st:
        case C.Cir.State{+rg, +cl, +nx, +fs, +im, +pg, +lim, +inp, +out, +outn}:
          h(p)

def Wp.emit.if(ok: Bool, +bb: U32, +v: U32, +st: C.Cir.State, -K: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type,
  h: @p: U32 -> K(St.emit(st, p, v))) -> Wp(C.Cir.exec.emit.if(ok, bb, v, st), K, H):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      match st:
        case C.Cir.State{+rg, +cl, +nx, +fs, +im, +pg, +lim, +inp, +out, +outn}:
          Wp.emit.of(C.Cir.room(bb, pg, lim), v, C.Cir.State{rg, cl, nx, fs, im, pg, lim, inp, out, outn}, K, H, h)

def Wp.emit(+f: Nat, +e: C.Cir.Expr, +st: C.Cir.State, -K: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type, +v: U32,
  +ev: {Some{v} == C.Cir.eval(e, st) : Maybe<&2, U32>}, h: @p: U32 -> K(St.emit(st, p, v))) ->
  Wp(C.Cir.exec(1n+f, C.Cir.Stmt.emit{e}, st), K, H):
  match st:
    case C.Cir.State{+rg, +cl, +nx, +fs, +im, +pg, +lim, +inp, +out, +outn}:
      %ev : Wp(C.Cir.exec.emit(_, C.Cir.State{rg, cl, nx, fs, im, pg, lim, inp, out, outn}), K, H)
      Wp.emit.if(Bool.and(U32.is_lt(nx, 214748365), U32.is_ge(U32.add(C.Cir.at(nx), outn), outn)), U32.add(C.Cir.at(nx), outn), v,
        C.Cir.State{rg, cl, nx, fs, im, pg, lim, inp, out, outn}, K, H, h)

# ok, read with any fuel
def Pr(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def ok.isc(+n: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +h: {ok(n, m, ks, img, c, im, fs, nx) == True{} : Bool}) -> {True{} == C.Cir.is_cell(c, im, fs, nx) : Bool}:
  match n:
    case 0n:
      Empty.absurd({True{} == C.Cir.is_cell(c, im, fs, nx) : Bool}, ok.zero(m, ks, img, c, im, fs, nx, h))
    case 1n+f:
      Equal.sym(Bool, C.Cir.is_cell(c, im, fs, nx), True{}, ok.cell(f, m, ks, img, c, im, fs, nx, h))

def ok.L(+n: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +h: {ok(n, m, ks, img, c, im, fs, nx) == True{} : Bool}, +eP: {Pm(m, c) == True{} : Bool}) ->
  {ok(Pr(n), m, ks, img, Fd(2n, m, c), im, fs, nx) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({ok(0n, m, ks, img, Fd(2n, m, c), im, fs, nx) == True{} : Bool}, ok.zero(m, ks, img, c, im, fs, nx, h))
    case 1n+f:
      ok.l(f, m, ks, img, c, im, fs, nx, h, eP)

def ok.R(+n: Nat, +m: C.Cir.Cells, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +c: U32, +im: U32, +fs: U32, +nx: U32,
  +h: {ok(n, m, ks, img, c, im, fs, nx) == True{} : Bool}, +eP: {Pm(m, c) == True{} : Bool}) ->
  {ok(Pr(n), m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({ok(0n, m, ks, img, Fd(3n, m, c), im, fs, nx) == True{} : Bool}, ok.zero(m, ks, img, c, im, fs, nx, h))
    case 1n+f:
      ok.r(f, m, ks, img, c, im, fs, nx, h, eP)

# The bit
# -------

# the value of ov once the bit x is read, at the index oi
def OV(x: Bool, +ov: U32, +oi: U32) -> U32:
  match x:
    case True{}:
      U32.or(ov, C.Wasm.op(C.Wasm.Op.shl{}, 1, oi))
    case False{}:
      ov

def MB.o() -> C.Cir.Stmt:
  C.M.set(C.R.ov(), C.M.or(C.M.g(C.R.ov()), C.M.shl(C.M.c(1), C.M.g(C.R.oi()))))

def MB.b() -> C.Cir.Stmt:
  C.M.need(C.M.or(C.M.eq(C.M.g(C.R.t2()), C.M.c(C.N.true())), C.M.eq(C.M.g(C.R.t2()), C.M.c(C.N.false()))),
    C.M.when(C.M.eq(C.M.g(C.R.t2()), C.M.c(C.N.true())), MB.o()))

def MB.a() -> C.Cir.Stmt:
  C.M.set(C.R.t2(), C.M.f(2n, C.M.f(2n, C.M.g(C.R.t1()))))

def MB.s2() -> C.Cir.Stmt:
  C.M.need(C.M.eq(C.M.tag(C.M.f(2n, C.M.g(C.R.t1()))), C.M.c(C.T.lab())), C.M.do([MB.a(), MB.b()]))

def MB.s1() -> C.Cir.Stmt:
  C.M.need(C.M.last(C.R.t1()), MB.s2())

# CB's value, once its tests pass
def CB.ok(+m: C.Cir.Cells, +c: U32, +eP: {Pm(m, c) == True{} : Bool}, +eL: {LAST(m, c) == True{} : Bool},
  +eM: {Lm(m, Fd(2n, m, c)) == True{} : Bool},
  +eO: {Bool.or(U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 6), U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 7)) == True{} : Bool}) ->
  {CB(m, c) == Some{U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 6)} : Maybe<&2, Bool>}:
  +x2 = Fd(2n, m, Fd(2n, m, c))
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {CB.p(_, m, c) == Some{U32.is_eq(x2, 6)} : Maybe<&2, Bool>}
  %Equal.sym(Bool, LAST(m, c), True{}, eL) : {CB.l(_, m, c) == Some{U32.is_eq(x2, 6)} : Maybe<&2, Bool>}
  %Equal.sym(Bool, Lm(m, Fd(2n, m, c)), True{}, eM) : {CB.x(_, x2) == Some{U32.is_eq(x2, 6)} : Maybe<&2, Bool>}
  %Equal.sym(Bool, Bool.or(U32.is_eq(x2, 6), U32.is_eq(x2, 7)), True{}, eO) : {CB.t(_, U32.is_eq(x2, 6)) == Some{U32.is_eq(x2, 6)} : Maybe<&2, Bool>}
  {==}

def CB.n1(+m: C.Cir.Cells, +c: U32, +eP: {Pm(m, c) == False{} : Bool}) -> {CB(m, c) == None{} : Maybe<&2, Bool>}:
  Equal.cong(Bool, Maybe<&2, Bool>, x => CB.p(x, m, c), Pm(m, c), False{}, eP)

def CB.n2(+m: C.Cir.Cells, +c: U32, +eP: {Pm(m, c) == True{} : Bool}, +eL: {LAST(m, c) == False{} : Bool}) -> {CB(m, c) == None{} : Maybe<&2, Bool>}:
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {CB.p(_, m, c) == None{} : Maybe<&2, Bool>}
  Equal.cong(Bool, Maybe<&2, Bool>, x => CB.l(x, m, c), LAST(m, c), False{}, eL)

def CB.n3(+m: C.Cir.Cells, +c: U32, +eP: {Pm(m, c) == True{} : Bool}, +eL: {LAST(m, c) == True{} : Bool},
  +eM: {Lm(m, Fd(2n, m, c)) == False{} : Bool}) -> {CB(m, c) == None{} : Maybe<&2, Bool>}:
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {CB.p(_, m, c) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Bool, LAST(m, c), True{}, eL) : {CB.l(_, m, c) == None{} : Maybe<&2, Bool>}
  Equal.cong(Bool, Maybe<&2, Bool>, x => CB.x(x, Fd(2n, m, Fd(2n, m, c))), Lm(m, Fd(2n, m, c)), False{}, eM)

def CB.n4(+m: C.Cir.Cells, +c: U32, +eP: {Pm(m, c) == True{} : Bool}, +eL: {LAST(m, c) == True{} : Bool},
  +eM: {Lm(m, Fd(2n, m, c)) == True{} : Bool},
  +eO: {Bool.or(U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 6), U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 7)) == False{} : Bool}) ->
  {CB(m, c) == None{} : Maybe<&2, Bool>}:
  +x2 = Fd(2n, m, Fd(2n, m, c))
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {CB.p(_, m, c) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Bool, LAST(m, c), True{}, eL) : {CB.l(_, m, c) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Bool, Lm(m, Fd(2n, m, c)), True{}, eM) : {CB.x(_, x2) == None{} : Maybe<&2, Bool>}
  Equal.cong(Bool, Maybe<&2, Bool>, x => CB.t(x, U32.is_eq(x2, 6)), Bool.or(U32.is_eq(x2, 6), U32.is_eq(x2, 7)), False{}, eO)

# X(x) for Some{x}, else Y
def MC(r: Maybe<&2, Bool>, X: Bool -> Type, Y: Type) -> Type:
  match r:
    case Some{x}:
      X(x)
    case None{}:
      Y

# the case of r, with a passed to it
def CasesM(r: Maybe<&2, Bool>, -A: Type, a: A, -X: Bool -> Type, -Y: Type, s: A -> @x: Bool -> {r == Some{x} : Maybe<&2, Bool>} -> X(x),
  n: A -> {r == None{} : Maybe<&2, Bool>} -> Y) -> MC(r, X, Y):
  match r:
    case Some{x}:
      s(a, x, {==})
    case None{}:
      n(a, {==})

# what the run of a bit goes on with, by what CB reads: its value in ov, or
# no result
def MB.Kc(+b: C.Cir.State, +oc: U32, +ow: U32, +ov: U32, +oi: U32, +c: U32, +pg: U32, +out: List<&2, U32>, +outn: U32,
  -K: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type) -> Type:
  @r: Maybe<&2, Bool> -> {CB(St.cl(b), c) == r : Maybe<&2, Bool>} ->
    MC(r, x => K(ST(b, oc, ow, OV(x, ov, oi), oi, c, Fd(2n, St.cl(b), Fd(2n, St.cl(b), c)), pg, out, outn)), @st: C.Cir.State -> H(2, st))

# M.out.bit on the cell c in t1: the bit that CB reads goes into ov, or the
# run ends with no result
def MB(+f: Nat, +b: C.Cir.State, +oc: U32, +ow: U32, +ov: U32, +oi: U32, +c: U32, +t2: U32, +pg: U32, +out: List<&2, U32>, +outn: U32,
  +nb: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, -K: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type,
  +hok: {ok(nb, St.cl(b), ks, img, c, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  kk: MB.Kc(b, oc, ow, ov, oi, c, pg, out, outn, K, H)) ->
  Wp(C.Cir.exec(1n+f, C.M.out.bit(), ST(b, oc, ow, ov, oi, c, t2, pg, out, outn)), K, H):
  +m = St.cl(b)
  +s0 = ST(b, oc, ow, ov, oi, c, t2, pg, out, outn)
  +x2 = Fd(2n, m, Fd(2n, m, c))
  +s1 = ST(b, oc, ow, ov, oi, c, x2, pg, out, outn)
  +hc = ok.isc(nb, m, ks, img, c, St.im(b), St.fs(b), St.nx(b), hok)
  -A = MB.Kc(b, oc, ow, ov, oi, c, pg, out, outn, K, H)
  Wp.need(f, C.M.pair(C.R.t1()), MB.s1(), s0, K, H, Pm(m, c), ev.pair(62n, s0, c, {==}, hc),
   CasesK(Pm(m, c), A, kk, Wp(C.Cir.exec(1n+f, MB.s1(), s0), K, H), H(2, s0),
    kk => +eP =>
      Wp.need(f, C.M.last(C.R.t1()), MB.s2(), s0, K, H, LAST(m, c),
        ev.islab(3n, 62n, 0, s0, c, {==}, hc, ok.isc(Pr(nb), m, ks, img, Fd(3n, m, c), St.im(b), St.fs(b), St.nx(b), ok.R(nb, m, ks, img, c, St.im(b), St.fs(b), St.nx(b), hok, eP))),
       CasesK(LAST(m, c), A, kk, Wp(C.Cir.exec(1n+f, MB.s2(), s0), K, H), H(2, s0),
        kk => +eL =>
          Wp.need(f, C.M.eq(C.M.tag(C.M.f(2n, C.M.g(C.R.t1()))), C.M.c(C.T.lab())), C.M.do([MB.a(), MB.b()]), s0, K, H, Lm(m, Fd(2n, m, c)),
            ev.tag(2n, 62n, s0, c, {==}, hc, ok.isc(Pr(nb), m, ks, img, Fd(2n, m, c), St.im(b), St.fs(b), St.nx(b), ok.L(nb, m, ks, img, c, St.im(b), St.fs(b), St.nx(b), hok, eP))),
           CasesK(Lm(m, Fd(2n, m, c)), A, kk, Wp(C.Cir.exec(1n+f, C.M.do([MB.a(), MB.b()]), s0), K, H), H(2, s0),
            kk => +eM =>
              Wp.seq(f, MB.a(), C.M.do([MB.b()]), s0, K, H,
                Wp.set(f, 63n, C.M.f(2n, C.M.f(2n, C.M.g(C.R.t1()))), s0, t => Wp(C.Cir.exec(1n+f, C.M.do([MB.b()]), t), K, H), H, x2,
                  ev.ff(2n, 2n, 62n, s0, c, {==}, hc, ok.isc(Pr(nb), m, ks, img, Fd(2n, m, c), St.im(b), St.fs(b), St.nx(b), ok.L(nb, m, ks, img, c, St.im(b), St.fs(b), St.nx(b), hok, eP))),
                  Wp.seq(f, MB.b(), C.Cir.Stmt.nop{}, s1, K, H,
                    Wp.need(f, C.M.or(C.M.eq(C.M.g(C.R.t2()), C.M.c(C.N.true())), C.M.eq(C.M.g(C.R.t2()), C.M.c(C.N.false()))),
                      C.M.when(C.M.eq(C.M.g(C.R.t2()), C.M.c(C.N.true())), MB.o()), s1, t => Wp(C.Cir.exec(1n+f, C.Cir.Stmt.nop{}, t), K, H), H,
                      Bool.or(U32.is_eq(x2, 6), U32.is_eq(x2, 7)),
                      Equal.cong(U32, Maybe<&2, U32>, x => Some{x}, Bool.to_u32(Bool.or(U32.is_eq(x2, 6), U32.is_eq(x2, 7))),
                        U32.or(Bool.to_u32(U32.is_eq(x2, 6)), Bool.to_u32(U32.is_eq(x2, 7))), or_u32(U32.is_eq(x2, 6), U32.is_eq(x2, 7))),
                     CasesK(Bool.or(U32.is_eq(x2, 6), U32.is_eq(x2, 7)), A, kk,
                      Wp(C.Cir.exec(1n+f, C.M.when(C.M.eq(C.M.g(C.R.t2()), C.M.c(C.N.true())), MB.o()), s1), t => Wp(C.Cir.exec(1n+f, C.Cir.Stmt.nop{}, t), K, H), H), H(2, s1),
                      kk => +eO =>
                        Wp.if(f, C.M.eq(C.M.g(C.R.t2()), C.M.c(C.N.true())), MB.o(), C.Cir.Stmt.nop{}, s1, t => Wp(C.Cir.exec(1n+f, C.Cir.Stmt.nop{}, t), K, H), H,
                          U32.is_eq(x2, 6), {==},
                         CasesK(U32.is_eq(x2, 6), A, kk,
                          Wp(C.Cir.exec(1n+f, MB.o(), s1), t => Wp(C.Cir.exec(1n+f, C.Cir.Stmt.nop{}, t), K, H), H),
                          Wp(C.Cir.exec(1n+f, C.Cir.Stmt.nop{}, s1), t => Wp(C.Cir.exec(1n+f, C.Cir.Stmt.nop{}, t), K, H), H),
                          kk => +eT =>
                            Wp.set(f, 47n, C.M.or(C.M.g(C.R.ov()), C.M.shl(C.M.c(1), C.M.g(C.R.oi()))), s1, t => Wp(C.Cir.exec(1n+f, C.Cir.Stmt.nop{}, t), K, H), H,
                              OV(True{}, ov, oi), {==},
                              kk(Some{True{}}, Equal.trans(Maybe<&2, Bool>, CB(m, c), Some{U32.is_eq(x2, 6)}, Some{True{}}, CB.ok(m, c, eP, eL, eM, eO),
                                Equal.cong(Bool, Maybe<&2, Bool>, x => Some{x}, U32.is_eq(x2, 6), True{}, eT)))),
                          kk => +eT =>
                            kk(Some{False{}}, Equal.trans(Maybe<&2, Bool>, CB(m, c), Some{U32.is_eq(x2, 6)}, Some{False{}}, CB.ok(m, c, eP, eL, eM, eO),
                              Equal.cong(Bool, Maybe<&2, Bool>, x => Some{x}, U32.is_eq(x2, 6), False{}, eT))))),
                      kk => +eO =>
                        kk(None{}, CB.n4(m, c, eP, eL, eM, eO), s1)))))),
            kk => +eM =>
              kk(None{}, CB.n3(m, c, eP, eL, eM), s0))),
        kk => +eL =>
          kk(None{}, CB.n2(m, c, eP, eL), s0))),
    kk => +eP =>
      kk(None{}, CB.n1(m, c, eP), s0)))

# The word
# --------

# a word is its bits, then its WNil
def CWt.nil(t: Maybe<&2, Word(0n)>) -> {t == CWt(0n, Some{WNil{}}, t) : Maybe<&2, Word(0n)>}:
  match t:
    case None{}:
      {==}
    case Some{y}:
      match y:
        case WNil{}:
          {==}

def CWt.w(-q: Nat, x: Bool, rb: Maybe<&2, Word(q)>, t: Maybe<&2, Word(0n)>) ->
  {W1.w(q, x, CWt(q, rb, t)) == CWt(1n+q, W1.w(q, x, rb), t) : Maybe<&2, Word(1n+q)>}:
  match rb:
    case None{}:
      {==}
    case Some{y}:
      match t:
        case None{}:
          {==}
        case Some{z}:
          {==}

def CWt.g(-q: Nat, g: Maybe<&2, Bool>, rb: Maybe<&2, Word(q)>, t: Maybe<&2, Word(0n)>) ->
  {W1.g(q, g, CWt(q, rb, t)) == CWt(1n+q, W1.g(q, g, rb), t) : Maybe<&2, Word(1n+q)>}:
  match g:
    case None{}:
      {==}
    case Some{x}:
      CWt.w(q, x, rb, t)

def CW.split(+p: Nat, +m: C.Cir.Cells, +c: U32) -> {CW(p, m, c) == CWt(p, CWb(p, m, c), CW(0n, m, Nx(p, m, c))) : Maybe<&2, Word(p)>}:
  match p:
    case 0n:
      CWt.nil(CW(0n, m, c))
    case 1n+q:
      %Equal.sym(Maybe<&2, Word(q)>, CW(q, m, CW.next(m, c)), CWt(q, CWb(q, m, CW.next(m, c)), CW(0n, m, Nx(q, m, CW.next(m, c)))), CW.split(q, m, CW.next(m, c))) :
        {W1.g(q, GB(m, c), _) == CWt(1n+q, W1.g(q, GB(m, c), CWb(q, m, CW.next(m, c))), CW(0n, m, Nx(q, m, CW.next(m, c)))) : Maybe<&2, Word(1n+q)>}
      CWt.g(q, GB(m, c), CWb(q, m, CW.next(m, c)), CW(0n, m, Nx(q, m, CW.next(m, c))))

# GB's value, once its tests pass, or none when one fails
def GB.ok(+m: C.Cir.Cells, +c: U32, +eP: {Pm(m, c) == True{} : Bool}, +eI: {ISLAB(m, c, 5) == True{} : Bool},
  +eF: {Pm(m, Fd(3n, m, c)) == True{} : Bool}, +x: Bool, +eB: {CB(m, Fd(2n, m, Fd(3n, m, c))) == Some{x} : Maybe<&2, Bool>},
  +eR: {Pm(m, Fd(3n, m, Fd(3n, m, c))) == True{} : Bool}, +eZ: {LAST(m, Fd(3n, m, Fd(3n, m, c))) == True{} : Bool}) ->
  {GB(m, c) == Some{x} : Maybe<&2, Bool>}:
  +fc = Fd(3n, m, c)
  +rc = Fd(3n, m, fc)
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {GB.p(_, m, c) == Some{x} : Maybe<&2, Bool>}
  %Equal.sym(Bool, ISLAB(m, c, 5), True{}, eI) : {GB.l(_, m, fc) == Some{x} : Maybe<&2, Bool>}
  %Equal.sym(Bool, Pm(m, fc), True{}, eF) : {GB.f(_, m, fc) == Some{x} : Maybe<&2, Bool>}
  %Equal.sym(Maybe<&2, Bool>, CB(m, Fd(2n, m, fc)), Some{x}, eB) : {GB.b(_, m, rc) == Some{x} : Maybe<&2, Bool>}
  %Equal.sym(Bool, Pm(m, rc), True{}, eR) : {GB.r(x, _, m, rc) == Some{x} : Maybe<&2, Bool>}
  %Equal.sym(Bool, LAST(m, rc), True{}, eZ) : {GB.z(x, _) == Some{x} : Maybe<&2, Bool>}
  {==}

def GB.n1(+m: C.Cir.Cells, +c: U32, +eP: {Pm(m, c) == False{} : Bool}) -> {GB(m, c) == None{} : Maybe<&2, Bool>}:
  Equal.cong(Bool, Maybe<&2, Bool>, y => GB.p(y, m, c), Pm(m, c), False{}, eP)

def GB.n2(+m: C.Cir.Cells, +c: U32, +eP: {Pm(m, c) == True{} : Bool}, +eI: {ISLAB(m, c, 5) == False{} : Bool}) ->
  {GB(m, c) == None{} : Maybe<&2, Bool>}:
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {GB.p(_, m, c) == None{} : Maybe<&2, Bool>}
  Equal.cong(Bool, Maybe<&2, Bool>, y => GB.l(y, m, Fd(3n, m, c)), ISLAB(m, c, 5), False{}, eI)

def GB.n3(+m: C.Cir.Cells, +c: U32, +eP: {Pm(m, c) == True{} : Bool}, +eI: {ISLAB(m, c, 5) == True{} : Bool},
  +eF: {Pm(m, Fd(3n, m, c)) == False{} : Bool}) -> {GB(m, c) == None{} : Maybe<&2, Bool>}:
  +fc = Fd(3n, m, c)
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {GB.p(_, m, c) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Bool, ISLAB(m, c, 5), True{}, eI) : {GB.l(_, m, fc) == None{} : Maybe<&2, Bool>}
  Equal.cong(Bool, Maybe<&2, Bool>, y => GB.f(y, m, fc), Pm(m, fc), False{}, eF)

def GB.n4(+m: C.Cir.Cells, +c: U32, +eP: {Pm(m, c) == True{} : Bool}, +eI: {ISLAB(m, c, 5) == True{} : Bool},
  +eF: {Pm(m, Fd(3n, m, c)) == True{} : Bool}, +eB: {CB(m, Fd(2n, m, Fd(3n, m, c))) == None{} : Maybe<&2, Bool>}) ->
  {GB(m, c) == None{} : Maybe<&2, Bool>}:
  +fc = Fd(3n, m, c)
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {GB.p(_, m, c) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Bool, ISLAB(m, c, 5), True{}, eI) : {GB.l(_, m, fc) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Bool, Pm(m, fc), True{}, eF) : {GB.f(_, m, fc) == None{} : Maybe<&2, Bool>}
  Equal.cong(Maybe<&2, Bool>, Maybe<&2, Bool>, y => GB.b(y, m, Fd(3n, m, fc)), CB(m, Fd(2n, m, fc)), None{}, eB)

def GB.n5(+m: C.Cir.Cells, +c: U32, +eP: {Pm(m, c) == True{} : Bool}, +eI: {ISLAB(m, c, 5) == True{} : Bool},
  +eF: {Pm(m, Fd(3n, m, c)) == True{} : Bool}, +x: Bool, +eB: {CB(m, Fd(2n, m, Fd(3n, m, c))) == Some{x} : Maybe<&2, Bool>},
  +eR: {Pm(m, Fd(3n, m, Fd(3n, m, c))) == False{} : Bool}) -> {GB(m, c) == None{} : Maybe<&2, Bool>}:
  +fc = Fd(3n, m, c)
  +rc = Fd(3n, m, fc)
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {GB.p(_, m, c) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Bool, ISLAB(m, c, 5), True{}, eI) : {GB.l(_, m, fc) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Bool, Pm(m, fc), True{}, eF) : {GB.f(_, m, fc) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Maybe<&2, Bool>, CB(m, Fd(2n, m, fc)), Some{x}, eB) : {GB.b(_, m, rc) == None{} : Maybe<&2, Bool>}
  Equal.cong(Bool, Maybe<&2, Bool>, y => GB.r(x, y, m, rc), Pm(m, rc), False{}, eR)

def GB.n6(+m: C.Cir.Cells, +c: U32, +eP: {Pm(m, c) == True{} : Bool}, +eI: {ISLAB(m, c, 5) == True{} : Bool},
  +eF: {Pm(m, Fd(3n, m, c)) == True{} : Bool}, +x: Bool, +eB: {CB(m, Fd(2n, m, Fd(3n, m, c))) == Some{x} : Maybe<&2, Bool>},
  +eR: {Pm(m, Fd(3n, m, Fd(3n, m, c))) == True{} : Bool}, +eZ: {LAST(m, Fd(3n, m, Fd(3n, m, c))) == False{} : Bool}) ->
  {GB(m, c) == None{} : Maybe<&2, Bool>}:
  +fc = Fd(3n, m, c)
  +rc = Fd(3n, m, fc)
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {GB.p(_, m, c) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Bool, ISLAB(m, c, 5), True{}, eI) : {GB.l(_, m, fc) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Bool, Pm(m, fc), True{}, eF) : {GB.f(_, m, fc) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Maybe<&2, Bool>, CB(m, Fd(2n, m, fc)), Some{x}, eB) : {GB.b(_, m, rc) == None{} : Maybe<&2, Bool>}
  %Equal.sym(Bool, Pm(m, rc), True{}, eR) : {GB.r(x, _, m, rc) == None{} : Maybe<&2, Bool>}
  Equal.cong(Bool, Maybe<&2, Bool>, y => GB.z(x, y), LAST(m, rc), False{}, eZ)

# the loop of M.out.word, and its parts
def MW.a1() -> C.Cir.Stmt:
  C.M.set(C.R.ow(), C.M.f(3n, C.M.g(C.R.ow())))

def MW.a2() -> C.Cir.Stmt:
  C.M.set(C.R.t1(), C.M.f(2n, C.M.g(C.R.ow())))

def MW.a3() -> C.Cir.Stmt:
  C.M.set(C.R.ow(), C.M.f(3n, C.M.g(C.R.ow())))

def MW.a4() -> C.Cir.Stmt:
  C.M.set(C.R.ow(), C.M.f(2n, C.M.g(C.R.ow())))

def MW.a5() -> C.Cir.Stmt:
  C.M.set(C.R.oi(), C.M.add(C.M.g(C.R.oi()), C.M.c(1)))

def MW.s4() -> C.Cir.Stmt:
  C.M.need(C.M.last(C.R.ow()), C.M.do([MW.a4(), MW.a5()]))

def MW.s3() -> C.Cir.Stmt:
  C.M.need(C.M.pair(C.R.ow()), MW.s4())

def MW.r3() -> C.Cir.Stmt:
  C.M.do([MW.a3(), MW.s3()])

def MW.r2() -> C.Cir.Stmt:
  C.M.do([C.M.out.bit(), MW.a3(), MW.s3()])

def MW.r1() -> C.Cir.Stmt:
  C.M.do([MW.a2(), C.M.out.bit(), MW.a3(), MW.s3()])

def MW.s2() -> C.Cir.Stmt:
  C.M.need(C.M.pair(C.R.ow()), MW.r1())

def MW.s1() -> C.Cir.Stmt:
  C.M.need(C.M.is_lab(C.M.f(2n, C.M.g(C.R.ow())), C.N.wcon()), C.M.do([MW.a1(), MW.s2()]))

def MW.body() -> C.Cir.Stmt:
  C.M.need(C.M.pair(C.R.ow()), MW.s1())

def MW.loop() -> C.Cir.Stmt:
  C.M.while(C.M.lt(C.M.g(C.R.oi()), C.M.c(32)), MW.body())

def MW.end() -> C.Cir.Stmt:
  C.M.need(C.M.pair(C.R.ow()), C.M.need(C.M.is_lab(C.M.f(2n, C.M.g(C.R.ow())), C.N.wnil()), C.M.need(C.M.last(C.R.ow()), C.Cir.Stmt.nop{})))

# what a round of the loop goes on with, by what GB reads: the bit in ov and
# the next cell in ow, or no result
def MI.Kc(+b: C.Cir.State, +oc: U32, +c: U32, +ov: U32, +oi: U32, +pg: U32, +out: List<&2, U32>, +outn: U32,
  +nw: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, -K: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type) -> Type:
  @g: Maybe<&2, Bool> -> {GB(St.cl(b), c) == g : Maybe<&2, Bool>} ->
    MC(g, x => {ok(Pr(Pr(Pr(nw))), St.cl(b), ks, img, CW.next(St.cl(b), c), St.im(b), St.fs(b), St.nx(b)) == True{} : Bool} ->
      K(ST(b, oc, CW.next(St.cl(b), c), OV(x, ov, oi), U32.add(oi, 1), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)),
        Fd(2n, St.cl(b), Fd(2n, St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)))), pg, out, outn)),
      @st: C.Cir.State -> H(2, st))

# the round, once its bit is read: the rest of its tests
def MI.end(+f: Nat, +b: C.Cir.State, +oc: U32, +c: U32, +ov: U32, +oi: U32, +pg: U32, +out: List<&2, U32>, +outn: U32,
  +nw: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, -K: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type,
  +hok: {ok(nw, St.cl(b), ks, img, c, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  +eP: {Pm(St.cl(b), c) == True{} : Bool}, +eI: {ISLAB(St.cl(b), c, 5) == True{} : Bool},
  +eF: {Pm(St.cl(b), Fd(3n, St.cl(b), c)) == True{} : Bool}, +x: Bool,
  +eB: {CB(St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c))) == Some{x} : Maybe<&2, Bool>},
  kk: MI.Kc(b, oc, c, ov, oi, pg, out, outn, nw, ks, img, K, H)) ->
  Wp(C.Cir.exec(1n+f, MW.r3(), ST(b, oc, Fd(3n, St.cl(b), c), OV(x, ov, oi), oi, Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)),
      Fd(2n, St.cl(b), Fd(2n, St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)))), pg, out, outn)),
    t => Wp(C.Cir.exec(1n+f, C.Cir.Stmt.nop{}, t), K, H), H):
  +m = St.cl(b)
  +im = St.im(b)
  +fs = St.fs(b)
  +nx = St.nx(b)
  +fc = Fd(3n, m, c)
  +bc = Fd(2n, m, fc)
  +rc = Fd(3n, m, fc)
  +nc = Fd(2n, m, rc)
  +x2 = Fd(2n, m, Fd(2n, m, bc))
  +v = OV(x, ov, oi)
  +hokf = ok.R(nw, m, ks, img, c, im, fs, nx, hok, eP)
  +hcf = ok.isc(Pr(nw), m, ks, img, fc, im, fs, nx, hokf)
  +hokr = ok.R(Pr(nw), m, ks, img, fc, im, fs, nx, hokf, eF)
  +hcr = ok.isc(Pr(Pr(nw)), m, ks, img, rc, im, fs, nx, hokr)
  +s3 = ST(b, oc, fc, v, oi, bc, x2, pg, out, outn)
  +s4 = ST(b, oc, rc, v, oi, bc, x2, pg, out, outn)
  +s5 = ST(b, oc, nc, v, oi, bc, x2, pg, out, outn)
  -K1 = {t => Wp(C.Cir.exec(1n+f, C.Cir.Stmt.nop{}, t), K, H) : C.Cir.State -> Type}
  -K2 = {t => Wp(C.Cir.exec(1n+f, C.Cir.Stmt.nop{}, t), K1, H) : C.Cir.State -> Type}
  -A = MI.Kc(b, oc, c, ov, oi, pg, out, outn, nw, ks, img, K, H)
  Wp.seq(f, MW.a3(), C.M.do([MW.s3()]), s3, K1, H,
    Wp.set(f, 46n, C.M.f(3n, C.M.g(C.R.ow())), s3, t => Wp(C.Cir.exec(1n+f, C.M.do([MW.s3()]), t), K1, H), H, rc,
      ev.f(3n, C.M.g(C.R.ow()), s3, fc, {==}, hcf),
      Wp.seq(f, MW.s3(), C.Cir.Stmt.nop{}, s4, K1, H,
        Wp.need(f, C.M.pair(C.R.ow()), MW.s4(), s4, K2, H, Pm(m, rc), ev.pair(46n, s4, rc, {==}, hcr),
         CasesK(Pm(m, rc), A, kk, Wp(C.Cir.exec(1n+f, MW.s4(), s4), K2, H), H(2, s4),
          kk => +eR =>
            Wp.need(f, C.M.last(C.R.ow()), C.M.do([MW.a4(), MW.a5()]), s4, K2, H, LAST(m, rc),
              ev.islab(3n, 46n, 0, s4, rc, {==}, hcr, ok.isc(Pr(Pr(Pr(nw))), m, ks, img, Fd(3n, m, rc), im, fs, nx, ok.R(Pr(Pr(nw)), m, ks, img, rc, im, fs, nx, hokr, eR))),
             CasesK(LAST(m, rc), A, kk, Wp(C.Cir.exec(1n+f, C.M.do([MW.a4(), MW.a5()]), s4), K2, H), H(2, s4),
              kk => +eZ =>
                Wp.seq(f, MW.a4(), C.M.do([MW.a5()]), s4, K2, H,
                  Wp.set(f, 46n, C.M.f(2n, C.M.g(C.R.ow())), s4, t => Wp(C.Cir.exec(1n+f, C.M.do([MW.a5()]), t), K2, H), H, nc,
                    ev.f(2n, C.M.g(C.R.ow()), s4, rc, {==}, hcr),
                    Wp.seq(f, MW.a5(), C.Cir.Stmt.nop{}, s5, K2, H,
                      Wp.set(f, 48n, C.M.add(C.M.g(C.R.oi()), C.M.c(1)), s5, t => Wp(C.Cir.exec(1n+f, C.Cir.Stmt.nop{}, t), K2, H), H, U32.add(oi, 1), {==},
                        kk(Some{x}, GB.ok(m, c, eP, eI, eF, x, eB, eR, eZ), ok.L(Pr(Pr(nw)), m, ks, img, rc, im, fs, nx, hokr, eR)))))),
              kk => +eZ =>
                kk(None{}, GB.n6(m, c, eP, eI, eF, x, eB, eR, eZ), s4))),
          kk => +eR =>
            kk(None{}, GB.n5(m, c, eP, eI, eF, x, eB, eR), s4))))))

# the round, once its first tests pass: the bit, then the rest of its tests
def MI.bit(+f: Nat, +b: C.Cir.State, +oc: U32, +c: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32, +pg: U32, +out: List<&2, U32>, +outn: U32,
  +nw: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, -K: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type,
  +hok: {ok(nw, St.cl(b), ks, img, c, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  +eP: {Pm(St.cl(b), c) == True{} : Bool}, +eI: {ISLAB(St.cl(b), c, 5) == True{} : Bool},
  +eF: {Pm(St.cl(b), Fd(3n, St.cl(b), c)) == True{} : Bool},
  kk: MI.Kc(b, oc, c, ov, oi, pg, out, outn, nw, ks, img, K, H)) ->
  Wp(C.Cir.exec(1n+f, MW.r1(), ST(b, oc, Fd(3n, St.cl(b), c), ov, oi, t1, t2, pg, out, outn)),
    t => Wp(C.Cir.exec(1n+f, C.Cir.Stmt.nop{}, t), K, H), H):
  +m = St.cl(b)
  +im = St.im(b)
  +fs = St.fs(b)
  +nx = St.nx(b)
  +fc = Fd(3n, m, c)
  +bc = Fd(2n, m, fc)
  +rc = Fd(3n, m, fc)
  +nc = Fd(2n, m, rc)
  +x2 = Fd(2n, m, Fd(2n, m, bc))
  +hokf = ok.R(nw, m, ks, img, c, im, fs, nx, hok, eP)
  +hcf = ok.isc(Pr(nw), m, ks, img, fc, im, fs, nx, hokf)
  +hokr = ok.R(Pr(nw), m, ks, img, fc, im, fs, nx, hokf, eF)
  +hcr = ok.isc(Pr(Pr(nw)), m, ks, img, rc, im, fs, nx, hokr)
  +s1 = ST(b, oc, fc, ov, oi, t1, t2, pg, out, outn)
  -K1 = {t => Wp(C.Cir.exec(1n+f, C.Cir.Stmt.nop{}, t), K, H) : C.Cir.State -> Type}
  -A = MI.Kc(b, oc, c, ov, oi, pg, out, outn, nw, ks, img, K, H)
  Wp.seq(f, MW.a2(), MW.r2(), s1, K1, H,
    Wp.set(f, 62n, C.M.f(2n, C.M.g(C.R.ow())), s1, t => Wp(C.Cir.exec(1n+f, MW.r2(), t), K1, H), H, bc,
      ev.f(2n, C.M.g(C.R.ow()), s1, fc, {==}, hcf),
      Wp.seq(f, C.M.out.bit(), MW.r3(), ST(b, oc, fc, ov, oi, bc, t2, pg, out, outn), K1, H,
        MB(f, b, oc, fc, ov, oi, bc, t2, pg, out, outn, Pr(Pr(nw)), ks, img, t => Wp(C.Cir.exec(1n+f, MW.r3(), t), K1, H), H,
          ok.L(Pr(nw), m, ks, img, fc, im, fs, nx, hokf, eF),
          rB => +eB => CasesM(rB, A, kk, x => Wp(C.Cir.exec(1n+f, MW.r3(), ST(b, oc, fc, OV(x, ov, oi), oi, bc, x2, pg, out, outn)), K1, H),
            @st: C.Cir.State -> H(2, st),
            kk => +x => +ex =>
              MI.end(f, b, oc, c, ov, oi, pg, out, outn, nw, ks, img, K, H, hok, eP, eI, eF, x,
                Equal.trans(Maybe<&2, Bool>, CB(m, bc), rB, Some{x}, eB, ex), kk),
            kk => +ex =>
              st => kk(None{}, GB.n4(m, c, eP, eI, eF, Equal.trans(Maybe<&2, Bool>, CB(m, bc), rB, None{}, eB, ex)), st))))))

# a round of the loop of M.out.word, on the cell c in ow: the bit that GB
# reads goes into ov, and ow gets the cell after it; or the run ends with no
# result
def MI(+f: Nat, +b: C.Cir.State, +oc: U32, +c: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32, +pg: U32, +out: List<&2, U32>, +outn: U32,
  +nw: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, -K: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type,
  +hok: {ok(nw, St.cl(b), ks, img, c, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  kk: MI.Kc(b, oc, c, ov, oi, pg, out, outn, nw, ks, img, K, H)) ->
  Wp(C.Cir.exec(1n+f, MW.body(), ST(b, oc, c, ov, oi, t1, t2, pg, out, outn)), K, H):
  +m = St.cl(b)
  +im = St.im(b)
  +fs = St.fs(b)
  +nx = St.nx(b)
  +fc = Fd(3n, m, c)
  +bc = Fd(2n, m, fc)
  +rc = Fd(3n, m, fc)
  +nc = Fd(2n, m, rc)
  +x2 = Fd(2n, m, Fd(2n, m, bc))
  +s0 = ST(b, oc, c, ov, oi, t1, t2, pg, out, outn)
  +s1 = ST(b, oc, fc, ov, oi, t1, t2, pg, out, outn)
  +s2 = ST(b, oc, fc, ov, oi, bc, t2, pg, out, outn)
  +hc = ok.isc(nw, m, ks, img, c, im, fs, nx, hok)
  -A = MI.Kc(b, oc, c, ov, oi, pg, out, outn, nw, ks, img, K, H)
  Wp.need(f, C.M.pair(C.R.ow()), MW.s1(), s0, K, H, Pm(m, c), ev.pair(46n, s0, c, {==}, hc),
   CasesK(Pm(m, c), A, kk, Wp(C.Cir.exec(1n+f, MW.s1(), s0), K, H), H(2, s0),
    kk => +eP =>
      Wp.need(f, C.M.is_lab(C.M.f(2n, C.M.g(C.R.ow())), C.N.wcon()), C.M.do([MW.a1(), MW.s2()]), s0, K, H, ISLAB(m, c, 5),
        ev.islab(2n, 46n, 5, s0, c, {==}, hc, ok.isc(Pr(nw), m, ks, img, Fd(2n, m, c), im, fs, nx, ok.L(nw, m, ks, img, c, im, fs, nx, hok, eP))),
       CasesK(ISLAB(m, c, 5), A, kk, Wp(C.Cir.exec(1n+f, C.M.do([MW.a1(), MW.s2()]), s0), K, H), H(2, s0),
        kk => +eI =>
          Wp.seq(f, MW.a1(), C.M.do([MW.s2()]), s0, K, H,
            Wp.set(f, 46n, C.M.f(3n, C.M.g(C.R.ow())), s0, t => Wp(C.Cir.exec(1n+f, C.M.do([MW.s2()]), t), K, H), H, fc,
              ev.f(3n, C.M.g(C.R.ow()), s0, c, {==}, hc),
              Wp.seq(f, MW.s2(), C.Cir.Stmt.nop{}, s1, K, H,
                Wp.need(f, C.M.pair(C.R.ow()), MW.r1(), s1, t => Wp(C.Cir.exec(1n+f, C.Cir.Stmt.nop{}, t), K, H), H, Pm(m, fc),
                  ev.pair(46n, s1, fc, {==}, ok.isc(Pr(nw), m, ks, img, fc, im, fs, nx, ok.R(nw, m, ks, img, c, im, fs, nx, hok, eP))),
                 CasesK(Pm(m, fc), A, kk, Wp(C.Cir.exec(1n+f, MW.r1(), s1), t => Wp(C.Cir.exec(1n+f, C.Cir.Stmt.nop{}, t), K, H), H), H(2, s1),
                  kk => +eF =>
                    MI.bit(f, b, oc, c, ov, oi, t1, t2, pg, out, outn, nw, ks, img, K, H, hok, eP, eI, eF, kk),
                  kk => +eF =>
                    kk(None{}, GB.n3(m, c, eP, eI, eF), s1)))))),
        kk => +eI =>
          kk(None{}, GB.n2(m, c, eP, eI), s0))),
    kk => +eP =>
      kk(None{}, GB.n1(m, c, eP), s0)))

# The loop of the word
# --------------------
#
# Each round reads a bit x into ov (M.out.bit sets bit oi of ov when x is
# True). With r bits left, ov holds U32{K(zeros(r))}: K puts the bits read
# so far below its argument, and Kz puts zeros there, so that or-ing 1 << oi,
# which is U32{Kz(WCon{True, zeros})} (Good), sets the next bit (HKT).

def SH(+idx: U32) -> U32:
  C.Wasm.op(C.Wasm.Op.shl{}, 1, idx)

# h, moved along the equation e
def Tr(-A: Type, -P: A -> Type, -a: A, -b: A, +e: {a == b : A}, h: P(a)) -> P(b):
  %e : P(_)
  h

# a pair of two Data types, itself Data, and its parts
def PD(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

def D1(-A: Data, -B: Data, +p: PD(A, B)) -> A:
  (a, b) = p
  a

def D2(-A: Data, -B: Data, +p: PD(A, B)) -> B:
  (a, b) = p
  b

def Good(r: Nat, +idx: U32, Kz: Word(r) -> Word(32n)) -> Data:
  match r:
    case 0n:
      {U32.is_lt(idx, 32) == False{} : Bool}
    case 1n+q:
      PD({U32.is_lt(idx, 32) == True{} : Bool}, PD({U32{Kz(WCon{True{}, zeros(q)})} == SH(idx) : U32}, Good(q, U32.add(idx, 1), y => Kz(WCon{False{}, y}))))

def HKT(r: Nat, K: Word(r) -> Word(32n), Kz: Word(r) -> Word(32n)) -> Data:
  {(a => b => K(Word.or(r, a, b))) == (a => b => Word.or(32n, K(a), Kz(b))) : Word(r) -> Word(r) -> Word(32n)}

def or_zz(+q: Nat) -> {zeros(q) == Word.or(q, zeros(q), zeros(q)) : Word(q)}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      %or_zz(p) : {WCon{False{}, zeros(p)} == WCon{False{}, _} : Word(1n+p)}
      {==}

# the value of ov after the bit x
def acc_step(x: Bool, +q: Nat, -K: Word(1n+q) -> Word(32n), -Kz: Word(1n+q) -> Word(32n), +idx: U32, +HK: HKT(1n+q, K, Kz),
  +esh: {U32{Kz(WCon{True{}, zeros(q)})} == SH(idx) : U32}) -> {U32{K(WCon{x, zeros(q)})} == OV(x, U32{K(zeros(1n+q))}, idx) : U32}:
  match x:
    case False{}:
      {==}
    case True{}:
      %esh : {U32{K(WCon{True{}, zeros(q)})} == U32.or(U32{K(zeros(1n+q))}, _) : U32}
      %Equal.cong(Word(1n+q) -> Word(1n+q) -> Word(32n), Word(32n), h => h(WCon{False{}, zeros(q)}, WCon{True{}, zeros(q)}),
        a => b => K(Word.or(1n+q, a, b)), a => b => Word.or(32n, K(a), Kz(b)), HK) : {U32{K(WCon{True{}, zeros(q)})} == U32{_} : U32}
      %or_zz(q) : {U32{K(WCon{True{}, zeros(q)})} == U32{K(WCon{True{}, _})} : U32}
      {==}

# HKT holds after the bit x
def HK.step(+q: Nat, +x: Bool, -K: Word(1n+q) -> Word(32n), -Kz: Word(1n+q) -> Word(32n), +HK: HKT(1n+q, K, Kz)) ->
  HKT(q, y => K(WCon{x, y}), y => Kz(WCon{False{}, y})):
  %Equal.sym(Bool, x, Bool.or(x, False{}), or_false(x)) :
    {(a => b => K(WCon{_, Word.or(q, a, b)})) == (a => b => Word.or(32n, K(WCon{x, a}), Kz(WCon{False{}, b}))) : Word(q) -> Word(q) -> Word(32n)}
  Equal.cong(Word(1n+q) -> Word(1n+q) -> Word(32n), Word(q) -> Word(q) -> Word(32n), h => (a => b => h(WCon{x, a}, WCon{False{}, b})),
    a => b => K(Word.or(1n+q, a, b)), a => b => Word.or(32n, K(a), Kz(b)), HK)

# X(w) for Some{w}, else Y
def MCW(-p: Nat, rr: Maybe<&2, Word(p)>, X: Word(p) -> Type, Y: Type) -> Type:
  match rr:
    case Some{w}:
      X(w)
    case None{}:
      Y

def CasesW(-p: Nat, rr: Maybe<&2, Word(p)>, -A: Type, a: A, -X: Word(p) -> Type, -Y: Type,
  s: A -> @w: Word(p) -> {rr == Some{w} : Maybe<&2, Word(p)>} -> X(w), n: A -> {rr == None{} : Maybe<&2, Word(p)>} -> Y) -> MCW(p, rr, X, Y):
  match rr:
    case Some{w}:
      s(a, w, {==})
    case None{}:
      n(a, {==})

def CWb.some(+q: Nat, +m: C.Cir.Cells, +c: U32, +x: Bool, +w: Word(q), +e1: {GB(m, c) == Some{x} : Maybe<&2, Bool>},
  +e2: {CWb(q, m, CW.next(m, c)) == Some{w} : Maybe<&2, Word(q)>}) -> {CWb(1n+q, m, c) == Some{WCon{x, w}} : Maybe<&2, Word(1n+q)>}:
  %Equal.sym(Maybe<&2, Bool>, GB(m, c), Some{x}, e1) : {W1.g(q, _, CWb(q, m, CW.next(m, c))) == Some{WCon{x, w}} : Maybe<&2, Word(1n+q)>}
  %Equal.sym(Maybe<&2, Word(q)>, CWb(q, m, CW.next(m, c)), Some{w}, e2) : {W1.w(q, x, _) == Some{WCon{x, w}} : Maybe<&2, Word(1n+q)>}
  {==}

def CWb.none2(+q: Nat, +m: C.Cir.Cells, +c: U32, +x: Bool, +e1: {GB(m, c) == Some{x} : Maybe<&2, Bool>},
  +e2: {CWb(q, m, CW.next(m, c)) == None{} : Maybe<&2, Word(q)>}) -> {CWb(1n+q, m, c) == None{} : Maybe<&2, Word(1n+q)>}:
  %Equal.sym(Maybe<&2, Bool>, GB(m, c), Some{x}, e1) : {W1.g(q, _, CWb(q, m, CW.next(m, c))) == None{} : Maybe<&2, Word(1n+q)>}
  %Equal.sym(Maybe<&2, Word(q)>, CWb(q, m, CW.next(m, c)), None{}, e2) : {W1.w(q, x, _) == None{} : Maybe<&2, Word(1n+q)>}
  {==}

def CWb.none1(+q: Nat, +m: C.Cir.Cells, +c: U32, +e1: {GB(m, c) == None{} : Maybe<&2, Bool>}) ->
  {CWb(1n+q, m, c) == None{} : Maybe<&2, Word(1n+q)>}:
  Equal.cong(Maybe<&2, Bool>, Maybe<&2, Word(1n+q)>, g => W1.g(q, g, CWb(q, m, CW.next(m, c))), GB(m, c), None{}, e1)

# M.lt on register r
def ev.lt(+r: Nat, +n: U32, +st: C.Cir.State, +i: U32, +er: {Some{i} == C.Cir.eval(C.M.g(r), st) : Maybe<&2, U32>}, -b: Bool,
  +eb: {U32.is_lt(i, n) == b : Bool}) -> {Some{Bool.to_u32(b)} == C.Cir.eval(C.M.lt(C.M.g(r), C.M.c(n)), st) : Maybe<&2, U32>}:
  %er : {Some{Bool.to_u32(b)} == C.Cir.eval.op(C.Wasm.Op.lt_u{}, _, Some{n}) : Maybe<&2, U32>}
  %eb : {Some{Bool.to_u32(_)} == Some{Bool.to_u32(U32.is_lt(i, n))} : Maybe<&2, U32>}
  {==}

def Wp.while(+f: Nat, +c: C.Cir.Expr, +body: C.Cir.Stmt, +st: C.Cir.State, -K: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type,
  b: Bool, +ev: {Some{Bool.to_u32(b)} == C.Cir.eval(c, st) : Maybe<&2, U32>},
  g: IFT(b, Wp(C.Cir.exec.then(C.Cir.exec(f, body, st), t => C.Cir.exec(f, C.Cir.Stmt.while{c, body}, t)), K, H), K(st))) ->
  Wp(C.Cir.exec(1n+f, C.Cir.Stmt.while{c, body}, st), K, H):
  match b:
    case True{}:
      %ev : Wp(C.Cir.exec.if(_, u => C.Cir.exec.then(C.Cir.exec(f, body, st), t => C.Cir.exec(f, C.Cir.Stmt.while{c, body}, t)), u => C.Cir.Out.next{st}), K, H)
      g
    case False{}:
      %ev : Wp(C.Cir.exec.if(_, u => C.Cir.exec.then(C.Cir.exec(f, body, st), t => C.Cir.exec(f, C.Cir.Stmt.while{c, body}, t)), u => C.Cir.Out.next{st}), K, H)
      g

# the fuel of ok left after r bits of a word
def Pn(r: Nat, +n: Nat) -> Nat:
  match r:
    case 0n:
      n
    case 1n+q:
      Pn(q, Pr(Pr(Pr(n))))

# what the loop goes on with, by what CWb reads: its r bits below K in ov,
# with ow at the cell after them, or no result
def ML.Kc(r: Nat, +b: C.Cir.State, +oc: U32, +c: U32, -K: Word(r) -> Word(32n), +pg: U32, +out: List<&2, U32>, +outn: U32,
  +nw: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, -KK: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type) -> Type:
  @rr: Maybe<&2, Word(r)> -> {CWb(r, St.cl(b), c) == rr : Maybe<&2, Word(r)>} ->
    MCW(r, rr, w => {ok(Pn(r, nw), St.cl(b), ks, img, Nx(r, St.cl(b), c), St.im(b), St.fs(b), St.nx(b)) == True{} : Bool} ->
      @oi: U32 -> @t1: U32 -> @t2: U32 -> KK(ST(b, oc, Nx(r, St.cl(b), c), U32{K(w)}, oi, t1, t2, pg, out, outn)),
      @st: C.Cir.State -> H(2, st))

# the loop goes on after a round that read the bit x
def ML.next(+q: Nat, +g: Nat, +b: C.Cir.State, +oc: U32, +c: U32, +ov: U32, +idx: U32, +pg: U32,
  +out: List<&2, U32>, +outn: U32, +nw: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  -K: Word(1n+q) -> Word(32n), -Kz: Word(1n+q) -> Word(32n), +HK: HKT(1n+q, K, Kz), +G: Good(1n+q, idx, Kz),
  -KK: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type, +eov: {U32{K(zeros(1n+q))} == ov : U32}, +x: Bool,
  +ex: {GB(St.cl(b), c) == Some{x} : Maybe<&2, Bool>},
  +hokn: {ok(Pr(Pr(Pr(nw))), St.cl(b), ks, img, CW.next(St.cl(b), c), St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  kk: ML.Kc(1n+q, b, oc, c, K, pg, out, outn, nw, ks, img, KK, H),
  ih: @nc: U32 -> @x: Bool -> {ok(Pr(Pr(Pr(nw))), St.cl(b), ks, img, nc, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool} ->
    @ov2: U32 -> {U32{K(WCon{x, zeros(q)})} == ov2 : U32} ->
    ML.Kc(q, b, oc, nc, y => K(WCon{x, y}), pg, out, outn, Pr(Pr(Pr(nw))), ks, img, KK, H) ->
    Wp(C.Cir.exec(1n+g, MW.loop(), ST(b, oc, nc, ov2, U32.add(idx, 1), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)),
      Fd(2n, St.cl(b), Fd(2n, St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)))), pg, out, outn)), KK, H)) ->
  Wp(C.Cir.exec(1n+g, MW.loop(), ST(b, oc, CW.next(St.cl(b), c), OV(x, ov, idx), U32.add(idx, 1), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)),
    Fd(2n, St.cl(b), Fd(2n, St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)))), pg, out, outn)), KK, H):
  +m = St.cl(b)
  +nc = CW.next(m, c)
  -A = ML.Kc(1n+q, b, oc, c, K, pg, out, outn, nw, ks, img, KK, H)
  ih(nc, x, hokn, OV(x, ov, idx),
    Equal.trans(U32, U32{K(WCon{x, zeros(q)})}, OV(x, U32{K(zeros(1n+q))}, idx), OV(x, ov, idx),
      acc_step(x, q, K, Kz, idx, HK, D1({U32{Kz(WCon{True{}, zeros(q)})} == SH(idx) : U32}, Good(q, U32.add(idx, 1), y => Kz(WCon{False{}, y})), D2({U32.is_lt(idx, 32) == True{} : Bool}, PD({U32{Kz(WCon{True{}, zeros(q)})} == SH(idx) : U32}, Good(q, U32.add(idx, 1), y => Kz(WCon{False{}, y}))), G))),
      Equal.cong(U32, U32, v => OV(x, v, idx), U32{K(zeros(1n+q))}, ov, eov)),
    rr => +err => CasesW(q, rr, A, kk,
      w => {ok(Pn(q, Pr(Pr(Pr(nw)))), m, ks, img, Nx(q, m, nc), St.im(b), St.fs(b), St.nx(b)) == True{} : Bool} ->
        @oi: U32 -> @t1: U32 -> @t2: U32 -> KK(ST(b, oc, Nx(q, m, nc), U32{K(WCon{x, w})}, oi, t1, t2, pg, out, outn)),
      @st: C.Cir.State -> H(2, st),
      kk => +w => +ew => kk(Some{WCon{x, w}}, CWb.some(q, m, c, x, w, ex, Equal.trans(Maybe<&2, Word(q)>, CWb(q, m, nc), rr, Some{w}, err, ew))),
      kk => +ew => kk(None{}, CWb.none2(q, m, c, x, ex, Equal.trans(Maybe<&2, Word(q)>, CWb(q, m, nc), rr, None{}, err, ew)))))

# a round of the loop, then the rest of it
def ML.go(+q: Nat, +g: Nat, +b: C.Cir.State, +oc: U32, +c: U32, +ov: U32, +idx: U32, +pg: U32,
  +out: List<&2, U32>, +outn: U32, +nw: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  -K: Word(1n+q) -> Word(32n), -Kz: Word(1n+q) -> Word(32n), +HK: HKT(1n+q, K, Kz), +G: Good(1n+q, idx, Kz),
  -KK: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type, +eov: {U32{K(zeros(1n+q))} == ov : U32}, +t1: U32, +t2: U32, +hF: PN.Le(1n+q, 1n+g),
  +hok: {ok(nw, St.cl(b), ks, img, c, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  kk: ML.Kc(1n+q, b, oc, c, K, pg, out, outn, nw, ks, img, KK, H),
  ih: @nc: U32 -> @x: Bool -> {ok(Pr(Pr(Pr(nw))), St.cl(b), ks, img, nc, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool} ->
    @ov2: U32 -> {U32{K(WCon{x, zeros(q)})} == ov2 : U32} ->
    ML.Kc(q, b, oc, nc, y => K(WCon{x, y}), pg, out, outn, Pr(Pr(Pr(nw))), ks, img, KK, H) ->
    Wp(C.Cir.exec(1n+g, MW.loop(), ST(b, oc, nc, ov2, U32.add(idx, 1), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)),
      Fd(2n, St.cl(b), Fd(2n, St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)))), pg, out, outn)), KK, H)) ->
  Wp(C.Cir.exec(1n+1n+g, MW.loop(), ST(b, oc, c, ov, idx, t1, t2, pg, out, outn)), KK, H):
  +m = St.cl(b)
  +s0 = ST(b, oc, c, ov, idx, t1, t2, pg, out, outn)
  +bc = Fd(2n, m, Fd(3n, m, c))
  +x2 = Fd(2n, m, Fd(2n, m, bc))
  -A = ML.Kc(1n+q, b, oc, c, K, pg, out, outn, nw, ks, img, KK, H)
  Wp.while(1n+g, C.M.lt(C.M.g(C.R.oi()), C.M.c(32)), MW.body(), s0, KK, H, True{},
    ev.lt(48n, 32, s0, idx, {==}, True{}, D1({U32.is_lt(idx, 32) == True{} : Bool}, PD({U32{Kz(WCon{True{}, zeros(q)})} == SH(idx) : U32}, Good(q, U32.add(idx, 1), y => Kz(WCon{False{}, y}))), G)),
    Wp.then(C.Cir.exec(1n+g, MW.body(), s0), t => C.Cir.exec(1n+g, MW.loop(), t), KK, H,
      MI(g, b, oc, c, ov, idx, t1, t2, pg, out, outn, nw, ks, img, t => Wp(C.Cir.exec(1n+g, MW.loop(), t), KK, H), H, hok,
        gb => +egb => CasesM(gb, A, kk,
          x => {ok(Pr(Pr(Pr(nw))), m, ks, img, CW.next(m, c), St.im(b), St.fs(b), St.nx(b)) == True{} : Bool} ->
            Wp(C.Cir.exec(1n+g, MW.loop(), ST(b, oc, CW.next(m, c), OV(x, ov, idx), U32.add(idx, 1), bc, x2, pg, out, outn)), KK, H),
          @st: C.Cir.State -> H(2, st),
          kk => +x => +ex => +hokn =>
            ML.next(q, g, b, oc, c, ov, idx, pg, out, outn, nw, ks, img, K, Kz, HK, G, KK, H, eov, x,
              Equal.trans(Maybe<&2, Bool>, GB(m, c), gb, Some{x}, egb, ex), hokn, kk, ih),
          kk => +ex =>
            st => kk(None{}, CWb.none1(q, m, c, Equal.trans(Maybe<&2, Bool>, GB(m, c), gb, None{}, egb, ex)), st)))))

# the loop of M.out.word, with r bits left, from the cell c in ow
def ML(+r: Nat, +F: Nat, +hF: PN.Le(1n+r, F), +b: C.Cir.State, +oc: U32, +c: U32, +ov: U32, +idx: U32, +t1: U32, +t2: U32, +pg: U32,
  +out: List<&2, U32>, +outn: U32, +nw: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  -K: Word(r) -> Word(32n), -Kz: Word(r) -> Word(32n), +HK: HKT(r, K, Kz), +G: Good(r, idx, Kz),
  -KK: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type, +eov: {U32{K(zeros(r))} == ov : U32},
  +hok: {ok(nw, St.cl(b), ks, img, c, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  kk: ML.Kc(r, b, oc, c, K, pg, out, outn, nw, ks, img, KK, H)) ->
  Wp(C.Cir.exec(F, MW.loop(), ST(b, oc, c, ov, idx, t1, t2, pg, out, outn)), KK, H):
  match r:
    case 0n:
      match F:
        case 0n:
          Empty.absurd(Wp(C.Cir.exec(0n, MW.loop(), ST(b, oc, c, ov, idx, t1, t2, pg, out, outn)), KK, H), hF)
        case 1n+f:
          Wp.while(f, C.M.lt(C.M.g(C.R.oi()), C.M.c(32)), MW.body(), ST(b, oc, c, ov, idx, t1, t2, pg, out, outn), KK, H, False{},
            ev.lt(48n, 32, ST(b, oc, c, ov, idx, t1, t2, pg, out, outn), idx, {==}, False{}, G),
            Tr(U32, v => KK(ST(b, oc, c, v, idx, t1, t2, pg, out, outn)), U32{K(zeros(0n))}, ov, eov, kk(Some{WNil{}}, {==}, hok, idx, t1, t2)))
    case 1n+q:
      match F:
        case 0n:
          Empty.absurd(Wp(C.Cir.exec(0n, MW.loop(), ST(b, oc, c, ov, idx, t1, t2, pg, out, outn)), KK, H), hF)
        case 1n+f:
          match f:
            case 0n:
              Empty.absurd(Wp(C.Cir.exec(1n, MW.loop(), ST(b, oc, c, ov, idx, t1, t2, pg, out, outn)), KK, H), hF)
            case 1n+g:
              ML.go(q, g, b, oc, c, ov, idx, pg, out, outn, nw, ks, img, K, Kz, HK, G, KK, H, eov, t1, t2, hF, hok, kk,
                nc => +x => +hokn => +ov2 => +eov2 => kk2 =>
                  ML(q, 1n+g, hF, b, oc, nc, ov2, U32.add(idx, 1), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)),
                    Fd(2n, St.cl(b), Fd(2n, St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)))), pg, out, outn, Pr(Pr(Pr(nw))), ks, img,
                    y => K(WCon{x, y}), y => Kz(WCon{False{}, y}), HK.step(q, x, K, Kz, HK),
                    D2({U32{Kz(WCon{True{}, zeros(q)})} == SH(idx) : U32}, Good(q, U32.add(idx, 1), y => Kz(WCon{False{}, y})),
                      D2({U32.is_lt(idx, 32) == True{} : Bool}, PD({U32{Kz(WCon{True{}, zeros(q)})} == SH(idx) : U32}, Good(q, U32.add(idx, 1), y => Kz(WCon{False{}, y}))), G)),
                    KK, H, eov2, hokn, kk2))

# The word
# --------

def CW0.ok(+m: C.Cir.Cells, +d: U32, +eP: {Pm(m, d) == True{} : Bool}, +eI: {ISLAB(m, d, 4) == True{} : Bool},
  +eL: {LAST(m, d) == True{} : Bool}) -> {CW(0n, m, d) == Some{WNil{}} : Maybe<&2, Word(0n)>}:
  %Equal.sym(Bool, Pm(m, d), True{}, eP) : {CW0.p(_, m, d) == Some{WNil{}} : Maybe<&2, Word(0n)>}
  %Equal.sym(Bool, ISLAB(m, d, 4), True{}, eI) : {CW0.l(_, m, d) == Some{WNil{}} : Maybe<&2, Word(0n)>}
  %Equal.sym(Bool, LAST(m, d), True{}, eL) : {CW0.z(_) == Some{WNil{}} : Maybe<&2, Word(0n)>}
  {==}

def CW0.n1(+m: C.Cir.Cells, +d: U32, +eP: {Pm(m, d) == False{} : Bool}) -> {CW(0n, m, d) == None{} : Maybe<&2, Word(0n)>}:
  Equal.cong(Bool, Maybe<&2, Word(0n)>, y => CW0.p(y, m, d), Pm(m, d), False{}, eP)

def CW0.n2(+m: C.Cir.Cells, +d: U32, +eP: {Pm(m, d) == True{} : Bool}, +eI: {ISLAB(m, d, 4) == False{} : Bool}) ->
  {CW(0n, m, d) == None{} : Maybe<&2, Word(0n)>}:
  %Equal.sym(Bool, Pm(m, d), True{}, eP) : {CW0.p(_, m, d) == None{} : Maybe<&2, Word(0n)>}
  Equal.cong(Bool, Maybe<&2, Word(0n)>, y => CW0.l(y, m, d), ISLAB(m, d, 4), False{}, eI)

def CW0.n3(+m: C.Cir.Cells, +d: U32, +eP: {Pm(m, d) == True{} : Bool}, +eI: {ISLAB(m, d, 4) == True{} : Bool},
  +eL: {LAST(m, d) == False{} : Bool}) -> {CW(0n, m, d) == None{} : Maybe<&2, Word(0n)>}:
  %Equal.sym(Bool, Pm(m, d), True{}, eP) : {CW0.p(_, m, d) == None{} : Maybe<&2, Word(0n)>}
  %Equal.sym(Bool, ISLAB(m, d, 4), True{}, eI) : {CW0.l(_, m, d) == None{} : Maybe<&2, Word(0n)>}
  Equal.cong(Bool, Maybe<&2, Word(0n)>, y => CW0.z(y), LAST(m, d), False{}, eL)

# CW, from its bits and its WNil
def CWs.some(+p: Nat, +m: C.Cir.Cells, +c: U32, +w: Word(p), +ew: {CWb(p, m, c) == Some{w} : Maybe<&2, Word(p)>},
  +et: {CW(0n, m, Nx(p, m, c)) == Some{WNil{}} : Maybe<&2, Word(0n)>}) -> {CW(p, m, c) == Some{w} : Maybe<&2, Word(p)>}:
  %Equal.sym(Maybe<&2, Word(p)>, CW(p, m, c), CWt(p, CWb(p, m, c), CW(0n, m, Nx(p, m, c))), CW.split(p, m, c)) : {_ == Some{w} : Maybe<&2, Word(p)>}
  %Equal.sym(Maybe<&2, Word(p)>, CWb(p, m, c), Some{w}, ew) : {CWt(p, _, CW(0n, m, Nx(p, m, c))) == Some{w} : Maybe<&2, Word(p)>}
  %Equal.sym(Maybe<&2, Word(0n)>, CW(0n, m, Nx(p, m, c)), Some{WNil{}}, et) : {CWt(p, Some{w}, _) == Some{w} : Maybe<&2, Word(p)>}
  {==}

def CWs.none(+p: Nat, +m: C.Cir.Cells, +c: U32, +w: Word(p), +ew: {CWb(p, m, c) == Some{w} : Maybe<&2, Word(p)>},
  +et: {CW(0n, m, Nx(p, m, c)) == None{} : Maybe<&2, Word(0n)>}) -> {CW(p, m, c) == None{} : Maybe<&2, Word(p)>}:
  %Equal.sym(Maybe<&2, Word(p)>, CW(p, m, c), CWt(p, CWb(p, m, c), CW(0n, m, Nx(p, m, c))), CW.split(p, m, c)) : {_ == None{} : Maybe<&2, Word(p)>}
  %Equal.sym(Maybe<&2, Word(p)>, CWb(p, m, c), Some{w}, ew) : {CWt(p, _, CW(0n, m, Nx(p, m, c))) == None{} : Maybe<&2, Word(p)>}
  %Equal.sym(Maybe<&2, Word(0n)>, CW(0n, m, Nx(p, m, c)), None{}, et) : {CWt(p, Some{w}, _) == None{} : Maybe<&2, Word(p)>}
  {==}

def CWs.none0(+p: Nat, +m: C.Cir.Cells, +c: U32, +ew: {CWb(p, m, c) == None{} : Maybe<&2, Word(p)>}) -> {CW(p, m, c) == None{} : Maybe<&2, Word(p)>}:
  %Equal.sym(Maybe<&2, Word(p)>, CW(p, m, c), CWt(p, CWb(p, m, c), CW(0n, m, Nx(p, m, c))), CW.split(p, m, c)) : {_ == None{} : Maybe<&2, Word(p)>}
  %Equal.sym(Maybe<&2, Word(p)>, CWb(p, m, c), None{}, ew) : {CWt(p, _, CW(0n, m, Nx(p, m, c))) == None{} : Maybe<&2, Word(p)>}
  {==}

# the index of the loop from 0: its 32 rounds, and the bit each sets
def Good32() -> Good(32n, 0, y => y):
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==}))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

# what the run of a word goes on with, by what CW reads: the word in ov, or
# no result
def MWd.Kc(+b: C.Cir.State, +oc: U32, +c: U32, +pg: U32, +out: List<&2, U32>, +outn: U32,
  -K: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type) -> Type:
  @rr: Maybe<&2, Word(32n)> -> {CW(32n, St.cl(b), c) == rr : Maybe<&2, Word(32n)>} ->
    MCW(32n, rr, w => @ow: U32 -> @oi: U32 -> @t1: U32 -> @t2: U32 -> K(ST(b, oc, ow, U32{w}, oi, t1, t2, pg, out, outn)),
      @st: C.Cir.State -> H(2, st))

# the end of a word: its WNil
def MWd.end(+f: Nat, +b: C.Cir.State, +oc: U32, +c: U32, +w: Word(32n), +oi: U32, +t1: U32, +t2: U32, +pg: U32, +out: List<&2, U32>, +outn: U32,
  +nw: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, -K: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type,
  +ew: {CWb(32n, St.cl(b), c) == Some{w} : Maybe<&2, Word(32n)>},
  +hok: {ok(Pn(32n, nw), St.cl(b), ks, img, Nx(32n, St.cl(b), c), St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  kk: MWd.Kc(b, oc, c, pg, out, outn, K, H)) ->
  Wp(C.Cir.exec(1n+f, C.M.do([MW.end()]), ST(b, oc, Nx(32n, St.cl(b), c), U32{w}, oi, t1, t2, pg, out, outn)), K, H):
  +m = St.cl(b)
  +d = Nx(32n, m, c)
  +s0 = ST(b, oc, d, U32{w}, oi, t1, t2, pg, out, outn)
  +hc = ok.isc(Pn(32n, nw), m, ks, img, d, St.im(b), St.fs(b), St.nx(b), hok)
  -K1 = {t => Wp(C.Cir.exec(1n+f, C.Cir.Stmt.nop{}, t), K, H) : C.Cir.State -> Type}
  -A = MWd.Kc(b, oc, c, pg, out, outn, K, H)
  Wp.seq(f, MW.end(), C.Cir.Stmt.nop{}, s0, K, H,
    Wp.need(f, C.M.pair(C.R.ow()), C.M.need(C.M.is_lab(C.M.f(2n, C.M.g(C.R.ow())), C.N.wnil()), C.M.need(C.M.last(C.R.ow()), C.Cir.Stmt.nop{})), s0, K1, H,
      Pm(m, d), ev.pair(46n, s0, d, {==}, hc),
     CasesK(Pm(m, d), A, kk, Wp(C.Cir.exec(1n+f, C.M.need(C.M.is_lab(C.M.f(2n, C.M.g(C.R.ow())), C.N.wnil()), C.M.need(C.M.last(C.R.ow()), C.Cir.Stmt.nop{})), s0), K1, H), H(2, s0),
      kk => +eP =>
        Wp.need(f, C.M.is_lab(C.M.f(2n, C.M.g(C.R.ow())), C.N.wnil()), C.M.need(C.M.last(C.R.ow()), C.Cir.Stmt.nop{}), s0, K1, H, ISLAB(m, d, 4),
          ev.islab(2n, 46n, 4, s0, d, {==}, hc, ok.isc(Pr(Pn(32n, nw)), m, ks, img, Fd(2n, m, d), St.im(b), St.fs(b), St.nx(b), ok.L(Pn(32n, nw), m, ks, img, d, St.im(b), St.fs(b), St.nx(b), hok, eP))),
         CasesK(ISLAB(m, d, 4), A, kk, Wp(C.Cir.exec(1n+f, C.M.need(C.M.last(C.R.ow()), C.Cir.Stmt.nop{}), s0), K1, H), H(2, s0),
          kk => +eI =>
            Wp.need(f, C.M.last(C.R.ow()), C.Cir.Stmt.nop{}, s0, K1, H, LAST(m, d),
              ev.islab(3n, 46n, 0, s0, d, {==}, hc, ok.isc(Pr(Pn(32n, nw)), m, ks, img, Fd(3n, m, d), St.im(b), St.fs(b), St.nx(b), ok.R(Pn(32n, nw), m, ks, img, d, St.im(b), St.fs(b), St.nx(b), hok, eP))),
             CasesK(LAST(m, d), A, kk, Wp(C.Cir.exec(1n+f, C.Cir.Stmt.nop{}, s0), K1, H), H(2, s0),
              kk => +eL =>
                kk(Some{w}, CWs.some(32n, m, c, w, ew, CW0.ok(m, d, eP, eI, eL)), d, oi, t1, t2),
              kk => +eL =>
                kk(None{}, CWs.none(32n, m, c, w, ew, CW0.n3(m, d, eP, eI, eL)), s0))),
          kk => +eI =>
            kk(None{}, CWs.none(32n, m, c, w, ew, CW0.n2(m, d, eP, eI)), s0))),
      kk => +eP =>
        kk(None{}, CWs.none(32n, m, c, w, ew, CW0.n1(m, d, eP)), s0))))

# M.out.word on the cell c in ow: the word that CW reads goes into ov, or
# the run ends with no result
def MWd(+f: Nat, +hF: PN.Le(33n, 1n+f), +b: C.Cir.State, +oc: U32, +c: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32, +pg: U32,
  +out: List<&2, U32>, +outn: U32, +nw: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  -K: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type,
  +hok: {ok(nw, St.cl(b), ks, img, c, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  kk: MWd.Kc(b, oc, c, pg, out, outn, K, H)) ->
  Wp(C.Cir.exec(1n+f, C.M.out.word(), ST(b, oc, c, ov, oi, t1, t2, pg, out, outn)), K, H):
  +m = St.cl(b)
  +s1 = ST(b, oc, c, 0, oi, t1, t2, pg, out, outn)
  +s2 = ST(b, oc, c, 0, 0, t1, t2, pg, out, outn)
  -K1 = {t => Wp(C.Cir.exec(1n+f, C.M.do([MW.end()]), t), K, H) : C.Cir.State -> Type}
  -A = MWd.Kc(b, oc, c, pg, out, outn, K, H)
  Wp.seq(f, C.M.set(C.R.ov(), C.M.c(0)), C.M.do([C.M.set(C.R.oi(), C.M.c(0)), MW.loop(), MW.end()]), ST(b, oc, c, ov, oi, t1, t2, pg, out, outn), K, H,
    Wp.set(f, 47n, C.M.c(0), ST(b, oc, c, ov, oi, t1, t2, pg, out, outn), t => Wp(C.Cir.exec(1n+f, C.M.do([C.M.set(C.R.oi(), C.M.c(0)), MW.loop(), MW.end()]), t), K, H), H, 0, {==},
      Wp.seq(f, C.M.set(C.R.oi(), C.M.c(0)), C.M.do([MW.loop(), MW.end()]), s1, K, H,
        Wp.set(f, 48n, C.M.c(0), s1, t => Wp(C.Cir.exec(1n+f, C.M.do([MW.loop(), MW.end()]), t), K, H), H, 0, {==},
          Wp.seq(f, MW.loop(), C.M.do([MW.end()]), s2, K, H,
            ML(32n, 1n+f, hF, b, oc, c, 0, 0, t1, t2, pg, out, outn, nw, ks, img, y => y, y => y, {==}, Good32(), K1, H, {==}, hok,
              rr => +err => CasesW(32n, rr, A, kk,
                w => {ok(Pn(32n, nw), m, ks, img, Nx(32n, m, c), St.im(b), St.fs(b), St.nx(b)) == True{} : Bool} ->
                  @oi: U32 -> @t1: U32 -> @t2: U32 -> K1(ST(b, oc, Nx(32n, m, c), U32{w}, oi, t1, t2, pg, out, outn)),
                @st: C.Cir.State -> H(2, st),
                kk => +w => +ew => +hokd => +oi2 => +t12 => +t22 =>
                  MWd.end(f, b, oc, c, w, oi2, t12, t22, pg, out, outn, nw, ks, img, K, H,
                    Equal.trans(Maybe<&2, Word(32n)>, CWb(32n, m, c), rr, Some{w}, err, ew), hokd, kk),
                kk => +ew =>
                  st => kk(None{}, CWs.none0(32n, m, c, Equal.trans(Maybe<&2, Word(32n)>, CWb(32n, m, c), rr, None{}, err, ew)), st))))))))

# a U32 below 256 is its low byte
def lowbyte.h(b31: Bool, b30: Bool, b29: Bool, b28: Bool, b27: Bool, b26: Bool, b25: Bool, b24: Bool, b23: Bool, b22: Bool, b21: Bool, b20: Bool, b19: Bool, b18: Bool, b17: Bool, b16: Bool, b15: Bool, b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool,
  +h: {U32.is_lt(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 256) == True{} : Bool}) ->
  {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}:
  match b31:
    case True{}:
      Empty.absurd({U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{True{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{True{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}, PN.false_ne_true(h))
    case False{}:
      match b30:
        case True{}:
          Empty.absurd({U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}, PN.false_ne_true(h))
        case False{}:
          match b29:
            case True{}:
              Empty.absurd({U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}, PN.false_ne_true(h))
            case False{}:
              match b28:
                case True{}:
                  Empty.absurd({U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}, PN.false_ne_true(h))
                case False{}:
                  match b27:
                    case True{}:
                      Empty.absurd({U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}, PN.false_ne_true(h))
                    case False{}:
                      match b26:
                        case True{}:
                          Empty.absurd({U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}, PN.false_ne_true(h))
                        case False{}:
                          match b25:
                            case True{}:
                              Empty.absurd({U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}, PN.false_ne_true(h))
                            case False{}:
                              match b24:
                                case True{}:
                                  Empty.absurd({U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}, PN.false_ne_true(h))
                                case False{}:
                                  match b23:
                                    case True{}:
                                      Empty.absurd({U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}, PN.false_ne_true(h))
                                    case False{}:
                                      match b22:
                                        case True{}:
                                          Empty.absurd({U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}, PN.false_ne_true(h))
                                        case False{}:
                                          match b21:
                                            case True{}:
                                              Empty.absurd({U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}, PN.false_ne_true(h))
                                            case False{}:
                                              match b20:
                                                case True{}:
                                                  Empty.absurd({U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}, PN.false_ne_true(h))
                                                case False{}:
                                                  match b19:
                                                    case True{}:
                                                      Empty.absurd({U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}, PN.false_ne_true(h))
                                                    case False{}:
                                                      match b18:
                                                        case True{}:
                                                          Empty.absurd({U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}, PN.false_ne_true(h))
                                                        case False{}:
                                                          match b17:
                                                            case True{}:
                                                              Empty.absurd({U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}, PN.false_ne_true(h))
                                                            case False{}:
                                                              match b16:
                                                                case True{}:
                                                                  Empty.absurd({U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}, PN.false_ne_true(h))
                                                                case False{}:
                                                                  match b15:
                                                                    case True{}:
                                                                      Empty.absurd({U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}, PN.false_ne_true(h))
                                                                    case False{}:
                                                                      match b14:
                                                                        case True{}:
                                                                          Empty.absurd({U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}, PN.false_ne_true(h))
                                                                        case False{}:
                                                                          match b13:
                                                                            case True{}:
                                                                              Empty.absurd({U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}, PN.false_ne_true(h))
                                                                            case False{}:
                                                                              match b12:
                                                                                case True{}:
                                                                                  Empty.absurd({U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}, PN.false_ne_true(h))
                                                                                case False{}:
                                                                                  match b11:
                                                                                    case True{}:
                                                                                      Empty.absurd({U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}, PN.false_ne_true(h))
                                                                                    case False{}:
                                                                                      match b10:
                                                                                        case True{}:
                                                                                          Empty.absurd({U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}, PN.false_ne_true(h))
                                                                                        case False{}:
                                                                                          match b9:
                                                                                            case True{}:
                                                                                              Empty.absurd({U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}, PN.false_ne_true(h))
                                                                                            case False{}:
                                                                                              match b8:
                                                                                                case True{}:
                                                                                                  Empty.absurd({U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32.and(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 255) : U32}, PN.true_ne_false(Equal.trans(Bool, True{}, U32.is_lt(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 256), False{}, Equal.sym(Bool, U32.is_lt(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 256), True{}, h), nolt(8n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}))))
                                                                                                case False{}:
                                                                                                  Equal.cong(Word(32n), U32, x => U32{x}, cat(8n, 24n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}, zeros(24n)), Word.and(32n, cat(8n, 24n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}, zeros(24n)), PN.ones(32n, 8n)),
                                                                                                    Equal.sym(Word(32n), Word.and(32n, cat(8n, 24n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}, zeros(24n)), PN.ones(32n, 8n)), cat(8n, 24n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}, zeros(24n)), and_cat(8n, 24n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}})))

def lowbyte(+w: Word(32n), +h: {U32.is_lt(U32{w}, 256) == True{} : Bool}) -> {U32{w} == U32.and(U32{w}, 255) : U32}:
  match w:
    case WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, WCon{+b6, WCon{+b7, WCon{+b8, WCon{+b9, WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WCon{+b16, WCon{+b17, WCon{+b18, WCon{+b19, WCon{+b20, WCon{+b21, WCon{+b22, WCon{+b23, WCon{+b24, WCon{+b25, WCon{+b26, WCon{+b27, WCon{+b28, WCon{+b29, WCon{+b30, WCon{+b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      lowbyte.h(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, h)

# the steps of S.c0: its value once its tests pass, or none when one fails
def Sc.ok(+m: C.Cir.Cells, +bc: U32, +w: Word(32n),
  +ePb: {Pm(m, bc) == True{} : Bool},
  +ePy: {Pm(m, Fd(3n, m, bc)) == True{} : Bool},
  +eLy: {LAST(m, Fd(3n, m, bc)) == True{} : Bool},
  +ePx: {Pm(m, Fd(2n, m, bc)) == True{} : Bool},
  +eIx: {ISLAB(m, Fd(2n, m, bc), 3) == True{} : Bool},
  +ePw: {Pm(m, Fd(3n, m, Fd(2n, m, bc))) == True{} : Bool},
  +eLw: {LAST(m, Fd(3n, m, Fd(2n, m, bc))) == True{} : Bool},
  +eW: {CW(32n, m, Fd(2n, m, Fd(3n, m, Fd(2n, m, bc)))) == Some{w} : Maybe<&2, Word(32n)>},
  +eV: {U32.is_lt(U32{w}, 256) == True{} : Bool}) ->
  {S.c0(Pm(m, bc), m, bc) == SR.more{U32{w}, Fd(2n, m, Fd(3n, m, bc))} : SR}:
  +xc = Fd(2n, m, bc)
  +yc = Fd(3n, m, bc)
  +rc = Fd(2n, m, yc)
  +wtc = Fd(3n, m, xc)
  +wc = Fd(2n, m, wtc)
  %Equal.sym(Bool, Pm(m, bc), True{}, ePb) : {S.c0(_, m, bc) == SR.more{U32{w}, Fd(2n, m, Fd(3n, m, bc))} : SR}
  %Equal.sym(Bool, Pm(m, yc), True{}, ePy) : {S.c1(_, m, xc, yc) == SR.more{U32{w}, Fd(2n, m, Fd(3n, m, bc))} : SR}
  %Equal.sym(Bool, LAST(m, yc), True{}, eLy) : {S.c2(_, m, xc, rc) == SR.more{U32{w}, Fd(2n, m, Fd(3n, m, bc))} : SR}
  %Equal.sym(Bool, Pm(m, xc), True{}, ePx) : {S.c3(_, m, xc, rc) == SR.more{U32{w}, Fd(2n, m, Fd(3n, m, bc))} : SR}
  %Equal.sym(Bool, ISLAB(m, xc, 3), True{}, eIx) : {S.c4(_, m, wtc, rc) == SR.more{U32{w}, Fd(2n, m, Fd(3n, m, bc))} : SR}
  %Equal.sym(Bool, Pm(m, wtc), True{}, ePw) : {S.c5(_, m, wtc, rc) == SR.more{U32{w}, Fd(2n, m, Fd(3n, m, bc))} : SR}
  %Equal.sym(Bool, LAST(m, wtc), True{}, eLw) : {S.c6(_, m, wc, rc) == SR.more{U32{w}, Fd(2n, m, Fd(3n, m, bc))} : SR}
  %Equal.sym(Maybe<&2, Word(32n)>, CW(32n, m, wc), Some{w}, eW) : {S.c7(_, rc) == SR.more{U32{w}, Fd(2n, m, Fd(3n, m, bc))} : SR}
  %Equal.sym(Bool, U32.is_lt(U32{w}, 256), True{}, eV) : {S.c8(_, U32{w}, rc) == SR.more{U32{w}, Fd(2n, m, Fd(3n, m, bc))} : SR}
  {==}

def Sc.n1(+m: C.Cir.Cells, +bc: U32, +w: Word(32n),
  +ePb: {Pm(m, bc) == False{} : Bool}) ->
  {S.c0(Pm(m, bc), m, bc) == SR.done{None{}} : SR}:
  +xc = Fd(2n, m, bc)
  +yc = Fd(3n, m, bc)
  +rc = Fd(2n, m, yc)
  +wtc = Fd(3n, m, xc)
  +wc = Fd(2n, m, wtc)
  Equal.cong(Bool, SR, yy => S.c0(yy, m, bc), Pm(m, bc), False{}, ePb)

def Sc.n2(+m: C.Cir.Cells, +bc: U32, +w: Word(32n),
  +ePb: {Pm(m, bc) == True{} : Bool},
  +ePy: {Pm(m, Fd(3n, m, bc)) == False{} : Bool}) ->
  {S.c0(Pm(m, bc), m, bc) == SR.done{None{}} : SR}:
  +xc = Fd(2n, m, bc)
  +yc = Fd(3n, m, bc)
  +rc = Fd(2n, m, yc)
  +wtc = Fd(3n, m, xc)
  +wc = Fd(2n, m, wtc)
  %Equal.sym(Bool, Pm(m, bc), True{}, ePb) : {S.c0(_, m, bc) == SR.done{None{}} : SR}
  Equal.cong(Bool, SR, yy => S.c1(yy, m, xc, yc), Pm(m, yc), False{}, ePy)

def Sc.n3(+m: C.Cir.Cells, +bc: U32, +w: Word(32n),
  +ePb: {Pm(m, bc) == True{} : Bool},
  +ePy: {Pm(m, Fd(3n, m, bc)) == True{} : Bool},
  +eLy: {LAST(m, Fd(3n, m, bc)) == False{} : Bool}) ->
  {S.c0(Pm(m, bc), m, bc) == SR.done{None{}} : SR}:
  +xc = Fd(2n, m, bc)
  +yc = Fd(3n, m, bc)
  +rc = Fd(2n, m, yc)
  +wtc = Fd(3n, m, xc)
  +wc = Fd(2n, m, wtc)
  %Equal.sym(Bool, Pm(m, bc), True{}, ePb) : {S.c0(_, m, bc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, Pm(m, yc), True{}, ePy) : {S.c1(_, m, xc, yc) == SR.done{None{}} : SR}
  Equal.cong(Bool, SR, yy => S.c2(yy, m, xc, rc), LAST(m, yc), False{}, eLy)

def Sc.n4(+m: C.Cir.Cells, +bc: U32, +w: Word(32n),
  +ePb: {Pm(m, bc) == True{} : Bool},
  +ePy: {Pm(m, Fd(3n, m, bc)) == True{} : Bool},
  +eLy: {LAST(m, Fd(3n, m, bc)) == True{} : Bool},
  +ePx: {Pm(m, Fd(2n, m, bc)) == False{} : Bool}) ->
  {S.c0(Pm(m, bc), m, bc) == SR.done{None{}} : SR}:
  +xc = Fd(2n, m, bc)
  +yc = Fd(3n, m, bc)
  +rc = Fd(2n, m, yc)
  +wtc = Fd(3n, m, xc)
  +wc = Fd(2n, m, wtc)
  %Equal.sym(Bool, Pm(m, bc), True{}, ePb) : {S.c0(_, m, bc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, Pm(m, yc), True{}, ePy) : {S.c1(_, m, xc, yc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, LAST(m, yc), True{}, eLy) : {S.c2(_, m, xc, rc) == SR.done{None{}} : SR}
  Equal.cong(Bool, SR, yy => S.c3(yy, m, xc, rc), Pm(m, xc), False{}, ePx)

def Sc.n5(+m: C.Cir.Cells, +bc: U32, +w: Word(32n),
  +ePb: {Pm(m, bc) == True{} : Bool},
  +ePy: {Pm(m, Fd(3n, m, bc)) == True{} : Bool},
  +eLy: {LAST(m, Fd(3n, m, bc)) == True{} : Bool},
  +ePx: {Pm(m, Fd(2n, m, bc)) == True{} : Bool},
  +eIx: {ISLAB(m, Fd(2n, m, bc), 3) == False{} : Bool}) ->
  {S.c0(Pm(m, bc), m, bc) == SR.done{None{}} : SR}:
  +xc = Fd(2n, m, bc)
  +yc = Fd(3n, m, bc)
  +rc = Fd(2n, m, yc)
  +wtc = Fd(3n, m, xc)
  +wc = Fd(2n, m, wtc)
  %Equal.sym(Bool, Pm(m, bc), True{}, ePb) : {S.c0(_, m, bc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, Pm(m, yc), True{}, ePy) : {S.c1(_, m, xc, yc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, LAST(m, yc), True{}, eLy) : {S.c2(_, m, xc, rc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, Pm(m, xc), True{}, ePx) : {S.c3(_, m, xc, rc) == SR.done{None{}} : SR}
  Equal.cong(Bool, SR, yy => S.c4(yy, m, wtc, rc), ISLAB(m, xc, 3), False{}, eIx)

def Sc.n6(+m: C.Cir.Cells, +bc: U32, +w: Word(32n),
  +ePb: {Pm(m, bc) == True{} : Bool},
  +ePy: {Pm(m, Fd(3n, m, bc)) == True{} : Bool},
  +eLy: {LAST(m, Fd(3n, m, bc)) == True{} : Bool},
  +ePx: {Pm(m, Fd(2n, m, bc)) == True{} : Bool},
  +eIx: {ISLAB(m, Fd(2n, m, bc), 3) == True{} : Bool},
  +ePw: {Pm(m, Fd(3n, m, Fd(2n, m, bc))) == False{} : Bool}) ->
  {S.c0(Pm(m, bc), m, bc) == SR.done{None{}} : SR}:
  +xc = Fd(2n, m, bc)
  +yc = Fd(3n, m, bc)
  +rc = Fd(2n, m, yc)
  +wtc = Fd(3n, m, xc)
  +wc = Fd(2n, m, wtc)
  %Equal.sym(Bool, Pm(m, bc), True{}, ePb) : {S.c0(_, m, bc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, Pm(m, yc), True{}, ePy) : {S.c1(_, m, xc, yc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, LAST(m, yc), True{}, eLy) : {S.c2(_, m, xc, rc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, Pm(m, xc), True{}, ePx) : {S.c3(_, m, xc, rc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, ISLAB(m, xc, 3), True{}, eIx) : {S.c4(_, m, wtc, rc) == SR.done{None{}} : SR}
  Equal.cong(Bool, SR, yy => S.c5(yy, m, wtc, rc), Pm(m, wtc), False{}, ePw)

def Sc.n7(+m: C.Cir.Cells, +bc: U32, +w: Word(32n),
  +ePb: {Pm(m, bc) == True{} : Bool},
  +ePy: {Pm(m, Fd(3n, m, bc)) == True{} : Bool},
  +eLy: {LAST(m, Fd(3n, m, bc)) == True{} : Bool},
  +ePx: {Pm(m, Fd(2n, m, bc)) == True{} : Bool},
  +eIx: {ISLAB(m, Fd(2n, m, bc), 3) == True{} : Bool},
  +ePw: {Pm(m, Fd(3n, m, Fd(2n, m, bc))) == True{} : Bool},
  +eLw: {LAST(m, Fd(3n, m, Fd(2n, m, bc))) == False{} : Bool}) ->
  {S.c0(Pm(m, bc), m, bc) == SR.done{None{}} : SR}:
  +xc = Fd(2n, m, bc)
  +yc = Fd(3n, m, bc)
  +rc = Fd(2n, m, yc)
  +wtc = Fd(3n, m, xc)
  +wc = Fd(2n, m, wtc)
  %Equal.sym(Bool, Pm(m, bc), True{}, ePb) : {S.c0(_, m, bc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, Pm(m, yc), True{}, ePy) : {S.c1(_, m, xc, yc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, LAST(m, yc), True{}, eLy) : {S.c2(_, m, xc, rc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, Pm(m, xc), True{}, ePx) : {S.c3(_, m, xc, rc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, ISLAB(m, xc, 3), True{}, eIx) : {S.c4(_, m, wtc, rc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, Pm(m, wtc), True{}, ePw) : {S.c5(_, m, wtc, rc) == SR.done{None{}} : SR}
  Equal.cong(Bool, SR, yy => S.c6(yy, m, wc, rc), LAST(m, wtc), False{}, eLw)

def Sc.n8(+m: C.Cir.Cells, +bc: U32, +w: Word(32n),
  +ePb: {Pm(m, bc) == True{} : Bool},
  +ePy: {Pm(m, Fd(3n, m, bc)) == True{} : Bool},
  +eLy: {LAST(m, Fd(3n, m, bc)) == True{} : Bool},
  +ePx: {Pm(m, Fd(2n, m, bc)) == True{} : Bool},
  +eIx: {ISLAB(m, Fd(2n, m, bc), 3) == True{} : Bool},
  +ePw: {Pm(m, Fd(3n, m, Fd(2n, m, bc))) == True{} : Bool},
  +eLw: {LAST(m, Fd(3n, m, Fd(2n, m, bc))) == True{} : Bool},
  +eW: {CW(32n, m, Fd(2n, m, Fd(3n, m, Fd(2n, m, bc)))) == None{} : Maybe<&2, Word(32n)>}) ->
  {S.c0(Pm(m, bc), m, bc) == SR.done{None{}} : SR}:
  +xc = Fd(2n, m, bc)
  +yc = Fd(3n, m, bc)
  +rc = Fd(2n, m, yc)
  +wtc = Fd(3n, m, xc)
  +wc = Fd(2n, m, wtc)
  %Equal.sym(Bool, Pm(m, bc), True{}, ePb) : {S.c0(_, m, bc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, Pm(m, yc), True{}, ePy) : {S.c1(_, m, xc, yc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, LAST(m, yc), True{}, eLy) : {S.c2(_, m, xc, rc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, Pm(m, xc), True{}, ePx) : {S.c3(_, m, xc, rc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, ISLAB(m, xc, 3), True{}, eIx) : {S.c4(_, m, wtc, rc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, Pm(m, wtc), True{}, ePw) : {S.c5(_, m, wtc, rc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, LAST(m, wtc), True{}, eLw) : {S.c6(_, m, wc, rc) == SR.done{None{}} : SR}
  Equal.cong(Maybe<&2, Word(32n)>, SR, yy => S.c7(yy, rc), CW(32n, m, wc), None{}, eW)

def Sc.n9(+m: C.Cir.Cells, +bc: U32, +w: Word(32n),
  +ePb: {Pm(m, bc) == True{} : Bool},
  +ePy: {Pm(m, Fd(3n, m, bc)) == True{} : Bool},
  +eLy: {LAST(m, Fd(3n, m, bc)) == True{} : Bool},
  +ePx: {Pm(m, Fd(2n, m, bc)) == True{} : Bool},
  +eIx: {ISLAB(m, Fd(2n, m, bc), 3) == True{} : Bool},
  +ePw: {Pm(m, Fd(3n, m, Fd(2n, m, bc))) == True{} : Bool},
  +eLw: {LAST(m, Fd(3n, m, Fd(2n, m, bc))) == True{} : Bool},
  +eW: {CW(32n, m, Fd(2n, m, Fd(3n, m, Fd(2n, m, bc)))) == Some{w} : Maybe<&2, Word(32n)>},
  +eV: {U32.is_lt(U32{w}, 256) == False{} : Bool}) ->
  {S.c0(Pm(m, bc), m, bc) == SR.done{None{}} : SR}:
  +xc = Fd(2n, m, bc)
  +yc = Fd(3n, m, bc)
  +rc = Fd(2n, m, yc)
  +wtc = Fd(3n, m, xc)
  +wc = Fd(2n, m, wtc)
  %Equal.sym(Bool, Pm(m, bc), True{}, ePb) : {S.c0(_, m, bc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, Pm(m, yc), True{}, ePy) : {S.c1(_, m, xc, yc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, LAST(m, yc), True{}, eLy) : {S.c2(_, m, xc, rc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, Pm(m, xc), True{}, ePx) : {S.c3(_, m, xc, rc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, ISLAB(m, xc, 3), True{}, eIx) : {S.c4(_, m, wtc, rc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, Pm(m, wtc), True{}, ePw) : {S.c5(_, m, wtc, rc) == SR.done{None{}} : SR}
  %Equal.sym(Bool, LAST(m, wtc), True{}, eLw) : {S.c6(_, m, wc, rc) == SR.done{None{}} : SR}
  %Equal.sym(Maybe<&2, Word(32n)>, CW(32n, m, wc), Some{w}, eW) : {S.c7(_, rc) == SR.done{None{}} : SR}
  Equal.cong(Bool, SR, yy => S.c8(yy, U32{w}, rc), U32.is_lt(U32{w}, 256), False{}, eV)

# The byte
# --------

# the statements of M.out.con
def OC.A1() -> C.Cir.Stmt:
  C.M.set(C.R.oc(), C.M.f(3n, C.M.g(C.R.oc())))

def OC.B1() -> C.Cir.Stmt:
  C.M.set(C.R.ow(), C.M.f(2n, C.M.g(C.R.oc())))

def OC.B2() -> C.Cir.Stmt:
  C.M.set(C.R.oc(), C.M.f(3n, C.M.g(C.R.oc())))

def OC.C1() -> C.Cir.Stmt:
  C.M.set(C.R.oc(), C.M.f(2n, C.M.g(C.R.oc())))

def OC.D1() -> C.Cir.Stmt:
  C.M.set(C.R.ow(), C.M.f(3n, C.M.g(C.R.ow())))

def OC.E1() -> C.Cir.Stmt:
  C.M.set(C.R.ow(), C.M.f(2n, C.M.g(C.R.ow())))

def OC.E3() -> C.Cir.Stmt:
  C.M.need(C.M.lt(C.M.g(C.R.ov()), C.M.c(256)), C.Cir.Stmt.emit{C.M.g(C.R.ov())})

def OC.E() -> C.Cir.Stmt:
  C.M.do([OC.E1(), C.M.out.word(), OC.E3()])

def OC.D2() -> C.Cir.Stmt:
  C.M.need(C.M.pair(C.R.ow()), C.M.need(C.M.last(C.R.ow()), OC.E()))

def OC.D() -> C.Cir.Stmt:
  C.M.do([OC.D1(), OC.D2()])

def OC.C2() -> C.Cir.Stmt:
  C.M.need(C.M.pair(C.R.ow()), C.M.need(C.M.is_lab(C.M.f(2n, C.M.g(C.R.ow())), C.N.u32()), OC.D()))

def OC.C() -> C.Cir.Stmt:
  C.M.do([OC.C1(), OC.C2()])

def OC.B3() -> C.Cir.Stmt:
  C.M.need(C.M.pair(C.R.oc()), C.M.need(C.M.last(C.R.oc()), OC.C()))

def OC.B() -> C.Cir.Stmt:
  C.M.do([OC.B1(), OC.B2(), OC.B3()])

# Y for a list's end, X(v, rest) for a byte v and the cell of the rest
def MSR(s: SR, X: U32 -> U32 -> Type, Y: Maybe<&2, List<&2, U32>> -> Type) -> Type:
  match s:
    case SR.more{v, rest}:
      X(v, rest)
    case SR.done{r}:
      Y(r)

def CasesS(s: SR, -A: Type, a: A, -X: U32 -> U32 -> Type, -Y: Maybe<&2, List<&2, U32>> -> Type,
  sm: A -> @v: U32 -> @rest: U32 -> {s == SR.more{v, rest} : SR} -> X(v, rest),
  sd: A -> @r: Maybe<&2, List<&2, U32>> -> {s == SR.done{r} : SR} -> Y(r)) -> MSR(s, X, Y):
  match s:
    case SR.more{v, rest}:
      sm(a, v, rest, {==})
    case SR.done{r}:
      sd(a, r, {==})

# what the run of M.out.con goes on with, by what S.c0 reads at the fields
# of the cell c: its byte out, with oc at the rest of the list, or no result
def MC.Kc(+b: C.Cir.State, +c: U32, +pg: U32, +out: List<&2, U32>, +outn: U32, +n1: Nat, +ks: List<&2, List<&2, U32>>,
  +img: List<&2, C.Term>, -K: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type) -> Type:
  @s: SR -> {S.c0(Pm(St.cl(b), Fd(3n, St.cl(b), c)), St.cl(b), Fd(3n, St.cl(b), c)) == s : SR} ->
    MSR(s, v => rest => {ok(Pr(Pr(n1)), St.cl(b), ks, img, rest, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool} ->
      @pg2: U32 -> @ow: U32 -> @ov: U32 -> @oi: U32 -> @t1: U32 -> @t2: U32 -> K(ST(b, rest, ow, ov, oi, t1, t2, pg2, Con{v, out}, U32.inc(outn))),
      r => {r == None{} : Maybe<&2, List<&2, U32>>} -> @st: C.Cir.State -> H(2, st))

# the byte goes out
def MC.emit(+f: Nat, +b: C.Cir.State, +c: U32, +ow: U32, +w: Word(32n), +oi: U32, +t1: U32, +t2: U32, +pg: U32,
  +out: List<&2, U32>, +outn: U32, +n1: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  -K: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type,
  +hok1: {ok(n1, St.cl(b), ks, img, Fd(3n, St.cl(b), c), St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  +ePb: {Pm(St.cl(b), Fd(3n, St.cl(b), c)) == True{} : Bool},
  +ePy: {Pm(St.cl(b), Fd(3n, St.cl(b), Fd(3n, St.cl(b), c))) == True{} : Bool},
  +eLy: {LAST(St.cl(b), Fd(3n, St.cl(b), Fd(3n, St.cl(b), c))) == True{} : Bool},
  +ePx: {Pm(St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c))) == True{} : Bool},
  +eIx: {ISLAB(St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)), 3) == True{} : Bool},
  +ePw: {Pm(St.cl(b), Fd(3n, St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)))) == True{} : Bool},
  +eLw: {LAST(St.cl(b), Fd(3n, St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)))) == True{} : Bool},
  +eW: {CW(32n, St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c))))) == Some{w} : Maybe<&2, Word(32n)>},
  kk: MC.Kc(b, c, pg, out, outn, n1, ks, img, K, H)) ->
  Wp(C.Cir.exec(1n+f, C.M.do([OC.E3()]), ST(b, Fd(2n, St.cl(b), Fd(3n, St.cl(b), Fd(3n, St.cl(b), c))), ow, U32{w}, oi, t1, t2, pg, out, outn)), K, H):
  +m = St.cl(b)
  +bc = Fd(3n, m, c)
  +xc = Fd(2n, m, bc)
  +yc = Fd(3n, m, bc)
  +rc = Fd(2n, m, yc)
  +wtc = Fd(3n, m, xc)
  +wc = Fd(2n, m, wtc)
  -A = MC.Kc(b, c, pg, out, outn, n1, ks, img, K, H)
  +s = ST(b, rc, ow, U32{w}, oi, t1, t2, pg, out, outn)
  -K1 = {t => Wp(C.Cir.exec(1n+f, C.Cir.Stmt.nop{}, t), K, H) : C.Cir.State -> Type}
  Wp.seq(f, OC.E3(), C.Cir.Stmt.nop{}, s, K, H,
    Wp.need(f, C.M.lt(C.M.g(C.R.ov()), C.M.c(256)), C.Cir.Stmt.emit{C.M.g(C.R.ov())}, s, K1, H, U32.is_lt(U32{w}, 256),
      ev.lt(47n, 256, s, U32{w}, {==}, U32.is_lt(U32{w}, 256), {==}),
     CasesK(U32.is_lt(U32{w}, 256), A, kk, Wp(C.Cir.exec(1n+f, C.Cir.Stmt.emit{C.M.g(C.R.ov())}, s), K1, H), H(2, s),
      kk => +eV =>
        Wp.emit(f, C.M.g(C.R.ov()), s, K1, H, U32{w}, {==},
          p => Tr(U32, v => K(ST(b, rc, ow, U32{w}, oi, t1, t2, p, Con{v, out}, U32.inc(outn))), U32{w}, U32.and(U32{w}, 255), lowbyte(w, eV),
            kk(SR.more{U32{w}, rc}, Sc.ok(m, bc, w, ePb, ePy, eLy, ePx, eIx, ePw, eLw, eW, eV), ok.L(Pr(n1), m, ks, img, yc, St.im(b), St.fs(b), St.nx(b), ok.R(n1, m, ks, img, bc, St.im(b), St.fs(b), St.nx(b), hok1, ePb), ePy), p, ow, U32{w}, oi, t1, t2))),
      kk => +eV =>
        kk(SR.done{None{}}, Sc.n9(m, bc, w, ePb, ePy, eLy, ePx, eIx, ePw, eLw, eW, eV), {==}, s))))

# the word of the byte
def MC.E(+f: Nat, +hF: PN.Le(33n, 1n+f), +b: C.Cir.State, +c: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32, +pg: U32,
  +out: List<&2, U32>, +outn: U32, +n1: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  -K: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type,
  +hok1: {ok(n1, St.cl(b), ks, img, Fd(3n, St.cl(b), c), St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  +ePb: {Pm(St.cl(b), Fd(3n, St.cl(b), c)) == True{} : Bool},
  +ePy: {Pm(St.cl(b), Fd(3n, St.cl(b), Fd(3n, St.cl(b), c))) == True{} : Bool},
  +eLy: {LAST(St.cl(b), Fd(3n, St.cl(b), Fd(3n, St.cl(b), c))) == True{} : Bool},
  +ePx: {Pm(St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c))) == True{} : Bool},
  +eIx: {ISLAB(St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)), 3) == True{} : Bool},
  +ePw: {Pm(St.cl(b), Fd(3n, St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)))) == True{} : Bool},
  +eLw: {LAST(St.cl(b), Fd(3n, St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)))) == True{} : Bool},
  kk: MC.Kc(b, c, pg, out, outn, n1, ks, img, K, H)) ->
  Wp(C.Cir.exec(1n+f, OC.E(), ST(b, Fd(2n, St.cl(b), Fd(3n, St.cl(b), Fd(3n, St.cl(b), c))), Fd(3n, St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c))), ov, oi, t1, t2, pg, out, outn)), K, H):
  +m = St.cl(b)
  +bc = Fd(3n, m, c)
  +xc = Fd(2n, m, bc)
  +yc = Fd(3n, m, bc)
  +rc = Fd(2n, m, yc)
  +wtc = Fd(3n, m, xc)
  +wc = Fd(2n, m, wtc)
  -A = MC.Kc(b, c, pg, out, outn, n1, ks, img, K, H)
  +s0 = ST(b, rc, wtc, ov, oi, t1, t2, pg, out, outn)
  +s1 = ST(b, rc, wc, ov, oi, t1, t2, pg, out, outn)
  Wp.seq(f, OC.E1(), C.M.do([C.M.out.word(), OC.E3()]), s0, K, H,
    Wp.set(f, 46n, C.M.f(2n, C.M.g(C.R.ow())), s0, t => Wp(C.Cir.exec(1n+f, C.M.do([C.M.out.word(), OC.E3()]), t), K, H), H, wc,
      ev.f(2n, C.M.g(C.R.ow()), s0, wtc, {==}, ok.isc(Pr(Pr(n1)), m, ks, img, wtc, St.im(b), St.fs(b), St.nx(b), ok.R(Pr(n1), m, ks, img, xc, St.im(b), St.fs(b), St.nx(b), ok.L(n1, m, ks, img, bc, St.im(b), St.fs(b), St.nx(b), hok1, ePb), ePx))),
      Wp.seq(f, C.M.out.word(), C.M.do([OC.E3()]), s1, K, H,
        MWd(f, hF, b, rc, wc, ov, oi, t1, t2, pg, out, outn, Pr(Pr(Pr(n1))), ks, img, t => Wp(C.Cir.exec(1n+f, C.M.do([OC.E3()]), t), K, H), H,
          ok.L(Pr(Pr(n1)), m, ks, img, wtc, St.im(b), St.fs(b), St.nx(b), ok.R(Pr(n1), m, ks, img, xc, St.im(b), St.fs(b), St.nx(b), ok.L(n1, m, ks, img, bc, St.im(b), St.fs(b), St.nx(b), hok1, ePb), ePx), ePw),
          rr => +err => CasesW(32n, rr, A, kk,
            w => @ow: U32 -> @oi: U32 -> @t1: U32 -> @t2: U32 -> Wp(C.Cir.exec(1n+f, C.M.do([OC.E3()]), ST(b, rc, ow, U32{w}, oi, t1, t2, pg, out, outn)), K, H),
            @st: C.Cir.State -> H(2, st),
            kk => +w => +ew => +ow2 => +oi2 => +t12 => +t22 =>
              MC.emit(f, b, c, ow2, w, oi2, t12, t22, pg, out, outn, n1, ks, img, K, H, hok1, ePb, ePy, eLy, ePx, eIx, ePw, eLw,
                Equal.trans(Maybe<&2, Word(32n)>, CW(32n, m, wc), rr, Some{w}, err, ew), kk),
            kk => +ew =>
              st => kk(SR.done{None{}}, Sc.n8(m, bc, zeros(32n), ePb, ePy, eLy, ePx, eIx, ePw, eLw,
                Equal.trans(Maybe<&2, Word(32n)>, CW(32n, m, wc), rr, None{}, err, ew)), {==}, st))))))

# the U32 of the byte
def MC.D(+f: Nat, +hF: PN.Le(33n, 1n+f), +b: C.Cir.State, +c: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32, +pg: U32,
  +out: List<&2, U32>, +outn: U32, +n1: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  -K: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type,
  +hok1: {ok(n1, St.cl(b), ks, img, Fd(3n, St.cl(b), c), St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  +ePb: {Pm(St.cl(b), Fd(3n, St.cl(b), c)) == True{} : Bool},
  +ePy: {Pm(St.cl(b), Fd(3n, St.cl(b), Fd(3n, St.cl(b), c))) == True{} : Bool},
  +eLy: {LAST(St.cl(b), Fd(3n, St.cl(b), Fd(3n, St.cl(b), c))) == True{} : Bool},
  +ePx: {Pm(St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c))) == True{} : Bool},
  +eIx: {ISLAB(St.cl(b), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)), 3) == True{} : Bool},
  kk: MC.Kc(b, c, pg, out, outn, n1, ks, img, K, H)) ->
  Wp(C.Cir.exec(1n+f, OC.D(), ST(b, Fd(2n, St.cl(b), Fd(3n, St.cl(b), Fd(3n, St.cl(b), c))), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)), ov, oi, t1, t2, pg, out, outn)), K, H):
  +m = St.cl(b)
  +bc = Fd(3n, m, c)
  +xc = Fd(2n, m, bc)
  +yc = Fd(3n, m, bc)
  +rc = Fd(2n, m, yc)
  +wtc = Fd(3n, m, xc)
  +wc = Fd(2n, m, wtc)
  -A = MC.Kc(b, c, pg, out, outn, n1, ks, img, K, H)
  +s4 = ST(b, rc, xc, ov, oi, t1, t2, pg, out, outn)
  +s5 = ST(b, rc, wtc, ov, oi, t1, t2, pg, out, outn)
  -K1 = {t => Wp(C.Cir.exec(1n+f, C.Cir.Stmt.nop{}, t), K, H) : C.Cir.State -> Type}
  Wp.seq(f, OC.D1(), C.M.do([OC.D2()]), s4, K, H,
    Wp.set(f, 46n, C.M.f(3n, C.M.g(C.R.ow())), s4, t => Wp(C.Cir.exec(1n+f, C.M.do([OC.D2()]), t), K, H), H, wtc,
      ev.f(3n, C.M.g(C.R.ow()), s4, xc, {==}, ok.isc(Pr(n1), m, ks, img, xc, St.im(b), St.fs(b), St.nx(b), ok.L(n1, m, ks, img, bc, St.im(b), St.fs(b), St.nx(b), hok1, ePb))),
      Wp.seq(f, OC.D2(), C.Cir.Stmt.nop{}, s5, K, H,
        Wp.need(f, C.M.pair(C.R.ow()), C.M.need(C.M.last(C.R.ow()), OC.E()), s5, K1, H, Pm(m, wtc), ev.pair(46n, s5, wtc, {==}, ok.isc(Pr(Pr(n1)), m, ks, img, wtc, St.im(b), St.fs(b), St.nx(b), ok.R(Pr(n1), m, ks, img, xc, St.im(b), St.fs(b), St.nx(b), ok.L(n1, m, ks, img, bc, St.im(b), St.fs(b), St.nx(b), hok1, ePb), ePx))),
         CasesK(Pm(m, wtc), A, kk, Wp(C.Cir.exec(1n+f, C.M.need(C.M.last(C.R.ow()), OC.E()), s5), K1, H), H(2, s5),
          kk => +ePw =>
            Wp.need(f, C.M.last(C.R.ow()), OC.E(), s5, K1, H, LAST(m, wtc), ev.islab(3n, 46n, 0, s5, wtc, {==}, ok.isc(Pr(Pr(n1)), m, ks, img, wtc, St.im(b), St.fs(b), St.nx(b), ok.R(Pr(n1), m, ks, img, xc, St.im(b), St.fs(b), St.nx(b), ok.L(n1, m, ks, img, bc, St.im(b), St.fs(b), St.nx(b), hok1, ePb), ePx)), ok.isc(Pr(Pr(Pr(n1))), m, ks, img, Fd(3n, m, wtc), St.im(b), St.fs(b), St.nx(b), ok.R(Pr(Pr(n1)), m, ks, img, wtc, St.im(b), St.fs(b), St.nx(b), ok.R(Pr(n1), m, ks, img, xc, St.im(b), St.fs(b), St.nx(b), ok.L(n1, m, ks, img, bc, St.im(b), St.fs(b), St.nx(b), hok1, ePb), ePx), ePw))),
             CasesK(LAST(m, wtc), A, kk, Wp(C.Cir.exec(1n+f, OC.E(), s5), K1, H), H(2, s5),
              kk => +eLw =>
                MC.E(f, hF, b, c, ov, oi, t1, t2, pg, out, outn, n1, ks, img, K1, H, hok1, ePb, ePy, eLy, ePx, eIx, ePw, eLw, kk),
              kk => +eLw =>
                kk(SR.done{None{}}, Sc.n7(m, bc, zeros(32n), ePb, ePy, eLy, ePx, eIx, ePw, eLw), {==}, s5))),
          kk => +ePw =>
            kk(SR.done{None{}}, Sc.n6(m, bc, zeros(32n), ePb, ePy, eLy, ePx, eIx, ePw), {==}, s5))))))

# the first field of the list cell's Con
def MC.C(+f: Nat, +hF: PN.Le(33n, 1n+f), +b: C.Cir.State, +c: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32, +pg: U32,
  +out: List<&2, U32>, +outn: U32, +n1: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  -K: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type,
  +hok1: {ok(n1, St.cl(b), ks, img, Fd(3n, St.cl(b), c), St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  +ePb: {Pm(St.cl(b), Fd(3n, St.cl(b), c)) == True{} : Bool},
  +ePy: {Pm(St.cl(b), Fd(3n, St.cl(b), Fd(3n, St.cl(b), c))) == True{} : Bool},
  +eLy: {LAST(St.cl(b), Fd(3n, St.cl(b), Fd(3n, St.cl(b), c))) == True{} : Bool},
  kk: MC.Kc(b, c, pg, out, outn, n1, ks, img, K, H)) ->
  Wp(C.Cir.exec(1n+f, OC.C(), ST(b, Fd(3n, St.cl(b), Fd(3n, St.cl(b), c)), Fd(2n, St.cl(b), Fd(3n, St.cl(b), c)), ov, oi, t1, t2, pg, out, outn)), K, H):
  +m = St.cl(b)
  +bc = Fd(3n, m, c)
  +xc = Fd(2n, m, bc)
  +yc = Fd(3n, m, bc)
  +rc = Fd(2n, m, yc)
  +wtc = Fd(3n, m, xc)
  +wc = Fd(2n, m, wtc)
  -A = MC.Kc(b, c, pg, out, outn, n1, ks, img, K, H)
  +s3 = ST(b, yc, xc, ov, oi, t1, t2, pg, out, outn)
  +s4 = ST(b, rc, xc, ov, oi, t1, t2, pg, out, outn)
  -K1 = {t => Wp(C.Cir.exec(1n+f, C.Cir.Stmt.nop{}, t), K, H) : C.Cir.State -> Type}
  Wp.seq(f, OC.C1(), C.M.do([OC.C2()]), s3, K, H,
    Wp.set(f, 45n, C.M.f(2n, C.M.g(C.R.oc())), s3, t => Wp(C.Cir.exec(1n+f, C.M.do([OC.C2()]), t), K, H), H, rc,
      ev.f(2n, C.M.g(C.R.oc()), s3, yc, {==}, ok.isc(Pr(n1), m, ks, img, yc, St.im(b), St.fs(b), St.nx(b), ok.R(n1, m, ks, img, bc, St.im(b), St.fs(b), St.nx(b), hok1, ePb))),
      Wp.seq(f, OC.C2(), C.Cir.Stmt.nop{}, s4, K, H,
        Wp.need(f, C.M.pair(C.R.ow()), C.M.need(C.M.is_lab(C.M.f(2n, C.M.g(C.R.ow())), C.N.u32()), OC.D()), s4, K1, H, Pm(m, xc),
          ev.pair(46n, s4, xc, {==}, ok.isc(Pr(n1), m, ks, img, xc, St.im(b), St.fs(b), St.nx(b), ok.L(n1, m, ks, img, bc, St.im(b), St.fs(b), St.nx(b), hok1, ePb))),
         CasesK(Pm(m, xc), A, kk, Wp(C.Cir.exec(1n+f, C.M.need(C.M.is_lab(C.M.f(2n, C.M.g(C.R.ow())), C.N.u32()), OC.D()), s4), K1, H), H(2, s4),
          kk => +ePx =>
            Wp.need(f, C.M.is_lab(C.M.f(2n, C.M.g(C.R.ow())), C.N.u32()), OC.D(), s4, K1, H, ISLAB(m, xc, 3),
              ev.islab(2n, 46n, 3, s4, xc, {==}, ok.isc(Pr(n1), m, ks, img, xc, St.im(b), St.fs(b), St.nx(b), ok.L(n1, m, ks, img, bc, St.im(b), St.fs(b), St.nx(b), hok1, ePb)), ok.isc(Pr(Pr(n1)), m, ks, img, Fd(2n, m, xc), St.im(b), St.fs(b), St.nx(b), ok.L(Pr(n1), m, ks, img, xc, St.im(b), St.fs(b), St.nx(b), ok.L(n1, m, ks, img, bc, St.im(b), St.fs(b), St.nx(b), hok1, ePb), ePx))),
             CasesK(ISLAB(m, xc, 3), A, kk, Wp(C.Cir.exec(1n+f, OC.D(), s4), K1, H), H(2, s4),
              kk => +eIx =>
                MC.D(f, hF, b, c, ov, oi, t1, t2, pg, out, outn, n1, ks, img, K1, H, hok1, ePb, ePy, eLy, ePx, eIx, kk),
              kk => +eIx =>
                kk(SR.done{None{}}, Sc.n5(m, bc, zeros(32n), ePb, ePy, eLy, ePx, eIx), {==}, s4))),
          kk => +ePx =>
            kk(SR.done{None{}}, Sc.n4(m, bc, zeros(32n), ePb, ePy, eLy, ePx), {==}, s4))))))

# M.out.con on the cell c in oc, a list's Con: its byte goes out, and oc
# gets the rest of the list; or the run ends with no result
def MCon(+f: Nat, +hF: PN.Le(33n, 1n+f), +b: C.Cir.State, +c: U32, +ow: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32, +pg: U32,
  +out: List<&2, U32>, +outn: U32, +n1: Nat, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  -K: C.Cir.State -> Type, -H: U32 -> C.Cir.State -> Type,
  +hc: {True{} == C.Cir.is_cell(c, St.im(b), St.fs(b), St.nx(b)) : Bool},
  +hok1: {ok(n1, St.cl(b), ks, img, Fd(3n, St.cl(b), c), St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  kk: MC.Kc(b, c, pg, out, outn, n1, ks, img, K, H)) ->
  Wp(C.Cir.exec(1n+f, C.M.out.con(), ST(b, c, ow, ov, oi, t1, t2, pg, out, outn)), K, H):
  +m = St.cl(b)
  +bc = Fd(3n, m, c)
  +xc = Fd(2n, m, bc)
  +yc = Fd(3n, m, bc)
  +rc = Fd(2n, m, yc)
  +wtc = Fd(3n, m, xc)
  +wc = Fd(2n, m, wtc)
  -A = MC.Kc(b, c, pg, out, outn, n1, ks, img, K, H)
  +s0 = ST(b, c, ow, ov, oi, t1, t2, pg, out, outn)
  +s1 = ST(b, bc, ow, ov, oi, t1, t2, pg, out, outn)
  +s2 = ST(b, bc, xc, ov, oi, t1, t2, pg, out, outn)
  +s3 = ST(b, yc, xc, ov, oi, t1, t2, pg, out, outn)
  +hcb = ok.isc(n1, m, ks, img, bc, St.im(b), St.fs(b), St.nx(b), hok1)
  -K1 = {t => Wp(C.Cir.exec(1n+f, C.Cir.Stmt.nop{}, t), K, H) : C.Cir.State -> Type}
  -K2 = {t => Wp(C.Cir.exec(1n+f, C.Cir.Stmt.nop{}, t), K1, H) : C.Cir.State -> Type}
  Wp.seq(f, OC.A1(), C.M.do([C.M.need(C.M.pair(C.R.oc()), OC.B())]), s0, K, H,
    Wp.set(f, 45n, C.M.f(3n, C.M.g(C.R.oc())), s0, t => Wp(C.Cir.exec(1n+f, C.M.do([C.M.need(C.M.pair(C.R.oc()), OC.B())]), t), K, H), H, bc,
      ev.f(3n, C.M.g(C.R.oc()), s0, c, {==}, hc),
      Wp.seq(f, C.M.need(C.M.pair(C.R.oc()), OC.B()), C.Cir.Stmt.nop{}, s1, K, H,
        Wp.need(f, C.M.pair(C.R.oc()), OC.B(), s1, K1, H, Pm(m, bc), ev.pair(45n, s1, bc, {==}, hcb),
         CasesK(Pm(m, bc), A, kk, Wp(C.Cir.exec(1n+f, OC.B(), s1), K1, H), H(2, s1),
          kk => +ePb =>
            Wp.seq(f, OC.B1(), C.M.do([OC.B2(), OC.B3()]), s1, K1, H,
              Wp.set(f, 46n, C.M.f(2n, C.M.g(C.R.oc())), s1, t => Wp(C.Cir.exec(1n+f, C.M.do([OC.B2(), OC.B3()]), t), K1, H), H, xc,
                ev.f(2n, C.M.g(C.R.oc()), s1, bc, {==}, hcb),
                Wp.seq(f, OC.B2(), C.M.do([OC.B3()]), s2, K1, H,
                  Wp.set(f, 45n, C.M.f(3n, C.M.g(C.R.oc())), s2, t => Wp(C.Cir.exec(1n+f, C.M.do([OC.B3()]), t), K1, H), H, yc,
                    ev.f(3n, C.M.g(C.R.oc()), s2, bc, {==}, hcb),
                    Wp.seq(f, OC.B3(), C.Cir.Stmt.nop{}, s3, K1, H,
                      Wp.need(f, C.M.pair(C.R.oc()), C.M.need(C.M.last(C.R.oc()), OC.C()), s3, K2, H, Pm(m, yc), ev.pair(45n, s3, yc, {==}, ok.isc(Pr(n1), m, ks, img, yc, St.im(b), St.fs(b), St.nx(b), ok.R(n1, m, ks, img, bc, St.im(b), St.fs(b), St.nx(b), hok1, ePb))),
                       CasesK(Pm(m, yc), A, kk, Wp(C.Cir.exec(1n+f, C.M.need(C.M.last(C.R.oc()), OC.C()), s3), K2, H), H(2, s3),
                        kk => +ePy =>
                          Wp.need(f, C.M.last(C.R.oc()), OC.C(), s3, K2, H, LAST(m, yc), ev.islab(3n, 45n, 0, s3, yc, {==}, ok.isc(Pr(n1), m, ks, img, yc, St.im(b), St.fs(b), St.nx(b), ok.R(n1, m, ks, img, bc, St.im(b), St.fs(b), St.nx(b), hok1, ePb)), ok.isc(Pr(Pr(n1)), m, ks, img, Fd(3n, m, yc), St.im(b), St.fs(b), St.nx(b), ok.R(Pr(n1), m, ks, img, yc, St.im(b), St.fs(b), St.nx(b), ok.R(n1, m, ks, img, bc, St.im(b), St.fs(b), St.nx(b), hok1, ePb), ePy))),
                           CasesK(LAST(m, yc), A, kk, Wp(C.Cir.exec(1n+f, OC.C(), s3), K2, H), H(2, s3),
                            kk => +eLy =>
                              MC.C(f, hF, b, c, ov, oi, t1, t2, pg, out, outn, n1, ks, img, K2, H, hok1, ePb, ePy, eLy, kk),
                            kk => +eLy =>
                              kk(SR.done{None{}}, Sc.n3(m, bc, zeros(32n), ePb, ePy, eLy), {==}, s3))),
                        kk => +ePy =>
                          kk(SR.done{None{}}, Sc.n2(m, bc, zeros(32n), ePb, ePy), {==}, s3)))))))),
          kk => +ePb =>
            kk(SR.done{None{}}, Sc.n1(m, bc, zeros(32n), ePb), {==}, s1))))))

# The list
# --------

# the steps of Step at a list cell: its end, its Con, or none when a test fails
def StN.ok(+m: C.Cir.Cells, +c: U32,
  +eP: {Pm(m, c) == True{} : Bool},
  +eM: {Lm(m, Fd(2n, m, c)) == True{} : Bool},
  +eN: {U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 1) == True{} : Bool},
  +eL: {LAST(m, c) == True{} : Bool}) ->
  {Step(m, c) == SR.done{Some{Nil{}}} : SR}:
  +x22 = Fd(2n, m, Fd(2n, m, c))
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {S.p(_, m, c) == SR.done{Some{Nil{}}} : SR}
  %Equal.sym(Bool, Lm(m, Fd(2n, m, c)), True{}, eM) : {S.l(_, m, c) == SR.done{Some{Nil{}}} : SR}
  %Equal.sym(Bool, U32.is_eq(x22, 1), True{}, eN) : {S.w(_, U32.is_eq(x22, 2), m, c) == SR.done{Some{Nil{}}} : SR}
  %Equal.sym(Bool, LAST(m, c), True{}, eL) : {S.nil(_) == SR.done{Some{Nil{}}} : SR}
  {==}

def StN.n1(+m: C.Cir.Cells, +c: U32,
  +eP: {Pm(m, c) == False{} : Bool}) ->
  {Step(m, c) == SR.done{None{}} : SR}:
  +x22 = Fd(2n, m, Fd(2n, m, c))
  Equal.cong(Bool, SR, yy => S.p(yy, m, c), Pm(m, c), False{}, eP)

def StN.n2(+m: C.Cir.Cells, +c: U32,
  +eP: {Pm(m, c) == True{} : Bool},
  +eM: {Lm(m, Fd(2n, m, c)) == False{} : Bool}) ->
  {Step(m, c) == SR.done{None{}} : SR}:
  +x22 = Fd(2n, m, Fd(2n, m, c))
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {S.p(_, m, c) == SR.done{None{}} : SR}
  Equal.cong(Bool, SR, yy => S.l(yy, m, c), Lm(m, Fd(2n, m, c)), False{}, eM)

def StN.n4(+m: C.Cir.Cells, +c: U32,
  +eP: {Pm(m, c) == True{} : Bool},
  +eM: {Lm(m, Fd(2n, m, c)) == True{} : Bool},
  +eN: {U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 1) == True{} : Bool},
  +eL: {LAST(m, c) == False{} : Bool}) ->
  {Step(m, c) == SR.done{None{}} : SR}:
  +x22 = Fd(2n, m, Fd(2n, m, c))
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {S.p(_, m, c) == SR.done{None{}} : SR}
  %Equal.sym(Bool, Lm(m, Fd(2n, m, c)), True{}, eM) : {S.l(_, m, c) == SR.done{None{}} : SR}
  %Equal.sym(Bool, U32.is_eq(x22, 1), True{}, eN) : {S.w(_, U32.is_eq(x22, 2), m, c) == SR.done{None{}} : SR}
  Equal.cong(Bool, SR, yy => S.nil(yy), LAST(m, c), False{}, eL)

def StC.ok(+m: C.Cir.Cells, +c: U32,
  +eP: {Pm(m, c) == True{} : Bool},
  +eM: {Lm(m, Fd(2n, m, c)) == True{} : Bool},
  +eN: {U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 1) == False{} : Bool},
  +eC: {U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 2) == True{} : Bool}) ->
  {Step(m, c) == S.c0(Pm(m, Fd(3n, m, c)), m, Fd(3n, m, c)) : SR}:
  +x22 = Fd(2n, m, Fd(2n, m, c))
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {S.p(_, m, c) == S.c0(Pm(m, Fd(3n, m, c)), m, Fd(3n, m, c)) : SR}
  %Equal.sym(Bool, Lm(m, Fd(2n, m, c)), True{}, eM) : {S.l(_, m, c) == S.c0(Pm(m, Fd(3n, m, c)), m, Fd(3n, m, c)) : SR}
  %Equal.sym(Bool, U32.is_eq(x22, 1), False{}, eN) : {S.w(_, U32.is_eq(x22, 2), m, c) == S.c0(Pm(m, Fd(3n, m, c)), m, Fd(3n, m, c)) : SR}
  %Equal.sym(Bool, U32.is_eq(x22, 2), True{}, eC) : {S.k2(_, m, Fd(3n, m, c)) == S.c0(Pm(m, Fd(3n, m, c)), m, Fd(3n, m, c)) : SR}
  {==}

def StC.n4(+m: C.Cir.Cells, +c: U32,
  +eP: {Pm(m, c) == True{} : Bool},
  +eM: {Lm(m, Fd(2n, m, c)) == True{} : Bool},
  +eN: {U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 1) == False{} : Bool},
  +eC: {U32.is_eq(Fd(2n, m, Fd(2n, m, c)), 2) == False{} : Bool}) ->
  {Step(m, c) == SR.done{None{}} : SR}:
  +x22 = Fd(2n, m, Fd(2n, m, c))
  %Equal.sym(Bool, Pm(m, c), True{}, eP) : {S.p(_, m, c) == SR.done{None{}} : SR}
  %Equal.sym(Bool, Lm(m, Fd(2n, m, c)), True{}, eM) : {S.l(_, m, c) == SR.done{None{}} : SR}
  %Equal.sym(Bool, U32.is_eq(x22, 1), False{}, eN) : {S.w(_, U32.is_eq(x22, 2), m, c) == SR.done{None{}} : SR}
  Equal.cong(Bool, SR, yy => S.k2(yy, m, Fd(3n, m, c)), U32.is_eq(x22, 2), False{}, eC)

# n increments of x, one for each byte of bs
def Incs(bs: List<&2, U32>, x: U32) -> U32:
  match bs:
    case Nil{}:
      x
    case Con{_, t}:
      Incs(t, U32.inc(x))

# a halt of the run of M.out, with the status s and the state st, says what
# r says: the bytes of r out (the last first, before out0) and their number
# added to outn0, with the status 0; the status 2 when r is none
def Fin(r: Maybe<&2, List<&2, U32>>, out0: List<&2, U32>, outn0: U32, s: U32, st: C.Cir.State) -> Type:
  match r:
    case Some{bs}:
      {s == 0 : U32} & ({St.out(st) == List.reverse.go(&2, U32, bs, out0) : List<&2, U32>} & {St.outn(st) == Incs(bs, outn0) : U32})
    case None{}:
      {s == 2 : U32}

def Fin.cons(r: Maybe<&2, List<&2, U32>>, +v: U32, +out: List<&2, U32>, +outn: U32, +s: U32, +st: C.Cir.State,
  h: Fin(r, Con{v, out}, U32.inc(outn), s, st)) -> Fin(U.c12(v, r), out, outn, s, st):
  match r:
    case Some{bs}:
      h
    case None{}:
      h

def Wp.mapH(o: C.Cir.Out, -K: C.Cir.State -> Type, -H1: U32 -> C.Cir.State -> Type, -H2: U32 -> C.Cir.State -> Type,
  f: @s: U32 -> @st: C.Cir.State -> H1(s, st) -> H2(s, st), h: Wp(o, K, H1)) -> Wp(o, K, H2):
  match o:
    case C.Cir.Out.next{st}:
      h
    case C.Cir.Out.halt{s, st}:
      f(s, st, h)
    case C.Cir.Out.out_of_memory{}:
      Unit{}
    case C.Cir.Out.trap{}:
      match h:
    case C.Cir.Out.not_done{}:
      match h:

# CU at the end of a list
def CUd(+a: Nat, +m: C.Cir.Cells, +r: Maybe<&2, List<&2, U32>>) -> {CU(1n+a, m, SR.done{r}) == r : Maybe<&2, List<&2, U32>>}:
  match a:
    case 0n:
      {==}
    case 1n+b:
      match b:
        case 0n:
          {==}
        case 1n+d:
          {==}

# CU at a byte, with the fuel that ok grants the rest
def CUm(+n1: Nat, +m: C.Cir.Cells, +v: U32, +rc: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +im: U32, +fs: U32, +nx: U32,
  +h: {ok(Pr(Pr(n1)), m, ks, img, rc, im, fs, nx) == True{} : Bool}) ->
  {U.c12(v, CU(Pr(Pr(n1)), m, Step(m, rc))) == CU(1n+n1, m, SR.more{v, rc}) : Maybe<&2, List<&2, U32>>}:
  match n1:
    case 0n:
      Empty.absurd({U.c12(v, CU(0n, m, Step(m, rc))) == CU(1n, m, SR.more{v, rc}) : Maybe<&2, List<&2, U32>>}, ok.zero(m, ks, img, rc, im, fs, nx, h))
    case 1n+n2:
      match n2:
        case 0n:
          Empty.absurd({U.c12(v, CU(0n, m, Step(m, rc))) == CU(2n, m, SR.more{v, rc}) : Maybe<&2, List<&2, U32>>}, ok.zero(m, ks, img, rc, im, fs, nx, h))
        case 1n+d:
          {==}

def Fin.none(+n1: Nat, +m: C.Cir.Cells, +c: U32, +out: List<&2, U32>, +outn: U32, +st: C.Cir.State,
  +e: {Step(m, c) == SR.done{None{}} : SR}) -> Fin(CU(1n+n1, m, Step(m, c)), out, outn, 2, st):
  %Equal.sym(SR, Step(m, c), SR.done{None{}}, e) : Fin(CU(1n+n1, m, _), out, outn, 2, st)
  %Equal.sym(Maybe<&2, List<&2, U32>>, CU(1n+n1, m, SR.done{None{}}), None{}, CUd(n1, m, None{})) : Fin(_, out, outn, 2, st)
  {==}

def Fin.nil(+n1: Nat, +b: C.Cir.State, +c: U32, +ow: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32, +pg: U32, +out: List<&2, U32>, +outn: U32,
  +e: {Step(St.cl(b), c) == SR.done{Some{Nil{}}} : SR}) ->
  Fin(CU(1n+n1, St.cl(b), Step(St.cl(b), c)), out, outn, 0, ST(b, c, ow, ov, oi, t1, t2, pg, out, outn)):
  %Equal.sym(SR, Step(St.cl(b), c), SR.done{Some{Nil{}}}, e) : Fin(CU(1n+n1, St.cl(b), _), out, outn, 0, ST(b, c, ow, ov, oi, t1, t2, pg, out, outn))
  %Equal.sym(Maybe<&2, List<&2, U32>>, CU(1n+n1, St.cl(b), SR.done{Some{Nil{}}}), Some{Nil{}}, CUd(n1, St.cl(b), Some{Nil{}})) :
    Fin(_, out, outn, 0, ST(b, c, ow, ov, oi, t1, t2, pg, out, outn))
  ({==}, ({==}, {==}))

def Fin.step(+n1: Nat, +m: C.Cir.Cells, +c: U32, +v: U32, +rc: U32, +out: List<&2, U32>, +outn: U32,
  +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>, +im: U32, +fs: U32, +nx: U32,
  +e: {Step(m, c) == SR.more{v, rc} : SR}, +hokr: {ok(Pr(Pr(n1)), m, ks, img, rc, im, fs, nx) == True{} : Bool}, +s: U32, +st: C.Cir.State,
  h: Fin(CU(Pr(Pr(n1)), m, Step(m, rc)), Con{v, out}, U32.inc(outn), s, st)) -> Fin(CU(1n+n1, m, Step(m, c)), out, outn, s, st):
  %Equal.sym(SR, Step(m, c), SR.more{v, rc}, e) : Fin(CU(1n+n1, m, _), out, outn, s, st)
  %CUm(n1, m, v, rc, ks, img, im, fs, nx, hokr) : Fin(_, out, outn, s, st)
  Fin.cons(CU(Pr(Pr(n1)), m, Step(m, rc)), v, out, outn, s, st, h)

def le_pr(+n: Nat) -> PN.Le(Pr(n), n):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      PN.le_succ(p, p, PN.le_refl(p))

def le_pr2(+n: Nat) -> PN.Le(Nat.add(Pr(Pr(n)), 34n), Nat.add(n, 34n)):
  PN.add_mono(Pr(Pr(n)), n, 34n, 34n, PN.le_trans(Pr(Pr(n)), Pr(n), n, le_pr(Pr(n)), le_pr(n)), PN.le_refl(34n))

# the loop of M.out and its body
def BO.a() -> C.Cir.Stmt:
  C.M.set(C.R.ow(), C.M.f(2n, C.M.f(2n, C.M.g(C.R.oc()))))

def BO.i() -> C.Cir.Stmt:
  C.M.if(C.M.eq(C.M.g(C.R.ow()), C.M.c(C.N.nil())), C.M.need(C.M.last(C.R.oc()), C.M.halt(0)),
    C.M.need(C.M.eq(C.M.g(C.R.ow()), C.M.c(C.N.con())), C.M.out.con()))

def BO.s1() -> C.Cir.Stmt:
  C.M.need(C.M.eq(C.M.tag(C.M.f(2n, C.M.g(C.R.oc()))), C.M.c(C.T.lab())), C.M.do([BO.a(), BO.i()]))

def BO() -> C.Cir.Stmt:
  C.M.need(C.M.pair(C.R.oc()), BO.s1())

def WO() -> C.Cir.Stmt:
  C.M.while(C.M.c(1), BO())

# the claim of the loop of M.out for the rest of the list, at any cell rc
# that ok grants, with the fuel f2
def LO.IH(+n1: Nat, +b: C.Cir.State, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>) -> Type:
  @rc: U32 -> {ok(Pr(Pr(n1)), St.cl(b), ks, img, rc, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool} ->
    @f2: Nat -> PN.Le(Nat.add(Pr(Pr(n1)), 34n), f2) -> @pg2: U32 -> @ow2: U32 -> @ov2: U32 -> @oi2: U32 -> @t12: U32 -> @t22: U32 ->
    @out2: List<&2, U32> -> @outn2: U32 ->
    Wp(C.Cir.exec(f2, WO(), ST(b, rc, ow2, ov2, oi2, t12, t22, pg2, out2, outn2)), st => Empty,
      s => st => Fin(CU(Pr(Pr(n1)), St.cl(b), Step(St.cl(b), rc)), out2, outn2, s, st))

# the round of a Con: its byte goes out (MCon), then the rest of the list
def LO.con(+n1: Nat, +g: Nat, +hF: PN.Le(Nat.add(n1, 34n), 1n+g), +b: C.Cir.State, +c: U32, +ow: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32,
  +pg: U32, +out: List<&2, U32>, +outn: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +hok: {ok(1n+n1, St.cl(b), ks, img, c, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  +hc: {True{} == C.Cir.is_cell(c, St.im(b), St.fs(b), St.nx(b)) : Bool},
  +eP: {Pm(St.cl(b), c) == True{} : Bool}, +eM: {Lm(St.cl(b), Fd(2n, St.cl(b), c)) == True{} : Bool},
  +eN: {U32.is_eq(Fd(2n, St.cl(b), Fd(2n, St.cl(b), c)), 1) == False{} : Bool},
  +eC: {U32.is_eq(Fd(2n, St.cl(b), Fd(2n, St.cl(b), c)), 2) == True{} : Bool},
  ih: LO.IH(n1, b, ks, img)) ->
  Wp(C.Cir.exec(1n+g, C.M.out.con(), ST(b, c, ow, ov, oi, t1, t2, pg, out, outn)),
    t => Wp(C.Cir.exec(1n+g, C.Cir.Stmt.nop{}, t), u => Wp(C.Cir.exec(1n+g, WO(), u), st => Empty,
      s => st => Fin(CU(1n+n1, St.cl(b), Step(St.cl(b), c)), out, outn, s, st)),
      s => st => Fin(CU(1n+n1, St.cl(b), Step(St.cl(b), c)), out, outn, s, st)),
    s => st => Fin(CU(1n+n1, St.cl(b), Step(St.cl(b), c)), out, outn, s, st)):
  +m = St.cl(b)
  +im = St.im(b)
  +fs = St.fs(b)
  +nx = St.nx(b)
  +bc = Fd(3n, m, c)
  +estep = StC.ok(m, c, eP, eM, eN, eC)
  -K0 = {st => Empty : C.Cir.State -> Type}
  -H0 = {s => st => Fin(CU(1n+n1, m, Step(m, c)), out, outn, s, st) : U32 -> C.Cir.State -> Type}
  -KW = {t => Wp(C.Cir.exec(1n+g, WO(), t), K0, H0) : C.Cir.State -> Type}
  -KB = {t => Wp(C.Cir.exec(1n+g, C.Cir.Stmt.nop{}, t), KW, H0) : C.Cir.State -> Type}
  -IH = LO.IH(n1, b, ks, img)
  MCon(g, PN.weaken(33n, 1n+g, PN.le_trans(34n, Nat.add(n1, 34n), 1n+g, PN.le_add_l(n1, 34n), hF)),
    b, c, ow, ov, oi, t1, t2, pg, out, outn, n1, ks, img, KB, H0, hc, ok.R(1n+n1, m, ks, img, c, im, fs, nx, hok, eP),
    sr => +esr => CasesS(sr, IH, ih,
      v => rest => {ok(Pr(Pr(n1)), m, ks, img, rest, im, fs, nx) == True{} : Bool} ->
        @pg2: U32 -> @ow2: U32 -> @ov2: U32 -> @oi2: U32 -> @t12: U32 -> @t22: U32 -> KB(ST(b, rest, ow2, ov2, oi2, t12, t22, pg2, Con{v, out}, U32.inc(outn))),
      r => {r == None{} : Maybe<&2, List<&2, U32>>} -> @st: C.Cir.State -> H0(2, st),
      ih => +v => +rest => +emv => +hokr => +pg2 => +ow2 => +ov2 => +oi2 => +t12 => +t22 =>
        Wp.mapH(C.Cir.exec(1n+g, WO(), ST(b, rest, ow2, ov2, oi2, t12, t22, pg2, Con{v, out}, U32.inc(outn))), K0,
          s => st => Fin(CU(Pr(Pr(n1)), m, Step(m, rest)), Con{v, out}, U32.inc(outn), s, st), H0,
          s => st => hf => Fin.step(n1, m, c, v, rest, out, outn, ks, img, im, fs, nx,
            Equal.trans(SR, Step(m, c), sr, SR.more{v, rest}, Equal.trans(SR, Step(m, c), S.c0(Pm(m, bc), m, bc), sr, estep, esr), emv),
            hokr, s, st, hf),
          ih(rest, hokr, 1n+g, PN.le_trans(Nat.add(Pr(Pr(n1)), 34n), Nat.add(n1, 34n), 1n+g, le_pr2(n1), hF),
            pg2, ow2, ov2, oi2, t12, t22, Con{v, out}, U32.inc(outn))),
      ih => +r => +ed => +er => st =>
        Fin.none(n1, m, c, out, outn, st,
          Equal.trans(SR, Step(m, c), sr, SR.done{None{}}, Equal.trans(SR, Step(m, c), S.c0(Pm(m, bc), m, bc), sr, estep, esr),
            Equal.trans(SR, sr, SR.done{r}, SR.done{None{}}, ed, Equal.cong(Maybe<&2, List<&2, U32>>, SR, x => SR.done{x}, r, None{}, er))))))

# a round of the loop of M.out at the list cell c, then, by ih, the rest
def LO.run(+n1: Nat, +g: Nat, +hF: PN.Le(Nat.add(n1, 34n), 1n+g), +b: C.Cir.State, +c: U32, +ow: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32,
  +pg: U32, +out: List<&2, U32>, +outn: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +hok: {ok(1n+n1, St.cl(b), ks, img, c, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  ih: LO.IH(n1, b, ks, img)) ->
  Wp(C.Cir.exec(1n+1n+g, WO(), ST(b, c, ow, ov, oi, t1, t2, pg, out, outn)), st => Empty,
    s => st => Fin(CU(1n+n1, St.cl(b), Step(St.cl(b), c)), out, outn, s, st)):
  +m = St.cl(b)
  +im = St.im(b)
  +fs = St.fs(b)
  +nx = St.nx(b)
  +x22 = Fd(2n, m, Fd(2n, m, c))
  +s0 = ST(b, c, ow, ov, oi, t1, t2, pg, out, outn)
  +s1 = ST(b, c, x22, ov, oi, t1, t2, pg, out, outn)
  +hc = ok.isc(1n+n1, m, ks, img, c, im, fs, nx, hok)
  -K0 = {st => Empty : C.Cir.State -> Type}
  -H0 = {s => st => Fin(CU(1n+n1, m, Step(m, c)), out, outn, s, st) : U32 -> C.Cir.State -> Type}
  -KW = {t => Wp(C.Cir.exec(1n+g, WO(), t), K0, H0) : C.Cir.State -> Type}
  -KB = {t => Wp(C.Cir.exec(1n+g, C.Cir.Stmt.nop{}, t), KW, H0) : C.Cir.State -> Type}
  -IH = LO.IH(n1, b, ks, img)
  Wp.while(1n+g, C.M.c(1), BO(), s0, K0, H0, True{}, {==},
    Wp.then(C.Cir.exec(1n+g, BO(), s0), t => C.Cir.exec(1n+g, WO(), t), K0, H0,
      Wp.need(g, C.M.pair(C.R.oc()), BO.s1(), s0, KW, H0, Pm(m, c), ev.pair(45n, s0, c, {==}, hc),
       CasesK(Pm(m, c), IH, ih, Wp(C.Cir.exec(1n+g, BO.s1(), s0), KW, H0), H0(2, s0),
        ih => +eP =>
          Wp.need(g, C.M.eq(C.M.tag(C.M.f(2n, C.M.g(C.R.oc()))), C.M.c(C.T.lab())), C.M.do([BO.a(), BO.i()]), s0, KW, H0, Lm(m, Fd(2n, m, c)),
            ev.tag(2n, 45n, s0, c, {==}, hc, ok.isc(n1, m, ks, img, Fd(2n, m, c), im, fs, nx, ok.L(1n+n1, m, ks, img, c, im, fs, nx, hok, eP))),
           CasesK(Lm(m, Fd(2n, m, c)), IH, ih, Wp(C.Cir.exec(1n+g, C.M.do([BO.a(), BO.i()]), s0), KW, H0), H0(2, s0),
            ih => +eM =>
              Wp.seq(g, BO.a(), C.M.do([BO.i()]), s0, KW, H0,
                Wp.set(g, 46n, C.M.f(2n, C.M.f(2n, C.M.g(C.R.oc()))), s0, t => Wp(C.Cir.exec(1n+g, C.M.do([BO.i()]), t), KW, H0), H0, x22,
                  ev.ff(2n, 2n, 45n, s0, c, {==}, hc, ok.isc(n1, m, ks, img, Fd(2n, m, c), im, fs, nx, ok.L(1n+n1, m, ks, img, c, im, fs, nx, hok, eP))),
                  Wp.seq(g, BO.i(), C.Cir.Stmt.nop{}, s1, KW, H0,
                    Wp.if(g, C.M.eq(C.M.g(C.R.ow()), C.M.c(C.N.nil())), C.M.need(C.M.last(C.R.oc()), C.M.halt(0)),
                      C.M.need(C.M.eq(C.M.g(C.R.ow()), C.M.c(C.N.con())), C.M.out.con()), s1, KB, H0, U32.is_eq(x22, 1), {==},
                     CasesK(U32.is_eq(x22, 1), IH, ih, Wp(C.Cir.exec(1n+g, C.M.need(C.M.last(C.R.oc()), C.M.halt(0)), s1), KB, H0),
                      Wp(C.Cir.exec(1n+g, C.M.need(C.M.eq(C.M.g(C.R.ow()), C.M.c(C.N.con())), C.M.out.con()), s1), KB, H0),
                      ih => +eN =>
                        Wp.need(g, C.M.last(C.R.oc()), C.M.halt(0), s1, KB, H0, LAST(m, c),
                          ev.islab(3n, 45n, 0, s1, c, {==}, hc, ok.isc(n1, m, ks, img, Fd(3n, m, c), im, fs, nx, ok.R(1n+n1, m, ks, img, c, im, fs, nx, hok, eP))),
                         CasesK(LAST(m, c), IH, ih, Wp(C.Cir.exec(1n+g, C.M.halt(0), s1), KB, H0), H0(2, s1),
                          ih => +eL =>
                            Fin.nil(n1, b, c, x22, ov, oi, t1, t2, pg, out, outn, StN.ok(m, c, eP, eM, eN, eL)),
                          ih => +eL =>
                            Fin.none(n1, m, c, out, outn, s1, StN.n4(m, c, eP, eM, eN, eL)))),
                      ih => +eN =>
                        Wp.need(g, C.M.eq(C.M.g(C.R.ow()), C.M.c(C.N.con())), C.M.out.con(), s1, KB, H0, U32.is_eq(x22, 2), {==},
                         CasesK(U32.is_eq(x22, 2), IH, ih, Wp(C.Cir.exec(1n+g, C.M.out.con(), s1), KB, H0), H0(2, s1),
                          ih => +eC =>
                            LO.con(n1, g, hF, b, c, x22, ov, oi, t1, t2, pg, out, outn, ks, img, hok, hc, eP, eM, eN, eC, ih),
                          ih => +eC =>
                            Fin.none(n1, m, c, out, outn, s1, StC.n4(m, c, eP, eM, eN, eC))))))))),
            ih => +eM =>
              Fin.none(n1, m, c, out, outn, s0, StN.n2(m, c, eP, eM)))),
        ih => +eP =>
          Fin.none(n1, m, c, out, outn, s0, StN.n1(m, c, eP))))))

# the loop of M.out from the list cell c, with fuel F
def LO.body(+n1: Nat, +F: Nat, +hF: PN.Le(Nat.add(1n+n1, 34n), F), +b: C.Cir.State, +c: U32, +ow: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32,
  +pg: U32, +out: List<&2, U32>, +outn: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +hok: {ok(1n+n1, St.cl(b), ks, img, c, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool},
  ih: LO.IH(n1, b, ks, img)) ->
  Wp(C.Cir.exec(F, WO(), ST(b, c, ow, ov, oi, t1, t2, pg, out, outn)), st => Empty, s => st => Fin(CU(1n+n1, St.cl(b), Step(St.cl(b), c)), out, outn, s, st)):
  match F:
    case 0n:
      Empty.absurd(Wp(C.Cir.exec(0n, WO(), ST(b, c, ow, ov, oi, t1, t2, pg, out, outn)), st => Empty, s => st => Fin(CU(1n+n1, St.cl(b), Step(St.cl(b), c)), out, outn, s, st)), hF)
    case 1n+f:
      match f:
        case 0n:
          Empty.absurd(Wp(C.Cir.exec(1n, WO(), ST(b, c, ow, ov, oi, t1, t2, pg, out, outn)), st => Empty, s => st => Fin(CU(1n+n1, St.cl(b), Step(St.cl(b), c)), out, outn, s, st)), PN.le_trans(34n, Nat.add(n1, 34n), 0n, PN.le_add_l(n1, 34n), hF))
        case 1n+g:
          LO.run(n1, g, hF, b, c, ow, ov, oi, t1, t2, pg, out, outn, ks, img, hok, ih)

# the loop of M.out from the list cell c: the run halts as CU says, or runs
# out of memory
def LO(+n: Nat, +F: Nat, +hF: PN.Le(Nat.add(n, 34n), F), +b: C.Cir.State, +c: U32, +ow: U32, +ov: U32, +oi: U32, +t1: U32, +t2: U32,
  +pg: U32, +out: List<&2, U32>, +outn: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +hok: {ok(n, St.cl(b), ks, img, c, St.im(b), St.fs(b), St.nx(b)) == True{} : Bool}) ->
  Wp(C.Cir.exec(F, WO(), ST(b, c, ow, ov, oi, t1, t2, pg, out, outn)), st => Empty, s => st => Fin(CU(n, St.cl(b), Step(St.cl(b), c)), out, outn, s, st)):
  match n:
    case 0n:
      Empty.absurd(Wp(C.Cir.exec(F, WO(), ST(b, c, ow, ov, oi, t1, t2, pg, out, outn)), st => Empty, s => st => Fin(CU(0n, St.cl(b), Step(St.cl(b), c)), out, outn, s, st)), ok.zero(St.cl(b), ks, img, c, St.im(b), St.fs(b), St.nx(b), hok))
    case 1n+n1:
      match n1:
        case 0n:
          LO.body(0n, F, hF, b, c, ow, ov, oi, t1, t2, pg, out, outn, ks, img, hok,
            rc => +hokr => +f2 => +hF2 => +pg2 => +ow2 => +ov2 => +oi2 => +t12 => +t22 => +out2 => +outn2 =>
            Empty.absurd(Wp(C.Cir.exec(f2, WO(), ST(b, rc, ow2, ov2, oi2, t12, t22, pg2, out2, outn2)), st => Empty,
              s => st => Fin(CU(0n, St.cl(b), Step(St.cl(b), rc)), out2, outn2, s, st)), ok.zero(St.cl(b), ks, img, rc, St.im(b), St.fs(b), St.nx(b), hokr)))
        case 1n+n2:
          match n2:
            case 0n:
              LO.body(1n, F, hF, b, c, ow, ov, oi, t1, t2, pg, out, outn, ks, img, hok,
                rc => +hokr => +f2 => +hF2 => +pg2 => +ow2 => +ov2 => +oi2 => +t12 => +t22 => +out2 => +outn2 =>
            Empty.absurd(Wp(C.Cir.exec(f2, WO(), ST(b, rc, ow2, ov2, oi2, t12, t22, pg2, out2, outn2)), st => Empty,
              s => st => Fin(CU(0n, St.cl(b), Step(St.cl(b), rc)), out2, outn2, s, st)), ok.zero(St.cl(b), ks, img, rc, St.im(b), St.fs(b), St.nx(b), hokr)))
            case 1n+n3:
              LO.body(1n+1n+n3, F, hF, b, c, ow, ov, oi, t1, t2, pg, out, outn, ks, img, hok,
                rc => +hokr => +f2 => +hF2 => +pg2 => +ow2 => +ov2 => +oi2 => +t12 => +t22 => +out2 => +outn2 =>
                  LO(n3, f2, hF2, b, rc, ow2, ov2, oi2, t12, t22, pg2, out2, outn2, ks, img, hokr))

# The run of M.out
# ----------------

# register k of xs
def At(+k: Nat, +xs: List<&2, U32>) -> U32:
  Rg.hd(Rg.drop(k, xs))

# M.out from a state whose focus register holds the cell c: the run halts as
# CU says of the list of c, or runs out of memory
def MOUT(+n: Nat, +regs: List<&2, U32>, +m: C.Cir.Cells, +nx: U32, +fs: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, U32>,
  +out: List<&2, U32>, +outn: U32, +c: U32, +ks: List<&2, List<&2, U32>>, +img: List<&2, C.Term>,
  +hreg: {List.get(&2, U32, regs, C.R.focus()) == Some{c} : Maybe<&2, U32>},
  +hlen: {Nat.is_le(C.Mach.regs(), List.length(&2, U32, regs)) == True{} : Bool},
  +hok: {ok(n, m, ks, img, c, im, fs, nx) == True{} : Bool}) ->
  Wp(C.Cir.exec(1n+Nat.add(n, 34n), C.M.out(), C.Cir.State{regs, m, nx, fs, im, pg, lim, inp, out, outn}), st => Empty,
    s => st => Fin(CU(n, m, Step(m, c)), out, outn, s, st)):
  +b = {C.Cir.State{regs, m, nx, fs, im, pg, lim, inp, out, outn} : C.Cir.State}
  +N = Nat.add(n, 34n)
  +esp = Rg.sp_eq(64n, regs, PN.toLe(64n, List.length(&2, U32, regs), hlen))
  +ec = Equal.cong(Maybe<&2, U32>, U32, x => Maybe.default(&2, U32, x, 0), Some{Rg.hd(regs)}, Some{c},
    Equal.trans(Maybe<&2, U32>, Some{Rg.hd(regs)}, List.get(&2, U32, regs, 0n), Some{c},
      Equal.cong(List<&2, U32>, Maybe<&2, U32>, xs => List.get(&2, U32, xs, 0n), Rg.sp(regs), regs, esp), hreg))
  -K0 = {st => Empty : C.Cir.State -> Type}
  -H0 = {s => st => Fin(CU(n, m, Step(m, Rg.hd(regs))), out, outn, s, st) : U32 -> C.Cir.State -> Type}
  %ec : Wp(C.Cir.exec(1n+N, C.M.out(), b), st => Empty, s => st => Fin(CU(n, m, Step(m, _)), out, outn, s, st))
  %esp : Wp(C.Cir.exec(1n+N, C.M.out(), C.Cir.State{_, m, nx, fs, im, pg, lim, inp, out, outn}), K0, H0)
  Wp.seq(N, C.M.set(C.R.oc(), C.M.g(C.R.focus())), C.M.do([WO()]), C.Cir.State{Rg.sp(regs), m, nx, fs, im, pg, lim, inp, out, outn}, K0, H0,
    Wp.set(N, 45n, C.M.g(C.R.focus()), C.Cir.State{Rg.sp(regs), m, nx, fs, im, pg, lim, inp, out, outn},
      t => Wp(C.Cir.exec(1n+N, C.M.do([WO()]), t), K0, H0), H0, Rg.hd(regs), {==},
      Wp.seq(N, WO(), C.Cir.Stmt.nop{}, ST(b, Rg.hd(regs), At(46n, regs), At(47n, regs), At(48n, regs), At(62n, regs), At(63n, regs), pg, out, outn), K0, H0,
        LO(n, 1n+N, PN.le_succ(N, N, PN.le_refl(N)), b, Rg.hd(regs), At(46n, regs), At(47n, regs), At(48n, regs), At(62n, regs), At(63n, regs),
          pg, out, outn, ks, img,
          Tr(U32, x => {ok(n, m, ks, img, x, im, fs, nx) == True{} : Bool}, c, Rg.hd(regs), Equal.sym(U32, Rg.hd(regs), c, ec), hok)))))

# U reads what Program.unbytes reads, for every term
def UE(+t: C.Term) -> {C.Program.unbytes(t) == U(t) : Maybe<&2, List<&2, U32>>}:
  match t:
    case C.Term.Var{_}:
      {==}
    case C.Term.Ref{_}:
      {==}
    case C.Term.Ann{_, _}:
      {==}
    case C.Term.Let{_, _, _}:
      {==}
    case C.Term.Typ{_}:
      {==}
    case C.Term.Min{_, _}:
      {==}
    case C.Term.All{_, _, _}:
      {==}
    case C.Term.Lam{_, _}:
      {==}
    case C.Term.App{_, _, _}:
      {==}
    case C.Term.Sig{_, _, _}:
      {==}
    case C.Term.Tup{+q, +a, +b}:
      match q:
        case C.Quan.Q0{}:
          {==}
        case C.Quan.Q1{}:
          match a:
            case C.Term.Var{_}:
              {==}
            case C.Term.Ref{_}:
              {==}
            case C.Term.Ann{_, _}:
              {==}
            case C.Term.Let{_, _, _}:
              {==}
            case C.Term.Typ{_}:
              {==}
            case C.Term.Min{_, _}:
              {==}
            case C.Term.All{_, _, _}:
              {==}
            case C.Term.Lam{_, _}:
              {==}
            case C.Term.App{_, _, _}:
              {==}
            case C.Term.Sig{_, _, _}:
              {==}
            case C.Term.Tup{_, _, _}:
              {==}
            case C.Term.Prj{_}:
              {==}
            case C.Term.Enu{_}:
              {==}
            case C.Term.Lab{+k}:
              match b:
                case C.Term.Var{_}:
                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                case C.Term.Ref{_}:
                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                case C.Term.Ann{_, _}:
                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                case C.Term.Let{_, _, _}:
                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                case C.Term.Typ{_}:
                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                case C.Term.Min{_, _}:
                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                case C.Term.All{_, _, _}:
                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                case C.Term.Lam{_, _}:
                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                case C.Term.App{_, _, _}:
                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                case C.Term.Sig{_, _, _}:
                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                case C.Term.Tup{+q2, +x, +y}:
                  match q2:
                    case C.Quan.Q0{}:
                      Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                    case C.Quan.Q1{}:
                      match x:
                        case C.Term.Var{_}:
                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                        case C.Term.Ref{_}:
                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                        case C.Term.Ann{_, _}:
                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                        case C.Term.Let{_, _, _}:
                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                        case C.Term.Typ{_}:
                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                        case C.Term.Min{_, _}:
                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                        case C.Term.All{_, _, _}:
                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                        case C.Term.Lam{_, _}:
                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                        case C.Term.App{_, _, _}:
                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                        case C.Term.Sig{_, _, _}:
                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                        case C.Term.Tup{+q3, +x1, +x2}:
                          match q3:
                            case C.Quan.Q0{}:
                              Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                            case C.Quan.Q1{}:
                              match x1:
                                case C.Term.Var{_}:
                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                                case C.Term.Ref{_}:
                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                                case C.Term.Ann{_, _}:
                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                                case C.Term.Let{_, _, _}:
                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                                case C.Term.Typ{_}:
                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                                case C.Term.Min{_, _}:
                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                                case C.Term.All{_, _, _}:
                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                                case C.Term.Lam{_, _}:
                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                                case C.Term.App{_, _, _}:
                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                                case C.Term.Sig{_, _, _}:
                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                                case C.Term.Tup{_, _, _}:
                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                                case C.Term.Prj{_}:
                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                                case C.Term.Enu{_}:
                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                                case C.Term.Lab{+c}:
                                  match x2:
                                    case C.Term.Var{_}:
                                      Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                    case C.Term.Ref{_}:
                                      Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                    case C.Term.Ann{_, _}:
                                      Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                    case C.Term.Let{_, _, _}:
                                      Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                    case C.Term.Typ{_}:
                                      Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                    case C.Term.Min{_, _}:
                                      Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                    case C.Term.All{_, _, _}:
                                      Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                    case C.Term.Lam{_, _}:
                                      Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                    case C.Term.App{_, _, _}:
                                      Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                    case C.Term.Sig{_, _, _}:
                                      Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                    case C.Term.Tup{+q4, +w, +l1}:
                                      match q4:
                                        case C.Quan.Q0{}:
                                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                        case C.Quan.Q1{}:
                                          match l1:
                                            case C.Term.Var{_}:
                                              Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                            case C.Term.Ref{_}:
                                              Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                            case C.Term.Ann{_, _}:
                                              Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                            case C.Term.Let{_, _, _}:
                                              Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                            case C.Term.Typ{_}:
                                              Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                            case C.Term.Min{_, _}:
                                              Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                            case C.Term.All{_, _, _}:
                                              Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                            case C.Term.Lam{_, _}:
                                              Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                            case C.Term.App{_, _, _}:
                                              Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                            case C.Term.Sig{_, _, _}:
                                              Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                            case C.Term.Tup{_, _, _}:
                                              Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                            case C.Term.Prj{_}:
                                              Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                            case C.Term.Enu{_}:
                                              Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                            case C.Term.Lab{+u1}:
                                              match y:
                                                case C.Term.Var{_}:
                                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                case C.Term.Ref{_}:
                                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                case C.Term.Ann{_, _}:
                                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                case C.Term.Let{_, _, _}:
                                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                case C.Term.Typ{_}:
                                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                case C.Term.Min{_, _}:
                                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                case C.Term.All{_, _, _}:
                                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                case C.Term.Lam{_, _}:
                                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                case C.Term.App{_, _, _}:
                                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                case C.Term.Sig{_, _, _}:
                                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                case C.Term.Tup{+q5, +rest, +z}:
                                                  match q5:
                                                    case C.Quan.Q0{}:
                                                      Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                    case C.Quan.Q1{}:
                                                      match z:
                                                        case C.Term.Var{_}:
                                                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                        case C.Term.Ref{_}:
                                                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                        case C.Term.Ann{_, _}:
                                                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                        case C.Term.Let{_, _, _}:
                                                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                        case C.Term.Typ{_}:
                                                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                        case C.Term.Min{_, _}:
                                                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                        case C.Term.All{_, _, _}:
                                                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                        case C.Term.Lam{_, _}:
                                                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                        case C.Term.App{_, _, _}:
                                                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                        case C.Term.Sig{_, _, _}:
                                                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                        case C.Term.Tup{_, _, _}:
                                                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                        case C.Term.Prj{_}:
                                                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                        case C.Term.Enu{_}:
                                                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                        case C.Term.Lab{+u2}:
                                                          LF(k, c, w, u1, rest, u2)
                                                        case C.Term.Mat{_, _, _}:
                                                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                        case C.Term.Efq{}:
                                                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                        case C.Term.Eql{_, _, _}:
                                                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                        case C.Term.Rfl{}:
                                                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                        case C.Term.Rwt{_, _, _}:
                                                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                    case C.Quan.Q2{}:
                                                      Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                case C.Term.Prj{_}:
                                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                case C.Term.Enu{_}:
                                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                case C.Term.Lab{_}:
                                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                case C.Term.Mat{_, _, _}:
                                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                case C.Term.Efq{}:
                                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                case C.Term.Eql{_, _, _}:
                                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                case C.Term.Rfl{}:
                                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                                case C.Term.Rwt{_, _, _}:
                                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                                            case C.Term.Mat{_, _, _}:
                                              Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                            case C.Term.Efq{}:
                                              Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                            case C.Term.Eql{_, _, _}:
                                              Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                            case C.Term.Rfl{}:
                                              Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                            case C.Term.Rwt{_, _, _}:
                                              Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                        case C.Quan.Q2{}:
                                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                    case C.Term.Prj{_}:
                                      Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                    case C.Term.Enu{_}:
                                      Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                    case C.Term.Lab{_}:
                                      Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                    case C.Term.Mat{_, _, _}:
                                      Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                    case C.Term.Efq{}:
                                      Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                    case C.Term.Eql{_, _, _}:
                                      Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                    case C.Term.Rfl{}:
                                      Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                    case C.Term.Rwt{_, _, _}:
                                      Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => Uc6_none(C.Name.is_eq(c, C.Program.name.u32()), x2, rest, {==})))
                                case C.Term.Mat{_, _, _}:
                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                                case C.Term.Efq{}:
                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                                case C.Term.Eql{_, _, _}:
                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                                case C.Term.Rfl{}:
                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                                case C.Term.Rwt{_, _, _}:
                                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                            case C.Quan.Q2{}:
                              Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                        case C.Term.Prj{_}:
                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                        case C.Term.Enu{_}:
                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                        case C.Term.Lab{_}:
                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                        case C.Term.Mat{_, _, _}:
                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                        case C.Term.Efq{}:
                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                        case C.Term.Eql{_, _, _}:
                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                        case C.Term.Rfl{}:
                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                        case C.Term.Rwt{_, _, _}:
                          Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, Uc1_none(x, V1(y), rest => {==}))
                    case C.Quan.Q2{}:
                      Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                case C.Term.Prj{_}:
                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                case C.Term.Enu{_}:
                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                case C.Term.Lab{+u}:
                  LN(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), u)
                case C.Term.Mat{_, _, _}:
                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                case C.Term.Efq{}:
                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                case C.Term.Eql{_, _, _}:
                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                case C.Term.Rfl{}:
                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
                case C.Term.Rwt{_, _, _}:
                  Uk_none(C.Name.is_eq(k, C.Program.name.nil()), C.Name.is_eq(k, C.Program.name.con()), b, {==}, {==})
            case C.Term.Mat{_, _, _}:
              {==}
            case C.Term.Efq{}:
              {==}
            case C.Term.Eql{_, _, _}:
              {==}
            case C.Term.Rfl{}:
              {==}
            case C.Term.Rwt{_, _, _}:
              {==}
        case C.Quan.Q2{}:
          {==}
    case C.Term.Prj{_}:
      {==}
    case C.Term.Enu{_}:
      {==}
    case C.Term.Lab{_}:
      {==}
    case C.Term.Mat{_, _, _}:
      {==}
    case C.Term.Efq{}:
      {==}
    case C.Term.Eql{_, _, _}:
      {==}
    case C.Term.Rfl{}:
      {==}
    case C.Term.Rwt{_, _, _}:
      {==}

# Wd reads what Program.unword reads, for every term
def W0N(A: Bool, +u: List<&2, U32>) ->
  {C.Program.unword.nil(Bool.and(A, C.Name.is_eq(u, C.Program.name.unit()))) == W0.k(A, C.Term.Lab{u}) : Maybe<&2, Word(0n)>}:
  match A:
    case True{}:
      {==}
    case False{}:
      {==}

def W0K_none(A: Bool, -z: C.Term, +h: {None{} == W0.z(VL(z)) : Maybe<&2, Word(0n)>}) -> {None{} == W0.k(A, z) : Maybe<&2, Word(0n)>}:
  match A:
    case True{}:
      h
    case False{}:
      {==}

def W1K_none(+q: Nat, A: Bool, -f: C.Term, +h: {None{} == W1.f(q, V1(f)) : Maybe<&2, Word(1n+q)>}) -> {None{} == W1.k(q, A, f) : Maybe<&2, Word(1n+q)>}:
  match A:
    case True{}:
      h
    case False{}:
      {==}

def W1BU_none(+q: Nat, B: Bool, -x: C.Term, -r: C.Term, +h: {None{} == Ub.x(VL(x)) : Maybe<&2, Bool>}) ->
  {None{} == W1.b(q, Ub.u(B, x), r) : Maybe<&2, Word(1n+q)>}:
  match B:
    case True{}:
      Equal.cong(Maybe<&2, Bool>, Maybe<&2, Word(1n+q)>, mb => W1.b(q, mb, r), None{}, Ub.x(VL(x)), h)
    case False{}:
      {==}

def W1B_none(+q: Nat, mb: Maybe<&2, Bool>, -r: C.Term, h: @bb: Bool -> {None{} == W1.r2(q, bb, V1(r)) : Maybe<&2, Word(1n+q)>}) ->
  {None{} == W1.b(q, mb, r) : Maybe<&2, Word(1n+q)>}:
  match mb:
    case Some{bb}:
      h(bb)
    case None{}:
      {==}

def LW.W(+q: Nat, bb: Bool, mw: Maybe<&2, Word(q)>) -> {C.Program.unword.con(q, True{}, Some{bb}, mw) == W1.w(q, bb, mw) : Maybe<&2, Word(1n+q)>}:
  match mw:
    case Some{y}:
      {==}
    case None{}:
      {==}

def LW.C(C: Bool, +q: Nat, bb: Bool, +w: C.Term) ->
  {C.Program.unword.con(q, C, Some{bb}, C.Program.unword(q, w)) == W1.u(q, bb, C, w) : Maybe<&2, Word(1n+q)>}:
  match C:
    case True{}:
      LW.W(q, bb, C.Program.unword(q, w))
    case False{}:
      {==}

def LW.N(C: Bool, +q: Nat, mw: Maybe<&2, Word(q)>) -> {C.Program.unword.con(q, C, None{}, mw) == None{} : Maybe<&2, Word(1n+q)>}:
  match C:
    case True{}:
      {==}
    case False{}:
      {==}

def LW.M(mb: Maybe<&2, Bool>, +q: Nat, +w: C.Term, +u2: List<&2, U32>) ->
  {C.Program.unword.con(q, C.Name.is_eq(u2, C.Program.name.unit()), mb, C.Program.unword(q, w)) ==
   W1.b(q, mb, C.Term.Tup{C.Quan.Q1{}, w, C.Term.Lab{u2}}) : Maybe<&2, Word(1n+q)>}:
  match mb:
    case None{}:
      LW.N(C.Name.is_eq(u2, C.Program.name.unit()), q, C.Program.unword(q, w))
    case Some{bb}:
      LW.C(C.Name.is_eq(u2, C.Program.name.unit()), q, bb, w)

def LW.B(B: Bool, +q: Nat, +bn: List<&2, U32>, +w: C.Term, +u2: List<&2, U32>) ->
  {C.Program.unword.con(q, Bool.and(B, C.Name.is_eq(u2, C.Program.name.unit())), C.Program.unbit(bn), C.Program.unword(q, w)) ==
   W1.b(q, Ub.u(B, C.Term.Lab{bn}), C.Term.Tup{C.Quan.Q1{}, w, C.Term.Lab{u2}}) : Maybe<&2, Word(1n+q)>}:
  match B:
    case True{}:
      LW.M(C.Program.unbit(bn), q, w, u2)
    case False{}:
      {==}

def LW.A(A: Bool, +q: Nat, +bn: List<&2, U32>, +u1: List<&2, U32>, +w: C.Term, +u2: List<&2, U32>) ->
  {C.Program.unword.con(q, Bool.and(Bool.and(A, C.Name.is_eq(u1, C.Program.name.unit())), C.Name.is_eq(u2, C.Program.name.unit())),
     C.Program.unbit(bn), C.Program.unword(q, w)) ==
   W1.k(q, A, C.Term.Tup{C.Quan.Q1{}, C.Term.Tup{C.Quan.Q1{}, C.Term.Lab{bn}, C.Term.Lab{u1}}, C.Term.Tup{C.Quan.Q1{}, w, C.Term.Lab{u2}}}) : Maybe<&2, Word(1n+q)>}:
  match A:
    case True{}:
      LW.B(C.Name.is_eq(u1, C.Program.name.unit()), q, bn, w, u2)
    case False{}:
      {==}

def WE0(+t: C.Term) -> {C.Program.unword(0n, t) == Wd(0n, t) : Maybe<&2, Word(0n)>}:
  match t:
    case C.Term.Var{_}:
      {==}
    case C.Term.Ref{_}:
      {==}
    case C.Term.Ann{_, _}:
      {==}
    case C.Term.Let{_, _, _}:
      {==}
    case C.Term.Typ{_}:
      {==}
    case C.Term.Min{_, _}:
      {==}
    case C.Term.All{_, _, _}:
      {==}
    case C.Term.Lam{_, _}:
      {==}
    case C.Term.App{_, _, _}:
      {==}
    case C.Term.Sig{_, _, _}:
      {==}
    case C.Term.Tup{+q, +a, +b}:
      match q:
        case C.Quan.Q0{}:
          {==}
        case C.Quan.Q1{}:
          match a:
            case C.Term.Var{_}:
              {==}
            case C.Term.Ref{_}:
              {==}
            case C.Term.Ann{_, _}:
              {==}
            case C.Term.Let{_, _, _}:
              {==}
            case C.Term.Typ{_}:
              {==}
            case C.Term.Min{_, _}:
              {==}
            case C.Term.All{_, _, _}:
              {==}
            case C.Term.Lam{_, _}:
              {==}
            case C.Term.App{_, _, _}:
              {==}
            case C.Term.Sig{_, _, _}:
              {==}
            case C.Term.Tup{_, _, _}:
              {==}
            case C.Term.Prj{_}:
              {==}
            case C.Term.Enu{_}:
              {==}
            case C.Term.Lab{+k}:
              match b:
                case C.Term.Var{_}:
                  W0K_none(C.Name.is_eq(k, C.Program.name.wnil()), b, {==})
                case C.Term.Ref{_}:
                  W0K_none(C.Name.is_eq(k, C.Program.name.wnil()), b, {==})
                case C.Term.Ann{_, _}:
                  W0K_none(C.Name.is_eq(k, C.Program.name.wnil()), b, {==})
                case C.Term.Let{_, _, _}:
                  W0K_none(C.Name.is_eq(k, C.Program.name.wnil()), b, {==})
                case C.Term.Typ{_}:
                  W0K_none(C.Name.is_eq(k, C.Program.name.wnil()), b, {==})
                case C.Term.Min{_, _}:
                  W0K_none(C.Name.is_eq(k, C.Program.name.wnil()), b, {==})
                case C.Term.All{_, _, _}:
                  W0K_none(C.Name.is_eq(k, C.Program.name.wnil()), b, {==})
                case C.Term.Lam{_, _}:
                  W0K_none(C.Name.is_eq(k, C.Program.name.wnil()), b, {==})
                case C.Term.App{_, _, _}:
                  W0K_none(C.Name.is_eq(k, C.Program.name.wnil()), b, {==})
                case C.Term.Sig{_, _, _}:
                  W0K_none(C.Name.is_eq(k, C.Program.name.wnil()), b, {==})
                case C.Term.Tup{_, _, _}:
                  W0K_none(C.Name.is_eq(k, C.Program.name.wnil()), b, {==})
                case C.Term.Prj{_}:
                  W0K_none(C.Name.is_eq(k, C.Program.name.wnil()), b, {==})
                case C.Term.Enu{_}:
                  W0K_none(C.Name.is_eq(k, C.Program.name.wnil()), b, {==})
                case C.Term.Lab{+u}:
                  W0N(C.Name.is_eq(k, C.Program.name.wnil()), u)
                case C.Term.Mat{_, _, _}:
                  W0K_none(C.Name.is_eq(k, C.Program.name.wnil()), b, {==})
                case C.Term.Efq{}:
                  W0K_none(C.Name.is_eq(k, C.Program.name.wnil()), b, {==})
                case C.Term.Eql{_, _, _}:
                  W0K_none(C.Name.is_eq(k, C.Program.name.wnil()), b, {==})
                case C.Term.Rfl{}:
                  W0K_none(C.Name.is_eq(k, C.Program.name.wnil()), b, {==})
                case C.Term.Rwt{_, _, _}:
                  W0K_none(C.Name.is_eq(k, C.Program.name.wnil()), b, {==})
            case C.Term.Mat{_, _, _}:
              {==}
            case C.Term.Efq{}:
              {==}
            case C.Term.Eql{_, _, _}:
              {==}
            case C.Term.Rfl{}:
              {==}
            case C.Term.Rwt{_, _, _}:
              {==}
        case C.Quan.Q2{}:
          {==}
    case C.Term.Prj{_}:
      {==}
    case C.Term.Enu{_}:
      {==}
    case C.Term.Lab{_}:
      {==}
    case C.Term.Mat{_, _, _}:
      {==}
    case C.Term.Efq{}:
      {==}
    case C.Term.Eql{_, _, _}:
      {==}
    case C.Term.Rfl{}:
      {==}
    case C.Term.Rwt{_, _, _}:
      {==}

def WE1(+q: Nat, +t: C.Term) -> {C.Program.unword(1n+q, t) == Wd(1n+q, t) : Maybe<&2, Word(1n+q)>}:
  match t:
    case C.Term.Var{_}:
      {==}
    case C.Term.Ref{_}:
      {==}
    case C.Term.Ann{_, _}:
      {==}
    case C.Term.Let{_, _, _}:
      {==}
    case C.Term.Typ{_}:
      {==}
    case C.Term.Min{_, _}:
      {==}
    case C.Term.All{_, _, _}:
      {==}
    case C.Term.Lam{_, _}:
      {==}
    case C.Term.App{_, _, _}:
      {==}
    case C.Term.Sig{_, _, _}:
      {==}
    case C.Term.Tup{+qq, +a, +f}:
      match qq:
        case C.Quan.Q0{}:
          {==}
        case C.Quan.Q1{}:
          match a:
            case C.Term.Var{_}:
              {==}
            case C.Term.Ref{_}:
              {==}
            case C.Term.Ann{_, _}:
              {==}
            case C.Term.Let{_, _, _}:
              {==}
            case C.Term.Typ{_}:
              {==}
            case C.Term.Min{_, _}:
              {==}
            case C.Term.All{_, _, _}:
              {==}
            case C.Term.Lam{_, _}:
              {==}
            case C.Term.App{_, _, _}:
              {==}
            case C.Term.Sig{_, _, _}:
              {==}
            case C.Term.Tup{_, _, _}:
              {==}
            case C.Term.Prj{_}:
              {==}
            case C.Term.Enu{_}:
              {==}
            case C.Term.Lab{+k}:
              match f:
                case C.Term.Var{_}:
                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                case C.Term.Ref{_}:
                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                case C.Term.Ann{_, _}:
                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                case C.Term.Let{_, _, _}:
                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                case C.Term.Typ{_}:
                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                case C.Term.Min{_, _}:
                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                case C.Term.All{_, _, _}:
                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                case C.Term.Lam{_, _}:
                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                case C.Term.App{_, _, _}:
                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                case C.Term.Sig{_, _, _}:
                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                case C.Term.Tup{+q2, +bt, +r}:
                  match q2:
                    case C.Quan.Q0{}:
                      W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                    case C.Quan.Q1{}:
                      match bt:
                        case C.Term.Var{_}:
                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                        case C.Term.Ref{_}:
                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                        case C.Term.Ann{_, _}:
                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                        case C.Term.Let{_, _, _}:
                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                        case C.Term.Typ{_}:
                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                        case C.Term.Min{_, _}:
                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                        case C.Term.All{_, _, _}:
                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                        case C.Term.Lam{_, _}:
                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                        case C.Term.App{_, _, _}:
                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                        case C.Term.Sig{_, _, _}:
                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                        case C.Term.Tup{+q3, +x, +y}:
                          match q3:
                            case C.Quan.Q0{}:
                              W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                            case C.Quan.Q1{}:
                              match y:
                                case C.Term.Var{_}:
                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                                case C.Term.Ref{_}:
                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                                case C.Term.Ann{_, _}:
                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                                case C.Term.Let{_, _, _}:
                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                                case C.Term.Typ{_}:
                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                                case C.Term.Min{_, _}:
                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                                case C.Term.All{_, _, _}:
                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                                case C.Term.Lam{_, _}:
                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                                case C.Term.App{_, _, _}:
                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                                case C.Term.Sig{_, _, _}:
                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                                case C.Term.Tup{_, _, _}:
                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                                case C.Term.Prj{_}:
                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                                case C.Term.Enu{_}:
                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                                case C.Term.Lab{+u1}:
                                  match x:
                                    case C.Term.Var{_}:
                                      W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1BU_none(q, C.Name.is_eq(u1, C.Program.name.unit()), x, r, {==}))
                                    case C.Term.Ref{_}:
                                      W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1BU_none(q, C.Name.is_eq(u1, C.Program.name.unit()), x, r, {==}))
                                    case C.Term.Ann{_, _}:
                                      W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1BU_none(q, C.Name.is_eq(u1, C.Program.name.unit()), x, r, {==}))
                                    case C.Term.Let{_, _, _}:
                                      W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1BU_none(q, C.Name.is_eq(u1, C.Program.name.unit()), x, r, {==}))
                                    case C.Term.Typ{_}:
                                      W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1BU_none(q, C.Name.is_eq(u1, C.Program.name.unit()), x, r, {==}))
                                    case C.Term.Min{_, _}:
                                      W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1BU_none(q, C.Name.is_eq(u1, C.Program.name.unit()), x, r, {==}))
                                    case C.Term.All{_, _, _}:
                                      W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1BU_none(q, C.Name.is_eq(u1, C.Program.name.unit()), x, r, {==}))
                                    case C.Term.Lam{_, _}:
                                      W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1BU_none(q, C.Name.is_eq(u1, C.Program.name.unit()), x, r, {==}))
                                    case C.Term.App{_, _, _}:
                                      W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1BU_none(q, C.Name.is_eq(u1, C.Program.name.unit()), x, r, {==}))
                                    case C.Term.Sig{_, _, _}:
                                      W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1BU_none(q, C.Name.is_eq(u1, C.Program.name.unit()), x, r, {==}))
                                    case C.Term.Tup{_, _, _}:
                                      W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1BU_none(q, C.Name.is_eq(u1, C.Program.name.unit()), x, r, {==}))
                                    case C.Term.Prj{_}:
                                      W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1BU_none(q, C.Name.is_eq(u1, C.Program.name.unit()), x, r, {==}))
                                    case C.Term.Enu{_}:
                                      W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1BU_none(q, C.Name.is_eq(u1, C.Program.name.unit()), x, r, {==}))
                                    case C.Term.Lab{+bn}:
                                      match r:
                                        case C.Term.Var{_}:
                                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case C.Term.Ref{_}:
                                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case C.Term.Ann{_, _}:
                                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case C.Term.Let{_, _, _}:
                                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case C.Term.Typ{_}:
                                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case C.Term.Min{_, _}:
                                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case C.Term.All{_, _, _}:
                                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case C.Term.Lam{_, _}:
                                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case C.Term.App{_, _, _}:
                                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case C.Term.Sig{_, _, _}:
                                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case C.Term.Tup{+q4, +w, +z}:
                                          match q4:
                                            case C.Quan.Q0{}:
                                              W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                            case C.Quan.Q1{}:
                                              match z:
                                                case C.Term.Var{_}:
                                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case C.Term.Ref{_}:
                                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case C.Term.Ann{_, _}:
                                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case C.Term.Let{_, _, _}:
                                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case C.Term.Typ{_}:
                                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case C.Term.Min{_, _}:
                                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case C.Term.All{_, _, _}:
                                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case C.Term.Lam{_, _}:
                                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case C.Term.App{_, _, _}:
                                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case C.Term.Sig{_, _, _}:
                                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case C.Term.Tup{_, _, _}:
                                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case C.Term.Prj{_}:
                                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case C.Term.Enu{_}:
                                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case C.Term.Lab{+u2}:
                                                  LW.A(C.Name.is_eq(k, C.Program.name.wcon()), q, bn, u1, w, u2)
                                                case C.Term.Mat{_, _, _}:
                                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case C.Term.Efq{}:
                                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case C.Term.Eql{_, _, _}:
                                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case C.Term.Rfl{}:
                                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                                case C.Term.Rwt{_, _, _}:
                                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                            case C.Quan.Q2{}:
                                              W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case C.Term.Prj{_}:
                                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case C.Term.Enu{_}:
                                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case C.Term.Lab{_}:
                                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case C.Term.Mat{_, _, _}:
                                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case C.Term.Efq{}:
                                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case C.Term.Eql{_, _, _}:
                                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case C.Term.Rfl{}:
                                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                        case C.Term.Rwt{_, _, _}:
                                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1B_none(q, Ub(bt), r, bb => {==}))
                                    case C.Term.Mat{_, _, _}:
                                      W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1BU_none(q, C.Name.is_eq(u1, C.Program.name.unit()), x, r, {==}))
                                    case C.Term.Efq{}:
                                      W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1BU_none(q, C.Name.is_eq(u1, C.Program.name.unit()), x, r, {==}))
                                    case C.Term.Eql{_, _, _}:
                                      W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1BU_none(q, C.Name.is_eq(u1, C.Program.name.unit()), x, r, {==}))
                                    case C.Term.Rfl{}:
                                      W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1BU_none(q, C.Name.is_eq(u1, C.Program.name.unit()), x, r, {==}))
                                    case C.Term.Rwt{_, _, _}:
                                      W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, W1BU_none(q, C.Name.is_eq(u1, C.Program.name.unit()), x, r, {==}))
                                case C.Term.Mat{_, _, _}:
                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                                case C.Term.Efq{}:
                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                                case C.Term.Eql{_, _, _}:
                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                                case C.Term.Rfl{}:
                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                                case C.Term.Rwt{_, _, _}:
                                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                            case C.Quan.Q2{}:
                              W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                        case C.Term.Prj{_}:
                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                        case C.Term.Enu{_}:
                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                        case C.Term.Lab{_}:
                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                        case C.Term.Mat{_, _, _}:
                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                        case C.Term.Efq{}:
                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                        case C.Term.Eql{_, _, _}:
                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                        case C.Term.Rfl{}:
                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                        case C.Term.Rwt{_, _, _}:
                          W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                    case C.Quan.Q2{}:
                      W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                case C.Term.Prj{_}:
                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                case C.Term.Enu{_}:
                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                case C.Term.Lab{_}:
                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                case C.Term.Mat{_, _, _}:
                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                case C.Term.Efq{}:
                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                case C.Term.Eql{_, _, _}:
                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                case C.Term.Rfl{}:
                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
                case C.Term.Rwt{_, _, _}:
                  W1K_none(q, C.Name.is_eq(k, C.Program.name.wcon()), f, {==})
            case C.Term.Mat{_, _, _}:
              {==}
            case C.Term.Efq{}:
              {==}
            case C.Term.Eql{_, _, _}:
              {==}
            case C.Term.Rfl{}:
              {==}
            case C.Term.Rwt{_, _, _}:
              {==}
        case C.Quan.Q2{}:
          {==}
    case C.Term.Prj{_}:
      {==}
    case C.Term.Enu{_}:
      {==}
    case C.Term.Lab{_}:
      {==}
    case C.Term.Mat{_, _, _}:
      {==}
    case C.Term.Efq{}:
      {==}
    case C.Term.Eql{_, _, _}:
      {==}
    case C.Term.Rfl{}:
      {==}
    case C.Term.Rwt{_, _, _}:
      {==}

def WE(+p: Nat, +t: C.Term) -> {C.Program.unword(p, t) == Wd(p, t) : Maybe<&2, Word(p)>}:
  match p:
    case 0n:
      WE0(t)
    case 1n+q:
      WE1(q, t)

