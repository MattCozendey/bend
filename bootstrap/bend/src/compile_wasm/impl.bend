import Base
import ../source/impl.bend as Source
import ../front/impl.bend as Front
import ../wasm/impl.bend as Wasm
import ../imp/impl.bend as Imp
import ../fun/impl.bend as Fun
import ../fmachine/impl.bend as FM
import ../fmachine/code.bend as Code
import ../runtime/impl.bend as RT

# The compiler
# ============
#
# The assembly (step 6): the module of a text is the run time (step 5) of the
# machine in F (step 4), on the defs that the front (step 2) parses. Its
# function 51, F.Main, starts with the book, the input, the def
# bootstrap.run and the number 255 (FM.start). A text that does not parse
# gives a module that traps. When the image of the book does not fit in the
# memory (RT.fits), the module gives Out.oom.

# the values after the input at the start: the def bootstrap.run, and 255
def Tail(+bk: List<&2, Source.Def>) -> List<&2, Fun.V>:
  [FM.Enc.mdef(FM.Input.run_def(bk)), FM.Enc.nat(255n)]

# a program that gives Out.oom
def Oom() -> Imp.Prog:
  Imp.Prog{18n, Imp.Stm.loop{RT.S.oom(0n)}, RT.E.l(8n)}

# a program that traps
def Trap() -> Imp.Prog:
  Imp.Prog{0n, Imp.Stm.trap{}, RT.E.k(0)}

# the run time of the F program prog on the book bk, when its image fits
def Prog.book(+prog: List<&2, Fun.C>, +bk: List<&2, Source.Def>) -> Imp.Prog:
  Bool.pick(Imp.Prog, RT.fits(prog, FM.Enc.book(bk), Tail(bk)), RT.RT(prog, 51n, FM.Enc.book(bk), Tail(bk)), Oom())

def Prog.of(+prog: List<&2, Fun.C>, m: Maybe<&2, List<&2, Source.Def>>) -> Imp.Prog:
  match m:
    case Some{bk}:
      Prog.book(prog, bk)
    case None{}:
      Trap()

# the module of the text src
def compile(+src: List<&2, Nat>) -> Wasm.Module:
  Imp.Imp.compile(Prog.of(Code.prog(), Front.Front.book(src)))
