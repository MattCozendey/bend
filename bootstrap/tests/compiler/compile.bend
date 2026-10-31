# the compiler of step 1 as a program: the bytes of a book in, the bytes of its
# module out
import Base
import ../../bend/src/compiler/impl.bend as C

def main(+p: List<&2, U32>) -> List<&2, U32>:
  C.Compiler.compile(p)
