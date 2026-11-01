import Base
import ./impl.bend as C

def Mb.ok(m: Maybe<List<&2, C.Item>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{_}:
      False{}

def t.lam(st: List<&2, C.Item>) -> {Mb.ok(C.Book.read.lam(st)) == True{} : Bool}:
  match st:
    case Con{C.Item.term{+f}, Con{C.Item.quan{+q}, +rest}}:
      ?h
    case _:
      {==}
