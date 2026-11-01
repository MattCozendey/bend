import Base
import ./impl.bend as C

def isApp(t: C.Term) -> Bool:
  match t:
    case C.Term.App{_, _, _}:
      True{}
    case _:
      False{}

def t.k(+t: C.Term) -> {isApp(t) == isApp(t) : Bool}:
  match t:
    case C.Term.Var{i}:
      ?h
    case _:
      {==}
