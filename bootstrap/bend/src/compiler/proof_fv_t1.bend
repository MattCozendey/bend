import Base
import ./impl.bend as C

def isApp(t: C.Term) -> Bool:
  match t:
    case C.Term.App{_, _, _}:
      True{}
    case _:
      False{}

def t.args(t: C.Term, xs: List<&2, C.Arg>) -> {Bool.or(isApp(t), Nat.is_eq(List.length(&2, C.Arg, C.Term.args(t, xs)), List.length(&2, C.Arg, xs))) == True{} : Bool}:
  match t:
    case C.Term.App{q, f, x}:
      {==}
    case _:
      {==}
