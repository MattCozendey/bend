# perf (rev-route): a pure rule (rev, quadratic, gets a linear route) and
# an IO rule (report), the second proven with the first. main's rev and
# report both take their routes; the output is the same without them.
import Base
import ./main.bend as M

def rev_go(xs: List<&2, Nat>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      rev_go(t, h <> acc)

def rev_fast(xs: List<&2, Nat>) -> List<&2, Nat>:
  rev_go(xs, Nil{})

# Lemmas
# ------

def app_nil(xs: List<&2, Nat>) -> {xs == M.app(xs, Nil{}) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %app_nil(t) : {h <> t == h <> _ : List<&2, Nat>}
      {==}

def app_assoc(xs: List<&2, Nat>, +ys: List<&2, Nat>, +zs: List<&2, Nat>)
  -> {M.app(xs, M.app(ys, zs)) == M.app(M.app(xs, ys), zs) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %app_assoc(t, ys, zs) : {h <> M.app(t, M.app(ys, zs)) == h <> _ : List<&2, Nat>}
      {==}

# rev_go(xs, acc) is app(rev(xs), acc): the step moves h from the end of
# rev(t) onto acc, which app_assoc allows
def rev_go_app(xs: List<&2, Nat>, +acc: List<&2, Nat>)
  -> {M.app(M.rev(xs), acc) == rev_go(xs, acc) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %app_assoc(M.rev(t), [h], acc) : {_ == rev_go(t, h <> acc) : List<&2, Nat>}
      rev_go_app(t, h <> acc)

# The rule
# --------

law rev.fast:
  for +xs: List<&2, Nat>
  {M.rev(xs) == rev_fast(xs) : List<&2, Nat>}

def rev.fast(xs):
  %rev_go_app(xs, Nil{}) : {M.rev(xs) == _ : List<&2, Nat>}
  %app_nil(M.rev(xs)) : {M.rev(xs) == _ : List<&2, Nat>}
  {==}

def report_fast(xs: List<&2, Nat>) -> IO(Unit):
  IO.print(Nat.show(M.last(rev_fast(xs))))

law report.fast:
  for +xs: List<&2, Nat>
  {M.report(xs) == report_fast(xs) : IO(Unit)}

def report.fast(xs):
  %rev.fast(xs) : {M.report(xs) == IO.print(Nat.show(M.last(_))) : IO(Unit)}
  {==}
