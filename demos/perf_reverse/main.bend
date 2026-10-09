# perf_reverse: reverse, written the plain way. The reverse of h <> t is
# the reverse of t with h appended at its end, and each append walks the
# whole list, so rev is quadratic. main.bend never names PERF.bend, which
# gives rev a linear route and report, an IO function, a route of its own,
# each proven equal; a run or a build takes them. main reverses the range
# twice, once in main and once in report, and prints 0.
#
#   bend demos/perf_reverse/main.bend [length]
#   bend demos/perf_reverse/main.bend --no-perf [length]

import Base

def app(xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      ys
    case h <> t:
      h <> app(t, ys)

def rev(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      app(rev(t), [h])

def last(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      h

# prints the head of the reverse of xs
def report(xs: List<&2, Nat>) -> IO(Unit):
  IO.print(Nat.show(last(rev(xs))))

# the list's length: the first argument, else 20000
def size.or(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      20000n
    case Some{n}:
      n

def size(xs: List<String>) -> Nat:
  match xs:
    case Nil{}:
      20000n
    case p <> t:
      match t:
        case Nil{}:
          20000n
        case a <> r:
          size.or(Nat.read(a))

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    report(rev(List.range(size(xs))))
