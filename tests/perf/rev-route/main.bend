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

def report(xs: List<&2, Nat>) -> IO(Unit):
  IO.print(Nat.show(last(rev(xs))))

def main() -> IO(Unit):
  report(rev([1n, 2n, 3n]))

#|1
#?ALL PROOFS CHECK
#?Use --verdict for mathematical validity.
#?PERF routes:
#?- rev -> PERF.rev_fast (every call)
#?- report -> PERF.report_fast (every call)
