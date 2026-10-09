# perf_tree_array: a sequence of U32 kept as a perfect binary tree, read by
# index the way a perfect tree is read: wrap the index to the size, then
# descend left or right by comparing it with the half size. lookups reads
# k scattered positions and sums them. main.bend never names PERF.bend,
# which turns a perfect tree into a contiguous Array and reads that.
#
#   bend demos/perf_tree_array/main.bend <depth> <lookups>
#   bend demos/perf_tree_array/main.bend --no-perf <depth> <lookups>

import Base

type Tree is Data:
  Leaf{value: U32}
  Node{l: Tree, r: Tree}

# 2^d as a U32
def pw(d: Nat) -> U32:
  match d:
    case 0n:
      1
    case 1n+p:
      U32.shl(pw(p))

# the perfect tree of depth d holding lo, lo + 1, ..
def build(d: Nat, +lo: U32) -> Tree:
  match d:
    case 0n:
      Leaf{lo}
    case 1n++p:
      Node{build(p, lo), build(p, U32.add(lo, pw(p)))}

# a perfect tree's size: twice its left half's
def tree_size(t: Tree) -> U32:
  match t:
    case Leaf{x}:
      1
    case Node{l, r}:
      U32.shl(tree_size(l))

# the value at i in a tree of size n; z says whether i is in the left half
def tree_go(t: Tree, n: U32, +i: U32, z: Bool) -> U32:
  match t z:
    case Leaf{x} _:
      x
    case Node{l, r} True{}:
      +h = U32.shr(n)
      tree_go(l, h, i, U32.is_lt(i, U32.shr(h)))
    case Node{l, r} False{}:
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      tree_go(r, h, j, U32.is_lt(j, U32.shr(h)))

# the value at i, the index wrapped to the size
def tree_get(+t: Tree, +i: U32) -> U32:
  +n = tree_size(t)
  +j = U32.and(i, U32.sub(n, 1))
  tree_go(t, n, j, U32.is_lt(j, U32.shr(n)))

# the sum of k reads, at i * 7919, (i + 1) * 7919, ..
def lookups(k: Nat, +i: U32, +t: Tree, acc: U32) -> U32:
  match k:
    case 0n:
      acc
    case 1n+p:
      lookups(p, U32.add(i, 1), t, U32.add(acc, tree_get(t, U32.mul(i, 7919))))

# the two numbers after the program (0 when missing)
def num(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{n}:
      n

def two(xs: List<String>) -> Nat & Nat:
  match xs:
    case Nil{}:
      (0n, 0n)
    case p <> t:
      match t:
        case Nil{}:
          (0n, 0n)
        case a <> r:
          match r:
            case Nil{}:
              (num(Nat.read(a)), 0n)
            case b <> s:
              (num(Nat.read(a)), num(Nat.read(b)))

def run(dk: Nat & Nat) -> String:
  (d, k) = dk
  U32.show(lookups(k, 0, build(d, 0), 0))

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    IO.print(run(two(xs)))
