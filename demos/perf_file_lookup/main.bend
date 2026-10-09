# perf_file_lookup: the numbers of a file, one per line, paired up level
# by level into a balanced tree, then k scattered reads by index, as in
# perf_tree_array. The tree is perfect exactly when the file holds 2^n
# numbers, so the route's guard decides from the data: a perfect tree is
# read through a contiguous Array, any other keeps main's lookups.
# main.bend never names PERF.bend.
#
#   bend demos/perf_file_lookup/main.bend <file> <reads>
#   bend demos/perf_file_lookup/main.bend --no-perf <file> <reads>

import Base

type Tree is Data:
  Leaf{value: U32}
  Node{l: Tree, r: Tree}

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

# Reading
# -------

def num(m: Maybe<&2, U32>) -> U32:
  match m:
    case None{}:
      0
    case Some{v}:
      v

# the numbers of the lines, blank lines skipped
def nums(ls: List<&2, String>) -> List<&2, U32>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> r:
      match l:
        case SNil{}:
          nums(r)
        case SCon{c, t}:
          num(U32.read(SCon{c, t})) <> nums(r)

def leaves(xs: List<&2, U32>) -> List<&2, Tree>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> r:
      Leaf{x} <> leaves(r)

# neighbours paired: a level of the tree over the one below
def pairs(ts: List<&2, Tree>) -> List<&2, Tree>:
  match ts:
    case Nil{}:
      Nil{}
    case a <> r:
      match r:
        case Nil{}:
          [a]
        case b <> s:
          Node{a, b} <> pairs(s)

def first(ts: List<&2, Tree>) -> Tree:
  match ts:
    case Nil{}:
      Leaf{0}
    case t <> r:
      t

# the levels paired up to one tree, f levels at most
def rise(f: Nat, ts: List<&2, Tree>) -> Tree:
  match f:
    case 0n:
      first(ts)
    case 1n+g:
      match ts:
        case Nil{}:
          Leaf{0}
        case t <> r:
          match r:
            case Nil{}:
              t
            case u <> s:
              rise(g, pairs(t <> u <> s))

def run(text: String, k: Nat) -> String:
  U32.show(lookups(k, 0, rise(40n, leaves(nums(String.lines(text)))), 0))

# Main
# ----

def natv(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{n}:
      n

# the file and the reads after the program
def opts(xs: List<String>) -> String & Nat:
  match xs:
    case Nil{}:
      ("", 0n)
    case p <> t:
      match t:
        case Nil{}:
          ("", 0n)
        case a <> r:
          match r:
            case Nil{}:
              (a, 0n)
            case b <> s:
              (a, natv(Nat.read(b)))

def text(p: File & Result<&1, &1, U32 & String, String>) -> IO(String):
  (f, r) = p
  do IO<String>:
    Unit <- File.close(f)
    IO.pass(String, r)

def go(o: String & Nat) -> IO(Unit):
  (path, k) = o
  do IO<Unit>:
    r : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    f : File <- IO.pass(File, r)
    p : File & Result<&1, &1, U32 & String, String> <- File.read(f, 200000000)
    s : String <- text(p)
    IO.print(run(s, k))

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    go(opts(xs))
