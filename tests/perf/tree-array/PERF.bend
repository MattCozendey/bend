# perf (tree-array): lookups on build's tree takes the producer route (an
# Array built directly); on a lopsided tree it takes the plain route,
# whose guard keeps main's lookups. Both print what main.bend alone prints.
import Base
import ./main.bend as M

# The route
# ---------

# the tree as an Array, node for node
def to_arr(t: M.Tree) -> Array<U32>:
  match t:
    case Leaf{x}:
      ALeaf{x}
    case Node{l, r}:
      ANode{to_arr(l), to_arr(r)}

# whether every leaf of t sits at depth d. An Array is perfect at run
# time: halves of different sizes stop the program, so the route checks.
def perfect.at(t: M.Tree, d: Nat) -> Bool:
  match t d:
    case Leaf{x} 0n:
      True{}
    case Leaf{x} 1n+p:
      False{}
    case Node{l, r} 0n:
      False{}
    case Node{l, r} 1n++p:
      Bool.and(perfect.at(l, p), perfect.at(r, p))

# the depth of t's left spine
def depth(t: M.Tree) -> Nat:
  match t:
    case Leaf{x}:
      0n
    case Node{l, r}:
      1n+depth(l)

def perfect(+t: M.Tree) -> Bool:
  perfect.at(t, depth(t))

def step.fin(acc: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  (b, v) = r
  (b, U32.add(acc, v))

def step(+i: U32, s: Array<U32> & U32) -> Array<U32> & U32:
  (a, acc) = s
  step.fin(acc, Array.get(U32, a, U32.mul(i, 7919)))

# lookups on the Array, threading it with the sum
def lookups_arr(k: Nat, +i: U32, s: Array<U32> & U32) -> Array<U32> & U32:
  match k:
    case 0n:
      s
    case 1n+p:
      lookups_arr(p, U32.add(i, 1), step(i, s))

def lookups.pick(k: Nat, +i: U32, +t: M.Tree, acc: U32, ok: Bool) -> U32:
  match ok:
    case True{}:
      Pair.snd(Array<U32>, U32, lookups_arr(k, i, (to_arr(t), acc)))
    case False{}:
      M.lookups(k, i, t, acc)

def lookups_fast(k: Nat, +i: U32, +t: M.Tree, acc: U32) -> U32:
  lookups.pick(k, i, t, acc, perfect(t))

# Lemmas
# ------

# Array.size reads to_arr(t) as tree_size reads t
def size_arr(t: M.Tree) ->
  {(to_arr(t), M.tree_size(t)) == Array.size(U32, to_arr(t)) : Array<U32> & U32}:
  match t:
    case Leaf{x}:
      {==}
    case Node{l, r}:
      %size_arr(l) : {(ANode{to_arr(l), to_arr(r)}, U32.shl(M.tree_size(l))) == Array.size.node(U32, to_arr(r), _) : Array<U32> & U32}
      {==}

# Array.get.go descends to_arr(t) as tree_go descends t
def go_arr(t: M.Tree, +n: U32, +i: U32, z: Bool) ->
  {(to_arr(t), M.tree_go(t, n, i, z)) == Array.get.go(U32, to_arr(t), n, i, z) : Array<U32> & U32}:
  match t z:
    case Leaf{x} _:
      {==}
    case Node{l, r} True{}:
      %go_arr(l, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n)))) : {(ANode{to_arr(l), to_arr(r)}, M.tree_go(l, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n))))) == Array.swap.lo(U32, to_arr(r), _) : Array<U32> & U32}
      {==}
    case Node{l, r} False{}:
      %go_arr(r, U32.shr(n), U32.sub(i, U32.shr(n)), U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))) : {(ANode{to_arr(l), to_arr(r)}, M.tree_go(r, U32.shr(n), U32.sub(i, U32.shr(n)), U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))) == Array.swap.hi(U32, to_arr(l), _) : Array<U32> & U32}
      {==}

# Array.get reads to_arr(t) as tree_get reads t, and hands it back
def get_arr(+t: M.Tree, +i: U32) ->
  {(to_arr(t), M.tree_get(t, i)) == Array.get(U32, to_arr(t), i) : Array<U32> & U32}:
  %size_arr(t) : {(to_arr(t), M.tree_get(t, i)) == Array.get.at(U32, i, _) : Array<U32> & U32}
  go_arr(t, M.tree_size(t), U32.and(i, U32.sub(M.tree_size(t), 1)), U32.is_lt(U32.and(i, U32.sub(M.tree_size(t), 1)), U32.shr(M.tree_size(t))))

# lookups_arr on to_arr(t) sums what lookups sums on t
def lookups_arr_eq(k: Nat, +i: U32, +t: M.Tree, acc: U32) ->
  {(to_arr(t), M.lookups(k, i, t, acc)) == lookups_arr(k, i, (to_arr(t), acc)) : Array<U32> & U32}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      %get_arr(t, U32.mul(i, 7919)) : {(to_arr(t), M.lookups(1n+p, i, t, acc)) == lookups_arr(p, U32.add(i, 1), step.fin(acc, _)) : Array<U32> & U32}
      lookups_arr_eq(p, U32.add(i, 1), t, U32.add(acc, M.tree_get(t, U32.mul(i, 7919))))

# whichever way the guard answers, the route sums what lookups sums
def pick_eq(k: Nat, +i: U32, +t: M.Tree, acc: U32, ok: Bool) ->
  {M.lookups(k, i, t, acc) == lookups.pick(k, i, t, acc, ok) : U32}:
  match ok:
    case True{}:
      %lookups_arr_eq(k, i, t, acc) : {M.lookups(k, i, t, acc) == Pair.snd(Array<U32>, U32, _) : U32}
      {==}
    case False{}:
      {==}

# The rule
# --------

law lookups.fast:
  for k: Nat
  for +i: U32
  for +t: M.Tree
  for acc: U32
  {M.lookups(k, i, t, acc) == lookups_fast(k, i, t, acc) : U32}

def lookups.fast(k, i, t, acc):
  pick_eq(k, i, t, acc, perfect(t))

# A producer rule
# ---------------

# main calls lookups on build's tree: that call reads an Array built
# directly, with no Tree to convert and no guard, as build's trees are
# perfect

# build's tree, built as an Array
def build_arr(d: Nat, +lo: U32) -> Array<U32>:
  match d:
    case 0n:
      ALeaf{lo}
    case 1n++p:
      ANode{build_arr(p, lo), build_arr(p, U32.add(lo, M.pw(p)))}

def build_arr_eq(d: Nat, +lo: U32) -> {to_arr(M.build(d, lo)) == build_arr(d, lo) : Array<U32>}:
  match d:
    case 0n:
      {==}
    case 1n++p:
      %build_arr_eq(p, lo) : {ANode{to_arr(M.build(p, lo)), to_arr(M.build(p, U32.add(lo, M.pw(p))))} == ANode{_, build_arr(p, U32.add(lo, M.pw(p)))} : Array<U32>}
      %build_arr_eq(p, U32.add(lo, M.pw(p))) : {ANode{to_arr(M.build(p, lo)), to_arr(M.build(p, U32.add(lo, M.pw(p))))} == ANode{to_arr(M.build(p, lo)), _} : Array<U32>}
      {==}

def lookups_built(k: Nat, +i: U32, d: Nat, +lo: U32, acc: U32) -> U32:
  Pair.snd(Array<U32>, U32, lookups_arr(k, i, (build_arr(d, lo), acc)))

law lookups.built:
  for k: Nat
  for +i: U32
  for +d: Nat
  for +lo: U32
  for acc: U32
  {M.lookups(k, i, M.build(d, lo), acc) == lookups_built(k, i, d, lo, acc) : U32}

def lookups.built(k, i, d, lo, acc):
  %build_arr_eq(d, lo) : {M.lookups(k, i, M.build(d, lo), acc) == Pair.snd(Array<U32>, U32, lookups_arr(k, i, (_, acc))) : U32}
  %lookups_arr_eq(k, i, M.build(d, lo), acc) : {M.lookups(k, i, M.build(d, lo), acc) == Pair.snd(Array<U32>, U32, _) : U32}
  {==}
