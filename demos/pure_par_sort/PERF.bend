# Parallel sort -- the route. main sorts the tree gen builds, and gen's tree
# is always one block of consecutive numbers, descending. Sorted up it is
# the same block ascending, which asc builds in one pass with no compare;
# sorted down it is gen's tree itself. The proofs follow the bitonic sort
# on such blocks: a mix of two blocks that do not overlap keeps one whole
# block, so every flow and sort lands on asc or gen again.

import Base
import ./main.bend as M

# Order
# -----

# LT(a, b): a < b, as Unit or Empty
def LT(a: Nat, b: Nat) -> Data:
  match a b:
    case 0n 0n:
      Empty
    case 0n 1n+b1:
      Unit
    case 1n+a1 0n:
      Empty
    case 1n+a1 1n+b1:
      LT(a1, b1)

def lt_true(+k: Nat, +j: Nat, h: LT(k, j)) -> {True{} == Nat.is_lt(k, j) : Bool}:
  match k j:
    case 0n 0n:
      match h:
    case 0n 1n+j1:
      {==}
    case 1n+k1 0n:
      match h:
    case 1n+k1 1n+j1:
      lt_true(k1, j1, h)

def lt_false(+k: Nat, +j: Nat, h: LT(k, j)) -> {False{} == Nat.is_lt(j, k) : Bool}:
  match k j:
    case 0n 0n:
      match h:
    case 0n 1n+j1:
      {==}
    case 1n+k1 0n:
      match h:
    case 1n+k1 1n+j1:
      lt_false(k1, j1, h)

def lt_succ(+n: Nat) -> LT(n, 1n+n):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      lt_succ(p)

# k < j keeps 2k < 2j, 2k + 1 < 2j and 2k < 2j + 1
def lt_dd(+k: Nat, +j: Nat, h: LT(k, j)) -> LT(Nat.double(k), Nat.double(j)):
  match k j:
    case 0n 0n:
      match h:
    case 0n 1n+j1:
      Unit{}
    case 1n+k1 0n:
      match h:
    case 1n+k1 1n+j1:
      lt_dd(k1, j1, h)

def lt_sd(+k: Nat, +j: Nat, h: LT(k, j)) -> LT(1n+Nat.double(k), Nat.double(j)):
  match k j:
    case 0n 0n:
      match h:
    case 0n 1n+j1:
      Unit{}
    case 1n+k1 0n:
      match h:
    case 1n+k1 1n+j1:
      lt_sd(k1, j1, h)

def lt_ds(+k: Nat, +j: Nat, h: LT(k, j)) -> LT(Nat.double(k), 1n+Nat.double(j)):
  match k j:
    case 0n 0n:
      match h:
    case 0n 1n+j1:
      Unit{}
    case 1n+k1 0n:
      match h:
    case 1n+k1 1n+j1:
      lt_ds(k1, j1, h)

# The route
# ---------

# the numbers i * 2^d .. (i + 1) * 2^d - 1, ascending: gen's block
def asc(d: Nat, +i: Nat) -> M.Tree(d):
  match d:
    case 0n:
      i
    case 1n++p:
      (asc(p, Nat.double(i)), asc(p, 1n+Nat.double(i)))

# gen's block sorted: ascending up, as it is down
def sorted(d: Nat, s: Bool, +i: Nat) -> M.Tree(d):
  match s:
    case True{}:
      asc(d, i)
    case False{}:
      M.gen(d, i)

# Mix
# ---
# Every leaf of the block k is below every leaf of the block j when
# k < j, so a mix keeps one block whole: the lesser up, the greater down.

# an ascending upper block against a descending lower one
def mix_lo_ag(d: Nat, +s: Bool, +j: Nat, +k: Nat, +h: LT(k, j)) ->
  {M.pick(M.Tree(d), s, M.gen(d, k), asc(d, j)) == M.mix(d, s, asc(d, j), M.gen(d, k)) : M.Tree(d)}:
  match d s:
    case 0n True{}:
      %lt_true(k, j, h) : {M.pick(Nat, True{}, k, j) == M.pick(Nat, Bool.xor(True{}, _), j, k) : Nat}
      {==}
    case 0n False{}:
      %lt_true(k, j, h) : {M.pick(Nat, False{}, k, j) == M.pick(Nat, Bool.xor(False{}, _), j, k) : Nat}
      {==}
    case 1n++p True{}:
      %mix_lo_ag(p, True{}, Nat.double(j), 1n+Nat.double(k), lt_sd(k, j, h)) : {M.pick(M.Tree(1n+p), True{}, M.gen(1n+p, k), asc(1n+p, j)) == (_, M.mix(p, True{}, asc(p, 1n+Nat.double(j)), M.gen(p, Nat.double(k)))) : M.Tree(1n+p)}
      %mix_lo_ag(p, True{}, 1n+Nat.double(j), Nat.double(k), lt_ds(k, j, h)) : {M.pick(M.Tree(1n+p), True{}, M.gen(1n+p, k), asc(1n+p, j)) == (M.pick(M.Tree(p), True{}, M.gen(p, 1n+Nat.double(k)), asc(p, Nat.double(j))), _) : M.Tree(1n+p)}
      {==}
    case 1n++p False{}:
      %mix_lo_ag(p, False{}, Nat.double(j), 1n+Nat.double(k), lt_sd(k, j, h)) : {M.pick(M.Tree(1n+p), False{}, M.gen(1n+p, k), asc(1n+p, j)) == (_, M.mix(p, False{}, asc(p, 1n+Nat.double(j)), M.gen(p, Nat.double(k)))) : M.Tree(1n+p)}
      %mix_lo_ag(p, False{}, 1n+Nat.double(j), Nat.double(k), lt_ds(k, j, h)) : {M.pick(M.Tree(1n+p), False{}, M.gen(1n+p, k), asc(1n+p, j)) == (M.pick(M.Tree(p), False{}, M.gen(p, 1n+Nat.double(k)), asc(p, Nat.double(j))), _) : M.Tree(1n+p)}
      {==}

# an ascending lower block against an ascending upper one
def mix_hi_aa(d: Nat, +s: Bool, +k: Nat, +j: Nat, +h: LT(k, j)) ->
  {M.pick(M.Tree(d), s, asc(d, k), asc(d, j)) == M.mix(d, s, asc(d, k), asc(d, j)) : M.Tree(d)}:
  match d s:
    case 0n True{}:
      %lt_false(k, j, h) : {M.pick(Nat, True{}, k, j) == M.pick(Nat, Bool.xor(True{}, _), k, j) : Nat}
      {==}
    case 0n False{}:
      %lt_false(k, j, h) : {M.pick(Nat, False{}, k, j) == M.pick(Nat, Bool.xor(False{}, _), k, j) : Nat}
      {==}
    case 1n++p True{}:
      %mix_hi_aa(p, True{}, Nat.double(k), Nat.double(j), lt_dd(k, j, h)) : {M.pick(M.Tree(1n+p), True{}, asc(1n+p, k), asc(1n+p, j)) == (_, M.mix(p, True{}, asc(p, 1n+Nat.double(k)), asc(p, 1n+Nat.double(j)))) : M.Tree(1n+p)}
      %mix_hi_aa(p, True{}, 1n+Nat.double(k), 1n+Nat.double(j), lt_dd(k, j, h)) : {M.pick(M.Tree(1n+p), True{}, asc(1n+p, k), asc(1n+p, j)) == (M.pick(M.Tree(p), True{}, asc(p, Nat.double(k)), asc(p, Nat.double(j))), _) : M.Tree(1n+p)}
      {==}
    case 1n++p False{}:
      %mix_hi_aa(p, False{}, Nat.double(k), Nat.double(j), lt_dd(k, j, h)) : {M.pick(M.Tree(1n+p), False{}, asc(1n+p, k), asc(1n+p, j)) == (_, M.mix(p, False{}, asc(p, 1n+Nat.double(k)), asc(p, 1n+Nat.double(j)))) : M.Tree(1n+p)}
      %mix_hi_aa(p, False{}, 1n+Nat.double(k), 1n+Nat.double(j), lt_dd(k, j, h)) : {M.pick(M.Tree(1n+p), False{}, asc(1n+p, k), asc(1n+p, j)) == (M.pick(M.Tree(p), False{}, asc(p, Nat.double(k)), asc(p, Nat.double(j))), _) : M.Tree(1n+p)}
      {==}

# a descending upper block against a descending lower one
def mix_lo_gg(d: Nat, +s: Bool, +j: Nat, +k: Nat, +h: LT(k, j)) ->
  {M.pick(M.Tree(d), s, M.gen(d, k), M.gen(d, j)) == M.mix(d, s, M.gen(d, j), M.gen(d, k)) : M.Tree(d)}:
  match d s:
    case 0n True{}:
      %lt_true(k, j, h) : {M.pick(Nat, True{}, k, j) == M.pick(Nat, Bool.xor(True{}, _), j, k) : Nat}
      {==}
    case 0n False{}:
      %lt_true(k, j, h) : {M.pick(Nat, False{}, k, j) == M.pick(Nat, Bool.xor(False{}, _), j, k) : Nat}
      {==}
    case 1n++p True{}:
      %mix_lo_gg(p, True{}, 1n+Nat.double(j), 1n+Nat.double(k), lt_dd(k, j, h)) : {M.pick(M.Tree(1n+p), True{}, M.gen(1n+p, k), M.gen(1n+p, j)) == (_, M.mix(p, True{}, M.gen(p, Nat.double(j)), M.gen(p, Nat.double(k)))) : M.Tree(1n+p)}
      %mix_lo_gg(p, True{}, Nat.double(j), Nat.double(k), lt_dd(k, j, h)) : {M.pick(M.Tree(1n+p), True{}, M.gen(1n+p, k), M.gen(1n+p, j)) == (M.pick(M.Tree(p), True{}, M.gen(p, 1n+Nat.double(k)), M.gen(p, 1n+Nat.double(j))), _) : M.Tree(1n+p)}
      {==}
    case 1n++p False{}:
      %mix_lo_gg(p, False{}, 1n+Nat.double(j), 1n+Nat.double(k), lt_dd(k, j, h)) : {M.pick(M.Tree(1n+p), False{}, M.gen(1n+p, k), M.gen(1n+p, j)) == (_, M.mix(p, False{}, M.gen(p, Nat.double(j)), M.gen(p, Nat.double(k)))) : M.Tree(1n+p)}
      %mix_lo_gg(p, False{}, Nat.double(j), Nat.double(k), lt_dd(k, j, h)) : {M.pick(M.Tree(1n+p), False{}, M.gen(1n+p, k), M.gen(1n+p, j)) == (M.pick(M.Tree(p), False{}, M.gen(p, 1n+Nat.double(k)), M.gen(p, 1n+Nat.double(j))), _) : M.Tree(1n+p)}
      {==}

# Flow
# ----
# A sorted block, either way, flows into the block sorted by s.

def flow_asc(d: Nat, +s: Bool, +i: Nat) ->
  {M.pick(M.Tree(d), s, asc(d, i), M.gen(d, i)) == M.flow(d, s, asc(d, i)) : M.Tree(d)}:
  match d:
    case 0n:
      match s:
        case True{}:
          {==}
        case False{}:
          {==}
    case 1n++p:
      match s:
        case True{}:
          %mix_hi_aa(p, True{}, Nat.double(i), 1n+Nat.double(i), lt_succ(Nat.double(i))) : {asc(1n+p, i) == (M.flow(p, True{}, _), M.flow(p, True{}, M.mix(p, False{}, asc(p, Nat.double(i)), asc(p, 1n+Nat.double(i))))) : M.Tree(1n+p)}
          %mix_hi_aa(p, False{}, Nat.double(i), 1n+Nat.double(i), lt_succ(Nat.double(i))) : {asc(1n+p, i) == (M.flow(p, True{}, asc(p, Nat.double(i))), M.flow(p, True{}, _)) : M.Tree(1n+p)}
          %flow_asc(p, True{}, Nat.double(i)) : {asc(1n+p, i) == (_, M.flow(p, True{}, asc(p, 1n+Nat.double(i)))) : M.Tree(1n+p)}
          %flow_asc(p, True{}, 1n+Nat.double(i)) : {asc(1n+p, i) == (asc(p, Nat.double(i)), _) : M.Tree(1n+p)}
          {==}
        case False{}:
          %mix_hi_aa(p, False{}, Nat.double(i), 1n+Nat.double(i), lt_succ(Nat.double(i))) : {M.gen(1n+p, i) == (M.flow(p, False{}, _), M.flow(p, False{}, M.mix(p, True{}, asc(p, Nat.double(i)), asc(p, 1n+Nat.double(i))))) : M.Tree(1n+p)}
          %mix_hi_aa(p, True{}, Nat.double(i), 1n+Nat.double(i), lt_succ(Nat.double(i))) : {M.gen(1n+p, i) == (M.flow(p, False{}, asc(p, 1n+Nat.double(i))), M.flow(p, False{}, _)) : M.Tree(1n+p)}
          %flow_asc(p, False{}, 1n+Nat.double(i)) : {M.gen(1n+p, i) == (_, M.flow(p, False{}, asc(p, Nat.double(i)))) : M.Tree(1n+p)}
          %flow_asc(p, False{}, Nat.double(i)) : {M.gen(1n+p, i) == (M.gen(p, 1n+Nat.double(i)), _) : M.Tree(1n+p)}
          {==}

def flow_gen(d: Nat, +s: Bool, +i: Nat) ->
  {M.pick(M.Tree(d), s, asc(d, i), M.gen(d, i)) == M.flow(d, s, M.gen(d, i)) : M.Tree(d)}:
  match d:
    case 0n:
      match s:
        case True{}:
          {==}
        case False{}:
          {==}
    case 1n++p:
      match s:
        case True{}:
          %mix_lo_gg(p, True{}, 1n+Nat.double(i), Nat.double(i), lt_succ(Nat.double(i))) : {asc(1n+p, i) == (M.flow(p, True{}, _), M.flow(p, True{}, M.mix(p, False{}, M.gen(p, 1n+Nat.double(i)), M.gen(p, Nat.double(i))))) : M.Tree(1n+p)}
          %mix_lo_gg(p, False{}, 1n+Nat.double(i), Nat.double(i), lt_succ(Nat.double(i))) : {asc(1n+p, i) == (M.flow(p, True{}, M.gen(p, Nat.double(i))), M.flow(p, True{}, _)) : M.Tree(1n+p)}
          %flow_gen(p, True{}, Nat.double(i)) : {asc(1n+p, i) == (_, M.flow(p, True{}, M.gen(p, 1n+Nat.double(i)))) : M.Tree(1n+p)}
          %flow_gen(p, True{}, 1n+Nat.double(i)) : {asc(1n+p, i) == (asc(p, Nat.double(i)), _) : M.Tree(1n+p)}
          {==}
        case False{}:
          %mix_lo_gg(p, False{}, 1n+Nat.double(i), Nat.double(i), lt_succ(Nat.double(i))) : {M.gen(1n+p, i) == (M.flow(p, False{}, _), M.flow(p, False{}, M.mix(p, True{}, M.gen(p, 1n+Nat.double(i)), M.gen(p, Nat.double(i))))) : M.Tree(1n+p)}
          %mix_lo_gg(p, True{}, 1n+Nat.double(i), Nat.double(i), lt_succ(Nat.double(i))) : {M.gen(1n+p, i) == (M.flow(p, False{}, M.gen(p, 1n+Nat.double(i))), M.flow(p, False{}, _)) : M.Tree(1n+p)}
          %flow_gen(p, False{}, 1n+Nat.double(i)) : {M.gen(1n+p, i) == (_, M.flow(p, False{}, M.gen(p, Nat.double(i)))) : M.Tree(1n+p)}
          %flow_gen(p, False{}, Nat.double(i)) : {M.gen(1n+p, i) == (M.gen(p, 1n+Nat.double(i)), _) : M.Tree(1n+p)}
          {==}

# Sort
# ----

# gen's block sorts to itself sorted: the halves sort to an ascending
# upper block and a descending lower one, which flow then merges
def sort_gen(d: Nat, +s: Bool, +i: Nat) ->
  {M.pick(M.Tree(d), s, asc(d, i), M.gen(d, i)) == M.sort(d, s, M.gen(d, i)) : M.Tree(d)}:
  match d:
    case 0n:
      match s:
        case True{}:
          {==}
        case False{}:
          {==}
    case 1n++p:
      match s:
        case True{}:
          %sort_gen(p, True{}, 1n+Nat.double(i)) : {M.pick(M.Tree(1n+p), True{}, asc(1n+p, i), M.gen(1n+p, i)) == M.flow(1n+p, True{}, (_, M.sort(p, False{}, M.gen(p, Nat.double(i))))) : M.Tree(1n+p)}
          %sort_gen(p, False{}, Nat.double(i)) : {M.pick(M.Tree(1n+p), True{}, asc(1n+p, i), M.gen(1n+p, i)) == M.flow(1n+p, True{}, (asc(p, 1n+Nat.double(i)), _)) : M.Tree(1n+p)}
          %mix_lo_ag(p, True{}, 1n+Nat.double(i), Nat.double(i), lt_succ(Nat.double(i))) : {asc(1n+p, i) == (M.flow(p, True{}, _), M.flow(p, True{}, M.mix(p, False{}, asc(p, 1n+Nat.double(i)), M.gen(p, Nat.double(i))))) : M.Tree(1n+p)}
          %mix_lo_ag(p, False{}, 1n+Nat.double(i), Nat.double(i), lt_succ(Nat.double(i))) : {asc(1n+p, i) == (M.flow(p, True{}, M.gen(p, Nat.double(i))), M.flow(p, True{}, _)) : M.Tree(1n+p)}
          %flow_gen(p, True{}, Nat.double(i)) : {asc(1n+p, i) == (_, M.flow(p, True{}, asc(p, 1n+Nat.double(i)))) : M.Tree(1n+p)}
          %flow_asc(p, True{}, 1n+Nat.double(i)) : {asc(1n+p, i) == (asc(p, Nat.double(i)), _) : M.Tree(1n+p)}
          {==}
        case False{}:
          %sort_gen(p, True{}, 1n+Nat.double(i)) : {M.pick(M.Tree(1n+p), False{}, asc(1n+p, i), M.gen(1n+p, i)) == M.flow(1n+p, False{}, (_, M.sort(p, False{}, M.gen(p, Nat.double(i))))) : M.Tree(1n+p)}
          %sort_gen(p, False{}, Nat.double(i)) : {M.pick(M.Tree(1n+p), False{}, asc(1n+p, i), M.gen(1n+p, i)) == M.flow(1n+p, False{}, (asc(p, 1n+Nat.double(i)), _)) : M.Tree(1n+p)}
          %mix_lo_ag(p, False{}, 1n+Nat.double(i), Nat.double(i), lt_succ(Nat.double(i))) : {M.gen(1n+p, i) == (M.flow(p, False{}, _), M.flow(p, False{}, M.mix(p, True{}, asc(p, 1n+Nat.double(i)), M.gen(p, Nat.double(i))))) : M.Tree(1n+p)}
          %mix_lo_ag(p, True{}, 1n+Nat.double(i), Nat.double(i), lt_succ(Nat.double(i))) : {M.gen(1n+p, i) == (M.flow(p, False{}, asc(p, 1n+Nat.double(i))), M.flow(p, False{}, _)) : M.Tree(1n+p)}
          %flow_asc(p, False{}, 1n+Nat.double(i)) : {M.gen(1n+p, i) == (_, M.flow(p, False{}, M.gen(p, Nat.double(i)))) : M.Tree(1n+p)}
          %flow_gen(p, False{}, Nat.double(i)) : {M.gen(1n+p, i) == (M.gen(p, 1n+Nat.double(i)), _) : M.Tree(1n+p)}
          {==}

# The rule
# --------

# sort on gen's tree: gen's block sorted, with no compare
law sort.gen:
  for +d: Nat
  for +s: Bool
  for +i: Nat
  {M.sort(d, s, M.gen(d, i)) == sorted(d, s, i) : M.Tree(d)}

def sort.gen(d, s, i):
  match s:
    case True{}:
      %sort_gen(d, True{}, i) : {_ == sorted(d, True{}, i) : M.Tree(d)}
      {==}
    case False{}:
      %sort_gen(d, False{}, i) : {_ == sorted(d, False{}, i) : M.Tree(d)}
      {==}
