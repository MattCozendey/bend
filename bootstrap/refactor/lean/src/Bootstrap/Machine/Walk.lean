import Bootstrap.Machine.Basic

-- Machine.Walk
-- ============
--
-- walkOpen walks as walk (Bootstrap/Interp.lean) does, and what it knows is true.

open Quan Term

namespace Machine

-- the leaf of walkOpen, put together
def leaf : Term × Locals × List MArg → Term
  | (t, l, ys) => spine (close t l) (ys.map fun (q, y, _) => (q, y))

theorem walkOpen_walk : (walkOpen bk t l xs).map (·.map leaf) =
    _root_.walk bk t (l.map (·.1)) (xs.map fun (q, x, _) => (q, x)) := sorry

theorem walkOpen_ok (hl : Locals.Ok bk l) (hx : ∀ a ∈ xs, a.2.2 = true → Value bk a.2.1)
    (h : walkOpen bk t l xs = some (some (u, l', ys))) :
    Locals.Ok bk l' ∧ ∀ a ∈ ys, a.2.2 = true → Value bk a.2.1 := sorry

end Machine
