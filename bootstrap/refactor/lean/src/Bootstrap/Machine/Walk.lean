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
    _root_.walk bk t (l.map (·.1)) (xs.map fun (q, x, _) => (q, x)) := by
  fun_induction walkOpen bk t l xs
  case case11 t l xs h1 h2 h3 h4 ht hx =>
    rcases xs with _ | ⟨⟨q, x, k⟩, xs⟩
    · simp at hx
    cases t <;> try cases x
    all_goals first
      | exact (h1 _ _ _ _ _ _ rfl rfl).elim
      | exact (h2 _ _ _ _ _ _ _ rfl rfl).elim
      | exact (h3 _ _ _ _ _ _ _ rfl rfl).elim
      | simp_all [_root_.walk, takes]
  case case12 t l xs h1 h2 h3 h4 ht =>
    rcases xs with _ | ⟨⟨q, x, k⟩, xs⟩
    · cases t <;> simp_all [_root_.walk, takes, leaf, close_eq, subst]
    cases t <;> try cases x
    all_goals first
      | exact (h1 _ _ _ _ _ _ rfl rfl).elim
      | exact (h2 _ _ _ _ _ _ _ rfl rfl).elim
      | exact (h3 _ _ _ _ _ _ _ rfl rfl).elim
      | simp_all [_root_.walk, takes, leaf, close_eq, subst]
  all_goals simp_all [_root_.walk, leaf, close_eq, localAt_eq, subst]

theorem walkOpen_ok (hl : Locals.Ok bk l) (hx : ∀ a ∈ xs, a.2.2 = true → Value bk a.2.1)
    (h : walkOpen bk t l xs = some (some (u, l', ys))) :
    Locals.Ok bk l' ∧ ∀ a ∈ ys, a.2.2 = true → Value bk a.2.1 := by
  fun_induction walkOpen bk t l xs
  case case1 p f q x k xs l hb ih =>
    refine ih ?_ (fun a ha => hx a (.tail _ ha)) h
    intro y hy hk
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hx _ (.head _) hk
    · exact hl y hy hk
  case case3 hq ih =>
    refine ih hl ?_ h
    intro a ha hk
    rcases List.mem_cons.1 ha with rfl | ha
    · simp only [Bool.and_eq_true] at hk
      exact (value_tup (hx _ (.head _) hk.1)).1 hk.2
    rcases List.mem_cons.1 ha with rfl | ha
    · exact (value_tup (hx _ (.head _) hk)).2
    · exact hx a (.tail _ ha) hk
  case case5 ih => exact ih hl (fun a ha => hx a (.tail _ ha)) h
  case case6 ih =>
    refine ih hl ?_ h
    intro a ha hk
    rcases List.mem_cons.1 ha with rfl | ha
    · exact .lab
    · exact hx a (.tail _ ha) hk
  case case8 ih =>
    refine ih hl ?_ h
    intro a ha hk
    rcases List.mem_cons.1 ha with rfl | ha
    · exact localAt_ok hl hk
    · exact hx a ha hk
  all_goals simp only [Option.some.injEq, reduceCtorEq] at h
  all_goals first
    | exact h.elim
    | (cases h; exact ⟨hl, hx⟩)

end Machine
