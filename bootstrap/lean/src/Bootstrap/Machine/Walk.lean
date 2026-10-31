import Bootstrap.Machine.Basic

-- Machine.Walk
-- ============
--
-- walkOpen walks as walk (Bootstrap/Interp.lean) does, and what it knows is true.

open Quan Term

namespace Machine

-- the leaf of walkOpen, put together
def leaf : Term × Locals × List MArg → Term
  | (t, l, ys) => spine (close t l) (ys.map argOf)

-- walkOpen gives walk's outcome, with its leaf left open
theorem walkOpen_walk : (walkOpen bk t l xs).map (·.map leaf) =
    _root_.walk bk t l.terms (xs.map argOf) := by
  fun_induction walkOpen bk t l xs
  case case1 hb ih =>
    rw [bindsAtL_eq] at hb
    rw [ih, terms_cons]; simp [argOf, _root_.walk, hb]
  case case2 hb =>
    rw [bindsAtL_eq] at hb
    simp [argOf, _root_.walk, hb]
  case case3 e hq ih =>
    rw [ih]; simp [argOf, resolve_eq e, close_tup, _root_.walk, hq]
  case case4 e hq =>
    simp [argOf, resolve_eq e, close_tup, _root_.walk, hq]
  case case5 h l q x xl k xs hr =>
    rcases e : resolve x xl with ⟨u, ul⟩
    have hc := resolve_eq e
    cases u
    case Tup => exact (hr _ _ _ _ e).elim
    case Var i => obtain rfl := resolve_var e; simp [argOf, hc, close_nil, _root_.walk, takes]
    all_goals simp [argOf, hc, close_eq (l := ul), sub, _root_.walk, takes]
  case case6 e hq ih =>
    rw [ih]; simp [argOf, resolve_eq e, close_lab, _root_.walk, hq]
  case case7 e hq hij ih =>
    rw [ih]; simp [argOf, resolve_eq e, close_lab, _root_.walk, hq, hij]
  case case8 e hq =>
    simp [argOf, resolve_eq e, close_lab, _root_.walk, hq]
  case case10 ht ih =>
    rw [ih]; simp [argOf_eq, localAt_eq, _root_.walk, ht, subst]
  case case11 ht =>
    simp [leaf, _root_.walk, ht, close_eq, subst]
  case case9 j h m l q x xl k xs hr =>
    rcases e : resolve x xl with ⟨u, ul⟩
    have hc := resolve_eq e
    cases u
    case Lab => exact (hr _ _ e).elim
    case Var i => obtain rfl := resolve_var e; simp [argOf, hc, close_nil, _root_.walk, takes]
    all_goals simp [argOf, hc, close_eq (l := ul), sub, _root_.walk, takes]
  case case12 t l xs h1 h2 h3 h4 ht hx =>
    obtain rfl := List.isEmpty_iff.1 hx
    cases t <;> simp_all [_root_.walk, takes]
  case case13 t l xs h1 h2 h3 h4 ht hx =>
    rcases xs with _ | ⟨⟨q, x, xl, k⟩, xs⟩
    · simp at hx
    cases t
    all_goals first
      | exact (h1 _ _ _ _ _ _ _ rfl rfl).elim
      | exact (h2 _ _ _ _ _ _ rfl rfl).elim
      | exact (h3 _ _ _ _ _ _ _ _ rfl rfl).elim
      | simp_all [_root_.walk, takes]
  case case14 t l xs h1 h2 h3 h4 ht =>
    rcases xs with _ | ⟨⟨q, x, xl, k⟩, xs⟩
    · cases t <;> simp_all [_root_.walk, takes, leaf, close_eq, subst]
    cases t
    case App q' f y => cases y <;> simp_all [_root_.walk, takes, leaf, close_eq, subst]
    all_goals simp_all [_root_.walk, takes, leaf, close_eq, subst]

-- the leaf's locals and the arguments left know what is true
theorem walkOpen_ok (hl : l.Ok bk) (hx : ∀ a ∈ xs, argOk bk a)
    (h : walkOpen bk t l xs = some (some (u, l', ys))) : l'.Ok bk ∧ ∀ a ∈ ys, argOk bk a := by
  fun_induction walkOpen bk t l xs
  case case1 p f l q x xl k xs hb ih =>
    have ha := hx _ List.mem_cons_self
    exact ih ⟨ha.2, ha.1, hl⟩ (fun a m => hx a (.tail _ m)) h
  case case3 h' l q x xl k xs r a b al e hq ih =>
    have ha := hx _ List.mem_cons_self
    have hal := resolve_ok' ha.1 e
    have hv : k = true → Value bk (Tup r (close a al) (close b al)) := fun hk => by
      rw [← close_tup, ← resolve_eq e]; exact ha.2 hk
    refine ih hl ?_ h
    intro c m
    rcases List.mem_cons.1 m with rfl | m
    · refine ⟨hal, fun hk => ?_⟩
      simp only [Bool.and_eq_true] at hk
      exact (value_tup (hv hk.1)).1 hk.2
    rcases List.mem_cons.1 m with rfl | m
    · exact ⟨hal, fun hk => (value_tup (hv hk)).2⟩
    · exact hx c (.tail _ m)
  case case6 ih => exact ih hl (fun a m => hx a (.tail _ m)) h
  case case7 ih =>
    refine ih hl ?_ h
    intro a m
    rcases List.mem_cons.1 m with rfl | m
    · exact ⟨trivial, fun _ => .lab⟩
    · exact hx a (.tail _ m)
  case case10 ih =>
    refine ih hl ?_ h
    intro a m
    rcases List.mem_cons.1 m with rfl | m
    · exact localAt_ok hl
    · exact hx a m
  all_goals simp only [Option.some.injEq, reduceCtorEq] at h
  all_goals first
    | exact h.elim
    | (cases h; exact ⟨hl, hx⟩)

end Machine
