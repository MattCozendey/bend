import Bootstrap.Machine.Walk

-- Machine.App
-- ===========
--
-- The moves of a call, and of an application of a value.

open Quan Term

namespace Machine

-- no locals know anything false
private theorem nil_ok : Locals.Ok bk [] := by intro _ m; cases m

-- stripping the flags gives back the arguments
private theorem strip_flags (ys : List Arg) :
    (ys.map fun (q, y) => (q, y, q.live)).map (fun (q, x, _) => (q, x)) = ys := by
  induction ys with
  | nil => rfl
  | cons a ys ih => simp only [List.map_cons] at ih ⊢; rw [ih]

-- the flags q.live of values are true only on values
private theorem flags_ok (vs : Values bk ys) :
    ∀ a ∈ ys.map (fun (q, y) => (q, y, q.live)), a.2.2 = true → Value bk a.2.1 := by
  induction ys with
  | nil => simp
  | cons b ys ih =>
    obtain ⟨q, y⟩ := b
    cases vs with
    | cons hx vs =>
      intro a m
      simp only [List.map_cons, List.mem_cons] at m
      rcases m with rfl | m
      · exact hx
      · exact ih vs a m

-- the frames of arguments known to be values where their flag says so
private theorem argFrames_ok (h : ∀ a ∈ ys, a.2.2 = true → Value bk a.2.1) :
    ∀ f ∈ argFrames ys, f.Ok bk := by
  intro f m
  simp only [argFrames, List.mem_map] at m
  obtain ⟨⟨q, y, k⟩, m, rfl⟩ := m
  exact h _ m

-- the term an unspine took apart
private theorem spine_unspine (h : unspine t ys = (u, zs)) : spine t ys = spine u zs := by
  induction t generalizing ys with
  | App q f x ihf _ => exact ihf h
  | _ => simp only [unspine, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl

-- a call that waits for more arguments: v is a value
theorem callMove_admin (vs : Values bk ys) (hv : v = spine (Ref k) ys) (hst : ∀ f ∈ st, f.Ok bk)
    (h : callMove bk k (ys.map fun (q, y) => (q, y, q.live)) st v = .admin s') :
    s'.Ok bk ∧ s'.term = plugs st v := by
  unfold callMove at h
  split at h
  · cases h
  next d hk =>
    split at h
    · cases h
    next hw =>
      cases h
      have w := walkOpen_walk (bk := bk) (t := d.v) (l := [])
        (xs := ys.map fun (q, y) => (q, y, q.live))
      rw [hw, strip_flags] at w
      have w' := walk_iff.1 w.symm
      subst hv
      exact ⟨⟨.call hk vs w', hst⟩, rfl⟩
    · cases h

-- a call that takes a step
theorem callMove_step (vs : Values bk ys) (hv : v = spine (Ref k) ys) (hst : ∀ f ∈ st, f.Ok bk)
    (h : callMove bk k (ys.map fun (q, y) => (q, y, q.live)) st v = .step s') :
    s'.Ok bk ∧ Eval bk (plugs st v) s'.term := by
  unfold callMove at h
  split at h
  · cases h
  next d hk =>
    split at h
    next t l ys' hw =>
      cases h
      have w := walkOpen_walk (bk := bk) (t := d.v) (l := [])
        (xs := ys.map fun (q, y) => (q, y, q.live))
      rw [hw, strip_flags] at w
      have w' := walk_iff.1 w.symm
      have ⟨hl, hys⟩ := walkOpen_ok nil_ok (flags_ok vs) hw
      refine ⟨⟨hl, fun f m => ?_⟩, ?_⟩
      · rcases List.mem_append.1 m with m | m
        · exact argFrames_ok hys f m
        · exact hst f m
      · subst hv
        simp only [State.term, Focus.term, plugs_append, plugs_argFrames]
        exact Eval.plugs hst (.call hk vs w')
    · cases h
    · cases h

-- an App of a value that unspines to a call is a spine of values on a def
private theorem app_call (hf : Value bk f) (hx : q.live = true → Value bk x)
    (e : unspine (App q f x) [] = (Ref k, xs)) :
    App q f x = spine (Ref k) xs ∧ Values bk xs := by
  have e' : unspine f [(q, x)] = (Ref k, xs) := e
  rw [unspine_app] at e'
  simp only [Prod.mk.injEq] at e'
  obtain ⟨e1, rfl⟩ := e'
  have ef : f = spine (Ref k) (unspine f []).2 :=
    spine_unspine (t := f) (ys := []) (by rw [← e1])
  have ⟨k', d, ys, e2, _, vs, _⟩ := value_inv hf (by rw [ef]; exact (spine_ft ⟨rfl, rfl⟩).1)
  have h3 := spine_head e2
  rw [h3] at ef ⊢
  exact ⟨by rw [spine_snoc, ← ef], values_snoc.2 ⟨vs, hx⟩⟩

-- App q f x, with f a value, and x a value when q is live
theorem appMove_admin (hf : Value bk f) (hx : q.live = true → Value bk x)
    (hst : ∀ g ∈ st, g.Ok bk) (h : appMove bk q f x st = .admin s') :
    s'.Ok bk ∧ s'.term = plugs st (App q f x) := by
  unfold appMove at h
  split at h
  · split at h <;> cases h
  · split at h <;> cases h
  · split at h
    · split at h <;> cases h
    · cases h
  · split at h
    next k xs e =>
      have ⟨hv, vs⟩ := app_call hf hx e
      exact callMove_admin vs hv hst h
    · cases h

theorem appMove_step (hf : Value bk f) (hx : q.live = true → Value bk x)
    (hst : ∀ g ∈ st, g.Ok bk) (h : appMove bk q f x st = .step s') :
    s'.Ok bk ∧ Eval bk (plugs st (App q f x)) s'.term := by
  unfold appMove at h
  split at h
  · split at h
    next hb =>
      cases h
      refine ⟨⟨fun a m hk => ?_, hst⟩, ?_⟩
      · simp only [List.mem_singleton] at m
        subst m
        exact hx hk
      · simp only [State.term, Focus.term, close_one]
        exact Eval.plugs hst (.beta (bindsAt_iff.1 hb).1 hx (bindsAt_iff.1 hb).2)
    · cases h
  · split at h
    next l =>
      cases h
      have ⟨va, vb⟩ := value_tup (hx l)
      refine ⟨⟨nil_ok, ?_⟩, ?_⟩
      · intro g m
        simp only [List.mem_cons] at m
        rcases m with rfl | rfl | m
        · exact va
        · exact fun _ => vb
        · exact hst g m
      · simp only [State.term, Focus.term, close, List.isEmpty_nil, ite_true]
        exact Eval.plugs hst (.split l (hx l))
    · cases h
  · split at h
    next l =>
      split at h
      next e =>
        cases h
        subst e
        refine ⟨⟨nil_ok, hst⟩, ?_⟩
        simp only [State.term, Focus.term, close, List.isEmpty_nil, ite_true]
        exact Eval.plugs hst (.hit l)
      next e =>
        cases h
        refine ⟨⟨nil_ok, ?_⟩, ?_⟩
        · intro g m
          simp only [List.mem_cons] at m
          rcases m with rfl | m
          · exact fun _ => .lab
          · exact hst g m
        · simp only [State.term, Focus.term, close, List.isEmpty_nil, ite_true]
          exact Eval.plugs hst (.miss l e)
    · cases h
  · split at h
    next k xs e =>
      have ⟨hv, vs⟩ := app_call hf hx e
      exact callMove_step vs hv hst h
    · cases h

end Machine
