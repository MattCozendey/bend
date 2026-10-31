import Bootstrap.Machine.Walk

-- Machine.App
-- ===========
--
-- The moves of a call, and of an application of a value.

open Quan Term

namespace Machine

-- the frames of arguments known to be values where their flag says so
private theorem argFrames_ok (h : ∀ a ∈ ys, argOk bk a) : ∀ f ∈ argFrames ys, f.Ok bk := by
  intro f m
  simp only [argFrames, List.mem_map] at m
  obtain ⟨⟨q, y, l, k⟩, m, rfl⟩ := m
  exact ⟨(h _ m).2, (h _ m).1⟩

-- a call that waits for more arguments: v under vl is a value
theorem callMove_admin (vs : Values bk (xs.map argOf))
    (hv : close v vl = spine (Ref k) (xs.map argOf)) (hvl : vl.Ok bk) (hst : ∀ f ∈ st, f.Ok bk)
    (h : callMove bk k xs st v vl = .admin s') :
    s'.Ok bk ∧ s'.term = plugs st (close v vl) := by
  unfold callMove at h
  split at h
  · cases h
  next d hk =>
    split at h
    · cases h
    next hw =>
      cases h
      have w := walkOpen_walk (bk := bk) (t := d.v) (l := .nil) (xs := xs)
      rw [hw] at w
      have w' := walk_iff.1 w.symm
      refine ⟨⟨⟨?_, hvl⟩, hst⟩, rfl⟩
      rw [hv]; exact .call hk vs w'
    · cases h

-- a call that takes a step
theorem callMove_step (vs : Values bk (xs.map argOf)) (hx : ∀ a ∈ xs, argOk bk a)
    (hst : ∀ f ∈ st, f.Ok bk) (h : callMove bk k xs st v vl = .step s') :
    s'.Ok bk ∧ Eval bk (plugs st (spine (Ref k) (xs.map argOf))) s'.term := by
  unfold callMove at h
  split at h
  · cases h
  next d hk =>
    split at h
    next t l ys hw =>
      cases h
      have w := walkOpen_walk (bk := bk) (t := d.v) (l := .nil) (xs := xs)
      rw [hw] at w
      have w' := walk_iff.1 w.symm
      have ⟨hl, hys⟩ := walkOpen_ok (l := .nil) trivial hx hw
      refine ⟨⟨hl, fun f m => ?_⟩, ?_⟩
      · rcases List.mem_append.1 m with m | m
        · exact argFrames_ok hys f m
        · exact hst f m
      · simp only [State.term, Focus.term, plugs_append, plugs_argFrames]
        exact Eval.plugs hst (.call hk vs w')
    · cases h
    · cases h

-- an App of a value whose spine is on a def is a spine of values on a def
private theorem app_call (hf : Value bk f) (hx : q.live = true → Value bk x)
    (e : unspine f [(q, x)] = (Ref k, xs)) :
    App q f x = spine (Ref k) xs ∧ Values bk xs := by
  have e' := e
  rw [unspine_app] at e'
  simp only [Prod.mk.injEq] at e'
  obtain ⟨e1, rfl⟩ := e'
  have ef : f = spine (Ref k) (unspine f []).2 :=
    spine_unspine (t := f) (ys := []) (by rw [← e1])
  have ⟨k', d, ys, e2, _, vs, _⟩ := value_inv hf (by rw [ef]; exact (spine_ft ⟨rfl, rfl⟩).1)
  have h3 := spine_head e2
  rw [h3] at ef ⊢
  exact ⟨by rw [spine_snoc, ← ef], values_snoc.2 ⟨vs, hx⟩⟩

-- the call of appMove: a spine of values on a def, whose arguments know what
-- is true
private theorem appMove_call (hf : Value bk (close f fl)) (hfl : fl.Ok bk)
    (hx : q.live = true → Value bk (close x xl)) (hxl : xl.Ok bk)
    (e : unspineL f fl [(q, x, xl, q.live)] = (Ref k, kl, ys)) :
    App q (close f fl) (close x xl) = spine (Ref k) (ys.map argOf) ∧
      Values bk (ys.map argOf) ∧ ∀ a ∈ ys, argOk bk a := by
  have u := unspineL_unspine (t := f) (l := fl) (xs := [(q, x, xl, q.live)])
  rw [e] at u
  simp only [close_ref, List.map_cons, List.map_nil, argOf, unspine] at u
  have ⟨hv, vs⟩ := app_call hf hx u
  have ho := unspineL_ok (t := f) (xs := [(q, x, xl, q.live)]) hfl (by simp [hxl])
  rw [e] at ho
  refine ⟨hv, vs, fun a m => ⟨(ho a m).1, fun hk => ?_⟩⟩
  have m' : (a.1, close a.2.1 a.2.2.1) ∈ ys.map argOf := List.mem_map_of_mem m
  exact values_mem vs m' ((ho a m).2 ▸ hk)

-- App q f x, with f under fl a value, and x under xl a value when q is live
theorem appMove_admin (hf : Value bk (close f fl)) (hfl : fl.Ok bk)
    (hx : q.live = true → Value bk (close x xl)) (hxl : xl.Ok bk)
    (hst : ∀ g ∈ st, g.Ok bk) (h : appMove bk q f fl x xl st = .admin s') :
    s'.Ok bk ∧ s'.term = plugs st (App q (close f fl) (close x xl)) := by
  unfold appMove at h
  split at h
  · split at h <;> cases h
  · split at h
    · split at h <;> cases h
    · cases h
  · split at h
    · split at h
      · split at h <;> cases h
      · cases h
    · cases h
  · split at h
    next k kl ys e =>
      have ⟨hv, vs, hys⟩ := appMove_call hf hfl hx hxl e
      have := callMove_admin (vl := .cons x xl q.live fl) vs (by rw [close_shift]; exact hv)
        ⟨hx, hxl, hfl⟩ hst h
      rwa [close_shift] at this
    · cases h

theorem appMove_step (hf : Value bk (close f fl)) (hfl : fl.Ok bk)
    (hx : q.live = true → Value bk (close x xl)) (hxl : xl.Ok bk)
    (hst : ∀ g ∈ st, g.Ok bk) (h : appMove bk q f fl x xl st = .step s') :
    s'.Ok bk ∧ Eval bk (plugs st (App q (close f fl) (close x xl))) s'.term := by
  unfold appMove at h
  split at h
  next p b bl e =>
    split at h
    next hb =>
      cases h
      rw [bindsAtL_eq] at hb
      refine ⟨⟨⟨hx, hxl, resolve_ok' hfl e⟩, hst⟩, ?_⟩
      simp only [State.term, Focus.term, close_cons]
      rw [resolve_eq e, close_lam]
      exact Eval.plugs hst (.beta (bindsAt_iff.1 hb).1 hx (bindsAt_iff.1 hb).2)
    · cases h
  next h' hl e =>
    split at h
    next r a b al e2 =>
      split at h
      next hq =>
        cases h
        have hal := resolve_ok' hxl e2
        have ex : close x xl = Tup r (close a al) (close b al) := by rw [resolve_eq e2, close_tup]
        have ⟨va, vb⟩ := value_tup (ex ▸ hx hq)
        refine ⟨⟨resolve_ok' hfl e, ?_⟩, ?_⟩
        · intro g m
          simp only [List.mem_cons] at m
          rcases m with rfl | rfl | m
          · exact ⟨va, hal⟩
          · exact ⟨fun _ => vb, hal⟩
          · exact hst g m
        · rw [resolve_eq e, close_prj, ex]
          exact Eval.plugs hst (.split hq (ex ▸ hx hq))
      · cases h
    · cases h
  next j h' m hl e =>
    split at h
    next i il e2 =>
      have ex : close x xl = Lab i := by rw [resolve_eq e2, close_lab]
      split at h
      next hq =>
        split at h
        next hij =>
          cases h
          subst hij
          refine ⟨⟨resolve_ok' hfl e, hst⟩, ?_⟩
          rw [resolve_eq e, close_mat, ex]
          exact Eval.plugs hst (.hit hq)
        next hij =>
          cases h
          refine ⟨⟨resolve_ok' hfl e, ?_⟩, ?_⟩
          · intro g m
            simp only [List.mem_cons] at m
            rcases m with rfl | m
            · exact ⟨fun _ => .lab, trivial⟩
            · exact hst g m
          · rw [resolve_eq e, close_mat, ex]
            exact Eval.plugs hst (.miss hq hij)
      · cases h
    · cases h
  · split at h
    next k kl ys e =>
      have ⟨hv, vs, hys⟩ := appMove_call hf hfl hx hxl e
      rw [hv]
      exact callMove_step vs hys hst h
    · cases h

end Machine
