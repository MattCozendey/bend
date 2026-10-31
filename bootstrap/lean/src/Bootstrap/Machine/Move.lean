import Bootstrap.Machine.App

-- Machine.Move
-- ============
--
-- A move that is no step keeps the term, and a move that is a step is one step
-- of Eval. Each keeps what the state knows true.

open Quan Term

namespace Machine

theorem move_admin (hs : s.Ok bk) (h : move bk s = .admin s') : s'.Ok bk ∧ s'.term = s.term := by
  obtain ⟨fc, st⟩ := s
  obtain ⟨hf, hst⟩ := hs
  simp only at hst
  cases fc with
  | ev t l =>
    simp only [Focus.Ok] at hf
    cases t <;> simp only [move] at h
    case Var i =>
      split at h <;> cases h
      · rename_i x hx
        refine ⟨⟨hf _ (List.mem_of_getElem? hx) rfl, hst⟩, ?_⟩
        simp only [State.term, Focus.term, close_eq, Term.sub, subst_get hx]
      · rename_i x hx
        refine ⟨⟨by simp [Focus.Ok, Locals.Ok], hst⟩, ?_⟩
        simp only [State.term, Focus.term, close_eq, Term.sub, subst_get hx, subst_nil, sub_var]
    case Ref k =>
      have := callMove_admin (ys := []) (k := k) (v := Ref k) .nil rfl hst h
      refine ⟨this.1, this.2.trans ?_⟩
      simp only [State.term, Focus.term, close_eq, Term.sub]
    case Ann => cases h
    case Let q v f =>
      split at h <;> cases h
      rename_i hq
      exact ⟨⟨hf, List.forall_mem_cons.2 ⟨⟨hq, hf⟩, hst⟩⟩, by
        simp only [State.term, Focus.term, close_eq, Term.sub, plugs, List.foldl, Frame.plug]⟩
    case Tup q a b =>
      split at h <;> cases h
      · rename_i hq
        exact ⟨⟨hf, List.forall_mem_cons.2 ⟨⟨hq, hf⟩, hst⟩⟩, by
          simp only [State.term, Focus.term, close_eq, Term.sub, plugs, List.foldl, Frame.plug]⟩
      · rename_i hq
        exact ⟨⟨hf, List.forall_mem_cons.2 ⟨fun h => absurd h hq, hst⟩⟩, by
          simp only [State.term, Focus.term, close_eq, Term.sub, plugs, List.foldl, Frame.plug]⟩
    all_goals cases h
    all_goals first
      | exact ⟨⟨hf, List.forall_mem_cons.2 ⟨hf, hst⟩⟩, by
          simp only [State.term, Focus.term, close_eq, Term.sub, plugs, List.foldl, Frame.plug]⟩
      | exact ⟨⟨by simp only [Focus.Ok, close_eq, Term.sub]; constructor, hst⟩, rfl⟩
  | ret v =>
    simp only [Focus.Ok] at hf
    cases st with
    | nil => simp only [move] at h; cases h
    | cons g st =>
      have hg := hst g List.mem_cons_self
      have hs := fun g' h => hst g' (List.mem_cons_of_mem g h)
      clear hst
      cases g <;> simp only [move] at h <;> simp only [Frame.Ok] at hg
      case appArg q x l =>
        split at h
        · cases h
          rename_i hq
          exact ⟨⟨hg, List.forall_mem_cons.2 ⟨⟨hq, hf⟩, hs⟩⟩, rfl⟩
        · rename_i hq
          exact appMove_admin hf (fun h => absurd h hq) hs h
      case appVal q x k =>
        split at h
        · cases h
          rename_i hq
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hq
          refine ⟨⟨by simp [Focus.Ok, Locals.Ok], List.forall_mem_cons.2 ⟨⟨hq.1, hf⟩, hs⟩⟩, ?_⟩
          simp only [State.term, Focus.term, close_eq, subst_nil, sub_var, plugs, List.foldl,
            Frame.plug]
        · rename_i hq
          simp only [Bool.and_eq_true, Bool.not_eq_true', not_and, Bool.not_eq_false] at hq
          exact appMove_admin hf (fun h => hg (hq h)) hs h
      case appFun q f => exact appMove_admin hg.2 (fun _ => hf) hs h
      case letIn => split at h <;> cases h
      case tupB q b l => cases h; exact ⟨⟨hg.2, List.forall_mem_cons.2 ⟨fun _ => hf, hs⟩⟩, rfl⟩
      case tupA q a => cases h; exact ⟨⟨Value.tup hg hf, hs⟩, rfl⟩
      case rwt => split at h <;> cases h
      case minB b l => cases h; exact ⟨⟨hg, List.forall_mem_cons.2 ⟨hf, hs⟩⟩, rfl⟩
      case minA a => split at h <;> (try split at h) <;> cases h

theorem move_step (hs : s.Ok bk) (h : move bk s = .step s') : s'.Ok bk ∧ Eval bk s.term s'.term := by
  obtain ⟨fc, st⟩ := s
  obtain ⟨hf, hst⟩ := hs
  simp only at hst
  cases fc with
  | ev t l =>
    simp only [Focus.Ok] at hf
    cases t <;> simp only [move] at h
    case Var i => split at h <;> cases h
    case Ref k =>
      have := callMove_step (ys := []) (k := k) (v := Ref k) .nil rfl hst h
      refine ⟨this.1, ?_⟩
      have e : close (Ref k) l = Ref k := by simp only [close_eq, Term.sub]
      simpa only [State.term, Focus.term, e] using this.2
    case Ann x T =>
      cases h
      refine ⟨⟨hf, hst⟩, Eval.plugs hst ?_⟩
      simp only [Focus.term, close_eq, Term.sub]
      exact .ann
    case Let q v f =>
      split at h <;> cases h
      rename_i hq
      refine ⟨⟨?_, hst⟩, Eval.plugs hst ?_⟩
      · simp only [Focus.Ok, Locals.Ok, List.forall_mem_cons]
        exact ⟨by simp, hf⟩
      · simp only [Focus.term, close_cons]
        simp only [close_eq, Term.sub]
        exact .unlet (fun h => absurd h hq) (fun e => by subst e; exact absurd rfl hq)
    case Tup => split at h <;> cases h
    all_goals cases h
  | ret v =>
    simp only [Focus.Ok] at hf
    cases st with
    | nil => simp only [move] at h; cases h
    | cons g st =>
      have hg := hst g List.mem_cons_self
      have hs := fun g' h => hst g' (List.mem_cons_of_mem g h)
      clear hst
      cases g <;> simp only [move] at h <;> simp only [Frame.Ok] at hg
      case appArg q x l =>
        split at h
        · cases h
        · rename_i hq
          exact appMove_step hf (fun h => absurd h hq) hs h
      case appVal q x k =>
        split at h
        · cases h
        · rename_i hq
          simp only [Bool.and_eq_true, Bool.not_eq_true', not_and, Bool.not_eq_false] at hq
          exact appMove_step hf (fun h => hg (hq h)) hs h
      case appFun q f => exact appMove_step hg.2 (fun _ => hf) hs h
      case letIn q f l =>
        split at h <;> cases h
        rename_i hq
        refine ⟨⟨?_, hs⟩, Eval.plugs hs ?_⟩
        · simp only [Focus.Ok, Locals.Ok, List.forall_mem_cons]
          exact ⟨fun _ => hf, hg.2⟩
        · simp only [Focus.term, close_cons]
          refine .unlet (fun _ => hf) (fun e => data_iff.1 ?_)
          subst e
          simpa using hq
      case tupB => cases h
      case tupA => cases h
      case rwt P f l =>
        split at h <;> cases h
        rename_i hv
        subst hv
        exact ⟨⟨hg, hs⟩, Eval.plugs hs .cast⟩
      case minB => cases h
      case minA a =>
        split at h <;> try (split at h)
        all_goals cases h
        rename_i i j hq
        refine ⟨⟨by simp [Focus.Ok, Locals.Ok], hs⟩, Eval.plugs hs ?_⟩
        simp only [Focus.term, close_eq, subst_nil, sub_var]
        exact .meet hq.1 hq.2

end Machine
