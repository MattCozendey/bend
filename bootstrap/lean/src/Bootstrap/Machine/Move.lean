import Bootstrap.Machine.App

-- Machine.Move
-- ============
--
-- A move that is no step keeps the term, and a move that is a step is one step
-- of Eval. Each keeps what the state knows true.

open Quan Term

namespace Machine

-- a move that is no step keeps the term, and what the state knows true
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
      · rename_i x xl hx
        have := get?_ok hf hx
        refine ⟨⟨⟨this.1 rfl, this.2⟩, hst⟩, ?_⟩
        simp only [State.term, Focus.term, close_var, get?_close hx]
      · rename_i x xl hx
        refine ⟨⟨(get?_ok hf hx).2, hst⟩, ?_⟩
        simp only [State.term, Focus.term, close_var, get?_close hx]
    case Ref k =>
      have := callMove_admin (xs := []) (k := k) (v := Ref k) (vl := .nil) .nil rfl trivial hst h
      refine ⟨this.1, this.2.trans ?_⟩
      simp only [State.term, Focus.term, close_ref]
    case Ann => cases h
    case Let q v f =>
      split at h <;> cases h
      rename_i hq
      exact ⟨⟨hf, List.forall_mem_cons.2 ⟨⟨hq, hf⟩, hst⟩⟩, by
        simp only [State.term, Focus.term, close_eq, Term.sub, plugs, List.foldl, Frame.plug]⟩
    case Tup q a b =>
      split at h
      · cases h
        rename_i hv
        simp only [Bool.and_eq_true] at hv
        refine ⟨⟨⟨value_iff.1 hv.2, trivial⟩, hst⟩, ?_⟩
        simp only [State.term, Focus.term, noVars_close hv.1]
      split at h <;> cases h
      · rename_i hq
        exact ⟨⟨hf, List.forall_mem_cons.2 ⟨⟨hq, hf⟩, hst⟩⟩, by
          simp only [State.term, Focus.term, close_tup, plugs, List.foldl, Frame.plug]⟩
      · rename_i hq
        exact ⟨⟨hf, List.forall_mem_cons.2 ⟨⟨fun h => absurd h hq, hf⟩, hst⟩⟩, by
          simp only [State.term, Focus.term, close_tup, plugs, List.foldl, Frame.plug]⟩
    all_goals cases h
    all_goals first
      | exact ⟨⟨hf, List.forall_mem_cons.2 ⟨hf, hst⟩⟩, by
          simp only [State.term, Focus.term, close_eq, Term.sub, plugs, List.foldl, Frame.plug]⟩
      | exact ⟨⟨hf, List.forall_mem_cons.2 ⟨⟨hf, hf⟩, hst⟩⟩, by
          simp only [State.term, Focus.term, close_eq, Term.sub, plugs, List.foldl, Frame.plug]⟩
      | exact ⟨⟨⟨by simp only [close_eq, Term.sub]; constructor, trivial⟩, hst⟩, by
          simp only [State.term, Focus.term, close_eq, Term.sub]⟩
      | exact ⟨⟨⟨by simp only [close_eq, Term.sub]; constructor, hf⟩, hst⟩, rfl⟩
  | ret v vl =>
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
          exact appMove_admin hf.1 hf.2 (fun h => absurd h hq) hg hs h
      case appVal q x l k =>
        split at h
        · cases h
          rename_i hq
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hq
          exact ⟨⟨hg.2, List.forall_mem_cons.2 ⟨⟨hq.1, hf⟩, hs⟩⟩, rfl⟩
        · rename_i hq
          simp only [Bool.and_eq_true, Bool.not_eq_true', not_and, Bool.not_eq_false] at hq
          exact appMove_admin hf.1 hf.2 (fun h => hg.1 (hq h)) hg.2 hs h
      case appFun q f fl => exact appMove_admin hg.2.1 hg.2.2 (fun _ => hf.1) hf.2 hs h
      case letIn => split at h <;> cases h
      case tupB q b l =>
        cases h; exact ⟨⟨hg.2, List.forall_mem_cons.2 ⟨⟨fun _ => hf.1, hf.2⟩, hs⟩⟩, rfl⟩
      case tupA q a al => cases h; exact ⟨⟨⟨Value.tup hg.1 hf.1, trivial⟩, hs⟩, rfl⟩
      case rwt => split at h <;> cases h
      case minB b l =>
        cases h
        refine ⟨⟨hg, List.forall_mem_cons.2 ⟨?_, hs⟩⟩, ?_⟩
        · simp only [Frame.Ok]
          split
          · exact .lab
          · exact hf.1
        · simp only [State.term, Focus.term, plugs, List.foldl, Frame.plug]
          split
          · rename_i e; rw [resolve_eq e, close_lab]
          · rfl
      case minA a => split at h <;> (try split at h) <;> cases h

-- a move that is a step is one step of Eval, and keeps what the state knows true
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
      have := callMove_step (xs := []) (k := k) (v := Ref k) (vl := .nil) .nil nofun hst h
      refine ⟨this.1, ?_⟩
      simp only [State.term, Focus.term, close_ref]
      exact this.2
    case Ann x T =>
      cases h
      refine ⟨⟨hf, hst⟩, Eval.plugs hst ?_⟩
      simp only [Focus.term, close_eq, Term.sub]
      exact .ann
    case Let q v f =>
      split at h <;> cases h
      rename_i hq
      refine ⟨⟨⟨nofun, hf, hf⟩, hst⟩, Eval.plugs hst ?_⟩
      simp only [Focus.term, close_cons]
      simp only [close_eq, Term.sub]
      exact .unlet (fun h => absurd h hq) (fun e => by subst e; exact absurd rfl hq)
    case Tup => split at h <;> (try split at h) <;> cases h
    all_goals cases h
  | ret v vl =>
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
          exact appMove_step hf.1 hf.2 (fun h => absurd h hq) hg hs h
      case appVal q x l k =>
        split at h
        · cases h
        · rename_i hq
          simp only [Bool.and_eq_true, Bool.not_eq_true', not_and, Bool.not_eq_false] at hq
          exact appMove_step hf.1 hf.2 (fun h => hg.1 (hq h)) hg.2 hs h
      case appFun q f fl => exact appMove_step hg.2.1 hg.2.2 (fun _ => hf.1) hf.2 hs h
      case letIn q f l =>
        split at h <;> cases h
        rename_i hq
        refine ⟨⟨⟨fun _ => hf.1, hf.2, hg.2⟩, hs⟩, Eval.plugs hs ?_⟩
        simp only [Focus.term, close_cons]
        refine .unlet (fun _ => hf.1) (fun e => data_iff.1 ?_)
        subst e
        simpa [dataAt_eq] using hq
      case tupB => cases h
      case tupA => cases h
      case rwt P f l =>
        split at h <;> cases h
        rename_i hv
        have e := resolve_close (t := v) (l := vl)
        rw [hv, close_rfl] at e
        refine ⟨⟨hg, hs⟩, ?_⟩
        simp only [State.term, Focus.term, plugs, List.foldl, Frame.plug]
        rw [← e]
        exact Eval.plugs hs .cast
      case minB => cases h
      case minA a =>
        split at h <;> try (split at h)
        all_goals cases h
        rename_i i j e hq
        have ev := resolve_close (t := v) (l := vl)
        rw [e, close_lab] at ev
        refine ⟨⟨trivial, hs⟩, ?_⟩
        simp only [State.term, Focus.term, plugs, List.foldl, Frame.plug]
        rw [← ev]
        exact Eval.plugs hs (.meet hq.1 hq.2)

end Machine
