import Contract.Spec

-- Shut
-- ====
--
-- The proof of claim 6 (shut): Eval from a Pure def meets no opaque def.
-- Each Eval step keeps each def name in the def's shut set.

open Quan Term Contract

namespace Interp

-- Names S t: each def name in t is in S.
def Names (S : String → Prop) (t : Term) : Prop :=
  ∀ j ∈ refs t, S j

theorem refs_ren (t : Term) : refs (ren r t) = refs t := by
  induction t generalizing r <;> simp [ren, refs, *]

theorem names_up (h : ∀ i, Names S (σ i)) : ∀ i, Names S (Subst.up σ i)
  | 0 => by simp [Names, Subst.up, refs]
  | i + 1 => by simpa [Names, Subst.up, refs_ren] using h i

theorem names_sub (hs : ∀ i, Names S (σ i)) (ht : Names S t) : Names S (sub σ t) := by
  induction t generalizing σ <;>
    simp only [Names, sub, refs, List.mem_append, or_imp, forall_and] at ht ⊢
  case Var i => exact hs i
  case Ref => exact ht
  case Ann ihx ihT => exact ⟨ihx hs ht.1, ihT hs ht.2⟩
  case Let ihv ihf => exact ⟨ihv hs ht.1, ihf (names_up hs) ht.2⟩
  case Typ ih => exact ih hs ht
  case Min iha ihb => exact ⟨iha hs ht.1, ihb hs ht.2⟩
  case All ihA ihB => exact ⟨ihA hs ht.1, ihB (names_up hs) ht.2⟩
  case Lam ih => exact ih (names_up hs) ht
  case App ihf ihx => exact ⟨ihf hs ht.1, ihx hs ht.2⟩
  case Sig ihA ihB => exact ⟨ihA hs ht.1, ihB (names_up hs) ht.2⟩
  case Tup iha ihb => exact ⟨iha hs ht.1, ihb hs ht.2⟩
  case Prj ih => exact ih hs ht
  case Mat ihh ihm => exact ⟨ihh hs ht.1, ihm hs ht.2⟩
  case Eql iha ihb ihT => exact ⟨⟨iha hs ht.1.1, ihb hs ht.1.2⟩, ihT hs ht.2⟩
  case Rwt ihe ihP ihf => exact ⟨⟨ihe hs ht.1.1, ihP (names_up (names_up hs)) ht.1.2⟩, ihf hs ht.2⟩
  all_goals simp

theorem names_inst (hf : Names S f) (hv : Names S v) : Names S (inst f v) :=
  names_sub (fun | 0 => hv | _ + 1 => by simp [Names, Subst.one, refs]) hf

theorem names_spine : Names S (spine t xs) ↔ Names S t ∧ ∀ a ∈ xs, Names S a.2 := by
  induction xs generalizing t with
  | nil => simp [spine]
  | cons a xs ih =>
    simp only [spine, ih, List.mem_cons, forall_eq_or_imp]
    simp [Names, refs, or_imp, forall_and, and_assoc]

theorem names_env (he : ∀ x ∈ e, Names S x) : ∀ i, Names S (Env.sub e i) := by
  induction e with
  | nil => intro i; simp [Env.sub, Names, refs]
  | cons x e ih =>
    intro i; cases i
    · exact he x (by simp)
    · exact ih (fun y hy => he y (by simp [hy])) _

-- the leaf of a walk names only what the tree, the environment and the spine
-- name
theorem names_walk (w : Walk bk t e xs o) (ht : Names S t) (he : ∀ x ∈ e, Names S x)
    (hx : ∀ a ∈ xs, Names S a.2) : ∀ u, o = some u → Names S u := by
  induction w with
  | lam _ _ _ ih =>
    refine ih (by simpa [Names, refs] using ht) ?_ (fun p hp => hx p (List.mem_cons_of_mem _ hp))
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hx _ (List.mem_cons.2 (Or.inl rfl))
    · exact he y hy
  | prj _ _ ih =>
    refine ih (by simpa [Names, refs] using ht) he ?_
    have h0 := hx _ (List.mem_cons.2 (Or.inl rfl))
    simp only [Names, refs, List.mem_append, or_imp, forall_and] at h0
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h0.1
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h0.2
    · exact hx p (List.mem_cons_of_mem _ hp)
  | hit _ _ ih =>
    simp only [Names, refs, List.mem_append, or_imp, forall_and] at ht
    exact ih ht.1 he (fun p hp => hx p (List.mem_cons_of_mem _ hp))
  | miss _ _ _ ih =>
    simp only [Names, refs, List.mem_append, or_imp, forall_and] at ht
    exact ih ht.2 he hx
  | app _ _ ih =>
    simp only [Names, refs, List.mem_append, or_imp, forall_and] at ht
    refine ih ht.1 he ?_
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact names_env he _
    · exact hx p hp
  | need => intro u h; cases h
  | done =>
    rintro u ⟨⟩
    exact names_spine.2 ⟨names_sub (names_env he) ht, hx⟩

-- an Eval step keeps each name in S, when the body of each def in S names
-- only defs in S
theorem names_eval (hS : ∀ j, S j → ∃ d, bk.get j = some d ∧ Names S d.v)
    (h : Eval bk t u) (ht : Names S t) : Names S u := by
  induction h with
  | call hd _ w =>
    obtain ⟨hk, hx⟩ := names_spine.1 ht
    obtain ⟨d, hd', hv⟩ := hS _ (hk _ (List.mem_singleton.2 rfl))
    cases hd.symm.trans hd'
    exact names_walk w hv (by simp) hx _ rfl
  | beta =>
    simp only [Names, refs, List.mem_append, or_imp, forall_and] at ht
    exact names_inst ht.1 ht.2
  | unlet =>
    simp only [Names, refs, List.mem_append, or_imp, forall_and] at ht
    exact names_inst ht.2 ht.1
  | @meet i j _ _ =>
    rcases qmin_view (Lab i) (Lab j) with e | ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, _, e⟩ <;>
      simp [e, Names, refs]
  | _ => simp_all [Names, refs, or_imp, forall_and]

theorem names_evals (hS : ∀ j, S j → ∃ d, bk.get j = some d ∧ Names S d.v)
    (h : Evals bk t u) (ht : Names S t) : Names S u := by
  induction h with
  | refl => exact ht
  | step e _ ih => exact ih (names_eval hS e ht)

theorem grow_mem (h : k ∈ ks) : k ∈ grow bk n ks := by
  induction n generalizing ks with
  | zero => exact h
  | succ n ih => simp only [grow]; exact ih (List.mem_append_left _ h)

theorem claim_shut : Claim.shut := by
  intro bk k u hp ev
  unfold Contract.Pure at hp
  split at hp
  · simp at hp
  · simp only [Bool.and_eq_true] at hp
    have sh := hp.2
    simp only [shut, List.all_eq_true] at sh
    have hS : ∀ j, j ∈ grow bk bk.length [k] →
        ∃ d, bk.get j = some d ∧ d.o = false ∧ Names (· ∈ grow bk bk.length [k]) d.v := by
      intro j hj
      have := sh j hj
      split at this
      · rename_i d hd
        simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at this
        exact ⟨d, hd, this.1, fun i hi => by simpa using this.2 i hi⟩
      · simp at this
    have hu := names_evals (fun j hj => (hS j hj).imp fun _ h => ⟨h.1, h.2.2⟩) ev
      (fun j hj => by simp only [refs, List.mem_singleton] at hj; subst hj; exact grow_mem (by simp))
    intro j hj
    obtain ⟨d, hd, ho, -⟩ := hS j (hu j hj)
    exact ⟨d, hd, ho⟩

end Interp
