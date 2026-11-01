import Bootstrap.Rename
import Bootstrap.Copy.Trusted

-- Impl
-- ====
--
-- The names that `bend -o` gives impl.bend's defs and labels in the book of
-- a file that imports it (trusted.bend): impl.k for each name k of impl.bend's
-- own, and Base's names as they are. impl is the renaming of Rename that
-- swaps k and impl.k for each such k (trustedCopy.names, as the book of
-- trusted.bend names them), and keeps the names of `kept`: Base's names that
-- the theorems name.

open Quan Term

-- Base's names that the theorems name, which impl keeps
def kept : List String :=
  ["main", "Q0", "Q1", "Q2", "()", "Tuple", "Exists", "Sigma", "Sigma.arms",
   "Zero", "Succ", "Nat", "Nat.arms", "Nil", "Con", "List", "List.arms", "U32", "U32.arms",
   "WNil", "WCon", "Word", "Word.Nil", "Word.Nil.arms", "Word.Con", "Word.Con.arms",
   "False", "True", "Bool", "Bool.arms", "None", "Some", "Maybe", "Maybe.arms",
   "Or", "Either", "Either.arms", "Inl", "Inr"]

-- t, without the prefix "impl.", when it has it
def unimpl (s : String) : Option String :=
  if "impl.".toList.isPrefixOf s.toList then some (String.ofList (s.toList.drop "impl.".toList.length))
  else none

-- t is a name of impl.bend's own, which the book of trusted.bend names impl.t
def Moves (t : String) : Prop :=
  t ∉ kept ∧ "impl." ++ t ∉ kept ∧ t ∈ trustedCopy.names ∧ "impl." ++ t ∉ trustedCopy.names

instance : DecidablePred Moves := fun _ => inferInstanceAs (Decidable (_ ∧ _))

def impl (s : String) : String :=
  if Moves s then "impl." ++ s
  else match unimpl s with
    | some t => if Moves t then t else s
    | none => s

theorem unimpl_append : unimpl ("impl." ++ t) = some t := by
  have : "impl.".toList.isPrefixOf ("impl." ++ t).toList = true := by
    rw [String.toList_append, List.isPrefixOf_iff_prefix]; exact List.prefix_append _ _
  unfold unimpl; split
  · rw [String.toList_append, List.drop_left, String.ofList_toList]
  · contradiction

theorem unimpl_some (h : unimpl s = some t) : s = "impl." ++ t := by
  unfold unimpl at h
  split at h
  · rename_i hp
    cases h
    rw [List.isPrefixOf_iff_prefix, List.prefix_iff_eq_append] at hp
    apply String.ext
    rw [String.toList_append]
    simp only [String.toList_ofList]
    exact hp.symm
  · cases h

theorem impl_impl (s : String) : impl (impl s) = s := by
  by_cases hs : Moves s
  · have : ¬ Moves ("impl." ++ s) := fun h => hs.2.2.2 h.2.2.1
    simp [impl, hs, this, unimpl_append]
  · cases hu : unimpl s with
    | none => simp [impl, hs, hu]
    | some t =>
      by_cases ht : Moves t
      · have e := unimpl_some hu
        subst e
        simp [impl, hs, unimpl_append, ht]
      · simp [impl, hs, hu, ht]

-- impl keeps the names of kept
theorem impl_kept (h : s ∈ kept) : impl s = s := by
  have hs : ¬ Moves s := fun m => m.1 h
  cases hu : unimpl s with
  | none => simp [impl, hs, hu]
  | some t =>
    have : ¬ Moves t := fun m => m.2.1 (unimpl_some hu ▸ h)
    simp [impl, hs, hu, this]

theorem impl_ok : Rename.Ok impl where
  inv := impl_impl
  qs := fun s h => impl_kept (by simp only [QS, List.mem_cons, List.not_mem_nil, or_false] at h
                                 rcases h with rfl | rfl | rfl <;> decide)
