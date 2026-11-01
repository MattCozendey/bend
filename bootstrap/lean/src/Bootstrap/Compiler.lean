import Bootstrap.Laws
import Bootstrap.GivesRun

-- Compiler
-- ========
--
-- Step 3 of the plan: when the interpreter (Program.lean) runs our own
-- compiler, the main of trusted.bend, on the bytes that the Lean writer
-- writes for a book bk, the bytes w that it gives follow the laws of step 1
-- (spec.bend), in each book B that --verdict accepts for trusted.bend
-- (Book.check B = .ok ()) and that holds trusted.bend's defs (Trusted B):
-- the Bend copy of WASM, run on w, gives only what bk gives (no wrong
-- result), and when bk gives something, it gives it or runs out of memory
-- (no other failure).

open Quan Term

set_option linter.unusedSimpArgs false
set_option maxRecDepth 20000

-- Facts
-- -----

-- the list of bytes that a term reads back as is that term
theorem unbits_eq : unbits n w = some v → w = bits n v := by
  fun_induction unbits n w generalizing v
  all_goals intro h
  all_goals simp_all
  · subst h; rfl
  all_goals rename_i n w ih
  all_goals obtain ⟨a, ha, rfl⟩ := h
  all_goals rw [ih ha]
  all_goals simp [bits, ctor]
  all_goals congr 1; omega

theorem unbytes_eq : unbytes v = some bs → v = bytes bs := by
  fun_induction unbytes v generalizing bs
  all_goals intro h
  all_goals simp_all
  · subst h; rfl
  rename_i w t v l _ hx hv _
  subst h
  rw [unbits_eq hx]
  simp [bytes, list, cell, ctor, toUInt8_toNat hv]

-- in trusted.bend's book, renamed back to impl.bend's names, the copies hold
theorem Trusted.holds (hB : Trusted B) : Holds (Rename.book impl B) := by
  have sub (ds : List Def) (hs : ∀ d ∈ ds, d ∈ evalCopy ++ reader ++ programCopy ++ trustedCopy) :
      Contains (Rename.book impl B) ds :=
    Rename.contains_book impl_ok fun d hd => by
      obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
      exact hB.defs _ (List.mem_map_of_mem (hs d' hd'))
  exact ⟨sub _ (by simp +contextual), sub _ (by simp +contextual), sub _ (by simp +contextual)⟩

-- Program.gives in trusted.bend's book is Lean's Gives
theorem Trusted.gives (hB : Trusted B) :
    Runs B (givesOf (write bk) i n) (Form.some (bytes o)) ↔ Gives bk i o n := by
  rw [← Gives.gives_iff hB.holds, Rename.runs_iff' impl_ok]
  simp [Rename.term_spine, Rename.arg, Rename.term, givesOf]

-- main, our compiler, steps to Compiler.compile on its input
theorem Trusted.main (hB : Trusted B) : Eval B (start p) (compileOf p) := by
  have hk := hB.get (d := «trustedCopy.main») (by simp [trustedCopy])
  simp only [Rename.defn, «trustedCopy.main», impl_main] at hk
  exact Eval.walk (xs := [(Q1, bytes p)]) hk (.cons (fun _ => value_bytes) .nil)
    (by simp [walk, Rename.term, bindsAt, Quan.live, takes, Term.sub, Env.sub, Term.spine, compileOf,
      unspine, Gives.dbytes])

-- the bytes w that the interpreter gives for our compiler on the bytes p
-- are what Compiler.compile(p) runs to
theorem Trusted.compiles (hB : Trusted B) (hw : interp B fuel p = some (w, k)) :
    Runs B (compileOf p) (bytes w) := by
  obtain ⟨⟨v, hs, hv, hu⟩, -⟩ := interp_iff.1 hw
  cases unbytes_eq hu
  have : ∀ u, Steps B k (start p) u → Value B u → Runs B (compileOf p) u := by
    intro u s hv
    cases s with
    | refl => exact (eval_value hB.main hv).elim
    | step e s => cases eval_det e hB.main; exact ⟨_, s, hv⟩
  exact this _ hs hv

-- the run of WASM on Compiler.compile(p) is its run on the module that
-- Compiler.compile(p) runs to
theorem Trusted.wasm (hB : Trusted B) (rc : Runs B c (bytes w))
    (hr : Runs B (wasmRun f w i m) r) : Runs B (wasmOf f c i m) r := by
  have hk := hB.get (d := «trustedCopy.Wasm.run») (by simp [trustedCopy])
  refine Kit.runs_args hk (.v rfl value_nat (.r rfl rc (.v rfl value_bytes (.v rfl plain_u32.value .nil)))) ?_ hr
  intro m hm; simp at hm
  rcases m with _ | _ | _ | _ | m <;> first | omega |
    simp [Rename.defn, Rename.term, «trustedCopy.Wasm.run», walk, bindsAt, Quan.live, takes]

-- The theorems
-- ------------

-- no wrong result: a result that the Bend copy of WASM gives for the module
-- that our compiler writes is one that the book gives
theorem no_wrong_result (hc : Book.check B = .ok ()) (hB : Trusted B)
    (hw : interp B fuel (write bk) = some (w, k))
    (hr : Runs B (wasmRun f w i m) (resultOf o)) :
    ∃ n, Gives bk i o n := by
  obtain ⟨n, r⟩ := law_no_wrong_result hc hB (hB.wasm (hB.compiles hw) hr)
  exact ⟨n, hB.gives.1 r⟩
