import Bootstrap.Values
import Bootstrap.Copy.Reader
import Bootstrap.Copy.Exists
import Bootstrap.Copy.Program
import Bootstrap.Copy.Need

-- Trusted
-- =======
--
-- The book of trusted.bend (bootstrap/bend/src/compiler), whose main is our
-- own compiler, and which holds the laws of spec.bend with their proofs: what
-- the theorems of Compiler.lean ask of a book B that the interpreter runs.
-- B holds the Lean copies of impl.bend's defs that the theorems need, under
-- the names that trusted.bend's book gives them (Impl.lean), its main and
-- Wasm.run, Base's Exists, and a def of the type of each law: a theorem
-- needs a law's proof to exist, not to be a given one.

open Quan Term

set_option linter.unusedSimpArgs false

-- the copies of impl.bend's defs (from its own book), and of trusted.bend's
-- main and Wasm.run (with impl.bend's names as in impl.bend's book), under
-- the names that trusted.bend's book gives them
def trustedDefs : List Def := (evalCopy ++ reader ++ programCopy ++ needCopy ++ trustedCopy).map (Rename.defn impl)

-- the laws of spec.bend, by name and type (with impl.bend's names as in
-- impl.bend's book)
def laws : List (String × Term) :=
  [«trustedCopy.spec.no_wrong_result», «trustedCopy.spec.no_other_failure», «trustedCopy.spec.enough_memory»]

-- B has a def named l.1, of the type l.2 under the names of trusted.bend's book
def Declares (B : Book) (l : String × Term) : Prop :=
  ∃ d, Book.get B l.1 = some d ∧ d.T = Rename.term impl l.2

structure Trusted (B : Book) : Prop where
  defs : Contains B trustedDefs
  exists_ : Contains B existsCopy
  declares : ∀ l ∈ laws, Declares B l

-- The terms of the theorems
-- -------------------------

-- the Bend copy of WASM (impl.bend's Wasm.run), run with the fuel f on the
-- module w, the input i and m pages of memory
def wasmRun (f : Nat) (w i : List UInt8) (m : UInt32) : Term :=
  spine (Ref (impl "Wasm.run")) [(Q1, Form.nat f), (Q1, bytes w), (Q1, bytes i), (Q1, Form.u32 m)]

-- Wasm.Outcome.result{o}
def resultOf (o : List UInt8) : Term := ctor (impl "Wasm.Outcome.result") [bytes o]

-- Wasm.Outcome.out_of_memory{}
def outOfMemory : Term := ctor (impl "Wasm.Outcome.out_of_memory") []

-- Facts
-- -----

@[simp] theorem ren_bytes : Term.ren r (bytes bs) = bytes bs := plain_bytes.ren
@[simp] theorem sub_bytes : Term.sub s (bytes bs) = bytes bs := plain_bytes.sub
@[simp] theorem ren_nat : Term.ren r (Form.nat n) = Form.nat n := plain_nat.ren
@[simp] theorem sub_nat : Term.sub s (Form.nat n) = Form.nat n := plain_nat.sub
@[simp] theorem ren_u32 : Term.ren r (Form.u32 m) = Form.u32 m := plain_u32.ren
@[simp] theorem sub_u32 : Term.sub s (Form.u32 m) = Form.u32 m := plain_u32.sub

-- a def of the copies, under its name in trusted.bend's book
theorem Trusted.get (hB : Trusted B) (hd : d ∈ evalCopy ++ reader ++ programCopy ++ needCopy ++ trustedCopy) :
    Book.get B (impl d.k) = some (Rename.defn impl d) :=
  hB.defs _ (List.mem_map_of_mem hd)

-- impl renames none of Base's types
theorem baseTypes_kept (hd : d ∈ baseTypes) : Rename.defn impl d = d := by
  simp only [baseTypes, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Rename.defn, Rename.term, «evalCopy.Nat», «evalCopy.Nat.arms», «evalCopy.List»,
      «evalCopy.List.arms», «evalCopy.U32», «evalCopy.U32.arms», «evalCopy.Word», «evalCopy.Word.Nil»,
      «evalCopy.Word.Nil.arms», «evalCopy.Word.Con», «evalCopy.Word.Con.arms», «evalCopy.Bool»,
      «evalCopy.Bool.arms», «evalCopy.Maybe», «evalCopy.Maybe.arms»]

theorem Trusted.types (hB : Trusted B) : Contains B baseTypes := by
  intro d hd
  have h1 : d ∈ evalCopy ++ reader ++ programCopy ++ needCopy ++ trustedCopy := by
    simp only [baseTypes, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [evalCopy]
  have h2 := baseTypes_kept hd
  have := hB.get h1
  rwa [h2, show impl d.k = d.k from congrArg Def.k h2] at this

-- a closed, live call on plain arguments
theorem closed_call (h : ∀ a ∈ xs, Plain a.2) : Term.Closed (spine (Ref k) xs) :=
  closed_spine.2 ⟨fun _ => rfl, fun a ha => (h a ha).closed⟩

theorem live_call' (hk : Book.get B k = some d) (h : ∀ a ∈ xs, Plain a.2) :
    Term.Live B (spine (Ref k) xs) := by
  refine live_spine.2 ⟨?_, fun a ha _ => (h a ha).live⟩
  obtain ⟨j, hj⟩ := index_of_get hk
  simp [Term.Live, Term.live, called, unspine, hj, index_lt hj]

-- the type of a law, from its def
theorem Trusted.law {l : String × Term} (hB : Trusted B) (hl : l ∈ _root_.laws) :
    Typed B [] (Ref l.1) (Rename.term impl l.2) := by
  obtain ⟨d, hd, hT⟩ := hB.declares l hl
  have := Typed.ref (Γ := []) (σ := Var) hd
  rwa [sub_var, hT] at this
