import Bootstrap.Trusted

-- Laws
-- ====
--
-- What the laws of spec.bend say in a book B that --verdict accepts and that
-- holds trusted.bend's defs (Trusted.lean): each law, applied to the Bend
-- values of its arguments and to a proof of its "if" part (a run, by
-- runs_rfl), is a closed, live, typed proof, and its "there is" part gives a
-- witness (exists_conv), a Nat (canon_nat), at which its sides convert, so
-- run (conv_runs).

open Quan Term

set_option linter.unusedSimpArgs false

-- Compiler.compile(p), at quantity 2, as the laws apply it
def compileOf (p : List UInt8) : Term := App Q2 (Ref (impl "Compiler.compile")) (bytes p)

-- Wasm.run(f, c, i, m)
def wasmOf (f : Nat) (c : Term) (i : List UInt8) (m : UInt32) : Term :=
  spine (Ref (impl "Wasm.run")) [(Q1, Form.nat f), (Q1, c), (Q1, bytes i), (Q1, Form.u32 m)]

-- Program.gives(p, i, n)
def givesOf (p i : List UInt8) (n : Nat) : Term :=
  spine (Ref (impl "Program.gives")) [(Q1, bytes p), (Q1, bytes i), (Q1, Form.nat n)]

theorem data_value (h : Data t) : Value B t := by
  induction h with
  | lab => exact .lab
  | rfl => exact .rfl
  | tup _ _ iha ihb => exact .tup iha ihb

theorem typed_gives (hB : Trusted B) (cl : Book.Closed B) : Typed B [] (givesOf p i n) maybeList := by
  have hT := hB.types
  have := Typed.ref (Γ := []) (σ := Var) (hB.get (d := «programCopy.Program.gives») (by simp [programCopy]))
  rw [sub_var] at this
  simp [Rename.defn, Rename.term, «programCopy.Program.gives»] at this
  have := Typed.app (Typed.app (Typed.app this (typed_bytes hT cl (bs := p))) (typed_bytes hT cl (bs := i)))
    (typed_nat hT cl (n := n))
  simpa [Term.inst, Term.sub, Subst.one, Subst.up, Term.ren, givesOf, spine, maybeList, listU32] using this

theorem law_no_wrong_result (hc : Book.check B = .ok ()) (hB : Trusted B)
    (hr : Runs B (wasmOf f (compileOf p) i m) (resultOf o)) :
    ∃ n, Runs B (givesOf p i n) (Form.some (bytes o)) := by
  have hT := hB.types
  have ⟨wt, lv⟩ := book_check B hc
  have cl := lv.1
  have h0 := hB.law (l := «trustedCopy.spec.no_wrong_result») (by simp [laws])
  simp [Rename.term, «trustedCopy.spec.no_wrong_result»] at h0
  have h1 := Typed.app (Typed.app (Typed.app (Typed.app (Typed.app h0 (typed_nat hT cl (n := f)))
    (typed_bytes hT cl (bs := p))) (typed_bytes hT cl (bs := i))) (typed_u32' hT cl (m := m)))
    (typed_bytes hT cl (bs := o))
  simp [Term.inst, Term.sub, Subst.one, Subst.up, Term.ren] at h1
  have hr' : Runs B (App Q1 (App Q1 (App Q1 (App Q1 (Ref (impl "Wasm.run")) (Form.nat f))
      (App Q2 (Ref (impl "Compiler.compile")) (bytes p))) (bytes i)) (Form.u32 m))
      (Tup Q1 (Lab (impl "Wasm.Outcome.result")) (Tup Q1 (bytes o) (Lab "()"))) := hr
  have h2 := Typed.app h1 (runs_rfl hc hr' (T := Ref (impl "Wasm.Outcome")))
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, Term.ren, sub_bytes, ren_bytes] at h2
  obtain ⟨d, hd, -⟩ := hB.declares «trustedCopy.spec.no_wrong_result» (by simp [laws])
  have hN : Typed B [] (Ref "Nat") T2 := by
    have := Typed.ref (Γ := []) (σ := Var) (hT «evalCopy.Nat» (by simp [baseTypes]))
    simpa [sub_var, «evalCopy.Nat»] using this
  have pa : ∀ a ∈ [(Q2, Form.nat f), (Q2, bytes p), (Q2, bytes i), (Q2, Form.u32 m), (Q2, bytes o),
      (Q1, Rfl)], Plain a.2 := by
    simp [plain_nat, plain_bytes, plain_u32, Plain.rfl]
  obtain ⟨w, dw, tw, cw⟩ := exists_conv hc hB.exists_ (closed_call pa) (live_call' hd pa) h2 hN
  obtain ⟨n, rfl⟩ := canon_nat wt hT cl (data_value dw) tw
  simp only [Term.inst, Term.sub, Subst.one, sub_bytes] at cw
  refine ⟨n, conv_runs hc ?_ ?_ (typed_gives hB cl) (typed_maybeList hT) ?_ cw⟩
  · exact closed_call (by simp [plain_nat, plain_bytes])
  · exact live_call' (hB.get (d := «programCopy.Program.gives») (by simp [programCopy]))
      (by simp [plain_nat, plain_bytes])
  · exact plain_ctor (by simp [plain_bytes])
