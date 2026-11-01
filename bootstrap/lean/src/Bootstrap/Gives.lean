import Bootstrap.EvalSteps
import Bootstrap.Read
import Bootstrap.Kit
import Bootstrap.Program
import Bootstrap.Copy.Program

-- Gives
-- =====
--
-- The Bend Program.gives (impl.bend), on the bytes that the Lean writer
-- writes for a book bk, gives what Lean's Gives says that bk gives: through
-- the reader (read_write), the copy of Eval (copy_steps, vals_copy), and the
-- copies of Program.start and Program.unbytes, which give the forms of Lean's
-- start and unbytes.

open Quan Term

set_option linter.unusedSimpArgs false
set_option maxRecDepth 20000

-- the copies that Program.gives needs
structure Holds (B : Book) : Prop where
  eval : Contains B evalCopy
  reader : Contains B reader
  program : Contains B programCopy

namespace Gives

theorem dterm : data (Form.term t) = true := data_iff.2 data_term
theorem ddefs : data (Form.defs ds) = true := data_iff.2 data_defs
theorem dname : data (Form.name k) = true := data_iff.2 data_bytes
theorem dbytes : data (bytes bs) = true := data_iff.2 data_bytes
theorem dnat : data (Form.nat n) = true := data_iff.2 data_nat
theorem dbits : data (bits n v) = true := data_iff.2 data_bits
theorem dcell : data (cell b) = true := data_iff.2 data_cell

theorem _root_.Holds.get (h : Holds B) (hd : d ∈ programCopy := by simp [programCopy]) :
    Book.get B d.k = some d := h.program d hd

-- ByteArray.toList.loop puts the bytes from i after the reversed r (as EvalSteps' own)
theorem toList_loop (bs : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  fun_induction ByteArray.toList.loop bs i r with
  | case1 i r hi ih =>
    rw [ih]
    have hi' : i < bs.data.toList.length := by rw [Array.length_toList]; exact hi
    rw [List.drop_eq_getElem_cons hi']
    simp [ByteArray.get!, hi]
  | case2 i r hi =>
    have hi' : bs.data.toList.length ≤ i := by rw [Array.length_toList]; exact Nat.le_of_not_lt hi
    simp [List.drop_eq_nil_of_le hi']

-- the name k is the list of its UTF-8 bytes
theorem name_bytes (h : k = String.ofList cs) (e : (List.utf8Encode cs).data.toList = bs) :
    Form.name k = bytes bs := by
  subst h; unfold Form.name; congr 1
  simp only [String.toUTF8, String.toByteArray_ofList, ByteArray.toList, toList_loop,
    List.reverse_nil, List.nil_append, List.drop_zero, e]

macro "name_bytes" : tactic => `(tactic| exact name_bytes rfl (by decide))

theorem name_unit : Form.name "()" = bytes [40, 41] := by name_bytes
theorem name_nil : Form.name "Nil" = bytes [78, 105, 108] := by name_bytes
theorem name_con : Form.name "Con" = bytes [67, 111, 110] := by name_bytes
theorem name_u32 : Form.name "U32" = bytes [85, 51, 50] := by name_bytes
theorem name_wnil : Form.name "WNil" = bytes [87, 78, 105, 108] := by name_bytes
theorem name_wcon : Form.name "WCon" = bytes [87, 67, 111, 110] := by name_bytes
theorem name_true : Form.name "True" = bytes [84, 114, 117, 101] := by name_bytes
theorem name_false : Form.name "False" = bytes [70, 97, 108, 115, 101] := by name_bytes
theorem name_main : Form.name "main" = bytes [109, 97, 105, 110] := by name_bytes

-- a list literal of the refs ks
def litTerm : List String → Term
  | [] => ctor "Nil" []
  | k :: ks => ctor "Con" [Ref k, litTerm ks]

theorem lits_run : (ps : List (String × UInt8)) → (∀ p ∈ ps, Runs B (Ref p.1) (cell p.2)) →
    Runs B (litTerm (ps.map (·.1))) (bytes (ps.map (·.2)))
  | [], _ => .refl (value_ctor nofun)
  | p :: ps, h => by
    simp only [List.map_cons, litTerm, bytes, list, ctor, List.foldr]
    exact Kit.run_tup (.refl .lab) (Kit.run_tup (h p (by simp))
      (Kit.run_tup (by simpa [bytes, list, ctor] using lits_run ps (fun q hq => h q (by simp [hq])))
        (.refl .lab)))

-- a def with no λ runs to its body, when its body is a value
theorem body_run (hk : Book.get B k = some d) (hv : Value B d.v) (ht : takes d.v = false)
    (hn : ∀ q f x, d.v ≠ App q f (Var x)) : Runs B (Ref k) d.v := by
  refine Kit.call (xs := []) hk .nil ?_ (.refl hv)
  rw [walk_done (by rw [node_of (fun q f x e => hn q f x e)]; exact ht)]
  simp [Term.spine, env_nil, sub_var]

theorem body_run' (hk : Book.get B k = some d) (r : Runs B d.v v) (ht : takes d.v = false)
    (hn : ∀ q f x, d.v ≠ App q f (Var x)) : Runs B (Ref k) v := by
  refine Kit.call (xs := []) hk .nil ?_ r
  rw [walk_done (by rw [node_of (fun q f x e => hn q f x e)]; exact ht)]
  simp [Term.spine, env_nil, sub_var]

theorem lit_run (hk : Book.get B d.k = some d) (hv : d.v = cell b) : Runs B (Ref d.k) (cell b) := by
  have := body_run hk (hv ▸ value_cell) (by rw [hv]; rfl) (by rw [hv]; simp [cell, ctor])
  rwa [hv] at this

theorem name_run {ps : List (String × UInt8)} (h : Holds B) (hd : d ∈ programCopy) (hv : d.v = litTerm (ps.map (·.1)))
    (hr : ∀ p ∈ ps, Runs B (Ref p.1) (cell p.2)) (hn : Form.name k = bytes (ps.map (·.2))) :
    Runs B (Ref d.k) (Form.name k) := by
  rw [hn]
  refine body_run' (h.get hd) (hv ▸ lits_run ps hr) ?_ ?_
  · rw [hv]; cases ps <;> rfl
  · rw [hv]; cases ps <;> simp [litTerm, ctor]

macro "lit" d:term : tactic =>
  `(tactic| exact lit_run (d := $d) (Holds.get (by assumption) (by simp [programCopy])) (by decide))

theorem names_run (h : Holds B) :
    Runs B (Ref "Program.name.unit") (Form.name "()") ∧
    Runs B (Ref "Program.name.nil") (Form.name "Nil") ∧
    Runs B (Ref "Program.name.con") (Form.name "Con") ∧
    Runs B (Ref "Program.name.u32") (Form.name "U32") ∧
    Runs B (Ref "Program.name.wnil") (Form.name "WNil") ∧
    Runs B (Ref "Program.name.wcon") (Form.name "WCon") ∧
    Runs B (Ref "Program.name.true") (Form.name "True") ∧
    Runs B (Ref "Program.name.false") (Form.name "False") ∧
    Runs B (Ref "Program.name.main") (Form.name "main") := by
  have l40 : Runs B (Ref "U32.lit40") (cell 40) := by lit «programCopy.U32.lit40»
  have l41 : Runs B (Ref "U32.lit41") (cell 41) := by lit «programCopy.U32.lit41»
  have l78 : Runs B (Ref "U32.lit78") (cell 78) := by lit «programCopy.U32.lit78»
  have l105 : Runs B (Ref "U32.lit105") (cell 105) := by lit «programCopy.U32.lit105»
  have l108 : Runs B (Ref "U32.lit108") (cell 108) := by lit «programCopy.U32.lit108»
  have l67 : Runs B (Ref "U32.lit67") (cell 67) := by lit «programCopy.U32.lit67»
  have l111 : Runs B (Ref "U32.lit111") (cell 111) := by lit «programCopy.U32.lit111»
  have l110 : Runs B (Ref "U32.lit110") (cell 110) := by lit «programCopy.U32.lit110»
  have l85 : Runs B (Ref "U32.lit85") (cell 85) := by lit «programCopy.U32.lit85»
  have l51 : Runs B (Ref "U32.lit51") (cell 51) := by lit «programCopy.U32.lit51»
  have l50 : Runs B (Ref "U32.lit50") (cell 50) := by
    exact lit_run (h.eval «evalCopy.U32.lit50» (by simp [evalCopy])) (by decide)
  have l87 : Runs B (Ref "U32.lit87") (cell 87) := by lit «programCopy.U32.lit87»
  have l84 : Runs B (Ref "U32.lit84") (cell 84) := by lit «programCopy.U32.lit84»
  have l114 : Runs B (Ref "U32.lit114") (cell 114) := by lit «programCopy.U32.lit114»
  have l117 : Runs B (Ref "U32.lit117") (cell 117) := by lit «programCopy.U32.lit117»
  have l101 : Runs B (Ref "U32.lit101") (cell 101) := by lit «programCopy.U32.lit101»
  have l70 : Runs B (Ref "U32.lit70") (cell 70) := by lit «programCopy.U32.lit70»
  have l97 : Runs B (Ref "U32.lit97") (cell 97) := by lit «programCopy.U32.lit97»
  have l115 : Runs B (Ref "U32.lit115") (cell 115) := by lit «programCopy.U32.lit115»
  have l109 : Runs B (Ref "U32.lit109") (cell 109) := by lit «programCopy.U32.lit109»
  exact ⟨name_run h (d := «programCopy.Program.name.unit») (by simp [programCopy]) (ps := [("U32.lit40", 40), ("U32.lit41", 41)]) rfl
      (by simp [l40, l41]) name_unit,
    name_run h (d := «programCopy.Program.name.nil») (by simp [programCopy]) (ps := [("U32.lit78", 78), ("U32.lit105", 105), ("U32.lit108", 108)]) rfl
      (by simp [l78, l105, l108]) name_nil,
    name_run h (d := «programCopy.Program.name.con») (by simp [programCopy]) (ps := [("U32.lit67", 67), ("U32.lit111", 111), ("U32.lit110", 110)]) rfl
      (by simp [l67, l111, l110]) name_con,
    name_run h (d := «programCopy.Program.name.u32») (by simp [programCopy]) (ps := [("U32.lit85", 85), ("U32.lit51", 51), ("U32.lit50", 50)]) rfl
      (by simp [l85, l51, l50]) name_u32,
    name_run h (d := «programCopy.Program.name.wnil») (by simp [programCopy]) (ps := [("U32.lit87", 87), ("U32.lit78", 78), ("U32.lit105", 105), ("U32.lit108", 108)]) rfl
      (by simp [l87, l78, l105, l108]) name_wnil,
    name_run h (d := «programCopy.Program.name.wcon») (by simp [programCopy]) (ps := [("U32.lit87", 87), ("U32.lit67", 67), ("U32.lit111", 111), ("U32.lit110", 110)]) rfl
      (by simp [l87, l67, l111, l110]) name_wcon,
    name_run h (d := «programCopy.Program.name.true») (by simp [programCopy]) (ps := [("U32.lit84", 84), ("U32.lit114", 114), ("U32.lit117", 117), ("U32.lit101", 101)]) rfl
      (by simp [l84, l114, l117, l101]) name_true,
    name_run h (d := «programCopy.Program.name.false») (by simp [programCopy]) (ps := [("U32.lit70", 70), ("U32.lit97", 97), ("U32.lit108", 108), ("U32.lit115", 115), ("U32.lit101", 101)]) rfl
      (by simp [l70, l97, l108, l115, l101]) name_false,
    name_run h (d := «programCopy.Program.name.main») (by simp [programCopy]) (ps := [("U32.lit109", 109), ("U32.lit97", 97), ("U32.lit105", 105), ("U32.lit110", 110)]) rfl
      (by simp [l109, l97, l105, l110]) name_main⟩

-- a constructor literal runs field by field
theorem ctor0 : Runs B (ctor k []) (ctor k []) := .refl (value_ctor nofun)

theorem ctor1 (ra : Runs B a a') :
    Runs B (Tup Q1 (Lab k) (Tup Q1 a (Lab "()"))) (ctor k [a']) :=
  Kit.run_tup (.refl .lab) (Kit.run_tup ra (.refl .lab))

theorem ctor2 (ra : Runs B a a') (rb : Runs B b b') :
    Runs B (Tup Q1 (Lab k) (Tup Q1 a (Tup Q1 b (Lab "()")))) (ctor k [a', b']) :=
  Kit.run_tup (.refl .lab) (Kit.run_tup ra (Kit.run_tup rb (.refl .lab)))

theorem ctor3 (ra : Runs B a a') (rb : Runs B b b') (rc : Runs B c c') :
    Runs B (Tup Q1 (Lab k) (Tup Q1 a (Tup Q1 b (Tup Q1 c (Lab "()"))))) (ctor k [a', b', c']) :=
  Kit.run_tup (.refl .lab) (Kit.run_tup ra (Kit.run_tup rb (Kit.run_tup rc (.refl .lab))))

theorem vterm : Runs B (Form.term t) (Form.term t) := .refl value_term
theorem vq1 : Runs B (ctor "Quan.Q1" []) (ctor "Quan.Q1" []) := ctor0

theorem fields_run {xs : List Term} (h : Holds B) :
    Runs B (App Q1 (Ref "Program.fields") (list (xs.map Form.term))) (Form.term (xs.foldr (Tup Q1) (Lab "()"))) := by
  have hk := h.get (d := «programCopy.Program.fields»)
  induction xs with
  | nil =>
    refine Kit.call (xs := [(Q1, _)]) hk (.cons (fun _ => value_ctor nofun) .nil) ?_
      (ctor1 (names_run h).1)
    simp [«programCopy.Program.fields», walk, list, ctor, bindsAt, Quan.live, Quan.fld, takes,
      Term.sub, Env.sub, Term.spine]
  | cons x xs ih =>
    refine Kit.call (xs := [(Q1, _)]) hk (.cons (fun _ => value_list (by simp [value_term])) .nil) ?_
      (ctor3 vq1 vterm ih)
    simp [«programCopy.Program.fields», walk, list, ctor, bindsAt, Quan.live, Quan.fld, takes,
      Term.sub, Env.sub, Term.spine]

theorem ctor_run {xs : List Term} (h : Holds B) (rk : Runs B K (Form.name k)) (rl : Runs B L (list (xs.map Form.term))) :
    Runs B (App Q1 (App Q1 (Ref "Program.ctor") K) L) (Form.term (ctor k xs)) := by
  have hk := h.get (d := «programCopy.Program.ctor»)
  show Runs B (spine (Ref "Program.ctor") [(Q1, K), (Q1, L)]) _
  refine Kit.runs_call hk (.r rfl rk (.r rfl rl .nil)) ?_ ?_ (ctor3 vq1 (ctor1 (.refl value_bytes)) (fields_run h))
  · intro m hm; simp at hm
    rcases m with _ | _ | m <;> first | omega | simp [«programCopy.Program.ctor», walk, takes, bindsAt, Quan.live]
  · simp [«programCopy.Program.ctor», walk, takes, bindsAt, Quan.live, Term.sub, Env.sub, Term.spine]; rfl

macro "walks" d:term : tactic =>
  `(tactic| simp [$d:term, walk, list, ctor, bits, cell, bytes, bindsAt, Quan.live, Quan.fld, takes,
    Term.sub, Env.sub, Term.spine, Form.nat, data, dbits, dnat, dcell, dbytes])

theorem bit_run (h : Holds B) (c : Prop) [Decidable c] :
    Runs B (App Q1 (Ref "Program.bit") (ctor (if c then "True" else "False") []))
      (Form.term (ctor (if c then "True" else "False") [])) := by
  have hk := h.get (d := «programCopy.Program.bit»)
  by_cases hc : c
  · simp only [hc, ite_true]
    refine Kit.call (xs := [(Q1, _)]) hk (.cons (fun _ => value_ctor nofun) .nil) ?_
      (ctor_run (xs := []) h (names_run h).2.2.2.2.2.2.1 ctor0)
    walks «programCopy.Program.bit»
  · simp only [hc, ite_false]
    refine Kit.call (xs := [(Q1, _)]) hk (.cons (fun _ => value_ctor nofun) .nil) ?_
      (ctor_run (xs := []) h (names_run h).2.2.2.2.2.2.2.1 ctor0)
    walks «programCopy.Program.bit»

theorem word_run (h : Holds B) :
    Runs B (App Q1 (App Q1 (Ref "Program.word") (Form.nat n)) (bits n v)) (Form.term (bits n v)) := by
  have hk := h.get (d := «programCopy.Program.word»)
  induction n generalizing v with
  | zero =>
    show Runs B (spine (Ref _) [(Q1, _), (Q1, _)]) _
    refine Kit.call hk (.cons (fun _ => value_nat) (.cons (fun _ => value_bits) .nil)) ?_
      (ctor_run (xs := []) h (names_run h).2.2.2.2.1 ctor0)
    walks «programCopy.Program.word»
  | succ n ih =>
    show Runs B (spine (Ref _) [(Q1, _), (Q1, _)]) _
    refine Kit.call hk (.cons (fun _ => value_nat) (.cons (fun _ => value_bits) .nil)) ?_
      (ctor_run (xs := [_, _]) h (names_run h).2.2.2.2.2.1 (ctor2 (bit_run h _) (ctor2 ih ctor0)))
    walks «programCopy.Program.word»

-- the bitwise and of the low n bits of v and w
def andBits : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n + 1, v, w => (if v % 2 = 1 ∧ w % 2 = 1 then 1 else 0) + 2 * andBits n (v / 2) (w / 2)

theorem bits_and : bits (n + 1) (andBits (n + 1) v w) =
    ctor "WCon" [Form.bool (decide (v % 2 = 1) && decide (w % 2 = 1)), bits n (andBits n (v / 2) (w / 2))] := by
  have h1 : andBits (n + 1) v w % 2 = 1 ↔ (v % 2 = 1 ∧ w % 2 = 1) := by
    simp only [andBits]; split <;> omega
  have h2 : andBits (n + 1) v w / 2 = andBits n (v / 2) (w / 2) := by
    simp only [andBits]; split <;> omega
  rw [bits, h2]
  by_cases hv : v % 2 = 1 <;> by_cases hw : w % 2 = 1 <;> simp [hv, hw, Form.bool, h1]

theorem form_bool (c : Prop) [Decidable c] : ctor (if c then "True" else "False") [] = Form.bool (decide c) := by
  by_cases hc : c <;> simp [hc, Form.bool]

theorem word_and_run (h : Holds B) :
    Runs B (spine (Ref "Word.and") [(Q1, Form.nat n), (Q1, bits n v), (Q1, bits n w)])
      (bits n (andBits n v w)) := by
  have hk := h.get (d := «programCopy.Word.and»)
  induction n generalizing v w with
  | zero =>
    refine Kit.call hk (.cons (fun _ => value_nat) (.cons (fun _ => value_bits) (.cons (fun _ => value_bits) .nil))) ?_
      ctor0
    walks «programCopy.Word.and»
  | succ n ih =>
    rw [bits_and]
    refine Kit.call hk (.cons (fun _ => value_nat) (.cons (fun _ => value_bits) (.cons (fun _ => value_bits) .nil))) ?_
      (ctor2 (EvalCopy.and_copy h.eval) ih)
    walks «programCopy.Word.and»
    constructor <;> split <;> simp_all [Form.bool, ctor]

theorem u32_and_run (h : Holds B) (rx : Runs B x (ctor "U32" [bits 32 v])) (ry : Runs B y (ctor "U32" [bits 32 w])) :
    Runs B (App Q1 (App Q1 (Ref "U32.and") x) y) (ctor "U32" [bits 32 (andBits 32 v w)]) := by
  have hk := h.get (d := «programCopy.U32.and»)
  show Runs B (spine (Ref _) [(Q1, _), (Q1, _)]) _
  refine Kit.runs_call hk (.r rfl rx (.r rfl ry .nil)) ?_ ?_ (ctor1 (word_and_run h))
  · intro m hm; simp at hm
    rcases m with _ | _ | m <;> first | omega | walks «programCopy.U32.and»
  · walks «programCopy.U32.and»

theorem and_255 : ∀ b : Fin 256, andBits 32 b 255 = b := by decide

theorem cell_run (h : Holds B) : Runs B (App Q1 (Ref "Program.cell") (cell b)) (Form.term (cell b)) := by
  have hk := h.get (d := «programCopy.Program.cell»)
  have hk' := h.get (d := «programCopy.Program.cell.of»)
  have l255 : Runs B (Ref "U32.lit255") (cell 255) := by lit «programCopy.U32.lit255»
  have ha := u32_and_run h (.refl value_cell) l255 (v := b.toNat) (w := (255 : UInt8).toNat)
  have e : andBits 32 b.toNat (255 : UInt8).toNat = b.toNat := and_255 ⟨b.toNat, b.toNat_lt⟩
  rw [e] at ha
  refine Kit.call (xs := [(Q1, _)])
    (u := App Q1 (Ref "Program.cell.of") (App Q1 (App Q1 (Ref "U32.and") (cell b)) (Ref "U32.lit255")))
    hk (.cons (fun _ => value_cell) .nil) ?_ ?_
  · walks «programCopy.Program.cell»
  · show Runs B (spine (Ref _) [(Q1, _)]) _
    refine Kit.runs_call hk' (.r rfl ha .nil) ?_ ?_
      (ctor_run (xs := [_]) h (names_run h).2.2.2.1 (ctor2 (word_run h) ctor0))
    · intro m hm; simp at hm
      rcases m with _ | m <;> first | omega | walks «programCopy.Program.cell.of»
    · walks «programCopy.Program.cell.of»

theorem bytes_run (h : Holds B) : Runs B (App Q1 (Ref "Program.bytes") (bytes i)) (Form.term (bytes i)) := by
  have hk := h.get (d := «programCopy.Program.bytes»)
  induction i with
  | nil =>
    refine Kit.call (xs := [(Q1, _)]) hk (.cons (fun _ => value_bytes) .nil) ?_
      (ctor_run (xs := []) h (names_run h).2.1 ctor0)
    walks «programCopy.Program.bytes»
  | cons b i ih =>
    refine Kit.call (xs := [(Q1, _)]) hk (.cons (fun _ => value_bytes) .nil) ?_
      (ctor_run (xs := [_, _]) h (names_run h).2.2.1 (ctor2 (cell_run h) (ctor2 ih ctor0)))
    walks «programCopy.Program.bytes»

theorem start_run (h : Holds B) : Runs B (App Q1 (Ref "Program.start") (bytes i)) (Form.term (start i)) := by
  have hk := h.get (d := «programCopy.Program.start»)
  refine Kit.call (xs := [(Q1, _)]) hk (.cons (fun _ => value_bytes) .nil) ?_
    (ctor3 vq1 (ctor1 (names_run h).2.2.2.2.2.2.2.2) (bytes_run h))
  walks «programCopy.Program.start»

-- Comparisons (as EvalSteps' own)
-- ---------------------------------

-- the comparison of two words, as Word.cmp makes it from the top bit down
def wc : Nat → Nat → Nat → Ordering
  | 0, _, _ => .eq
  | n + 1, v, w =>
    match wc n (v / 2) (w / 2) with
    | .lt => .lt
    | .eq => compare (v % 2) (w % 2)
    | .gt => .gt

-- the form of a Cmp
def cmpForm : Ordering → Term
  | .lt => ctor "LT" []
  | .eq => ctor "EQ" []
  | .gt => ctor "GT" []

theorem value_cmp : Value B (cmpForm o) := by cases o <;> exact value_ctor nofun

-- Word.cmp compares the words as numbers modulo 2 ^ n
theorem wc_compare : wc n v w = compare (v % 2 ^ n) (w % 2 ^ n) := by
  induction n generalizing v w with
  | zero => simp [wc, Nat.mod_one]
  | succ n ih =>
    have ev : v % 2 ^ (n + 1) = v % 2 + 2 * (v / 2 % 2 ^ n) := by rw [Nat.pow_succ', Nat.mod_mul]
    have ew : w % 2 ^ (n + 1) = w % 2 + 2 * (w / 2 % 2 ^ n) := by rw [Nat.pow_succ', Nat.mod_mul]
    rw [ev, ew]
    simp only [wc, ih]
    have h2v : v % 2 < 2 := Nat.mod_lt _ (by omega)
    have h2w : w % 2 < 2 := Nat.mod_lt _ (by omega)
    cases hc : compare (v / 2 % 2 ^ n) (w / 2 % 2 ^ n)
    · rw [Nat.compare_eq_lt] at hc; exact (Nat.compare_eq_lt.2 (by omega)).symm
    · rw [Nat.compare_eq_eq] at hc
      cases hd : compare (v % 2) (w % 2)
      · rw [Nat.compare_eq_lt] at hd; exact (Nat.compare_eq_lt.2 (by omega)).symm
      · rw [Nat.compare_eq_eq] at hd; exact (Nat.compare_eq_eq.2 (by omega)).symm
      · rw [Nat.compare_eq_gt] at hd; exact (Nat.compare_eq_gt.2 (by omega)).symm
    · rw [Nat.compare_eq_gt] at hc; exact (Nat.compare_eq_gt.2 (by omega)).symm

-- the form of a word's lowest bit
abbrev bitForm (v : Nat) : Term := ctor (if v % 2 = 1 then "True" else "False") []

theorem bool_cmp (h : Contains B evalCopy) :
    Runs B (App Q1 (App Q1 (Ref "Bool.cmp") (bitForm v)) (bitForm w))
      (cmpForm (compare (v % 2) (w % 2))) := by
  have hk : Book.get B "Bool.cmp" = some «evalCopy.Bool.cmp» := h «evalCopy.Bool.cmp» (by simp [evalCopy])
  rcases Nat.mod_two_eq_zero_or_one v with hv | hv <;>
  rcases Nat.mod_two_eq_zero_or_one w with hw | hw <;>
  exact Kit.call (xs := [(Q1, _), (Q1, _)]) hk
    (.cons (fun _ => value_ctor nofun) (.cons (fun _ => value_ctor nofun) .nil))
    (by simp [walk, «evalCopy.Bool.cmp», hv, hw, ctor, cmpForm, takes, Quan.live, Quan.fld, sub, spine, compare, compareOfLessAndEq])
    (.refl value_cmp)

theorem word_cmp (h : Contains B evalCopy) :
    Runs B (App Q1 (App Q1 (App Q1 (Ref "Word.cmp") (Form.nat n)) (bits n v)) (bits n w))
      (cmpForm (wc n v w)) := by
  have hk : Book.get B "Word.cmp" = some «evalCopy.Word.cmp» := h «evalCopy.Word.cmp» (by simp [evalCopy])
  have hf : Book.get B "Word.cmp.fin" = some «evalCopy.Word.cmp.fin» := h «evalCopy.Word.cmp.fin» (by simp [evalCopy])
  induction n generalizing v w with
  | zero =>
    exact Kit.call (xs := [(Q1, _), (Q1, _), (Q1, _)]) hk
      (.cons (fun _ => value_nat) (.cons (fun _ => value_bits) (.cons (fun _ => value_bits) .nil)))
      (by simp [walk, «evalCopy.Word.cmp», Form.nat, bits, ctor, cmpForm, wc, takes, Quan.live, Quan.fld, sub, spine, bindsAt])
      (.refl value_cmp)
  | succ n ih =>
    refine Kit.call (xs := [(Q1, _), (Q1, _), (Q1, _)]) hk
      (u := App Q1 (App Q1 (App Q1 (Ref "Word.cmp.fin") (bitForm v)) (bitForm w))
        (App Q1 (App Q1 (App Q1 (Ref "Word.cmp") (Form.nat n)) (bits n (v / 2))) (bits n (w / 2))))
      (.cons (fun _ => value_nat) (.cons (fun _ => value_bits) (.cons (fun _ => value_bits) .nil)))
      ?_ ?_
    · simp [walk, «evalCopy.Word.cmp», Form.nat, bits, ctor, takes, Quan.live, Quan.fld, sub, spine, bindsAt, Env.sub, data_iff.2 data_nat, data_iff.2 data_bits]
    · have vs : Values B [(Q1, bitForm v), (Q1, bitForm w)] :=
        .cons (fun _ => value_ctor nofun) (.cons (fun _ => value_ctor nofun) .nil)
      refine Kit.run_x (Kit.part (xs := [(Q1, _), (Q1, _)]) hf vs
        (by simp [walk, «evalCopy.Word.cmp.fin», ctor, takes, bindsAt])) rfl ih ?_
      have vs3 : Values B [(Q1, bitForm v), (Q1, bitForm w), (Q1, cmpForm (wc n (v / 2) (w / 2)))] :=
        .cons (fun _ => value_ctor nofun) (.cons (fun _ => value_ctor nofun)
          (.cons (fun _ => value_cmp) .nil))
      revert vs3
      cases ho : wc n (v / 2) (w / 2) <;> intro vs3
      · exact Kit.call (xs := [(Q1, _), (Q1, _), (Q1, _)]) hf vs3 (u := cmpForm .lt)
          (by simp [walk, «evalCopy.Word.cmp.fin», ctor, cmpForm, takes, bindsAt, data, Quan.live, Quan.fld, sub, spine])
          (by simp only [wc, ho]; exact .refl value_cmp)
      · exact Kit.call (xs := [(Q1, _), (Q1, _), (Q1, _)]) hf vs3
          (u := App Q1 (App Q1 (Ref "Bool.cmp") (bitForm v)) (bitForm w))
          (by simp [walk, «evalCopy.Word.cmp.fin», ctor, cmpForm, takes, bindsAt, data, Quan.live, Quan.fld, sub, spine, Env.sub])
          (by simp only [wc, ho]; exact bool_cmp h)
      · exact Kit.call (xs := [(Q1, _), (Q1, _), (Q1, _)]) hf vs3 (u := cmpForm .gt)
          (by simp [walk, «evalCopy.Word.cmp.fin», ctor, cmpForm, takes, bindsAt, data, Quan.live, Quan.fld, sub, spine])
          (by simp only [wc, ho]; exact .refl value_cmp)

-- U32.is_lt says whether a word is below another
theorem u32_is_lt (h : Holds B) (ry : Runs B y (ctor "U32" [bits 32 w])) :
    Runs B (App Q1 (App Q1 (Ref "U32.is_lt") (ctor "U32" [bits 32 v])) y)
      (Form.bool (decide (v % 2 ^ 32 < w % 2 ^ 32))) := by
  have hk := h.get (d := «programCopy.U32.is_lt»)
  have hc : Book.get B "U32.cmp" = some «evalCopy.U32.cmp» := h.eval «evalCopy.U32.cmp» (by simp [evalCopy])
  have hl : Book.get B "Cmp.is_lt" = some «evalCopy.Cmp.is_lt» := h.eval «evalCopy.Cmp.is_lt» (by simp [evalCopy])
  show Runs B (spine (Ref _) [(Q1, _), (Q1, _)]) _
  refine Kit.runs_call hk (.v rfl (value_ctor (by simp [value_bits])) (.r rfl ry .nil))
    (u := App Q1 (Ref "Cmp.is_lt") (App Q1 (App Q1 (Ref "U32.cmp") (ctor "U32" [bits 32 v])) (ctor "U32" [bits 32 w])))
    ?_ ?_ ?_
  · intro m hm; simp at hm
    rcases m with _ | _ | m <;> first | omega | walks «programCopy.U32.is_lt»
  · walks «programCopy.U32.is_lt»
  have rc : Runs B (App Q1 (App Q1 (Ref "U32.cmp") (ctor "U32" [bits 32 v])) (ctor "U32" [bits 32 w]))
      (cmpForm (wc 32 v w)) :=
    Kit.call (xs := [(Q1, _), (Q1, _)]) hc (.cons (fun _ => value_ctor (by simp [value_bits]))
      (.cons (fun _ => value_ctor (by simp [value_bits])) .nil))
      (u := App Q1 (App Q1 (App Q1 (Ref "Word.cmp") (Form.nat 32)) (bits 32 v)) (bits 32 w))
      (by simp [walk, «evalCopy.U32.cmp», ctor, takes, bindsAt, Quan.live, Quan.fld, sub, spine, Env.sub, Form.nat, data, dbits])
      (word_cmp h.eval)
  refine Kit.run_x (Kit.part (xs := []) hl .nil (by simp [walk, «evalCopy.Cmp.is_lt», takes])) rfl rc ?_
  rw [wc_compare]
  have run_b (o : Ordering) (b : Bool) (hb : decide (v % 2 ^ 32 < w % 2 ^ 32) = b)
      (hw : walk B «evalCopy.Cmp.is_lt».v [] [(Q1, cmpForm o)] = some (some (Form.bool b))) :
      Runs B (App Q1 (Ref "Cmp.is_lt") (cmpForm o)) (Form.bool (decide (v % 2 ^ 32 < w % 2 ^ 32))) :=
    hb ▸ Kit.call (xs := [(Q1, _)]) hl (.cons (fun _ => value_cmp) .nil) hw (.refl value_bool)
  cases ho : compare (v % 2 ^ 32) (w % 2 ^ 32)
  · rw [Nat.compare_eq_lt] at ho
    exact run_b _ true (by simp [ho]) (by simp [walk, «evalCopy.Cmp.is_lt», cmpForm, ctor, takes, bindsAt, data, Quan.live, Quan.fld, sub, spine, Form.bool])
  · rw [Nat.compare_eq_eq] at ho
    exact run_b _ false (by simp [ho]) (by simp [walk, «evalCopy.Cmp.is_lt», cmpForm, ctor, takes, bindsAt, data, Quan.live, Quan.fld, sub, spine, Form.bool])
  · rw [Nat.compare_eq_gt] at ho
    exact run_b _ false (by simp; omega) (by simp [walk, «evalCopy.Cmp.is_lt», cmpForm, ctor, takes, bindsAt, data, Quan.live, Quan.fld, sub, spine, Form.bool])

end Gives
