import Bootstrap.Read.Model

-- Read.Write
-- ==========
--
-- The model reads back the bytes of the Lean writer.

open Quan Term

-- a small tag reads back as itself
theorem toUInt8_toNat (h : t < 256) : t.toUInt8.toNat = t := by
  simp [Nat.toUInt8]
  omega

-- a token runs first, then the rest
theorem run_tok (h : t < 256) :
    Read.run (Write.tok t a ++ ys) s = (Read.token t a s).bind (Read.run ys) := by
  simp [Write.tok, Read.run, toUInt8_toNat h]

-- a nat pushes its item
theorem run_nat : Read.run (Write.nat n ++ ys) s = Read.run ys (Read.item "nat" (Form.nat n) :: s) := by
  induction n generalizing ys s with
  | zero => simp [Write.nat, run_tok, Read.token, Form.nat]
  | succ n ih => simp [Write.nat, ih, run_tok, Read.token, unitem_item, Form.nat]

-- a quantity pushes its item
theorem run_quan : Read.run (Write.quan q ++ ys) s = Read.run ys (Read.item "quan" (Form.quan q) :: s) := by
  cases q <;> simp [Write.quan, run_tok, Read.token]

-- a bool pushes its item
theorem run_bool : Read.run (Write.bool o ++ ys) s = Read.run ys (Read.item "bool" (Form.bool o) :: s) := by
  cases o <;> simp [Write.bool, run_tok, Read.token]

-- bytes, each put in front of a name's
theorem run_cells {l acc : List UInt8} : Read.run (l.flatMap (Write.tok 6 ·) ++ ys) (Read.item "name" (bytes acc) :: s) =
    Read.run ys (Read.item "name" (bytes (l.reverse ++ acc)) :: s) := by
  induction l generalizing acc with
  | nil => simp
  | cons b l ih =>
    have h := ih (acc := b :: acc)
    simp [List.flatMap_cons, List.append_assoc, run_tok, Read.token, unitem_item, bytes]
    simpa [bytes, list] using h

-- a name pushes its item
theorem run_name : Read.run (Write.name k ++ ys) s = Read.run ys (Read.item "name" (Form.name k) :: s) := by
  have h := run_cells (l := k.toUTF8.toList.reverse) (acc := []) (ys := ys) (s := s)
  simp only [List.reverse_reverse, List.append_nil] at h
  rw [Write.name, List.append_assoc, run_tok (by decide)]
  simpa [Read.token, Form.name, bytes, list] using h

-- names, each put in front of a list's
theorem run_names' {l acc : List String} : Read.run (l.flatMap (Write.name · ++ Write.tok 8) ++ ys)
      (Read.item "names" (list (acc.map Form.name)) :: s) =
    Read.run ys (Read.item "names" (list ((l.reverse ++ acc).map Form.name)) :: s) := by
  induction l generalizing acc with
  | nil => simp
  | cons k l ih =>
    have h := ih (acc := k :: acc)
    simp [List.flatMap_cons, List.append_assoc, run_name, run_tok, Read.token, unitem_item]
    simpa [list] using h

-- a list of names pushes its item
theorem run_names : Read.run (Write.names ks ++ ys) s =
    Read.run ys (Read.item "names" (list (ks.map Form.name)) :: s) := by
  have h := run_names' (l := ks.reverse) (acc := []) (ys := ys) (s := s)
  simp only [List.reverse_reverse, List.append_nil] at h
  rw [Write.names, List.append_assoc, run_tok (by decide)]
  simpa [Read.token, list] using h

-- a term pushes its item
theorem run_term : Read.run (Write.term t ++ ys) s = Read.run ys (Read.item "term" (Form.term t) :: s) := by
  induction t generalizing ys s <;>
    simp [Write.term, Form.term, List.append_assoc, run_tok, Read.token, unitem_item,
      run_nat, run_name, run_quan, run_names, *]

-- a def pushes its item
theorem run_defn : Read.run (Write.defn d ++ ys) s = Read.run ys (Read.item "def" (Form.defn d) :: s) := by
  simp [Write.defn, Form.defn, List.append_assoc, run_tok, Read.token, unitem_item,
    run_name, run_term, run_bool]

-- defs, each put in front of a list's
theorem run_defs {l acc : List Def} : Read.run (l.flatMap (Write.defn · ++ Write.tok 12) ++ ys)
      (Read.item "defs" (list (acc.map Form.defn)) :: s) =
    Read.run ys (Read.item "defs" (list ((l.reverse ++ acc).map Form.defn)) :: s) := by
  induction l generalizing acc with
  | nil => simp
  | cons d l ih =>
    have h := ih (acc := d :: acc)
    simp [List.flatMap_cons, List.append_assoc, run_defn, run_tok, Read.token, unitem_item]
    simpa [list] using h

theorem run_write : (Read.run (write bk) []).bind Read.done = some (Form.defs bk.defs) := by
  have h := run_defs (l := bk.defs.reverse) (acc := []) (ys := []) (s := [])
  simp only [List.reverse_reverse, List.append_nil, List.map_nil, Read.run] at h
  rw [write, run_tok (by decide)]
  simp [Read.token, h, Read.done, unitem_item, Form.defs]
