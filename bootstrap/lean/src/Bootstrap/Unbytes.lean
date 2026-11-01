import Bootstrap.Gives

-- Unbytes
-- =======
--
-- The copy of Program.unbytes, on the form of any term v, gives the form of
-- Lean's unbytes v: the list of bytes of a term that is one, and nothing for
-- any other term.

open Quan Term

set_option linter.unusedSimpArgs false
set_option maxRecDepth 20000

namespace Gives

macro "walks'" d:term : tactic =>
  `(tactic| simp [$d:term, walk, list, ctor, bits, cell, bytes, bindsAt, Quan.live, Quan.fld, takes,
    Term.sub, Env.sub, Term.spine, Form.nat, Form.term, Form.quan, Form.bool, Form.some, Form.maybe, data,
    dbits, dnat, dcell, dbytes, dname, dterm])

theorem value_is_eq (h : Holds B) : Value B (App Q1 (Ref "Name.is_eq") (Form.name a)) := by
  have hk : Book.get B "Name.is_eq" = some «evalCopy.Name.is_eq» :=
    h.eval «evalCopy.Name.is_eq» (by simp [evalCopy])
  unfold Form.name
  cases a.toUTF8.toList <;>
  exact Kit.part (xs := [(Q1, _)]) hk (.cons (fun _ => value_bytes) .nil)
    (by simp [walk, «evalCopy.Name.is_eq», bytes, list, ctor, takes, bindsAt, Quan.live, Quan.fld])

theorem is_eq_run (h : Holds B) (r : Runs B y (Form.name b)) :
    Runs B (App Q1 (App Q1 (Ref "Name.is_eq") (Form.name a)) y) (Form.bool (a == b)) :=
  Kit.run_x (value_is_eq h) rfl r (EvalCopy.name_is_eq_copy h.eval)

theorem value_and (h : Holds B) : Value B (App Q1 (Ref "Bool.and") (Form.bool b)) := by
  have hk : Book.get B "Bool.and" = some «evalCopy.Bool.and» := h.eval «evalCopy.Bool.and» (by simp [evalCopy])
  cases b <;> exact Kit.part (xs := [(Q1, _)]) hk (.cons (fun _ => value_bool) .nil)
    (by simp [walk, «evalCopy.Bool.and», Form.bool, ctor, takes, Quan.live, Quan.fld])

theorem and_run (h : Holds B) (rx : Runs B x (Form.bool a)) (ry : Runs B y (Form.bool b)) :
    Runs B (App Q1 (App Q1 (Ref "Bool.and") x) y) (Form.bool (a && b)) := by
  have hk : Book.get B "Bool.and" = some «evalCopy.Bool.and» := h.eval «evalCopy.Bool.and» (by simp [evalCopy])
  exact Kit.run_f (Kit.run_x (Kit.part (xs := []) hk .nil (by simp [walk, «evalCopy.Bool.and», takes])) rfl rx
    (.refl (value_and h))) (Kit.run_x (value_and h) rfl ry (EvalCopy.and_copy h.eval))

-- the forms of a Maybe of Bools
def mbool : Option Bool → Term := Form.maybe Form.bool

theorem value_maybe' (h : ∀ x, Value B (f x)) : Value B (Form.maybe f o) := by
  cases o <;> simp only [Form.maybe, Form.some] <;> exact value_ctor (by simp [h])

theorem unbit_run (h : Holds B) :
    Runs B (App Q2 (Ref "Program.unbit") (Form.name k))
      (mbool (if k = "True" then some true else if k = "False" then some false else none)) := by
  have hk := h.get (d := «programCopy.Program.unbit»)
  have hi := h.get (d := «programCopy.Program.unbit.if»)
  refine Kit.call (xs := [(Q2, Form.name k)]) hk (.cons (fun _ => value_bytes) .nil)
    (u := App Q1 (App Q1 (Ref "Program.unbit.if") (App Q1 (App Q1 (Ref "Name.is_eq") (Form.name k))
      (Ref "Program.name.true"))) (App Q1 (App Q1 (Ref "Name.is_eq") (Form.name k)) (Ref "Program.name.false")))
    (by walks' «programCopy.Program.unbit») ?_
  show Runs B (spine (Ref _) [(Q1, _), (Q1, _)]) _
  refine Kit.runs_call hi (.r rfl (is_eq_run h (names_run h).2.2.2.2.2.2.1)
    (.r rfl (is_eq_run h (names_run h).2.2.2.2.2.2.2.1) .nil)) ?_ ?_ (.refl (value_maybe' (fun _ => value_bool)))
  · intro m hm; simp at hm
    rcases m with _ | _ | m <;> first | omega | (cases (k == "True") <;> walks' «programCopy.Program.unbit.if»)
  · by_cases h1 : k = "True"
    · subst h1; simp [«programCopy.Program.unbit.if», walk, Form.bool, ctor, takes, bindsAt, Quan.live,
        Quan.fld, data, Term.sub, Env.sub, Term.spine, mbool, Form.maybe, Form.some]
    · by_cases h2 : k = "False"
      · subst h2; simp [«programCopy.Program.unbit.if», walk, Form.bool, ctor, takes, bindsAt, Quan.live,
          Quan.fld, data, Term.sub, Env.sub, Term.spine, mbool, Form.maybe, Form.some]
      · simp [h1, h2, «programCopy.Program.unbit.if», walk, Form.bool, ctor, takes, bindsAt, Quan.live,
          Quan.fld, data, Term.sub, Env.sub, Term.spine, mbool, Form.maybe, Form.some]

-- Lean's unbits, on the two shapes it reads
theorem unbits_nil : unbits 0 (Tup Q1 (Lab k) (Lab u)) = if k = "WNil" ∧ u = "()" then some 0 else none := by
  by_cases h1 : k = "WNil" <;> by_cases h2 : u = "()" <;> simp_all [unbits]

theorem unbits_con : unbits (n + 1) (Tup Q1 (Lab k) (Tup Q1 (Tup Q1 (Lab b) (Lab u1)) (Tup Q1 w (Lab u2)))) =
    if k = "WCon" ∧ u1 = "()" ∧ u2 = "()" then
      (if b = "True" then (unbits n w).map (2 * · + 1) else if b = "False" then (unbits n w).map (2 * ·) else none)
    else none := by
  by_cases h1 : k = "WCon" <;> by_cases h2 : u1 = "()" <;> by_cases h3 : u2 = "()" <;> simp_all [unbits]

theorem bits_odd : bits (n + 1) (2 * v + 1) = ctor "WCon" [Form.bool true, bits n v] := by
  have h1 : (2 * v + 1) % 2 = 1 := by omega
  have h2 : (2 * v + 1) / 2 = v := by omega
  simp [bits, h1, h2, Form.bool]

theorem bits_even : bits (n + 1) (2 * v) = ctor "WCon" [Form.bool false, bits n v] := by
  have h1 : (2 * v) % 2 = 0 := by omega
  have h2 : (2 * v) / 2 = v := by omega
  simp [bits, h1, h2, Form.bool]

theorem value_mbits : Value B (Form.maybe (bits n) o) := value_maybe' (fun _ => value_bits)

-- the bits of n + 1 that a bit and the bits of n make
def wordOf (ok : Bool) (ob : Option Bool) (ow : Option Nat) : Option Nat :=
  if ok then
    match ob with
    | some true => ow.map (2 * · + 1)
    | some false => ow.map (2 * ·)
    | none => none
  else none

theorem unword_con_run (h : Holds B) :
    Runs B (spine (Ref "Program.unword.con") [(Q0, Form.nat n), (Q1, Form.bool ok), (Q1, mbool ob),
      (Q1, Form.maybe (bits n) ow)]) (Form.maybe (bits (n + 1)) (wordOf ok ob ow)) := by
  have hc := h.get (d := «programCopy.Program.unword.con»)
  cases ok <;> rcases ob with _ | ⟨_ | _⟩ <;> rcases ow with _ | v <;>
    refine Kit.call hc (.cons (fun h => by simp [Quan.live] at h) (.cons (fun _ => value_bool)
      (.cons (fun _ => value_maybe' (fun _ => value_bool)) (.cons (fun _ => value_mbits) .nil)))) ?_
      (.refl value_mbits) <;>
    simp [wordOf, bits_odd, bits_even, mbool, «programCopy.Program.unword.con», walk, list, ctor, bindsAt,
      Quan.live, Quan.fld, takes, Term.sub, Env.sub, Term.spine, Form.term, Form.bool, Form.some, Form.maybe, data,
      dbits, dnat] <;> rfl

theorem unword_con_part (h : Holds B) : ∀ m < 4,
    walk B «programCopy.Program.unword.con».v [] (List.take m [(Q0, Form.nat n), (Q1, Form.bool ok),
      (Q1, mbool ob), (Q1, Form.maybe (bits n) ow)]) = some none := by
  intro m hm
  cases ok <;> rcases ob with _ | ⟨_ | _⟩ <;> rcases ow with _ | v <;>
    rcases m with _ | _ | _ | _ | m <;> first | omega |
    simp [mbool, «programCopy.Program.unword.con», walk, list, ctor, bindsAt,
      Quan.live, Quan.fld, takes, Term.sub, Env.sub, Term.spine, Form.term, Form.bool, Form.some, Form.maybe, data,
      dbits, dnat]

theorem unword_none (h : Holds B)
    (e : walk B «programCopy.Program.unword».v [] [(Q1, Form.nat n), (Q1, Form.term w)] =
      some (some (ctor "None" []))) (hu : unbits n w = none) :
    Runs B (App Q1 (App Q1 (Ref "Program.unword") (Form.nat n)) (Form.term w)) (Form.maybe (bits n) (unbits n w)) :=
  Kit.call (h.get (d := «programCopy.Program.unword»)) (.cons (fun _ => value_nat) (.cons (fun _ => value_term) .nil))
    e (Kit.runs_eq ctor0 (by rw [hu]; rfl))

macro "nc" : tactic =>
  `(tactic| try (exact unword_none (by assumption) (by walks' «programCopy.Program.unword») (by simp [unbits])))

theorem unword_run (h : Holds B) :
    Runs B (App Q1 (App Q1 (Ref "Program.unword") (Form.nat n)) (Form.term w)) (Form.maybe (bits n) (unbits n w)) := by
  have hk := h.get (d := «programCopy.Program.unword»)
  have hn := h.get (d := «programCopy.Program.unword.nil»)
  have hc := h.get (d := «programCopy.Program.unword.con»)
  induction n generalizing w with
  | zero =>
    have vs : Values B [(Q1, Form.nat 0), (Q1, Form.term w)] :=
      .cons (fun _ => value_nat) (.cons (fun _ => value_term) .nil)
    cases w <;> nc
    rename_i q a b
    cases q <;> nc
    cases a <;> nc
    rename_i k
    cases b <;> nc
    rename_i u
    refine Kit.call hk vs (u := App Q1 (Ref "Program.unword.nil") (App Q1 (App Q1 (Ref "Bool.and")
      (App Q1 (App Q1 (Ref "Name.is_eq") (Form.name k)) (Ref "Program.name.wnil")))
      (App Q1 (App Q1 (Ref "Name.is_eq") (Form.name u)) (Ref "Program.name.unit"))))
      (by walks' «programCopy.Program.unword») ?_
    refine Kit.run_x (Kit.part (xs := []) hn .nil (by walks' «programCopy.Program.unword.nil»)) rfl
      (and_run h (is_eq_run h (names_run h).2.2.2.2.1) (is_eq_run h (names_run h).1)) ?_
    rw [unbits_nil]
    by_cases h1 : k = "WNil" <;> by_cases h2 : u = "()" <;>
      exact Kit.call (xs := [(Q1, _)]) hn (.cons (fun _ => value_bool) .nil)
        (by simp [h1, h2]; walks' «programCopy.Program.unword.nil» <;> simp [h1, h2]) (.refl value_mbits)
  | succ n ih =>
    have vs : Values B [(Q1, Form.nat (n + 1)), (Q1, Form.term w)] :=
      .cons (fun _ => value_nat) (.cons (fun _ => value_term) .nil)
    cases w <;> nc
    rename_i q a b
    cases q <;> nc
    cases a <;> nc
    rename_i k
    cases b <;> nc
    rename_i q c d
    cases q <;> nc
    cases c <;> nc
    rename_i q e f
    cases q <;> nc
    cases e <;> nc
    rename_i bt
    cases f <;> nc
    rename_i u1
    cases d <;> nc
    rename_i q w' g
    cases q <;> nc
    cases g <;> nc
    rename_i u2
    refine Kit.call hk vs (u := App Q1 (App Q1 (App Q1 (App Q0 (Ref "Program.unword.con") (Form.nat n))
      (App Q1 (App Q1 (Ref "Bool.and") (App Q1 (App Q1 (Ref "Bool.and")
        (App Q1 (App Q1 (Ref "Name.is_eq") (Form.name k)) (Ref "Program.name.wcon")))
        (App Q1 (App Q1 (Ref "Name.is_eq") (Form.name u1)) (Ref "Program.name.unit"))))
        (App Q1 (App Q1 (Ref "Name.is_eq") (Form.name u2)) (Ref "Program.name.unit"))))
      (App Q2 (Ref "Program.unbit") (Form.name bt))) (App Q1 (App Q1 (Ref "Program.unword") (Form.nat n)) (Form.term w')))
      (by walks' «programCopy.Program.unword») ?_
    show Runs B (spine (Ref "Program.unword.con") [(Q0, _), (Q1, _), (Q1, _), (Q1, _)]) _
    refine Kit.runs_args hc (.d rfl (.r rfl (and_run h (and_run h (is_eq_run h (names_run h).2.2.2.2.2.1)
      (is_eq_run h (names_run h).1)) (is_eq_run h (names_run h).1)) (.r rfl (unbit_run h) (.r rfl ih .nil))))
      (unword_con_part h) (Kit.runs_eq (unword_con_run h) ?_)
    rw [unbits_con]
    by_cases h1 : k = "WCon" <;> by_cases h2 : u1 = "()" <;> by_cases h3 : u2 = "()" <;>
      by_cases h4 : bt = "True" <;> by_cases h5 : bt = "False" <;> simp_all [wordOf]

-- Lean's unbytes, on the two shapes it reads
theorem unbytes_nil' : unbytes (Tup Q1 (Lab k) (Lab u)) = if k = "Nil" ∧ u = "()" then some [] else none := by
  by_cases h1 : k = "Nil" <;> by_cases h2 : u = "()" <;> simp_all [unbytes]

-- the list of bytes that a cell and a list of bytes make
def bytesOf (ok : Bool) (ow : Option Nat) (ob : Option (List UInt8)) : Option (List UInt8) :=
  if ok then
    match ow, ob with
    | some v, some bs => if v < 256 then some (v.toUInt8 :: bs) else none
    | _, _ => none
  else none

theorem unbytes_con' : unbytes (Tup Q1 (Lab k) (Tup Q1 (Tup Q1 (Lab c) (Tup Q1 w (Lab u1))) (Tup Q1 t (Lab u2)))) =
    bytesOf (k == "Con" && c == "U32" && u1 == "()" && u2 == "()") (unbits 32 w) (unbytes t) := by
  by_cases h1 : k = "Con" <;> by_cases h2 : c = "U32" <;> by_cases h3 : u1 = "()" <;> by_cases h4 : u2 = "()" <;>
    simp_all [unbytes, bytesOf] <;> rfl

theorem unbits_lt : unbits n w = some v → v < 2 ^ n := by
  fun_induction unbits n w generalizing v
  all_goals intro h
  all_goals simp_all
  · subst h; simp
  all_goals rename_i n w ih
  all_goals obtain ⟨a, ha, rfl⟩ := h
  all_goals have := ih ha
  all_goals rw [Nat.pow_succ]; omega

theorem value_mbytes : Value B (Form.maybe bytes o) := value_maybe' (fun _ => value_bytes)

theorem unbytes_con_run (h : Holds B) (hw : ∀ v, ow = some v → v < 2 ^ 32) :
    Runs B (spine (Ref "Program.unbytes.con") [(Q1, Form.bool ok), (Q1, Form.maybe (bits 32) ow),
      (Q1, Form.maybe bytes ob)]) (Form.maybe bytes (bytesOf ok ow ob)) := by
  have hc := h.get (d := «programCopy.Program.unbytes.con»)
  have hb := h.get (d := «programCopy.Program.unbytes.byte»)
  have l256 : Runs B (Ref "U32.lit256") (ctor "U32" [bits 32 256]) := by
    have e : «programCopy.U32.lit256».v = ctor "U32" [bits 32 256] := by decide
    have := body_run (h.get (d := «programCopy.U32.lit256»)) (e ▸ value_ctor (by simp [value_bits]))
      (by rw [e]; rfl) (by rw [e]; simp [ctor])
    rwa [e] at this
  have vs : Values B [(Q1, Form.bool ok), (Q1, Form.maybe (bits 32) ow), (Q1, Form.maybe bytes ob)] :=
    .cons (fun _ => value_bool) (.cons (fun _ => value_mbits) (.cons (fun _ => value_mbytes) .nil))
  cases ok
  · refine Kit.call hc vs (u := ctor "None" []) ?_ ctor0
    rcases ow with _ | v <;> rcases ob with _ | bs <;>
      simp [«programCopy.Program.unbytes.con», walk, list, ctor, bindsAt,
        Quan.live, Quan.fld, takes, Term.sub, Env.sub, Term.spine, Form.bool, Form.some, Form.maybe, data, dbits, dbytes]
  rcases ow with _ | v
  · refine Kit.call hc vs (u := ctor "None" []) ?_ ctor0
    rcases ob with _ | bs <;>
      simp [«programCopy.Program.unbytes.con», walk, list, ctor, bindsAt,
        Quan.live, Quan.fld, takes, Term.sub, Env.sub, Term.spine, Form.bool, Form.some, Form.maybe, data, dbits, dbytes]
  rcases ob with _ | bs
  · refine Kit.call hc vs (u := ctor "None" []) ?_ (Kit.runs_eq ctor0 (by simp [bytesOf, Form.maybe]))
    simp [«programCopy.Program.unbytes.con», walk, list, ctor, bindsAt,
        Quan.live, Quan.fld, takes, Term.sub, Env.sub, Term.spine, Form.bool, Form.some, Form.maybe, data, dbits, dbytes]
  have hv := hw v rfl
  refine Kit.call hc vs (u := App Q1 (App Q1 (App Q1 (Ref "Program.unbytes.byte")
    (App Q1 (App Q1 (Ref "U32.is_lt") (ctor "U32" [bits 32 v])) (Ref "U32.lit256"))) (ctor "U32" [bits 32 v])) (bytes bs))
    ?_ ?_
  · simp [«programCopy.Program.unbytes.con», walk, list, ctor, bindsAt,
        Quan.live, Quan.fld, takes, Term.sub, Env.sub, Term.spine, Form.bool, Form.some, Form.maybe, data, dbits, dbytes]
  have rl := u32_is_lt h l256 (v := v)
  have e1 : v % 2 ^ 32 = v := Nat.mod_eq_of_lt hv
  rw [e1] at rl
  show Runs B (spine (Ref _) [(Q1, _), (Q1, _), (Q1, _)]) _
  refine Kit.runs_args hb (.r rfl rl (.v rfl (value_ctor (by simp [value_bits])) (.v rfl value_bytes .nil))) ?_ ?_
  · intro m hm; simp at hm
    by_cases hl : v < 256 <;>
    rcases m with _ | _ | _ | m <;> first | omega |
      simp [hl, «programCopy.Program.unbytes.byte», walk, list, ctor, bindsAt,
        Quan.live, Quan.fld, takes, Term.sub, Env.sub, Term.spine, Form.bool, Form.some, Form.maybe, data, dbits, dbytes]
  · by_cases hl : v < 256
    · refine Kit.call hb (.cons (fun _ => value_bool) (.cons (fun _ => value_ctor (by simp [value_bits]))
        (.cons (fun _ => value_bytes) .nil))) ?_ (.refl value_mbytes)
      have e2 : v.toUInt8.toNat = v := toUInt8_toNat hl
      simp [hl, bytesOf, e2, cell, «programCopy.Program.unbytes.byte», walk, list, ctor, bindsAt,
        Quan.live, Quan.fld, takes, Term.sub, Env.sub, Term.spine, Form.bool, Form.some, Form.maybe, data, dbits, dbytes, bytes]
    · refine Kit.call hb (.cons (fun _ => value_bool) (.cons (fun _ => value_ctor (by simp [value_bits]))
        (.cons (fun _ => value_bytes) .nil))) ?_ (.refl value_mbytes)
      simp [hl, bytesOf, «programCopy.Program.unbytes.byte», walk, list, ctor, bindsAt,
        Quan.live, Quan.fld, takes, Term.sub, Env.sub, Term.spine, Form.bool, Form.some, Form.maybe, data, dbits, dbytes]

theorem unbytes_con_part (h : Holds B) : ∀ m < 3,
    walk B «programCopy.Program.unbytes.con».v [] (List.take m [(Q1, Form.bool ok),
      (Q1, Form.maybe (bits 32) ow), (Q1, Form.maybe bytes ob)]) = some none := by
  intro m hm
  cases ok <;> rcases ow with _ | v <;> rcases ob with _ | bs <;>
    rcases m with _ | _ | _ | m <;> first | omega |
    simp [«programCopy.Program.unbytes.con», walk, list, ctor, bindsAt,
      Quan.live, Quan.fld, takes, Term.sub, Env.sub, Term.spine, Form.bool, Form.some, Form.maybe, data,
      dbits, dbytes]

theorem unbytes_none (h : Holds B)
    (e : walk B «programCopy.Program.unbytes».v [] [(Q1, Form.term v)] = some (some (ctor "None" [])))
    (hu : unbytes v = none) :
    Runs B (App Q1 (Ref "Program.unbytes") (Form.term v)) (Form.maybe bytes (unbytes v)) :=
  Kit.call (h.get (d := «programCopy.Program.unbytes»)) (.cons (fun _ => value_term) .nil)
    e (Kit.runs_eq ctor0 (by rw [hu]; rfl))

macro "nb" : tactic =>
  `(tactic| try (exact unbytes_none (by assumption) (by walks' «programCopy.Program.unbytes») (by simp [unbytes])))

private theorem unbytes_lt (h : Holds B) : ∀ s v, sizeOf v < s →
    Runs B (App Q1 (Ref "Program.unbytes") (Form.term v)) (Form.maybe bytes (unbytes v)) := by
  have hk := h.get (d := «programCopy.Program.unbytes»)
  have hn := h.get (d := «programCopy.Program.unbytes.nil»)
  have hc := h.get (d := «programCopy.Program.unbytes.con»)
  intro s
  induction s with
  | zero => intro v hs; omega
  | succ s ih =>
  intro v hs
  cases v <;> nb
  rename_i q a b
  cases q <;> nb
  cases a <;> nb
  rename_i k
  cases b <;> nb
  · -- the con shape
    rename_i q c d
    cases q <;> nb
    cases c <;> nb
    rename_i q e f
    cases q <;> nb
    cases e <;> nb
    rename_i cu
    cases f <;> nb
    rename_i q w g
    cases q <;> nb
    cases g <;> nb
    rename_i u1
    cases d <;> nb
    rename_i q t r
    cases q <;> nb
    cases r <;> nb
    rename_i u2
    refine Kit.call hk (.cons (fun _ => value_term) .nil) (u := App Q1 (App Q1 (App Q1 (Ref "Program.unbytes.con")
      (App Q1 (App Q1 (Ref "Bool.and") (App Q1 (App Q1 (Ref "Bool.and") (App Q1 (App Q1 (Ref "Bool.and")
        (App Q1 (App Q1 (Ref "Name.is_eq") (Form.name k)) (Ref "Program.name.con")))
        (App Q1 (App Q1 (Ref "Name.is_eq") (Form.name cu)) (Ref "Program.name.u32"))))
        (App Q1 (App Q1 (Ref "Name.is_eq") (Form.name u1)) (Ref "Program.name.unit"))))
        (App Q1 (App Q1 (Ref "Name.is_eq") (Form.name u2)) (Ref "Program.name.unit"))))
      (App Q1 (App Q1 (Ref "Program.unword") (Form.nat 32)) (Form.term w)))
      (App Q1 (Ref "Program.unbytes") (Form.term t)))
      (by walks' «programCopy.Program.unbytes») ?_
    show Runs B (spine (Ref "Program.unbytes.con") [(Q1, _), (Q1, _), (Q1, _)]) _
    have ht : sizeOf t < s := by simp at hs; omega
    refine Kit.runs_args hc (.r rfl (and_run h (and_run h (and_run h (is_eq_run h (names_run h).2.2.1)
      (is_eq_run h (names_run h).2.2.2.1)) (is_eq_run h (names_run h).1)) (is_eq_run h (names_run h).1))
      (.r rfl (unword_run h) (.r rfl (ih t ht) .nil)))
      (unbytes_con_part h) (Kit.runs_eq (unbytes_con_run h (fun v hv => unbits_lt hv)) ?_)
    rw [unbytes_con']
  · -- the nil shape
    rename_i u
    refine Kit.call hk (.cons (fun _ => value_term) .nil) (u := App Q1 (Ref "Program.unbytes.nil")
      (App Q1 (App Q1 (Ref "Bool.and") (App Q1 (App Q1 (Ref "Name.is_eq") (Form.name k)) (Ref "Program.name.nil")))
      (App Q1 (App Q1 (Ref "Name.is_eq") (Form.name u)) (Ref "Program.name.unit"))))
      (by walks' «programCopy.Program.unbytes») ?_
    refine Kit.run_x (Kit.part (xs := []) hn .nil (by walks' «programCopy.Program.unbytes.nil»)) rfl
      (and_run h (is_eq_run h (names_run h).2.1) (is_eq_run h (names_run h).1)) ?_
    rw [unbytes_nil']
    by_cases h1 : k = "Nil" <;> by_cases h2 : u = "()" <;>
      exact Kit.call (xs := [(Q1, _)]) hn (.cons (fun _ => value_bool) .nil)
        (by simp [h1, h2]; walks' «programCopy.Program.unbytes.nil» <;> simp [h1, h2]) (.refl value_mbytes)

theorem unbytes_run (h : Holds B) :
    Runs B (App Q1 (Ref "Program.unbytes") (Form.term v)) (Form.maybe bytes (unbytes v)) :=
  unbytes_lt h _ v (Nat.lt_succ_self _)

end Gives
