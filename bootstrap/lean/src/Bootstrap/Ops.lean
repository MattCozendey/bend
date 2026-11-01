import Std.Data.HashMap.Lemmas
import Bootstrap.Ops.Shift
import Bootstrap.Ops.Cmp
import Bootstrap.Ops.Logic
import Bootstrap.Ops.Nat
import Bootstrap.Ops.Add

-- Ops
-- ===
--
-- Fast calls of Base's U32 operations, for the machine (Bootstrap/Machine.lean):
-- for a call of an operation on U32 terms (and a Nat term for a count), the
-- term that Eval reaches and its exact number of steps, computed natively.
--
-- Ops.prepare checks once which operations the book holds exactly as Base's:
-- the def of each operation, and each def that its evaluation reaches, is
-- equal as a Term to the one of src/Bootstrap/Ops/Defs.lean, which
-- scripts/Defs.lean wrote from the `bend -o` output of our compiler:
--
--   bun bend2/main.ts bootstrap/tests/compiler/compile.bend -o compile.bendtt
--   BOOK=compile.bendtt NAME=opsDefs SOURCE=bootstrap/tests/compiler/compile.bend \
--     OUTPUT=src/Bootstrap/Ops/Defs.lean ONLY=<the 45 defs that Op.defs names> \
--     lake lean scripts/Defs.lean
--
-- and each def U32.litN whose term is a U32. Ops.call answers only for those,
-- after one lookup in a HashMap, and only when each argument is at quantity 1
-- and is a U32 term, or a Nat term for a count. Ops.call_sound proves that Eval
-- reaches its term after exactly its number of steps, and that the term is a
-- value. With x, y the U32s, m the Nat, and the steps:
--
--   U32.shr x            x / 2                   34
--   U32.shrn x m         x >>> m                 1 + 35 m
--   U32.shl x            2 x mod 2^32            34
--   U32.shln x m         x <<< m mod 2^32        1 + 35 m
--   U32.cmp x y          compare x y             66 + E           (1)
--   U32.is_eq, is_lt, is_le, is_gt, is_ge        68 + E
--   U32.is_ne x y                                69 + E
--   U32.is_zero x        x = 0                   70 + E (y = 0)
--   U32.and, U32.or      x &&& y, x ||| y        66
--   U32.inc x            x + 1 mod 2^32          2 + T x                (2)
--   U32.add x y          x + y mod 2^32          4 + sum of 7 + x_i + y_i
--   U32.sub x y          x - y mod 2^32          4 + sum of 8 + x_i + (1 - y_i)
--   U32.to_nat x         the Nat x, x < 2^16     66 + sum of x >>> i, 1 ≤ i ≤ 32
--   U32.from_nat m       m mod 2^32              2 + sum of 3 + T k, k < m
--   U32.litN             the U32 N               1
--
--   (1) E = 32 when x = y, else 32 - log2 (x ^^^ y): one more step per bit
--       above the top bit where x and y differ
--   (2) T x: the number of trailing ones of x mod 2^32, at most 32
--   (x_i is the bit i of x, and each sum is over the 32 bits i)
--
-- A result below 256 is its cell (Bootstrap/Bytes.lean), so that equal
-- results share memory; the labels of the words that Ops builds are those of
-- the cells, so that decoding a cell, or a result of Ops, compares each label
-- by pointer.

open Quan Term

set_option linter.unusedSimpArgs false

namespace Ops

-- the operations
inductive Op where
  | shr | shrn | shl | shln
  | cmp | is_eq | is_ne | is_lt | is_le | is_gt | is_ge | is_zero
  | and | or | inc | to_nat | from_nat | add | sub
  -- a def U32.litN, whose term is the U32 v, and that U32, made once
  | lit (v : Nat) (t : Term)
  deriving Inhabited

-- the name of an operation's def (a literal has its own)
def Op.name : Op → String
  | shr => "U32.shr"
  | shrn => "U32.shrn"
  | shl => "U32.shl"
  | shln => "U32.shln"
  | cmp => "U32.cmp"
  | is_eq => "U32.is_eq"
  | is_ne => "U32.is_ne"
  | is_lt => "U32.is_lt"
  | is_le => "U32.is_le"
  | is_gt => "U32.is_gt"
  | is_ge => "U32.is_ge"
  | is_zero => "U32.is_zero"
  | and => "U32.and"
  | or => "U32.or"
  | inc => "U32.inc"
  | to_nat => "U32.to_nat"
  | from_nat => "U32.from_nat"
  | add => "U32.add"
  | sub => "U32.sub"
  | lit _ _ => ""

-- the defs that an operation reaches, its own first, as the book must hold them
def shrDefs : List (String × Term) :=
  [("U32.shr", «opsDefs.U32.shr».v), ("Word.shr", «opsDefs.Word.shr».v),
   ("Word.shr.pad", «opsDefs.Word.shr.pad».v)]

def shlDefs : List (String × Term) :=
  [("U32.shl", «opsDefs.U32.shl».v), ("Word.shl", «opsDefs.Word.shl».v),
   ("Word.shl.put", «opsDefs.Word.shl.put».v)]

def cmpDefs : List (String × Term) :=
  [("U32.cmp", «opsDefs.U32.cmp».v), ("Word.cmp", «opsDefs.Word.cmp».v),
   ("Word.cmp.fin", «opsDefs.Word.cmp.fin».v), ("Bool.cmp", «opsDefs.Bool.cmp».v)]

def adcDefs : List (String × Term) :=
  [("Word.adc.group", «opsDefs.Word.adc.group».v), ("Bool.full_add", «opsDefs.Bool.full_add».v),
   ("Bool.xor", «opsDefs.Bool.xor».v), ("Bool.not", «opsDefs.Bool.not».v),
   ("Bool.and", «opsDefs.Bool.and».v), ("Bool.or", «opsDefs.Bool.or».v)]

def Op.defs : Op → List (String × Term)
  | shr => shrDefs
  | shrn => ("U32.shrn", «opsDefs.U32.shrn».v) :: shrDefs
  | shl => shlDefs
  | shln => ("U32.shln", «opsDefs.U32.shln».v) :: shlDefs
  | cmp => cmpDefs
  | is_eq => ("U32.is_eq", «opsDefs.U32.is_eq».v) :: ("Cmp.is_eq", «opsDefs.Cmp.is_eq».v) :: cmpDefs
  | is_ne => ("U32.is_ne", «opsDefs.U32.is_ne».v) :: ("Cmp.is_eq", «opsDefs.Cmp.is_eq».v) ::
      ("Bool.not", «opsDefs.Bool.not».v) :: cmpDefs
  | is_lt => ("U32.is_lt", «opsDefs.U32.is_lt».v) :: ("Cmp.is_lt", «opsDefs.Cmp.is_lt».v) :: cmpDefs
  | is_le => ("U32.is_le", «opsDefs.U32.is_le».v) :: ("Cmp.is_le", «opsDefs.Cmp.is_le».v) :: cmpDefs
  | is_gt => ("U32.is_gt", «opsDefs.U32.is_gt».v) :: ("Cmp.is_gt", «opsDefs.Cmp.is_gt».v) :: cmpDefs
  | is_ge => ("U32.is_ge", «opsDefs.U32.is_ge».v) :: ("Cmp.is_ge", «opsDefs.Cmp.is_ge».v) :: cmpDefs
  | is_zero => ("U32.is_zero", «opsDefs.U32.is_zero».v) :: ("U32.is_eq", «opsDefs.U32.is_eq».v) ::
      ("Cmp.is_eq", «opsDefs.Cmp.is_eq».v) :: ("U32.lit0", «opsDefs.U32.lit0».v) :: cmpDefs
  | and => [("U32.and", «opsDefs.U32.and».v), ("Word.and", «opsDefs.Word.and».v),
      ("Bool.and", «opsDefs.Bool.and».v)]
  | or => [("U32.or", «opsDefs.U32.or».v), ("Word.or", «opsDefs.Word.or».v),
      ("Bool.or", «opsDefs.Bool.or».v)]
  | inc => [("U32.inc", «opsDefs.U32.inc».v), ("Word.inc", «opsDefs.Word.inc».v)]
  | to_nat => [("U32.to_nat", «opsDefs.U32.to_nat».v), ("Word.to_nat", «opsDefs.Word.to_nat».v),
      ("Nat.double", «opsDefs.Nat.double».v)]
  | from_nat => [("U32.from_nat", «opsDefs.U32.from_nat».v), ("U32.lit0", «opsDefs.U32.lit0».v),
      ("U32.inc", «opsDefs.U32.inc».v), ("Word.inc", «opsDefs.Word.inc».v)]
  | add => ("U32.add", «opsDefs.U32.add».v) :: ("Word.add", «opsDefs.Word.add».v) :: adcDefs
  | sub => ("U32.sub", «opsDefs.U32.sub».v) :: ("Word.sub", «opsDefs.Word.sub».v) :: adcDefs
  | lit _ _ => []

-- the book holds the op under the name k
def Op.ok (bk : Book) (k : String) : Op → Bool
  | lit v t => has bk k (u32 v) && t == u32 v
  | op => k == op.name && op.defs.all fun d => has bk d.1 d.2

-- Arguments
-- ---------

def arg1 : List Arg → Option Term
  | [(.Q1, a)] => some a
  | _ => none

def arg2 : List Arg → Option (Term × Term)
  | [(.Q1, a), (.Q1, b)] => some (a, b)
  | _ => none

theorem arg1_eq (h : arg1 xs = some a) : xs = [(Q1, a)] := by
  unfold arg1 at h; split at h <;> simp_all

theorem arg2_eq (h : arg2 xs = some (a, b)) : xs = [(Q1, a), (Q1, b)] := by
  unfold arg2 at h; split at h <;> simp_all

-- a U32 and a Nat
def argUN (xs : List Arg) : Option (Nat × Nat) :=
  (arg2 xs).bind fun (a, n) => (decU32 a).bind fun v => (decNat n 0).map fun m => (v, m)

theorem argUN_eq (h : argUN xs = some (v, m)) :
    xs = [(Q1, u32 v), (Q1, Form.nat m)] ∧ v < 2 ^ 32 := by
  simp only [argUN, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨a, n⟩, h2, v', hv, m', hm, rfl, rfl⟩ := h
  obtain ⟨rfl, hlt⟩ := decU32_eq hv
  obtain ⟨rfl, -⟩ := decNat_eq hm
  exact ⟨by rw [arg2_eq h2]; rfl, hlt⟩

-- one U32
def argU (xs : List Arg) : Option Nat := (arg1 xs).bind decU32

theorem argU_eq (h : argU xs = some v) : xs = [(Q1, u32 v)] ∧ v < 2 ^ 32 := by
  simp only [argU, Option.bind_eq_some_iff] at h
  obtain ⟨a, h1, hv⟩ := h
  obtain ⟨rfl, hlt⟩ := decU32_eq hv
  exact ⟨arg1_eq h1, hlt⟩

-- two U32s
def argUU (xs : List Arg) : Option (Nat × Nat) :=
  (arg2 xs).bind fun (a, b) => (decU32 a).bind fun v => (decU32 b).map fun w => (v, w)

theorem argUU_eq (h : argUU xs = some (v, w)) :
    xs = [(Q1, u32 v), (Q1, u32 w)] ∧ v < 2 ^ 32 ∧ w < 2 ^ 32 := by
  simp only [argUU, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨a, b⟩, h2, v', hv, w', hw, rfl, rfl⟩ := h
  obtain ⟨rfl, hlt⟩ := decU32_eq hv
  obtain ⟨rfl, hlt'⟩ := decU32_eq hw
  exact ⟨by rw [arg2_eq h2], hlt, hlt'⟩

-- one Nat
def argN (xs : List Arg) : Option Nat := (arg1 xs).bind (decNat · 0)

theorem argN_eq (h : argN xs = some m) : xs = [(Q1, Form.nat m)] := by
  simp only [argN, Option.bind_eq_some_iff] at h
  obtain ⟨a, h1, hm⟩ := h
  obtain ⟨rfl, -⟩ := decNat_eq hm
  exact arg1_eq h1

-- Results
-- -------

-- the Bools and the Cmps, made once
def trueT : Term := Form.bool true
def falseT : Term := Form.bool false
def boolT (b : Bool) : Term := if b then trueT else falseT

theorem boolT_eq : boolT b = Form.bool b := by cases b <;> rfl

def ltT : Term := cmpT .lt
def eqT : Term := cmpT .eq
def gtT : Term := cmpT .gt

def cmpTF : Ordering → Term
  | .lt => ltT
  | .eq => eqT
  | .gt => gtT

theorem cmpTF_eq : cmpTF o = cmpT o := by cases o <;> rfl

-- Runs
-- ----

-- the term and the number of steps of a call of op on xs
def Op.run : Op → List Arg → Option (Term × Nat)
  | shr, xs => (argU xs).map fun v => (mkU32 (v / 2), 34)
  | shrn, xs => (argUN xs).map fun (v, m) => (mkU32 (v >>> m), 1 + 35 * m)
  | shl, xs => (argU xs).map fun v => (mkU32 (2 * v % 4294967296), 34)
  | shln, xs => (argUN xs).map fun (v, m) =>
      (mkU32 (if m < 32 then (v <<< m) % 4294967296 else 0), 1 + 35 * m)
  | cmp, xs => (argUU xs).map fun (v, w) => let r := cmpFast v w; (cmpTF r.2, r.1 + 1)
  | is_eq, xs => (argUU xs).map fun (v, w) => let r := cmpFast v w; (boolT (r.2 == .eq), r.1 + 3)
  | is_ne, xs => (argUU xs).map fun (v, w) => let r := cmpFast v w; (boolT (r.2 != .eq), r.1 + 4)
  | is_lt, xs => (argUU xs).map fun (v, w) => let r := cmpFast v w; (boolT (r.2 == .lt), r.1 + 3)
  | is_le, xs => (argUU xs).map fun (v, w) => let r := cmpFast v w; (boolT (r.2 != .gt), r.1 + 3)
  | is_gt, xs => (argUU xs).map fun (v, w) => let r := cmpFast v w; (boolT (r.2 == .gt), r.1 + 3)
  | is_ge, xs => (argUU xs).map fun (v, w) => let r := cmpFast v w; (boolT (r.2 != .lt), r.1 + 3)
  | is_zero, xs => (argU xs).map fun v => let r := cmpFast v 0; (boolT (r.2 == .eq), r.1 + 5)
  | and, xs => (argUU xs).map fun (v, w) => (mkU32 (v &&& w), 66)
  | or, xs => (argUU xs).map fun (v, w) => (mkU32 (v ||| w), 66)
  | inc, xs => (argU xs).map fun v => (mkU32 ((v + 1) % 4294967296), incC 32 v + 1)
  -- the nat of a large U32 is too large a term: the machine makes it
  | to_nat, xs => (argU xs).bind fun v =>
      if v < 65536 then some (natUp v (Form.nat 0), tnF 32 v 0 + 1) else none
  | from_nat, xs => (argN xs).map fun m => (mkU32 (m % 4294967296), fnF m 0)
  | add, xs => (argUU xs).map fun (v, w) => let r := adcCV 32 v w false false; (mkU32 r.1, r.2 + 3)
  | sub, xs => (argUU xs).map fun (v, w) => let r := adcCV 32 v w true true; (mkU32 r.1, r.2 + 3)
  | lit _ t, xs => if xs.isEmpty then some (t, 1) else none

theorem all_has {ds : List (String × Term)} (h : (ds.all fun d => has bk d.1 d.2) = true) : ∀ d ∈ ds, Has bk d.1 d.2 :=
  fun d hd => has_sound (List.all_eq_true.1 h d hd)

theorem Op.run_sound (hok : Op.ok bk k op = true) (h : Op.run op xs = some (r, n)) :
    Steps bk n (spine (Ref k) xs) r ∧ Value bk r := by
  cases op
  case lit v t =>
    simp only [Op.ok, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨hk, rfl⟩ := hok
    simp only [Op.run] at h
    split at h
    next he =>
      cases h
      obtain rfl := List.isEmpty_iff.1 he
      exact ⟨lit_steps (has_sound hk), value_u32⟩
    next => cases h
  all_goals
    simp only [Op.ok, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨rfl, hd⟩ := hok
    have hd := all_has hd
    simp only [Op.defs, shrDefs, shlDefs, cmpDefs, adcDefs, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, or_false,
      forall_eq, implies_true, and_true] at hd
    simp only [Op.run, Option.map_eq_some_iff, Option.bind_eq_some_iff, Prod.mk.injEq] at h
  case shr =>
    obtain ⟨v, hv, rfl, rfl⟩ := h
    obtain ⟨rfl, hlt⟩ := argU_eq hv
    refine ⟨?_, by rw [mkU32_eq]; exact value_u32⟩
    rw [mkU32_eq, ← shrV_32 hlt]
    exact u32_shr_steps ⟨hd.1, hd.2.1, hd.2.2⟩
  case shrn =>
    obtain ⟨⟨v, m⟩, hv, rfl, rfl⟩ := h
    obtain ⟨rfl, hlt⟩ := argUN_eq hv
    refine ⟨?_, by rw [mkU32_eq]; exact value_u32⟩
    rw [mkU32_eq, ← shrnV_eq hlt]
    exact u32_shrn_steps ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2⟩
  case shl =>
    obtain ⟨v, hv, rfl, rfl⟩ := h
    obtain ⟨rfl, hlt⟩ := argU_eq hv
    refine ⟨?_, by rw [mkU32_eq]; exact value_u32⟩
    rw [mkU32_eq, ← two32, ← shlV_eq]
    exact u32_shl_steps ⟨hd.1, hd.2.1, hd.2.2⟩
  case shln =>
    obtain ⟨⟨v, m⟩, hv, rfl, rfl⟩ := h
    obtain ⟨rfl, hlt⟩ := argUN_eq hv
    refine ⟨?_, by rw [mkU32_eq]; exact value_u32⟩
    rw [mkU32_eq, ← shln_fast hlt]
    exact u32_shln_steps ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2⟩
  case to_nat =>
    obtain ⟨v, hv, e⟩ := h
    obtain ⟨rfl, hlt⟩ := argU_eq hv
    split at e
    next =>
      obtain ⟨rfl, rfl⟩ := e
      rw [natUp_eq, tnF_eq hlt, Nat.zero_add, Nat.zero_add]
      refine ⟨?_, value_nat⟩
      have := u32_to_nat_steps (v := v) ⟨hd.1, hd.2.1, hd.2.2⟩
      rwa [padV_eq, Nat.mod_eq_of_lt hlt] at this
    next => cases e
  case from_nat =>
    obtain ⟨m, hm, rfl, rfl⟩ := h
    obtain rfl := argN_eq hm
    rw [mkU32_eq, fnF_eq, Nat.zero_add, show (4294967296 : Nat) = 2 ^ 32 from rfl, ← u32_fnV]
    exact ⟨u32_from_nat_steps ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2⟩, value_u32⟩
  all_goals first
    | (obtain ⟨⟨v, w⟩, hv, rfl, rfl⟩ := h; obtain ⟨rfl, hv, hw⟩ := argUU_eq hv
       try rw [cmpFast_eq hv hw])
    | (obtain ⟨v, hv, rfl, rfl⟩ := h; obtain ⟨rfl, hv⟩ := argU_eq hv
       try rw [cmpFast_eq hv (Nat.two_pow_pos 32)])
  all_goals simp only [cmpTF_eq, boolT_eq, mkU32_eq, adcCV_eq]
  case add =>
    exact ⟨u32_adc_steps (u32_add_eq ▸ hd.1) (word_add_eq ▸ hd.2.1)
      ⟨hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2⟩, value_u32⟩
  case sub =>
    exact ⟨u32_adc_steps (u32_sub_eq ▸ hd.1) (word_sub_eq ▸ hd.2.1)
      ⟨hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2⟩, value_u32⟩
  case and =>
    rw [show u32 (v &&& w) = u32 (andV 32 v w) by rw [andV_eq, u32, u32, bits_mod]]
    exact ⟨u32_and_steps ⟨hd.1, hd.2.1, hd.2.2⟩, value_u32⟩
  case or =>
    rw [show u32 (v ||| w) = u32 (orV 32 v w) by rw [orV_eq, u32, u32, bits_mod]]
    exact ⟨u32_or_steps ⟨hd.1, hd.2.1, hd.2.2⟩, value_u32⟩
  case inc =>
    rw [show (4294967296 : Nat) = 2 ^ 32 from rfl, ← u32_incV]
    exact ⟨u32_inc_steps ⟨hd.1, hd.2⟩, value_u32⟩
  case cmp => exact ⟨u32_cmp_steps ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2⟩, value_cmpT⟩
  case is_eq =>
    exact ⟨u32_is_steps hd.1 (value_ref hd.2.1 rfl) (fun _ => is_eq_steps hd.2.1)
      ⟨hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2⟩, value_bool⟩
  case is_lt =>
    exact ⟨u32_is_steps hd.1 (value_ref hd.2.1 rfl) (fun _ => is_lt_steps hd.2.1)
      ⟨hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2⟩, value_bool⟩
  case is_le =>
    exact ⟨u32_is_steps hd.1 (value_ref hd.2.1 rfl) (fun _ => is_le_steps hd.2.1)
      ⟨hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2⟩, value_bool⟩
  case is_gt =>
    exact ⟨u32_is_steps hd.1 (value_ref hd.2.1 rfl) (fun _ => is_gt_steps hd.2.1)
      ⟨hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2⟩, value_bool⟩
  case is_ge =>
    exact ⟨u32_is_steps hd.1 (value_ref hd.2.1 rfl) (fun _ => is_ge_steps hd.2.1)
      ⟨hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2⟩, value_bool⟩
  case is_ne =>
    exact ⟨u32_is_ne_steps hd.1 hd.2.1 hd.2.2.1
      ⟨hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩, value_bool⟩
  case is_zero =>
    rw [cmpFast_eq (by assumption) (Nat.two_pow_pos 32)]
    exact ⟨u32_is_zero_steps hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1
      ⟨hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2⟩, value_bool⟩

-- The table
-- ---------

-- the operations that Ops.prepare found in the book, by the name of their def
structure Table where
  ops : Std.HashMap String Op

-- the operations with a name of their own
def named : List Op := [.shr, .shrn, .shl, .shln, .cmp, .is_eq, .is_ne, .is_lt, .is_le, .is_gt,
  .is_ge, .is_zero, .and, .or, .inc, .to_nat, .from_nat, .add, .sub]

def addNamed (bk : Book) (m : Std.HashMap String Op) (op : Op) : Std.HashMap String Op :=
  if op.ok bk op.name then m.insert op.name op else m

-- a def U32.litN whose term is a U32
def addLit (bk : Book) (m : Std.HashMap String Op) (d : Def) : Std.HashMap String Op :=
  if d.k.startsWith "U32.lit" then
    match decU32 d.v with
    | some v => if (Op.lit v (mkU32 v)).ok bk d.k then m.insert d.k (.lit v (mkU32 v)) else m
    | none => m
  else m

def prepare (bk : Book) : Table :=
  ⟨bk.defs.foldl (addLit bk) (named.foldl (addNamed bk) ∅)⟩

-- the fast call: the term that Eval reaches from the call of the def k on xs,
-- and its exact number of steps; none when k is no operation of the table, or
-- the arguments are not what it takes
def call (tb : Table) (k : String) (xs : List Arg) : Option (Term × Nat) :=
  match tb.ops[k]? with
  | some op => op.run xs
  | none => none

-- each operation of a map is one that the book holds under its name
def Sound (bk : Book) (m : Std.HashMap String Op) : Prop :=
  ∀ (k : String) (op : Op), m[k]? = some op → op.ok bk k = true

theorem Sound.insert (s : Sound bk m) (h : op.ok bk k = true) : Sound bk (m.insert k op) := by
  unfold Sound; intro k' op' e
  rw [Std.HashMap.getElem?_insert] at e
  split at e
  next hk => cases e; rw [← beq_iff_eq.1 hk]; exact h
  next => exact s k' op' e

theorem prepare_sound : Sound bk (prepare bk).ops := by
  have h0 : Sound bk (∅ : Std.HashMap String Op) := by unfold Sound; intro k op e; simp at e
  have h1 : ∀ (ops : List Op) m, Sound bk m → Sound bk (ops.foldl (addNamed bk) m) := by
    intro ops
    induction ops with
    | nil => exact fun _ s => s
    | cons op ops ih =>
      intro m s
      refine ih _ ?_
      unfold addNamed
      split
      next h => exact s.insert h
      next => exact s
  have h2 : ∀ (ds : List Def) m, Sound bk m → Sound bk (ds.foldl (addLit bk) m) := by
    intro ds
    induction ds with
    | nil => exact fun _ s => s
    | cons d ds ih =>
      intro m s
      refine ih _ ?_
      unfold addLit
      split
      · split
        · split
          next h => exact s.insert h
          next => exact s
        · exact s
      · exact s
  exact h2 _ _ (h1 _ _ h0)

theorem call_sound (h : call (prepare bk) k xs = some (r, n)) :
    Steps bk n (Term.spine (Ref k) xs) r ∧ Value bk r := by
  unfold call at h
  split at h
  next op e => exact Op.run_sound (prepare_sound k op e) h
  next => cases h

end Ops
