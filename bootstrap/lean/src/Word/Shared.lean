import Word.Ref

-- Word.Shared
-- ===========
--
-- What the word families share: their terms, the check of a def's body,
-- the decoders, and the tools of the round proofs. A round proof (x_round)
-- follows Eval on a call of a word def to a term with the next call, or to
-- the result. The rest of each word stays open (wordT t). x_round0 is the
-- last round, on 0 or on empty words. An induction on the rounds then
-- proves, for each width, that a call reaches the result of a Lean
-- function, like adcBits.

open Quan Term Contract

namespace Interp.Word

-- Terms
-- =====

def bitT (b : Bool) : Term := Tup Q1 (Lab (if b then "True" else "False")) (Lab "()")

-- cellT h t: the word cell of the lowest bit h and the rest t
def cellT (h t : Term) : Term := Tup Q1 (Lab "WCon") (Tup Q1 h (Tup Q1 t (Lab "()")))

def wordT : List Bool → Term
  | [] => Tup Q1 (Lab "WNil") (Lab "()")
  | b :: bs => cellT (bitT b) (wordT bs)

def succT (n : Term) : Term := Tup Q1 (Lab "Succ") (Tup Q1 n (Lab "()"))

-- boxT k x: k{x}, for a one-field constructor k, like U32 or Succ
def boxT (k : String) (x : Term) : Term := Tup Q1 (Lab k) (Tup Q1 x (Lab "()"))

def cmpT (o : Ordering) : Term :=
  Tup Q1 (Lab (match o with | .lt => "LT" | .eq => "EQ" | .gt => "GT")) (Lab "()")

-- callT k xs: def k applied to xs, each at quantity 1
def callT (k : String) (xs : List Term) : Term := spine (Ref k) (xs.map (Q1, ·))

-- Refs
-- ====

-- HasRef bk k r: def k of bk has the body r
def HasRef (bk : Book) (k : String) (r : Term) : Prop := ∃ d, bk.get k = some d ∧ d.v = r

def hasRef (bk : Book) (k : String) (r : Term) : Bool := (bk.get k).map (·.v) == some r

theorem hasRef_sound (h : hasRef bk k r = true) : HasRef bk k r := by
  simp only [hasRef, beq_iff_eq, Option.map_eq_some_iff] at h; exact h

-- Values
-- ======

theorem value_step (v : isValue bk t = true) : step bk t = none := by
  cases h : step bk t with
  | none => rfl
  | some u => exact (eval_value (step_sound h) (isValue_iff.1 v)).elim

theorem bit_isValue : isValue bk (bitT b) = true := by
  cases b <;> simp [bitT, isValue, Quan.live]

theorem bit_isData : isData (bitT b) = true := by
  cases b <;> simp [bitT, isData, Quan.live]

theorem word_isValue : isValue bk (wordT bs) = true := by
  induction bs with
  | nil => simp [wordT, isValue]
  | cons b bs ih => simp [wordT, cellT, isValue, Quan.live, ih, bit_isValue]

theorem word_isData : isData (wordT bs) = true := by
  induction bs with
  | nil => simp [wordT, isData]
  | cons b bs ih => simp [wordT, cellT, isData, Quan.live, ih, bit_isData]

theorem nat_isValue : isValue bk (Bytes.nat n) = true := by
  induction n with
  | zero => simp [Bytes.nat, isValue]
  | succ n ih => simp [Bytes.nat, isValue, Quan.live, ih]

theorem nat_isData : isData (Bytes.nat n) = true := by
  induction n with
  | zero => simp [Bytes.nat, isData]
  | succ n ih => simp [Bytes.nat, isData, Quan.live, ih]

theorem word_step : step bk (wordT bs) = none := value_step word_isValue

theorem nat_step : step bk (Bytes.nat n) = none := value_step nat_isValue

-- Rounds
-- ======

-- stepUntil bk stop n t: the first term of the step chain from t where stop
-- holds or no step fits; none when the first n terms do not have it
def stepUntil (bk : Book) (stop : Term → Bool) : Nat → Term → Option Term
  | 0, _ => none
  | n + 1, t =>
    if stop t then some t else
    match step bk t with
    | some u => stepUntil bk stop n u
    | none => some t

theorem stepUntil_sound : stepUntil bk stop n t = some u → Evals bk t u := by
  induction n generalizing t with
  | zero => simp [stepUntil]
  | succ n ih =>
    simp only [stepUntil]; split
    · simp only [Option.some.injEq]; rintro rfl; exact .refl
    · split
      · rename_i u' h; exact fun e => .step (step_sound h) (ih e)
      · simp only [Option.some.injEq]; rintro rfl; exact .refl

-- headIs k t: the head of t is Ref k
def headIs (k : String) (t : Term) : Bool := (unspine t []).1 == Ref k

-- a word cell whose bit is known and whose rest is a call of def k
def cellEnd (k : String) : Term → Bool
  | Tup _ (Lab "WCon") (Tup _ (Tup _ (Lab _) (Lab "()")) (Tup _ x (Lab "()"))) => headIs k x
  | _ => false

-- word_simp: the simp set of a round proof. It unfolds stepUntil and step on
-- terms whose words and numbers stay open. These terms are large, so it
-- sets higher limits.
macro "word_simp" "[" xs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| set_option maxHeartbeats 0 in set_option maxRecDepth 100000 in
    simp (config := { maxSteps := 50000000 }) [stepUntil, step, call, fires, isArgs,
    isValue, stops, unspine, walk, redex, isData, Quan.live, Quan.fld, takes, spine, Term.sub,
    Env.sub, bitT, cellT, callT, succT, boxT, cellEnd, headIs, nat_isValue, nat_isData, word_isValue,
    word_isData, nat_step, word_step, $xs,*])

-- Eval steps in the rest of a word cell
theorem evals_rest (h : Evals bk x x') : Evals bk (cellT (bitT s) x) (cellT (bitT s) x') := by
  have vs := isValue_iff.1 (bit_isValue (bk := bk) (b := s))
  exact evals_map (fun y => cellT (bitT s) y)
    (fun e => .tup_b (fun _ => .lab) (.tup_b (fun _ => vs) (.tup_a rfl e))) h

-- Eval steps in the field of boxT k
theorem evals_box (k : String) (h : Evals bk x x') : Evals bk (boxT k x) (boxT k x') :=
  evals_map (boxT k) (fun e => .tup_b (fun _ => .lab) (.tup_a rfl e)) h

-- Eval steps in the argument of an App whose function is a value
theorem evals_arg (vf : isValue bk f = true) (l : q.live = true) (h : Evals bk x x') :
    Evals bk (App q f x) (App q f x') :=
  evals_map (App q f ·) (fun e => .app_x (isValue_iff.1 vf) l e) h

-- an App that reaches a tuple makes one or more Eval steps
theorem plus_tup (h : Evals bk (App q f x) u) (e : ∃ p a b, u = Tup p a b) :
    Plus bk (App q f x) u :=
  plus_of h fun h' => by obtain ⟨_, _, _, rfl⟩ := e; cases h'

theorem word_tup : ∃ q a b, wordT bs = Tup q a b := by
  cases bs <;> exact ⟨_, _, _, rfl⟩

theorem nat_tup : ∃ q a b, Bytes.nat v = Tup q a b := by
  cases v <;> exact ⟨_, _, _, rfl⟩

-- Decoders
-- ========

def decBit : Term → Option Bool
  | Tup Q1 (Lab "True") (Lab "()") => some true
  | Tup Q1 (Lab "False") (Lab "()") => some false
  | _ => none

def decWord : Term → Option (List Bool)
  | Tup Q1 (Lab "WNil") (Lab "()") => some []
  | Tup Q1 (Lab "WCon") (Tup Q1 h (Tup Q1 t (Lab "()"))) => do
    let b ← decBit h
    let bs ← decWord t
    pure (b :: bs)
  | _ => none

def decNat : Term → Option Nat
  | Tup Q1 (Lab "Zero") (Lab "()") => some 0
  | Tup Q1 (Lab "Succ") (Tup Q1 n (Lab "()")) => (decNat n).map (· + 1)
  | _ => none

theorem decBit_sound (h : decBit t = some b) : t = bitT b := by
  unfold decBit at h
  split at h <;> simp_all [bitT]

theorem decWord_sound (h : decWord t = some bs) : t = wordT bs := by
  fun_induction decWord t generalizing bs with
  | case1 => cases h; rfl
  | case2 hd tl ih =>
    cases hb : decBit hd with
    | none => simp [hb] at h
    | some b =>
      cases ht : decWord tl with
      | none => simp [hb, ht] at h
      | some bs' =>
        simp [hb, ht] at h; subst h
        simp [wordT, cellT, decBit_sound hb, ih ht]
  | case3 => simp at h

theorem decNat_sound (h : decNat t = some n) : t = Bytes.nat n := by
  fun_induction decNat t generalizing n with
  | case1 => cases h; rfl
  | case2 m ih =>
    obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.1 h
    simp [Bytes.nat, ih hk]
  | case3 => simp at h

end Interp.Word
