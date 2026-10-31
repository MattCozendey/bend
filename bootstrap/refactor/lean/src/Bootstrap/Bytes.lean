import bendtt

-- Bytes
-- =====
--
-- INVARIANTS #3's list of bytes, as `bend -o` writes a value of Base's
-- List<&2, U32>: a constructor k{x, y} is the tuple (.k, x, y, ()) at
-- quantity 1, and each cell is a U32 below 256, whose Word(32n) has the
-- lowest bit first.

open Quan Term

-- the constructor k with the fields fs
def ctor (k : String) (fs : List Term) : Term :=
  Tup Q1 (Lab k) (fs.foldr (Tup Q1) (Lab "()"))

-- the Word(n) of v
def bits : Nat → Nat → Term
  | 0, _ => ctor "WNil" []
  | n + 1, v => ctor "WCon" [ctor (if v % 2 = 1 then "True" else "False") [], bits n (v / 2)]

def bytes : List UInt8 → Term
  | [] => ctor "Nil" []
  | b :: bs => ctor "Con" [ctor "U32" [bits 32 b.toNat], bytes bs]

-- the value of a Word(n)
def unbits : Nat → Term → Option Nat
  | 0, Tup Q1 (Lab "WNil") (Lab "()") => some 0
  | n + 1, Tup Q1 (Lab "WCon") (Tup Q1 (Tup Q1 (Lab b) (Lab "()")) (Tup Q1 w (Lab "()"))) =>
    if b = "True" then (unbits n w).map (2 * · + 1)
    else if b = "False" then (unbits n w).map (2 * ·)
    else none
  | _, _ => none

def unbytes : Term → Option (List UInt8)
  | Tup Q1 (Lab "Nil") (Lab "()") => some []
  | Tup Q1 (Lab "Con") (Tup Q1 (Tup Q1 (Lab "U32") (Tup Q1 w (Lab "()"))) (Tup Q1 t (Lab "()"))) =>
    match unbits 32 w, unbytes t with
    | some v, some bs => if v < 256 then some (v.toUInt8 :: bs) else none
    | _, _ => none
  | _ => none

-- a word reads back as its value modulo 2 ^ n
theorem unbits_bits : unbits n (bits n v) = some (v % 2 ^ n) := by
  induction n generalizing v with
  | zero => simp [bits, ctor, unbits, Nat.mod_one]
  | succ n ih =>
    have h : v % 2 ^ (n + 1) = v % 2 + 2 * (v / 2 % 2 ^ n) := by
      rw [Nat.pow_succ', Nat.mod_mul]
    rcases Nat.mod_two_eq_zero_or_one v with hv | hv <;>
      simp [bits, ctor, unbits, ih, h, hv] <;> omega

-- the bytes come back from their term
theorem unbytes_bytes : unbytes (bytes i) = some i := by
  induction i with
  | nil => simp [bytes, ctor, unbytes]
  | cons b bs ih =>
    have hb : b.toNat < 256 := b.toNat_lt
    have h : b.toNat % 2 ^ 32 = b.toNat := Nat.mod_eq_of_lt (by omega)
    simp [bytes, ctor, unbytes, unbits_bits, h, ih]
    exact hb
