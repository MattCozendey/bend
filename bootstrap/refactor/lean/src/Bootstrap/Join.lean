import Bootstrap.Code

-- Join
-- ====
--
-- Step 3 of the plan: what the Bend laws that --verdict accepts say about
-- runs. --verdict is Book.check on the kernel's parse of the `bend -o` text.
-- The kernel's adequate (bend2/bendtt.lean) turns a checked proof of a == b
-- into a conversion of a and b, and conv_runs turns that into a run.

open Quan Term

-- Data with no dead part: labels, Rfl, and pairs of it at a live quantity
inductive Plain : Term → Prop
  | lab : Plain (Lab k)
  | rfl : Plain Rfl
  | tup : q.live = true → Plain a → Plain b → Plain (Tup q a b)

-- in a book that --verdict accepts, a closed, live term a of a Data type,
-- that converts to the plain b, runs to b
theorem conv_runs : Book.check B = .ok () → Term.Closed a → Term.Live B a →
    Typed B [] a A → Typed B [] A T2 → Plain b → Conv B a b → Runs B a b := sorry
