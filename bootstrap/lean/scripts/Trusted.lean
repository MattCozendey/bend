import Bootstrap.Script
import Bootstrap.Trusted
import Bootstrap.OrLaw

-- Trusted
-- =======
--
-- Checks that the book of a .bendtt file (trusted.bend's) holds what
-- Trusted (src/Bootstrap/Trusted.lean) asks: each def of trustedDefs and
-- existsCopy, and a def of the type of each law. It runs the definitions,
-- it proves nothing: the theorems take Trusted B as a premise.
--
--   bend bootstrap/bend/src/compiler/trusted.bend -o trusted.bendtt
--   BOOK=trusted.bendtt lake lean scripts/Trusted.lean
--
-- (While proof.bend has open TODOs, `bend -o` refuses trusted.bend;
-- scripts/lower.ts writes the same lowering with each hole read as its own
-- def, which changes no def or type that Trusted names.)

def same (a b : Def) : Bool := a.k == b.k && a.T == b.T && a.v == b.v && a.o == b.o

def check : IO Unit := do
  let bk ← Script.book
  let ds := trustedDefs ++ existsCopy
  let bad := ds.filter fun d => match bk.get d.k with
    | some d' => !same d d'
    | none => true
  let badLaws := laws.filter fun (k, T) => match bk.get k with
    | some d => d.T != Rename.term impl T
    | none => true
  IO.println s!"{ds.length} defs, {laws.length} laws; missing or different: {bad.map (·.k) ++ badLaws.map (·.1)}"
  if !bad.isEmpty || !badLaws.isEmpty then throw (IO.userError "the book does not hold Trusted's defs")

#eval check
