import Step

-- GenRef
-- ======
--
-- Writes src/Word/Ref.lean from the BendTT text that bend gives for
-- scripts/ref.bend. From bootstrap/lean, run bend in WSL, and lake where Lean
-- is installed. <version> is what `bend version` prints.
--   bend scripts/ref.bend -o .lake/ref.bendtt
--   lake build Step
--   lake env lean --run scripts/GenRef.lean .lake/ref.bendtt src/Word/Ref.lean "<version>"
-- Then review the diff of Ref.lean. When base changes a def that a family
-- needs, the family does not jump until this script runs again and the
-- proofs in src/Word/ build on the new body.

-- the defs that Ref.lean copies: each def that the proofs in src/Word/ name
def names : List String :=
  ["Bool.not", "Bool.and", "Bool.or", "Bool.xor", "Bool.cmp", "Bool.full_add",
   "Nat.double", "Word.not", "Word.and", "Word.or", "Word.xor", "Word.inc",
   "Word.shl.put", "Word.shl", "Word.shr.pad", "Word.shr", "Word.cmp.fin", "Word.cmp",
   "Word.to_nat", "Word.adc.group", "Word.add", "Word.mul.go"]

def header (version : String) : String :=
  "import Step\n\n-- Word.Ref\n-- ========\n--\n" ++
  "-- GENERATED. The bodies of base's word code, as bend -o gives them: R.k is\n" ++
  "-- the body of def k. Made by scripts/GenRef.lean from scripts/ref.bend (a\n" ++
  s!"-- program whose book has each def below) with {version}, the repo's\n" ++
  "-- source in WSL. Do not edit: GenRef.lean has the commands.\n\n" ++
  "open Quan Term\n\n"

def main (args : List String) : IO UInt32 := do
  let [src, out, version] := args
    | IO.eprintln "usage: GenRef <file.bendtt> <Ref.lean> <bend version>"; return 2
  let bk ← match Book.parse (← IO.FS.readFile src) with
    | .ok bk => pure bk
    | .error e => throw (IO.userError e)
  let mut text := header version
  for k in names do
    let some d := bk.get k | throw (IO.userError s!"def {k} is not in {src}")
    if d.o then throw (IO.userError s!"def {k} is opaque in {src}")
    text := text ++ s!"def R.{k} : Term :=\n  {(reprStr d.v).replace "\n" "\n  "}\n\n"
  IO.FS.writeFile out text
  return 0
