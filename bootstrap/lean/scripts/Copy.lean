import Bootstrap.Script

-- Copy
-- ====
--
-- Writes a Lean copy of the defs that the kernel's parser reads from a .bendtt
-- file, for the laws about our Bend code (src/Bootstrap/Code.lean): the defs
-- that the defs ROOTS need, them included, in the order of the file.
--
--   bend <file.bend> -o <file.bendtt>
--   BOOK=<file.bendtt> ROOTS=<name>,... NAME=<name> SOURCE=<file.bend> \
--     OUTPUT=<file.lean> lake lean scripts/Copy.lean
--
-- The Lean file defines a def «NAME.k» per def k, and NAME : List Def.

open Term

-- the names of the defs that t refers to
def refs : Term → List String
  | Ref k => [k]
  | Typ a | Prj a | Lam _ a => refs a
  | Ann a b | Term.Min a b | Let _ a b | All _ a b | App _ a b | Sig _ a b | Tup _ a b
  | Mat _ a b => refs a ++ refs b
  | Eql a b c | Rwt a b c => refs a ++ refs b ++ refs c
  | Var _ | Enu _ | Lab _ | Efq | Rfl => []

-- the names that the names ks need, ks among them: a book has no more rounds
-- of new names than defs
def needs (bk : Book) (ks : List String) : List String :=
  (List.range bk.defs.length).foldl (init := ks) fun seen _ =>
    (seen ++ seen.flatMap fun k => ((bk.get k).map fun d => refs d.T ++ refs d.v).getD []).eraseDups

-- the Lean def that copies d: one atomic name, so that it opens no namespace in
-- which a Bend name such as List hides Lean's
def copyDef (name : String) (d : Def) : String :=
  s!"def «{name}.{d.k}» : Def :=\n  ⟨{repr d.k},\n    {(repr d.T).pretty 100 4},\n" ++
  s!"    {(repr d.v).pretty 100 4},\n    {d.o}⟩\n\n"

def copyBook : IO Unit := do
  let name ← Script.env "NAME"
  let roots ← Script.env "ROOTS"
  let bk ← Script.book
  let ks := needs bk (roots.splitOn ",")
  let ds := bk.defs.filter (ks.contains ·.k)
  IO.FS.writeFile (← Script.env "OUTPUT") <|
    s!"import bendtt\n\n-- Made by scripts/Copy.lean from the `bend -o` output of {← Script.env "SOURCE"},\n" ++
    s!"-- for the roots {roots}, and the defs that they need. Do not edit it.\n\nopen Quan Term\n\n" ++
    String.join (ds.map (copyDef name)) ++
    s!"def {name} : List Def :=\n  [" ++ ",\n   ".intercalate (ds.map fun d => s!"«{name}.{d.k}»") ++ "]\n"
  IO.println s!"{ds.length} defs"

#eval copyBook
