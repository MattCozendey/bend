import Bootstrap.Script

-- Defs
-- ====
--
-- Writes a Lean copy of some defs that the kernel's parser reads from a
-- .bendtt file, as scripts/Copy.lean does, but of chosen defs only, for the
-- laws about our Bend code (src/Bootstrap/Code.lean):
--
--   ROOTS    the defs that these names need, them included (as Copy.lean),
--   EXCLUDE  minus the defs that these names need (copied elsewhere),
--   ONLY     plus these defs alone, without the defs they need,
--   TYPES    plus the name and type of these defs, without their bodies: a
--            law that a Lean theorem uses only needs a def of its type,
--            whatever its proof,
--   STRIP    with this prefix taken off each name that has it, and
--            NAME.names: each name of the book that has it, without it,
--
--   bend <file.bend> -o <file.bendtt>
--   BOOK=<file.bendtt> NAME=<name> SOURCE=<file.bend> OUTPUT=<file.lean> \
--     [ROOTS=..] [EXCLUDE=..] [ONLY=..] [TYPES=..] [STRIP=<prefix>] \
--     lake lean scripts/Defs.lean
--
-- Each list is names separated by commas, in the file's names (prefix
-- included). The Lean file defines a def «NAME.k» : Def per def k, and
-- NAME : List Def, and a «NAME.k» : String × Term per type. A term that is
-- the form of a Nat n > 1 (as `bend -o` writes it, Succ{..}) is written
-- Form.nat n, which is that term: `bend -o` writes a literal 2^24 as
-- thousands of nested pairs, too deep for Lean to read.

open Term

-- the names of the defs that t refers to
def refs : Term → List String
  | Ref k => [k]
  | Typ a | Prj a | Lam _ a => refs a
  | Ann a b | Term.Min a b | Let _ a b | All _ a b | App _ a b | Sig _ a b | Tup _ a b
  | Mat _ a b => refs a ++ refs b
  | Eql a b c | Rwt a b c => refs a ++ refs b ++ refs c
  | Var _ | Enu _ | Lab _ | Efq | Rfl => []

-- the names that the names ks need, ks among them (as Copy.lean)
def needs (bk : Book) (ks : List String) : List String :=
  (List.range bk.defs.length).foldl (init := ks) fun seen _ =>
    (seen ++ seen.flatMap fun k => ((bk.get k).map fun d => refs d.T ++ refs d.v).getD []).eraseDups

-- every name and label of t
def names : Term → List String
  | Ref k | Lab k => [k]
  | Mat k a b => k :: names a ++ names b
  | Enu ks => ks
  | Typ a | Prj a | Lam _ a => names a
  | Ann a b | Term.Min a b | Let _ a b | All _ a b | App _ a b | Sig _ a b | Tup _ a b =>
    names a ++ names b
  | Eql a b c | Rwt a b c => names a ++ names b ++ names c
  | Var _ | Efq | Rfl => []

-- k without the prefix p, when it has it
def unprefixName (p k : String) : String :=
  if p.isPrefixOf k then String.ofList (k.toList.drop p.length) else k

def Term.unprefix (p : String) : Term → Term
  | Ref k => Ref (unprefixName p k)
  | Lab k => Lab (unprefixName p k)
  | Mat k a b => Mat (unprefixName p k) (Term.unprefix p a) (Term.unprefix p b)
  | Enu ks => Enu (ks.map (unprefixName p))
  | Typ a => Typ (Term.unprefix p a)
  | Prj a => Prj (Term.unprefix p a)
  | Lam q a => Lam q (Term.unprefix p a)
  | Ann a b => Ann (Term.unprefix p a) (Term.unprefix p b)
  | Term.Min a b => Term.Min (Term.unprefix p a) (Term.unprefix p b)
  | Let q a b => Let q (Term.unprefix p a) (Term.unprefix p b)
  | All q a b => All q (Term.unprefix p a) (Term.unprefix p b)
  | App q a b => App q (Term.unprefix p a) (Term.unprefix p b)
  | Sig q a b => Sig q (Term.unprefix p a) (Term.unprefix p b)
  | Tup q a b => Tup q (Term.unprefix p a) (Term.unprefix p b)
  | Eql a b c => Eql (Term.unprefix p a) (Term.unprefix p b) (Term.unprefix p c)
  | Rwt a b c => Rwt (Term.unprefix p a) (Term.unprefix p b) (Term.unprefix p c)
  | t => t

-- the n of a term that is the form of the Nat n
def natOf : Term → Option Nat
  | Tup .Q1 (Lab "Zero") (Lab "()") => some 0
  | Tup .Q1 (Lab "Succ") (Tup .Q1 t (Lab "()")) => (natOf t).map (· + 1)
  | _ => none

def quan : Quan → String
  | .Q0 => "Quan.Q0"
  | .Q1 => "Quan.Q1"
  | .Q2 => "Quan.Q2"

-- t as Lean code, on one line
partial def lean (t : Term) : String :=
  match natOf t with
  | some n => if n > 1 then s!"(Form.nat {n})" else go t
  | none => go t
where
  go : Term → String
  | Var i => s!"(Term.Var {i})"
  | Ref k => s!"(Term.Ref {repr k})"
  | Ann a b => s!"(Term.Ann {lean a} {lean b})"
  | Let q a b => s!"(Term.Let {quan q} {lean a} {lean b})"
  | Typ a => s!"(Term.Typ {lean a})"
  | Term.Min a b => s!"(Term.Min {lean a} {lean b})"
  | All q a b => s!"(Term.All {quan q} {lean a} {lean b})"
  | Lam q a => s!"(Term.Lam {quan q} {lean a})"
  | App q a b => s!"(Term.App {quan q} {lean a} {lean b})"
  | Sig q a b => s!"(Term.Sig {quan q} {lean a} {lean b})"
  | Tup q a b => s!"(Term.Tup {quan q} {lean a} {lean b})"
  | Prj a => s!"(Term.Prj {lean a})"
  | Enu ks => s!"(Term.Enu {repr ks})"
  | Lab k => s!"(Term.Lab {repr k})"
  | Mat k a b => s!"(Term.Mat {repr k} {lean a} {lean b})"
  | Efq => "Term.Efq"
  | Eql a b c => s!"(Term.Eql {lean a} {lean b} {lean c})"
  | Rfl => "Term.Rfl"
  | Rwt a b c => s!"(Term.Rwt {lean a} {lean b} {lean c})"

def list (k : String) : IO (List String) := do
  match ← IO.getEnv k with
  | some v => pure ((v.splitOn ",").filter (· != ""))
  | none => pure []

def copyDefs : IO Unit := do
  let name ← Script.env "NAME"
  let bk ← Script.book
  let p := (← IO.getEnv "STRIP").getD ""
  let roots ← list "ROOTS"
  let ex := needs bk (← list "EXCLUDE")
  let ks := (needs bk roots).filter (!ex.contains ·) ++ (← list "ONLY")
  let ds := bk.defs.filter (ks.contains ·.k)
  let ts := (← list "TYPES").filterMap bk.get
  let k' (k : String) := unprefixName p k
  let defs := String.join <| ds.map fun d =>
    s!"def «{name}.{k' d.k}» : Def :=\n  ⟨{repr (k' d.k)},\n    {lean (d.T.unprefix p)},\n" ++
    s!"    {lean (d.v.unprefix p)},\n    {d.o}⟩\n\n"
  let types := String.join <| ts.map fun d =>
    s!"def «{name}.{k' d.k}» : String × Term :=\n  ({repr (k' d.k)},\n    {lean (d.T.unprefix p)})\n\n"
  let all := (bk.defs.flatMap fun d => d.k :: names d.T ++ names d.v).eraseDups
  let ns := if p == "" then "" else
    s!"def {name}.names : List String :=\n  {repr ((all.filter p.isPrefixOf).map k')}\n\n"
  IO.FS.writeFile (← Script.env "OUTPUT") <|
    s!"import Bootstrap.Book\n\n-- Made by scripts/Defs.lean from the `bend -o` output of {← Script.env "SOURCE"}.\n" ++
    "-- Do not edit it.\n\nopen Quan Term\n\nset_option maxRecDepth 100000\n\n" ++ defs ++ types ++ ns ++
    s!"def {name} : List Def :=\n  [" ++ ",\n   ".intercalate (ds.map fun d => s!"«{name}.{k' d.k}»") ++ "]\n"
  IO.println s!"{ds.length} defs, {ts.length} types"

#eval copyDefs
