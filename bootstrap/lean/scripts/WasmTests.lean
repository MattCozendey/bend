import Bootstrap.Run
import Bootstrap.Book
import Bootstrap.Script

-- WasmTests
-- =========
--
-- A test of kind b (bend2 skill): the Bend copy of WASM (the section Wasm of
-- bootstrap/bend/src/compiler/impl.bend) against the official WebAssembly
-- tests of bootstrap/tests/wasm (W6), run by the Lean interpreter that the
-- plan trusts (src/Bootstrap/Run.lean), not by the TypeScript compiler.
--
--   bend bootstrap/bend/src/compiler/impl.bend -o <file.bendtt>
--   lake build Bootstrap.Run Bootstrap.Script
--   BOOK=<file.bendtt> TESTS=bootstrap/tests/wasm/bin ONLY=<test>,... \
--     OUT=<file.log> lake env lean scripts/WasmTests.lean
--
-- It runs each command of a binary script (spec interpreter README: Binary
-- Scripts) as the spec's harness does, and counts each assertion as passed,
-- failed, unsupported (the module or the values leave the subset, W1) or not
-- done (the model's fuel ran out). assert_invalid and assert_malformed pass
-- only when the model refuses the module: it may never accept a module that
-- the spec rejects (W1).

open Quan Term

-- S-expressions
-- -------------

inductive Sexp where
  | atom : String → Sexp
  | str : List UInt8 → Sexp
  | list : List Sexp → Sexp
  deriving Inhabited

partial def Sexp.show : Sexp → String
  | .atom a => a
  | .str bs => "\"" ++ String.join (bs.map fun b => s!"\\{(Nat.toDigits 16 b.toNat).asString}") ++ "\""
  | .list xs => "(" ++ " ".intercalate (xs.map Sexp.show) ++ ")"

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

-- the UTF-8 bytes of the code point c
def utf8 (c : Nat) : List UInt8 := (String.singleton (Char.ofNat c)).toUTF8.toList

-- the bytes of a string's body, up to its closing quote, and the rest
partial def strBody (cs : List Char) (acc : Array UInt8) : Except String (List UInt8 × List Char) :=
  match cs with
  | [] => .error "unclosed string"
  | '"' :: rest => .ok (acc.toList, rest)
  | '\\' :: 'n' :: rest => strBody rest (acc.push 10)
  | '\\' :: 't' :: rest => strBody rest (acc.push 9)
  | '\\' :: '\\' :: rest => strBody rest (acc.push 92)
  | '\\' :: '\'' :: rest => strBody rest (acc.push 39)
  | '\\' :: '"' :: rest => strBody rest (acc.push 34)
  | '\\' :: 'u' :: '{' :: rest =>
    let digits := rest.takeWhile (· ≠ '}')
    let v := digits.foldl (fun n c => n * 16 + (hexVal c).getD 0) 0
    strBody ((rest.dropWhile (· ≠ '}')).drop 1) (acc ++ (utf8 v).toArray)
  | '\\' :: a :: b :: rest =>
    match hexVal a, hexVal b with
    | some x, some y => strBody rest (acc.push (x * 16 + y).toUInt8)
    | _, _ => .error s!"bad escape \\{a}{b}"
  | c :: rest => strBody rest (acc ++ (utf8 c.toNat).toArray)

def isAtomChar (c : Char) : Bool := !(c.isWhitespace || c == '(' || c == ')' || c == '"' || c == ';')

-- the characters after a block comment (; ... ;), which may nest
partial def skipBlock (cs : List Char) (depth : Nat) : List Char :=
  match cs with
  | [] => []
  | ';' :: ')' :: rest => if depth = 0 then rest else skipBlock rest (depth - 1)
  | '(' :: ';' :: rest => skipBlock rest (depth + 1)
  | _ :: rest => skipBlock rest depth

-- the S-expressions of cs, up to a closing parenthesis (when inner) or the end
partial def parseSeq (cs : List Char) (inner : Bool) (acc : Array Sexp) :
    Except String (List Sexp × List Char) :=
  match cs with
  | [] => if inner then .error "unclosed (" else .ok (acc.toList, [])
  | ';' :: ';' :: rest => parseSeq (rest.dropWhile (· ≠ '\n')) inner acc
  | '(' :: ';' :: rest => parseSeq (skipBlock rest 0) inner acc
  | ')' :: rest => if inner then .ok (acc.toList, rest) else .error "unexpected )"
  | '(' :: rest => do
    let (xs, rest) ← parseSeq rest true #[]
    parseSeq rest inner (acc.push (.list xs))
  | '"' :: rest => do
    let (bs, rest) ← strBody rest #[]
    parseSeq rest inner (acc.push (.str bs))
  | c :: rest =>
    if c.isWhitespace then parseSeq rest inner acc
    else
      let a := (c :: rest).takeWhile isAtomChar
      parseSeq ((c :: rest).dropWhile isAtomChar) inner (acc.push (.atom (String.mk a)))

-- Values
-- ------

-- a U32, as Base's U32
def u32 (v : Nat) : Term := ctor "U32" [bits 32 v]

-- the constructor and fields of a value in the `bend -o` form (Bytes.lean)
partial def unctor : Term → Option (String × List Term)
  | Tup Q1 (Lab k) rest =>
    let rec fields : Term → Option (List Term)
      | Lab "()" => some []
      | Tup Q1 x r => (fields r).map (x :: ·)
      | _ => none
    (fields rest).map (k, ·)
  | _ => none

def unU32 (t : Term) : Option Nat :=
  match unctor t with
  | some ("U32", [w]) => unbits 32 w
  | _ => none

partial def unlist (t : Term) : Option (List Term) :=
  match unctor t with
  | some ("Nil", []) => some []
  | some ("Con", [x, xs]) => (unlist xs).map (x :: ·)
  | _ => none

-- an i32 literal of a binary script: hex, maybe negative, with _ between digits
def i32Lit (s : String) : Option Nat :=
  let (neg, cs) := match s.toList with
    | '-' :: rest => (true, rest)
    | cs => (false, cs)
  match cs with
  | '0' :: 'x' :: ds =>
    let ds := ds.filter (· ≠ '_')
    if ds.isEmpty then none else
      (ds.foldlM (fun n c => (hexVal c).map (n * 16 + ·)) 0).map fun v =>
        if neg then (2 ^ 32 - v % 2 ^ 32) % 2 ^ 32 else v % 2 ^ 32
  | _ => none

-- the i32 value of (i32.const n); None for any other value
def constOf : Sexp → Option Nat
  | .list [.atom "i32.const", .atom n] => i32Lit n
  | _ => none

-- Running
-- -------

structure Cfg where
  B : Book
  fuel : Term
  limit : Term

-- the value that t runs to, by the trusted interpreter
def evalTerm (c : Cfg) (t : Term) : Option Term :=
  let (v, _) := steps c.B 4000000000 t 0
  if value c.B v then some v else none

-- how an instantiation ends
inductive Made where
  | inst : Term → Made
  | unsupported | out_of_memory | trap | stuck

def instantiate (c : Cfg) (w : List UInt8) : Made :=
  match (evalTerm c (App Q1 (App Q1 (Ref "Wasm.instantiate") (bytes w)) c.limit)).bind unctor with
  | some ("Wasm.Made.instance", [i]) => .inst i
  | some ("Wasm.Made.unsupported", []) => .unsupported
  | some ("Wasm.Made.out_of_memory", []) => .out_of_memory
  | some ("Wasm.Made.trap", []) => .trap
  | _ => .stuck

-- how an invocation ends
inductive Invoked where
  | values : List Nat → Term → Invoked
  | trap : Term → Invoked
  | not_done | unsupported | stuck

def invoke (c : Cfg) (i : Term) (name : List UInt8) (args : List Nat) : Invoked :=
  let t := App Q1 (App Q1 (App Q1 (App Q1 (Ref "Wasm.invoke") c.fuel) i) (bytes name)) (list (args.map u32))
  match (evalTerm c t).bind unctor with
  | some ("Wasm.Invoked.values", [vs, i']) =>
    match (unlist vs).bind (·.mapM unU32) with
    | some ns => .values ns i'
    | none => .stuck
  | some ("Wasm.Invoked.trap", [i']) => .trap i'
  | some ("Wasm.Invoked.not_done", []) => .not_done
  | some ("Wasm.Invoked.unsupported", []) => .unsupported
  | _ => .stuck

-- Scripts
-- -------

-- an instance, or why there is none
inductive Inst where
  | ok : Term → Inst
  | none

structure St where
  defs : List (Option String × List UInt8) := []
  insts : List (Option String × Inst) := []
  pass : Nat := 0
  fail : Nat := 0
  unsupported : Nat := 0
  notDone : Nat := 0
  failures : Array String := #[]

def St.set (s : St) (n : Option String) (i : Inst) : St :=
  { s with insts := (none, i) :: (match n with | some k => (some k, i) :: s.insts | none => s.insts) }

-- the instance of the name, or the last one
def St.get (s : St) (n : Option String) : Option Inst :=
  match n with
  | none => (s.insts.find? (·.1.isNone)).map (·.2)
  | some k => (s.insts.find? (·.1 == some k)).map (·.2)

def St.defn (s : St) (n : Option String) : Option (List UInt8) :=
  match n with
  | none => s.defs.head?.map (·.2)
  | some k => (s.defs.find? (·.1 == some k)).map (·.2)

def St.passed (s : St) : St := { s with pass := s.pass + 1 }
def St.unsup (s : St) : St := { s with unsupported := s.unsupported + 1 }
def St.notdone (s : St) : St := { s with notDone := s.notDone + 1 }
def St.failed (s : St) (why : String) (e : Sexp) : St :=
  { s with fail := s.fail + 1, failures := s.failures.push s!"{why}: {(e.show).take 300}" }

def strOf : Sexp → Option (List UInt8)
  | .str b => some b
  | _ => none

-- a module of the script: its name and bytes
def moduleOf : List Sexp → Option (Option String × List UInt8)
  | .atom "binary" :: ss => (ss.mapM strOf).map fun bs => (none, bs.flatten)
  | .atom n :: .atom "binary" :: ss =>
    if n.startsWith "$" then (ss.mapM strOf).map fun bs => (some n, bs.flatten) else none
  | _ => none

def instOf (c : Cfg) (w : List UInt8) : Inst :=
  match instantiate c w with
  | .inst i => .ok i
  | _ => .none

-- an action: (invoke $i? "name" consts*)
def action (c : Cfg) (s : St) (e : Sexp) : Option (Invoked × Option String) :=
  let run (n : Option String) (name : List UInt8) (args : List Sexp) :=
    match s.get n, args.mapM constOf with
    | some (.ok i), some ns => some (invoke c i name ns, n)
    | some .none, _ => some (.unsupported, n)
    | _, _ => none
  match e with
  | .list (.atom "invoke" :: .atom n :: .str name :: args) => run (some n) name args
  | .list (.atom "invoke" :: .str name :: args) => run none name args
  | _ => none

-- the instance after an action, when it ran
def St.after (s : St) (n : Option String) : Invoked → St
  | .values _ i => s.set n (.ok i)
  | .trap i => s.set n (.ok i)
  | _ => s

-- a result pattern holds for the value v
def patOk (p : Sexp) (v : Nat) : Option Bool :=
  match p with
  | .list (.atom "either" :: ps) => (ps.mapM fun q => constOf q).map fun ns => ns.contains v
  | _ => (constOf p).map (· == v)

def command (c : Cfg) (s : St) (e : Sexp) : St :=
  match e with
  | .list (.atom "module" :: .atom "definition" :: rest) =>
    match moduleOf rest with
    | some (n, w) => { s with defs := (n, w) :: s.defs }
    | none => s
  | .list (.atom "module" :: .atom "instance" :: rest) =>
    let (n, d) := match rest with
      | [.atom i, .atom d] => (some i, some d)
      | [.atom i] => (some i, none)
      | _ => (none, none)
    match s.defn d with
    | some w => s.set n (instOf c w)
    | none => s.set n .none
  | .list (.atom "module" :: rest) =>
    match moduleOf rest with
    | some (n, w) => s.set n (instOf c w)
    | none => s.set none .none
  | .list [.atom "register", _] | .list [.atom "register", _, _] => s
  | .list (.atom "invoke" :: _) =>
    match action c s e with
    | some (r, n) => s.after n r
    | none => s
  | .list (.atom "assert_return" :: a :: pats) =>
    match action c s a with
    | none => s.unsup
    | some (r, n) =>
      let s := s.after n r
      match r with
      | .values vs _ =>
        if vs.length != pats.length then s.failed s!"gave {vs}" e else
        match (pats.zip vs).mapM fun (p, v) => patOk p v with
        | none => s.unsup
        | some oks => if oks.all id then s.passed else s.failed s!"gave {vs}" e
      | .trap _ => s.failed "trapped" e
      | .not_done => s.notdone
      | .unsupported => s.unsup
      | .stuck => s.failed "stuck" e
  | .list [.atom "assert_trap", .list (.atom "module" :: rest), _] =>
    match moduleOf rest with
    | none => s.unsup
    | some (_, w) =>
      match instantiate c w with
      | .trap => s.passed
      | .unsupported => s.unsup
      | _ => s.failed "did not trap at instantiation" e
  | .list [.atom "assert_trap", a, _] =>
    match action c s a with
    | none => s.unsup
    | some (r, n) =>
      let s := s.after n r
      match r with
      | .trap _ => s.passed
      | .not_done => s.notdone
      | .unsupported => s.unsup
      | .values vs _ => s.failed s!"gave {vs}" e
      | .stuck => s.failed "stuck" e
  | .list [.atom kind, .list (.atom "module" :: rest), _] =>
    if kind == "assert_invalid" || kind == "assert_malformed" then
      match moduleOf rest with
      | none => s.unsup
      | some (_, w) =>
        match instantiate c w with
        | .unsupported => s.passed
        | .stuck => s.failed "stuck" e
        | _ => s.failed "accepted" e
    else s.unsup
  | _ => s.unsup

def runFile (c : Cfg) (h : IO.FS.Handle) (path : String) : IO St := do
  let text ← IO.FS.readFile path
  match parseSeq text.toList false #[] with
  | .error msg => throw (IO.userError s!"{path}: {msg}")
  | .ok (cmds, _) =>
    let mut s : St := {}
    let mut k := 0
    for e in cmds do
      s := command c s e
      k := k + 1
      if k % 10 == 0 then
        h.putStrLn s!"  {path}: {k}/{cmds.length} commands, {s.pass} passed, {s.fail} failed"
        h.flush
    pure s

def main' : IO Unit := do
  let B ← Script.book
  let dir ← Script.env "TESTS"
  let only := (← IO.getEnv "ONLY").map (·.splitOn ",")
  let h ← IO.FS.Handle.mk (← Script.env "OUT") .write
  -- the model's fuel per invocation, and its memory limit: 2^16 pages, the
  -- spec's own limit for 32-bit memories
  let c : Cfg := { B, fuel := Form.nat 100000, limit := u32 65536 }
  let files := ((← System.FilePath.readDir dir).map (·.path.toString)).qsort (· < ·) |>.toList.filter fun p =>
    p.endsWith ".bin.wast" && (only.map fun ks => ks.any fun k => p.endsWith s!"/{k}.bin.wast").getD true
  let mut total : St := {}
  for p in files do
    let t0 ← IO.monoMsNow
    let s ← runFile c h p
    let t1 ← IO.monoMsNow
    h.putStrLn s!"{p}: {s.pass} passed, {s.fail} failed, {s.unsupported} unsupported, {s.notDone} not done, {(t1 - t0) / 1000} s"
    for f in s.failures do h.putStrLn s!"  FAIL {f}"
    h.flush
    total := { total with pass := total.pass + s.pass, fail := total.fail + s.fail,
                          unsupported := total.unsupported + s.unsupported, notDone := total.notDone + s.notDone }
  h.putStrLn s!"ALL: {total.pass} passed, {total.fail} failed, {total.unsupported} unsupported, {total.notDone} not done"
  h.flush

#eval main'
