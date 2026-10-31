import Lean

-- Guard
-- =====
--
-- #guard_axioms fails the build when a declaration of this library uses an
-- axiom beyond Lean's standard three. A sorry is the axiom sorryAx, so it
-- fails too. It also fails when a file of this library is not imported where
-- it runs, so that it sees each declaration.

open Lean Elab Command

namespace Guard

-- the axioms that a declaration may use
def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

-- the module that the file f under dir names: dir/A/B.lean names A.B
def moduleOf (dir f : System.FilePath) : Option Name :=
  let cs := (f.withExtension "").components
  let ds := dir.components
  if f.extension == some "lean" && ds.isPrefixOf cs then
    some ((cs.drop ds.length).foldl Name.str .anonymous)
  else
    none

-- the modules of the files under dir/<main module> that env does not import
def unimported (env : Environment) (dir : System.FilePath) : IO (List Name) := do
  let files ← System.FilePath.walkDir (dir / env.mainModule.toString)
  return (files.filterMap (moduleOf dir)).toList.filter fun m =>
    m != env.mainModule && (env.getModuleIdx? m).isNone

-- the declarations of the main module, and of each imported module under it
def decls (env : Environment) : List Name :=
  let mods := (env.header.moduleNames.zip env.header.moduleData).toList.filter fun (m, _) =>
    m.getRoot == env.mainModule
  env.constants.map₂.toList.map (·.1) ++ mods.flatMap (·.2.constNames.toList)

elab "#guard_axioms" : command => do
  let env ← getEnv
  let missing ← unimported env ((System.FilePath.mk (← getFileName)).parent.getD ".")
  unless missing.isEmpty do
    throwError "not imported by {env.mainModule}, so not checked: {missing}"
  let bad ← (decls env).filterMapM fun n => do
    let extra := (← collectAxioms n).toList.filter (!allowed.contains ·)
    return if extra.isEmpty then none else some m!"{n}: {extra}"
  unless bad.isEmpty do
    throwError "axioms beyond {allowed}:\n{MessageData.joinSep bad "\n"}"
  logInfo m!"#guard_axioms: {(decls env).length} declarations of {env.mainModule} use only {allowed}"

end Guard
