import Lean

-- Guard
-- =====
--
-- Two build checks.
-- 1. #guard_runs f: each def that f uses, in the modules of this project,
--    runs as its body shows. The check fails on a def that is opaque,
--    extern or unsafe, or that has an other implementation.
-- 2. #guard_axioms t ...: each proof uses only Lean's three standard
--    axioms: propext, Classical.choice and Quot.sound.
-- Lean's own library is exempt: we trust it.

open Lean Elab Command

namespace Guard

-- the roots of the modules of Lean's own library
def LEAN_ROOTS : List Name := [`Init, `Std, `Lean, `Lake]

-- why the def c can run code that its body does not show
def why (env : Environment) (c : Name) (ci : ConstantInfo) : List String :=
  (if ci.isUnsafe then ["unsafe"] else []) ++
  (match ci with | .opaqueInfo _ => ["opaque"] | _ => []) ++
  (if isExtern env c then ["extern"] else []) ++
  (if (Compiler.getImplementedBy? env c).isSome then ["an other implementation"] else [])

-- c is in a module of this project, or in the current module: in any
-- module outside Lean's own library. A module that this misjudges as ours
-- fails the check; none passes it unseen.
def ours (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some i => !LEAN_ROOTS.contains (env.allImportedModuleNames[i.toNat]!).getRoot
  | none => true

end Guard

elab "#guard_runs " f:ident : command => do
  let env ← getEnv
  let root ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo f
  let mut todo := #[root]
  let mut seen : NameSet := {}
  let mut bad : Array String := #[]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c || !Guard.ours env c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    for w in Guard.why env c ci do
      bad := bad.push s!"{c}: {w}"
    if let some v := ci.value? (allowOpaque := true) then
      todo := todo ++ v.getUsedConstants
  unless bad.isEmpty do
    throwError "{f} can run code that the proofs do not see:\n{"\n".intercalate bad.toList}"

elab "#guard_axioms " ts:ident* : command => do
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  for t in ts do
    let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
    for a in (← liftCoreM <| collectAxioms c) do
      unless ok.contains a do
        throwError "{c} uses {a}, which is not one of Lean's three standard axioms"
