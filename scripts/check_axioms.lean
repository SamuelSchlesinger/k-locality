import KLocality
import Lean.Util.CollectAxioms

/-! Audit all declarations originating in project modules, including private helpers.

Module provenance avoids depending on a manually maintained list of theorem names.
A shared traversal visits each dependency once across the whole library.
Run with `lake env lean -DwarningAsError=true scripts/check_axioms.lean`.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  let mut declarations : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      if (`KLocality).isPrefixOf modules[index.toNat]! then
        declarations := declarations.push name
  if declarations.isEmpty then
    throwError "No project declarations found; the audit must not pass vacuously."
  let (_, audit) := ((declarations.forM CollectAxioms.collect).run env).run {}
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := audit.axioms.filter (!allowed.contains ·)
  unless unexpected.isEmpty do
    throwError "Unexpected project dependencies: {unexpected}"
  logInfo m!"Project axiom audit passed for {declarations.size} declarations: {audit.axioms}"
