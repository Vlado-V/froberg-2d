module

import all Mathlib.RingTheory.MvPolynomial.HomogeneousBasis
import all Mathlib.RingTheory.MvPolynomial.HomogeneousIdeal
import all Mathlib.RingTheory.MvPolynomial.LinearFamily
public meta import Batteries.Tactic.Lint

open Lean Elab Command Batteries.Tactic.Lint

set_option maxHeartbeats 5000000 in
-- Run the declaration linters on the complete metadata for the three new APIs.
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `Mathlib.RingTheory.MvPolynomial.HomogeneousBasis,
    `Mathlib.RingTheory.MvPolynomial.HomogeneousIdeal,
    `Mathlib.RingTheory.MvPolynomial.LinearFamily]
  let decls := env.constants.toList.toArray.filterMap fun (name, _) => do
    let index ← env.getModuleIdxFor? name
    let moduleName ← env.header.moduleNames[index.toNat]?
    if targets.contains moduleName then some name else none
  unless decls.size == 23 do
    throwError "Expected 23 declarations from the three new API modules, found {decls.size}"
  let linters ← liftCoreM <| getChecks (slow := true) (runOnly := none) (runAlways := none)
  unless linters.size == 15 do
    throwError "Expected 15 declaration linters, found {linters.size}"
  let results ← liftCoreM <| lintCore decls linters
  let mut failed := false
  for (linter, findings) in results do
    logInfo m!"{linter.name}: {findings.size} findings"
    for (name, message) in findings.toArray do
      failed := true
      logError m!"{name}: {message}"
  if failed then
    throwError "Targeted declaration lint failed"
  logInfo m!"PASS: {decls.size} declarations from the three new API modules, {linters.size} linters"
