module

public import Solution
public import Lean.Util.CollectAxioms

/-! Standard axiom audit of theorem declarations loaded from the submitted
proof libraries, followed by the public theorem and independent statement. -/

open Lean Elab Command in
elab "#audit_complete_project" : command => do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let roots : List Name := [`Froberg, `OAI, `Quartic, `Solution]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, info) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      let some origin := moduleNames[idx.toNat]?
        | throwError "Missing origin-module metadata for {name}"
      if roots.any (fun root => root.isPrefixOf origin) then
        match info with
        -- A module may export a proved theorem as an axiom-shaped interface.
        -- collectAxioms uses its recorded dependencies; a genuine axiom still
        -- reports itself and is rejected by the same allowlist.
        | .axiomInfo _ | .thmInfo _ =>
          let axioms ← Lean.collectAxioms name
          for axiomName in axioms do
            unless allowed.contains axiomName do
              throwError "Unexpected axiom {axiomName} in {name} (origin {origin})"
          checked := checked + 1
        | _ => pure ()
  logInfo m!"PASS: {checked} theorem/axiom interface declarations from Froberg, OAI, Quartic, and Solution. Only propext, Classical.choice, and Quot.sound allowed."

#audit_complete_project

#check Froberg.uniformMainStatement
#check Froberg.paperStatement
#check FrobergPaper.main_result
#print axioms Froberg.uniformMainStatement
#print axioms Froberg.paperStatement
#print axioms FrobergPaper.main_result
#print FrobergPaper.Statement
#print FrobergPaper.GenericHilbertThrough
#print FrobergPaper.hilbertFunction
#print FrobergPaper.formToRingQuotient
#print FrobergPaper.predictionSeries
#print FrobergPaper.positiveTruncation
