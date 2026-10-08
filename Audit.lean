import Froberg
import Froberg.ActualRestoredOuterOdd
import Froberg.ActualTopSeparation
import Froberg.AffineKernelSlices
import Froberg.CanonicalTensorScalarGrowth
import Froberg.CapacityReserveGeneral
import Froberg.ClosedParameterAvoidance
import Froberg.ColoredMinors
import Froberg.ColoredPolynomialCertificates
import Froberg.ComparisonLabelSplit
import Froberg.ConsistentProductMinors
import Froberg.CriticalChildDeletion
import Froberg.CriticalSubleading
import Froberg.FiniteAuxiliaryOpen
import Froberg.GrowthUnderProjection
import Froberg.IntrinsicLayeredSlices
import Froberg.LinearOpenPullback
import Froberg.MixedAmbientCoordinates
import Froberg.OddAmbientBlockQuotients
import Froberg.OddAmbientHigherBlocks
import Froberg.OuterScalar
import Froberg.OuterScalarSurjection
import Froberg.OutputFrameProducts
import Froberg.PairedEndpointCapacity
import Froberg.ParityNormalCoordinates
import Froberg.PolynomialCoefficientRows
import Froberg.PolynomialRowSingle
import Froberg.PreparedActualCubicPrivateReduction
import Froberg.PreparedActualMiddlePrivateReduction
import Froberg.PreparedCertifiedFiber
import Froberg.PreparedFlagLocalComparison
import Froberg.PreparedHighOpen
import Froberg.PreparedOutputRename
import Froberg.PreparedPositiveCounts
import Froberg.PreparedRestoredSelection
import Froberg.PreparedScalarOldOpen
import Froberg.PreparedTopGrowth
import Froberg.PrivateBiformIndependent
import Froberg.PrivateDetectorModel
import Froberg.PrivateModelExistence
import Froberg.PrivateScalarMaximalRank
import Froberg.ProductRowWitnesses
import Froberg.ProfileGraphBudget
import Froberg.RelativeKoszulExactness
import Froberg.RelativeKoszulSpan
import Froberg.ReplacementCompatibility
import Froberg.RetainedHomology
import Froberg.RetainedQuotient
import Froberg.RowTwoExactCounts
import Froberg.ShiftedStrongQuadratic
import Froberg.SparseIntermediate
import Froberg.ThinGenericChild
import Froberg.TriangularRank
import Froberg.TwoFamilyRealOpen
import Froberg.UniformPreparedActualReduction
import Froberg.UniformPreparedLayeredBudget
import Froberg.UnprojectedCoefficientMotion
import Froberg.VectorLowerInjection
import Lean.Util.CollectAxioms

/-! Complete audit of the bundled proof libraries.
The extra imports load all shipped Froberg helpers outside the main import closure.
Origin-module selection also includes private theorems and declarations placed in
other namespaces. A fresh build is still required for source/artifact consistency. -/

open Lean Elab Command in
elab "#audit_complete_project" : command => do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let roots : List Name := [`Froberg, `OAI, `Quartic]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut checkedAxioms : Nat := 0
  for (name, info) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      let some origin := moduleNames[idx.toNat]?
        | throwError "Missing origin-module metadata for {name}"
      if roots.any (fun root => root.isPrefixOf origin) then
        match info with
        | .axiomInfo _ =>
          unless allowed.contains name do
            throwError "Unexpected local axiom {name} declared in {origin}"
          checkedAxioms := checkedAxioms + 1
        | .thmInfo _ =>
          let axioms ← Lean.collectAxioms name
          for axiomName in axioms do
            unless allowed.contains axiomName do
              throwError "Unexpected axiom {axiomName} in {name} (origin {origin})"
          checked := checked + 1
        | _ => pure ()
  logInfo m!"PASS: {checked} theorems from Froberg, OAI, and Quartic; {checkedAxioms} allowed local axiom declarations. Only propext, Classical.choice, and Quot.sound allowed."

#audit_complete_project

-- The unconditional theorem and its complete transitive axiom dependencies.
#check Froberg.mainStatement
#print axioms Froberg.mainStatement

-- The statement and its actual polynomial-quotient interpretation.
#print Froberg.MainStatement
#print Froberg.GenericHilbertThrough
#print Froberg.Poly
#print Froberg.Forms
#print Froberg.CoefficientIndex
#print Froberg.coefficientForms
#print Froberg.coefficientSpace
#print Froberg.formToRingQuotient
#print Froberg.hilbertFunction

-- Fröberg's integer power series and positive-truncation convention.
#print Froberg.predictionSeries
#print Froberg.predictionCoefficient
#print Froberg.positiveTruncation
#print Froberg.predictedHilbertFunction
