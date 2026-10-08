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
import Lean

/-! Raw axiom reachability, independent of Lean's exported axiom summaries.

The worklist and visited set describe ONE graph traversal. The accumulator is
the union for ALL its roots, never a cache of per-node results. Visiting an
in-progress inductive/constructor cycle cannot erase dependencies. This code
does not call `Lean.collectAxioms` or any environment extension.
-/
namespace RawAxiomAudit
open Lean

structure Result where
  visited : NameSet := {}
  axioms : NameSet := {}
  deriving Inhabited

/-- Walk actual checked declarations. Missing declarations fail closed.
Includes types of axioms; definition, theorem and opaque bodies; constructors
and mutual inductive siblings; and recursor reduction rules. -/
def collect (env : Environment) (roots : Array Name) : Except String Result := Id.run do
  let env := env.setExporting false
  let kernel := env.checked.get
  let mut pending := roots.toList
  let mut result : Result := {}
  while !pending.isEmpty do
    match pending with
    | [] => pure ()
    | name :: rest =>
      pending := rest
      if result.visited.contains name then
        continue
      result := { result with visited := result.visited.insert name }
      let some info := kernel.find? name
        | return .error s!"Raw axiom audit: missing checked declaration {name}"
      for dep in info.type.getUsedConstants do
        pending := dep :: pending
      if let some body := info.value? (allowOpaque := true) then
        for dep in body.getUsedConstants do
          pending := dep :: pending
      match info with
      | .axiomInfo _ =>
        result := { result with axioms := result.axioms.insert name }
      | .inductInfo v =>
        for dep in v.ctors ++ v.all do
          pending := dep :: pending
      | .ctorInfo v =>
        pending := v.induct :: pending
      | .recInfo v =>
        for dep in v.all do
          pending := dep :: pending
        for rule in v.rules do
          pending := rule.ctor :: pending
          for dep in rule.rhs.getUsedConstants do
            pending := dep :: pending
      | _ => pure ()
  return .ok result

def allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

def unexpected (result : Result) : Array Name :=
  result.axioms.toArray.filter fun name => !allowed.contains name

def sortedAxioms (result : Result) : Array Name :=
  result.axioms.toArray.qsort Name.lt

structure SourceRoots where
  theorems : Array Name := #[]
  axiomDeclarations : Array Name := #[]
  modules : NameSet := {}
  deriving Inhabited

/-- Select by defining module, not declaration namespace. This includes private
theorems and declarations deliberately placed in a different namespace. -/
def selectOrigins (env : Environment) (prefixes : Array Name) : Except String SourceRoots := Id.run do
  let env := env.setExporting false
  let mut result : SourceRoots := {}
  for (name, _) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      let some origin := env.header.moduleNames[idx.toNat]?
        | return .error s!"Raw axiom audit: missing origin metadata for {name}"
      if prefixes.any (fun moduleRoot => moduleRoot.isPrefixOf origin) then
        let some info := env.checked.get.find? name
          | return .error s!"Raw axiom audit: selected declaration not checked: {name}"
        result := { result with modules := result.modules.insert origin }
        match info with
        | .thmInfo _ => result := { result with theorems := result.theorems.push name }
        | .axiomInfo _ =>
          result := { result with axiomDeclarations := result.axiomDeclarations.push name }
        | _ => pure ()
  return .ok result


end RawAxiomAudit

/-! Project audit using raw checked declarations only.

The import list matches CompleteProjectAudit.lean, including helper modules
outside the main theorem's import closure. No fixture is imported here.
Origin-module selection includes private and foreign-namespace theorems.

The union pass checks every selected theorem with one visited set. The final
main-theorem pass starts afresh, so no per-constant or cross-pass result cache
can hide an in-progress cyclic dependency. An unknown declaration is an error.

The audit source is intended to run only after the fresh build completes.
-/
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Lean Elab Command RawAxiomAudit in
elab "#audit_raw_project" : command => do
  let env := (← getEnv).setExporting false
  let origins ← match selectOrigins env #[`Froberg, `OAI, `Quartic] with
    | .error err => throwError "{err}"
    | .ok roots => pure roots
  if origins.theorems.isEmpty then
    throwError "Raw project audit selected no theorem roots"
  unless origins.theorems.contains ``Froberg.mainStatement do
    throwError "Raw project audit did not select Froberg.mainStatement by origin"
  for name in origins.axiomDeclarations do
    unless allowed.contains name do
      throwError "Unexpected axiom declaration in project source module: {name}"
  match collect env origins.theorems with
  | .error err => throwError "{err}"
  | .ok result =>
    let bad := unexpected result
    unless bad.isEmpty do
      throwError "Unexpected RAW axiom union in project theorems: {bad}"
    logInfo m!"PASS RAW PROJECT: {origins.theorems.size} theorem roots from {origins.modules.toArray.size} origin modules; {origins.axiomDeclarations.size} allowed local axiom declarations; {result.visited.toArray.size} visited checked declarations; axiom union = {sortedAxioms result}"
  -- This is a fresh traversal, with a new visited set and a new union.
  match collect env #[``Froberg.mainStatement] with
  | .error err => throwError "{err}"
  | .ok result =>
    let bad := unexpected result
    unless bad.isEmpty do
      throwError "Unexpected RAW axioms in Froberg.mainStatement: {bad}"
    logInfo m!"PASS RAW MAIN: Froberg.mainStatement; {result.visited.toArray.size} visited checked declarations; raw axioms = {sortedAxioms result}"

#audit_raw_project
#check Froberg.mainStatement
#print Froberg.MainStatement
#print Froberg.GenericHilbertThrough

-- Actual quotient interpretation and positive-truncation convention.
#print Froberg.Poly
#print Froberg.Forms
#print Froberg.CoefficientIndex
#print Froberg.coefficientForms
#print Froberg.coefficientSpace
#print Froberg.formToRingQuotient
#print Froberg.hilbertFunction
#print Froberg.predictionSeries
#print Froberg.predictionCoefficient
#print Froberg.positiveTruncation
#print Froberg.predictedHilbertFunction
