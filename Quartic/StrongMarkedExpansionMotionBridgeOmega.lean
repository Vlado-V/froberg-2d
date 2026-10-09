module

public import Quartic.StrongActualSlices
public import Quartic.ExpansionMotionBridge
public import Quartic.ActualMarkedSlicedMotionAvoidanceOmega

@[expose] public section

/-! The strong slice construction uses the dimension of the actual marked
subspace. It transports directly to the literal two-stage motion budget,
without an expected-dimension assumption. The extra marked target vector adds one to the correction budget. -/
noncomputable section
namespace Quartic.StrongMarkedExpansionMotionBridgeOmega
open Module UniformEndpoint ProfileCertificate RowMultiplicationCoordinates
open HomogeneousCoefficientCoordinates BilinearCovectorCharts BilinearCoefficientKernel
variable {K : Type*} [Field K] {m : ℕ} {upper : Bool}

/-- The actual marked dimension identifies the correction count exactly. -/
theorem correctionCount_eq (hm : 320 ≤ m)
    (h : Fin (upperEndpoint m) → Forms K m 2)
    (U : ActualMarkedSlicedMotionAvoidanceOmega.Marked h) :
    StrongActualSlices.markedCorrectionCount m upper (finrank K U+1) =
      ActualMarkedSlicedMotionAvoidanceOmega.correctionCount (c := mixedCount m upper) h U := by
  have hH := (UniformScalar.structural_dimension_signs m hm upper).2.1
  have hleft := StrongActualSlices.markedCorrectionCount_cast m hm upper (finrank K U+1)
  have hright : (ActualMarkedSlicedMotionAvoidanceOmega.correctionCount (c := mixedCount m upper) h U : ℤ) =
      Counts.H m (upperEndpoint m) (mixedCount m upper)+4+finrank K U :=
    Int.toNat_of_nonneg (by omega)
  push_cast at hleft
  omega

/-- Both clipped budgets agree term by term for the actual marked space. -/
theorem budget_eq (hm : 320 ≤ m)
    (h : Fin (upperEndpoint m) → Forms K m 2)
    (U : ActualMarkedSlicedMotionAvoidanceOmega.Marked h) (d : ℕ) :
    StrongActualSlices.slices m upper
      (StrongActualSlices.markedCorrectionCount m upper (finrank K U+1)) d =
      ActualMarkedSlicedMotionAvoidanceOmega.sliceCount (c := mixedCount m upper) h U d := by
  rw [StrongActualSlices.slices_eq,correctionCount_eq hm h U]
  rfl

/-- Only threshold and cut labels are reindexed. The ambient covectors,
actual generators, and rank conditions remain unchanged. -/
theorem closed_slices (hm : 320 ≤ m)
    (g : Fin (mixedCount m upper) → Rows K m 1)
    (h : Fin (upperEndpoint m) → Forms K m 2)
    (U : ActualMarkedSlicedMotionAvoidanceOmega.Marked h)
    (hslices : StrongActualSlices.HasAmbientSlices g
      (StrongActualSlices.markedCorrectionCount m upper (finrank K U+1)) h) :
    ∃ Z' : (d : AmbientSliceMotion.Threshold (RowCount m 1) (mixedCount m upper)) →
        Fin (ActualMarkedSlicedMotionAvoidanceOmega.sliceCount (c := mixedCount m upper) h U d.val) → Rows K m 3,
      ActualMarkedSlicedMotionAvoidanceOmega.ClosedSlices g h U Z' := by
  obtain ⟨Z,hZ⟩ := hslices
  let reindex (d : AmbientSliceMotion.Threshold (RowCount m 1) (mixedCount m upper)) :
      StrongExpansionOpen.Dimensions m upper :=
    Fin.cast (congrArg (fun n => n+1)
      (ExpansionMotionBridge.threshold_count_eq (K := K) (upper := upper) (by omega)).symm) d
  let Z' (d : AmbientSliceMotion.Threshold (RowCount m 1) (mixedCount m upper))
      (j : Fin (ActualMarkedSlicedMotionAvoidanceOmega.sliceCount (c := mixedCount m upper) h U d.val)) :=
    Z (reindex d) (Fin.cast (budget_eq hm h U d.val).symm j)
  refine ⟨Z',?_⟩
  intro d ell hker hE hQ hslice
  apply hZ (reindex d) ell hker hE hQ
  intro j
  have hh := hslice (Fin.cast (budget_eq hm h U d.val) j)
  have hj : Fin.cast (budget_eq hm h U d.val).symm
      (Fin.cast (budget_eq hm h U d.val) j)=j := Fin.ext rfl
  change covector ell (rowFiniteEquiv (Z (reindex d)
    (Fin.cast (budget_eq hm h U d.val).symm
      (Fin.cast (budget_eq hm h U d.val) j))))=0 at hh
  rw [hj] at hh
  exact hh

end Quartic.StrongMarkedExpansionMotionBridgeOmega
