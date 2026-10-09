module

public import Quartic.MarkedActualExpansionSlices
public import Quartic.ActualMarkedSlicedMotionAvoidanceOmega

@[expose] public section

/-! The literal marked quotient slices are the slices consumed by actual motions. -/
noncomputable section
namespace Quartic.MarkedExpansionMotionBridgeOmega
open Module UniformEndpoint ProfileCertificate RowMultiplicationCoordinates
open HomogeneousCoefficientCoordinates BilinearCovectorCharts BilinearCoefficientKernel
variable {K : Type*} [Field K] {m : ℕ} {upper : Bool}

/-- The prescribed marked-space dimension identifies the actual correction count. -/
theorem correctionCount_eq (h : Fin (upperEndpoint m) → Forms K m 2)
    (U : ActualMarkedSlicedMotionAvoidanceOmega.Marked h)
    (hU : (finrank K U:ℤ)=Counts.delta m (upperEndpoint m)) :
    MarkedActualExpansionSlices.correctionCount m upper =
      ActualMarkedSlicedMotionAvoidanceOmega.correctionCount (c := mixedCount m upper) h U := by
  simp only [MarkedActualExpansionSlices.correctionCount,ActualMarkedSlicedMotionAvoidanceOmega.correctionCount,hU]

/-- No inequality is needed: the two clipped budgets are equal term by term. -/
theorem budget_eq (h : Fin (upperEndpoint m) → Forms K m 2)
    (U : ActualMarkedSlicedMotionAvoidanceOmega.Marked h)
    (hU : (finrank K U:ℤ)=Counts.delta m (upperEndpoint m)) (d : ℕ) :
    MarkedActualExpansionSlices.slices m upper d =
      ActualMarkedSlicedMotionAvoidanceOmega.sliceCount (c := mixedCount m upper) h U d := by
  rw [MarkedActualExpansionSlices.slices_eq,correctionCount_eq h U hU]
  rfl

include K in
/-- The expanded quotient source and the shifted ambient kernel have the
same full range of threshold indices. -/
theorem threshold_count_eq (hm : 28 ≤ m) :
    totalA m (mixedCount m upper) = RowCount m 1-mixedCount m upper := by
  rw [SmallCovectorCommonOpen.rowCount_one (K := K)]
  have hc := ConvolutionAllRange.endpoint_columns_range m hm upper
  exact totalA_eq m _ hc.1 hc.2

/-- Reindex only the threshold and slice labels. The actual ambient vectors,
shared E/Q equations, and closed kernel inequalities are unchanged. -/
theorem closed_slices (hm : 28 ≤ m)
    (g : Fin (mixedCount m upper) → Rows K m 1)
    (h : Fin (upperEndpoint m) → Forms K m 2)
    (U : ActualMarkedSlicedMotionAvoidanceOmega.Marked h)
    (hU : (finrank K U:ℤ)=Counts.delta m (upperEndpoint m))
    (Z : (d : MarkedConvolutionExpansionOpen.Dimensions m upper) →
      Fin (MarkedActualExpansionSlices.slices m upper d.val) → Rows K m 3)
    (hZ : ∀ d : MarkedConvolutionExpansionOpen.Dimensions m upper,∀ ell : Fin (RowCount m 3) → K,
      d.val+mixedCount m upper ≤ finrank K (LinearMap.ker
        (relationMap RowMultiplicationCoordinates.coordinate ell)) →
      (∀ j f,covector ell (RowMultiplicationCoordinates.coordinate f (rowFiniteEquiv (g j)))=0) →
      (∀ i v,covector ell (RowMultiplicationCoordinates.coordinate (finiteEquiv (h i)) v)=0) →
      (∀ j,covector ell (rowFiniteEquiv (Z d j))=0) → ell=0) :
    ∃ Z' : (d : AmbientSliceMotion.Threshold (RowCount m 1) (mixedCount m upper)) →
        Fin (ActualMarkedSlicedMotionAvoidanceOmega.sliceCount (c := mixedCount m upper) h U d.val) → Rows K m 3,
      ActualMarkedSlicedMotionAvoidanceOmega.ClosedSlices g h U Z' := by
  let reindex (d : AmbientSliceMotion.Threshold (RowCount m 1) (mixedCount m upper)) :
      MarkedConvolutionExpansionOpen.Dimensions m upper :=
    Fin.cast (congrArg (fun n => n+1) (threshold_count_eq (K := K) (upper := upper) hm).symm) d
  let Z' (d : AmbientSliceMotion.Threshold (RowCount m 1) (mixedCount m upper))
      (j : Fin (ActualMarkedSlicedMotionAvoidanceOmega.sliceCount (c := mixedCount m upper) h U d.val)) :=
    Z (reindex d) (Fin.cast (budget_eq h U hU d.val).symm j)
  refine ⟨Z',?_⟩
  intro d ell hker hE hQ hslice
  apply hZ (reindex d) ell hker hE hQ
  intro j
  have hh := hslice (Fin.cast (budget_eq h U hU d.val) j)
  have hj : Fin.cast (budget_eq h U hU d.val).symm
      (Fin.cast (budget_eq h U hU d.val) j)=j := Fin.ext rfl
  change covector ell (rowFiniteEquiv (Z (reindex d)
    (Fin.cast (budget_eq h U hU d.val).symm (Fin.cast (budget_eq h U hU d.val) j))))=0 at hh
  rw [hj] at hh
  exact hh

end Quartic.MarkedExpansionMotionBridgeOmega
