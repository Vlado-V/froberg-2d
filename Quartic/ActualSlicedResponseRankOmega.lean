module

public import Quartic.ActualSlicedMotionAvoidanceOmega
public import Quartic.ActualDeformationResponseOmega

@[expose] public section

/-!
# Maximal actual deformation response ω from closed slices

The auxiliary count from closed-slice motion avoidance is identified with
the actual target-minus-source dimension. Actual motion existence therefore
implies maximal rank of the actual response ω map, for any specified marked
coefficient subspace. All child, augmented, and field hypotheses remain
explicit. No realization of that subspace by old-child homology is assumed.
-/
noncomputable section
namespace Quartic.ActualSlicedResponseRankOmega
open Module MvPolynomial UniformEndpoint ProfileCertificate
open ActualSlicedMotionAvoidanceOmega ActualDeformationResponseOmega SmallCovectorCommonOpen
open RowMultiplicationCoordinates
variable {K : Type*} [Field K] [IsAlgClosed K] {m c q : ℕ}
variable (ω : K)
set_option maxHeartbeats 1000000

omit [IsAlgClosed K] in
/-- The numerical auxiliary budget is exactly the dimension difference of
this actual response ω map and target. -/
theorem auxiliaryCount_eq (g : Mixed K m c) (h : Child K m q) (U : Marked h)
    (r : Fin 4 → Forms K m 2)
    (hg : LinearIndependent K g) (hh : LinearIndependent K h)
    (ha : Function.Injective (AugmentedGenericOmega.quotientAugmented ω
      (AugmentedGeneric.productMap g) h r))
    (hs : Function.Surjective (ActualCorrectionMotionOmega.middleMap g h))
    (hcubic : Function.Injective (CubicGeneric.cubicMap h))
    (h13 : Function.Injective (GeneralF13.f13Map g h)) :
    auxiliaryCount (c := c) h U=finrank K (J g h)-finrank K (Source ω g h r U) := by
  have hc := MovingMiddleCorrectionOmega.coefficientImage_finrank ω g h r hg hh ha hs U
  have hcount : (correctionCount (c := c) h U : ℤ)=
      Counts.H m q c+3+finrank K U := by
    apply Int.toNat_of_nonneg
    rw [← hc]
    exact Int.natCast_nonneg _
  have hsource : (finrank K (Source ω g h r U):ℤ)=
      ((2*m+2*c:ℕ):ℤ)+(correctionCount (c := c) h U:ℤ) := by
    rw [source_finrank ω g h r U hg hh ha hs,hcount]
    ring
  have htarget : (finrank K (J g h):ℤ)=
      Counts.j m q c :=
    ActualSplitCokernel.rawJ_finrank_eq_j g h hh hcubic h13
  have he : Counts.j m q c-
      ((2*m+2*c:ℕ):ℤ)-correctionCount (c := c) h U =
      (finrank K (J g h):ℤ)-(finrank K (Source ω g h r U):ℤ) := by
    rw [htarget,hsource]
    ring
  change (Counts.j m q c-
    ((2*m+2*c:ℕ):ℤ)-correctionCount (c := c) h U).toNat=_
  rw [he]
  omega

/-- Actual motions with augmented injectivity and maximal response ω rank.
No response ω-rank hypothesis or independently chosen stage is assumed. -/
theorem exists_maximal_response (g : Mixed K m c) (h : Child K m q) (U : Marked h)
    (Z : (d : AmbientSliceMotion.Threshold (RowCount m 1) c) →
      Fin (sliceCount (c := c) h U d.val) → Rows K m 3)
    (hclosed : ClosedSlices g h U Z)
    (hg : LinearIndependent K g) (hh : LinearIndependent K h)
    (hs : Function.Surjective (ActualCorrectionMotionOmega.middleMap g h))
    (htrace : Function.Injective (SplitMiddle31.mixedMultiplication (ActualTraceMotion.rowMixed g)))
    (hcubic : Function.Injective (CubicGeneric.cubicMap h))
    (h13 : Function.Injective (GeneralF13.f13Map g h))
    (r₀ : ActualCorrectionMotionOmega.Pure K m)
    (hr₀ : Function.Injective (AugmentedGenericOmega.quotientAugmented ω
      (AugmentedGeneric.productMap g) h r₀)) :
    ∃ r : Fin 4 → Forms K m 2,∃ s : Fin c → Forms K m 2,
      Function.Injective (AugmentedGenericOmega.quotientAugmented ω
        (AugmentedGeneric.productMap g) h r) ∧
      finrank K (LinearMap.range (response ω g h r U s)) =
        min (finrank K (Source ω g h r U)) (finrank K (J g h)) := by
  classical
  obtain ⟨r,s,Z,ha,havoid⟩ := exists_actual_motions ω g h U Z hclosed hg hh hs htrace r₀ hr₀
  have he := auxiliaryCount_eq ω g h U r hg hh ha hs hcubic h13
  let Z' : Fin (finrank K (J g h)-finrank K (Source ω g h r U)) →
      GeneralF13.Ambient K m := fun j => Z (Fin.cast he.symm j)
  refine ⟨r,s,ha,maximal_rank_of_ambient_exclusion ω g h r U s Z' ?_⟩
  intro ell hrel hfirst hsecond hZ
  apply havoid ell
  · intro j f
    exact hrel (product_generator_mem g h f j)
  · intro i v
    exact hrel (child_product_mem g h i v)
  · exact hfirst
  · exact hsecond
  · intro j
    have hz := hZ (Fin.cast he j)
    have hj : Fin.cast he.symm (Fin.cast he j)=j := Fin.ext rfl
    change ell (Z (Fin.cast he.symm (Fin.cast he j)))=0 at hz
    rw [hj] at hz
    exact hz

/-- The resulting actual rank has the literal manuscript integer count. -/
theorem exists_response_rank_formula (g : Mixed K m c) (h : Child K m q) (U : Marked h)
    (Z : (d : AmbientSliceMotion.Threshold (RowCount m 1) c) →
      Fin (sliceCount (c := c) h U d.val) → Rows K m 3)
    (hclosed : ClosedSlices g h U Z)
    (hg : LinearIndependent K g) (hh : LinearIndependent K h)
    (hs : Function.Surjective (ActualCorrectionMotionOmega.middleMap g h))
    (htrace : Function.Injective (SplitMiddle31.mixedMultiplication (ActualTraceMotion.rowMixed g)))
    (hcubic : Function.Injective (CubicGeneric.cubicMap h))
    (h13 : Function.Injective (GeneralF13.f13Map g h))
    (r₀ : ActualCorrectionMotionOmega.Pure K m)
    (hr₀ : Function.Injective (AugmentedGenericOmega.quotientAugmented ω
      (AugmentedGeneric.productMap g) h r₀)) :
    ∃ r : Fin 4 → Forms K m 2,∃ s : Fin c → Forms K m 2,
      Function.Injective (AugmentedGenericOmega.quotientAugmented ω
        (AugmentedGeneric.productMap g) h r) ∧
      (finrank K (LinearMap.range (response ω g h r U s)) : ℤ) =
        min (((2*m+2*c : ℕ):ℤ)+
          Counts.H m q c+3+finrank K U)
          (Counts.j m q c) := by
  obtain ⟨r,s,ha,hrank⟩ := exists_maximal_response ω g h U Z hclosed hg hh hs htrace hcubic h13 r₀ hr₀
  refine ⟨r,s,ha,?_⟩
  have hs' := source_finrank ω g h r U hg hh ha hs
  have hj := ActualSplitCokernel.rawJ_finrank_eq_j g h hh hcubic h13
  rw [hrank,Nat.cast_min,hs',hj]


end Quartic.ActualSlicedResponseRankOmega
