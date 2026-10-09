module

public import Quartic.ActualMarkedSlicedMotionAvoidanceOmega
public import Quartic.ActualMarkedSquareResponseOmega

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
namespace Quartic.ActualMarkedSlicedResponseRankOmega
open Module MvPolynomial UniformEndpoint ProfileCertificate
open ActualMarkedSlicedMotionAvoidanceOmega ActualDeformationResponseOmega SmallCovectorCommonOpen
open RowMultiplicationCoordinates
variable {K : Type*} [Field K] [IsAlgClosed K] {m c q : ℕ}
variable (ω : K)
set_option maxHeartbeats 1000000

omit [IsAlgClosed K] in
/-- The numerical auxiliary budget is exactly the dimension difference of
this actual response ω map and target. -/
theorem auxiliaryCount_eq (g : Mixed K m c) (h : Child K m q)
    (extra : ActualMarkedCorrectionMotionOmega.MiddleTarget h) (U : Marked h)
    (r : Fin 4 → Forms K m 2)
    (hg : LinearIndependent K g) (hh : LinearIndependent K h)
    (ha : Function.Injective (ExtraCorrectionOmega.augmented ω g h r extra))
    (hs : Function.Surjective (ActualMarkedCorrectionMotionOmega.middleMap g h))
    (hcubic : Function.Injective (CubicGeneric.cubicMap h))
    (h13 : Function.Injective (GeneralF13.f13Map g h)) :
    auxiliaryCount (c := c) h U=finrank K (J g h)-finrank K (ActualMarkedSquareResponseOmega.Source ω g h r extra U) := by
  have hc := ExtraCorrectionOmega.coefficientImage_finrank ω g h r extra hg hh ha hs U
  have hcount : (correctionCount (c := c) h U : ℤ)=
      Counts.H m q c+4+finrank K U := by
    apply Int.toNat_of_nonneg
    rw [← hc]
    exact Int.natCast_nonneg _
  have hsource : (finrank K (ActualMarkedSquareResponseOmega.Source ω g h r extra U):ℤ)=
      ((2*m+2*c:ℕ):ℤ)+(correctionCount (c := c) h U:ℤ) := by
    rw [ActualMarkedSquareResponseOmega.source_finrank ω g h r extra U hg hh ha hs,hcount]
    ring
  have htarget : (finrank K (J g h):ℤ)=
      Counts.j m q c :=
    ActualSplitCokernel.rawJ_finrank_eq_j g h hh hcubic h13
  have he : Counts.j m q c-
      ((2*m+2*c:ℕ):ℤ)-correctionCount (c := c) h U =
      (finrank K (J g h):ℤ)-(finrank K (ActualMarkedSquareResponseOmega.Source ω g h r extra U):ℤ) := by
    rw [htarget,hsource]
    ring
  change (Counts.j m q c-
    ((2*m+2*c:ℕ):ℤ)-correctionCount (c := c) h U).toNat=_
  rw [he]
  omega

/-- Actual motions with augmented injectivity and maximal response ω rank.
No response ω-rank hypothesis or independently chosen stage is assumed. -/
theorem exists_maximal_response (g : Mixed K m c) (h : Child K m q)
    (extra : ActualMarkedCorrectionMotionOmega.MiddleTarget h) (U : Marked h)
    (Z : (d : AmbientSliceMotion.Threshold (RowCount m 1) c) →
      Fin (sliceCount (c := c) h U d.val) → Rows K m 3)
    (hclosed : ClosedSlices g h U Z)
    (hg : LinearIndependent K g) (hh : LinearIndependent K h)
    (hs : Function.Surjective (ActualMarkedCorrectionMotionOmega.middleMap g h))
    (htrace : Function.Injective (SplitMiddle31.mixedMultiplication (ActualTraceMotion.rowMixed g)))
    (hcubic : Function.Injective (CubicGeneric.cubicMap h))
    (h13 : Function.Injective (GeneralF13.f13Map g h))
    (r₀ : ActualMarkedCorrectionMotionOmega.Pure K m)
    (hr₀ : Function.Injective (ExtraCorrectionOmega.augmented ω g h r₀ extra)) :
    ∃ r : Fin 4 → Forms K m 2,∃ s : Fin c → Forms K m 2,
      Function.Injective (ExtraCorrectionOmega.augmented ω g h r extra) ∧
      finrank K (LinearMap.range (ActualMarkedSquareResponseOmega.response ω g h r extra U s)) =
        min (finrank K (ActualMarkedSquareResponseOmega.Source ω g h r extra U)) (finrank K (J g h)) := by
  classical
  obtain ⟨r,s,Z,ha,havoid⟩ := exists_actual_motions ω g h extra U Z hclosed hg hh hs htrace r₀ hr₀
  have he := auxiliaryCount_eq ω g h extra U r hg hh ha hs hcubic h13
  let Z' : Fin (finrank K (J g h)-finrank K (ActualMarkedSquareResponseOmega.Source ω g h r extra U)) →
      GeneralF13.Ambient K m := fun j => Z (Fin.cast he.symm j)
  refine ⟨r,s,ha,ActualMarkedSquareResponseOmega.maximal_rank_of_ambient_exclusion ω g h r extra U s Z' ?_⟩
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
theorem exists_response_rank_formula (g : Mixed K m c) (h : Child K m q)
    (extra : ActualMarkedCorrectionMotionOmega.MiddleTarget h) (U : Marked h)
    (Z : (d : AmbientSliceMotion.Threshold (RowCount m 1) c) →
      Fin (sliceCount (c := c) h U d.val) → Rows K m 3)
    (hclosed : ClosedSlices g h U Z)
    (hg : LinearIndependent K g) (hh : LinearIndependent K h)
    (hs : Function.Surjective (ActualMarkedCorrectionMotionOmega.middleMap g h))
    (htrace : Function.Injective (SplitMiddle31.mixedMultiplication (ActualTraceMotion.rowMixed g)))
    (hcubic : Function.Injective (CubicGeneric.cubicMap h))
    (h13 : Function.Injective (GeneralF13.f13Map g h))
    (r₀ : ActualMarkedCorrectionMotionOmega.Pure K m)
    (hr₀ : Function.Injective (ExtraCorrectionOmega.augmented ω g h r₀ extra)) :
    ∃ r : Fin 4 → Forms K m 2,∃ s : Fin c → Forms K m 2,
      Function.Injective (ExtraCorrectionOmega.augmented ω g h r extra) ∧
      (finrank K (LinearMap.range (ActualMarkedSquareResponseOmega.response ω g h r extra U s)) : ℤ) =
        min (((2*m+2*c : ℕ):ℤ)+
          Counts.H m q c+4+finrank K U)
          (Counts.j m q c) := by
  obtain ⟨r,s,ha,hrank⟩ := exists_maximal_response ω g h extra U Z hclosed hg hh hs htrace hcubic h13 r₀ hr₀
  refine ⟨r,s,ha,?_⟩
  have hs' := ActualMarkedSquareResponseOmega.source_finrank ω g h r extra U hg hh ha hs
  have hj := ActualSplitCokernel.rawJ_finrank_eq_j g h hh hcubic h13
  rw [hrank,Nat.cast_min,hs',hj]


end Quartic.ActualMarkedSlicedResponseRankOmega
