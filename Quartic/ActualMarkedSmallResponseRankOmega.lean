module

public import Quartic.ActualMarkedSmallMotionAvoidanceOmega
public import Quartic.ActualMarkedSquareResponseOmega
public import Quartic.SmallCovectorCommonOpenOmega

@[expose] public section

/-!
# Maximal actual deformation response in the small range

The auxiliary count from closed-slice motion avoidance is identified with
the actual target-minus-source dimension. Actual motion existence therefore
implies maximal rank of the actual response map, for any specified marked
coefficient subspace. All child, augmented, and field hypotheses remain
explicit. No realization of that subspace by old-child homology is assumed.
-/
noncomputable section
namespace Quartic.ActualMarkedSmallResponseRankOmega
open Module MvPolynomial UniformEndpoint ProfileCertificate
open ActualMarkedSmallMotionAvoidanceOmega ActualDeformationResponseOmega SmallCovectorCommonOpen
open RowMultiplicationCoordinates
variable {K : Type*} [Field K] [IsAlgClosed K] {m : ℕ} {upper : Bool}
variable (ω : K)
set_option maxHeartbeats 1000000

omit [IsAlgClosed K] in
/-- The numerical auxiliary budget is exactly the dimension difference of
this actual response map and target. -/
theorem auxiliaryCount_eq (p : Parameters K m upper)
    (extra : ActualMarkedCorrectionMotionOmega.MiddleTarget (Q p)) (U : Marked p)
    (r : Fin 4 → Forms K m 2)
    (hg : LinearIndependent K (G p)) (hh : LinearIndependent K (Q p))
    (ha : Function.Injective (ExtraCorrectionOmega.augmented ω
      (G p) (Q p) r extra))
    (hs : Function.Surjective (ActualMarkedCorrectionMotionOmega.middleMap (G p) (Q p)))
    (hcubic : Function.Injective (CubicGeneric.cubicMap (Q p)))
    (h13 : Function.Injective (GeneralF13.f13Map (G p) (Q p))) :
    auxiliaryCount p U=finrank K (J (G p) (Q p))-finrank K (ActualMarkedSquareResponseOmega.Source ω (G p) (Q p) r extra U) := by
  have hc := ExtraCorrectionOmega.coefficientImage_finrank ω (G p) (Q p) r extra hg hh ha hs U
  have hcount : (correctionCount p U : ℤ)=
      Counts.H m (upperEndpoint m) (mixedCount m upper)+4+finrank K U := by
    apply Int.toNat_of_nonneg
    rw [← hc]
    exact Int.natCast_nonneg _
  have hsource : (finrank K (ActualMarkedSquareResponseOmega.Source ω (G p) (Q p) r extra U):ℤ)=
      ((2*m+2*mixedCount m upper:ℕ):ℤ)+(correctionCount p U:ℤ) := by
    rw [ActualMarkedSquareResponseOmega.source_finrank ω (G p) (Q p) r extra U hg hh ha hs,hcount]
    ring
  have htarget : (finrank K (J (G p) (Q p)):ℤ)=
      Counts.j m (upperEndpoint m) (mixedCount m upper) :=
    ActualSplitCokernel.rawJ_finrank_eq_j (G p) (Q p) hh hcubic h13
  have he : Counts.j m (upperEndpoint m) (mixedCount m upper)-
      ((2*m+2*mixedCount m upper:ℕ):ℤ)-correctionCount p U =
      (finrank K (J (G p) (Q p)):ℤ)-(finrank K (ActualMarkedSquareResponseOmega.Source ω (G p) (Q p) r extra U):ℤ) := by
    rw [htarget,hsource]
    ring
  change (Counts.j m (upperEndpoint m) (mixedCount m upper)-
    ((2*m+2*mixedCount m upper:ℕ):ℤ)-correctionCount p U).toNat=_
  rw [he]
  omega

/-- Actual motions with augmented injectivity and maximal response rank.
No response-rank hypothesis or independently chosen stage is assumed. -/
theorem exists_maximal_response (hm : 28 ≤ m) (p : Parameters K m upper)
    (extra : ActualMarkedCorrectionMotionOmega.MiddleTarget (Q p))
    (hp : ClosedConditions p) (U : Marked p)
    (hg : LinearIndependent K (G p)) (hh : LinearIndependent K (Q p))
    (hs : Function.Surjective (ActualMarkedCorrectionMotionOmega.middleMap (G p) (Q p)))
    (htrace : Function.Injective (SplitMiddle31.mixedMultiplication (ActualTraceMotion.rowMixed (G p))))
    (hcubic : Function.Injective (CubicGeneric.cubicMap (Q p)))
    (h13 : Function.Injective (GeneralF13.f13Map (G p) (Q p)))
    (r₀ : ActualMarkedCorrectionMotionOmega.Pure K m)
    (hr₀ : Function.Injective (ExtraCorrectionOmega.augmented ω
      (G p) (Q p) r₀ extra)) :
    ∃ r : Fin 4 → Forms K m 2,∃ s : Fin (mixedCount m upper) → Forms K m 2,
      Function.Injective (ExtraCorrectionOmega.augmented ω
        (G p) (Q p) r extra) ∧
      finrank K (LinearMap.range (ActualMarkedSquareResponseOmega.response ω (G p) (Q p) r extra U s)) =
        min (finrank K (ActualMarkedSquareResponseOmega.Source ω (G p) (Q p) r extra U)) (finrank K (J (G p) (Q p))) := by
  classical
  obtain ⟨r,s,Z,ha,havoid⟩ := exists_actual_motions ω hm p extra hp U hg hh hs htrace r₀ hr₀
  have he := auxiliaryCount_eq ω p extra U r hg hh ha hs hcubic h13
  let Z' : Fin (finrank K (J (G p) (Q p))-finrank K (ActualMarkedSquareResponseOmega.Source ω (G p) (Q p) r extra U)) →
      GeneralF13.Ambient K m := fun j => Z (Fin.cast he.symm j)
  refine ⟨r,s,ha,ActualMarkedSquareResponseOmega.maximal_rank_of_ambient_exclusion ω (G p) (Q p) r extra U s Z' ?_⟩
  intro ell hrel hfirst hsecond hZ
  apply havoid ell
  · intro j f
    exact hrel (product_generator_mem (G p) (Q p) f j)
  · intro i v
    exact hrel (child_product_mem (G p) (Q p) i v)
  · exact hfirst
  · exact hsecond
  · intro j
    have hz := hZ (Fin.cast he j)
    have hj : Fin.cast he.symm (Fin.cast he j)=j := Fin.ext rfl
    change ell (Z (Fin.cast he.symm (Fin.cast he j)))=0 at hz
    rw [hj] at hz
    exact hz

/-- The resulting actual rank has the literal manuscript integer count. -/
theorem exists_response_rank_formula (hm : 28 ≤ m) (p : Parameters K m upper)
    (extra : ActualMarkedCorrectionMotionOmega.MiddleTarget (Q p))
    (hp : ClosedConditions p) (U : Marked p)
    (hg : LinearIndependent K (G p)) (hh : LinearIndependent K (Q p))
    (hs : Function.Surjective (ActualMarkedCorrectionMotionOmega.middleMap (G p) (Q p)))
    (htrace : Function.Injective (SplitMiddle31.mixedMultiplication (ActualTraceMotion.rowMixed (G p))))
    (hcubic : Function.Injective (CubicGeneric.cubicMap (Q p)))
    (h13 : Function.Injective (GeneralF13.f13Map (G p) (Q p)))
    (r₀ : ActualMarkedCorrectionMotionOmega.Pure K m)
    (hr₀ : Function.Injective (ExtraCorrectionOmega.augmented ω
      (G p) (Q p) r₀ extra)) :
    ∃ r : Fin 4 → Forms K m 2,∃ s : Fin (mixedCount m upper) → Forms K m 2,
      Function.Injective (ExtraCorrectionOmega.augmented ω
        (G p) (Q p) r extra) ∧
      (finrank K (LinearMap.range (ActualMarkedSquareResponseOmega.response ω (G p) (Q p) r extra U s)) : ℤ) =
        min (((2*m+2*mixedCount m upper : ℕ):ℤ)+
          Counts.H m (upperEndpoint m) (mixedCount m upper)+4+finrank K U)
          (Counts.j m (upperEndpoint m) (mixedCount m upper)) := by
  obtain ⟨r,s,ha,hrank⟩ := exists_maximal_response ω hm p extra hp U hg hh hs htrace hcubic h13 r₀ hr₀
  refine ⟨r,s,ha,?_⟩
  have hs' := ActualMarkedSquareResponseOmega.source_finrank ω (G p) (Q p) r extra U hg hh ha hs
  have hj := ActualSplitCokernel.rawJ_finrank_eq_j (G p) (Q p) hh hcubic h13
  rw [hrank,Nat.cast_min,hs',hj]



theorem common_open_with (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 40)
    (upper : Bool) (hω : ω ≠ 0) (hω1 : ω ≠ -1)
    (extra : (a : AugmentedGeneric.ParameterIndex m (mixedCount m upper) (upperEndpoint m) → K) →
      ActualMarkedCorrectionMotionOmega.MiddleTarget (AugmentedGeneric.coefficientChild a))
    (P : MvPolynomial (AugmentedGeneric.ParameterIndex m (mixedCount m upper) (upperEndpoint m)) K)
    (hP : ∃ a,eval a P≠0)
    (hExtra : ∀ a,eval a P≠0 → Function.Injective (ExtraCorrectionOmega.augmented ω
      (AugmentedGeneric.coefficientMixed a) (AugmentedGeneric.coefficientChild a)
      (AugmentedGeneric.coefficientMotions a) (extra a))) :
    ∃ D : MvPolynomial (SmallCovectorCommonOpen.ParameterIndex m upper m
        (mixedCount m upper) (upperEndpoint m)) K,
      (∃ p : Parameters K m upper,eval p D ≠ 0) ∧
      ∀ p : Parameters K m upper,eval p D ≠ 0 →
        eval (baseProjection p) P≠0 ∧
        SimultaneousBlockConditionsOmega.BlockConditions ω (baseProjection p) ∧
        GenericF13.Conditions (G p) (Q p) ∧ ClosedConditions p ∧
        ∀ U : Marked p,∃ r : Fin 4 → Forms K m 2,∃ s : Fin (mixedCount m upper) → Forms K m 2,
          Function.Injective (ExtraCorrectionOmega.augmented ω
            (G p) (Q p) r (extra (baseProjection p))) ∧
          finrank K (LinearMap.range (ActualMarkedSquareResponseOmega.response ω (G p) (Q p) r (extra (baseProjection p)) U s)) =
            min (finrank K (ActualMarkedSquareResponseOmega.Source ω (G p) (Q p) r (extra (baseProjection p)) U)) (finrank K (J (G p) (Q p))) := by
  obtain ⟨D,hD,hgood⟩ := SmallCovectorCommonOpenOmega.common_open_with (K := K) ω m hmlo hmhi upper hω hω1 P hP
  refine ⟨D,hD,?_⟩
  intro p hp
  obtain ⟨hPp,hblock,hf13,_,hclosed⟩ := hgood p hp
  refine ⟨hPp,hblock,hf13,hclosed,?_⟩
  intro U
  exact exists_maximal_response ω hmlo p (extra (baseProjection p)) hclosed U hblock.1.1 hblock.1.2.1 hblock.1.2.2.1
    (by rw [ActualTraceMotion.rowMixed_eq_transpose]; exact hblock.2.2.1)
    hf13.2.1 hf13.2.2 (AugmentedGeneric.coefficientMotions (baseProjection p)) (hExtra _ hPp)


/-- A shared actual coefficient witness, leaving the marked subspace and
any old-child realization explicit for the induction step. -/
theorem exists_common_maximal_response_with (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 40)
    (upper : Bool) (hω : ω ≠ 0) (hω1 : ω ≠ -1)
    (extra : (a : AugmentedGeneric.ParameterIndex m (mixedCount m upper) (upperEndpoint m) → K) →
      ActualMarkedCorrectionMotionOmega.MiddleTarget (AugmentedGeneric.coefficientChild a))
    (P : MvPolynomial (AugmentedGeneric.ParameterIndex m (mixedCount m upper) (upperEndpoint m)) K)
    (hP : ∃ a,eval a P≠0)
    (hExtra : ∀ a,eval a P≠0 → Function.Injective (ExtraCorrectionOmega.augmented ω
      (AugmentedGeneric.coefficientMixed a) (AugmentedGeneric.coefficientChild a)
      (AugmentedGeneric.coefficientMotions a) (extra a))) :
    ∃ p : Parameters K m upper,
      eval (baseProjection p) P≠0 ∧
      SimultaneousBlockConditionsOmega.BlockConditions ω (baseProjection p) ∧
      GenericF13.Conditions (G p) (Q p) ∧ ClosedConditions p ∧
      ∀ U : Marked p,∃ r : Fin 4 → Forms K m 2,∃ s : Fin (mixedCount m upper) → Forms K m 2,
        Function.Injective (ExtraCorrectionOmega.augmented ω
          (G p) (Q p) r (extra (baseProjection p))) ∧
        finrank K (LinearMap.range (ActualMarkedSquareResponseOmega.response ω (G p) (Q p) r (extra (baseProjection p)) U s)) =
          min (finrank K (ActualMarkedSquareResponseOmega.Source ω (G p) (Q p) r (extra (baseProjection p)) U)) (finrank K (J (G p) (Q p))) := by
  obtain ⟨_,⟨p,hp⟩,hgood⟩ := common_open_with (K := K) ω m hmlo hmhi upper hω hω1 extra P hP hExtra
  exact ⟨p,hgood p hp⟩

end Quartic.ActualMarkedSmallResponseRankOmega
