module

public import Quartic.ActualSmallMotionAvoidanceOmega
public import Quartic.ActualDeformationResponseOmega
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
namespace Quartic.ActualSmallResponseRankOmega
open Module MvPolynomial UniformEndpoint ProfileCertificate
open ActualSmallMotionAvoidanceOmega ActualDeformationResponseOmega SmallCovectorCommonOpen
open RowMultiplicationCoordinates
variable {K : Type*} [Field K] [IsAlgClosed K] {m : ℕ} {upper : Bool}
variable (ω : K)
set_option maxHeartbeats 1000000

omit [IsAlgClosed K] in
/-- The numerical auxiliary budget is exactly the dimension difference of
this actual response map and target. -/
theorem auxiliaryCount_eq (p : Parameters K m upper) (U : Marked p)
    (r : Fin 4 → Forms K m 2)
    (hg : LinearIndependent K (G p)) (hh : LinearIndependent K (Q p))
    (ha : Function.Injective (AugmentedGenericOmega.quotientAugmented ω
      (AugmentedGeneric.productMap (G p)) (Q p) r))
    (hs : Function.Surjective (ActualCorrectionMotionOmega.middleMap (G p) (Q p)))
    (hcubic : Function.Injective (CubicGeneric.cubicMap (Q p)))
    (h13 : Function.Injective (GeneralF13.f13Map (G p) (Q p))) :
    auxiliaryCount p U=finrank K (J (G p) (Q p))-finrank K (Source ω (G p) (Q p) r U) := by
  have hc := MovingMiddleCorrectionOmega.coefficientImage_finrank ω (G p) (Q p) r hg hh ha hs U
  have hcount : (correctionCount p U : ℤ)=
      Counts.H m (upperEndpoint m) (mixedCount m upper)+3+finrank K U := by
    apply Int.toNat_of_nonneg
    rw [← hc]
    exact Int.natCast_nonneg _
  have hsource : (finrank K (Source ω (G p) (Q p) r U):ℤ)=
      ((2*m+2*mixedCount m upper:ℕ):ℤ)+(correctionCount p U:ℤ) := by
    rw [source_finrank ω (G p) (Q p) r U hg hh ha hs,hcount]
    ring
  have htarget : (finrank K (J (G p) (Q p)):ℤ)=
      Counts.j m (upperEndpoint m) (mixedCount m upper) :=
    ActualSplitCokernel.rawJ_finrank_eq_j (G p) (Q p) hh hcubic h13
  have he : Counts.j m (upperEndpoint m) (mixedCount m upper)-
      ((2*m+2*mixedCount m upper:ℕ):ℤ)-correctionCount p U =
      (finrank K (J (G p) (Q p)):ℤ)-(finrank K (Source ω (G p) (Q p) r U):ℤ) := by
    rw [htarget,hsource]
    ring
  change (Counts.j m (upperEndpoint m) (mixedCount m upper)-
    ((2*m+2*mixedCount m upper:ℕ):ℤ)-correctionCount p U).toNat=_
  rw [he]
  omega

/-- Actual motions with augmented injectivity and maximal response rank.
No response-rank hypothesis or independently chosen stage is assumed. -/
theorem exists_maximal_response (hm : 28 ≤ m) (p : Parameters K m upper)
    (hp : ClosedConditions p) (U : Marked p)
    (hg : LinearIndependent K (G p)) (hh : LinearIndependent K (Q p))
    (hs : Function.Surjective (ActualCorrectionMotionOmega.middleMap (G p) (Q p)))
    (htrace : Function.Injective (SplitMiddle31.mixedMultiplication (ActualTraceMotion.rowMixed (G p))))
    (hcubic : Function.Injective (CubicGeneric.cubicMap (Q p)))
    (h13 : Function.Injective (GeneralF13.f13Map (G p) (Q p)))
    (r₀ : ActualCorrectionMotionOmega.Pure K m)
    (hr₀ : Function.Injective (AugmentedGenericOmega.quotientAugmented ω
      (AugmentedGeneric.productMap (G p)) (Q p) r₀)) :
    ∃ r : Fin 4 → Forms K m 2,∃ s : Fin (mixedCount m upper) → Forms K m 2,
      Function.Injective (AugmentedGenericOmega.quotientAugmented ω
        (AugmentedGeneric.productMap (G p)) (Q p) r) ∧
      finrank K (LinearMap.range (response ω (G p) (Q p) r U s)) =
        min (finrank K (Source ω (G p) (Q p) r U)) (finrank K (J (G p) (Q p))) := by
  classical
  obtain ⟨r,s,Z,ha,havoid⟩ := exists_actual_motions ω hm p hp U hg hh hs htrace r₀ hr₀
  have he := auxiliaryCount_eq ω p U r hg hh ha hs hcubic h13
  let Z' : Fin (finrank K (J (G p) (Q p))-finrank K (Source ω (G p) (Q p) r U)) →
      GeneralF13.Ambient K m := fun j => Z (Fin.cast he.symm j)
  refine ⟨r,s,ha,maximal_rank_of_ambient_exclusion ω (G p) (Q p) r U s Z' ?_⟩
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
    (hp : ClosedConditions p) (U : Marked p)
    (hg : LinearIndependent K (G p)) (hh : LinearIndependent K (Q p))
    (hs : Function.Surjective (ActualCorrectionMotionOmega.middleMap (G p) (Q p)))
    (htrace : Function.Injective (SplitMiddle31.mixedMultiplication (ActualTraceMotion.rowMixed (G p))))
    (hcubic : Function.Injective (CubicGeneric.cubicMap (Q p)))
    (h13 : Function.Injective (GeneralF13.f13Map (G p) (Q p)))
    (r₀ : ActualCorrectionMotionOmega.Pure K m)
    (hr₀ : Function.Injective (AugmentedGenericOmega.quotientAugmented ω
      (AugmentedGeneric.productMap (G p)) (Q p) r₀)) :
    ∃ r : Fin 4 → Forms K m 2,∃ s : Fin (mixedCount m upper) → Forms K m 2,
      Function.Injective (AugmentedGenericOmega.quotientAugmented ω
        (AugmentedGeneric.productMap (G p)) (Q p) r) ∧
      (finrank K (LinearMap.range (response ω (G p) (Q p) r U s)) : ℤ) =
        min (((2*m+2*mixedCount m upper : ℕ):ℤ)+
          Counts.H m (upperEndpoint m) (mixedCount m upper)+3+finrank K U)
          (Counts.j m (upperEndpoint m) (mixedCount m upper)) := by
  obtain ⟨r,s,ha,hrank⟩ := exists_maximal_response ω hm p hp U hg hh hs htrace hcubic h13 r₀ hr₀
  refine ⟨r,s,ha,?_⟩
  have hs' := source_finrank ω (G p) (Q p) r U hg hh ha hs
  have hj := ActualSplitCokernel.rawJ_finrank_eq_j (G p) (Q p) hh hcubic h13
  rw [hrank,Nat.cast_min,hs',hj]


/-- On the actual common coefficient open, all marked subspaces admit
actual motions with maximal response rank. The coefficient point is shared
by every closed threshold and by every required block condition. -/
theorem common_open (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 40)
    (upper : Bool) (hω : ω ≠ 0) (hω1 : ω ≠ -1) :
    ∃ D : MvPolynomial (SmallCovectorCommonOpen.ParameterIndex m upper m
        (mixedCount m upper) (upperEndpoint m)) K,
      (∃ p : Parameters K m upper,eval p D ≠ 0) ∧
      ∀ p : Parameters K m upper,eval p D ≠ 0 →
        SimultaneousBlockConditionsOmega.BlockConditions ω (baseProjection p) ∧
        GenericF13.Conditions (G p) (Q p) ∧ ClosedConditions p ∧
        ∀ U : Marked p,∃ r : Fin 4 → Forms K m 2,∃ s : Fin (mixedCount m upper) → Forms K m 2,
          Function.Injective (AugmentedGenericOmega.quotientAugmented ω
            (AugmentedGeneric.productMap (G p)) (Q p) r) ∧
          finrank K (LinearMap.range (response ω (G p) (Q p) r U s)) =
            min (finrank K (Source ω (G p) (Q p) r U)) (finrank K (J (G p) (Q p))) := by
  obtain ⟨D,hD,hgood⟩ := SmallCovectorCommonOpenOmega.common_open (K := K) ω m hmlo hmhi upper hω hω1
  refine ⟨D,hD,?_⟩
  intro p hp
  obtain ⟨hblock,hf13,_,hclosed⟩ := hgood p hp
  refine ⟨hblock,hf13,hclosed,?_⟩
  intro U
  exact exists_maximal_response ω hmlo p hclosed U hblock.1.1 hblock.1.2.1 hblock.1.2.2.1
    (by rw [ActualTraceMotion.rowMixed_eq_transpose]; exact hblock.2.2.1)
    hf13.2.1 hf13.2.2 (AugmentedGeneric.coefficientMotions (baseProjection p)) hblock.1.2.2.2

/-- A shared actual coefficient witness, leaving the marked subspace and
any old-child realization explicit for the induction step. -/
theorem exists_common_maximal_response (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 40)
    (upper : Bool) (hω : ω ≠ 0) (hω1 : ω ≠ -1) :
    ∃ p : Parameters K m upper,
      SimultaneousBlockConditionsOmega.BlockConditions ω (baseProjection p) ∧
      GenericF13.Conditions (G p) (Q p) ∧ ClosedConditions p ∧
      ∀ U : Marked p,∃ r : Fin 4 → Forms K m 2,∃ s : Fin (mixedCount m upper) → Forms K m 2,
        Function.Injective (AugmentedGenericOmega.quotientAugmented ω
          (AugmentedGeneric.productMap (G p)) (Q p) r) ∧
        finrank K (LinearMap.range (response ω (G p) (Q p) r U s)) =
          min (finrank K (Source ω (G p) (Q p) r U)) (finrank K (J (G p) (Q p))) := by
  obtain ⟨_,⟨p,hp⟩,hgood⟩ := common_open (K := K) ω m hmlo hmhi upper hω hω1
  exact ⟨p,hgood p hp⟩

/-- On the actual common coefficient open, all marked subspaces admit
actual motions with maximal response rank. The coefficient point is shared
by every closed threshold and by every required block condition. -/
theorem common_open_with (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 40)
    (upper : Bool) (hω : ω ≠ 0) (hω1 : ω ≠ -1)
    (P : MvPolynomial (AugmentedGeneric.ParameterIndex m (mixedCount m upper) (upperEndpoint m)) K)
    (hP : ∃ a,eval a P≠0) :
    ∃ D : MvPolynomial (SmallCovectorCommonOpen.ParameterIndex m upper m
        (mixedCount m upper) (upperEndpoint m)) K,
      (∃ p : Parameters K m upper,eval p D ≠ 0) ∧
      ∀ p : Parameters K m upper,eval p D ≠ 0 →
        eval (baseProjection p) P≠0 ∧
        SimultaneousBlockConditionsOmega.BlockConditions ω (baseProjection p) ∧
        GenericF13.Conditions (G p) (Q p) ∧ ClosedConditions p ∧
        ∀ U : Marked p,∃ r : Fin 4 → Forms K m 2,∃ s : Fin (mixedCount m upper) → Forms K m 2,
          Function.Injective (AugmentedGenericOmega.quotientAugmented ω
            (AugmentedGeneric.productMap (G p)) (Q p) r) ∧
          finrank K (LinearMap.range (response ω (G p) (Q p) r U s)) =
            min (finrank K (Source ω (G p) (Q p) r U)) (finrank K (J (G p) (Q p))) := by
  obtain ⟨D,hD,hgood⟩ := SmallCovectorCommonOpenOmega.common_open_with (K := K) ω m hmlo hmhi upper hω hω1 P hP
  refine ⟨D,hD,?_⟩
  intro p hp
  obtain ⟨hPp,hblock,hf13,_,hclosed⟩ := hgood p hp
  refine ⟨hPp,hblock,hf13,hclosed,?_⟩
  intro U
  exact exists_maximal_response ω hmlo p hclosed U hblock.1.1 hblock.1.2.1 hblock.1.2.2.1
    (by rw [ActualTraceMotion.rowMixed_eq_transpose]; exact hblock.2.2.1)
    hf13.2.1 hf13.2.2 (AugmentedGeneric.coefficientMotions (baseProjection p)) hblock.1.2.2.2


/-- A shared actual coefficient witness, leaving the marked subspace and
any old-child realization explicit for the induction step. -/
theorem exists_common_maximal_response_with (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 40)
    (upper : Bool) (hω : ω ≠ 0) (hω1 : ω ≠ -1)
    (P : MvPolynomial (AugmentedGeneric.ParameterIndex m (mixedCount m upper) (upperEndpoint m)) K)
    (hP : ∃ a,eval a P≠0) :
    ∃ p : Parameters K m upper,
      eval (baseProjection p) P≠0 ∧
      SimultaneousBlockConditionsOmega.BlockConditions ω (baseProjection p) ∧
      GenericF13.Conditions (G p) (Q p) ∧ ClosedConditions p ∧
      ∀ U : Marked p,∃ r : Fin 4 → Forms K m 2,∃ s : Fin (mixedCount m upper) → Forms K m 2,
        Function.Injective (AugmentedGenericOmega.quotientAugmented ω
          (AugmentedGeneric.productMap (G p)) (Q p) r) ∧
        finrank K (LinearMap.range (response ω (G p) (Q p) r U s)) =
          min (finrank K (Source ω (G p) (Q p) r U)) (finrank K (J (G p) (Q p))) := by
  obtain ⟨_,⟨p,hp⟩,hgood⟩ := common_open_with (K := K) ω m hmlo hmhi upper hω hω1 P hP
  exact ⟨p,hgood p hp⟩

end Quartic.ActualSmallResponseRankOmega
