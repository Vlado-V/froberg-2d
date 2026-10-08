import Froberg.MixedHigherRowData

/-! Literal multiplication is diagonal in all higher source coordinates;
no row of the odd target is discarded. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module MvPolynomial TensorProduct Quartic
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f u b : ℕ}

theorem mixedHigherProjection_scalar (hd : Odd d) (hd3 : 3≤d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K)) (hR : Function.Surjective R)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (hker : R.ker=(Submodule.span K (Set.range U)).map
      (topGrowthDegree (Nat.le_trans (by decide : 1≤3) hd3) h).symm.toLinearMap)
    (B : HigherOddCoordinates K h m d (Nat.le_trans (by decide : 1≤3) hd3) →ₗ[K] (Fin u → K))
    (hB : B.comp (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
      (fun i => mixedPureOddGenerator hd (U i) (P i)))=LinearMap.id)
    (p : Forms K m d) (v : MixedAmbientSource hd hd3 F U P)
    (r : MixedHigherIndex d hd3) :
    mixedHigherProjection hd hd3 R Q F U P hker r
      (mixedAmbientScalar hd hd3 Q F U P p v)=
      mixedHigherAction hd hd3 R hR Q F U P hker r p
        ((oddMixedSourceBlockCoordinates hd hd3 F U P B hB v).2 r) := by
  unfold mixedHigherProjection mixedHigherAction
  split_ifs with ht
  · obtain ⟨v,rfl⟩ := (oddBackgroundCoefficientRelations
      (fun i => oddBiformEmbedding (Nat.le_trans (by decide : 1≤3) hd3) (by decide) (F i))
      (fun i => mixedPureOddGenerator hd (U i) (P i))).mkQ_surjective v
    apply Prod.ext
    · change ambientTopGrowthProjection (Nat.le_trans (by decide : 1≤3) hd3) hd (by omega) R Q F U P
        (mixedProjectionKillsU hd3 R U hker)
        ((ambientOddRelations _ _ _).mkQ (evenScalarOddProduct (scalarEvenBiform p) v))=
        topGrowthScalarAction (Nat.le_trans (by decide : 1≤3) hd3) R Q F p
          (oddHigherTopProjectionEquiv hd hd3 R hR F U P hker r ht
            ((oddMixedSourceBlockCoordinates hd hd3 F U P B hB
              ((oddBackgroundCoefficientRelations _ _).mkQ v)).2 r))
      rw [ambientTopGrowthProjection_product]
      exact congrArg (topGrowthScalarAction (Nat.le_trans (by decide : 1≤3) hd3) R Q F p)
        (oddMixedSourceBlockCoordinates_top_projection hd hd3 R hR F U P hker B hB v r ht).symm
    · rfl
  · apply Prod.ext
    · rfl
    · change oddAmbientRowProjection _ _ _ _ _ _ _ _
        (oddAmbientScalarProduct _ _ _ (scalarBiformEquiv p) v)=
        oddActualRowScalarAction _ _ _ _ p
          (oddHigherNonTopQuotientEquiv _ _ _ _ _ _ _
            ((oddMixedSourceBlockCoordinates _ _ _ _ _ _ _ v).2 r))
      rw [oddIntermediateSourceProjection_scalar,
        oddIntermediateSourceProjection_coordinates hd hd3 F U P B hB r
          (by have := r.val.isLt; omega) (mixedHigherIndex_ge_three hd3 r)]
      rfl

theorem mixedHigherProjection_weighted_bottom (hd : Odd d) (hd3 : 3≤d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K))
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (hker : R.ker=(Submodule.span K (Set.range U)).map
      (topGrowthDegree (Nat.le_trans (by decide : 1≤3) hd3) h).symm.toLinearMap)
    (r : MixedHigherIndex d hd3)
    (v : biformParitySpace K h m (2*d) 1)
    (hv : v.val.IsWeightedHomogeneous (blockWeight h m) 1) :
    mixedHigherProjection hd hd3 R Q F U P hker r
      ((ambientOddRelations _ _ _).mkQ v)=0 := by
  unfold mixedHigherProjection
  split_ifs with ht
  · apply Prod.ext
    · exact ambientTopGrowthProjection_weighted_zero _ _ _ _ _ _ _ _ _ (by omega) v hv
    · rfl
  · apply Prod.ext
    · rfl
    · change oddAmbientRowProjection _ _ _ _ _ _ _ _ ((ambientOddRelations _ _ _).mkQ v)=0
      rw [oddAmbientRowProjection_mk]
      rw [biformTensorComponent_weight_ne _ v hv (by
        have := mixedHigherIndex_ge_three hd3 r
        omega),map_zero]

end Froberg
