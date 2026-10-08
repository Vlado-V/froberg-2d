import Froberg.MixedHigherRowData
import Froberg.BottomVectorSlices
import Froberg.MixedAmbientCorrection

/-! Literal bottom-source multiplication agrees with the B.3 vector
quotient action in the corrected ambient target. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct Quartic VectorMultiplicationCoordinates
attribute [local instance] tensorFormGroup
attribute [local irreducible] oddAmbientCoordinates oddAmbientHigherRelationMap oddAmbientBottomRelationMap
attribute [local irreducible] oddMixedSourceBlockCoordinates mixedAmbientScalar
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable (hd : Odd d) (hd3 : 3≤d)
  (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1))
  (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
  (B : HigherOddCoordinates K h m d (Nat.le_trans (by decide : 1≤3) hd3) →ₗ[K] (Fin u → K))
  (hB : B.comp (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) (bottomTensorFamily g)
    (fun i => mixedPureOddGenerator hd (U i) (P i)))=LinearMap.id)
local notation "hdp" => Nat.le_trans (by decide : 1≤3) hd3
local notation "F" => bottomTensorFamily g
local notation "Q₀" => fun i => scalarEvenBiform (h := h) (Q i)
local notation "F₁" => fun i => oddBiformEmbedding hdp (by decide) (F i)
local notation "G₁" => fun i => mixedPureOddGenerator hd (U i) (P i)
local notation "hQ₀" => fun i => scalarEvenBiform_weighted (h := h) (Q i)
local notation "hF₁" => fun i => oddLinearBiform_weighted hdp (F i)


theorem mixedAmbientScalar_bottom
    (D : HigherOddTargetRows hdp Q₀ F₁ →ₗ[K] OddTargetRowQuotient Q₀ F₁ (oddTargetBottomIndex hdp))
  (hD : D.comp (oddAmbientHigherRelationMap hdp Q₀ F₁ hQ₀ hF₁ G₁)=
    oddAmbientBottomRelationMap hdp Q₀ F₁ hQ₀ hF₁ G₁) (p : Forms K m d) (x : OddBottomQuotient F) :
    oddAmbientCoordinates (K := K) (h := h) (m := m) (d := d) (q := q) (f := f) (u := u) hdp Q₀ F₁ hQ₀ hF₁ G₁ D hD
      (mixedAmbientScalar hd hd3 Q F U P p
        ((oddMixedSourceBlockCoordinates hd hd3 F U P B hB).symm (x,0)))=
      (bottomCoordinateScalarAction hdp Q g p x,0) := by
  obtain ⟨v,rfl⟩ := (Submodule.span K (Set.range F)).mkQ_surjective x
  have hb := oddMixedSourceBlockCoordinates_bottom hd hd3 F U P B hB v
  have hbi : (oddMixedSourceBlockCoordinates hd hd3 F U P B hB).symm
      ((Submodule.span K (Set.range F)).mkQ v,0)=
      (oddBackgroundCoefficientRelations F₁ G₁).mkQ (oddBiformEmbedding hdp (by decide) v) := by
    apply (oddMixedSourceBlockCoordinates hd hd3 F U P B hB).injective
    rw [LinearEquiv.apply_symm_apply]
    exact hb.symm
  rw [hbi,mixedAmbientScalar_mk,oddAmbientCoordinates_bottom_product hdp Q₀ F₁ hQ₀ hF₁ G₁ D hD
    (scalarEvenBiform p) (scalarEvenBiform_weighted p) _ (oddLinearBiform_weighted hdp v)]
  apply Prod.ext
  · rw [bottomCoordinateScalarAction_mk,oddTargetBaseMap_bottom]
    congr 1
    rw [←biformTensorComponent_eq_oddCoordinates]
    change biformTensorComponent (by omega : 1≤2*d)
      (evenScalarOddProduct (evenBiformEmbedding (Nat.zero_le d) (by decide) (scalarBiformEquiv p))
        (oddBiformEmbedding hdp (by decide) v))=_
    rw [biformTensorComponent_scalar_product hdp, biformTensorComponent_odd hdp (by decide)]
    rfl
  · rfl

end Froberg
