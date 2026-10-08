import Froberg.MixedHigherRowData
import Froberg.MixedAmbientCorrection

/-! Literal bottom-source multiplication agrees with the B.3 vector
quotient action in the corrected ambient target. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxHeartbeats 100000
namespace Froberg
open Module MvPolynomial TensorProduct Quartic
attribute [local instance] tensorFormGroup
attribute [local irreducible] oddAmbientCoordinates oddAmbientHigherRelationMap oddAmbientBottomRelationMap
attribute [local irreducible] oddMixedSourceBlockCoordinates mixedAmbientScalar
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable (hd : Odd d) (hd3 : 3≤d)
  (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
  (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
local notation "hdp" => Nat.le_trans (by decide : 1≤3) hd3
local notation "Q₀" => fun i => scalarEvenBiform (h := h) (Q i)
local notation "F₁" => fun i => oddBiformEmbedding hdp (by decide) (F i)
local notation "G₁" => fun i => mixedPureOddGenerator hd (U i) (P i)
local notation "hQ₀" => fun i => scalarEvenBiform_weighted (h := h) (Q i)
local notation "hF₁" => fun i => oddLinearBiform_weighted hdp (F i)
local instance : AddCommGroup (HigherOddTargetRows hdp Q₀ F₁) :=
  higherOddTargetRowsGroup hdp Q₀ F₁
local instance : Module K (HigherOddTargetRows hdp Q₀ F₁) :=
  higherOddTargetRowsModule hdp Q₀ F₁
local instance : AddCommGroup (OddTargetRowQuotient Q₀ F₁ (oddTargetBottomIndex hdp)) :=
  oddTargetRowQuotientGroup Q₀ F₁ (oddTargetBottomIndex hdp)
local instance : Module K (OddTargetRowQuotient Q₀ F₁ (oddTargetBottomIndex hdp)) :=
  oddTargetRowQuotientModule Q₀ F₁ (oddTargetBottomIndex hdp)


def mixedAmbientCoordinates
    (D : HigherOddTargetRows hdp Q₀ F₁ →ₗ[K] OddTargetRowQuotient Q₀ F₁ (oddTargetBottomIndex hdp))
  (hD : D.comp (oddAmbientHigherRelationMap hdp Q₀ F₁ hQ₀ hF₁ G₁)=
    oddAmbientBottomRelationMap hdp Q₀ F₁ hQ₀ hF₁ G₁) :=
  (oddAmbientGraphQuotientEquiv hdp Q₀ F₁ hQ₀ hF₁ G₁).trans
    (factoredGraphCoordinates
      (oddAmbientBottomRelationMap hdp Q₀ F₁ hQ₀ hF₁ G₁)
      (oddAmbientHigherRelationMap hdp Q₀ F₁ hQ₀ hF₁ G₁) D hD)

end Froberg
