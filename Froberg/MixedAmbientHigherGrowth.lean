module

public import Froberg.MixedHigherCompatibility
public import Froberg.MixedHigherGrowth
public import Froberg.MixedAmbientCorrection

@[expose] public section

/-! Growth of the actual higher component of the corrected ambient odd
target, simultaneously over all higher source blocks. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module MvPolynomial TensorProduct Quartic
attribute [local instance] tensorFormGroup
attribute [local irreducible] oddAmbientCoordinates oddAmbientHigherRelationMap oddAmbientBottomRelationMap
attribute [local irreducible] oddMixedSourceBlockCoordinates mixedAmbientScalar
variable {K : Type} [Field K] [Infinite K] {h m d q f u b : ℕ}
variable (hd : Odd d) (hd3 : 3≤d)
  (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K)) (hR : Function.Surjective R)
  (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
  (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
  (hker : R.ker=(Submodule.span K (Set.range U)).map
    (topGrowthDegree (Nat.le_trans (by decide : 1≤3) hd3) h).symm.toLinearMap)
  (B : HigherOddCoordinates K h m d (Nat.le_trans (by decide : 1≤3) hd3) →ₗ[K] (Fin u → K))
  (hB : B.comp (oddHigherRelationMap (Nat.le_trans (by decide : 1≤3) hd3) F
    (fun i => mixedPureOddGenerator hd (U i) (P i)))=LinearMap.id)

local notation "hdp" => Nat.le_trans (by decide : 1≤3) hd3
local notation "Q₀" => fun i => scalarEvenBiform (h := h) (Q i)
local notation "F₁" => fun i => oddBiformEmbedding hdp (by decide) (F i)
local notation "G₁" => fun i => mixedPureOddGenerator hd (U i) (P i)
local notation "hQ₀" => fun i => scalarEvenBiform_weighted (h := h) (Q i)
local notation "hF₁" => fun i => oddLinearBiform_weighted hdp (F i)



 theorem mixedHigherProjection_kills_bottom
    (D : HigherOddTargetRows hdp Q₀ F₁ →ₗ[K] OddTargetRowQuotient Q₀ F₁ (oddTargetBottomIndex hdp))
  (hD : D.comp (oddAmbientHigherRelationMap hdp Q₀ F₁ hQ₀ hF₁ G₁)=
    oddAmbientBottomRelationMap hdp Q₀ F₁ hQ₀ hF₁ G₁) (r : MixedHigherIndex d hd3)
    (x : OddTargetRowQuotient Q₀ F₁ (oddTargetBottomIndex hdp)) :
    mixedHigherProjection hd hd3 R Q F U P hker r
      ((oddAmbientCoordinates (K := K) (h := h) (m := m) (d := d) (q := q) (f := f) (u := u) hdp Q₀ F₁ hQ₀ hF₁ G₁ D hD).symm (x,0))=0 := by
  apply odd_ambient_projection_kills_bottom
  intro v hv
  exact mixedHigherProjection_weighted_bottom hd hd3 R Q F U P hker r v hv

include hR hker in
 theorem mixedAmbientHigher_growth
    (D : HigherOddTargetRows hdp Q₀ F₁ →ₗ[K] OddTargetRowQuotient Q₀ F₁ (oddTargetBottomIndex hdp))
  (hD : D.comp (oddAmbientHigherRelationMap hdp Q₀ F₁ hQ₀ hF₁ G₁)=
    oddAmbientBottomRelationMap hdp Q₀ F₁ hQ₀ hF₁ G₁)
    (t : ℕ)
    (htop : ∀ L : Submodule K (Fin b → K), t*finrank K L≤finrank K
      (BilinearImage.image (projectedTopScalarAction R (topGrowthParameters hdp Q F)) L))
    (hmid : ∀ (j : ℕ) (hj : 3≤j) (hjd : j<d), j%2=1 →
      OddScalarLayerProperty t (by omega : 1≤j) (by omega : j≤d)
        (F,fun i => scalarBiformEquiv (h := h) (Q i)))
    (L : Submodule K (MixedAmbientSource hd hd3 F U P)) :
    t*(finrank K L-finrank K (L.comap
      ((oddMixedSourceBlockCoordinates hd hd3 F U P B hB).symm.toLinearMap.comp
        (LinearMap.inl K (OddBottomQuotient F)
          ((r : MixedHigherIndex d hd3) → MixedHigherSource hd hd3 F U P r))))) ≤
      finrank K (BilinearImage.image
        (splitTargetHigherAction (oddAmbientCoordinates (K := K) (h := h) (m := m) (d := d) (q := q) (f := f) (u := u) hdp Q₀ F₁ hQ₀ hF₁ G₁ D hD)
          (mixedAmbientScalar hd hd3 Q F U P)) L) := by
  let e := oddAmbientCoordinates (K := K) (h := h) (m := m) (d := d) (q := q) (f := f) (u := u) hdp Q₀ F₁ hQ₀ hF₁ G₁ D hD
  let mu := mixedAmbientScalar hd hd3 Q F U P
  let pi := LinearMap.pi (fun r : MixedHigherIndex d hd3 =>
    splitHigherProjection e (mixedHigherProjection hd hd3 R Q F U P hker r))
  apply higher_growth_of_pi_projection
    (oddMixedSourceBlockCoordinates hd hd3 F U P B hB) pi
    (splitTargetHigherAction e mu)
    (mixedHigherAction hd hd3 R hR Q F U P hker)
  · intro p v r
    change splitHigherProjection e (mixedHigherProjection hd hd3 R Q F U P hker r)
      (splitTargetHigherAction e mu p v)=_
    exact (splitHigherProjection_action e _
      (mixedHigherProjection_kills_bottom hd hd3 R Q F U P hker D hD r) mu p v).trans
      (mixedHigherProjection_scalar hd hd3 R hR Q F U P hker B hB p v r)
  · exact mixedHigherAction_growth hd hd3 R hR Q F U P hker t htop hmid

end Froberg
