module

public import Froberg.MixedAmbientHigherGrowth
public import Froberg.MixedBottomCompatibility
public import Froberg.SurjectiveSplitTarget
public import Froberg.BottomVectorSlices
public import Froberg.MixedAmbientCorrection

@[expose] public section

/-! Literal bottom-source multiplication agrees with the B.3 vector
quotient action in the corrected ambient target. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
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



local notation "eV" => oddMixedSourceBlockCoordinates hd hd3 F U P B hB
local notation "π" => oddAmbientToFull Q₀ F₁ G₁
local notation "μ" => oddBackgroundScalarProduct Q₀ F₁ G₁
local notation "ν" => bottomCoordinateScalarAction hdp Q g

include B hB in
theorem mixed_full_bottom_compat
    (D : HigherOddTargetRows hdp Q₀ F₁ →ₗ[K] OddTargetRowQuotient Q₀ F₁ (oddTargetBottomIndex hdp))
  (hD : D.comp (oddAmbientHigherRelationMap hdp Q₀ F₁ hQ₀ hF₁ G₁)=
    oddAmbientBottomRelationMap hdp Q₀ F₁ hQ₀ hF₁ G₁)
    (ell : (biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations Q₀ F₁ G₁) →ₗ[K] K)
    (p : Forms K m d) (x : OddBottomQuotient F) :
    ell (μ p ((eV).symm (x,0)))=
      quotientSplitBottom (oddAmbientCoordinates (K := K) (h := h) (m := m) (d := d) (q := q) (f := f) (u := u) hdp Q₀ F₁ hQ₀ hF₁ G₁ D hD) π ell (ν p x) := by
  have he : oddAmbientCoordinates (K := K) (h := h) (m := m) (d := d)
      (q := q) (f := f) (u := u) hdp Q₀ F₁ hQ₀ hF₁ G₁ D hD
      (mixedAmbientScalar hd hd3 Q F U P p ((eV).symm (x,0))) = (ν p x,0) :=
    mixedAmbientScalar_bottom hd hd3 Q g U P B hB D hD p x
  have hmu : π (mixedAmbientScalar hd hd3 Q F U P p ((eV).symm (x,0)))=
      μ p ((eV).symm (x,0)) := by
    have hgen (v : MixedAmbientSource hd hd3 F U P) :
        π (mixedAmbientScalar hd hd3 Q F U P p v)=μ p v := by
      obtain ⟨z,rfl⟩ := (oddBackgroundCoefficientRelations F₁ G₁).mkQ_surjective v
      rw [mixedAmbientScalar_mk, oddAmbientToFull_mk]
      rfl
    exact hgen _
  rw [←hmu]
  change ell (π (mixedAmbientScalar hd hd3 Q F U P p ((eV).symm (x,0))))=
    ell (π (((oddAmbientCoordinates (K := K) (h := h) (m := m) (d := d) (q := q) (f := f) (u := u) hdp Q₀ F₁ hQ₀ hF₁ G₁ D hD)).symm (ν p x,0)))
  rw [←he,LinearEquiv.symm_apply_apply]

include B hB in
theorem mixed_full_bottom_kernel
    (D : HigherOddTargetRows hdp Q₀ F₁ →ₗ[K] OddTargetRowQuotient Q₀ F₁ (oddTargetBottomIndex hdp))
  (hD : D.comp (oddAmbientHigherRelationMap hdp Q₀ F₁ hQ₀ hF₁ G₁)=
    oddAmbientBottomRelationMap hdp Q₀ F₁ hQ₀ hF₁ G₁)
    (ell : (biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations Q₀ F₁ G₁) →ₗ[K] K) :
    (QuotientCovectorKernel.relation μ ell).ker.comap
      ((eV).symm.toLinearMap.comp (LinearMap.inl K (OddBottomQuotient F)
        (OddMixedBlockCoordinates hd hd3 F U P)))=
      (QuotientCovectorKernel.relation ν (quotientSplitBottom (oddAmbientCoordinates (K := K) (h := h) (m := m) (d := d) (q := q) (f := f) (u := u) hdp Q₀ F₁ hQ₀ hF₁ G₁ D hD) π ell)).ker :=
  pi_bottom_kernel_eq eV μ ν ell (quotientSplitBottom (oddAmbientCoordinates (K := K) (h := h) (m := m) (d := d) (q := q) (f := f) (u := u) hdp Q₀ F₁ hQ₀ hF₁ G₁ D hD) π ell)
    (mixed_full_bottom_compat hd hd3 Q g U P B hB D hD ell)

include B hB in
theorem mixed_full_bottom_kernel_finrank_le
    (D : HigherOddTargetRows hdp Q₀ F₁ →ₗ[K] OddTargetRowQuotient Q₀ F₁ (oddTargetBottomIndex hdp))
  (hD : D.comp (oddAmbientHigherRelationMap hdp Q₀ F₁ hQ₀ hF₁ G₁)=
    oddAmbientBottomRelationMap hdp Q₀ F₁ hQ₀ hF₁ G₁)
    (ell : (biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations Q₀ F₁ G₁) →ₗ[K] K) :
    finrank K (QuotientCovectorKernel.relation ν (quotientSplitBottom (oddAmbientCoordinates (K := K) (h := h) (m := m) (d := d) (q := q) (f := f) (u := u) hdp Q₀ F₁ hQ₀ hF₁ G₁ D hD) π ell)).ker≤
      finrank K (QuotientCovectorKernel.relation μ ell).ker :=
  pi_bottom_kernel_finrank_le eV μ ν ell (quotientSplitBottom (oddAmbientCoordinates (K := K) (h := h) (m := m) (d := d) (q := q) (f := f) (u := u) hdp Q₀ F₁ hQ₀ hF₁ G₁ D hD) π ell)
    (mixed_full_bottom_compat hd hd3 Q g U P B hB D hD ell)

include B hB in
theorem mixed_full_higher_kernel_growth
    (D : HigherOddTargetRows hdp Q₀ F₁ →ₗ[K] OddTargetRowQuotient Q₀ F₁ (oddTargetBottomIndex hdp))
  (hD : D.comp (oddAmbientHigherRelationMap hdp Q₀ F₁ hQ₀ hF₁ G₁)=
    oddAmbientBottomRelationMap hdp Q₀ F₁ hQ₀ hF₁ G₁) {b : ℕ}
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K)) (hR : Function.Surjective R)
    (hker : R.ker=(Submodule.span K (Set.range U)).map
      (topGrowthDegree hdp h).symm.toLinearMap)
    (t : ℕ)
    (htop : ∀ L : Submodule K (Fin b → K), t*finrank K L≤finrank K
      (BilinearImage.image (projectedTopScalarAction R (topGrowthParameters hdp Q F)) L))
    (hmid : ∀ (j : ℕ) (hj : 3≤j) (hjd : j<d), j%2=1 →
      OddScalarLayerProperty t (by omega : 1≤j) (by omega : j≤d)
        (F,fun i => scalarBiformEquiv (h := h) (Q i)))
    (ell : (biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations Q₀ F₁ G₁) →ₗ[K] K) :
    t*(finrank K (QuotientCovectorKernel.relation μ ell).ker-
      finrank K (QuotientCovectorKernel.relation ν (quotientSplitBottom (oddAmbientCoordinates (K := K) (h := h) (m := m) (d := d) (q := q) (f := f) (u := u) hdp Q₀ F₁ hQ₀ hF₁ G₁ D hD) π ell)).ker)≤
      finrank K (BilinearImage.image (splitTargetHigherAction (oddAmbientCoordinates (K := K) (h := h) (m := m) (d := d) (q := q) (f := f) (u := u) hdp Q₀ F₁ hQ₀ hF₁ G₁ D hD) (mixedAmbientScalar hd hd3 Q F U P)) (QuotientCovectorKernel.relation μ ell).ker) := by
  have hg : t*(finrank K (QuotientCovectorKernel.relation μ ell).ker-
      finrank K ((QuotientCovectorKernel.relation μ ell).ker.comap
        ((eV).symm.toLinearMap.comp (LinearMap.inl K (OddBottomQuotient F)
          (OddMixedBlockCoordinates hd hd3 F U P))))) ≤
      finrank K (BilinearImage.image (splitTargetHigherAction
        (oddAmbientCoordinates (K := K) (h := h) (m := m) (d := d) (q := q)
          (f := f) (u := u) hdp Q₀ F₁ hQ₀ hF₁ G₁ D hD)
        (mixedAmbientScalar hd hd3 Q F U P)) (QuotientCovectorKernel.relation μ ell).ker) :=
    mixedAmbientHigher_growth hd hd3 R hR Q F U P hker B hB D hD t htop hmid
      (QuotientCovectorKernel.relation μ ell).ker
  rw [mixed_full_bottom_kernel hd hd3 Q g U P B hB D hD ell] at hg
  exact hg

end Froberg
