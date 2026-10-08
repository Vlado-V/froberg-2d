import Froberg.EvenBottomCompatibility

/-! The actual even-case contraction kernels satisfy both the bottom
monotonicity and the full higher-image bound needed by C.4. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module MvPolynomial TensorProduct Quartic VectorMultiplicationCoordinates
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f : ℕ}
variable (hd3 : 3≤d) (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1))
local notation "hdp" => Nat.le_trans (by decide : 1≤3) hd3
local notation "F" => bottomTensorFamily g
local notation "Q₀" => fun i => scalarEvenBiform (h := h) (Q i)
local notation "F₁" => fun i => oddBiformEmbedding hdp (by decide) (F i)
local notation "hQ₀" => fun i => scalarEvenBiform_weighted (h := h) (Q i)
local notation "hF₁" => fun i => oddLinearBiform_weighted hdp (F i)
local notation "eW" => oddTargetBaseEquiv hdp Q₀ F₁ hQ₀ hF₁
local notation "eV" => oddSourceBaseEquiv hdp F
local notation "μ" => evenBackgroundScalar hdp Q F
local notation "ν" => bottomCoordinateScalarAction hdp Q g

theorem even_full_bottom_compat (ell : EvenBackgroundTarget hdp Q F →ₗ[K] K)
    (p : Forms K m d) (x : OddBottomQuotient F) :
    ell (μ p ((eV).symm (x,0)))=splitTargetBottom eW ell (ν p x) := by
  have he := evenBackgroundScalar_bottom hdp Q g p x
  change ell (μ p ((eV).symm (x,0)))=ell ((eW).symm (ν p x,0))
  rw [←he,LinearEquiv.symm_apply_apply]

theorem even_full_bottom_kernel (ell : EvenBackgroundTarget hdp Q F →ₗ[K] K) :
    (QuotientCovectorKernel.relation μ ell).ker.comap
      ((eV).symm.toLinearMap.comp (LinearMap.inl K (OddBottomQuotient F)
        (HigherOddCoordinates K h m d hdp)))=
      (QuotientCovectorKernel.relation ν (splitTargetBottom eW ell)).ker :=
  pi_bottom_kernel_eq eV μ ν ell (splitTargetBottom eW ell)
    (even_full_bottom_compat hd3 Q g ell)

theorem even_full_bottom_kernel_finrank_le (ell : EvenBackgroundTarget hdp Q F →ₗ[K] K) :
    finrank K (QuotientCovectorKernel.relation ν (splitTargetBottom eW ell)).ker≤
      finrank K (QuotientCovectorKernel.relation μ ell).ker :=
  pi_bottom_kernel_finrank_le eV μ ν ell (splitTargetBottom eW ell)
    (even_full_bottom_compat hd3 Q g ell)

theorem even_full_higher_kernel_growth
    (t : ℕ)
    (hmid : ∀ (j : ℕ) (hj : 3≤j) (hjd : j≤d), j%2=1 →
      OddScalarLayerProperty t (by omega : 1≤j) hjd
        (F,fun i => scalarBiformEquiv (h := h) (Q i)))
    (ell : EvenBackgroundTarget hdp Q F →ₗ[K] K) :
    t*(finrank K (QuotientCovectorKernel.relation μ ell).ker-
      finrank K (QuotientCovectorKernel.relation ν (splitTargetBottom eW ell)).ker)≤
      finrank K (BilinearImage.image (splitTargetHigherAction eW μ)
        (QuotientCovectorKernel.relation μ ell).ker) := by
  have hg := evenAmbientHigher_growth hd3 Q F t hmid
    (QuotientCovectorKernel.relation μ ell).ker
  rw [even_full_bottom_kernel hd3 Q g ell] at hg
  exact hg

end Froberg
