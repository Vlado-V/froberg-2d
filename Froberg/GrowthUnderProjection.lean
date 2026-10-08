import Froberg.BilinearPostcompose

/-! A lower bound after a target projection is a lower bound before it. -/
noncomputable section
namespace Froberg
open Module Quartic
variable {K F V W Z : Type*} [Field K]
  [AddCommGroup F] [Module K F]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup Z] [Module K Z]

theorem bilinear_image_postcompose_finrank_le (mu : F →ₗ[K] V →ₗ[K] W)
    (P : W →ₗ[K] Z) (L : Submodule K V) :
    finrank K (BilinearImage.image (mu.compr₂ₛₗ P) L)≤finrank K (BilinearImage.image mu L) := by
  rw [bilinearImage_postcompose]
  exact Submodule.finrank_map_le P _

theorem bilinear_growth_of_postcompose (mu : F →ₗ[K] V →ₗ[K] W)
    (P : W →ₗ[K] Z) (c : ℕ)
    (h : ∀ L : Submodule K V,c*finrank K L≤finrank K (BilinearImage.image (mu.compr₂ₛₗ P) L))
    (L : Submodule K V) : c*finrank K L≤finrank K (BilinearImage.image mu L) :=
  (h L).trans (bilinear_image_postcompose_finrank_le mu P L)

end Froberg
