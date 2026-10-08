import Froberg.HigherProjectedGrowth

/-! Surjective scalar-coordinate changes preserve the actual full
bilinear image; source isomorphisms preserve every uniform growth rate. -/
noncomputable section
namespace Froberg
open Module Quartic
variable {K P P' V V' W : Type*} [Field K]
  [AddCommGroup P] [Module K P] [AddCommGroup P'] [Module K P']
  [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
  [AddCommGroup W] [Module K W]

theorem bilinearImage_parameter_surjective (mu : P →ₗ[K] V →ₗ[K] W)
    (e : P' →ₗ[K] P) (he : Function.Surjective e) (L : Submodule K V) :
    BilinearImage.image (mu.comp e) L=BilinearImage.image mu L := by
  apply le_antisymm
  · apply iSup_le
    intro p
    exact le_iSup (fun p => L.map (mu p)) (e p)
  · apply iSup_le
    intro p
    obtain ⟨p,rfl⟩ := he p
    exact le_iSup (fun p => L.map ((mu.comp e) p)) p

theorem bilinear_growth_parameter_equiv [FiniteDimensional K V] [FiniteDimensional K W]
    (mu : P →ₗ[K] V →ₗ[K] W) (e : P' ≃ₗ[K] P) (r : ℕ)
    (hg : ∀ L : Submodule K V,r*finrank K L≤finrank K (BilinearImage.image mu L))
    (L : Submodule K V) :
    r*finrank K L≤finrank K (BilinearImage.image (mu.comp e.toLinearMap) L) := by
  rw [bilinearImage_parameter_surjective mu e.toLinearMap e.surjective]
  exact hg L

theorem bilinear_growth_source_equiv [FiniteDimensional K V] [FiniteDimensional K V']
    [FiniteDimensional K W] (mu : P →ₗ[K] V →ₗ[K] W) (e : V' ≃ₗ[K] V) (r : ℕ)
    (hg : ∀ L : Submodule K V,r*finrank K L≤finrank K (BilinearImage.image mu L))
    (L : Submodule K V') :
    r*finrank K L≤finrank K (BilinearImage.image (mu.compl₂ e.toLinearMap) L) := by
  rw [bilinearImage_precompose]
  have hh := hg (L.map e.toLinearMap)
  rwa [e.finrank_map_eq] at hh

end Froberg
