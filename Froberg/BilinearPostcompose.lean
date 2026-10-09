module

public import Quartic.BilinearImage

@[expose] public section

/-! Postcomposition of the actual image of a bilinear map. -/
noncomputable section
namespace Froberg
open Quartic
variable {K : Type*} [Field K]

theorem bilinearImage_postcompose {P V W Z : Type*}
    [AddCommGroup P] [Module K P] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup Z] [Module K Z]
    (μ : P →ₗ[K] V →ₗ[K] W) (f : W →ₗ[K] Z) (L : Submodule K V) :
    BilinearImage.image (μ.compr₂ₛₗ f) L=(BilinearImage.image μ L).map f := by
  simp only [BilinearImage.image,Submodule.map_iSup]
  congr 1
  funext p
  rw [← Submodule.map_comp]
  rfl

end Froberg
