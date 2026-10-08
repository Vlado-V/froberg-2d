import Froberg.BilinearPostcompose

/-! A surjective change of scalar parameters leaves the full bilinear
image unchanged. -/
noncomputable section
namespace Froberg
open Quartic
variable {K P Q V W : Type*} [Field K]
  [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem bilinearImage_scalar_comp (mu : P →ₗ[K] V →ₗ[K] W)
    (f : Q →ₗ[K] P) (hf : Function.Surjective f) (L : Submodule K V) :
    BilinearImage.image (mu.comp f) L=BilinearImage.image mu L := by
  apply le_antisymm
  · apply iSup_le
    intro q
    exact le_iSup (fun p : P => L.map (mu p)) (f q)
  · apply iSup_le
    intro p
    obtain ⟨q,rfl⟩ := hf p
    exact le_iSup (fun q : Q => L.map ((mu.comp f) q)) q

end Froberg
