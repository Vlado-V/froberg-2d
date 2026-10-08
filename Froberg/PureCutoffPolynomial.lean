import Froberg.PureCutoffPropagation
import Froberg.PureCutoff

/-! Translation of the intrinsic pure cutoff into the actual polynomial
product equality used by upper-row propagation. -/
noncomputable section
namespace Froberg
open Module Quartic
variable {K : Type*} [Field K] {h d e : ℕ}

theorem graded_flip_image_polynomial (U : Submodule K (Forms K h d)) :
    (BilinearImage.image (gradedMultiplication (K := K) (n := h) (d := d) (e := e)).flip U).map
      (Forms K h (d+e)).subtype = U.map (Forms K h d).subtype*Forms K h e := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply iSup_le
    intro f
    rintro _ ⟨u,hu,rfl⟩
    exact Submodule.mul_mem_mul ⟨u,hu,rfl⟩ f.property
  · apply Submodule.mul_le.mpr
    intro u hu f hf
    obtain ⟨u,hu,rfl⟩ := hu
    exact ⟨gradedMultiplication u ⟨f,hf⟩,
      BilinearImage.product_mem gradedMultiplication.flip U ⟨f,hf⟩ u hu,rfl⟩

theorem pure_cutoff_polynomial (U : Submodule K (Forms K h d))
    (hU : BilinearImage.image (gradedMultiplication (K := K) (n := h) (d := d) (e := 1)).flip U=⊤) :
    U.map (Forms K h d).subtype*Forms K h 1=Forms K h (d+1) := by
  have he := graded_flip_image_polynomial (e := 1) U
  rw [hU,Submodule.map_top,Submodule.range_subtype] at he
  exact he.symm

end Froberg
