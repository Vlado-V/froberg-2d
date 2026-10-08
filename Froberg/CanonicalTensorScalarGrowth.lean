import Froberg.TensorScalarGrowth

/-! Tensor scalar growth with the canonical tensor additive group, for use in dependent quotients. -/
noncomputable section
namespace Froberg
open Module TensorProduct Quartic
variable {K V P : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup P] [Module K P] [FiniteDimensional K P]

theorem tensorScalarProduct_canonical_image (L : Submodule K V) :
    BilinearImage.image (tensorScalarProduct (P := P)) L=
      (TensorProduct.map L.subtype (LinearMap.id : P →ₗ[K] P)).range := by
  apply le_antisymm
  · apply iSup_le
    intro p
    rintro _ ⟨v,hv,rfl⟩
    exact ⟨(⟨v,hv⟩ : L) ⊗ₜ[K] p,rfl⟩
  · rintro _ ⟨v,rfl⟩
    induction v using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul v p => exact BilinearImage.product_mem _ L p v.val v.property
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

theorem tensorScalarProduct_canonical_finrank (L : Submodule K V) :
    finrank K (BilinearImage.image (tensorScalarProduct (P := P)) L)=
      finrank K P*finrank K L := by
  rw [tensorScalarProduct_canonical_image]
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := P)
    L.subtype L.subtype_injective
  change Function.Injective (TensorProduct.map L.subtype (LinearMap.id : P →ₗ[K] P)) at hinj
  rw [LinearMap.finrank_range_of_inj hinj,Module.finrank_tensorProduct,mul_comm]

end Froberg
