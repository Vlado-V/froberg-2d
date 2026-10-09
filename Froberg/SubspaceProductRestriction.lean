module

public import Froberg.SymmetricIndependence

@[expose] public section

/-! Restricting an independent symmetric-product space to a linear output
constraint loses at most the number of constraint coordinates. -/
noncomputable section
namespace Froberg
open Module
variable {K : Type} [Field K]
variable {A : Type*} [CommRing A] [Algebra K A]

/-- Symmetric multiplication remains injective on every smaller subspace. -/
theorem subspaceSymmetricMultiplication_injective_mono {U W : Submodule K A}
    (hUW : U ≤ W) (hW : Function.Injective (subspaceSymmetricMultiplication W)) :
    Function.Injective (subspaceSymmetricMultiplication U) := by
  have he : subspaceSymmetricMultiplication U =
      (subspaceSymmetricMultiplication W).comp
        (SymmetricFunctor.map (Submodule.inclusion hUW)) := by
    unfold subspaceSymmetricMultiplication
    rw [LinearMap.comp_assoc, ← SymmetricFunctor.map_comp]
    rfl
  rw [he]
  exact hW.comp (SymmetricFunctor.map_injective _ (Submodule.inclusion_injective hUW))

variable {X : Type*} [AddCommGroup X] [Module K X]

/-- The constraint loss is bounded by the dimension of the detector target,
even when the full ambient algebra is infinite-dimensional. -/
theorem finrank_intersection_kernel_lower_bound (O : Submodule K A)
    [Module.Finite K O] [Module.Finite K X] (T : A →ₗ[K] X) :
    finrank K O - finrank K X ≤ finrank K (O ⊓ T.ker : Submodule K A) := by
  let e : (T.comp O.subtype).ker ≃ₗ[K] (O ⊓ T.ker : Submodule K A) :=
    { toFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
      invFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h := (T.comp O.subtype).finrank_range_add_finrank_ker
  have hle := (T.comp O.subtype).range.finrank_le
  have he := e.finrank_eq
  omega

end Froberg
