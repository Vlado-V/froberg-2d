module

public import Froberg.Graded
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

@[expose] public section

/-! Propagation of the pure-X cutoff to every upper bidegree, using actual
polynomial multiplication and its tensor product with the scalar forms. -/
noncomputable section
namespace Froberg
open Module TensorProduct
variable {K : Type*} [Field K] {h m d b e : ℕ}

/-- Once degree d+1 is full, every higher pure-X degree is full. -/
theorem pure_cutoff_propagates (U : Submodule K (Poly K h))
    (hU : U * Forms K h 1 = Forms K h (d+1)) (hb : d+1 ≤ b) :
    U * Forms K h (b-d) = Forms K h b := by
  have hbd : b-d = 1+(b-(d+1)) := by omega
  have ht : d+1+(b-(d+1)) = b := by omega
  rw [hbd,← forms_mul_forms K h 1 (b-(d+1)),← mul_assoc,hU,forms_mul_forms,ht]

/-- Actual multiplication onto any known full homogeneous product piece. -/
def fullProductMap (U : Submodule K (Poly K h))
    (hU : U * Forms K h e = Forms K h b) :
    U ⊗[K] Forms K h e →ₗ[K] Forms K h b :=
  (LinearEquiv.ofEq _ _ hU).toLinearMap.comp (Submodule.mulMap' U (Forms K h e))

@[simp] theorem fullProductMap_tmul (U : Submodule K (Poly K h))
    (hU : U * Forms K h e = Forms K h b) (u : U) (v : Forms K h e) :
    (fullProductMap U hU (u ⊗ₜ[K] v)).val = u.val * v.val := rfl

theorem fullProductMap_surjective (U : Submodule K (Poly K h))
    (hU : U * Forms K h e = Forms K h b) : Function.Surjective (fullProductMap U hU) :=
  (LinearEquiv.ofEq _ _ hU).surjective.comp (Submodule.mulMap'_surjective U (Forms K h e))

/-- The same actual pure multiplication fills the entire upper tensor row. -/
theorem pure_cutoff_tensor_surjective (U : Submodule K (Poly K h))
    (hU : U * Forms K h 1 = Forms K h (d+1)) (hb : d+1 ≤ b) :
    Function.Surjective (TensorProduct.map
      (fullProductMap U (pure_cutoff_propagates U hU hb))
      (LinearMap.id : Forms K m e →ₗ[K] Forms K m e)) := by
  exact TensorProduct.map_surjective (fullProductMap_surjective _ _) Function.surjective_id

end Froberg
