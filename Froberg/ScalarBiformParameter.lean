import Froberg.BiformActions

/-! The scalar slot in a biform action is the actual scalar form space:
the degree-zero output factor is canonically one-dimensional. -/
noncomputable section
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type*} [Field K] {h n d : ℕ}

def constantFormEquiv : K ≃ₗ[K] Forms K h 0 where
  toFun c := ⟨C c,isHomogeneous_C _ c⟩
  invFun p := p.val.coeff 0
  left_inv c := by simp
  right_inv p := by
    apply Subtype.ext
    exact (totalDegree_eq_zero_iff_eq_C.mp
      ((totalDegree_zero_iff_isHomogeneous (Fin h)).mpr p.property)).symm
  map_add' c c' := Subtype.ext (map_add C c c')
  map_smul' c c' := by
    apply Subtype.ext
    simp only [Submodule.coe_smul,smul_eq_mul,smul_eq_C_mul,map_mul,RingHom.id_apply]

def scalarBiformEquiv : Forms K n d ≃ₗ[K] (Forms K h 0 ⊗[K] Forms K n d) :=
  (TensorProduct.lid K (Forms K n d)).symm.trans
    (TensorProduct.congr constantFormEquiv (LinearEquiv.refl K (Forms K n d)))

@[simp] theorem scalarBiformEquiv_apply (f : Forms K n d) :
    scalarBiformEquiv (h := h) f=constantFormEquiv (h := h) (1 : K) ⊗ₜ[K] f := by
  simp only [scalarBiformEquiv,LinearEquiv.trans_apply,TensorProduct.lid_symm_apply,
    TensorProduct.congr_tmul,LinearEquiv.refl_apply]

/-- Use scalar forms directly in any biform action; the scalar slot has no
additional parameter or restriction. -/
def scalarBiformAction {b : ℕ} (hbd : b≤d) :
    Forms K n d →ₗ[K] (Forms K h b ⊗[K] Forms K n (d-b)) →ₗ[K]
      (Forms K h b ⊗[K] Forms K n (2*d-b)) :=
  (oddRowScalarAction hbd).comp scalarBiformEquiv.toLinearMap

end Froberg
