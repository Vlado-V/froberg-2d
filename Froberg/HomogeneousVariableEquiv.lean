import Froberg.Graded

/-! Equivalences of variable sets on homogeneous polynomial spaces, with
their compatibility with multiplication. -/
noncomputable section
namespace Froberg
open MvPolynomial

variable {K σ τ : Type*} [Field K]

/-- Renaming by a variable equivalence restricts to every homogeneous degree. -/
def homogeneousVariableEquiv (e : σ ≃ τ) (d : ℕ) :
    homogeneousSubmodule σ K d ≃ₗ[K] homogeneousSubmodule τ K d where
  toFun p := ⟨rename e p.val, p.property.rename_isHomogeneous⟩
  invFun p := ⟨rename e.symm p.val, p.property.rename_isHomogeneous⟩
  left_inv p := Subtype.ext (by
    change rename e.symm (rename e p.val) = p.val
    rw [rename_rename, e.symm_comp_self, rename_id_apply])
  right_inv p := Subtype.ext (by
    change rename e (rename e.symm p.val) = p.val
    rw [rename_rename, e.self_comp_symm, rename_id_apply])
  map_add' p q := Subtype.ext (map_add (rename e) p.val q.val)
  map_smul' c p := Subtype.ext (by simp)

@[simp] theorem coe_homogeneousVariableEquiv (e : σ ≃ τ) (d : ℕ)
    (p : homogeneousSubmodule σ K d) :
    (homogeneousVariableEquiv e d p).val = rename e p.val := rfl

@[simp] theorem homogeneousVariableEquiv_symm (e : σ ≃ τ) (d : ℕ) :
    (homogeneousVariableEquiv (K := K) e d).symm =
      homogeneousVariableEquiv e.symm d := rfl

/-- Homogeneous multiplication for an arbitrary variable type. -/
def homogeneousMul {a b : ℕ} :
    homogeneousSubmodule σ K a →ₗ[K]
      homogeneousSubmodule σ K b →ₗ[K] homogeneousSubmodule σ K (a + b) where
  toFun p :=
    { toFun := fun q => ⟨p.val * q.val, p.property.mul q.property⟩
      map_add' := fun q r => Subtype.ext (mul_add _ _ _)
      map_smul' := fun c q => Subtype.ext (mul_smul_comm _ _ _) }
  map_add' p q := by
    apply LinearMap.ext
    intro r
    exact Subtype.ext (add_mul _ _ _)
  map_smul' c p := by
    apply LinearMap.ext
    intro q
    exact Subtype.ext (smul_mul_assoc _ _ _)

@[simp] theorem coe_homogeneousMul {a b : ℕ}
    (p : homogeneousSubmodule σ K a) (q : homogeneousSubmodule σ K b) :
    (homogeneousMul p q).val = p.val * q.val := rfl

/-- A variable equivalence commutes with homogeneous multiplication. -/
theorem homogeneousVariableEquiv_mul (e : σ ≃ τ) {a b : ℕ}
    (p : homogeneousSubmodule σ K a) (q : homogeneousSubmodule σ K b) :
    homogeneousVariableEquiv e (a + b) (homogeneousMul p q) =
      homogeneousMul (homogeneousVariableEquiv e a p) (homogeneousVariableEquiv e b q) :=
  Subtype.ext (map_mul (rename e) p.val q.val)

/-- Multiplication of linear forms, with its target written in degree two. -/
abbrev homogeneousOneMul :
    homogeneousSubmodule σ K 1 →ₗ[K]
      homogeneousSubmodule σ K 1 →ₗ[K] homogeneousSubmodule σ K 2 :=
  homogeneousMul

theorem homogeneousVariableEquiv_one_mul (e : σ ≃ τ)
    (p q : homogeneousSubmodule σ K 1) :
    homogeneousVariableEquiv e 2 (homogeneousOneMul p q) =
      homogeneousOneMul (homogeneousVariableEquiv e 1 p) (homogeneousVariableEquiv e 1 q) :=
  homogeneousVariableEquiv_mul e p q

end Froberg
