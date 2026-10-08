import Froberg.LinearPolynomialActions

/-! # Changes of the ordered generating family

The same matrix acts on an arbitrary finite family of vectors by linear
combinations.  The contragredient change on coefficients preserves the
actual endpoint multiplication map.
-/

noncomputable section
namespace Froberg
open Matrix

section Families
variable {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V] {r : ℕ}

def mixFamily (A : Matrix (Fin r) (Fin r) K) (v : Fin r → V) : Fin r → V :=
  fun i => ∑ j, A i j • v j

@[simp] theorem mixFamily_one (v : Fin r → V) : mixFamily (1 : Matrix _ _ K) v = v := by
  ext i
  simp [mixFamily, Matrix.one_apply]

theorem mixFamily_mul (A B : Matrix (Fin r) (Fin r) K) (v : Fin r → V) :
    mixFamily (A * B) v = mixFamily A (mixFamily B v) := by
  ext i
  simp only [mixFamily, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  rw [Finset.sum_comm]

def mixFamilyLinear (A : Matrix (Fin r) (Fin r) K) : (Fin r → V) →ₗ[K] (Fin r → V) where
  toFun := mixFamily A
  map_add' v w := by ext i; simp [mixFamily, smul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    funext i
    change (∑ j, A i j • (c • v j)) = c • ∑ j, A i j • v j
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact smul_comm _ _ _

def slFamilyEquiv (a : SpecialLinearGroup (Fin r) K) : (Fin r → V) ≃ₗ[K] (Fin r → V) where
  toFun := mixFamily (a : Matrix (Fin r) (Fin r) K)
  invFun := mixFamily ((a⁻¹ : SpecialLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K)
  left_inv v := by
    rw [← mixFamily_mul, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
      SpecialLinearGroup.coe_one, mixFamily_one]
  right_inv v := by
    rw [← mixFamily_mul, ← SpecialLinearGroup.coe_mul, mul_inv_cancel,
      SpecialLinearGroup.coe_one, mixFamily_one]
  map_add' v w := (mixFamilyLinear (V := V) (a : Matrix (Fin r) (Fin r) K)).map_add v w
  map_smul' c v := (mixFamilyLinear (V := V) (a : Matrix (Fin r) (Fin r) K)).map_smul c v

end Families

variable {K : Type*} [Field K] {n d r : ℕ}

/-- The bilinear endpoint pairing is unchanged by inverse-transpose
changes of generators and coefficients. -/
theorem endpointMultiplication_change_generators
    (A B : Matrix (Fin r) (Fin r) K) (hAB : A * B = 1)
    (q f : Fin r → Forms K n d) :
    endpointMultiplication (mixFamily A.transpose q) (mixFamily B f) =
      endpointMultiplication q f := by
  apply Subtype.ext
  simp only [endpointMultiplication_val, mixFamily, Submodule.coe_sum,
    Submodule.coe_smul, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  simp only [smul_mul_smul_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, ← Matrix.mul_apply, hAB, Matrix.one_apply]
  simp

end Froberg
