module

public import Froberg.CoreBiform

@[expose] public section

/-! Actual tensor-product denominator pieces are killed by the split detector
when either their output product or their scalar product is killed. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module TensorProduct MvPolynomial
variable {K : Type} [Field K] {h m : ℕ}

/-- The actual polynomial image of a tensor product of arbitrary subspaces. -/
def polynomialTensorMap (A : Submodule K (Poly K h)) (B : Submodule K (Poly K m)) :
    (A ⊗[K] B) →ₗ[K] Poly K (h+m) :=
  (splitPolynomialEquiv (K := K) h m).toLinearMap.comp (TensorProduct.map A.subtype B.subtype)

def polynomialTensorSpace (A : Submodule K (Poly K h)) (B : Submodule K (Poly K m)) :
    Submodule K (Poly K (h+m)) := (polynomialTensorMap A B).range

@[simp] theorem polynomialTensorMap_tmul (A : Submodule K (Poly K h))
    (B : Submodule K (Poly K m)) (a : A) (b : B) :
    polynomialTensorMap A B (a ⊗ₜ[K] b) =
      splitPolynomialEquiv (K := K) h m (a.val ⊗ₜ[K] b.val) := rfl

@[simp] theorem coreCoefficientSpace_eq_polynomialTensorSpace (i j : ℕ) :
    coreCoefficientSpace K h m (i+j) i =
      polynomialTensorSpace (Forms K h i) (Forms K m j) :=
  coreCoefficientSpace_eq_split_range

/-- The pure-tensor formula for a product is its actual polynomial formula. -/
theorem splitPolynomialDetector_product {X : Type*} [AddCommGroup X] [Module K X]
    (T : Poly K h →ₗ[K] X) (Q : Submodule K (Poly K m))
    (a c : Poly K h) (b e : Poly K m) :
    splitPolynomialDetector T Q
      (splitPolynomialEquiv (K := K) h m (a ⊗ₜ[K] b) * splitPolynomialEquiv (K := K) h m (c ⊗ₜ[K] e)) =
      T (a*c) ⊗ₜ[K] Q.mkQ (b*e) := by
  rw [← map_mul]
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  simp only [splitPolynomialDetector,LinearMap.comp_apply,AlgEquiv.toLinearMap_apply,
    AlgEquiv.symm_apply_apply,TensorProduct.map_tmul]

/-- Products of actual tensor-subspaces are killed whenever the pure
output-scalar pairs are killed; finite tensor sums introduce no extra condition. -/
theorem polynomialTensorSpace_product_killed {X : Type*} [AddCommGroup X] [Module K X]
    (T : Poly K h →ₗ[K] X) (Q : Submodule K (Poly K m))
    (A C : Submodule K (Poly K h)) (B D : Submodule K (Poly K m))
    (hzero : ∀ a : A, ∀ b : B, ∀ c : C, ∀ e : D,
      T (a.val*c.val) ⊗ₜ[K] Q.mkQ (b.val*e.val) = 0) :
    polynomialTensorSpace A B * polynomialTensorSpace C D ≤ (splitPolynomialDetector T Q).ker := by
  apply Submodule.mul_le.mpr
  rintro _ ⟨v,rfl⟩ _ ⟨w,rfl⟩
  change splitPolynomialDetector T Q (polynomialTensorMap A B v * polynomialTensorMap C D w) = 0
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c e =>
      rw [polynomialTensorMap_tmul,polynomialTensorMap_tmul,splitPolynomialDetector_product]
      exact hzero a b c e
    | add u v hu hv => simp only [map_add,mul_add,hu,hv,add_zero]
  | add u v hu hv => simp only [map_add,add_mul,hu,hv,add_zero]

/-- A killed output product kills the entire actual polynomial denominator. -/
theorem polynomialTensorSpace_product_le_ker_left {X : Type*} [AddCommGroup X] [Module K X]
    (T : Poly K h →ₗ[K] X) (Q : Submodule K (Poly K m))
    (A C : Submodule K (Poly K h)) (B D : Submodule K (Poly K m))
    (hAC : A*C ≤ T.ker) :
    polynomialTensorSpace A B * polynomialTensorSpace C D ≤ (splitPolynomialDetector T Q).ker := by
  apply polynomialTensorSpace_product_killed T Q A C B D
  intro a b c e
  have hz := hAC (Submodule.mul_mem_mul a.property c.property)
  change T (a.val*c.val) = 0 at hz
  rw [hz,zero_tmul]

/-- A scalar ideal product kills the entire actual polynomial denominator. -/
theorem polynomialTensorSpace_product_le_ker_right {X : Type*} [AddCommGroup X] [Module K X]
    (T : Poly K h →ₗ[K] X) (Q : Submodule K (Poly K m))
    (A C : Submodule K (Poly K h)) (B D : Submodule K (Poly K m))
    (hBD : B*D ≤ Q) :
    polynomialTensorSpace A B * polynomialTensorSpace C D ≤ (splitPolynomialDetector T Q).ker := by
  apply polynomialTensorSpace_product_killed T Q A C B D
  intro a b c e
  have hz : Q.mkQ (b.val*e.val) = 0 :=
    (Submodule.Quotient.mk_eq_zero Q).mpr (hBD (Submodule.mul_mem_mul b.property e.property))
  rw [hz,tmul_zero]

end Froberg
