module

public import Froberg.Koszul
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

@[expose] public section

/-!+# Linear changes of the actual homogeneous polynomial spaces

The substitution uses the columns of the matrix, so multiplication of matrices
agrees with composition of substitutions.  All maps act on the polynomial
spaces used to define the endpoint multiplication map.
-/

noncomputable section
namespace Froberg
open MvPolynomial Matrix

section Linear
variable {K : Type*} [Field K] {n d : ℕ}

/-- Linear substitution on the polynomial algebra, in column convention. -/
def linearSubstitution (A : Matrix (Fin n) (Fin n) K) : Poly K n →ₐ[K] Poly K n :=
  aeval (fun i => ∑ j, C (A j i) * X j)

@[simp] theorem linearSubstitution_X (A : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    linearSubstitution A (X i) = ∑ j, C (A j i) * X j := by
  simp [linearSubstitution]

@[simp] theorem linearSubstitution_C (A : Matrix (Fin n) (Fin n) K) (c : K) :
    linearSubstitution A (C c) = C c := by simp [linearSubstitution]

@[simp] theorem linearSubstitution_one :
    linearSubstitution (1 : Matrix (Fin n) (Fin n) K) = AlgHom.id K (Poly K n) := by
  ext i
  simp [linearSubstitution_X, Matrix.one_apply]

theorem linearSubstitution_mul (A B : Matrix (Fin n) (Fin n) K) :
    linearSubstitution (A * B) = (linearSubstitution A).comp (linearSubstitution B) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, linearSubstitution_X, map_sum, map_mul,
    linearSubstitution_C, Matrix.mul_apply]
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem linearSubstitution_homogeneous (A : Matrix (Fin n) (Fin n) K)
    (p : Poly K n) (hp : p.IsHomogeneous d) :
    (linearSubstitution A p).IsHomogeneous d := by
  simpa only [linearSubstitution, one_mul] using hp.aeval
    (fun i => ∑ j, C (A j i) * X j)
    (fun i => IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X (A j i) j))

theorem linearSubstitution_smul_one (a : K) :
    linearSubstitution (a • (1 : Matrix (Fin n) (Fin n) K)) =
      aeval (fun i => C a * X i) := by
  ext i
  simp [linearSubstitution_X, Matrix.smul_apply, Matrix.one_apply]

/-- A scalar change of variables acts on degree `d` by its `d`-th power. -/
theorem linearSubstitution_scalar_homogeneous (a : K) (p : Poly K n)
    (hp : p.IsHomogeneous d) :
    linearSubstitution (a • (1 : Matrix (Fin n) (Fin n) K)) p = a ^ d • p := by
  rw [linearSubstitution_smul_one]
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp only [map_add, ihp, ihq, smul_add]
  | monomial s c hs =>
    have hs' : s.degree = d := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hs
    have hpow : s.prod (fun _ k => C a ^ k) = (C a : Poly K n) ^ d := by
      rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply, hs']
    rw [aeval_monomial]
    simp only [algebraMap_eq, mul_pow, Finsupp.prod_mul, hpow,
      MvPolynomial.smul_eq_C_mul, map_pow, monomial_eq]
    ring

/-- An actual special-linear matrix induces an algebra equivalence. -/
def slPolynomialEquiv (g : SpecialLinearGroup (Fin n) K) : Poly K n ≃ₐ[K] Poly K n :=
  AlgEquiv.ofAlgHom (linearSubstitution (g : Matrix (Fin n) (Fin n) K))
    (linearSubstitution (g⁻¹ : SpecialLinearGroup (Fin n) K))
    (by rw [← linearSubstitution_mul, ← SpecialLinearGroup.coe_mul,
      mul_inv_cancel, SpecialLinearGroup.coe_one, linearSubstitution_one])
    (by rw [← linearSubstitution_mul, ← SpecialLinearGroup.coe_mul,
      inv_mul_cancel, SpecialLinearGroup.coe_one, linearSubstitution_one])

@[simp] theorem slPolynomialEquiv_apply (g : SpecialLinearGroup (Fin n) K) (p : Poly K n) :
    slPolynomialEquiv g p = linearSubstitution (g : Matrix (Fin n) (Fin n) K) p := rfl

/-- The special-linear action on the polynomial algebra. -/
def slPolynomialAction : SpecialLinearGroup (Fin n) K →* (Poly K n ≃ₐ[K] Poly K n) where
  toFun := slPolynomialEquiv
  map_one' := by
    apply AlgEquiv.ext
    intro p
    exact AlgHom.congr_fun linearSubstitution_one p
  map_mul' g h := by
    apply AlgEquiv.ext
    intro p
    exact AlgHom.congr_fun (linearSubstitution_mul
      (g : Matrix (Fin n) (Fin n) K) (h : Matrix (Fin n) (Fin n) K)) p

/-- The induced action on degree-`d` forms. -/
def slFormsEquiv (g : SpecialLinearGroup (Fin n) K) (d : ℕ) :
    Forms K n d ≃ₗ[K] Forms K n d where
  toFun p := ⟨slPolynomialEquiv g p.val, linearSubstitution_homogeneous _ _ p.property⟩
  invFun p := ⟨slPolynomialEquiv g⁻¹ p.val, linearSubstitution_homogeneous _ _ p.property⟩
  left_inv p := Subtype.ext ((slPolynomialEquiv g).left_inv p.val)
  right_inv p := Subtype.ext ((slPolynomialEquiv g).right_inv p.val)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

@[simp] theorem slFormsEquiv_val (g : SpecialLinearGroup (Fin n) K)
    (p : Forms K n d) :
    (slFormsEquiv g d p).val = slPolynomialEquiv g p.val := rfl

end Linear

variable {K : Type*} [Field K] {n d r : ℕ}

/-- Variable changes commute with actual endpoint multiplication. -/
theorem slFormsEquiv_endpointMultiplication (g : SpecialLinearGroup (Fin n) K)
    (q f : Fin r → Forms K n d) :
    slFormsEquiv g (2 * d) (endpointMultiplication q f) =
      endpointMultiplication (fun i => slFormsEquiv g d (q i))
        (fun i => slFormsEquiv g d (f i)) := by
  apply Subtype.ext
  simp only [slFormsEquiv_val, endpointMultiplication, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, Submodule.coe_sum]
  change slPolynomialEquiv g (∑ i, (q i).val * (f i).val) =
    ∑ i, slPolynomialEquiv g (q i).val * slPolynomialEquiv g (f i).val
  simp only [map_sum, map_mul]

end Froberg
