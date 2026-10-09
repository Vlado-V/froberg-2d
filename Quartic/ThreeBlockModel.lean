module

public import Quartic.ThreeBlock
public import Quartic.Homology

@[expose] public section

/-!
# The explicit three-variable block in the homogeneous polynomial model

The four quadrics `(xy, xz, yz, x²+y²+z²)` are linearly independent.
Their products with linear forms fill the cubic space, and their products
with quadrics fill the quartic space. Consequently their actual degree-four
Koszul homology has dimension three.
-/

namespace Quartic.ThreeBlockModel

noncomputable section

open MvPolynomial Quartic.ThreeBlock

variable {K : Type*} [Field K]

theorem quadrics_homogeneous (i : Fin 4) :
    IsHomogeneous (quadrics (K := K) i) 2 := by
  fin_cases i
  · exact (isHomogeneous_X K (0 : Fin 3)).mul (isHomogeneous_X K (1 : Fin 3))
  · exact (isHomogeneous_X K (0 : Fin 3)).mul (isHomogeneous_X K (2 : Fin 3))
  · exact (isHomogeneous_X K (1 : Fin 3)).mul (isHomogeneous_X K (2 : Fin 3))
  · exact ((isHomogeneous_X_pow (0 : Fin 3) 2).add
      (isHomogeneous_X_pow (1 : Fin 3) 2)).add (isHomogeneous_X_pow (2 : Fin 3) 2)

/-- The manuscript's generators, as actual homogeneous quadrics. -/
def blockQuadrics (i : Fin 4) : Quartic.Forms K 3 2 :=
  ⟨quadrics i, quadrics_homogeneous i⟩

@[simp] theorem blockQuadrics_val (i : Fin 4) :
    (blockQuadrics (K := K) i).val = quadrics i := rfl

/-- Four coefficient positions that distinguish the four block quadrics. -/
def separatingExponents : Fin 4 → (Fin 3 →₀ ℕ) :=
  ![Finsupp.single 0 1 + Finsupp.single 1 1,
    Finsupp.single 0 1 + Finsupp.single 2 1,
    Finsupp.single 1 1 + Finsupp.single 2 1, Finsupp.single 0 2]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem separating_coefficients (i j : Fin 4) :
    (quadrics (K := K) j).coeff (separatingExponents i) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [quadrics, separatingExponents, x, y, z, MvPolynomial.X, pow_two,
      monomial_mul_monomial, coeff_monomial, Finsupp.ext_iff, Fin.forall_fin_succ]

theorem blockQuadrics_independent : LinearIndependent K (blockQuadrics (K := K)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have h := congrArg (fun p : Quartic.Forms K 3 2 => p.val.coeff (separatingExponents i)) hc
  simpa [Submodule.coe_sum, Submodule.coe_smul, coeff_sum, coeff_smul,
    blockQuadrics_val, separating_coefficients, Submodule.coe_zero, AddMonoidAlgebra.coeff_zero, Pi.zero_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
    ite_true] using h

/-- The intrinsic quadratic generator subspace in the polynomial ring. -/
def blockSpace : Submodule K (Quartic.Poly K 3) :=
  Submodule.span K (Set.range (quadrics (K := K)))

theorem cubicPreimages_homogeneous (i : Fin 10) (j : Fin 4) :
    IsHomogeneous (cubicPreimages (K := K) i j) 1 := by
  fin_cases i <;> fin_cases j <;> simp [cubicPreimages, x, y, z]
  all_goals first | exact isHomogeneous_X K _ | exact (isHomogeneous_X K _).neg |
    exact isHomogeneous_zero _ K _

theorem relation_mem_cubic_product (a : Fin 4 → Quartic.Poly K 3)
    (ha : ∀ i, IsHomogeneous (a i) 1) :
    relation a ∈ blockSpace (K := K) * Quartic.Forms K 3 1 := by
  have h (i : Fin 4) : a i * quadrics i ∈ blockSpace (K := K) * Quartic.Forms K 3 1 := by
    rw [mul_comm (a i) (quadrics i)]
    exact Submodule.mul_mem_mul
      (show quadrics i ∈ blockSpace from Submodule.subset_span ⟨i, rfl⟩) (ha i)
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (h 0) (h 1))
    (h 2)) (h 3)

theorem cubicMonomials_mem_product (i : Fin 10) :
    cubicMonomials (K := K) i ∈ blockSpace (K := K) * Quartic.Forms K 3 1 := by
  rw [← cubicPreimages_spec]
  exact relation_mem_cubic_product _ (cubicPreimages_homogeneous i)

set_option maxHeartbeats 2000000 in
theorem triple_variable_product_mem (i j k : Fin 3) :
    (X i * X j) * X k ∈ blockSpace (K := K) * Quartic.Forms K 3 1 := by
  fin_cases i <;> fin_cases j <;> fin_cases k
  · convert cubicMonomials_mem_product (K := K) 0 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 1 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 2 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 1 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 3 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 4 using 1
    simp [cubicMonomials, x, y, z]
  · convert cubicMonomials_mem_product (K := K) 2 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 4 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 5 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 1 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 3 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 4 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 3 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 6 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 7 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 4 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 7 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 8 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 2 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 4 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 5 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 4 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 7 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 8 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 5 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 8 using 1
    simp [cubicMonomials, x, y, z]
    ring
  · convert cubicMonomials_mem_product (K := K) 9 using 1
    simp [cubicMonomials, x, y, z]
    ring

/-- The four explicit generators fill the entire cubic space. -/
theorem cubic_products_eq :
    blockSpace (K := K) * Quartic.Forms K 3 1 = Quartic.Forms K 3 3 := by
  apply le_antisymm
  · apply (mul_le_mul_left ?_ _).trans (homogeneousSubmodule_mul 2 1)
    exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact quadrics_homogeneous i)
  · rw [Quartic.Forms, ← homogeneousSubmodule_one_pow K 3,
      homogeneousSubmodule_one_eq_span_X, pow_succ, pow_two,
      Submodule.span_mul_span, Submodule.span_mul_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ⟨b, ⟨i, rfl⟩, c, ⟨j, rfl⟩, rfl⟩, d, ⟨k, rfl⟩, rfl⟩
    exact triple_variable_product_mem i j k

/-- Quartic surjectivity follows by multiplying cubic surjectivity by linear forms. -/
theorem quartic_products_eq :
    blockSpace (K := K) * Quartic.Forms K 3 2 = Quartic.Forms K 3 4 := by
  calc
    blockSpace * Quartic.Forms K 3 2 =
        (blockSpace * Quartic.Forms K 3 1) * Quartic.Forms K 3 1 := by
      rw [mul_assoc, ← pow_two, Quartic.Forms, homogeneousSubmodule_one_pow]
    _ = Quartic.Forms K 3 3 * Quartic.Forms K 3 1 := by rw [cubic_products_eq]
    _ = Quartic.Forms K 3 4 := by
      rw [Quartic.Forms, ← homogeneousSubmodule_one_pow K 3,
        ← pow_succ, homogeneousSubmodule_one_pow]

/-- The actual quartic multiplication map of the four block quadrics is onto. -/
theorem blockMultiplication_surjective :
    Function.Surjective (Quartic.quadraticMultiplication (blockQuadrics (K := K))) := by
  rw [← LinearMap.range_eq_top, Quartic.range_quadraticMultiplication]
  change (blockSpace * Quartic.Forms K 3 2).comap (Quartic.Forms K 3 4).subtype = ⊤
  rw [quartic_products_eq]
  simp

/-- The actual degree-four first Koszul homology of the three-variable block
has the dimension asserted in `tb:pure`. -/
theorem blockHomology_finrank :
    Module.finrank K (Quartic.QuarticHomology (blockQuadrics (K := K))) = 3 := by
  have hhom := Quartic.homology_add_pairs (blockQuadrics (K := K)) blockQuadrics_independent
  have hrank := (Quartic.quadraticMultiplication (blockQuadrics (K := K))).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr blockMultiplication_surjective, finrank_top,
    Quartic.finrank_quartics] at hrank
  have hsource : Module.finrank K (Fin 4 → Quartic.Forms K 3 2) = 24 := by
    norm_num [Module.finrank_pi_fintype, Quartic.finrank_quadrics, Nat.choose]
  rw [hsource] at hrank
  norm_num [Nat.choose] at hhom hrank
  omega

end

end Quartic.ThreeBlockModel
