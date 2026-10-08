import Froberg.Graded
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # A basis of products of Vandermonde linear forms

Complementary root polynomials supply diagonal evaluation functionals. This
is the product-basis assertion used in symmetric-power convolution, proved
on the actual homogeneous polynomial spaces.
-/

noncomputable section
namespace Froberg
open Finset

variable {K : Type*} [Field K]

/-- The linear form with moment-curve coefficient vector. -/
def momentLinear (a : ℕ) (t : K) : Poly K a :=
  ∑ i : Fin a, MvPolynomial.C (t ^ (i : ℕ)) * MvPolynomial.X i

theorem momentLinear_homogeneous (a : ℕ) (t : K) :
    (momentLinear a t).IsHomogeneous 1 := by
  exact MvPolynomial.IsHomogeneous.sum _ _ _
    (fun i _ => MvPolynomial.isHomogeneous_C_mul_X _ _)

/-- Evaluating the moment linear form at polynomial coefficients evaluates
the original univariate polynomial. -/
theorem momentLinear_eval {a : ℕ} (t : K) (p : Polynomial K) (hp : p.natDegree < a) :
    MvPolynomial.aeval (fun i : Fin a => p.coeff i) (momentLinear a t) = p.eval t := by
  rw [Polynomial.eval_eq_sum_range' hp]
  simp only [momentLinear, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Algebra.algebraMap_self_apply]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => t ^ i * p.coeff i)]
  apply Finset.sum_congr rfl
  intro i hi
  ring

abbrev ConvolutionSubset (a e : ℕ) :=
  {I : Finset (Fin (a + e - 1)) // I.card = e}

/-- The product indexed by an `e`-element subset of the moment linear forms. -/
def momentProduct {a e : ℕ} (t : Fin (a + e - 1) → K) (I : ConvolutionSubset a e) :
    Forms K a e :=
  ⟨∏ i ∈ I.val, momentLinear a (t i), by
    have h := MvPolynomial.IsHomogeneous.prod I.val (fun i => momentLinear a (t i))
      (fun _ => 1) (fun i _ => momentLinear_homogeneous a (t i))
    change (∏ i ∈ I.val, momentLinear a (t i)).IsHomogeneous e
    simpa [I.property] using h⟩

/-- A polynomial vanishing exactly at the complementary labels. -/
def complementRootPolynomial {a e : ℕ} (t : Fin (a + e - 1) → K)
    (I : ConvolutionSubset a e) : Polynomial K :=
  ∏ j ∈ I.valᶜ, (Polynomial.X - Polynomial.C (t j))

theorem complementRootPolynomial_degree {a e : ℕ} (ha : 0 < a)
    (t : Fin (a + e - 1) → K) (I : ConvolutionSubset a e) :
    (complementRootPolynomial t I).natDegree < a := by
  rw [complementRootPolynomial, Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  simp only [Finset.card_compl, Fintype.card_fin, I.property]
  omega

theorem momentProduct_eval {a e : ℕ} (ha : 0 < a) (t : Fin (a + e - 1) → K)
    (I J : ConvolutionSubset a e) :
    MvPolynomial.aeval (fun k : Fin a => (complementRootPolynomial t I).coeff k)
      (momentProduct t J).val =
        ∏ j ∈ J.val, (complementRootPolynomial t I).eval (t j) := by
  simp only [momentProduct, map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  exact momentLinear_eval _ _ (complementRootPolynomial_degree ha t I)

theorem complementRootPolynomial_eval_zero {a e : ℕ} (t : Fin (a + e - 1) → K)
    (I : ConvolutionSubset a e) {j : Fin (a + e - 1)} (hj : j ∉ I.val) :
    (complementRootPolynomial t I).eval (t j) = 0 := by
  simp only [complementRootPolynomial, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  exact Finset.prod_eq_zero (Finset.mem_compl.mpr hj) (sub_self (t j))

theorem complementRootPolynomial_eval_ne_zero {a e : ℕ} (t : Fin (a + e - 1) → K)
    (ht : Function.Injective t) (I : ConvolutionSubset a e)
    {j : Fin (a + e - 1)} (hj : j ∈ I.val) :
    (complementRootPolynomial t I).eval (t j) ≠ 0 := by
  simp only [complementRootPolynomial, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  apply sub_ne_zero.mpr
  intro heq
  have hkj : j = k := ht heq
  subst k
  exact (Finset.mem_compl.mp hk) hj

theorem momentProduct_eval_off_diagonal {a e : ℕ} (ha : 0 < a)
    (t : Fin (a + e - 1) → K) (I J : ConvolutionSubset a e) (hIJ : I ≠ J) :
    MvPolynomial.aeval (fun k : Fin a => (complementRootPolynomial t I).coeff k)
      (momentProduct t J).val = 0 := by
  rw [momentProduct_eval ha]
  have hsub : ¬J.val ⊆ I.val := by
    intro h
    have heq : J.val = I.val := Finset.eq_of_subset_of_card_le h (by rw [I.property, J.property])
    exact hIJ (Subtype.ext heq.symm)
  obtain ⟨j, hj, hnot⟩ := Finset.not_subset.mp hsub
  exact Finset.prod_eq_zero hj (complementRootPolynomial_eval_zero t I hnot)

theorem momentProduct_eval_diagonal_ne_zero {a e : ℕ} (ha : 0 < a)
    (t : Fin (a + e - 1) → K) (ht : Function.Injective t) (I : ConvolutionSubset a e) :
    MvPolynomial.aeval (fun k : Fin a => (complementRootPolynomial t I).coeff k)
      (momentProduct t I).val ≠ 0 := by
  rw [momentProduct_eval ha]
  exact Finset.prod_ne_zero_iff.mpr fun j hj => complementRootPolynomial_eval_ne_zero t ht I hj

/-- All subset products are independent in the actual degree-`e` homogeneous component. -/
theorem momentProducts_linearIndependent {a e : ℕ} (ha : 0 < a)
    (t : Fin (a + e - 1) → K) (ht : Function.Injective t) :
    LinearIndependent K (momentProduct t) := by
  let F : ConvolutionSubset a e → Forms K a e →ₗ[K] K := fun I =>
    (MvPolynomial.aeval (fun k : Fin a => (complementRootPolynomial t I).coeff k)).toLinearMap.comp
      (MvPolynomial.homogeneousSubmodule (Fin a) K e).subtype
  apply LinearIndependent.of_pairwise_dual_eq_zero_one (momentProduct t)
    (fun I => (F I (momentProduct t I))⁻¹ • F I)
  · intro I J hIJ
    simp only [LinearMap.smul_apply, smul_eq_mul]
    have hzero : F I (momentProduct t J) = 0 := momentProduct_eval_off_diagonal ha t I J hIJ
    rw [hzero, mul_zero]
  · intro I
    simp only [LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ (momentProduct_eval_diagonal_ne_zero ha t ht I)

/-- Vandermonde subset products form a basis. -/
def momentProductsBasis {a e : ℕ} (ha : 0 < a)
    (t : Fin (a + e - 1) → K) (ht : Function.Injective t) :
    Module.Basis (ConvolutionSubset a e) K (Forms K a e) := by
  apply basisOfLinearIndependentOfCardEqFinrank' (momentProduct t)
    (momentProducts_linearIndependent ha t ht)
  rw [finrank_forms K a e ha, Fintype.card_finset_len, Fintype.card_fin]

end Froberg
