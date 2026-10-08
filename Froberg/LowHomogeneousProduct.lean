import Froberg.Graded
import Mathlib.Algebra.DirectSum.Internal
import Mathlib.Data.Finset.NatAntidiagonal

/-! The exact low-degree product formula used by background detection. -/
noncomputable section
namespace Froberg
open MvPolynomial
variable {K σ : Type*} [Field K]

/-- Weighted extraction is the finite convolution for any nonnegative
variable weights; weights equal to zero are allowed. -/
theorem weightedHomogeneousComponent_product (w : σ → ℕ)
    (p q : MvPolynomial σ K) (n : ℕ) :
    weightedHomogeneousComponent w n (p*q) =
      ∑ ij ∈ Finset.antidiagonal n,
        weightedHomogeneousComponent w ij.1 p * weightedHomogeneousComponent w ij.2 q := by
  letI : GradedAlgebra (weightedHomogeneousSubmodule K w) := MvPolynomial.weightedGradedAlgebra K w
  have he (r : MvPolynomial σ K) (j : ℕ) :
      (DirectSum.decompose (weightedHomogeneousSubmodule K w) r j : MvPolynomial σ K) =
        weightedHomogeneousComponent w j r := MvPolynomial.weightedDecomposition.decompose'_apply K w r j
  rw [← he,DirectSum.decompose_mul,DirectSum.coe_mul_apply_eq_sum_antidiagonal]
  apply Finset.sum_congr rfl
  intro ij _
  rw [he,he]

/-- The three exact weighted-degree pairs contributing to degree two. -/
theorem weightedHomogeneousComponent_two_product (w : σ → ℕ) (p q : MvPolynomial σ K) :
    weightedHomogeneousComponent w 2 (p*q) =
      weightedHomogeneousComponent w 0 p * weightedHomogeneousComponent w 2 q +
      weightedHomogeneousComponent w 1 p * weightedHomogeneousComponent w 1 q +
      weightedHomogeneousComponent w 2 p * weightedHomogeneousComponent w 0 q := by
  rw [weightedHomogeneousComponent_product]
  have ha : Finset.antidiagonal 2 = {(0,2),(1,1),(2,0)} := by decide
  rw [ha]
  simp [Finset.sum_insert, add_assoc]

/-- Homogeneous extraction of a product is the actual finite convolution. -/
theorem homogeneousComponent_product (p q : MvPolynomial σ K) (n : ℕ) :
    homogeneousComponent n (p*q) =
      ∑ ij ∈ Finset.antidiagonal n,
        homogeneousComponent ij.1 p * homogeneousComponent ij.2 q := by
  letI : GradedAlgebra (homogeneousSubmodule σ K) := MvPolynomial.gradedAlgebra
  have he (r : MvPolynomial σ K) (j : ℕ) :
      (DirectSum.decompose (homogeneousSubmodule σ K) r j : MvPolynomial σ K) =
        homogeneousComponent j r := MvPolynomial.decomposition.decompose'_apply r j
  rw [← he,DirectSum.decompose_mul,DirectSum.coe_mul_apply_eq_sum_antidiagonal]
  apply Finset.sum_congr rfl
  intro ij _
  rw [he,he]

/-- Only the three low-degree pairs contribute to degree two. -/
theorem homogeneousComponent_two_product (p q : MvPolynomial σ K) :
    homogeneousComponent 2 (p*q) =
      homogeneousComponent 0 p * homogeneousComponent 2 q +
      homogeneousComponent 1 p * homogeneousComponent 1 q +
      homogeneousComponent 2 p * homogeneousComponent 0 q := by
  rw [homogeneousComponent_product]
  have ha : Finset.antidiagonal 2 = {(0,2),(1,1),(2,0)} := by decide
  rw [ha]
  simp [Finset.sum_insert, add_assoc]

/-- A polynomial with no components of degrees zero, one, or two remains
invisible in degree two after multiplication by every polynomial. -/
theorem high_degree_invisible (p q : MvPolynomial σ K)
    (h0 : homogeneousComponent 0 p = 0) (h1 : homogeneousComponent 1 p = 0)
    (h2 : homogeneousComponent 2 p = 0) : homogeneousComponent 2 (p*q) = 0 := by
  rw [homogeneousComponent_two_product,h0,h1,h2]
  simp

/-- Multiplying a homogeneous quadratic changes its degree-two component only
by the constant coefficient of the multiplier. -/
theorem homogeneous_quadratic_product (p q : MvPolynomial σ K) (hp : p.IsHomogeneous 2) :
    homogeneousComponent 2 (p*q) = p * C (q.coeff 0) := by
  rw [homogeneousComponent_two_product]
  simp [homogeneousComponent_of_mem hp, homogeneousComponent_zero]

end Froberg
