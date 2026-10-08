import Froberg.PolynomialAsymptotics

/-! Polynomial upper bounds for the rounded critical generator counts. -/
noncomputable section
namespace Froberg
open Polynomial

def outerCountBoundPolynomial (P : Polynomial ℝ) (d : ℕ) (h α : ℝ) : Polynomial ℝ :=
  taylor h P - P + C 4 - monomial (d - 2) (α * h ^ 2)

theorem adjustedCritical_degree {d : ℕ} (P : Polynomial ℝ)
    (hP : P.natDegree ≤ d) : (P + C 2).natDegree ≤ d :=
  (natDegree_add_le _ _).trans (max_le hP (by simp))

theorem adjustedCritical_coeff {j : ℕ} (P : Polynomial ℝ) (hj : 0 < j) :
    (P + C 2).coeff j = P.coeff j := by
  simp [coeff_add, coeff_C, hj.ne']

theorem outerCountBound_degree {d : ℕ} (hd : 2 ≤ d) (P : Polynomial ℝ) (h α : ℝ)
    (hP : P.natDegree ≤ d) : (outerCountBoundPolynomial P d h α).natDegree ≤ d - 1 := by
  have hdiff : (taylor h P - P).natDegree ≤ d - 1 :=
    finite_difference_degree P h (d - 1) (by omega)
  have hc : (taylor h P - P + C 4).natDegree ≤ d - 1 :=
    (natDegree_add_le _ _).trans (max_le hdiff (by simp))
  exact (natDegree_sub_le _ _).trans
    (max_le hc ((natDegree_monomial_le _).trans (by omega)))

theorem outerCountBound_top {d : ℕ} (hd : 3 ≤ d) (P : Polynomial ℝ) (h α : ℝ)
    (hP : P.natDegree ≤ d) :
    (outerCountBoundPolynomial P d h α).coeff (d - 1) = (d : ℝ) * h * P.coeff d := by
  have hdiff := finite_difference_top_coefficient P h (d - 1) (by omega)
  have hi : d - 1 + 1 = d := by omega
  have hir : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by exact_mod_cast hi
  rw [hi, hir] at hdiff
  simp only [outerCountBoundPolynomial, coeff_sub, coeff_add, coeff_C, coeff_monomial]
  rw [ite_eq_right (by omega : d - 1 ≠ 0), ite_eq_right (by omega : d - 2 ≠ d - 1),
    add_zero, sub_zero]
  exact hdiff

theorem outerCountBound_second {d : ℕ} (hd : 3 ≤ d) (P : Polynomial ℝ) (h α : ℝ)
    (hP : P.natDegree ≤ d) :
    (outerCountBoundPolynomial P d h α).coeff (d - 2) =
      ((d : ℝ) - 1) * h * P.coeff (d - 1) +
        ((d.choose 2 : ℕ) : ℝ) * h ^ 2 * P.coeff d - α * h ^ 2 := by
  have hdiff := finite_difference_second_coefficient P h (d - 2) (by omega)
  have hi : d - 2 + 2 = d := by omega
  have hj : d - 2 + 1 = d - 1 := by omega
  have hir : ((d - 2 : ℕ) : ℝ) + 1 = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 2 ≤ d)]
    norm_num
    ring
  rw [hi, hj, hir] at hdiff
  simp only [outerCountBoundPolynomial, coeff_sub, coeff_add, coeff_C, coeff_monomial]
  rw [ite_eq_right (by omega : d - 2 ≠ 0), ite_true, add_zero]
  rw [← hdiff]
  rfl

end Froberg
