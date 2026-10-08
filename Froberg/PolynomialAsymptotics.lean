import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Tactic

/-! Exact top coefficients of finite differences, and normalized limits.
These supply the asymptotic estimates used in the integer count selection. -/
noncomputable section
namespace Froberg
open Polynomial Filter
open scoped Topology

theorem polynomial_div_pow_tendsto (P : Polynomial ℝ) (k : ℕ)
    (hP : P.natDegree ≤ k) :
    Tendsto (fun x : ℝ => P.eval x / x ^ k) atTop (𝓝 (P.coeff k)) := by
  by_cases hz : P = 0
  · simp [hz]
  by_cases heq : P.natDegree = k
  · have hdegree : P.degree = (X ^ k : Polynomial ℝ).degree := by
      rw [degree_eq_natDegree hz, heq]
      simp
    have h := P.div_tendsto_atTop_leadingCoeff_div_of_degree_eq (X ^ k) hdegree
    simpa [← heq] using h
  · have hlt : P.natDegree < k := lt_of_le_of_ne hP heq
    have hdegree : P.degree < (X ^ k : Polynomial ℝ).degree := by
      rw [degree_eq_natDegree hz]
      simpa using hlt
    have h := P.div_tendsto_atTop_zero_of_degree_lt (X ^ k) hdegree
    simpa [coeff_eq_zero_of_natDegree_lt hlt] using h

theorem polynomial_div_pow_nat_tendsto (P : Polynomial ℝ) (k : ℕ)
    (hP : P.natDegree ≤ k) :
    Tendsto (fun n : ℕ => P.eval (n : ℝ) / (n : ℝ) ^ k)
      atTop (𝓝 (P.coeff k)) :=
  (polynomial_div_pow_tendsto P k hP).comp tendsto_natCast_atTop_atTop

theorem taylor_coefficient_near_top (P : Polynomial ℝ) (h : ℝ) (k s : ℕ)
    (hP : P.natDegree ≤ k + s) :
    (taylor h P).coeff k = ∑ i ∈ Finset.range (s + 1),
      ((i + k).choose k : ℝ) * P.coeff (i + k) * h ^ i := by
  rw [taylor_coeff]
  have hb : (hasseDeriv k P).natDegree < s + 1 := by
    rw [natDegree_hasseDeriv]
    omega
  rw [eval_eq_sum_range' hb]
  simp only [hasseDeriv_coeff]

theorem taylor_coefficient_at_bound (P : Polynomial ℝ) (h : ℝ) (k : ℕ)
    (hP : P.natDegree ≤ k) : (taylor h P).coeff k = P.coeff k := by
  simpa using taylor_coefficient_near_top P h k 0 (by simpa using hP)

theorem finite_difference_degree (P : Polynomial ℝ) (h : ℝ) (k : ℕ)
    (hP : P.natDegree ≤ k + 1) : (taylor h P - P).natDegree ≤ k := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [coeff_sub]
  by_cases heq : j = k + 1
  · subst j
    rw [taylor_coefficient_at_bound P h _ hP, sub_self]
  · have hlt : P.natDegree < j := by omega
    rw [coeff_eq_zero_of_natDegree_lt (by simpa using hlt),
      coeff_eq_zero_of_natDegree_lt hlt, sub_self]

theorem finite_difference_top_coefficient (P : Polynomial ℝ) (h : ℝ) (k : ℕ)
    (hP : P.natDegree ≤ k + 1) :
    (taylor h P - P).coeff k = (k + 1 : ℝ) * h * P.coeff (k + 1) := by
  rw [coeff_sub, taylor_coefficient_near_top P h k 1 hP]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.choose_self, Nat.cast_one, one_mul, pow_zero, mul_one, pow_one]
  rw [Nat.add_comm 1 k, Nat.choose_succ_self_right]
  push_cast
  ring

theorem finite_difference_second_coefficient (P : Polynomial ℝ) (h : ℝ) (k : ℕ)
    (hP : P.natDegree ≤ k + 2) :
    (taylor h P - P).coeff k =
      (k + 1 : ℝ) * h * P.coeff (k + 1) +
        ((k + 2).choose 2 : ℝ) * h ^ 2 * P.coeff (k + 2) := by
  rw [coeff_sub, taylor_coefficient_near_top P h k 2 hP]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.choose_self, Nat.cast_one, one_mul, pow_zero, mul_one, pow_one]
  rw [Nat.add_comm 1 k, Nat.add_comm 2 k, Nat.choose_succ_self_right,
    Nat.choose_symm_of_eq_add (show k + 2 = 2 + k by omega)]
  push_cast
  ring

theorem finite_difference_normalized_limit (P : Polynomial ℝ) (h : ℝ) (k : ℕ)
    (hP : P.natDegree ≤ k + 1) :
    Tendsto (fun n : ℕ => (P.eval ((n : ℝ) + h) - P.eval (n : ℝ)) / (n : ℝ) ^ k)
      atTop (𝓝 ((k + 1 : ℝ) * h * P.coeff (k + 1))) := by
  have hlim := polynomial_div_pow_nat_tendsto (taylor h P - P) k
    (finite_difference_degree P h k hP)
  simpa only [eval_sub, taylor_eval, finite_difference_top_coefficient P h k hP] using hlim

theorem subtract_top_degree (P : Polynomial ℝ) (k : ℕ)
    (hP : P.natDegree ≤ k + 1) :
    (P - monomial (k + 1) (P.coeff (k + 1))).natDegree ≤ k := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [coeff_sub, coeff_monomial]
  by_cases heq : k + 1 = j
  · subst j
    simp
  · simp only [heq, ite_false, sub_zero]
    exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem polynomial_two_term_limit (P : Polynomial ℝ) (k : ℕ)
    (hP : P.natDegree ≤ k + 1) :
    Tendsto (fun n : ℕ =>
      (P.eval (n : ℝ) - P.coeff (k + 1) * (n : ℝ) ^ (k + 1)) / (n : ℝ) ^ k)
      atTop (𝓝 (P.coeff k)) := by
  have hlim := polynomial_div_pow_nat_tendsto
    (P - monomial (k + 1) (P.coeff (k + 1))) k (subtract_top_degree P k hP)
  simpa [coeff_monomial, eval_monomial] using hlim

end Froberg
