import Froberg.CriticalRatioBounds
import Froberg.PrefixPolynomial

/-! The strict asymptotic numerical surplus used by scalar separation. -/
noncomputable section
namespace Froberg
open Polynomial Filter
open scoped Topology

theorem monomial_count_normalized_tendsto (d : ℕ) :
    Tendsto (fun n : ℕ => ((n + d - 1).choose d : ℝ) / (n : ℝ) ^ d)
      atTop (𝓝 (d.factorial : ℝ)⁻¹) := by
  have hp : monomialCountPolynomial d ≠ 0 := by
    rw [← leadingCoeff_ne_zero, monomialCountPolynomial_leadingCoeff]
    exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero d)
  have hdeg : (monomialCountPolynomial d).degree = (X ^ d : ℝ[X]).degree := by
    rw [degree_eq_natDegree hp, monomialCountPolynomial_natDegree, degree_X_pow]
  have h := ((monomialCountPolynomial d).div_tendsto_atTop_leadingCoeff_div_of_degree_eq
    (X ^ d) hdeg).comp tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, monomialCountPolynomial_eval, eval_pow, eval_X,
    monomialCountPolynomial_leadingCoeff, leadingCoeff_X_pow, div_one] using h

theorem monomial_count_normalized_small_tendsto {e d : ℕ} (hed : e < d) :
    Tendsto (fun n : ℕ => ((n + e - 1).choose e : ℝ) / (n : ℝ) ^ d)
      atTop (𝓝 0) := by
  have hdeg : (monomialCountPolynomial e).degree < (X ^ d : ℝ[X]).degree := by
    apply degree_lt_degree
    simpa only [monomialCountPolynomial_natDegree, natDegree_X_pow] using hed
  have h := ((monomialCountPolynomial e).div_tendsto_atTop_zero_of_degree_lt
    (X ^ d) hdeg).comp tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, monomialCountPolynomial_eval, eval_pow, eval_X] using h

theorem twice_neighbor_choose_le_half_binomial {d : ℕ} (hd : 2 ≤ d) :
    2 * (2 * d - 2).choose d ≤ centralHalfBinomial d := by
  have hp := Nat.choose_succ_succ (2 * d - 2) (d - 2)
  have htop : 2 * d - 2 + 1 = 2 * d - 1 := by omega
  have hbot : d - 2 + 1 = d - 1 := by omega
  simp only [Nat.succ_eq_add_one, htop, hbot] at hp
  have hsym : (2 * d - 2).choose (d - 2) = (2 * d - 2).choose d :=
    Nat.choose_symm_of_eq_add (by omega)
  have hmid := Nat.choose_le_middle d (2 * d - 2)
  have hhalf : (2 * d - 2) / 2 = d - 1 := by omega
  rw [hhalf] at hmid
  unfold centralHalfBinomial
  omega

theorem scalar_separation_leading_gap {d : ℕ} (hd : 2 ≤ d) :
    5 * ((d - 2).factorial : ℝ)⁻¹ * (criticalRatio d / (d.factorial : ℝ)) <
      2 * ((2 * d - 2).factorial : ℝ)⁻¹ := by
  have hr := criticalRatio_bounds hd
  have hc : 2 * ((2 * d - 2).choose d : ℝ) ≤ centralHalfBinomial d := by
    exact_mod_cast twice_neighbor_choose_le_half_binomial hd
  have hcr : 5 * criticalRatio d * ((2 * d - 2).choose d : ℝ) < 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hc hr.1.le]
  have hf : ((2 * d - 2).choose d : ℝ) * (d.factorial : ℝ) * ((d - 2).factorial : ℝ) =
      (2 * d - 2).factorial := by
    exact_mod_cast (show (2 * d - 2).choose d * d.factorial * (d - 2).factorial =
      (2 * d - 2).factorial by
        simpa only [show 2 * d - 2 - d = d - 2 by omega] using
          Nat.choose_mul_factorial_mul_factorial (show d ≤ 2 * d - 2 by omega))
  have hD : (0 : ℝ) < (2 * d - 2).factorial := by exact_mod_cast Nat.factorial_pos _
  have he : (0 : ℝ) < (d - 2).factorial := by exact_mod_cast Nat.factorial_pos _
  have hd' : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos _
  apply (mul_lt_mul_iff_left₀ hD).mp
  have heq : (5 * ((d - 2).factorial : ℝ)⁻¹ * (criticalRatio d / (d.factorial : ℝ))) *
      (2 * d - 2).factorial = 5 * criticalRatio d * ((2 * d - 2).choose d : ℝ) := by
    rw [← hf]
    field_simp
  rw [heq]
  simpa only [mul_assoc, inv_mul_cancel₀ hD.ne', mul_one] using hcr

/-- A family with the stated leading size satisfies the full incidence count
inequality, including the lower-order coefficient-span parameter term. -/
theorem eventually_scalar_incidence_budget {d e : ℕ} (hed : e < d)
    (r : ℕ → ℕ) (c : ℝ)
    (hr : Tendsto (fun n : ℕ => (r n : ℝ) / (n : ℝ) ^ d) atTop (𝓝 c))
    (hgap : 5 * (e.factorial : ℝ)⁻¹ * c < 2 * ((e + d).factorial : ℝ)⁻¹) :
    ∀ᶠ n : ℕ in atTop,
      5 * (n + e - 1).choose e * ((n + e - 1).choose e + r n) ≤
        2 * (n + (e + d) - 1).choose (e + d) := by
  have hleft := ((monomial_count_normalized_tendsto e).const_mul 5).mul
    ((monomial_count_normalized_small_tendsto hed).add hr)
  simp only [zero_add] at hleft
  have hright := (monomial_count_normalized_tendsto (e + d)).const_mul 2
  filter_upwards [hleft.eventually_lt hright hgap, eventually_gt_atTop 0] with n hn hnpos
  have hnp : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hpow : (0 : ℝ) < (n : ℝ) ^ (e + d) := pow_pos hnp _
  have heq :
      5 * (((n + e - 1).choose e : ℝ) / (n : ℝ) ^ e) *
        (((n + e - 1).choose e : ℝ) / (n : ℝ) ^ d + (r n : ℝ) / (n : ℝ) ^ d) =
      (5 * ((n + e - 1).choose e : ℝ) * ((n + e - 1).choose e + r n)) / (n : ℝ) ^ (e + d) := by
    rw [pow_add]
    field_simp
  rw [heq] at hn
  have hrightEq : 2 * (((n + (e + d) - 1).choose (e + d) : ℝ) / (n : ℝ) ^ (e + d)) =
      (2 * ((n + (e + d) - 1).choose (e + d) : ℝ)) / (n : ℝ) ^ (e + d) := by ring
  rw [hrightEq] at hn
  have h := (div_lt_div_iff_of_pos_right hpow).mp hn
  exact_mod_cast h.le

theorem eventually_critical_scalar_incidence_budget {d : ℕ} (hd : 2 ≤ d)
    (r : ℕ → ℕ)
    (hr : Tendsto (fun n : ℕ => (r n : ℝ) / (n : ℝ) ^ d)
      atTop (𝓝 (criticalRatio d / (d.factorial : ℝ)))) :
    ∀ᶠ n : ℕ in atTop,
      5 * (n + (d - 2) - 1).choose (d - 2) * ((n + (d - 2) - 1).choose (d - 2) + r n) ≤
        2 * (n + (2 * d - 2) - 1).choose (2 * d - 2) := by
  simpa only [show d - 2 + d = 2 * d - 2 by omega] using
    eventually_scalar_incidence_budget (show d - 2 < d by omega) r
      (criticalRatio d / (d.factorial : ℝ)) hr (by
        simpa only [show d - 2 + d = 2 * d - 2 by omega] using scalar_separation_leading_gap hd)

end Froberg
