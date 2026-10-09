module

public import Froberg.SlackMargins
public import Froberg.CriticalLimits

@[expose] public section

/-! Cancellation of the leading term and strict asymptotic positivity of
the polynomial lower bound for the dimension margin. -/
noncomputable section
namespace Froberg
open Polynomial Filter
open scoped Topology

theorem inverse_factorial_step {d : ℕ} (hd : 0 < d) :
    (((d - 1).factorial : ℝ))⁻¹ = (d : ℝ) * ((d.factorial : ℝ))⁻¹ := by
  have hnat : d.factorial = d * (d - 1).factorial := by
    simpa only [Nat.sub_add_cancel hd] using Nat.factorial_succ (d - 1)
  have hreal : (d.factorial : ℝ) = (d : ℝ) * ((d - 1).factorial : ℝ) := by exact_mod_cast hnat
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [hreal, mul_inv_rev]
  field_simp

theorem critical_leading_equation {d : ℕ} (hd : 2 ≤ d) :
    (criticalRatio d / (d.factorial : ℝ)) ^ 2 -
      2 * (d.factorial : ℝ)⁻¹ * (criticalRatio d / (d.factorial : ℝ)) +
      2 * ((2 * d).factorial : ℝ)⁻¹ = 0 := by
  have hh : (centralHalfBinomial d : ℝ) ≠ 0 := by
    have : 2 ≤ centralHalfBinomial d := centralHalfBinomial_ge_two hd
    exact_mod_cast (show centralHalfBinomial d ≠ 0 by omega)
  have hf : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  rw [factorial_twice_degree (by omega : 0 < d)]
  push_cast
  field_simp
  have hid := criticalRatio_identity hd
  nlinarith

theorem adjusted_slack_top_zero {d : ℕ} (hd : 3 ≤ d)
    (P : Polynomial ℝ) (h α : ℝ) (hP : P.natDegree ≤ d)
    (hL : P.coeff d = criticalRatio d / (d.factorial : ℝ)) :
    (transferSlackPolynomial d (P + C 2) (outerCountBoundPolynomial P d h α) h).coeff
      (2 * d - 1) = 0 := by
  rw [transferSlackPolynomial_top (by omega) _ _ _ (adjustedCritical_degree P hP)
    (outerCountBound_degree (by omega) P h α hP),
    adjustedCritical_coeff P (by omega : 0 < d), outerCountBound_top hd P h α hP, hL]
  simp only [div_eq_mul_inv]
  rw [inverse_factorial_step (show 0 < 2 * d by omega),
    inverse_factorial_step (show 0 < d by omega)]
  push_cast
  linear_combination h * (d : ℝ) * critical_leading_equation (by omega : 2 ≤ d)

theorem adjusted_slack_degree {d : ℕ} (hd : 3 ≤ d)
    (P : Polynomial ℝ) (h α : ℝ) (hP : P.natDegree ≤ d)
    (hL : P.coeff d = criticalRatio d / (d.factorial : ℝ)) :
    (transferSlackPolynomial d (P + C 2) (outerCountBoundPolynomial P d h α) h).natDegree ≤
      2 * d - 2 := by
  have hb := transferSlackPolynomial_degree (by omega : 1 ≤ d) (P + C 2)
    (outerCountBoundPolynomial P d h α) h (adjustedCritical_degree P hP)
    (outerCountBound_degree (by omega) P h α hP)
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  by_cases heq : j = 2 * d - 1
  · subst j
    exact adjusted_slack_top_zero hd P h α hP hL
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem polynomial_positive_lower_bound (P : Polynomial ℝ) (k : ℕ)
    (hP : P.natDegree ≤ k) (hc : 0 < P.coeff k) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, δ * (n : ℝ) ^ k < P.eval (n : ℝ) := by
  refine ⟨P.coeff k / 2, by linarith, ?_⟩
  have hlim := polynomial_div_pow_nat_tendsto P k hP
  have hg := hlim.eventually (lt_mem_nhds (show P.coeff k / 2 < P.coeff k by linarith))
  filter_upwards [hg, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  exact (lt_div_iff₀ (pow_pos (by exact_mod_cast hn0 : (0 : ℝ) < n) k)).mp hn

theorem adjusted_slack_eventually_positive {d : ℕ} (hd : 3 ≤ d)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (hL : P.coeff d = criticalRatio d / (d.factorial : ℝ)) :
    ∃ H : ℕ, ∀ h : ℕ, H ≤ h → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ n : ℕ in atTop, δ * (n : ℝ) ^ (2 * d - 2) <
        (transferSlackPolynomial d (P + C 2)
          (outerCountBoundPolynomial P d h (countAlpha d)) h).eval (n : ℝ) := by
  obtain ⟨H, hH⟩ := adjusted_slack_second_eventually_pos hd P hP hL
  exact ⟨H, fun h hh => polynomial_positive_lower_bound _ _
    (adjusted_slack_degree hd P h (countAlpha d) hP hL) (hH h hh)⟩

end Froberg
