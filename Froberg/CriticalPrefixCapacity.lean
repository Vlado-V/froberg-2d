module

public import Froberg.ScalarSeparationAsymptotic
public import Froberg.AsymptoticCounts

@[expose] public section

/-! Any scalar family of critical leading size, including all prepared
scalar shifts, fits the last strict-prefix multiplication budget. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem critical_prefix_leading_gap {d : ℕ} (hd : 2 ≤ d) :
    (criticalRatio d/(d.factorial : ℝ))*((d-1).factorial : ℝ)⁻¹ <
      ((d+(d-1)).factorial : ℝ)⁻¹ := by
  have hc : criticalRatio d*(centralHalfBinomial d : ℝ) < 1 := by
    have hh := (criticalRatio_bounds hd).2.2.2
    nlinarith
  have hfact : (centralHalfBinomial d : ℝ)*(d.factorial : ℝ)*((d-1).factorial : ℝ)=
      (d+(d-1)).factorial := by
    have hn := Nat.choose_mul_factorial_mul_factorial (show d-1 ≤ d+(d-1) by omega)
    have he : d+(d-1)-(d-1)=d := by omega
    rw [he] at hn
    exact_mod_cast (by simpa only [centralHalfBinomial,show 2*d-1=d+(d-1) by omega,
      Nat.mul_right_comm] using hn)
  have hdne : (d.factorial : ℝ) ≠ 0 := by positivity
  have hene : ((d-1).factorial : ℝ) ≠ 0 := by positivity
  have hcn : (centralHalfBinomial d : ℝ) ≠ 0 := by
    have hh := centralHalfBinomial_ge_two hd
    exact_mod_cast (show centralHalfBinomial d ≠ 0 by omega)
  have heq : (criticalRatio d/(d.factorial : ℝ))*((d-1).factorial : ℝ)⁻¹=
      (criticalRatio d*(centralHalfBinomial d : ℝ))/((d+(d-1)).factorial : ℝ) := by
    rw [←hfact]
    field_simp
  rw [heq,inv_eq_one_div]
  exact div_lt_div_of_pos_right hc (by positivity)

theorem eventually_critical_prefix_capacity {d : ℕ} (hd : 2 ≤ d)
    (r : ℕ → ℕ)
    (hr : Tendsto (fun n : ℕ => (r n : ℝ)/(n : ℝ)^d) atTop
      (𝓝 (criticalRatio d/(d.factorial : ℝ)))) :
    ∀ᶠ n : ℕ in atTop,
      r n*(n+(d-1)-1).choose (d-1) ≤ (n+(d+(d-1))-1).choose (d+(d-1)) := by
  have hl := hr.mul (monomial_count_normalized_tendsto (d-1))
  have hleft : Tendsto (fun n : ℕ =>
      ((r n*(n+(d-1)-1).choose (d-1) : ℕ) : ℝ)/(n : ℝ)^(d+(d-1))) atTop
      (𝓝 ((criticalRatio d/(d.factorial : ℝ))*((d-1).factorial : ℝ)⁻¹)) := by
    simpa only [Nat.cast_mul,div_mul_div_comm,←pow_add] using hl
  filter_upwards [eventually_lt_of_normalized_limits _ _ _ _ _ hleft
    (monomial_count_normalized_tendsto (d+(d-1))) (critical_prefix_leading_gap hd)] with n hn
  exact_mod_cast hn.le

end Froberg
