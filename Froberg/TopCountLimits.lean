module

public import Froberg.CapacityFactors
public import Froberg.ScalarSeparationAsymptotic

@[expose] public section

/-! # Exact tail and quotient counts in the projected top degree -/

noncomputable section
namespace Froberg
open Filter
open scoped Topology

/-- Degree-`d-1` source dimension in the `h` outer variables. -/
def topSourceCount (d h : ℕ) : ℕ := (h + (d - 1) - 1).choose (d - 1)

/-- The dimension left after removing the prescribed pure family. -/
def topComplementCount (d h : ℕ) : ℕ :=
  (h + d - 1).choose d - tailGeneratorCount d h

def topComplementDensity (d : ℕ) : ℝ :=
  (d.factorial : ℝ)⁻¹ - 2 / ((d + 1).factorial : ℝ)

theorem topComplementDensity_eq (d : ℕ) :
    topComplementDensity d = ((d : ℝ) - 1) /
      (((d : ℝ) + 1) * (d.factorial : ℝ)) := by
  unfold topComplementDensity
  rw [factorial_add_one_real]
  field_simp [factorial_real_ne_zero]
  ring

theorem topComplementDensity_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < topComplementDensity d := by
  rw [topComplementDensity_eq]
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact div_pos (by linarith) (by positivity)

theorem odd_tail_normalized_limit {d : ℕ} (hd : 0 < d) (ho : Odd d) :
    Tendsto (fun h : ℕ => (tailGeneratorCount d h : ℝ) / (h : ℝ) ^ d)
      atTop (𝓝 (2 / ((d + 1).factorial : ℝ))) := by
  simp only [tailGeneratorCount, if_pos ho]
  apply ceil_normalized_limit _ hd _ (Eventually.of_forall fun h => by positivity)
  convert scaled_power_normalized_limit (2 / ((d + 1).factorial : ℝ)) d using 1 <;>
    ext h <;> ring

/-- The natural subtraction in the quotient count is eventually exact. -/
theorem odd_top_count_budget_limit {d : ℕ} (hd : 3 ≤ d) (ho : Odd d) :
    (∀ᶠ h : ℕ in atTop, tailGeneratorCount d h ≤ (h + d - 1).choose d) ∧
    Tendsto (fun h : ℕ => (topComplementCount d h : ℝ) / (h : ℝ) ^ d)
      atTop (𝓝 (topComplementDensity d)) := by
  have hlim : Tendsto (fun h : ℕ =>
      (((h + d - 1).choose d : ℝ) - tailGeneratorCount d h) / (h : ℝ) ^ d)
      atTop (𝓝 (topComplementDensity d)) := by
    simpa only [topComplementDensity, sub_div] using
      (monomial_count_normalized_tendsto d).sub (odd_tail_normalized_limit (by omega) ho)
  have h := natural_budget_limit (fun h => (h + d - 1).choose d)
    (tailGeneratorCount d) (fun _ => 0) (by omega : 0 < d)
    (topComplementDensity d) (topComplementDensity_pos (by omega)) hlim (by simp)
  simpa only [Nat.add_zero, Nat.sub_zero, topComplementCount] using h

theorem topSourceCount_pos {d h : ℕ} (hh : 0 < h) : 0 < topSourceCount d h := by
  unfold topSourceCount
  exact Nat.choose_pos (by omega)

/-- Multiplication by `h` puts the source dimension on the same scale as the target. -/
theorem top_source_times_dimension_limit {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (fun h : ℕ => (topSourceCount d h : ℝ) * h / (h : ℝ) ^ d)
      atTop (𝓝 ((d - 1).factorial : ℝ)⁻¹) := by
  apply (monomial_count_normalized_tendsto (d - 1)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with h hh
  have hne : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hp : (h : ℝ) ^ d = (h : ℝ) ^ (d - 1) * h := by
    conv_lhs => rw [← Nat.sub_add_cancel hd, pow_succ]
  dsimp [topSourceCount]
  rw [hp]
  field_simp

/-- The limiting projected multiplication ratio displayed in C.8. -/
theorem odd_top_complement_ratio_limit {d : ℕ} (hd : 3 ≤ d) (ho : Odd d) :
    Tendsto (fun h : ℕ => (topComplementCount d h : ℝ) /
      ((topSourceCount d h : ℝ) * h)) atTop
      (𝓝 (((d : ℝ) - 1) / ((d : ℝ) * ((d : ℝ) + 1)))) := by
  have h := (odd_top_count_budget_limit hd ho).2.div
    (top_source_times_dimension_limit (by omega : 1 ≤ d))
    (inv_ne_zero (factorial_real_ne_zero _))
  have hc : topComplementDensity d / ((d - 1).factorial : ℝ)⁻¹ =
      ((d : ℝ) - 1) / ((d : ℝ) * ((d : ℝ) + 1)) := by
    rw [topComplementDensity_eq, factorial_pred_real (by omega : 0 < d)]
    field_simp [factorial_real_ne_zero]
  rw [hc] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact div_div_div_cancel_right₀ (pow_ne_zero d (by exact_mod_cast hn.ne')) _ _

/-- The normalized incidence surplus `ub/(a²h²)` has a strictly positive limit. -/
theorem odd_top_incidence_ratio_limit {d : ℕ} (hd : 3 ≤ d) (ho : Odd d) :
    Tendsto (fun h : ℕ => (tailGeneratorCount d h : ℝ) * topComplementCount d h /
      ((topSourceCount d h : ℝ) ^ 2 * (h : ℝ) ^ 2)) atTop
      (𝓝 (2 * ((d : ℝ) - 1) / ((d : ℝ) ^ 2 * ((d : ℝ) + 1) ^ 2))) := by
  have h := ((odd_tail_normalized_limit (by omega : 0 < d) ho).mul
    (odd_top_count_budget_limit hd ho).2).div
      ((top_source_times_dimension_limit (by omega : 1 ≤ d)).pow 2)
      (pow_ne_zero 2 (inv_ne_zero (factorial_real_ne_zero _)))
  have hc : (2 / ((d + 1).factorial : ℝ)) * topComplementDensity d /
      (((d - 1).factorial : ℝ)⁻¹) ^ 2 =
      2 * ((d : ℝ) - 1) / ((d : ℝ) ^ 2 * ((d : ℝ) + 1) ^ 2) := by
    rw [topComplementDensity_eq, factorial_add_one_real,
      factorial_pred_real (by omega : 0 < d)]
    field_simp [factorial_real_ne_zero]
  rw [hc] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have haR : (topSourceCount d n : ℝ) ≠ 0 := by
    exact_mod_cast (topSourceCount_pos hn).ne'
  dsimp only [Pi.div_apply, Pi.mul_apply, Pi.pow_apply]
  field_simp

end Froberg
