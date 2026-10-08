import Froberg.CapacityRatios

/-! # Binomial bounds for the scalar-source capacities -/

noncomputable section
namespace Froberg

private theorem two_choose_le_next {n k : ℕ} (hk : k ≤ n) (hn : n + 1 ≤ 2 * k) :
    2 * n.choose k ≤ (n + 1).choose k := by
  have h := Nat.choose_mul_succ_eq n k
  have ht : 2 * (n + 1 - k) ≤ n + 1 := by omega
  apply Nat.le_of_mul_le_mul_right (c := n + 1) _ (by omega)
  calc
    2 * n.choose k * (n + 1) = (n + 1).choose k * (2 * (n + 1 - k)) := by nlinarith [h]
    _ ≤ (n + 1).choose k * (n + 1) := Nat.mul_le_mul_left _ ht

theorem scalarCapacityBinomial_eq_choose {d j : ℕ} (hj : j ≤ d) :
    scalarCapacityBinomial d j = (2 * d - j).choose d := by
  unfold scalarCapacityBinomial
  exact Nat.choose_symm_of_eq_add (by omega)

private theorem centralHalfBinomial_eq_choose {d : ℕ} (hd : 0 < d) :
    centralHalfBinomial d = (2 * d - 1).choose d := by
  unfold centralHalfBinomial
  exact Nat.choose_symm_of_eq_add (by omega)

theorem scalarCapacityBinomial_two_le {d : ℕ} (hd : 2 ≤ d) :
    2 * scalarCapacityBinomial d 2 ≤ centralHalfBinomial d := by
  rw [scalarCapacityBinomial_eq_choose hd, centralHalfBinomial_eq_choose (by omega)]
  have h := two_choose_le_next (n := 2 * d - 2) (k := d) (by omega) (by omega)
  simpa only [show 2 * d - 2 + 1 = 2 * d - 1 by omega] using h

theorem scalarCapacityBinomial_eight_le {d j : ℕ} (hj : 4 ≤ j) (hjd : j ≤ d) :
    8 * scalarCapacityBinomial d j ≤ centralHalfBinomial d := by
  rw [scalarCapacityBinomial_eq_choose hjd, centralHalfBinomial_eq_choose (by omega)]
  have h₁ := two_choose_le_next (n := 2 * d - 4) (k := d) (by omega) (by omega)
  have h₂ := two_choose_le_next (n := 2 * d - 3) (k := d) (by omega) (by omega)
  have h₃ := two_choose_le_next (n := 2 * d - 2) (k := d) (by omega) (by omega)
  rw [show 2 * d - 4 + 1 = 2 * d - 3 by omega] at h₁
  rw [show 2 * d - 3 + 1 = 2 * d - 2 by omega] at h₂
  rw [show 2 * d - 2 + 1 = 2 * d - 1 by omega] at h₃
  have hm := Nat.choose_le_choose d (show 2 * d - j ≤ 2 * d - 4 by omega)
  omega

/-- Every higher scalar-source density has the uniform one-eighth margin. -/
theorem higher_scalar_source_bound {d j : ℕ} (hj : 4 ≤ j) (hjd : j ≤ d) :
    (scalarCapacityBinomial d j : ℝ) * criticalRatio d < 1 / 8 := by
  have hρ := criticalRatio_bounds (d := d) (by omega)
  have hH := criticalRatio_sharp_bound (d := d) (by omega)
  have hb : 8 * (scalarCapacityBinomial d j : ℝ) ≤ (centralHalfBinomial d : ℝ) := by
    exact_mod_cast scalarCapacityBinomial_eight_le hj hjd
  have hm := mul_le_mul_of_nonneg_right hb hρ.1.le
  nlinarith

/-- The sharper quadratic margin used in B.8. -/
theorem quadratic_scalar_source_bound {d : ℕ} (hd : 9 ≤ d) :
    (scalarCapacityBinomial d 2 : ℝ) * criticalRatio d < 501 / 2000 := by
  have hρ := criticalRatio_bounds (d := d) (by omega)
  have hH : (1000 : ℝ) * d ≤ centralHalfBinomial d := by
    exact_mod_cast centralHalfBinomial_ge_thousand_mul hd
  have hdR : (9 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : (0 : ℝ) < centralHalfBinomial d := by nlinarith
  have hr := mul_lt_mul_of_pos_left (criticalRatio_rational_upper (d := d) (by omega)) hp
  have hb : (centralHalfBinomial d : ℝ) / (2 * (centralHalfBinomial d : ℝ) - 1) < 501 / 1000 := by
    apply (div_lt_iff₀ (by nlinarith : 0 < 2 * (centralHalfBinomial d : ℝ) - 1)).mpr
    nlinarith
  have hr' : (centralHalfBinomial d : ℝ) * criticalRatio d < 501 / 1000 := by
    have hr₁ : (centralHalfBinomial d : ℝ) * criticalRatio d <
        (centralHalfBinomial d : ℝ) / (2 * (centralHalfBinomial d : ℝ) - 1) := by
      simpa only [mul_one_div] using hr
    exact hr₁.trans hb
  have hB : 2 * (scalarCapacityBinomial d 2 : ℝ) ≤ (centralHalfBinomial d : ℝ) := by
    exact_mod_cast scalarCapacityBinomial_two_le (d := d) (by omega)
  have hm := mul_le_mul_of_nonneg_right hB hρ.1.le
  nlinarith

end Froberg
