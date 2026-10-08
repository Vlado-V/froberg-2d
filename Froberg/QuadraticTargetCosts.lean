import Froberg.TargetCosts

/-! # The three quadratic target costs fit the prescribed count -/

noncomputable section
namespace Froberg

def quadraticRowTwoCost (d : ℕ) : ℝ :=
  9 / (32 * ((d - 2).factorial : ℝ) * ((2 * d - 2).choose (d - 2) : ℝ))

def quadraticRowThreeCost (d : ℕ) : ℝ :=
  1 / (6 * ((d - 2).factorial : ℝ) * ((2 * d - 3).choose (d - 2) : ℝ))

theorem quadraticRowTwoCost_pos {d : ℕ} (hd : 3 ≤ d) : 0 < quadraticRowTwoCost d := by
  unfold quadraticRowTwoCost
  have hc : (0 : ℝ) < (2 * d - 2).choose (d - 2) := by
    exact_mod_cast Nat.choose_pos (show d - 2 ≤ 2 * d - 2 by omega)
  positivity

theorem quadraticRowThreeCost_pos {d : ℕ} (hd : 3 ≤ d) : 0 < quadraticRowThreeCost d := by
  unfold quadraticRowThreeCost
  have hc : (0 : ℝ) < (2 * d - 3).choose (d - 2) := by
    exact_mod_cast Nat.choose_pos (show d - 2 ≤ 2 * d - 3 by omega)
  positivity

/-- The row-two convolution cost relative to the quadratic endpoint cost. -/
theorem quadratic_row_two_cost_ratio {d : ℕ} (hd : 3 ≤ d) :
    quadraticRowTwoCost d / countTauFour d =
      9 * (d : ℝ) / (32 * criticalRatio 2 * (2 * (d : ℝ) - 3)) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hρ : criticalRatio 2 ≠ 0 := (criticalRatio_bounds (d := 2) (by omega)).1.ne'
  have h₁ := factorial_two_pred_real (m := d) (by omega)
  have h₂ := factorial_two_pred_real (m := 2 * d - 2) (by omega)
  rw [show 2 * d - 2 - 2 = 2 * d - 4 by omega,
    Nat.cast_sub (by omega : 2 ≤ 2 * d), Nat.cast_mul, Nat.cast_ofNat] at h₂
  rw [show 2 * (d : ℝ) - 2 - 1 = 2 * (d : ℝ) - 3 by ring] at h₂
  unfold quadraticRowTwoCost countTauFour
  rw [choose_real_factorial (show d - 2 ≤ 2 * d - 2 by omega),
    choose_real_factorial (show d - 2 ≤ 2 * d - 4 by omega),
    show 2 * d - 2 - (d - 2) = d by omega,
    show 2 * d - 4 - (d - 2) = d - 2 by omega, h₁, h₂]
  field_simp [factorial_real_ne_zero, hρ, show (d : ℝ) - 1 ≠ 0 by linarith,
    show 2 * (d : ℝ) - 2 ≠ 0 by linarith, show 2 * (d : ℝ) - 3 ≠ 0 by linarith] <;> ring

/-- The row-three convolution cost relative to the quadratic endpoint cost. -/
theorem quadratic_row_three_cost_ratio {d : ℕ} (hd : 3 ≤ d) :
    quadraticRowThreeCost d / countTauFour d =
      ((d : ℝ) - 1) / (3 * criticalRatio 2 * (2 * (d : ℝ) - 3)) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hρ : criticalRatio 2 ≠ 0 := (criticalRatio_bounds (d := 2) (by omega)).1.ne'
  have h₁ := factorial_pred_real (m := d - 1) (by omega)
  rw [show d - 1 - 1 = d - 2 by omega, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one] at h₁
  have h₂ := factorial_pred_real (m := 2 * d - 3) (by omega)
  rw [show 2 * d - 3 - 1 = 2 * d - 4 by omega,
    Nat.cast_sub (by omega : 3 ≤ 2 * d), Nat.cast_mul, Nat.cast_ofNat] at h₂
  unfold quadraticRowThreeCost countTauFour
  rw [choose_real_factorial (show d - 2 ≤ 2 * d - 3 by omega),
    choose_real_factorial (show d - 2 ≤ 2 * d - 4 by omega),
    show 2 * d - 3 - (d - 2) = d - 1 by omega,
    show 2 * d - 4 - (d - 2) = d - 2 by omega, h₁, h₂]
  field_simp [factorial_real_ne_zero, hρ, show 2 * (d : ℝ) - 3 ≠ 0 by linarith] <;> ring

theorem quadratic_row_two_lt_tau {d : ℕ} (hd : 7 ≤ d) :
    quadraticRowTwoCost d < countTauFour d := by
  have hdR : (7 : ℝ) ≤ d := by exact_mod_cast hd
  have hρ := quadratic_critical_ratio_gt
  have hp : 0 < 2 * (d : ℝ) - 3 := by linarith
  have hmul := mul_lt_mul_of_pos_right hρ hp
  have hden : 0 < 32 * criticalRatio 2 * (2 * (d : ℝ) - 3) := by
    have := (criticalRatio_bounds (d := 2) (by omega)).1
    positivity
  have hrat : quadraticRowTwoCost d / countTauFour d < 1 := by
    rw [quadratic_row_two_cost_ratio (by omega)]
    apply (div_lt_one hden).mpr
    nlinarith
  exact (div_lt_one (countTauFour_pos (by omega))).mp hrat

theorem quadratic_row_three_lt_tau {d : ℕ} (hd : 7 ≤ d) :
    quadraticRowThreeCost d < countTauFour d := by
  have hdR : (7 : ℝ) ≤ d := by exact_mod_cast hd
  have hρ := quadratic_critical_ratio_gt
  have hp : 0 < 2 * (d : ℝ) - 3 := by linarith
  have hmul := mul_lt_mul_of_pos_right hρ hp
  have hden : 0 < 3 * criticalRatio 2 * (2 * (d : ℝ) - 3) := by
    have := (criticalRatio_bounds (d := 2) (by omega)).1
    positivity
  have hrat : quadraticRowThreeCost d / countTauFour d < 1 := by
    rw [quadratic_row_three_cost_ratio (by omega)]
    apply (div_lt_one hden).mpr
    nlinarith
  exact (div_lt_one (countTauFour_pos (by omega))).mp hrat

/-- Every quadratic target cost is bounded by the actual chosen density. -/
theorem quadratic_target_costs_le_gamma {d : ℕ} (hd : 3 ≤ d) :
    quadraticRowTwoCost d ≤ countGammaTwo d ∧
      quadraticRowThreeCost d ≤ countGammaTwo d ∧ countTauFour d ≤ countGammaTwo d := by
  refine ⟨?_, ?_, countTauFour_le_gamma d⟩
  · by_cases hd8 : d ≤ 8
    · unfold countGammaTwo
      rw [if_pos hd8]
      exact le_max_left _ _
    · exact (quadratic_row_two_lt_tau (by omega)).le.trans (countTauFour_le_gamma d)
  · by_cases hd8 : d ≤ 8
    · unfold countGammaTwo
      rw [if_pos hd8]
      exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (quadratic_row_three_lt_tau (by omega)).le.trans (countTauFour_le_gamma d)

/-- The chosen enlargement gives a strict margin for all three target constructions. -/
theorem quadratic_target_costs_lt_alpha {d : ℕ} (hd : 3 ≤ d) :
    quadraticRowTwoCost d < countAlpha d ∧
      quadraticRowThreeCost d < countAlpha d ∧ countTauFour d < countAlpha d := by
  have h := quadratic_target_costs_le_gamma hd
  have hp := countTauFour_pos hd
  unfold countAlpha
  constructor
  · linarith [h.1, h.2.2]
  constructor <;> linarith [h.2.1, h.2.2]

end Froberg
