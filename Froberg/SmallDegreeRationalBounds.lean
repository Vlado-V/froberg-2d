import Froberg.CapacityRatios

/-! # Exact rational enclosures for the small-degree parameters -/

noncomputable section
namespace Froberg

/-- Rational endpoints are certified by the defining quadratic identity. -/
theorem criticalRatio_between_of_squares {d : ℕ} (hd : 2 ≤ d) (a b : ℝ)
    (ha : a ≤ 1) (hb : b ≤ 1)
    (hl : (centralHalfBinomial d : ℝ) - 1 < (centralHalfBinomial d : ℝ) * (1 - a) ^ 2)
    (hu : (centralHalfBinomial d : ℝ) * (1 - b) ^ 2 < (centralHalfBinomial d : ℝ) - 1) :
    a < criticalRatio d ∧ criticalRatio d < b := by
  have hH : (0 : ℝ) < centralHalfBinomial d := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (centralHalfBinomial_ge_two hd))
  have hρ := criticalRatio_bounds hd
  have hi := criticalRatio_identity hd
  have hid : (centralHalfBinomial d : ℝ) * (1 - criticalRatio d) ^ 2 =
      (centralHalfBinomial d : ℝ) - 1 := by nlinarith
  constructor
  · by_contra h
    have hs := mul_self_le_mul_self (by linarith : 0 ≤ 1 - a)
      (by linarith : 1 - a ≤ 1 - criticalRatio d)
    have hm := mul_le_mul_of_nonneg_left hs hH.le
    nlinarith
  · by_contra h
    have hs := mul_self_le_mul_self (by linarith : 0 ≤ 1 - criticalRatio d)
      (by linarith : 1 - criticalRatio d ≤ 1 - b)
    have hm := mul_le_mul_of_nonneg_left hs hH.le
    nlinarith

def smallCriticalNumerator (d : ℕ) : ℕ :=
  match d with
  | 2 => 18350341
  | 3 => 5131670
  | 4 => 1438923
  | 5 => 397615
  | 6 => 108283
  | 7 => 29141
  | 8 => 7770
  | _ => 0

def smallCriticalLower (d : ℕ) : ℝ := (smallCriticalNumerator d : ℝ) / 100000000
def smallCriticalUpper (d : ℕ) : ℝ := ((smallCriticalNumerator d : ℝ) + 1) / 100000000

theorem smallCritical_bounds {d : ℕ} (hd : 2 ≤ d) (hd8 : d ≤ 8) :
    smallCriticalLower d < criticalRatio d ∧ criticalRatio d < smallCriticalUpper d := by
  apply criticalRatio_between_of_squares hd
  all_goals interval_cases d <;>
    norm_num [smallCriticalLower, smallCriticalUpper, smallCriticalNumerator,
      centralHalfBinomial, Nat.choose_eq_factorial_div_factorial]

/-- Replacing the quadratic critical ratio by its rational upper endpoint. -/
def smallBetaBound (d : ℕ) : ℝ := (1011 / 1000) * max
  (9 / (32 * ((d - 2).factorial : ℝ) * ((2 * d - 2).choose (d - 2) : ℝ)))
  (max (1 / (6 * ((d - 2).factorial : ℝ) * ((2 * d - 3).choose (d - 2) : ℝ)))
    (smallCriticalUpper 2 /
      (2 * ((d - 2).factorial : ℝ) * ((2 * d - 4).choose (d - 2) : ℝ))))

def smallRateBound (d : ℕ) : ℝ := (11 / 10) * 2 ^ d * smallCriticalUpper d

theorem countBeta_le_smallBetaBound {d : ℕ} (hd : 3 ≤ d) (hd8 : d ≤ 8) :
    countBeta d ≤ smallBetaBound d := by
  unfold countBeta countGammaTwo smallBetaBound countTauFour
  rw [if_pos hd8]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply max_le_max le_rfl
  apply max_le_max le_rfl
  apply div_le_div_of_nonneg_right (smallCritical_bounds (d := 2) (by omega) (by omega)).2.le
  positivity

theorem outerColumnRate_lt_smallRateBound {d : ℕ} (hd : 3 ≤ d) (hd8 : d ≤ 8) :
    outerColumnRate d < smallRateBound d := by
  exact mul_lt_mul_of_pos_left (smallCritical_bounds (by omega) hd8).2 (by positivity)

theorem smallRateBound_nonneg (d : ℕ) : 0 ≤ smallRateBound d := by
  unfold smallRateBound smallCriticalUpper
  positivity

end Froberg
