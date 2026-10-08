import Froberg.CapacityFactors
import Froberg.CapacityQuadratic

/-! # Exact factorial expressions for the product capacities -/

noncomputable section
namespace Froberg

theorem choose_real_factorial {n k : ℕ} (hk : k ≤ n) :
    (n.choose k : ℝ) = (n.factorial : ℝ) /
      ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) := by
  apply (eq_div_iff (mul_ne_zero (factorial_real_ne_zero _) (factorial_real_ne_zero _))).mpr
  have h : (n.choose k : ℝ) * (k.factorial : ℝ) * ((n - k).factorial : ℝ) =
      (n.factorial : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  simpa only [mul_assoc] using h

theorem tauFour_product_ratio {d : ℕ} (hd : 2 ≤ d) :
    countTauFour d / productCapacity d 2 =
      criticalRatio 2 * (2 : ℝ) ^ (d + 1) / ((2 * d - 4).choose (d - 2) : ℝ) := by
  have hc : ((2 * d - 4).choose (d - 2) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show d - 2 ≤ 2 * d - 4 by omega)).ne'
  norm_num [countTauFour, productCapacity]
  field_simp [factorial_real_ne_zero, hc] <;> ring

theorem fourth_product_ratio {d : ℕ} (hd : 4 ≤ d) :
    scalarCapacity d 4 / productCapacity d 4 =
      (2 : ℝ) ^ (d + 1) / (scalarCapacityBinomial d 4 : ℝ) := by
  unfold scalarCapacityBinomial
  rw [choose_real_factorial (show d - 4 ≤ 2 * d - 4 by omega),
    show 2 * d - 4 - (d - 4) = d by omega]
  norm_num [scalarCapacity, productCapacity]
  field_simp [factorial_real_ne_zero] <;> ring

theorem higher_product_ratio {d j : ℕ} (hj : 6 ≤ j) (hjd : j ≤ d) :
    higherCountGamma d j / productCapacity d j =
      (2 : ℝ) ^ (d + 1) /
        (((2 * j - 4).choose j : ℝ) * ((2 * (d - j) + 4).choose (d - j) : ℝ)) := by
  rw [choose_real_factorial (show j ≤ 2 * j - 4 by omega),
    choose_real_factorial (show d - j ≤ 2 * (d - j) + 4 by omega)]
  rw [show 2 * j - 4 - j = j - 4 by omega,
    show 2 * (d - j) + 4 - (d - j) = d - j + 4 by omega]
  simp only [higherCountGamma, if_neg (by omega : j ≠ 4), productCapacity]
  rw [show 2 * d - 2 * j + 4 = 2 * (d - j) + 4 by omega]
  field_simp [factorial_real_ne_zero] <;> ring

end Froberg
