module

public import Froberg.CapacityFactorials

@[expose] public section

/-! # The quadratic scalar-capacity ratio -/

noncomputable section
namespace Froberg

theorem tauFour_scalar_ratio {d : ℕ} (hd : 3 ≤ d) :
    countTauFour d / scalarCapacity d 2 =
      2 * criticalRatio 2 * (2 * (d : ℝ) - 3) / (d : ℝ) := by
  have hf : ((d - 2).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (d - 2)
  have hF : ((2 * d - 4).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * d - 4)
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hcN := Nat.choose_mul_factorial_mul_factorial (show d - 2 ≤ 2 * d - 4 by omega)
  rw [show 2 * d - 4 - (d - 2) = d - 2 by omega] at hcN
  have hc : ((2 * d - 4).choose (d - 2) : ℝ) * ((d - 2).factorial : ℝ) *
      ((d - 2).factorial : ℝ) = ((2 * d - 4).factorial : ℝ) := by exact_mod_cast hcN
  have hc' : ((2 * d - 4).choose (d - 2) : ℝ) =
      ((2 * d - 4).factorial : ℝ) / (((d - 2).factorial : ℝ) * ((d - 2).factorial : ℝ)) := by
    apply (eq_div_iff (mul_ne_zero hf hf)).mpr
    simpa only [mul_assoc] using hc
  have ht := factorial_two_pred_real (m := 2 * d - 2) (by omega)
  rw [show 2 * d - 2 - 2 = 2 * d - 4 by omega,
    Nat.cast_sub (by omega : 2 ≤ 2 * d), Nat.cast_mul, Nat.cast_ofNat] at ht
  norm_num [countTauFour, scalarCapacity]
  rw [hc', ht, factorial_two_pred_real (by omega : 2 ≤ d)]
  field_simp [hf, hF, hd0, hd1] <;> ring

theorem quadratic_scalar_density_bound {d : ℕ} (hd : 9 ≤ d) :
    countGammaTwo d / scalarCapacity d 2 < (92 / 125 : ℝ) := by
  have he : countGammaTwo d = countTauFour d := by
    simp only [countGammaTwo, if_neg (by omega : ¬d ≤ 8)]
  rw [he, tauFour_scalar_ratio (by omega)]
  have hρ := (criticalRatio_bounds (d := 2) (by omega)).1
  have hu := quadratic_critical_ratio_lt
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hh : 2 * criticalRatio 2 * (2 * (d : ℝ) - 3) / (d : ℝ) < 4 * criticalRatio 2 := by
    apply (div_lt_iff₀ hd0).mpr
    nlinarith
  linarith

end Froberg
