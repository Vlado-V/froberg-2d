import Froberg.CapacityRatios

/-! # Factorial cancellation in the capacity estimates -/

noncomputable section
namespace Froberg

theorem factorial_pred_real {m : ℕ} (hm : 0 < m) :
    (m.factorial : ℝ) = (m : ℝ) * ((m - 1).factorial : ℝ) := by
  exact_mod_cast (Nat.mul_factorial_pred hm.ne').symm

theorem gamma_four_scalar_ratio {d : ℕ} (hd : 4 ≤ d) :
    higherCountGamma d 4 / scalarCapacity d 4 =
      (2 * (d : ℝ) - 4) / (5 * (d : ℝ)) := by
  have ht := factorial_pred_real (m := 2 * d - 4) (by omega)
  have hs : 2 * d - 4 - 1 = 2 * d - 5 := by omega
  rw [hs, Nat.cast_sub (by omega : 4 ≤ 2 * d), Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_ofNat] at ht
  have hfd : ((d - 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (d - 1)
  have hft : ((2 * d - 5).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * d - 5)
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  norm_num [higherCountGamma, scalarCapacity]
  rw [ht, factorial_pred_real (by omega : 0 < d)]
  field_simp [hfd, hft, hd0] <;> ring

theorem gamma_four_scalar_bound {d : ℕ} (hd : 4 ≤ d) :
    higherCountGamma d 4 / scalarCapacity d 4 < (2 / 5 : ℝ) := by
  rw [gamma_four_scalar_ratio hd]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 5 * (d : ℝ))).mpr
  linarith

theorem factorial_two_pred_real {m : ℕ} (hm : 2 ≤ m) :
    (m.factorial : ℝ) = (m : ℝ) * ((m : ℝ) - 1) * ((m - 2).factorial : ℝ) := by
  rw [factorial_pred_real (by omega : 0 < m),
    factorial_pred_real (by omega : 0 < m - 1)]
  rw [show m - 1 - 1 = m - 2 by omega, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  ring

theorem gamma_six_scalar_ratio {d : ℕ} (hd : 6 ≤ d) :
    higherCountGamma d 6 / scalarCapacity d 6 =
      (2 * (d : ℝ) - 6) * (2 * (d : ℝ) - 7) / (28 * (d : ℝ) * ((d : ℝ) - 1)) := by
  have ht := factorial_two_pred_real (m := 2 * d - 6) (by omega)
  rw [show 2 * d - 6 - 2 = 2 * d - 8 by omega,
    Nat.cast_sub (by omega : 6 ≤ 2 * d), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_ofNat] at ht
  have hfd : ((d - 2).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (d - 2)
  have hft : ((2 * d - 8).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * d - 8)
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (6 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  norm_num [higherCountGamma, scalarCapacity]
  rw [show d - 6 + 4 = d - 2 by omega, show 2 * d - 12 + 4 = 2 * d - 8 by omega,
    ht, factorial_two_pred_real (by omega : 2 ≤ d)]
  field_simp [hfd, hft, hd0, hd1] <;> ring

theorem gamma_six_scalar_bound {d : ℕ} (hd : 6 ≤ d) :
    higherCountGamma d 6 / scalarCapacity d 6 < (1 / 7 : ℝ) := by
  rw [gamma_six_scalar_ratio hd]
  have hdR : (6 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 28 * (d : ℝ) * ((d : ℝ) - 1))).mpr
  nlinarith

end Froberg
