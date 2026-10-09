module

public import Froberg.CapacityRatios

@[expose] public section

/-! # Elementary exponential bounds in the large-degree capacity estimates -/

namespace Froberg

theorem capacity_quadratic_power_nat {d : ℕ} (hd : 13 ≤ d) :
    10240 * (d + 1) ^ 2 ≤ 245 * 2 ^ d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ d hd ih =>
      have hs : (d + 1 + 1) ^ 2 ≤ 2 * (d + 1) ^ 2 := by
        have hh := Nat.mul_le_mul (show 2 ≤ d by omega) (show 2 ≤ d by omega)
        nlinarith
      rw [show (2 : ℕ) ^ (d + 1) = 2 ^ d * 2 from pow_succ _ _]
      nlinarith [Nat.mul_le_mul_left 10240 hs]

theorem capacity_linear_power_nat {d : ℕ} (hd : 13 ≤ d) :
    8192 * (2 * d - 3) ≤ 23 * 2 ^ d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ d hd ih =>
      have hs : 2 * (d + 1) - 3 ≤ 2 * (2 * d - 3) := by omega
      rw [show (2 : ℕ) ^ (d + 1) = 2 ^ d * 2 from pow_succ _ _]
      nlinarith [Nat.mul_le_mul_left 8192 hs]

theorem capacity_quadratic_power_bound {d : ℕ} (hd : 13 ≤ d) :
    10 * ((d : ℝ) + 1) ^ 2 / (2 : ℝ) ^ d ≤ 245 / 1024 := by
  have h : (10240 : ℝ) * ((d : ℝ) + 1) ^ 2 ≤ 245 * (2 : ℝ) ^ d := by
    exact_mod_cast capacity_quadratic_power_nat hd
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ d)).mpr
  linarith

theorem capacity_linear_power_bound {d : ℕ} (hd : 13 ≤ d) :
    64 * (2 * (d : ℝ) - 3) / (2 : ℝ) ^ d ≤ 23 / 128 := by
  have h : (8192 : ℝ) * ((2 * d - 3 : ℕ) : ℝ) ≤ 23 * (2 : ℝ) ^ d := by
    exact_mod_cast capacity_linear_power_nat hd
  rw [Nat.cast_sub (by omega : 3 ≤ 2 * d)] at h
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at h
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ d)).mpr
  linarith

end Froberg
