import Froberg.CapacityCentral
import Froberg.CapacityProductIdentity
import Froberg.CapacityPowers

/-! # Product-capacity bounds from explicit binomial estimates -/

noncomputable section
namespace Froberg

theorem reciprocal_near_product_bound {a b : ℕ} (ha : 4 ≤ a) (hb : 6 ≤ b) :
    (2 : ℝ) ^ (a + b + 1) /
      ((nearCentralBinomial a : ℝ) * (nearCentralBinomial b : ℝ)) ≤
        10 * (((a + b : ℕ) : ℝ) + 1) ^ 2 / (2 : ℝ) ^ (a + b) := by
  have hA : (2 : ℝ) * 4 ^ a ≤ 5 * (2 * (a : ℝ) + 1) * (nearCentralBinomial a : ℝ) := by
    exact_mod_cast nearCentralBinomial_exponential_five ha
  have hB : (4 : ℝ) ^ b ≤ 2 * (2 * (b : ℝ) + 1) * (nearCentralBinomial b : ℝ) := by
    exact_mod_cast nearCentralBinomial_exponential_two hb
  have hAB := mul_le_mul hA hB (by positivity) (by positivity)
  have hp : (4 : ℝ) ^ (a + b) = 4 ^ a * 4 ^ b := pow_add _ _ _
  have hs : (2 * (a : ℝ) + 1) * (2 * (b : ℝ) + 1) ≤ ((a : ℝ) + (b : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg ((a : ℝ) - (b : ℝ))]
  have hsm := mul_le_mul_of_nonneg_right hs
    (show 0 ≤ 10 * (nearCentralBinomial a : ℝ) * (nearCentralBinomial b : ℝ) by positivity)
  have hapos : (0 : ℝ) < nearCentralBinomial a := by
    exact_mod_cast Nat.choose_pos (show a + 2 ≤ 2 * a by omega)
  have hbpos : (0 : ℝ) < nearCentralBinomial b := by
    exact_mod_cast Nat.choose_pos (show b + 2 ≤ 2 * b by omega)
  have hfour : (4 : ℝ) ^ (a + b) = (2 : ℝ) ^ (a + b) * 2 ^ (a + b) := by
    rw [← mul_pow]
    norm_num
  apply (div_le_div_iff₀ (mul_pos hapos hbpos) (by positivity)).mpr
  rw [Nat.cast_add, pow_succ]
  nlinarith [hp, hfour]

/-- A single exponential binomial bound controls a reciprocal ratio. -/
theorem reciprocal_of_binomial_lower_bound (m : ℕ) (B : ℝ) (hB : 0 < B)
    (h : (4 : ℝ) ^ m ≤ 2 * (2 * (m : ℝ) + 1) * B) :
    (2 : ℝ) ^ (m + 3) / B ≤ 64 * (2 * (m : ℝ) + 1) / (2 : ℝ) ^ (m + 2) := by
  apply (div_le_div_iff₀ hB (by positivity)).mpr
  have hf : (4 : ℝ) ^ m = (2 : ℝ) ^ m * 2 ^ m := by
    rw [← mul_pow]
    norm_num
  norm_num only [pow_add, pow_two, pow_succ, pow_zero, mul_one] at ⊢
  nlinarith [hf]

/-- All higher layers with at least four complementary degrees satisfy
this uniform product-ratio estimate. -/
theorem higher_product_density_bound {d j : ℕ} (hj : 6 ≤ j) (ht : 4 ≤ d - j) (hjd : j ≤ d) :
    higherCountGamma d j / productCapacity d j ≤
      10 * ((d : ℝ) + 1) ^ 2 / (2 : ℝ) ^ d := by
  rw [higher_product_ratio hj hjd]
  have h := reciprocal_near_product_bound (a := j - 2) (b := d - j + 2) (by omega) (by omega)
  have hA : nearCentralBinomial (j - 2) = (2 * j - 4).choose j := by
    unfold nearCentralBinomial
    congr 1 <;> omega
  have hB : nearCentralBinomial (d - j + 2) = (2 * (d - j) + 4).choose (d - j) := by
    unfold nearCentralBinomial
    rw [show 2 * (d - j + 2) = 2 * (d - j) + 4 by omega,
      show d - j + 2 + 2 = d - j + 4 by omega]
    exact Nat.choose_symm_of_eq_add (by omega)
  rw [hA, hB, show j - 2 + (d - j + 2) = d by omega] at h
  exact h

/-- The same reciprocal estimate at the fourth layer. -/
theorem fourth_product_density_bound {d : ℕ} (hd : 8 ≤ d) :
    scalarCapacity d 4 / productCapacity d 4 ≤
      64 * (2 * (d : ℝ) - 3) / (2 : ℝ) ^ d := by
  rw [fourth_product_ratio (by omega)]
  have hnear : nearCentralBinomial (d - 2) = scalarCapacityBinomial d 4 := by
    unfold nearCentralBinomial scalarCapacityBinomial
    rw [show 2 * (d - 2) = 2 * d - 4 by omega, show d - 2 + 2 = d by omega]
    exact Nat.choose_symm_of_eq_add (by omega)
  have hp : (0 : ℝ) < nearCentralBinomial (d - 2) := by
    exact_mod_cast Nat.choose_pos (show d - 2 + 2 ≤ 2 * (d - 2) by omega)
  have hl : (4 : ℝ) ^ (d - 2) ≤ 2 * (2 * ((d - 2 : ℕ) : ℝ) + 1) *
      (nearCentralBinomial (d - 2) : ℝ) := by
    exact_mod_cast nearCentralBinomial_exponential_two (show 6 ≤ d - 2 by omega)
  have h := reciprocal_of_binomial_lower_bound (d - 2) _ hp hl
  rw [hnear, show d - 2 + 3 = d + 1 by omega, show d - 2 + 2 = d by omega,
    Nat.cast_sub (by omega : 2 ≤ d), Nat.cast_ofNat] at h
  convert h using 1 <;> ring

end Froberg
