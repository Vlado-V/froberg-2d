import Froberg.AsymptoticCounts
import Froberg.CountParameters

/-! Eventual bounds for the fixed outer block and the deleted target
codimension, including the small-codimension inequality for degrees at least nine. -/
noncomputable section
namespace Froberg
open Polynomial Filter
open scoped Topology

theorem centralHalfBinomial_double_step {d : ℕ} (hd : 0 < d) :
    2 * centralHalfBinomial d ≤ centralHalfBinomial (d + 1) := by
  have hp := Nat.choose_succ_succ (2 * d) (d - 1)
  have hi : d - 1 + 1 = d := by omega
  simp only [Nat.succ_eq_add_one, hi] at hp
  rw [centralBinomial_eq_twice_half hd] at hp
  have hnext : centralHalfBinomial (d + 1) = (2 * d + 1).choose d := by
    unfold centralHalfBinomial
    congr 1 <;> omega
  rw [hnext]
  omega

theorem centralHalfBinomial_ge_three_mul {d : ℕ} (hd : 3 ≤ d) :
    3 * d ≤ centralHalfBinomial d := by
  induction d, hd using Nat.le_induction with
  | base => decide
  | succ d hd ih =>
      have hh := centralHalfBinomial_double_step (d := d) (by omega)
      nlinarith

theorem centralHalfBinomial_ge_thousand_mul {d : ℕ} (hd : 9 ≤ d) :
    1000 * d ≤ centralHalfBinomial d := by
  induction d, hd using Nat.le_induction with
  | base => decide
  | succ d hd ih =>
      have hh := centralHalfBinomial_double_step (d := d) (by omega)
      nlinarith

theorem centralHalfBinomial_ge_five_quarters_pow {d : ℕ} (hd : 3 ≤ d) :
    5 * 2 ^ d ≤ 4 * centralHalfBinomial d := by
  induction d, hd using Nat.le_induction with
  | base => decide
  | succ d hd ih =>
      have hh := centralHalfBinomial_double_step (d := d) (by omega)
      rw [pow_succ]
      nlinarith

theorem centralHalfBinomial_ge_fortyfive_pow {d : ℕ} (hd : 9 ≤ d) :
    45 * 2 ^ d ≤ centralHalfBinomial d := by
  induction d, hd using Nat.le_induction with
  | base => decide
  | succ d hd ih =>
      have hh := centralHalfBinomial_double_step (d := d) (by omega)
      rw [pow_succ]
      nlinarith

def outerColumnRate (d : ℕ) : ℝ := (11 / 10) * 2 ^ d * criticalRatio d
def outerColumnCount (d h : ℕ) : ℕ := ⌈outerColumnRate d * h⌉₊
def deletedTargetCount (d h : ℕ) : ℕ := (outerColumnCount d h + 1).choose 2

theorem outerColumnRate_bounds {d : ℕ} (hd : 3 ≤ d) :
    0 < outerColumnRate d ∧ outerColumnRate d < 1 := by
  have hρ := criticalRatio_bounds (d := d) (by omega)
  have hH : 5 * (2 : ℝ) ^ d ≤ 4 * centralHalfBinomial d := by
    exact_mod_cast centralHalfBinomial_ge_five_quarters_pow hd
  have hm := mul_le_mul_of_nonneg_right hH hρ.1.le
  have hdpos : (0 : ℝ) < 2 ^ d := by positivity
  unfold outerColumnRate
  constructor
  · exact mul_pos (mul_pos (by norm_num) hdpos) hρ.1
  · nlinarith [hρ.2.2.2]

theorem outerColumnRate_small {d : ℕ} (hd : 9 ≤ d) : outerColumnRate d < 1 / 75 := by
  have hρ := criticalRatio_bounds (d := d) (by omega)
  have hH : 45 * (2 : ℝ) ^ d ≤ centralHalfBinomial d := by
    exact_mod_cast centralHalfBinomial_ge_fortyfive_pow hd
  have hm := mul_le_mul_of_nonneg_right hH hρ.1.le
  unfold outerColumnRate
  nlinarith [criticalRatio_sharp_bound (d := d) (by omega)]

theorem outerColumnCount_strict_lower {d h : ℕ} (hd : 3 ≤ d) (hh : 0 < h) :
    (2 : ℝ) ^ d * criticalRatio d * h < (outerColumnCount d h : ℝ) := by
  have hlo := Nat.le_ceil (outerColumnRate d * h)
  have hpos : 0 < (2 : ℝ) ^ d * criticalRatio d * h :=
    mul_pos (mul_pos (by positivity) (criticalRatio_bounds (d := d) (by omega)).1)
      (by exact_mod_cast hh)
  change (2 : ℝ) ^ d * criticalRatio d * h < (⌈outerColumnRate d * h⌉₊ : ℝ)
  apply lt_of_lt_of_le _ hlo
  unfold outerColumnRate
  nlinarith

theorem outerColumnCount_limit {d : ℕ} (hd : 3 ≤ d) :
    Tendsto (fun h : ℕ => (outerColumnCount d h : ℝ) / (h : ℝ))
      atTop (𝓝 (outerColumnRate d)) := by
  have h := ceil_normalized_limit (fun h : ℕ => outerColumnRate d * h) (k := 1)
    (by omega) (outerColumnRate d)
    (Eventually.of_forall fun h => mul_nonneg (outerColumnRate_bounds hd).1.le (Nat.cast_nonneg h))
    (by simpa only [pow_one] using scaled_power_normalized_limit (outerColumnRate d) 1)
  simpa only [outerColumnCount, pow_one] using h

theorem deletedTargetCount_limit {d : ℕ} (hd : 3 ≤ d) :
    Tendsto (fun h : ℕ => (deletedTargetCount d h : ℝ) / (h : ℝ) ^ 2)
      atTop (𝓝 (outerColumnRate d ^ 2 / 2)) := by
  have hL := outerColumnCount_limit hd
  have hone : Tendsto (fun h : ℕ => (1 : ℝ) / (h : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hp := ((hL.add hone).mul hL).div_const 2
  convert hp using 1
  · congr 1
    funext h
    simp only [deletedTargetCount, Nat.cast_choose_two, Nat.cast_add, Nat.cast_one]
    ring
  · congr 1
    ring

theorem block_parameters_eventually {d : ℕ} (hd : 3 ≤ d) :
    ∀ᶠ h : ℕ in atTop,
      outerColumnCount d h ≤ h ∧ 2 * h - 1 ≤ deletedTargetCount d h ∧
      (9 ≤ d → (deletedTargetCount d h : ℝ) < (h : ℝ) ^ 2 / 10000) := by
  have hL := eventually_lt_of_normalized_limits (fun h => (outerColumnCount d h : ℝ))
    (fun h : ℕ => (h : ℝ)) 1 (outerColumnRate d) 1
    (by simpa using outerColumnCount_limit hd)
    (by simpa using scaled_power_normalized_limit (1 : ℝ) 1)
    (outerColumnRate_bounds hd).2
  have hTwo : Tendsto (fun h : ℕ => (2 * (h : ℝ)) / (h : ℝ) ^ 2) atTop (𝓝 0) := by
    have hp := polynomial_div_pow_nat_tendsto (C 2 * X : Polynomial ℝ) 2 (by compute_degree <;> norm_num)
    simpa using hp
  have hcpos : 0 < outerColumnRate d ^ 2 / 2 := by
    have hh := (outerColumnRate_bounds hd).1
    positivity
  have hC := eventually_lt_of_normalized_limits (fun h : ℕ => 2 * (h : ℝ))
    (fun h => (deletedTargetCount d h : ℝ)) 2 0 _ hTwo (deletedTargetCount_limit hd) hcpos
  have hsmall : ∀ᶠ h : ℕ in atTop,
      9 ≤ d → (deletedTargetCount d h : ℝ) < (h : ℝ) ^ 2 / 10000 := by
    by_cases hd9 : 9 ≤ d
    · have hrate := outerColumnRate_small hd9
      have hpos := (outerColumnRate_bounds hd).1
      have hrate2 : outerColumnRate d ^ 2 / 2 < 1 / 10000 := by nlinarith
      have hs := eventually_lt_of_normalized_limits (fun h => (deletedTargetCount d h : ℝ))
        (fun h : ℕ => (1 / 10000 : ℝ) * (h : ℝ) ^ 2) 2 _ _
        (deletedTargetCount_limit hd) (scaled_power_normalized_limit (1 / 10000 : ℝ) 2) hrate2
      exact hs.mono fun h hh _ => by nlinarith
    · exact Eventually.of_forall fun _ hh => False.elim (hd9 hh)
  filter_upwards [hL, hC, hsmall] with h hl hc hs
  have hl' : outerColumnCount d h < h := by exact_mod_cast hl
  have hc' : 2 * h < deletedTargetCount d h := by exact_mod_cast hc
  exact ⟨by omega, by omega, hs⟩

end Froberg
