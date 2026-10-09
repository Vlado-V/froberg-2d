module

public import Froberg.TransportVariance

@[expose] public section

/-! The strict gain from a decrease of fiber capacity, and its relation
to conditional variance. -/
noncomputable section
namespace Froberg
open Finset

theorem capacity_decrease_gain (c d u : ℝ) (hc : 0 ≤ c) (hcd : c ≤ d)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    c * u + min c (d - c) * u * (1 - u) ≤ min c (d * u) := by
  have hk₁ := min_le_left c (d - c)
  have hk₂ := min_le_right c (d - c)
  have hu' : 0 ≤ u * (1 - u) := mul_nonneg hu (by linarith)
  by_cases hcu : c ≤ d * u
  · rw [min_eq_left hcu]
    have h₁ := mul_le_mul_of_nonneg_right hk₁ hu'
    have h₂ := mul_nonneg hc (sq_nonneg (1 - u))
    nlinarith
  · rw [min_eq_right (not_le.mp hcu).le]
    have h₁ := mul_le_mul_of_nonneg_right hk₂ hu'
    have h₂ := mul_nonneg (sub_nonneg.mpr hcd) (sq_nonneg u)
    nlinarith

variable {I : Type*} [Fintype I]

theorem weightedMean_bounds (p u : I → ℝ) (hp : ∑ i, p i = 1)
    (hp0 : ∀ i, 0 ≤ p i) (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1) :
    0 ≤ weightedMean p u ∧ weightedMean p u ≤ 1 := by
  constructor
  · exact sum_nonneg fun i _ => mul_nonneg (hp0 i) (hu0 i)
  · calc
      weightedMean p u ≤ ∑ i, p i * 1 := sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hu1 i) (hp0 i)
      _ = 1 := by simp only [mul_one, hp]

theorem weightedVariance_le_upper_gap (p u : I → ℝ) (hp : ∑ i, p i = 1)
    (hp0 : ∀ i, 0 ≤ p i) (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1)
    (b : ℝ) (hb : ∀ i, u i ≤ b) :
    weightedVariance p u ≤ b - weightedMean p u := by
  have hm := weightedMean_bounds p u hp hp0 hu0 hu1
  have hmb : weightedMean p u ≤ b := by
    calc
      weightedMean p u ≤ ∑ i, p i * b := sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hb i) (hp0 i)
      _ = b := by rw [← sum_mul, hp, one_mul]
  have hsq : (∑ i, p i * u i ^ 2) ≤ b * weightedMean p u := by
    calc
      (∑ i, p i * u i ^ 2) ≤ ∑ i, b * (p i * u i) := by
        apply sum_le_sum
        intro i _
        have hh := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hb i) (hu0 i)) (hp0 i)
        nlinarith
      _ = b * weightedMean p u := by rw [← mul_sum]; rfl
  rw [weightedVariance_expanded p u hp]
  have hh := mul_nonneg (sub_nonneg.mpr hm.2) (sub_nonneg.mpr hmb)
  nlinarith

theorem mean_defect_decomposition (p u : I → ℝ) (hp : ∑ i, p i = 1) :
    weightedMean p u * (1 - weightedMean p u) =
      (∑ i, p i * u i * (1 - u i)) + weightedVariance p u := by
  rw [weightedVariance_expanded p u hp]
  have hsum : (∑ i, p i * u i * (1 - u i)) = weightedMean p u - ∑ i, p i * u i ^ 2 := by
    unfold weightedMean
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [hsum]
  ring

end Froberg
