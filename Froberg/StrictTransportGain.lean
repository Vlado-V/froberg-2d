module

public import Froberg.CapacityGain

@[expose] public section

/-! The strict weighted growth estimate obtained by combining a decrease
of fiber capacity with mixing of the divisor transport. -/
noncomputable section
namespace Froberg
open Finset
variable {I J : Type*} [Fintype I] [Fintype J]

theorem weightedVariance_le_supported_upper_gap (p u : I → ℝ)
    (hp : ∑ i, p i = 1) (hp0 : ∀ i, 0 ≤ p i)
    (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1) (b : ℝ)
    (hb : ∀ i, 0 < p i → u i ≤ b) :
    weightedVariance p u ≤ b - weightedMean p u := by
  have hm := weightedMean_bounds p u hp hp0 hu0 hu1
  have hmb : weightedMean p u ≤ b := by
    calc
      weightedMean p u ≤ ∑ i, p i * b := by
        apply sum_le_sum
        intro i _
        by_cases hz : p i = 0
        · simp [hz]
        · exact mul_le_mul_of_nonneg_left (hb i (lt_of_le_of_ne (hp0 i) (Ne.symm hz))) (hp0 i)
      _ = b := by rw [← sum_mul, hp, one_mul]
  have hsq : (∑ i, p i * u i ^ 2) ≤ b * weightedMean p u := by
    calc
      (∑ i, p i * u i ^ 2) ≤ ∑ i, b * (p i * u i) := by
        apply sum_le_sum
        intro i _
        by_cases hz : p i = 0
        · simp [hz]
        · have hh := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hb i (lt_of_le_of_ne (hp0 i) (Ne.symm hz))) (hu0 i)) (hp0 i)
          nlinarith
      _ = b * weightedMean p u := by rw [← mul_sum]; rfl
  rw [weightedVariance_expanded p u hp]
  nlinarith [mul_nonneg (sub_nonneg.mpr hm.2) (sub_nonneg.mpr hmb)]

theorem averaged_conditional_mean (ν : J → ℝ) (C : J → I → ℝ) (p u : I → ℝ)
    (hmarginal : ∀ i, ∑ j, ν j * C j i = p i) :
    (∑ j, ν j * weightedMean (C j) u) = weightedMean p u := by
  simp only [weightedMean, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp_rw [← mul_assoc]
  rw [← sum_mul, hmarginal]

/-- Every ingredient is a finite-dimensional numerical condition on the
explicit transport. The result gives the strict normalized shadow gain. -/
theorem strict_transport_gain (ν : J → ℝ) (C D : J → I → ℝ)
    (p q u : I → ℝ) (g : J → ℝ) (η κ : ℝ)
    (hν : ∀ j, 0 ≤ ν j) (hC0 : ∀ j i, 0 ≤ C j i)
    (hC : ∀ j, ∑ i, C j i = 1) (hp : ∑ i, p i = 1)
    (hp0 : ∀ i, 0 ≤ p i) (hq : ∑ i, q i = 1) (hq0 : ∀ i, 0 ≤ q i)
    (hmarginal : ∀ i, ∑ j, ν j * C j i = p i)
    (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1)
    (hη : 0 ≤ η) (hκ : 0 ≤ κ)
    (hminor : ∀ i k, κ * p i * q k ≤ reversibleWeights ν C i k)
    (hmax : ∀ j i, 0 < C j i → u i ≤ g j)
    (hgain : ∀ j, weightedMean (C j) u + ∑ i, D j i * u i * (1 - u i) ≤ g j)
    (hdecrease : ∀ i, η * p i ≤ ∑ j, ν j * D j i) :
    weightedMean p u + (min η (κ / 2) / 2) *
      (weightedMean p u * (1 - weightedMean p u)) ≤ ∑ j, ν j * g j := by
  have hmean := averaged_conditional_mean ν C p u hmarginal
  have hmix := conditional_variance_mixing ν C p q u hC hp hq hq0 κ hκ hminor
  have hvariance : (∑ j, ν j * weightedVariance (C j) u) ≤
      (∑ j, ν j * g j) - weightedMean p u := by
    calc
      _ ≤ ∑ j, ν j * (g j - weightedMean (C j) u) := by
        apply sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left
          (weightedVariance_le_supported_upper_gap (C j) u (hC j) (hC0 j) hu0 hu1 (g j) (hmax j)) (hν j)
      _ = _ := by simp only [mul_sub, sum_sub_distrib, hmean]
  have hintrinsic : η * (∑ i, p i * u i * (1 - u i)) ≤
      (∑ j, ν j * g j) - weightedMean p u := by
    have h₁ : η * (∑ i, p i * u i * (1 - u i)) ≤
        ∑ j, ν j * ∑ i, D j i * u i * (1 - u i) := by
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_le_sum
      intro i _
      have hh := mul_le_mul_of_nonneg_right (hdecrease i)
        (mul_nonneg (hu0 i) (sub_nonneg.mpr (hu1 i)))
      convert hh using 1
      · ring
      · rw [sum_mul]
        apply sum_congr rfl
        intro j _
        ring
    have h₂ := sum_le_sum (fun j (_ : j ∈ (univ : Finset J)) =>
      mul_le_mul_of_nonneg_left (hgain j) (hν j))
    simp only [mul_add, sum_add_distrib, hmean] at h₂
    linarith
  have ha : 0 ≤ ∑ i, p i * u i * (1 - u i) :=
    sum_nonneg fun i _ => mul_nonneg (mul_nonneg (hp0 i) (hu0 i)) (sub_nonneg.mpr (hu1 i))
  have hb := weightedVariance_nonneg p u hp0
  have hma := mul_le_mul_of_nonneg_right (min_le_left η (κ / 2)) ha
  have hmb := mul_le_mul_of_nonneg_right (min_le_right η (κ / 2)) hb
  have hdecomp := mean_defect_decomposition p u hp
  have hmul := congrArg (fun z : ℝ => min η (κ / 2) * z) hdecomp
  nlinarith

/-- Converting the quadratic defect to the symmetric small/large subspace bound. -/
theorem quadratic_defect_ge_half_min (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    min θ (1 - θ) / 2 ≤ θ * (1 - θ) := by
  by_cases hhalf : θ ≤ 1 / 2
  · rw [min_eq_left (by linarith)]
    nlinarith [mul_nonneg hθ (show 0 ≤ 1 / 2 - θ by linarith)]
  · rw [min_eq_right (by linarith)]
    nlinarith [mul_nonneg (show 0 ≤ 1 - θ by linarith) (show 0 ≤ θ - 1 / 2 by linarith)]

end Froberg
