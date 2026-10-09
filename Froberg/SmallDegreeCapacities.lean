module

public import Froberg.SmallDegreeRationalBounds

@[expose] public section

/-! # The explicit inequalities of Appendix E

The estimates concern the actual count and deletion parameters. The finite
checks use rational endpoints for the critical roots, rather than numerical
approximations to square roots.
-/

noncomputable section
namespace Froberg

def smallGamma (d : ℕ) : ℝ := (101 / 100) * higherCountGamma d 4

theorem smallBetaBound_nonneg (d : ℕ) : 0 ≤ smallBetaBound d := by
  unfold smallBetaBound smallCriticalUpper
  positivity

theorem small_rate_sq_lt {d : ℕ} (hd : 3 ≤ d) (hd8 : d ≤ 8) :
    outerColumnRate d ^ 2 < smallRateBound d ^ 2 :=
  (sq_lt_sq₀ (outerColumnRate_bounds hd).1.le (smallRateBound_nonneg d)).mpr
    (outerColumnRate_lt_smallRateBound hd hd8)

theorem small_deletion_capacity {d : ℕ} (hd : 3 ≤ d) (hd8 : d ≤ 8) :
    outerColumnRate d ^ 2 / 2 < (7 / 32 : ℝ) := by
  have h := small_rate_sq_lt hd hd8
  interval_cases d <;>
    norm_num [smallRateBound, smallCriticalUpper, smallCriticalNumerator] at h <;> linarith

/-- The sparse quadratic inequality E.4. -/
theorem small_quadratic_scalar_capacity {d : ℕ} (hd : 3 ≤ d) (hd8 : d ≤ 8) :
    countBeta d / (scalarCapacity d 2 * (1 - outerColumnRate d ^ 2)) +
      (scalarCapacityBinomial d 2 : ℝ) * criticalRatio d < 1 := by
  have hβ := countBeta_le_smallBetaBound hd hd8
  have hr := (small_rate_sq_lt hd hd8).le
  have hρ := (smallCritical_bounds (by omega : 2 ≤ d) hd8).2.le
  have hpos : 0 < scalarCapacity d 2 * (1 - smallRateBound d ^ 2) := by
    interval_cases d <;>
      norm_num [scalarCapacity, smallRateBound, smallCriticalUpper, smallCriticalNumerator]
  have hden : scalarCapacity d 2 * (1 - smallRateBound d ^ 2) ≤
      scalarCapacity d 2 * (1 - outerColumnRate d ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (scalarCapacity_pos d 2).le
  have hf := div_le_div₀ (smallBetaBound_nonneg d) hβ hpos hden
  have hg := mul_le_mul_of_nonneg_left hρ
    (show (0 : ℝ) ≤ scalarCapacityBinomial d 2 by positivity)
  have hfin : smallBetaBound d / (scalarCapacity d 2 * (1 - smallRateBound d ^ 2)) +
      (scalarCapacityBinomial d 2 : ℝ) * smallCriticalUpper d < 1 := by
    interval_cases d <;>
      norm_num [smallBetaBound, smallRateBound, smallCriticalUpper, smallCriticalNumerator,
        scalarCapacity, scalarCapacityBinomial, Nat.choose_eq_factorial_div_factorial]
  linarith

/-- The sparse fourth-layer inequality E.5. -/
theorem small_fourth_scalar_capacity {d : ℕ} (hd : 5 ≤ d) (hd8 : d ≤ 8) :
    2 * smallGamma d / scalarCapacity d 4 +
      (scalarCapacityBinomial d 4 : ℝ) * criticalRatio d < 1 := by
  have hρ := (smallCritical_bounds (by omega : 2 ≤ d) hd8).2
  interval_cases d <;>
    norm_num [smallGamma, higherCountGamma, scalarCapacity, scalarCapacityBinomial,
      smallCriticalUpper, smallCriticalNumerator, Nat.choose_eq_factorial_div_factorial] at hρ ⊢ <;>
    linarith

/-- The scalar source separation inequality E.6. -/
theorem small_scalar_source_capacity {d R : ℕ} (hd : 3 ≤ d) (hd8 : d ≤ 8)
    (hR : R = 4 ∨ R = 6 ∨ R = 8) (hRd : R ≤ d) :
    ((2 * d - R).choose (d - R) : ℝ) * criticalRatio d < (2 / 5 : ℝ) := by
  have hρ := (smallCritical_bounds (by omega : 2 ≤ d) hd8).2
  rcases hR with rfl | rfl | rfl
  all_goals interval_cases d <;>
    norm_num [smallCriticalUpper, smallCriticalNumerator, Nat.choose_eq_factorial_div_factorial] at hρ ⊢ <;>
    first | omega | linarith

/-- The special quadratic symmetric-product capacities in degrees three and four. -/
theorem small_quadratic_symmetric_special {d : ℕ} (hd : d = 3 ∨ d = 4) :
    countBeta d < if d = 3 then (5 / 64 : ℝ) else 5 / 512 := by
  have hβ := countBeta_le_smallBetaBound (d := d) (by omega) (by omega)
  rcases hd with rfl | rfl
  all_goals norm_num [smallBetaBound, smallCriticalUpper, smallCriticalNumerator,
    Nat.choose_eq_factorial_div_factorial] at hβ ⊢ <;> linarith

/-- The quadratic symmetric-product capacity in degrees five through eight. -/
theorem small_quadratic_symmetric_capacity {d : ℕ} (hd : 5 ≤ d) (hd8 : d ≤ 8) :
    countBeta d < ((1 / 8 : ℝ) - outerColumnRate d ^ 2 / 2) /
      ((2 : ℝ) ^ (d - 1) * ((d - 2).factorial : ℝ)) := by
  have hβ := countBeta_le_smallBetaBound (d := d) (by omega) hd8
  have hr := (small_rate_sq_lt (d := d) (by omega) hd8).le
  apply (lt_div_iff₀ (by positivity)).mpr
  have hm := mul_le_mul_of_nonneg_right hβ
    (show 0 ≤ (2 : ℝ) ^ (d - 1) * ((d - 2).factorial : ℝ) by positivity)
  interval_cases d <;>
    norm_num [smallBetaBound, smallRateBound, smallCriticalUpper, smallCriticalNumerator,
      Nat.choose_eq_factorial_div_factorial] at hm hr ⊢ <;> linarith

/-- The quadratic factor capacity of the cross product. -/
theorem small_quadratic_cross_capacity {d : ℕ} (hd : 5 ≤ d) (hd8 : d ≤ 8) :
    countBeta d < ((2 / 25 : ℝ) - outerColumnRate d ^ 2 / 2) /
      ((2 : ℝ) ^ (d - 2) * ((d - 2).factorial : ℝ)) := by
  have hβ := countBeta_le_smallBetaBound (d := d) (by omega) hd8
  have hr := (small_rate_sq_lt (d := d) (by omega) hd8).le
  apply (lt_div_iff₀ (by positivity)).mpr
  have hm := mul_le_mul_of_nonneg_right hβ
    (show 0 ≤ (2 : ℝ) ^ (d - 2) * ((d - 2).factorial : ℝ) by positivity)
  interval_cases d <;>
    norm_num [smallBetaBound, smallRateBound, smallCriticalUpper, smallCriticalNumerator,
      Nat.choose_eq_factorial_div_factorial] at hm hr ⊢ <;> linarith

/-- The fourth-layer factor capacity of the cross product. -/
theorem small_fourth_cross_capacity {d : ℕ} (hd : 5 ≤ d) (hd8 : d ≤ 8) :
    smallGamma d < (3 / 5 : ℝ) ^ 4 /
      (24 * (2 : ℝ) ^ (d - 4) * ((d - 4).factorial : ℝ)) := by
  interval_cases d <;> norm_num [smallGamma, higherCountGamma]

/-- The fourth-layer symmetric-product capacity. -/
theorem small_fourth_symmetric_capacity {d : ℕ} (hd : 5 ≤ d) (hd8 : d ≤ 8) :
    smallGamma d < if d = 5 then (1 / 512 : ℝ) else
      1 / (512 * (2 : ℝ) ^ (d - 4) * ((d - 4).factorial : ℝ)) := by
  interval_cases d <;> norm_num [smallGamma, higherCountGamma]

end Froberg
