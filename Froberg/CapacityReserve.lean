module

public import Froberg.SmallDegreeRationalBounds

@[expose] public section

/-! # Strict margins for the additional scalar reserve -/

noncomputable section
namespace Froberg

/-- The explicit reserve density used in the normal-map shadow estimate. -/
def scalarReserveDensity (d : ℕ) : ℝ := 1 / (100 * ((2 * d).factorial : ℝ))

theorem scalarReserveDensity_pos (d : ℕ) : 0 < scalarReserveDensity d := by
  unfold scalarReserveDensity
  positivity

/-- The reserve contributes at most one hundredth in every coefficient degree. -/
theorem scalar_reserve_factorial_bound (d t : ℕ) :
    scalarReserveDensity d * ((2 * d - t).factorial : ℝ) /
      ((d - t).factorial : ℝ) ≤ (1 / 100 : ℝ) := by
  have hnum : ((2 * d - t).factorial : ℝ) ≤ ((2 * d).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.sub_le (2 * d) t)
  have hden : (1 : ℝ) ≤ (d - t).factorial := by
    exact_mod_cast Nat.factorial_pos (d - t)
  have hm := mul_le_mul_of_nonneg_left hden
    (show (0 : ℝ) ≤ (2 * d).factorial by positivity)
  calc
    scalarReserveDensity d * ((2 * d - t).factorial : ℝ) /
        ((d - t).factorial : ℝ) =
      ((2 * d - t).factorial : ℝ) /
        (100 * ((2 * d).factorial : ℝ) * ((d - t).factorial : ℝ)) := by
          unfold scalarReserveDensity
          ring
    _ ≤ 1 / 100 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)

/-- The intermediate coefficient shadow margin E.11, in fact without a parity restriction. -/
theorem intermediate_scalar_shadow_margin {d : ℕ} (hd : 3 ≤ d) (t : ℕ) :
    (centralHalfBinomial d : ℝ) * criticalRatio d +
      scalarReserveDensity d * ((2 * d - t).factorial : ℝ) /
        ((d - t).factorial : ℝ) < 1 := by
  have hρ := criticalRatio_sharp_bound hd
  have hδ := scalar_reserve_factorial_bound d t
  linarith

/-- The top-degree odd margin E.10 for the three small odd degrees. -/
theorem small_odd_top_shadow_margin {d : ℕ} (hd : d = 3 ∨ d = 5 ∨ d = 7) :
    (2 * (d : ℝ) ^ 2 + 1) * criticalRatio d +
      (d.factorial : ℝ) * scalarReserveDensity d < 1 := by
  have hρ := (smallCritical_bounds (d := d) (by omega) (by omega)).2
  rcases hd with rfl | rfl | rfl
  all_goals norm_num [scalarReserveDensity, smallCriticalUpper, smallCriticalNumerator] at hρ ⊢ <;>
    linarith

end Froberg
