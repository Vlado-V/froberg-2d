import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-! Irrationality of the leading coefficient of the critical generator count. -/

namespace Froberg

/-- The product of two consecutive positive integers is never a square. -/
theorem not_isSquare_mul_pred {H : ℕ} (hH : 2 ≤ H) :
    ¬ IsSquare (H * (H - 1)) := by
  rintro ⟨a, ha⟩
  have hpred : H - 1 + 1 = H := Nat.sub_add_cancel (by omega)
  have hpos : 0 < H - 1 := by omega
  by_cases h : a ≤ H - 1
  · nlinarith [sq_nonneg (H - 1 - a : ℤ)]
  · have h' : H ≤ a := by omega
    nlinarith

/-- For each integer `H ≥ 2`, the square root in the critical-count formula
is irrational. -/
theorem irrational_sqrt_one_sub_inv {H : ℕ} (hH : 2 ≤ H) :
    Irrational (Real.sqrt (1 - 1 / (H : ℝ))) := by
  have hH0 : H ≠ 0 := by omega
  have hHr : (H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hH0
  have hcast : ((H * (H - 1) : ℕ) : ℝ) =
      (H : ℝ) ^ 2 * (1 - 1 / (H : ℝ)) := by
    rw [Nat.cast_mul, Nat.cast_sub (show 1 ≤ H by omega), Nat.cast_one]
    field_simp
  have hi := irrational_sqrt_natCast_iff.mpr (not_isSquare_mul_pred hH)
  rw [hcast, Real.sqrt_mul (sq_nonneg (H : ℝ)),
    Real.sqrt_sq (Nat.cast_nonneg H)] at hi
  exact hi.of_natCast_mul H

/-- `ρ = 1 - √(1 - 1/H)` is irrational, including the central-binomial
values used by the critical generator count. -/
theorem irrational_critical_ratio {H : ℕ} (hH : 2 ≤ H) :
    Irrational (1 - Real.sqrt (1 - 1 / (H : ℝ))) := by
  simpa using (irrational_sqrt_one_sub_inv hH).natCast_sub 1

/-- Dividing the critical ratio by the generating degree factorial preserves
irrationality. -/
theorem irrational_critical_leadingCoeff {H : ℕ} (hH : 2 ≤ H) (d : ℕ) :
    Irrational ((1 - Real.sqrt (1 - 1 / (H : ℝ))) / (d.factorial : ℝ)) :=
  (irrational_critical_ratio hH).div_natCast (Nat.factorial_ne_zero d)

end Froberg
