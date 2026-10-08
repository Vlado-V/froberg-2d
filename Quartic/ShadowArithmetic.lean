import Quartic.Counts

/-! The exact binomial shadow and its linear relaxation, in integer arithmetic. -/

namespace Quartic.ShadowArithmetic

/-- The sharp numerical image bound, with `ceil(i/2)` written as `(i+1)/2`. -/
def shadow (p i : ℕ) : ℤ :=
  ((p + 1).choose 2 : ℤ) - ((p - (i + 1) / 2 + 1).choose 2 : ℤ)

theorem shadow_scaled (p i : ℕ) (hi : i ≤ 2 * p) :
    2 * shadow p i = (((i + 1) / 2 : ℕ) : ℤ) *
      (2 * (p : ℤ) + 1 - (((i + 1) / 2 : ℕ) : ℤ)) := by
  have ha : (i + 1) / 2 ≤ p := by omega
  have h₁ := Counts.b2_scaled p
  have h₂ := Counts.b2_scaled (p - (i + 1) / 2)
  unfold Counts.b2 at h₁ h₂
  rw [Nat.cast_sub ha] at h₂
  unfold shadow
  linear_combination h₁ - h₂

/-- The sharp shadow dominates the linear bound `((p+1)/4) i` without division. -/
theorem shadow_linear_bound (p i : ℕ) (hi : i ≤ 2 * p) :
    ((p : ℤ) + 1) * (i : ℤ) ≤ 4 * shadow p i := by
  let a := (i + 1) / 2
  have ha : a ≤ p := by dsimp [a]; omega
  have hceil : i ≤ 2 * a := by dsimp [a]; omega
  have ha' : (a : ℤ) ≤ p := by exact_mod_cast ha
  have hceil' : (i : ℤ) ≤ 2 * (a : ℤ) := by exact_mod_cast hceil
  have h₁ : 0 ≤ ((p : ℤ) + 1) * (2 * (a : ℤ) - (i : ℤ)) :=
    mul_nonneg (by omega) (by omega)
  have h₂ : 0 ≤ 2 * (a : ℤ) * ((p : ℤ) - (a : ℤ)) :=
    mul_nonneg (by positivity) (by omega)
  have h := shadow_scaled p i hi
  change 2 * shadow p i = (a : ℤ) * (2 * (p : ℤ) + 1 - (a : ℤ)) at h
  nlinarith

theorem shadow_nonnegative (p i : ℕ) (hi : i ≤ 2 * p) : 0 ≤ shadow p i := by
  have h := shadow_linear_bound p i hi
  have hzero : 0 ≤ ((p : ℤ) + 1) * (i : ℤ) := by positivity
  omega

end Quartic.ShadowArithmetic
