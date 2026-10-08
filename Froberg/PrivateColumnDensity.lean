import Froberg.CoreLimit
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The strict private-column probability margin for the B.2 extension. -/
noncomputable section
namespace Froberg

/-- The critical ratio is uniformly below `1/19` from degree three on. -/
theorem criticalRatio_lt_one_nineteenth {d : ℕ} (hd : 3≤d) :
    criticalRatio d < 1/19 := by
  have hH : (10 : ℝ) ≤ centralHalfBinomial d := by
    exact_mod_cast centralHalfBinomial_ge_ten hd
  have hp := (criticalRatio_bounds (by omega : 2≤d)).1
  have hsharp := criticalRatio_sharp_bound hd
  nlinarith [mul_le_mul_of_nonneg_right hH hp.le]

/-- A power greater than one half controls the first-order loss. -/
theorem power_half_first_order_loss {s : ℕ} {σ : ℝ} (hσ : 0<σ)
    (hp : (1/2 : ℝ) < σ^s) : (s : ℝ)*(1-σ) < 7/10 := by
  have hlog := Real.log_le_sub_one_of_pos hσ
  have hscaled := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
  have hloghalf := Real.log_lt_log (by norm_num : (0 : ℝ) < 1/2) hp
  have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hhalf, Real.log_pow] at hloghalf
  have htwo : Real.log 2 < 7/10 := by linarith [Real.log_two_lt_d9]
  nlinarith

def privateColumnDensity (d : ℕ) : ℝ :=
  1 - limitingCoreFraction d ^ d -
    (d : ℝ)*limitingCoreFraction d ^ (d-1)*(1-limitingCoreFraction d)

/-- Probability of selecting at least two variables outside the core. -/
theorem privateColumnDensity_lower_bound {d : ℕ} (hd : 3≤d) :
    (29/250 : ℝ) < privateColumnDensity d := by
  let σ := limitingCoreFraction d
  let p := (centralHalfBinomial d : ℝ)*criticalRatio d
  have hσ : 0<σ ∧ σ<1 := limitingCoreFraction_bounds hd
  have hpEq : σ^(d-1) = p := limitingCoreFraction_pow hd
  have hp : (1/2 : ℝ)<p := (criticalRatio_bounds (by omega : 2≤d)).2.2.1
  have hpUpper : p<13/25 := criticalRatio_sharp_bound hd
  have hloss := power_half_first_order_loss hσ.1 (hpEq.symm ▸ hp)
  have hp0 : 0<p := by linarith
  have hprod := mul_lt_mul_of_pos_left hloss hp0
  have hstep : σ^d = p*σ := by
    calc
      σ^d = σ^((d-1)+1) := by congr 1; omega
      _ = p*σ := by rw [pow_succ, hpEq]
  have hdR : (d : ℝ) = ((d-1 : ℕ) : ℝ)+1 := by
    exact_mod_cast (show d = (d-1)+1 by omega)
  change (29/250 : ℝ) < 1-σ^d-(d : ℝ)*σ^(d-1)*(1-σ)
  rw [hstep, hpEq, hdR]
  nlinarith

/-- The available private-column density strictly exceeds the endpoint ratio. -/
theorem criticalRatio_lt_privateColumnDensity {d : ℕ} (hd : 3≤d) :
    criticalRatio d < privateColumnDensity d := by
  have h₁ := criticalRatio_lt_one_nineteenth hd
  have h₂ := privateColumnDensity_lower_bound hd
  linarith

end Froberg
