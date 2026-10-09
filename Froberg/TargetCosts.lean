module

public import Froberg.CapacityProductIdentity

@[expose] public section

/-! # Exact convolution costs for the positive target rows -/

noncomputable section
namespace Froberg

/-- Leading density of the convolution construction for a degree-`j` layer
filling target row `b`. -/
def targetCost (d j b : ℕ) : ℝ :=
  ((b - j).factorial : ℝ) * ((d + j - b).factorial : ℝ) /
    ((b.factorial : ℝ) * ((2 * d - b).factorial : ℝ))

theorem targetCost_pos (d j b : ℕ) : 0 < targetCost d j b := by
  unfold targetCost
  positivity

/-- The factorial cost is the output threshold divided by the number of
convolution output directions and by the scalar factorial. -/
theorem targetCost_eq_convolution {d j b : ℕ} (hjd : j ≤ d) (hb : b ≤ d + j) :
    targetCost d j b =
      (((b - j).factorial : ℝ) / (b.factorial : ℝ)) /
        (((d - j).factorial : ℝ) * ((2 * d - b).choose (d - j) : ℝ)) := by
  rw [choose_real_factorial (show d - j ≤ 2 * d - b by omega),
    show 2 * d - b - (d - j) = d + j - b by omega]
  unfold targetCost
  field_simp [factorial_real_ne_zero] <;> ring

/-- The consecutive-row ratio from Proposition B.7. -/
theorem targetCost_step {d j b : ℕ} (hjb : j ≤ b) (hbd : b < d + j)
    (hjd : j ≤ d) :
    targetCost d j (b + 1) = targetCost d j b *
      ((((b : ℝ) - (j : ℝ) + 1) * (2 * (d : ℝ) - (b : ℝ))) /
        (((b : ℝ) + 1) * ((d : ℝ) + (j : ℝ) - (b : ℝ)))) := by
  have h₁ : b + 1 - j = (b - j) + 1 := by omega
  have h₂ : d + j - b = (d + j - (b + 1)) + 1 := by omega
  have h₃ : 2 * d - b = (2 * d - (b + 1)) + 1 := by omega
  have hdif : (d : ℝ) + (j : ℝ) - (b : ℝ) ≠ 0 := by
    have h : (b : ℝ) < (d : ℝ) + (j : ℝ) := by exact_mod_cast hbd
    linarith
  have htwo : 2 * (d : ℝ) - (b : ℝ) ≠ 0 := by
    have h : (b : ℝ) < 2 * (d : ℝ) := by exact_mod_cast (show b < 2 * d by omega)
    linarith
  unfold targetCost
  rw [h₁, factorial_add_one_real, factorial_add_one_real b,
    h₂, factorial_add_one_real (d + j - (b + 1)),
    h₃, factorial_add_one_real (2 * d - (b + 1))]
  rw [Nat.cast_sub hjb, Nat.cast_sub (by omega : b + 1 ≤ d + j),
    Nat.cast_sub (by omega : b + 1 ≤ 2 * d)]
  push_cast
  simp only [sub_add_eq_sub_sub, sub_add_cancel]
  field_simp [factorial_real_ne_zero, hdif, htwo]
  ring_nf
  have htwo' : -(b : ℝ) + (d : ℝ) * 2 ≠ 0 := by
    convert htwo using 1 <;> ring
  field_simp [htwo']
  ring

/-- Every successive cost decreases before the twice-layer degree. -/
theorem targetCost_strict_step {d j b : ℕ} (hj : 0 < j) (hjb : j ≤ b)
    (hb : b < 2 * j) (hbd : b < d + j) (hjd : j ≤ d) :
    targetCost d j (b + 1) < targetCost d j b := by
  rw [targetCost_step hjb hbd hjd]
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hbR : (b : ℝ) + 1 ≤ 2 * (j : ℝ) := by exact_mod_cast hb
  have hbdR : (b : ℝ) < (d : ℝ) + (j : ℝ) := by exact_mod_cast hbd
  have hratio : (((b : ℝ) - (j : ℝ) + 1) * (2 * (d : ℝ) - (b : ℝ))) /
      (((b : ℝ) + 1) * ((d : ℝ) + (j : ℝ) - (b : ℝ))) < 1 := by
    apply (div_lt_one (by positivity)).mpr
    have hp := mul_nonneg (show (0 : ℝ) ≤ d by positivity)
      (show 0 ≤ 2 * (j : ℝ) - (b : ℝ) - 1 by linarith)
    nlinarith
  simpa only [mul_one] using mul_lt_mul_of_pos_left hratio (targetCost_pos d j b)

/-- The first row bounds all subsequent convolution costs below degree `2j`. -/
theorem targetCost_le_first {d j a b : ℕ} (hj : 0 < j) (hja : j ≤ a)
    (hab : a ≤ b) (hb : b ≤ 2 * j) (hbd : b ≤ d + j) (hjd : j ≤ d) :
    targetCost d j b ≤ targetCost d j a := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
      exact (targetCost_strict_step hj (by omega) (by omega) (by omega) hjd).le.trans
        (ih (by omega) (by omega))

/-- The fourth layer's first row has exactly the prescribed density. -/
theorem targetCost_fourth_first {d : ℕ} (hd : 4 ≤ d) :
    targetCost d 4 5 = higherCountGamma d 4 := by
  simp only [targetCost, higherCountGamma, if_pos rfl]
  rw [show d + 4 - 5 = d - 1 by omega]
  norm_num

/-- The initial row for every higher layer has exactly the prescribed density. -/
theorem targetCost_higher_first {d j : ℕ} (hj : 6 ≤ j) (hjd : j ≤ d) :
    targetCost d j (2 * j - 4) = higherCountGamma d j := by
  simp only [targetCost, higherCountGamma, if_neg (by omega : j ≠ 4)]
  rw [show 2 * j - 4 - j = j - 4 by omega,
    show d + j - (2 * j - 4) = d - j + 4 by omega,
    show 2 * d - (2 * j - 4) = 2 * d - 2 * j + 4 by omega]

/-- The factor `101/100` supplies a strict margin in rows five through seven. -/
theorem fourth_target_cost_margin {d b : ℕ} (hd : 4 ≤ d) (hb : 5 ≤ b)
    (hb7 : b ≤ 7) (hbd : b ≤ d + 4) :
    targetCost d 4 b < (101 / 100 : ℝ) * higherCountGamma d 4 := by
  have h := targetCost_le_first (d := d) (j := 4) (a := 5) (b := b)
    (by omega) (by omega) hb (by omega) hbd hd
  rw [targetCost_fourth_first hd] at h
  have hp := higherCountGamma_pos d 4
  linarith

/-- The same strict margin holds on every prescribed higher-layer interval. -/
theorem higher_target_cost_margin {d j b : ℕ} (hj : 6 ≤ j) (hjd : j ≤ d)
    (hb : 2 * j - 4 ≤ b) (hbj : b < 2 * j) (hbd : b ≤ d + j) :
    targetCost d j b < (101 / 100 : ℝ) * higherCountGamma d j := by
  have h := targetCost_le_first (d := d) (j := j) (a := 2 * j - 4) (b := b)
    (by omega) (by omega) hb (by omega) hbd hjd
  rw [targetCost_higher_first hj hjd] at h
  have hp := higherCountGamma_pos d j
  linarith

end Froberg
