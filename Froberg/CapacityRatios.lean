import Froberg.AuxiliaryCounts
import Froberg.BlockParameters
import Mathlib.Data.Nat.Choose.Central

/-! # Explicit capacity ratios for the intermediate families

All constants below are the actual factorial formulas used for the counts;
no asymptotic capacity inequality is taken as a hypothesis.
-/

noncomputable section
namespace Froberg

/-- Scalar multiplication capacity at bidegree `j`. -/
def scalarCapacity (d j : ℕ) : ℝ :=
  (d.factorial : ℝ) / ((j.factorial : ℝ) * ((2 * d - j).factorial : ℝ))

/-- Separated-product capacity at bidegree `j`. -/
def productCapacity (d j : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ (d + 1) * (j.factorial : ℝ) * ((d - j).factorial : ℝ))

def scalarCapacityBinomial (d j : ℕ) : ℕ := (2 * d - j).choose (d - j)

def intermediateDensity (d j : ℕ) : ℝ :=
  if j = 2 then countGammaTwo d else higherCountGamma d j

theorem scalarCapacity_pos (d j : ℕ) : 0 < scalarCapacity d j := by
  unfold scalarCapacity
  positivity

theorem productCapacity_pos (d j : ℕ) : 0 < productCapacity d j := by
  unfold productCapacity
  positivity

/-- A rational upper bound avoids square-root approximation in finite checks. -/
theorem criticalRatio_rational_upper {d : ℕ} (hd : 2 ≤ d) :
    criticalRatio d < 1 / (2 * (centralHalfBinomial d : ℝ) - 1) := by
  have hH : (2 : ℝ) ≤ centralHalfBinomial d := by
    exact_mod_cast centralHalfBinomial_ge_two hd
  have hb := criticalRatio_bounds hd
  have hi := criticalRatio_identity hd
  apply (lt_div_iff₀ (by linarith : 0 < 2 * (centralHalfBinomial d : ℝ) - 1)).mpr
  have hm := mul_lt_mul_of_pos_right hb.2.2.2 hb.1
  nlinarith

theorem quadratic_critical_ratio_lt : criticalRatio 2 < (23 / 125 : ℝ) := by
  have hi := criticalRatio_identity (d := 2) (by omega)
  have hb := criticalRatio_bounds (d := 2) (by omega)
  norm_num [centralHalfBinomial] at hi
  by_contra h
  have hs := mul_self_le_mul_self (by linarith : 0 ≤ 1 - criticalRatio 2)
    (by linarith : 1 - criticalRatio 2 ≤ 102 / 125)
  nlinarith

end Froberg
