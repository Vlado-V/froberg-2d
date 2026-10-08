import Froberg.SlackPolynomial
import Froberg.CountPolynomials
import Froberg.CountParameters

/-! The quadratic-in-`h` coefficient of the outer dimension margin is
strictly positive for the prescribed generator-count interval. -/
noncomputable section
namespace Froberg
open Polynomial

def slackLinearCoefficient (d : ℕ) (P : Polynomial ℝ) : ℝ :=
  (2 * (d : ℝ) - 1) * (2 * (d : ℝ) - 2) / (2 * ((2 * d - 1).factorial : ℝ)) -
  (P.coeff d * (((d : ℝ) - 1) * ((d : ℝ) - 2) / (2 * ((d - 1).factorial : ℝ))) +
    P.coeff (d - 1) / ((d - 1).factorial : ℝ)) -
  (d : ℝ) * P.coeff d * ((d : ℝ) * ((d : ℝ) - 1) / (2 * (d.factorial : ℝ)) - P.coeff (d - 1)) -
  ((d : ℝ) - 1) * P.coeff (d - 1) * ((d.factorial : ℝ)⁻¹ - P.coeff d)

def slackQuadraticCoefficient (d : ℕ) (P : Polynomial ℝ) (α : ℝ) : ℝ :=
  (α - (d.choose 2 : ℝ) * P.coeff d) * ((d.factorial : ℝ)⁻¹ - P.coeff d)

theorem adjusted_slack_second {d : ℕ} (hd : 3 ≤ d) (P : Polynomial ℝ) (h α : ℝ)
    (hP : P.natDegree ≤ d) :
    (transferSlackPolynomial d (P + C 2) (outerCountBoundPolynomial P d h α) h).coeff
      (2 * d - 2) = h ^ 2 * slackQuadraticCoefficient d P α + h * slackLinearCoefficient d P := by
  rw [transferSlackPolynomial_second (by omega) _ _ _ (adjustedCritical_degree P hP)
    (outerCountBound_degree (by omega) P h α hP)]
  rw [adjustedCritical_coeff P (by omega : 0 < d),
    adjustedCritical_coeff P (by omega : 0 < d - 1),
    outerCountBound_top hd P h α hP, outerCountBound_second hd P h α hP]
  unfold slackQuadraticCoefficient slackLinearCoefficient
  ring

theorem slackQuadraticCoefficient_pos {d : ℕ} (hd : 3 ≤ d) (P : Polynomial ℝ)
    (hL : P.coeff d = criticalRatio d / (d.factorial : ℝ)) :
    0 < slackQuadraticCoefficient d P (countAlpha d) := by
  have hf : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  have hρ := (criticalRatio_bounds (d := d) (by omega)).2.1
  have hgap : 0 < (d.factorial : ℝ)⁻¹ - P.coeff d := by
    rw [hL]
    have hh := div_pos (sub_pos.mpr hρ) hf
    convert hh using 1 <;> ring
  have hc : (d.choose 2 : ℝ) * P.coeff d =
      (d : ℝ) * ((d : ℝ) - 1) * criticalRatio d / (2 * (d.factorial : ℝ)) := by
    rw [hL, Nat.cast_choose_two]
    ring
  unfold slackQuadraticCoefficient
  exact mul_pos (sub_pos.mpr (hc ▸ countAlpha_margin hd)) hgap

theorem eventually_positive_quadratic (a b : ℝ) (ha : 0 < a) :
    ∃ N : ℕ, ∀ h : ℕ, N ≤ h → 0 < (h : ℝ) ^ 2 * a + h * b := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (-b / a))
  refine ⟨N, fun h hh => ?_⟩
  have hNh : (N : ℝ) ≤ h := by exact_mod_cast hh
  have hpos : (0 : ℝ) < h := by have := le_max_left (1 : ℝ) (-b / a); linarith
  have hdiv : -b / a < (h : ℝ) := (le_max_right _ _).trans_lt (hN.trans_le hNh)
  have hlin : 0 < (h : ℝ) * a + b := by
    have := (div_lt_iff₀ ha).mp hdiv
    linarith
  have hp := mul_pos hpos hlin
  nlinarith

theorem adjusted_slack_second_eventually_pos {d : ℕ} (hd : 3 ≤ d)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (hL : P.coeff d = criticalRatio d / (d.factorial : ℝ)) :
    ∃ N : ℕ, ∀ h : ℕ, N ≤ h →
      0 < (transferSlackPolynomial d (P + C 2)
        (outerCountBoundPolynomial P d h (countAlpha d)) h).coeff (2 * d - 2) := by
  obtain ⟨N, hN⟩ := eventually_positive_quadratic
    (slackQuadraticCoefficient d P (countAlpha d)) (slackLinearCoefficient d P)
    (slackQuadraticCoefficient_pos hd P hL)
  exact ⟨N, fun h hh => (adjusted_slack_second hd P h (countAlpha d) hP).symm ▸ hN h hh⟩

end Froberg
