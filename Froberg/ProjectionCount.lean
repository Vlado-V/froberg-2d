import Mathlib.Tactic

/-! The explicit strict Schubert inequality in the projected-top argument. -/
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg

/-- Failure of normalized projected growth costs more parameters than a
Grassmannian source family whenever ub>a². -/
theorem projection_failure_count_real {a u b ell w t : ℝ}
    (ha : 0 < a) (hu : 0 ≤ u) (hb : 0 ≤ b) (hl : 0 < ell) (hla : ell ≤ a)
    (ht : 0 ≤ t) (hw : (u+b)*ell ≤ a*w) (hfail : a*t < b*ell)
    (hmargin : a*a < u*b) :
    ell*(a-ell)+t*(b-t) < w*(b-t) := by
  have hu0 : 0 < u := by nlinarith [sq_nonneg a]
  have hb0 : 0 < b := by nlinarith [sq_nonneg a]
  have hbt : 0 < b-t := by nlinarith [mul_le_mul_of_nonneg_left hla hb]
  have hwt : 0 < w-t := by nlinarith [mul_nonneg hu (le_of_lt hl)]
  have h₁ : u*ell < a*(w-t) := by nlinarith
  have h₂ : b*(a-ell) < a*(b-t) := by nlinarith
  by_cases he : ell = a
  · subst ell
    nlinarith [mul_pos hbt hwt]
  have hla' : 0 < a-ell := by
    apply sub_pos.mpr
    rcases lt_or_eq_of_le hla with h | h
    · exact h
    · exact False.elim (he h)
  have hp := mul_lt_mul h₁ h₂.le (mul_pos hb0 hla') (le_of_lt (mul_pos ha hwt))
  have hscale : a^2 * (ell*(a-ell)) < a^2 * ((w-t)*(b-t)) := by
    have hm := mul_le_mul_of_nonneg_right (le_of_lt hmargin)
      (le_of_lt (mul_pos hl hla'))
    nlinarith
  have hcost : ell*(a-ell) < (w-t)*(b-t) :=
    (mul_lt_mul_iff_right₀ (sq_pos_of_pos ha)).mp hscale
  nlinarith

end Froberg
