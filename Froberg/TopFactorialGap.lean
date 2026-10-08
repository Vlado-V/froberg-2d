import Froberg.TopShadowMargin

/-! The projected growth ratio pays for both families in C.9. -/
noncomputable section
namespace Froberg

theorem top_factorial_gap {d h a b : ℕ} (hd : 3≤d) (ha : 0<a) (hb : 0<b)
    (hratio : (h : ℝ)/(2*(d : ℝ))≤(b : ℝ)/a) :
    ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))*a+
      (criticalRatio d/(d.factorial : ℝ)+scalarReserveDensity d)*b<
        (b : ℝ)*(d.factorial : ℝ)⁻¹ := by
  have haR : (0 : ℝ)<a := by exact_mod_cast ha
  have hbR : (0 : ℝ)<b := by exact_mod_cast hb
  have hdR : (0 : ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hfR : (0 : ℝ)<d.factorial := by positivity
  have hrp := (criticalRatio_bounds (show 2≤d by omega)).1
  have hmul := (div_le_div_iff₀ (by positivity : (0 : ℝ)<2*d) haR).mp hratio
  have hscaled := mul_le_mul_of_nonneg_right hmul (mul_nonneg hdR.le hrp.le)
  have hmargin := mul_lt_mul_of_pos_left (top_scalar_shadow_margin hd) hbR
  rw [mul_one] at hmargin
  have hid : (((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))*a+
      (criticalRatio d/(d.factorial : ℝ)+scalarReserveDensity d)*b)*(d.factorial : ℝ)=
      (h : ℝ)*a*d*criticalRatio d+b*criticalRatio d+
        b*(d.factorial : ℝ)*scalarReserveDensity d := by
    rw [factorial_pred_real (show 0<d by omega)]
    field_simp [factorial_real_ne_zero]
    <;> ring
  rw [←div_eq_mul_inv]
  apply (lt_div_iff₀ hfR).mpr
  rw [hid]
  nlinarith

end Froberg
