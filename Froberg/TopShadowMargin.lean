module

public import Froberg.CapacityReserve
public import Froberg.TopCountInequalities

@[expose] public section

/-! The strict top-layer scalar reserve margin, including all small degrees. -/
noncomputable section
namespace Froberg

theorem centralHalfBinomial_quadratic_lower_four {d : ℕ} (hd : 4≤d) :
    2*(d : ℝ)^2+1≤centralHalfBinomial d := by
  have hm := Nat.choose_le_middle 3 (2*d-1)
  rw [show (2*d-1)/2=d-1 by omega] at hm
  have hp := monomial_count_three_real (2*d-3)
  rw [show 2*d-3+3-1=2*d-1 by omega] at hp
  have hc : ((2*d-3 : ℕ) : ℝ)=2*(d : ℝ)-3 := by
    rw [Nat.cast_sub (by omega),Nat.cast_mul]
    norm_num
  rw [hc] at hp
  have hmR : ((2*d-1).choose 3 : ℝ)≤centralHalfBinomial d := by exact_mod_cast hm
  have hdR : (4 : ℝ)≤d := by exact_mod_cast hd
  have hs := sq_nonneg ((d : ℝ)-4)
  have ht := mul_nonneg (show (0 : ℝ)≤d-4 by linarith) hs
  nlinarith

theorem top_scalar_shadow_margin {d : ℕ} (hd : 3≤d) :
    (2*(d : ℝ)^2+1)*criticalRatio d+(d.factorial : ℝ)*scalarReserveDensity d<1 := by
  by_cases he : d=3
  · exact small_odd_top_shadow_margin (Or.inl he)
  have hb := centralHalfBinomial_quadratic_lower_four (show 4≤d by omega)
  have hr := criticalRatio_sharp_bound hd
  have hrp := (criticalRatio_bounds (show 2≤d by omega)).1
  have hm := mul_le_mul_of_nonneg_right hb hrp.le
  have hf : (d.factorial : ℝ)≤(2*d).factorial := by
    exact_mod_cast Nat.factorial_le (show d≤2*d by omega)
  have hden : (0 : ℝ)<(2*d).factorial := by positivity
  have hreserve : (d.factorial : ℝ)*scalarReserveDensity d≤1/100 := by
    unfold scalarReserveDensity
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  linarith

end Froberg
