import Froberg.OddRowBinomialBudget
import Froberg.ScalarSeparationAsymptotic

/-! The literal two-family incidence inequalities for all higher odd rows. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

/-- The ratio of adjacent homogeneous dimensions, without division. -/
theorem consecutive_monomial_counts {h b : ℕ} (hh : 0<h) (hb : 0<b) :
    ((h : ℝ)+b-1)*((h+(b-1)-1).choose (b-1) : ℝ) =
      ((h+b-1).choose b : ℝ)*b := by
  have he := Nat.add_one_mul_choose_eq (h+b-2) (b-1)
  rw [show h+b-2+1=h+b-1 by omega,show b-1+1=b by omega] at he
  have hh' : ((h+b-1 : ℕ) : ℝ)=(h : ℝ)+b-1 := by
    rw [Nat.cast_sub (by omega),Nat.cast_add,Nat.cast_one]
  rw [show h+(b-1)-1=h+b-2 by omega,←hh']
  exact_mod_cast he

theorem odd_row_factorial_gap {d b h : ℕ} (hd : 3≤d) (hb : 3≤b) (hbd : b≤d)
    (hh : 0<h) :
    (criticalRatio d/(d.factorial : ℝ))*
        (((h+b-1).choose b : ℝ)*((d-b).factorial : ℝ)⁻¹) +
      ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))*
        (((h+(b-1)-1).choose (b-1) : ℝ)*((d-b+1).factorial : ℝ)⁻¹) <
      ((h+b-1).choose b : ℝ)*((2*d-b).factorial : ℝ)⁻¹ := by
  have hp : (0 : ℝ)<(h+b-1).choose b := by
    exact_mod_cast Nat.choose_pos (show b≤h+b-1 by omega)
  have hden : (0 : ℝ)<(h : ℝ)+b-1 := by
    have : (0 : ℝ)<h := by exact_mod_cast hh
    have : (3 : ℝ)≤b := by exact_mod_cast hb
    linarith
  have he := consecutive_monomial_counts hh (show 0<b by omega)
  have hg := oddRow_leading_ratio_lt hd hb hbd hh
  rw [choose_real_factorial (show d-1≤2*d-b by omega),
    choose_real_factorial (show d≤2*d-b by omega),
    show 2*d-b-(d-1)=d-b+1 by omega,
    show 2*d-b-d=d-b by omega] at hg
  have htarget : (0 : ℝ)<(2*d-b).factorial := by positivity
  apply (mul_lt_mul_iff_left₀ htarget).mp
  have hscaled := mul_lt_mul_of_pos_right hg hp
  have hsolve : ((h+(b-1)-1).choose (b-1) : ℝ)=
      ((h+b-1).choose b : ℝ)*b/((h : ℝ)+b-1) := by
    apply (eq_div_iff hden.ne').mpr
    simpa only [mul_comm] using he
  rw [hsolve]
  convert hscaled using 1 <;> field_simp [factorial_real_ne_zero,hden.ne'] <;> ring

/-- The finite two-family budget includes the dimensions of the source spaces
in addition to the prescribed scalar and outer-column family sizes. -/
theorem eventually_higher_odd_row_budget {d b h : ℕ}
    (hd : 3≤d) (hb : 3≤b) (hbd : b≤d) (hh : 0<h)
    (qS qO : ℕ → ℕ)
    (hS : Tendsto (fun n : ℕ => (qS n : ℝ)/(n : ℝ)^d) atTop
      (𝓝 (criticalRatio d/(d.factorial : ℝ))))
    (hO : Tendsto (fun n : ℕ => (qO n : ℝ)/(n : ℝ)^(d-1)) atTop
      (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ)))) :
    ∀ᶠ n : ℕ in atTop,
      (qS n+(h+b-1).choose b*(n+(d-b)-1).choose (d-b))*
          ((h+b-1).choose b*(n+(d-b)-1).choose (d-b)) +
        (qO n+(h+(b-1)-1).choose (b-1)*(n+(d-b+1)-1).choose (d-b+1))*
          ((h+(b-1)-1).choose (b-1)*(n+(d-b+1)-1).choose (d-b+1)) ≤
        (h+b-1).choose b*(n+(2*d-b)-1).choose (2*d-b) := by
  let A : ℝ := (h+b-1).choose b
  let B : ℝ := (h+(b-1)-1).choose (b-1)
  have h₁ := (hS.add ((monomial_count_normalized_small_tendsto
      (show d-b<d by omega)).const_mul A)).mul
    ((monomial_count_normalized_tendsto (d-b)).const_mul A)
  have h₂ := (hO.add ((monomial_count_normalized_small_tendsto
      (show d-b+1<d-1 by omega)).const_mul B)).mul
    ((monomial_count_normalized_tendsto (d-b+1)).const_mul B)
  have h₃ := (monomial_count_normalized_tendsto (2*d-b)).const_mul A
  simp only [mul_zero,add_zero] at h₁ h₂
  filter_upwards [(h₁.add h₂).eventually_lt h₃ (odd_row_factorial_gap hd hb hbd hh),
    eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  have hnR : (0 : ℝ)<n := by exact_mod_cast hnpos
  have hp₁ : (n : ℝ)^d*(n : ℝ)^(d-b)=(n : ℝ)^(2*d-b) := by
    rw [←pow_add,show d+(d-b)=2*d-b by omega]
  have hp₂ : (n : ℝ)^(d-1)*(n : ℝ)^(d-b+1)=(n : ℝ)^(2*d-b) := by
    rw [←pow_add,show d-1+(d-b+1)=2*d-b by omega]
  have heq₁ : ((qS n : ℝ)/(n : ℝ)^d+A*(((n+(d-b)-1).choose (d-b) : ℝ)/(n : ℝ)^d))*
      (A*(((n+(d-b)-1).choose (d-b) : ℝ)/(n : ℝ)^(d-b))) =
      (((qS n : ℝ)+A*(n+(d-b)-1).choose (d-b))*(A*(n+(d-b)-1).choose (d-b)))/
        (n : ℝ)^(2*d-b) := by
    rw [←hp₁]
    field_simp
  have heq₂ : ((qO n : ℝ)/(n : ℝ)^(d-1)+B*(((n+(d-b+1)-1).choose (d-b+1) : ℝ)/(n : ℝ)^(d-1)))*
      (B*(((n+(d-b+1)-1).choose (d-b+1) : ℝ)/(n : ℝ)^(d-b+1))) =
      (((qO n : ℝ)+B*(n+(d-b+1)-1).choose (d-b+1))*(B*(n+(d-b+1)-1).choose (d-b+1)))/
        (n : ℝ)^(2*d-b) := by
    rw [←hp₂]
    field_simp
  rw [heq₁,heq₂,←add_div,←mul_div_assoc] at hn
  have hfin := ((div_lt_div_iff_of_pos_right (pow_pos hnR (2*d-b))).mp hn).le
  dsimp only [A,B] at hfin
  exact_mod_cast hfin

/-- The upper odd row has only the outer family. -/
theorem odd_endpoint_factorial_gap {d h : ℕ} (hd : 3≤d) (hh : 0<h) :
    ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))*((h+d-1).choose d : ℝ) <
      ((h+(d+1)-1).choose (d+1) : ℝ)*((d-1).factorial : ℝ)⁻¹ := by
  have hp : (0 : ℝ)<(h+(d+1)-1).choose (d+1) := by
    exact_mod_cast Nat.choose_pos (show d+1≤h+(d+1)-1 by omega)
  have he := consecutive_monomial_counts hh (show 0<d+1 by omega)
  have hg := oddEndpoint_leading_ratio_lt hd hh
  have hden : (0 : ℝ)<(h : ℝ)+d := by
    have : (0 : ℝ)<h := by exact_mod_cast hh
    positivity
  have hsolve : ((h+d-1).choose d : ℝ)=
      ((h+(d+1)-1).choose (d+1) : ℝ)*((d : ℝ)+1)/((h : ℝ)+d) := by
    apply (eq_div_iff hden.ne').mpr
    simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] at he
    convert he using 1 <;> ring
  apply (mul_lt_mul_iff_left₀ (show (0 : ℝ)<(d-1).factorial by positivity)).mp
  have hs := mul_lt_mul_of_pos_right hg hp
  rw [hsolve]
  convert hs using 1 <;> field_simp [factorial_real_ne_zero,hden.ne'] <;> ring

theorem eventually_upper_odd_row_budget {d h : ℕ} (hd : 3≤d) (hh : 0<h)
    (qO : ℕ → ℕ)
    (hO : Tendsto (fun n : ℕ => (qO n : ℝ)/(n : ℝ)^(d-1)) atTop
      (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ)))) :
    ∀ᶠ n : ℕ in atTop,
      (qO n+(h+d-1).choose d)*(h+d-1).choose d ≤
        (h+(d+1)-1).choose (d+1)*(n+(d-1)-1).choose (d-1) := by
  have hc : Tendsto (fun n : ℕ => ((h+d-1).choose d : ℝ)/(n : ℝ)^(d-1))
      atTop (𝓝 0) := by
    have he := (monomial_count_normalized_small_tendsto
      (show 0<d-1 by omega)).const_mul ((h+d-1).choose d : ℝ)
    simpa only [Nat.add_zero,Nat.choose_zero_right,Nat.cast_one,mul_zero,mul_one_div] using he
  have hl := (hO.add hc).mul_const ((h+d-1).choose d : ℝ)
  have hr := (monomial_count_normalized_tendsto (d-1)).const_mul
    ((h+(d+1)-1).choose (d+1) : ℝ)
  simp only [add_zero] at hl
  filter_upwards [hl.eventually_lt hr (odd_endpoint_factorial_gap hd hh),
    eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  have hnR : (0 : ℝ)<n := by exact_mod_cast hnpos
  rw [←add_div,div_mul_eq_mul_div,←mul_div_assoc] at hn
  exact_mod_cast ((div_lt_div_iff_of_pos_right (pow_pos hnR (d-1))).mp hn).le

end Froberg
