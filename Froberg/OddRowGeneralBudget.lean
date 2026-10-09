module

public import Froberg.OddRowIncidenceBudget

@[expose] public section

noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem eventually_higher_odd_row_budget_of_gap {d b h : ℕ}
    (hd : 3≤d) (hb : 3≤b) (hbd : b≤d) (hh : 0<h)
    (qS qO : ℕ → ℕ) (S O : ℝ)
    (hgap : S*(((h+b-1).choose b : ℝ)*((d-b).factorial : ℝ)⁻¹) +
      O*(((h+(b-1)-1).choose (b-1) : ℝ)*((d-b+1).factorial : ℝ)⁻¹) <
      ((h+b-1).choose b : ℝ)*((2*d-b).factorial : ℝ)⁻¹)
    (hS : Tendsto (fun n : ℕ => (qS n : ℝ)/(n : ℝ)^d) atTop
      (𝓝 S))
    (hO : Tendsto (fun n : ℕ => (qO n : ℝ)/(n : ℝ)^(d-1)) atTop
      (𝓝 O)) :
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
  filter_upwards [(h₁.add h₂).eventually_lt h₃ hgap,
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


end Froberg
