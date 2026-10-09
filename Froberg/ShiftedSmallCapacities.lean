module

public import Froberg.ShiftedCountLimits
public import Froberg.SmallStrongQuadraticCapacity

@[expose] public section

/-! Appendix E capacities with a fixed private-variable reserve and any
fixed number of appended columns. The special output witnesses are unchanged. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

private theorem beta_nonnegative {d : ℕ} (hd : 3≤d) : 0≤countBeta d := by
  have hG := (countTauFour_pos hd).trans_le (countTauFour_le_gamma d)
  unfold countBeta
  positivity

theorem eventually_strong_cubic_diagonal_capacity_shift :
    ∀ᶠ h : ℕ in atTop,∀ z extra : ℕ,∀ᶠ n : ℕ in atTop,
      ⌈countBeta 3*(h : ℝ)^2*((n+z : ℕ) : ℝ)⌉₊+extra≤
        (2*(h/2).choose 2-deletedTargetCount 3 h)*(n/2) := by
  have hC := natural_monomial_div_limit 1 (by omega : 0<2) (by omega : 0<1)
  have hgap := small_strong_quadratic_gap (d := 3) (Or.inl rfl)
  norm_num at hC hgap
  simpa only [pow_one] using eventually_product_capacity_of_limits_shift
    (j := 2) (s := 1) (by omega)
    (fun h => 2*(h/2).choose 2-deletedTargetCount 3 h) (fun n => n/2)
    ((1/4 : ℝ)-outerColumnRate 3^2/2) (1/2) (countBeta 3) (beta_nonnegative (by omega))
    (strong_quadratic_output_limit (Or.inl rfl)) (by simpa only [pow_one] using hC) hgap

theorem eventually_strong_quartic_diagonal_capacity_shift :
    ∀ᶠ h : ℕ in atTop,∀ z extra : ℕ,∀ᶠ n : ℕ in atTop,
      ⌈countBeta 4*(h : ℝ)^2*((n+z : ℕ) : ℝ)^2⌉₊+extra≤
        (2*(h/2).choose 2-deletedTargetCount 4 h)*((n/2).choose 2/2) := by
  have hC := paired_monomial_capacity_limit (by omega : 0<2)
  have hgap := small_strong_quadratic_gap (d := 4) (Or.inr rfl)
  norm_num at hC hgap
  exact eventually_product_capacity_of_limits_shift (by omega)
    (fun h => 2*(h/2).choose 2-deletedTargetCount 4 h) (fun n => (n/2).choose 2/2)
    ((1/4 : ℝ)-outerColumnRate 4^2/2) (1/16) (countBeta 4) (beta_nonnegative (by omega))
    (strong_quadratic_output_limit (Or.inr rfl)) hC hgap

theorem eventually_small_quadratic_diagonal_capacity_shift {d : ℕ} (hd : 5≤d) (hd8 : d≤8) :
    ∀ᶠ h : ℕ in atTop,∀ z extra : ℕ,∀ᶠ n : ℕ in atTop,
      ⌈countBeta d*(h : ℝ)^2*((n+z : ℕ) : ℝ)^(d-2)⌉₊+extra≤
        ((h/2).choose 2-deletedTargetCount d h)*((n/2).choose (d-2)/2) := by
  have hgap : countBeta d < ((1/8 : ℝ)-outerColumnRate d^2/2)*
      (1/(2^(d-2+1)*((d-2).factorial : ℝ))) := by
    simpa only [show d-2+1=d-1 by omega,mul_one_div] using
      small_quadratic_symmetric_capacity hd hd8
  exact eventually_product_capacity_of_limits_shift (by omega)
    (fun h => (h/2).choose 2-deletedTargetCount d h)
    (fun n => (n/2).choose (d-2)/2) _ _ (countBeta d)
    (beta_nonnegative (by omega)) (small_quadratic_diagonal_output_limit hd hd8)
    (paired_monomial_capacity_limit (by omega)) hgap

theorem eventually_small_quadratic_cross_capacity_shift {d : ℕ} (hd : 5≤d) (hd8 : d≤8) :
    ∀ᶠ h : ℕ in atTop,∀ z extra : ℕ,∀ᶠ n : ℕ in atTop,
      ⌈countBeta d*(h : ℝ)^2*((n+z : ℕ) : ℝ)^(d-2)⌉₊+extra≤
        ((2*h/5+2-1).choose 2-deletedTargetCount d h)*(n/2+(d-2)-1).choose (d-2) := by
  have hgap : countBeta d < ((2/25 : ℝ)-outerColumnRate d^2/2)*
      ((1/2 : ℝ)^(d-2)/((d-2).factorial : ℝ)) := by
    simpa only [div_pow,one_pow,mul_one_div,div_div] using
      small_quadratic_cross_capacity hd hd8
  exact eventually_product_capacity_of_limits_shift (by omega)
    (fun h => (2*h/5+2-1).choose 2-deletedTargetCount d h)
    (fun n => (n/2+(d-2)-1).choose (d-2)) _ _ (countBeta d)
    (beta_nonnegative (by omega)) (small_quadratic_cross_output_limit hd hd8)
    (half_monomial_count_limit _) hgap

theorem eventually_quintic_quartic_diagonal_capacity_shift :
    ∀ᶠ h : ℕ in atTop,∀ z extra : ℕ,∀ᶠ n : ℕ in atTop,
      higherGeneratorCount 5 h (n+z) 4+extra≤(h^4/256)*(n/2) := by
  have hA := natural_monomial_div_limit 1 (by omega : 0<256) (by omega : 0<4)
  have hB := natural_monomial_div_limit 1 (by omega : 0<2) (by omega : 0<1)
  have hc := small_fourth_symmetric_capacity (d := 5) (by omega) (by omega)
  norm_num at hc
  have hh := eventually_product_capacity_of_limits_shift (j := 4) (s := 1) (by omega)
    (fun h => h^4/256) (fun n => n/2) (1/256) (1/2) (smallGamma 5)
    (by unfold smallGamma; exact mul_nonneg (by norm_num) (higherCountGamma_pos _ _).le)
    (by simpa using hA) (by simpa using hB) (by norm_num; exact hc)
  simpa only [higherGeneratorCount,smallGamma,show 5-4=1 by omega,pow_one] using hh

theorem eventually_small_quartic_diagonal_capacity_shift {d : ℕ} (hd : 6≤d) (hd8 : d≤8) :
    ∀ᶠ h : ℕ in atTop,∀ z extra : ℕ,∀ᶠ n : ℕ in atTop,
      higherGeneratorCount d h (n+z) 4+extra≤(h^4/256)*((n/2).choose (d-4)/2) := by
  have hA := natural_monomial_div_limit 1 (by omega : 0<256) (by omega : 0<4)
  have hB := paired_monomial_capacity_limit (by omega : 0<d-4)
  have hc := small_fourth_symmetric_capacity (by omega : 5≤d) hd8
  rw [if_neg (by omega : d≠5)] at hc
  have hgap : smallGamma d < (1/256 : ℝ)*(1/(2^(d-4+1)*((d-4).factorial : ℝ))) := by
    convert hc using 1
    rw [pow_succ]
    ring
  simpa only [higherGeneratorCount,smallGamma] using
    eventually_product_capacity_of_limits_shift (by omega : 0<d-4)
      (fun h => h^4/256) (fun n => (n/2).choose (d-4)/2)
      (1/256) (1/(2^(d-4+1)*((d-4).factorial : ℝ))) (smallGamma d)
      (by unfold smallGamma; exact mul_nonneg (by norm_num) (higherCountGamma_pos _ _).le)
      (by simpa using hA) hB hgap

theorem eventually_small_quartic_cross_capacity_shift {d : ℕ} (hd : 5≤d) (hd8 : d≤8) :
    ∀ᶠ h : ℕ in atTop,∀ z extra : ℕ,∀ᶠ n : ℕ in atTop,
      higherGeneratorCount d h (n+z) 4+extra≤
        (h-2*h/5+4-1).choose 4*(n/2+(d-4)-1).choose (d-4) := by
  have hgap : smallGamma d < ((3/5 : ℝ)^4/((4 : ℕ).factorial : ℝ))*
      ((1/2 : ℝ)^(d-4)/((d-4).factorial : ℝ)) := by
    have hc := small_fourth_cross_capacity hd hd8
    convert hc using 1
    norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,mul_one]
    rw [div_pow,one_pow]
    ring
  simpa only [higherGeneratorCount,smallGamma] using
    eventually_product_capacity_of_limits_shift (by omega : 0<d-4)
      (fun h => (h-2*h/5+4-1).choose 4)
      (fun n => (n/2+(d-4)-1).choose (d-4)) _ _ (smallGamma d)
      (by unfold smallGamma; exact mul_nonneg (by norm_num) (higherCountGamma_pos _ _).le)
      (complement_fifths_monomial_limit 4) (half_monomial_count_limit _) hgap

end Froberg
