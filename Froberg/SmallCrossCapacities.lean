module

public import Froberg.SmallCapacityLimits
public import Froberg.SmallDegreeCapacities

@[expose] public section

/-! The exact paired diagonal capacity and unequal cross-product capacities
for the intermediate E and G families in degrees five through eight. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

private theorem beta_nonnegative {d : ℕ} (hd : 3≤d) : 0≤countBeta d := by
  have hG := (countTauFour_pos hd).trans_le (countTauFour_le_gamma d)
  unfold countBeta
  positivity

theorem small_quadratic_diagonal_output_limit {d : ℕ} (hd : 5≤d) (hd8 : d≤8) :
    Tendsto (fun h : ℕ => (((h/2).choose 2-deletedTargetCount d h : ℕ) : ℝ)/(h : ℝ)^2)
      atTop (𝓝 ((1/8 : ℝ)-outerColumnRate d^2/2)) := by
  have hc := small_quadratic_symmetric_capacity hd hd8
  have hp : 0<(1/8 : ℝ)-outerColumnRate d^2/2 := by
    have hh : 0<((1/8 : ℝ)-outerColumnRate d^2/2)/(2^(d-1)*((d-2).factorial : ℝ)) :=
      lt_of_le_of_lt (beta_nonnegative (by omega)) hc
    exact (div_pos_iff_of_pos_right (by positivity)).mp hh
  have hN := half_index_choose_limit 2
  norm_num at hN
  exact nat_sub_normalized_limit _ _ (by omega) _ _ hN
    (deletedTargetCount_limit (by omega)) (by linarith)

theorem eventually_small_quadratic_diagonal_capacity {d : ℕ} (hd : 5≤d) (hd8 : d≤8) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ n : ℕ in atTop, ∀ r : ℕ,
      (r : ℝ)<countBeta d*(h : ℝ)^2*(n : ℝ)^(d-2) →
      r≤((h/2).choose 2-deletedTargetCount d h)*((n/2).choose (d-2)/2) := by
  have hgap : countBeta d < ((1/8 : ℝ)-outerColumnRate d^2/2)*
      (1/(2^(d-2+1)*((d-2).factorial : ℝ))) := by
    simpa only [show d-2+1=d-1 by omega,mul_one_div] using
      small_quadratic_symmetric_capacity hd hd8
  exact eventually_exact_product_capacity_of_limits (by omega)
    (fun h => (h/2).choose 2-deletedTargetCount d h)
    (fun n => (n/2).choose (d-2)/2) _ _ (countBeta d)
    (beta_nonnegative (by omega)) (small_quadratic_diagonal_output_limit hd hd8)
    (paired_monomial_capacity_limit (by omega)) hgap

theorem small_quadratic_cross_output_limit {d : ℕ} (hd : 5≤d) (hd8 : d≤8) :
    Tendsto (fun h : ℕ => (((2*h/5+2-1).choose 2-deletedTargetCount d h : ℕ) : ℝ)/(h : ℝ)^2)
      atTop (𝓝 ((2/25 : ℝ)-outerColumnRate d^2/2)) := by
  have hc := small_quadratic_cross_capacity hd hd8
  have hp : 0<(2/25 : ℝ)-outerColumnRate d^2/2 := by
    have hh : 0<((2/25 : ℝ)-outerColumnRate d^2/2)/(2^(d-2)*((d-2).factorial : ℝ)) :=
      lt_of_le_of_lt (beta_nonnegative (by omega)) hc
    exact (div_pos_iff_of_pos_right (by positivity)).mp hh
  have hN := natural_fraction_monomial_limit (by omega : 0<2) (by omega : 0<5) 2
  norm_num at hN
  exact nat_sub_normalized_limit _ _ (by omega) _ _ hN
    (deletedTargetCount_limit (by omega)) (by linarith)

theorem eventually_small_quadratic_cross_capacity {d : ℕ} (hd : 5≤d) (hd8 : d≤8) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ n : ℕ in atTop, ∀ r : ℕ,
      (r : ℝ)<countBeta d*(h : ℝ)^2*(n : ℝ)^(d-2) →
      r≤((2*h/5+2-1).choose 2-deletedTargetCount d h)*(n/2+(d-2)-1).choose (d-2) := by
  have hgap : countBeta d < ((2/25 : ℝ)-outerColumnRate d^2/2)*
      ((1/2 : ℝ)^(d-2)/((d-2).factorial : ℝ)) := by
    simpa only [div_pow,one_pow,mul_one_div,div_div] using
      small_quadratic_cross_capacity hd hd8
  exact eventually_exact_product_capacity_of_limits (by omega)
    (fun h => (2*h/5+2-1).choose 2-deletedTargetCount d h)
    (fun n => (n/2+(d-2)-1).choose (d-2)) _ _ (countBeta d)
    (beta_nonnegative (by omega)) (small_quadratic_cross_output_limit hd hd8)
    (half_monomial_count_limit _) hgap

theorem eventually_small_quartic_cross_capacity {d : ℕ} (hd : 5≤d) (hd8 : d≤8) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ n : ℕ in atTop,
      higherGeneratorCount d h n 4≤(h-2*h/5+4-1).choose 4*(n/2+(d-4)-1).choose (d-4) := by
  have hgap : smallGamma d < ((3/5 : ℝ)^4/((4 : ℕ).factorial : ℝ))*
      ((1/2 : ℝ)^(d-4)/((d-4).factorial : ℝ)) := by
    have hc := small_fourth_cross_capacity hd hd8
    convert hc using 1
    norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,mul_one]
    rw [div_pow,one_pow]
    ring
  simpa only [higherGeneratorCount,smallGamma] using
    eventually_product_capacity_of_limits (by omega : 0<d-4)
      (fun h => (h-2*h/5+4-1).choose 4)
      (fun n => (n/2+(d-4)-1).choose (d-4)) _ _ (smallGamma d)
      (by unfold smallGamma; exact mul_nonneg (by norm_num) (higherCountGamma_pos _ _).le)
      (complement_fifths_monomial_limit 4) (half_monomial_count_limit _) hgap

end Froberg
