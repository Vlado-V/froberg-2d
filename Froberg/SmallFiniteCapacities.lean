import Froberg.SmallCapacityLimits
import Froberg.SmallDegreeCapacities
import Froberg.QuadraticOutputDimension

/-! The exact integer product capacities of Appendix E, including its
special quadratic/quartic witnesses and its unequal cross split. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

private theorem small_beta_pos {d : ℕ} (hd : 3≤d) : 0<countBeta d := by
  have hG := (countTauFour_pos hd).trans_le (countTauFour_le_gamma d)
  unfold countBeta
  positivity

/-- The special quadratic symmetric-product space fits in the prescribed D. -/
theorem eventually_special_quadratic_output_fits {d : ℕ} (hd : 3≤d) :
    ∀ᶠ h : ℕ in atTop, 5*h^2/32≤quadraticOutputDimension d h := by
  have hA := natural_monomial_div_limit 5 (by omega : 0<32) (by omega : 0<2)
  filter_upwards [eventually_lt_of_normalized_limits _ _ 2 _ _ hA
    (quadraticOutputDimension_limit hd) (by
      have h := quadraticOutputDensity_lower hd
      norm_num at hA ⊢
      linarith)] with h hh
  exact_mod_cast hh.le

/-- The d=3 diagonal E capacity uses all linear scalar forms. -/
theorem eventually_cubic_quadratic_diagonal_capacity :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ n : ℕ in atTop, ∀ r : ℕ,
      (r : ℝ)<countBeta 3*(h : ℝ)^2*(n : ℝ) → r≤(5*h^2/32)*(n/2) := by
  have hA := natural_monomial_div_limit 5 (by omega : 0<32) (by omega : 0<2)
  have hB := natural_monomial_div_limit 1 (by omega : 0<2) (by omega : 0<1)
  have hc := small_quadratic_symmetric_special (d := 3) (Or.inl rfl)
  norm_num at hc
  have hh := eventually_exact_product_capacity_of_limits (j := 2) (s := 1) (by omega)
    (fun h => 5*h^2/32) (fun n => n/2) (5/32) (1/2) (countBeta 3)
    (small_beta_pos (by omega)).le hA (by simpa using hB) (by norm_num; exact hc)
  simpa using hh

/-- The d=4 diagonal E capacity uses the paired quadratic scalar space. -/
theorem eventually_quartic_quadratic_diagonal_capacity :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ n : ℕ in atTop, ∀ r : ℕ,
      (r : ℝ)<countBeta 4*(h : ℝ)^2*(n : ℝ)^2 →
      r≤(5*h^2/32)*((n/2).choose 2/2) := by
  have hA := natural_monomial_div_limit 5 (by omega : 0<32) (by omega : 0<2)
  have hB := paired_monomial_capacity_limit (by omega : 0<2)
  have hc := small_quadratic_symmetric_special (d := 4) (Or.inr rfl)
  norm_num at hc hB
  exact eventually_exact_product_capacity_of_limits (by omega)
    (fun h => 5*h^2/32) (fun n => (n/2).choose 2/2) (5/32) (1/16) (countBeta 4)
    (small_beta_pos (by omega)).le hA hB (by norm_num; exact hc)

/-- The d=5 diagonal G capacity uses all linear scalar forms. -/
theorem eventually_quintic_quartic_diagonal_capacity :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ n : ℕ in atTop,
      higherGeneratorCount 5 h n 4≤(h^4/256)*(n/2) := by
  have hA := natural_monomial_div_limit 1 (by omega : 0<256) (by omega : 0<4)
  have hB := natural_monomial_div_limit 1 (by omega : 0<2) (by omega : 0<1)
  have hc := small_fourth_symmetric_capacity (d := 5) (by omega) (by omega)
  norm_num at hc
  have hh := eventually_product_capacity_of_limits (j := 4) (s := 1) (by omega)
    (fun h => h^4/256) (fun n => n/2) (1/256) (1/2) (smallGamma 5)
    (by unfold smallGamma; exact mul_nonneg (by norm_num) (higherCountGamma_pos _ _).le)
    (by simpa using hA) (by simpa using hB) (by norm_num; exact hc)
  simpa only [higherGeneratorCount,smallGamma,show 5-4=1 by omega,pow_one] using hh

/-- For d=6,7,8 the quartic output witness combines with paired scalar forms. -/
theorem eventually_small_quartic_diagonal_capacity {d : ℕ} (hd : 6≤d) (hd8 : d≤8) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ n : ℕ in atTop,
      higherGeneratorCount d h n 4≤(h^4/256)*((n/2).choose (d-4)/2) := by
  have hA := natural_monomial_div_limit 1 (by omega : 0<256) (by omega : 0<4)
  have hB := paired_monomial_capacity_limit (by omega : 0<d-4)
  have hc := small_fourth_symmetric_capacity (by omega : 5≤d) hd8
  rw [if_neg (by omega : d≠5)] at hc
  have hgap : smallGamma d < (1/256 : ℝ)*(1/(2^(d-4+1)*((d-4).factorial : ℝ))) := by
    convert hc using 1
    rw [pow_succ]
    ring
  simpa only [higherGeneratorCount,smallGamma] using
    eventually_product_capacity_of_limits (by omega : 0<d-4)
      (fun h => h^4/256) (fun n => (n/2).choose (d-4)/2)
      (1/256) (1/(2^(d-4+1)*((d-4).factorial : ℝ))) (smallGamma d)
      (by unfold smallGamma; exact mul_nonneg (by norm_num) (higherCountGamma_pos _ _).le)
      (by simpa using hA) hB hgap

end Froberg
