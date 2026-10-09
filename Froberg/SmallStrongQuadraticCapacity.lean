module

public import Froberg.SmallFiniteCapacities
public import Froberg.SmallCrossCapacities

@[expose] public section

/-! The full quadratic block construction has density 1/4. In degrees
three and four it retains enough capacity after intersecting any detector
kernel, so the small quadratic product witness needs no genericity of D. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem small_strong_quadratic_gap {d : ℕ} (hd : d=3 ∨ d=4) :
    countBeta d < ((1/4 : ℝ)-outerColumnRate d^2/2)*
      (if d=3 then 1/2 else 1/16) := by
  have hb := countBeta_le_smallBetaBound (d := d) (by omega) (by omega)
  have hr := small_rate_sq_lt (d := d) (by omega) (by omega)
  rcases hd with rfl | rfl
  all_goals norm_num [smallBetaBound,smallRateBound,smallCriticalUpper,smallCriticalNumerator,
    Nat.choose_eq_factorial_div_factorial] at hb hr ⊢
  all_goals linarith

theorem strong_quadratic_output_limit {d : ℕ} (hd : d=3 ∨ d=4) :
    Tendsto (fun h : ℕ => (((2*(h/2).choose 2-deletedTargetCount d h : ℕ) : ℝ)/(h : ℝ)^2))
      atTop (𝓝 ((1/4 : ℝ)-outerColumnRate d^2/2)) := by
  have hg := small_strong_quadratic_gap hd
  have hb : 0 ≤ countBeta d := by
    unfold countBeta
    have := (countTauFour_pos (d := d) (by omega)).trans_le (countTauFour_le_gamma d)
    positivity
  have hp : 0<(1/4 : ℝ)-outerColumnRate d^2/2 := by
    rcases hd with rfl | rfl <;> norm_num at hg <;> linarith
  have hbase := (half_index_choose_limit 2).const_mul 2
  have hN : Tendsto (fun h : ℕ => ((2*(h/2).choose 2 : ℕ) : ℝ)/(h : ℝ)^2)
      atTop (𝓝 (1/4 : ℝ)) := by
    convert hbase using 1
    · funext h
      simp only [Nat.cast_mul,Nat.cast_ofNat,mul_div_assoc]
    · norm_num
  exact nat_sub_normalized_limit _ _ (by omega) _ _ hN
    (deletedTargetCount_limit (by omega)) (by linarith)

theorem eventually_strong_cubic_diagonal_capacity :
    ∀ᶠ h : ℕ in atTop,∀ᶠ n : ℕ in atTop,∀ r : ℕ,
      (r : ℝ)<countBeta 3*(h : ℝ)^2*(n : ℝ) →
      r≤(2*(h/2).choose 2-deletedTargetCount 3 h)*(n/2) := by
  have hb : 0 ≤ countBeta 3 := by norm_num [countBeta,countGammaTwo,countTauFour]
  have hC := natural_monomial_div_limit 1 (by omega : 0<2) (by omega : 0<1)
  have hgap := small_strong_quadratic_gap (d := 3) (Or.inl rfl)
  norm_num at hC hgap
  simpa only [pow_one] using eventually_exact_product_capacity_of_limits
    (j := 2) (s := 1) (by omega)
    (fun h => 2*(h/2).choose 2-deletedTargetCount 3 h) (fun n => n/2)
    ((1/4 : ℝ)-outerColumnRate 3^2/2) (1/2) (countBeta 3) hb
    (strong_quadratic_output_limit (Or.inl rfl)) (by simpa only [pow_one] using hC) hgap

theorem eventually_strong_quartic_diagonal_capacity :
    ∀ᶠ h : ℕ in atTop,∀ᶠ n : ℕ in atTop,∀ r : ℕ,
      (r : ℝ)<countBeta 4*(h : ℝ)^2*(n : ℝ)^2 →
      r≤(2*(h/2).choose 2-deletedTargetCount 4 h)*((n/2).choose 2/2) := by
  have hb : 0 ≤ countBeta 4 := by norm_num [countBeta,countGammaTwo,countTauFour]
  have hC := paired_monomial_capacity_limit (by omega : 0<2)
  have hgap := small_strong_quadratic_gap (d := 4) (Or.inr rfl)
  norm_num at hC hgap
  exact eventually_exact_product_capacity_of_limits (by omega)
    (fun h => 2*(h/2).choose 2-deletedTargetCount 4 h) (fun n => (n/2).choose 2/2)
    ((1/4 : ℝ)-outerColumnRate 4^2/2) (1/16) (countBeta 4) hb
    (strong_quadratic_output_limit (Or.inr rfl)) hC hgap

end Froberg
