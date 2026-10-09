module

public import Froberg.TopShadowMargin
public import Froberg.ScalarReserveCount

@[expose] public section

/-! Exact finite incidence budgets for the augmented top-degree map. -/
noncomputable section
namespace Froberg
open Filter Polynomial
open scoped Topology

theorem eventually_top_incidence_budget {d a b : ℕ} (hd : 3≤d)
    (qF qS : ℕ → ℕ) (cF cS : ℝ)
    (hF : Tendsto (fun m : ℕ => (qF m : ℝ)/(m : ℝ)^(d-1)) atTop (𝓝 cF))
    (hS : Tendsto (fun m : ℕ => (qS m : ℝ)/(m : ℝ)^d) atTop (𝓝 cS))
    (hgap : cF*a+cS*b<(b : ℝ)*(d.factorial : ℝ)⁻¹) :
    ∀ᶠ m : ℕ in atTop,(qF m+a*m)*(a*m)+(qS m+b)*b≤b*(m+d-1).choose d := by
  have hlinear : Tendsto (fun m : ℕ => (m : ℝ)/(m : ℝ)^(d-1)) atTop (𝓝 0) := by
    have hp := polynomial_div_pow_nat_tendsto (X : Polynomial ℝ) (d-1) (by simp; omega)
    simpa only [eval_X,coeff_X,show 1≠d-1 by omega,ite_false] using hp
  have hlin := hlinear.const_mul (a : ℝ)
  have hcon : Tendsto (fun m : ℕ => (b : ℝ)/(m : ℝ)^d) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (nat_power_tendsto_atTop d (by omega))
  have hleft := ((hF.add hlin).mul_const (a : ℝ)).add ((hS.add hcon).mul_const (b : ℝ))
  simp only [add_zero,mul_zero] at hleft
  have hright := (monomial_count_normalized_tendsto d).const_mul (b : ℝ)
  filter_upwards [hleft.eventually_lt hright hgap,eventually_gt_atTop (0 : ℕ)] with m hm hmpos
  have hne : (m : ℝ)≠0 := by exact_mod_cast hmpos.ne'
  have hpow : (m : ℝ)^d=(m : ℝ)^(d-1)*m := by
    rw [←pow_succ,show d-1+1=d by omega]
  have he : (((qF m : ℝ)/(m : ℝ)^(d-1)+(a : ℝ)*((m : ℝ)/(m : ℝ)^(d-1)))*a+
      ((qS m : ℝ)/(m : ℝ)^d+(b : ℝ)/(m : ℝ)^d)*b)=
      (((qF m : ℝ)+a*m)*(a*m)+((qS m : ℝ)+b)*b)/(m : ℝ)^d := by
    rw [hpow]
    field_simp
    <;> ring
  rw [he,←mul_div_assoc] at hm
  have hnat := (div_lt_div_iff_of_pos_right (pow_pos (show (0 : ℝ)<m by exact_mod_cast hmpos) d)).mp hm
  exact_mod_cast hnat.le

end Froberg
