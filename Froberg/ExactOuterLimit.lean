import Froberg.CoreLimit
import Froberg.ConcreteCounts

/-! The exact count identity supplies the outer-family density. -/
noncomputable section
namespace Froberg
open Filter Polynomial
open scoped Topology

theorem exact_counts_outer_limit {d h : ℕ} (hd : 3 ≤ d)
    (g r f e : ℕ → ℕ)
    (hr : ∀ n,0 < n → lowerCount n d ≤ r n ∧ r n ≤ upperCount n d)
    (hg : Tendsto (fun n => (g n : ℝ)/(n : ℝ)^(d-1)) atTop (𝓝 0))
    (hcounts : ∀ᶠ n : ℕ in atTop,
      upperCount n d+f n+g n+e n=r (n+h) ∧
      (e n : ℝ)<countBeta d*(h : ℝ)^2*(n : ℝ)^(d-2)) :
    Tendsto (fun n : ℕ => (f n : ℝ)/(n : ℝ)^(d-1)) atTop
      (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))) := by
  have heUpper : Tendsto (fun n : ℕ =>
      (countBeta d*(h : ℝ)^2*(n : ℝ)^(d-2))/(n : ℝ)^(d-1)) atTop (𝓝 0) := by
    let P : Polynomial ℝ := monomial (d-2) (countBeta d*(h : ℝ)^2)
    have hp : P.natDegree<d-1 := (natDegree_monomial_le _).trans_lt (by omega)
    simpa only [P,eval_monomial,coeff_eq_zero_of_natDegree_lt hp] using
      polynomial_div_pow_nat_tendsto P (d-1) hp.le
  have he : Tendsto (fun n => (e n : ℝ)/(n : ℝ)^(d-1)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => by positivity) _ heUpper
    filter_upwards [hcounts] with n hn
    exact div_le_div_of_nonneg_right hn.2.le (by positivity)
  have hc := ((rounded_critical_increment_limit' (by omega : 2 ≤ d) h r hr).sub hg).sub he
  simp only [sub_zero] at hc
  apply hc.congr'
  filter_upwards [hcounts] with n hn
  have ht : (upperCount n d : ℝ)+f n+g n+e n=r (n+h) := by exact_mod_cast hn.1
  simp only [← sub_div]
  congr 1
  linarith

theorem exact_conditions_outer_limit {d k h lo : ℕ} (hd : 3 ≤ d)
    (upper : Bool) (a f e : ℕ → ℕ)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper) :
    Tendsto (fun n : ℕ => (f n : ℝ)/(n : ℝ)^(d-1)) atTop
      (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))) := by
  apply exact_counts_outer_limit hd (auxiliaryGeneratorCount d h)
    (fun n => adjacentCriticalCount upper n d) f e
    (fun n _ => adjacentCriticalCount_bounds upper n d) (auxiliaryGeneratorCount_lower_order hd h)
  exact hc.mono fun n hn => ⟨hn.total,hn.quadratic_upper⟩

end Froberg
