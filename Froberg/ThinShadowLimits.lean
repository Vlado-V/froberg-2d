import Froberg.ShadowAbsorptionLimits

/-! The strict surplus dominates the thin deficit and all source overhead. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem thin_shadow_eventual_budget (A J : ℕ → ℝ) (s : ℕ) (α g : ℝ)
    (hα : 0 < α) (hg : 0 < g)
    (hA : Tendsto (fun n : ℕ => A n/(n : ℝ)^s) atTop (𝓝 α))
    (hJ : Tendsto (fun n : ℕ => J n/(n : ℝ)^(2*s+1)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      A n+(g/2)*(n : ℝ)^(s+1) ≤ g*(n : ℝ)^(s+1) ∧
      A n+J n/A n ≤ g*(n : ℝ)^(s+1) := by
  have hA0 : Tendsto (fun n : ℕ => A n/(n : ℝ)^(s+1)) atTop (𝓝 0) := by
    have h := hA.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Pi.div_apply,div_div,pow_succ] using h
  have hJA : Tendsto (fun n : ℕ => (J n/A n)/(n : ℝ)^(s+1)) atTop (𝓝 0) := by
    have h := normalized_quotient_limit A J hα.ne' s (s+1) hA
      (by simpa only [show s+(s+1)=2*s+1 by omega] using hJ)
    simpa only [zero_div] using h
  have hhalf := eventually_lt_of_normalized_limits A
    (fun n : ℕ => (g/2)*(n : ℝ)^(s+1)) (s+1) 0 (g/2)
    hA0 (scaled_power_normalized_limit _ _) (by positivity)
  have hsum : Tendsto (fun n : ℕ => (A n+J n/A n)/(n : ℝ)^(s+1))
      atTop (𝓝 0) := by
    simpa only [add_div,add_zero] using hA0.add hJA
  have hfull := eventually_lt_of_normalized_limits (fun n => A n+J n/A n)
    (fun n : ℕ => g*(n : ℝ)^(s+1)) (s+1) 0 g
    hsum (scaled_power_normalized_limit _ _) hg
  filter_upwards [hhalf,hfull] with n hn hm
  exact ⟨by linarith,hm.le⟩

end Froberg
