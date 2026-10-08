import Froberg.CoreQuotientLimits

/-! A fixed number of private columns preserves the leading dimensions and
critical quotient slope. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

lemma private_dimension_limits (A T : ℕ → ℝ) {s : ℕ} (hs : 0 < s) (b : ℝ)
    {α τ : ℝ} (hα : 0 < α)
    (hA : Tendsto (fun n : ℕ => A n/(n : ℝ)^s) atTop (𝓝 α))
    (hT : Tendsto (fun n : ℕ => T n/(n : ℝ)^(2*s+1)) atTop (𝓝 τ)) :
    Tendsto (fun n : ℕ => (A n-b)/(n : ℝ)^s) atTop (𝓝 α) ∧
    Tendsto (fun n : ℕ => (T n-b*((n+s).choose (s+1) : ℝ))/(n : ℝ)^(2*s+1)) atTop (𝓝 τ) ∧
    Tendsto (fun n : ℕ => ((T n-b*((n+s).choose (s+1) : ℝ))/(A n-b))/(n : ℝ)^(s+1))
      atTop (𝓝 (τ/α)) := by
  have hb : Tendsto (fun n : ℕ => b/(n : ℝ)^s) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (nat_power_tendsto_atTop s hs)
  have hsmall := (monomial_count_normalized_small_tendsto
    (show s+1<2*s+1 by omega)).const_mul b
  have hAsub : Tendsto (fun n : ℕ => (A n-b)/(n : ℝ)^s) atTop (𝓝 α) := by
    simpa only [sub_div,sub_zero] using hA.sub hb
  have hTsub : Tendsto (fun n : ℕ => (T n-b*((n+s).choose (s+1) : ℝ))/(n : ℝ)^(2*s+1))
      atTop (𝓝 τ) := by
    have he (n : ℕ) : n+(s+1)-1=n+s := by omega
    simpa only [he,mul_zero,sub_zero,sub_div,mul_div_assoc] using hT.sub hsmall
  refine ⟨hAsub,hTsub,?_⟩
  exact normalized_quotient_limit (fun n => A n-b)
    (fun n => T n-b*((n+s).choose (s+1) : ℝ)) hα.ne' s (s+1) hAsub
    (by simpa only [show s+(s+1)=2*s+1 by omega] using hTsub)

end Froberg
