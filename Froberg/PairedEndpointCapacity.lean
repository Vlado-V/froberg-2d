import Froberg.PairedCapacity

/-! The paired scalar budget applies uniformly to every chosen subfamily of
an actual lower or upper critical-endpoint increment. -/

noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem eventually_endpoint_paired_capacity {d h : ℕ} (hd : 3 ≤ d) (hh : 0 < h)
    (r : ℕ → ℕ)
    (hr : ∀ n, 0 < n → lowerCount n d ≤ r n ∧ r n ≤ upperCount n d) :
    ∀ᶠ n : ℕ in atTop, ∀ f : ℕ, upperCount n d + f ≤ r (n + h) →
      f ≤ outerColumnCount d h * ((n / 2).choose (d - 1) / 2) := by
  have hc : 0 < (h : ℝ) * criticalRatio d / ((d - 1).factorial : ℝ) :=
    div_pos (mul_pos (by exact_mod_cast hh) (criticalRatio_bounds (by omega : 2 ≤ d)).1)
      (by exact_mod_cast Nat.factorial_pos (d - 1))
  have hzero : Tendsto (fun n : ℕ => ((0 : ℕ) : ℝ) / (n : ℝ) ^ (d - 1))
      atTop (𝓝 (0 : ℝ)) := by simpa only [Nat.cast_zero, zero_div] using tendsto_const_nhds
  have hbudget := (natural_budget_limit (fun n => r (n + h)) (fun n => upperCount n d)
    (fun _ => 0) (by omega : 0 < d - 1) _ hc
    (rounded_critical_increment_limit' (by omega) h r hr) hzero).2
  simp only [Nat.sub_zero] at hbudget
  filter_upwards [eventually_critical_paired_capacity hd hh _ hbudget] with n hn f hf
  exact (show f ≤ r (n + h) - upperCount n d by omega).trans hn

end Froberg
