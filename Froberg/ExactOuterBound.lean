module

public import Froberg.ExactOuterLimit

@[expose] public section

/-! The actual outer-family size is eventually below every positive
degree-d allowance, as needed by the final thin-slice comparison. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem exact_counts_outer_below_degree {d k h lo : ℕ} (hd : 3≤d)
    (upper : Bool) (a f e : ℕ → ℕ)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {ξ : ℝ} (hξ : 0<ξ) :
    ∀ᶠ n : ℕ in atTop,(f n : ℝ)≤ξ*(n : ℝ)^d := by
  have hlim : Tendsto (fun n : ℕ => (f n : ℝ)/(n : ℝ)^d) atTop (𝓝 0) := by
    have H := (exact_conditions_outer_limit hd upper a f e hc).div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [div_div,←pow_succ,show d-1+1=d by omega] using H
  filter_upwards [hlim.eventually (gt_mem_nhds hξ),eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  exact ((div_lt_iff₀ (pow_pos (by exact_mod_cast hnpos) d)).mp hn).le

end Froberg
