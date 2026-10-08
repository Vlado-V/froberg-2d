import Froberg.ProductCapacityLimits
import Froberg.ScalarSeparationAsymptotic

/-! Exact product capacities from two strictly separated leading coefficients. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem eventually_product_capacity_of_limits {j s : ℕ} (hs : 0<s)
    (A B : ℕ → ℕ) (a b γ : ℝ) (hγ : 0≤γ)
    (hA : Tendsto (fun h : ℕ => (A h : ℝ)/(h : ℝ)^j) atTop (𝓝 a))
    (hB : Tendsto (fun n : ℕ => (B n : ℝ)/(n : ℝ)^s) atTop (𝓝 b))
    (hgap : γ<a*b) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ n : ℕ in atTop,
      ⌈γ*(h : ℝ)^j*(n : ℝ)^s⌉₊≤A h*B n := by
  have hl := hA.mul_const b
  filter_upwards [hl.eventually (lt_mem_nhds hgap),eventually_gt_atTop (0 : ℕ)] with h hh hh0
  have hp : 0<(h : ℝ)^j := pow_pos (by exact_mod_cast hh0) _
  have hg : γ*(h : ℝ)^j < (A h : ℝ)*b := by
    have he : (A h : ℝ)/(h : ℝ)^j*b = ((A h : ℝ)*b)/(h : ℝ)^j := by ring
    rw [he] at hh
    exact (lt_div_iff₀ hp).mp hh
  have hF := ceil_normalized_limit (fun n : ℕ => γ*(h : ℝ)^j*(n : ℝ)^s)
    hs (γ*(h : ℝ)^j) (Eventually.of_forall fun n => by positivity)
    (scaled_power_normalized_limit _ _)
  have hG : Tendsto (fun n : ℕ => ((A h*B n : ℕ) : ℝ)/(n : ℝ)^s)
      atTop (𝓝 ((A h : ℝ)*b)) := by
    simpa only [Nat.cast_mul,mul_div_assoc] using hB.const_mul (A h : ℝ)
  filter_upwards [eventually_lt_of_normalized_limits _ _ s _ _ hF hG hg] with n hn
  exact_mod_cast hn.le

theorem eventually_exact_product_capacity_of_limits {j s : ℕ} (hs : 0<s)
    (A B : ℕ → ℕ) (a b γ : ℝ) (hγ : 0≤γ)
    (hA : Tendsto (fun h : ℕ => (A h : ℝ)/(h : ℝ)^j) atTop (𝓝 a))
    (hB : Tendsto (fun n : ℕ => (B n : ℝ)/(n : ℝ)^s) atTop (𝓝 b))
    (hgap : γ<a*b) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ n : ℕ in atTop, ∀ r : ℕ,
      (r : ℝ)<γ*(h : ℝ)^j*(n : ℝ)^s → r≤A h*B n := by
  filter_upwards [eventually_product_capacity_of_limits hs A B a b γ hγ hA hB hgap] with h hh
  filter_upwards [hh] with n hn
  intro r hr
  apply le_trans _ hn
  exact_mod_cast hr.le.trans (Nat.le_ceil _)

end Froberg
