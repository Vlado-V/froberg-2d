module

public import Froberg.CoreFraction

@[expose] public section

/-! The exact generator counts leave a fixed fraction of variables free. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem exact_critical_generator_counts_core {d K h : ℕ} (hd : 3 ≤ d)
    (hK : 0 < K) (hh : h = K * centralHalfBinomial d)
    (hwidth : countAlpha d * (h : ℝ) ^ 2 + (K : ℝ) / ((d - 2).factorial : ℝ) <
      countBeta d * (h : ℝ) ^ 2)
    (g r : ℕ → ℕ) (hr : ∀ n, 0 < n → lowerCount n d ≤ r n ∧ r n ≤ upperCount n d)
    (hg : Tendsto (fun n => (g n : ℝ) / (n : ℝ) ^ (d - 1)) atTop (𝓝 0)) (lo : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∃ a f e : ℕ, lo ≤ a ∧ a ≤ n ∧
      a ≤ ⌊coreFraction (d - 1) * (n : ℝ)⌋₊ ∧
      f = K * (a + (d - 1) - 1).choose (d - 1) ∧
      upperCount n d + f + g n + e = r (n + h) ∧
      countAlpha d * (h : ℝ) ^ 2 * (n : ℝ) ^ (d - 2) ≤ (e : ℝ) ∧
      (e : ℝ) < countBeta d * (h : ℝ) ^ 2 * (n : ℝ) ^ (d - 2) := by
  have hcounts := exact_critical_generator_counts hd hK hh hwidth g r hr hg lo
  obtain ⟨hc, _⟩ := critical_increment_below_capacity hd hK hh
  obtain ⟨_, hR⟩ := natural_budget_limit
    (fun n => r (n + h)) (fun n => upperCount n d) g (by omega : 0 < d - 1)
    ((h : ℝ) * criticalRatio d / ((d - 1).factorial : ℝ)) hc
    (rounded_critical_increment_limit' (by omega) h r hr) hg
  have hcore := eventually_core_bound (fun n => r (n + h) - upperCount n d - g n)
    K (d - 1) (coreFraction (d - 1)) _ (coreFraction_bounds (by omega)).1 hR
    (critical_core_capacity_gap hd hK hh)
  filter_upwards [hcounts, hcore] with n hn hcn
  obtain ⟨a, f, e, ha₀, ha₁, hf, htotal, helo, hehi⟩ := hn
  exact ⟨a, f, e, ha₀, ha₁, hcn a f hf (by omega), hf, htotal, helo, hehi⟩

theorem free_variables_fraction {s n a : ℕ} (hs : 0 < s) (han : a ≤ n)
    (ha : a ≤ ⌊coreFraction s * (n : ℝ)⌋₊) :
    (n : ℝ) / (4 * (s : ℝ)) ≤ ((n - a : ℕ) : ℝ) := by
  have hp := (coreFraction_bounds hs).1
  have haf : (a : ℝ) ≤ coreFraction s * (n : ℝ) :=
    (show (a : ℝ) ≤ (⌊coreFraction s * (n : ℝ)⌋₊ : ℝ) by exact_mod_cast ha).trans
      (Nat.floor_le (mul_nonneg hp.le (Nat.cast_nonneg n)))
  rw [Nat.cast_sub han]
  unfold coreFraction at haf
  have heq : (n : ℝ) - (1 - 1 / (4 * (s : ℝ))) * n = n / (4 * (s : ℝ)) := by ring
  linarith

end Froberg
