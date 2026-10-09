module

public import Froberg.AsymptoticCounts
public import Froberg.CountMargin

@[expose] public section

/-! Exact counts at either critical endpoint, with lower-order auxiliary
families and any prescribed fixed lower bound for the core dimension. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem countAlpha_pos {d : ℕ} (hd : 3 ≤ d) : 0 < countAlpha d := by
  have hγ := (countTauFour_pos hd).trans_le (countTauFour_le_gamma d)
  unfold countAlpha
  positivity

theorem rounded_critical_increment_limit' {d : ℕ} (hd : 2 ≤ d) (h : ℕ)
    (r : ℕ → ℕ) (hr : ∀ n, 0 < n → lowerCount n d ≤ r n ∧ r n ≤ upperCount n d) :
    Tendsto (fun n : ℕ => ((r (n + h) : ℝ) - (upperCount n d : ℝ)) / (n : ℝ) ^ (d - 1))
      atTop (𝓝 ((h : ℝ) * criticalRatio d / ((d - 1).factorial : ℝ))) := by
  have hi : (d : ℝ) * h * (criticalRatio d / (d.factorial : ℝ)) =
      (h : ℝ) * criticalRatio d / ((d - 1).factorial : ℝ) := by
    simp only [div_eq_mul_inv]
    rw [inverse_factorial_step (by omega : 0 < d)]
    ring
  rw [← hi]
  exact rounded_critical_increment_limit hd h r hr

theorem critical_increment_below_capacity {d K h : ℕ} (hd : 3 ≤ d)
    (hK : 0 < K) (hh : h = K * centralHalfBinomial d) :
    0 < (h : ℝ) * criticalRatio d / ((d - 1).factorial : ℝ) ∧
      (h : ℝ) * criticalRatio d / ((d - 1).factorial : ℝ) <
        (K : ℝ) / ((d - 1).factorial : ℝ) := by
  have hb := criticalRatio_bounds (d := d) (by omega)
  have hH : (0 : ℝ) < centralHalfBinomial d := by
    exact_mod_cast (show 0 < centralHalfBinomial d by have := centralHalfBinomial_ge_two (d := d) (by omega); omega)
  have hf : (0 : ℝ) < (d - 1).factorial := by exact_mod_cast Nat.factorial_pos (d - 1)
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  rw [hh]
  push_cast
  constructor
  · exact div_pos (mul_pos (mul_pos hKr hH) hb.1) hf
  · apply div_lt_div_of_pos_right _ hf
    have hhρ : (centralHalfBinomial d : ℝ) * criticalRatio d < 1 := by linarith [hb.2.2.2]
    nlinarith [mul_lt_mul_of_pos_left hhρ hKr]

theorem exact_critical_generator_counts {d K h : ℕ} (hd : 3 ≤ d)
    (hK : 0 < K) (hh : h = K * centralHalfBinomial d)
    (hwidth : countAlpha d * (h : ℝ) ^ 2 + (K : ℝ) / ((d - 2).factorial : ℝ) <
      countBeta d * (h : ℝ) ^ 2)
    (g r : ℕ → ℕ) (hr : ∀ n, 0 < n → lowerCount n d ≤ r n ∧ r n ≤ upperCount n d)
    (hg : Tendsto (fun n => (g n : ℝ) / (n : ℝ) ^ (d - 1)) atTop (𝓝 0)) (lo : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∃ a f e : ℕ, lo ≤ a ∧ a ≤ n ∧
      f = K * (a + (d - 1) - 1).choose (d - 1) ∧
      upperCount n d + f + g n + e = r (n + h) ∧
      countAlpha d * (h : ℝ) ^ 2 * (n : ℝ) ^ (d - 2) ≤ (e : ℝ) ∧
      (e : ℝ) < countBeta d * (h : ℝ) ^ 2 * (n : ℝ) ^ (d - 2) := by
  obtain ⟨hc, hcap⟩ := critical_increment_below_capacity hd hK hh
  obtain ⟨hbudget, hR⟩ := natural_budget_limit
    (fun n => r (n + h)) (fun n => upperCount n d) g (by omega : 0 < d - 1)
    ((h : ℝ) * criticalRatio d / ((d - 1).factorial : ℝ)) hc
    (rounded_critical_increment_limit' (by omega) h r hr) hg
  have hcounts := eventually_exact_bounded_counts K (d - 1) lo hK (by omega)
    (fun n => r (n + h) - upperCount n d - g n)
    ((h : ℝ) * criticalRatio d / ((d - 1).factorial : ℝ))
    (countAlpha d * (h : ℝ) ^ 2) (countBeta d * (h : ℝ) ^ 2)
    (mul_nonneg (countAlpha_pos hd).le (sq_nonneg _)) hc hR hcap
    (by simpa only [show d - 1 - 1 = d - 2 by omega] using hwidth)
  filter_upwards [hbudget, hcounts] with n hbn hcn
  obtain ⟨a, f, e, ha₀, ha₁, hf, he, helo, hehi⟩ := hcn
  refine ⟨a, f, e, ha₀, ha₁, hf, by omega, ?_, ?_⟩
  · simpa only [show d - 1 - 1 = d - 2 by omega] using helo
  · simpa only [show d - 1 - 1 = d - 2 by omega] using hehi

theorem count_width_eventually {d : ℕ} (hd : 3 ≤ d) :
    ∃ N : ℕ, ∀ K : ℕ, N ≤ K →
      countAlpha d * ((K * centralHalfBinomial d : ℕ) : ℝ) ^ 2 +
        (K : ℝ) / ((d - 2).factorial : ℝ) <
      countBeta d * ((K * centralHalfBinomial d : ℕ) : ℝ) ^ 2 := by
  have hH : (0 : ℝ) < centralHalfBinomial d := by
    exact_mod_cast (show 0 < centralHalfBinomial d by have := centralHalfBinomial_ge_two (d := d) (by omega); omega)
  have hgap : 0 < (countBeta d - countAlpha d) * (centralHalfBinomial d : ℝ) ^ 2 :=
    mul_pos (sub_pos.mpr (countAlpha_lt_beta hd)) (sq_pos_of_pos hH)
  obtain ⟨N, hN⟩ := eventually_positive_quadratic
    ((countBeta d - countAlpha d) * (centralHalfBinomial d : ℝ) ^ 2)
    (-(((d - 2).factorial : ℝ)⁻¹)) hgap
  refine ⟨N, fun K hK => ?_⟩
  have hp := hN K hK
  push_cast
  simp only [div_eq_mul_inv]
  nlinarith

end Froberg
