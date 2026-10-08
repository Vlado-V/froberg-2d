import Froberg.CoreCounts

/-! A positive lower bound for the proportion of core variables. -/
noncomputable section
namespace Froberg
open Filter Polynomial
open scoped Topology

theorem eventually_core_lower (R : ℕ → ℕ) (K s : ℕ) (hs : 0 < s)
    (τ c B : ℝ) (hτ : 0 < τ)
    (hR : Tendsto (fun n => (R n : ℝ) / (n : ℝ) ^ s) atTop (𝓝 c))
    (hgap : (K : ℝ) * τ ^ s / (s.factorial : ℝ) < c) :
    ∀ᶠ n : ℕ in atTop, ∀ a f e : ℕ,
      f = K * (a + s - 1).choose s → f + e = R n →
      (e : ℝ) ≤ B * (n : ℝ) ^ (s - 1) → τ * (n : ℝ) < a := by
  have hsmall : Tendsto (fun n : ℕ => B * (n : ℝ) ^ (s - 1) / (n : ℝ) ^ s)
      atTop (𝓝 0) := by
    have hd : (monomial (s - 1) B : Polynomial ℝ).natDegree < s :=
      (natDegree_monomial_le _).trans_lt (by omega)
    simpa only [eval_monomial, coeff_eq_zero_of_natDegree_lt hd] using
      polynomial_div_pow_nat_tendsto (monomial (s - 1) B) s hd.le
  have hlim : Tendsto (fun n : ℕ =>
      ((K * (⌊τ * (n : ℝ)⌋₊ + 1 + s - 1).choose s : ℕ) : ℝ) / (n : ℝ) ^ s)
      atTop (𝓝 ((K : ℝ) * τ ^ s / (s.factorial : ℝ))) := by
    simpa only [Nat.cast_mul, div_eq_mul_inv, mul_assoc] using
      (floor_fraction_monomial_limit τ hτ s).const_mul (K : ℝ)
  have hsum := hlim.add hsmall
  simp only [← add_div, add_zero] at hsum
  have hh := eventually_lt_of_normalized_limits _ _ s _ _ hsum hR hgap
  filter_upwards [hh] with n hn a f e hf hfe he
  have hlarge : ⌊τ * (n : ℝ)⌋₊ + 1 < a := by
    by_contra ha
    have hm := Nat.mul_le_mul_left K (monomial_count_mono_variables (t := s)
      (show a ≤ ⌊τ * (n : ℝ)⌋₊ + 1 by omega))
    have hm' : (f : ℝ) ≤ ((K * (⌊τ * (n : ℝ)⌋₊ + 1 + s - 1).choose s : ℕ) : ℝ) := by
      exact_mod_cast (show f ≤ K * (⌊τ * (n : ℝ)⌋₊ + 1 + s - 1).choose s by omega)
    have hfe' : (f : ℝ) + e = R n := by exact_mod_cast hfe
    linarith
  exact (Nat.lt_floor_add_one _).trans (by exact_mod_cast hlarge)

theorem critical_core_lower_gap {d K h : ℕ} (hd : 3 ≤ d) (hK : 0 < K)
    (hh : h = K * centralHalfBinomial d) :
    (K : ℝ) * (1 / 4 : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) <
      (h : ℝ) * criticalRatio d / ((d - 1).factorial : ℝ) := by
  have hp : (1 / 4 : ℝ) ^ (d - 1) ≤ 1 / 4 := by
    simpa only [pow_one] using pow_le_pow_of_le_one
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1)
      (by omega : 1 ≤ d - 1)
  have hr := (criticalRatio_bounds (d := d) (by omega)).2.2.1
  apply div_lt_div_of_pos_right _ (by exact_mod_cast Nat.factorial_pos (d - 1))
  rw [hh]
  push_cast
  have hg : (1 / 4 : ℝ) ^ (d - 1) < (centralHalfBinomial d : ℝ) * criticalRatio d := by linarith
  have hm := mul_lt_mul_of_pos_left hg (show (0 : ℝ) < K by exact_mod_cast hK)
  nlinarith

theorem exact_counts_core_positive {d K h : ℕ} (hd : 3 ≤ d)
    (hK : 0 < K) (hh : h = K * centralHalfBinomial d)
    (g r : ℕ → ℕ) (hr : ∀ n, 0 < n → lowerCount n d ≤ r n ∧ r n ≤ upperCount n d)
    (hg : Tendsto (fun n => (g n : ℝ) / (n : ℝ) ^ (d - 1)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, ∀ a f e : ℕ,
      f = K * (a + (d - 1) - 1).choose (d - 1) →
      upperCount n d + f + g n + e = r (n + h) →
      (e : ℝ) < countBeta d * (h : ℝ) ^ 2 * (n : ℝ) ^ (d - 2) →
      (n : ℝ) / 4 < a := by
  obtain ⟨hc, _⟩ := critical_increment_below_capacity hd hK hh
  obtain ⟨_, hR⟩ := natural_budget_limit
    (fun n => r (n + h)) (fun n => upperCount n d) g (by omega : 0 < d - 1)
    ((h : ℝ) * criticalRatio d / ((d - 1).factorial : ℝ)) hc
    (rounded_critical_increment_limit' (by omega) h r hr) hg
  have hl := eventually_core_lower (fun n => r (n + h) - upperCount n d - g n)
    K (d - 1) (by omega) (1 / 4) _ (countBeta d * (h : ℝ) ^ 2) (by norm_num) hR
    (critical_core_lower_gap hd hK hh)
  filter_upwards [hl] with n hn a f e hf ht he
  have hres := hn a f e hf (by omega) (by simpa only [show d - 1 - 1 = d - 2 by omega] using he.le)
  linarith

end Froberg
