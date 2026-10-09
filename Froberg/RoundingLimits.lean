module

public import Froberg.CriticalLimits

@[expose] public section

/-! Rounding and finite lower-order auxiliary counts do not change the
leading normalized generator budget. -/
noncomputable section
namespace Froberg
open Polynomial Filter
open scoped Topology

theorem ceil_normalized_limit (f : ℕ → ℝ) {k : ℕ} (hk : 0 < k) (c : ℝ)
    (hf : ∀ᶠ n : ℕ in atTop, 0 ≤ f n)
    (hlim : Tendsto (fun n => f n / (n : ℝ) ^ k) atTop (𝓝 c)) :
    Tendsto (fun n => (⌈f n⌉₊ : ℝ) / (n : ℝ) ^ k) atTop (𝓝 c) := by
  have hlo : ∀ᶠ n : ℕ in atTop, (0 : ℝ) ≤ (⌈f n⌉₊ : ℝ) - f n :=
    Eventually.of_forall fun n => sub_nonneg.mpr (Nat.le_ceil (f n))
  have hhi : ∀ᶠ n : ℕ in atTop, (⌈f n⌉₊ : ℝ) - f n ≤ 1 :=
    hf.mono fun n hn => by
      have hh := Nat.ceil_lt_add_one hn
      linarith
  have he := tendsto_bdd_div_atTop_nhds_zero hlo hhi (nat_power_tendsto_atTop k hk)
  have h := he.add hlim
  simpa only [zero_add, sub_div, sub_add_cancel] using h

theorem ceil_polynomial_lower_order (P : Polynomial ℝ) {k : ℕ} (hk : 0 < k)
    (hP : P.natDegree < k) (hpos : ∀ᶠ n : ℕ in atTop, 0 ≤ P.eval (n : ℝ)) :
    Tendsto (fun n : ℕ => (⌈P.eval (n : ℝ)⌉₊ : ℝ) / (n : ℝ) ^ k) atTop (𝓝 0) := by
  apply ceil_normalized_limit _ hk _ hpos
  simpa only [coeff_eq_zero_of_natDegree_lt hP] using
    polynomial_div_pow_nat_tendsto P k hP.le

theorem ceil_monomial_lower_order {k j : ℕ} (hjk : j < k) (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (⌈a * (n : ℝ) ^ j⌉₊ : ℝ) / (n : ℝ) ^ k) atTop (𝓝 0) := by
  have hP : (monomial j a : Polynomial ℝ).natDegree < k :=
    (natDegree_monomial_le _).trans_lt hjk
  have hpos : ∀ᶠ n : ℕ in atTop, 0 ≤ (monomial j a : Polynomial ℝ).eval (n : ℝ) :=
    Eventually.of_forall fun n => by
      rw [eval_monomial]
      exact mul_nonneg ha (pow_nonneg (Nat.cast_nonneg n) j)
  simpa only [eval_monomial] using ceil_polynomial_lower_order (monomial j a) (by omega) hP hpos

theorem auxiliary_counts_lower_order {ι : Type*} (s : Finset ι) {k : ℕ} (hk : 0 < k)
    (a : ι → ℝ) (j : ι → ℕ) (u : ℕ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hj : ∀ i ∈ s, j i < k) :
    Tendsto (fun n : ℕ =>
      ((u + ∑ i ∈ s, ⌈a i * (n : ℝ) ^ j i⌉₊ : ℕ) : ℝ) / (n : ℝ) ^ k)
      atTop (𝓝 0) := by
  have hu : Tendsto (fun n : ℕ => (u : ℝ) / (n : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (nat_power_tendsto_atTop k hk)
  have hs := tendsto_finsetSum s (fun i hi => ceil_monomial_lower_order (hj i hi) (a i) (ha i hi))
  have hh := hu.add hs
  simpa only [Nat.cast_add, Nat.cast_sum, add_div, Finset.sum_div,
    Finset.sum_const_zero, add_zero] using hh

theorem natural_budget_limit (r q g : ℕ → ℕ) {k : ℕ} (hk : 0 < k) (c : ℝ) (hc : 0 < c)
    (hrq : Tendsto (fun n => ((r n : ℝ) - (q n : ℝ)) / (n : ℝ) ^ k) atTop (𝓝 c))
    (hg : Tendsto (fun n => (g n : ℝ) / (n : ℝ) ^ k) atTop (𝓝 0)) :
    (∀ᶠ n : ℕ in atTop, q n + g n ≤ r n) ∧
    Tendsto (fun n => ((r n - q n - g n : ℕ) : ℝ) / (n : ℝ) ^ k) atTop (𝓝 c) := by
  have hl : Tendsto (fun n => ((r n : ℝ) - (q n : ℝ) - (g n : ℝ)) / (n : ℝ) ^ k)
      atTop (𝓝 c) := by simpa only [sub_div, sub_zero] using hrq.sub hg
  have hpos := hl.eventually (lt_mem_nhds hc)
  have hbudget : ∀ᶠ n : ℕ in atTop, q n + g n ≤ r n := by
    filter_upwards [hpos, eventually_gt_atTop (0 : ℕ)] with n hn hn0
    have hnum := (div_pos_iff_of_pos_right
      (pow_pos (by exact_mod_cast hn0 : (0 : ℝ) < n) k)).mp hn
    have he : (q n : ℝ) + (g n : ℝ) ≤ (r n : ℝ) := by linarith
    exact_mod_cast he
  refine ⟨hbudget, hl.congr' ?_⟩
  filter_upwards [hbudget] with n hn
  rw [Nat.cast_sub (show g n ≤ r n - q n by omega),
    Nat.cast_sub (show q n ≤ r n by omega)]

end Froberg
