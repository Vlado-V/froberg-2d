module

public import Froberg.CoreLimit

@[expose] public section

/-! Normalizing a finite family of convergent positive-total weights. -/
noncomputable section
namespace Froberg
open Filter Finset
open scoped Topology
variable {I : Type*} [Fintype I]

theorem normalized_finite_weights_limit (w : ℕ → I → ℝ) (u : I → ℝ)
    (scale : ℝ) (hscale : 0 < scale) (hu : ∑ i, u i = 1)
    (hw : ∀ i, Tendsto (fun n => w n i) atTop (𝓝 (scale * u i))) :
    (∀ i, Tendsto (fun n => w n i / ∑ j, w n j) atTop (𝓝 (u i))) ∧
      (∀ᶠ n : ℕ in atTop, 0 < ∑ i, w n i) := by
  have hs : Tendsto (fun n => ∑ i, w n i) atTop (𝓝 scale) := by
    simpa only [← mul_sum, hu, mul_one] using tendsto_finsetSum univ (fun i _ => hw i)
  constructor
  · intro i
    have hh := (hw i).div hs hscale.ne'
    rw [mul_div_cancel_left₀ (u i) hscale.ne'] at hh
    apply hh.congr'
    exact Eventually.of_forall fun n => rfl
  · exact hs.eventually (lt_mem_nhds hscale)

theorem normalized_weights_sum (w : I → ℝ) (hw : ∑ i, w i ≠ 0) :
    ∑ i, w i / (∑ j, w j) = 1 := by
  rw [← sum_div, div_self hw]

theorem normalized_scaled_weights_limit (w : ℕ → I → ℝ) (u : I → ℝ)
    (r : ℕ) (scale : ℝ) (hscale : 0 < scale) (hu : ∑ i, u i = 1)
    (hw : ∀ i, Tendsto (fun n => w n i / (n : ℝ) ^ r) atTop (𝓝 (scale * u i))) :
    (∀ i, Tendsto (fun n => w n i / ∑ j, w n j) atTop (𝓝 (u i))) ∧
      (∀ᶠ n : ℕ in atTop, 0 < ∑ i, w n i) := by
  obtain ⟨hr, hp⟩ := normalized_finite_weights_limit
    (fun n i => w n i / (n : ℝ) ^ r) u scale hscale hu hw
  constructor
  · intro i
    apply (hr i).congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [← sum_div]
    exact div_div_div_cancel_right₀ (pow_ne_zero r (by exact_mod_cast hn.ne')) _ _
  · filter_upwards [hp, eventually_gt_atTop (0 : ℕ)] with n hn hn0
    rw [← sum_div] at hn
    exact (div_pos_iff_of_pos_right (pow_pos (by exact_mod_cast hn0 : (0 : ℝ) < n) r)).mp hn

theorem split_monomial_profile_limit (a b : ℕ → ℕ) (σ τ : ℝ) (r i : ℕ) (hi : i ≤ r)
    (ha : Tendsto a atTop atTop) (hb : Tendsto b atTop atTop)
    (har : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 σ))
    (hbr : Tendsto (fun n : ℕ => (b n : ℝ) / n) atTop (𝓝 τ)) :
    Tendsto (fun n : ℕ =>
      ((a n + i - 1).choose i : ℝ) * ((b n + (r - i) - 1).choose (r - i) : ℝ) /
        (n : ℝ) ^ r) atTop
      (𝓝 (σ ^ i * τ ^ (r - i) / ((i.factorial : ℝ) * ((r - i).factorial : ℝ)))) := by
  have h := (scaled_index_monomial_limit a σ i ha har).mul
    (scaled_index_monomial_limit b τ (r - i) hb hbr)
  have hi' : i + (r - i) = r := by omega
  simpa only [div_mul_div_comm, ← pow_add, hi'] using h

theorem complementary_index_ratio (a : ℕ → ℕ) (σ : ℝ)
    (ha : ∀ᶠ n : ℕ in atTop, a n ≤ n)
    (hr : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 σ)) :
    Tendsto (fun n : ℕ => ((n - a n : ℕ) : ℝ) / n) atTop (𝓝 (1 - σ)) := by
  have h := (scaled_power_normalized_limit (1 : ℝ) 1).sub hr
  simp only [one_mul, pow_one] at h
  apply h.congr'
  filter_upwards [ha] with n hn
  rw [Nat.cast_sub hn, sub_div]

theorem complementary_index_atTop (a : ℕ → ℕ) {s : ℕ} (hs : 0 < s)
    (ha : ∀ᶠ n : ℕ in atTop, a n ≤ n ∧ a n ≤ ⌊coreFraction s * (n : ℝ)⌋₊) :
    Tendsto (fun n : ℕ => n - a n) atTop atTop := by
  apply tendsto_atTop.mpr
  intro N
  filter_upwards [ha, eventually_ge_atTop (4 * s * N)] with n hn hN
  have hfree := free_variables_fraction hs hn.1 hn.2
  have hden : (0 : ℝ) < 4 * (s : ℝ) := by positivity
  have hN' : (4 : ℝ) * s * N ≤ n := by exact_mod_cast hN
  have hlow : (N : ℝ) ≤ (n : ℝ) / (4 * (s : ℝ)) :=
    (le_div_iff₀ hden).mpr (by nlinarith)
  exact_mod_cast hlow.trans hfree

end Froberg
