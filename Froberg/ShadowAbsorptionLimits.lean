module

public import Froberg.ShadowErrorAbsorption
public import Froberg.AsymptoticCounts

@[expose] public section

/-! # Eventual absorption of the finite B.2 errors -/

noncomputable section
namespace Froberg
open Filter
open scoped Topology

/-- Quotients of polynomially normalized sequences have the expected normalization. -/
theorem normalized_quotient_limit (A B : ℕ → ℝ) {a b : ℝ} (ha : a ≠ 0) (k l : ℕ)
    (hA : Tendsto (fun n : ℕ => A n / (n : ℝ) ^ k) atTop (𝓝 a))
    (hB : Tendsto (fun n : ℕ => B n / (n : ℝ) ^ (k + l)) atTop (𝓝 b)) :
    Tendsto (fun n : ℕ => (B n / A n) / (n : ℝ) ^ l) atTop (𝓝 (b / a)) := by
  apply (hB.div hA ha).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  dsimp only [Pi.div_apply]
  by_cases hAn : A n = 0
  · simp [hAn]
  · rw [pow_add]
    field_simp

theorem normalized_limit_eventually_pos (A : ℕ → ℝ) {a : ℝ} (ha : 0 < a) (k : ℕ)
    (hA : Tendsto (fun n : ℕ => A n / (n : ℝ) ^ k) atTop (𝓝 a)) :
    ∀ᶠ n : ℕ in atTop, 0 < A n := by
  filter_upwards [hA.eventually (lt_mem_nhds ha), eventually_gt_atTop (0 : ℕ)] with n hn hn0
  exact (div_pos_iff_of_pos_right (pow_pos (by exact_mod_cast hn0) k)).mp hn

/-- In codimension at least `δ n^s`, both the target discrepancy and exceptional
projection error are smaller than any fixed positive part of the shadow surplus. -/
theorem far_shadow_gap_eventually (A T₀ D E : ℕ → ℝ) (s : ℕ)
    {a t c δ g : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hg : g < c * (t / a))
    (hA : Tendsto (fun n : ℕ => A n / (n : ℝ) ^ s) atTop (𝓝 a))
    (hT : Tendsto (fun n : ℕ => T₀ n / (n : ℝ) ^ (2 * s + 1)) atTop (𝓝 t))
    (hD : Tendsto (fun n : ℕ => D n / (n : ℝ) ^ (2 * s + 1)) atTop (𝓝 0))
    (hE : Tendsto (fun n : ℕ => E n / (n : ℝ) ^ (s + 1)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      g * (n : ℝ) ^ (s + 1) + E n +
        D n / A n * (1 + A n / (δ * (n : ℝ) ^ s)) ≤ c * (T₀ n / A n) := by
  have hT' : Tendsto (fun n : ℕ => (T₀ n / A n) / (n : ℝ) ^ (s + 1))
      atTop (𝓝 (t / a)) := by
    apply normalized_quotient_limit A T₀ ha.ne' s (s + 1) hA
    simpa only [show s + (s + 1) = 2 * s + 1 by omega] using hT
  have hD' : Tendsto (fun n : ℕ => (D n / A n) / (n : ℝ) ^ (s + 1))
      atTop (𝓝 0) := by
    have h := normalized_quotient_limit A D ha.ne' s (s + 1) hA
      (by simpa only [show s + (s + 1) = 2 * s + 1 by omega] using hD)
    simpa only [zero_div] using h
  have hAδ : Tendsto (fun n : ℕ => A n / (δ * (n : ℝ) ^ s)) atTop (𝓝 (a / δ)) := by
    convert hA.div_const δ using 1
    ext n
    ring
  have hleft : Tendsto (fun n : ℕ =>
      (g * (n : ℝ) ^ (s + 1) + E n +
        D n / A n * (1 + A n / (δ * (n : ℝ) ^ s))) / (n : ℝ) ^ (s + 1))
      atTop (𝓝 g) := by
    have h := ((scaled_power_normalized_limit g (s + 1)).add hE).add
      (hD'.mul ((tendsto_const_nhds (x := (1 : ℝ))).add hAδ))
    simp only [add_zero, zero_mul] at h
    convert h using 1
    ext n
    ring
  have hright : Tendsto (fun n : ℕ => c * (T₀ n / A n) / (n : ℝ) ^ (s + 1))
      atTop (𝓝 (c * (t / a))) := by
    simpa only [mul_div_assoc] using hT'.const_mul c
  exact (eventually_lt_of_normalized_limits _ _ (s + 1) g _ hleft hright hg).mono
    (fun _ h => h.le)

/-- At codimension at most `δ n^s`, the quadratic missing-target estimate
fits inside the total-target surplus whenever `Hδ+g<t/a`. -/
theorem near_shadow_gap_eventually (A T₀ : ℕ → ℝ) (s : ℕ)
    {a t H δ g : ℝ} (ha : 0 < a) (hg : H * δ + g < t / a)
    (hA : Tendsto (fun n : ℕ => A n / (n : ℝ) ^ s) atTop (𝓝 a))
    (hT : Tendsto (fun n : ℕ => T₀ n / (n : ℝ) ^ (2 * s + 1)) atTop (𝓝 t)) :
    ∀ᶠ n : ℕ in atTop,
      (H * n) * (δ * (n : ℝ) ^ s) + g * (n : ℝ) ^ (s + 1) ≤ T₀ n / A n := by
  have hT' : Tendsto (fun n : ℕ => (T₀ n / A n) / (n : ℝ) ^ (s + 1))
      atTop (𝓝 (t / a)) := by
    apply normalized_quotient_limit A T₀ ha.ne' s (s + 1) hA
    simpa only [show s + (s + 1) = 2 * s + 1 by omega] using hT
  have h := eventually_lt_of_normalized_limits
    (fun n : ℕ => (H * δ + g) * (n : ℝ) ^ (s + 1)) (fun n : ℕ => T₀ n / A n)
    (s + 1) (H * δ + g) (t / a)
    (scaled_power_normalized_limit _ _) hT' hg
  refine h.mono fun n hn => ?_
  convert hn.le using 1
  rw [pow_succ]
  ring

end Froberg
