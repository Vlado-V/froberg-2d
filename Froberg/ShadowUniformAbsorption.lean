module

public import Froberg.ShadowAbsorptionLimits
public import Froberg.ScalarSeparationAsymptotic

@[expose] public section

/-! # Uniform finite-size shadow surplus

The geometric estimates enter only as explicit lower bounds on the image
size. This file proves their numerical combination and the lower-order
estimates for the concrete exceptional-set and target-discrepancy errors.
-/

noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem exceptional_projection_error_lower_order (C : ℝ) (s : ℕ) :
    Tendsto (fun n : ℕ => C * ((n + s - 1).choose s : ℝ) / (n : ℝ) ^ (s + 1))
      atTop (𝓝 0) := by
  simpa only [mul_div_assoc, mul_zero] using
    (monomial_count_normalized_small_tendsto (show s < s + 1 by omega)).const_mul C

theorem target_discrepancy_error_lower_order (C : ℝ) {s : ℕ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => C * n * ((n + (2 * s - 1) - 1).choose (2 * s - 1) : ℝ) /
      (n : ℝ) ^ (2 * s + 1)) atTop (𝓝 0) := by
  have h := (monomial_count_normalized_small_tendsto
    (show 2 * s - 1 < 2 * s by omega)).const_mul C
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [pow_succ]
  field_simp

/-- Combining the two geometric estimates yields one positive uniform
`n^(s+1) min(ℓ,A-ℓ)` surplus. -/
theorem uniform_shadow_surplus {ι : Type*} (size : ι → ℝ)
    (A T₀ T D E : ℕ → ℝ) (I : ℕ → ι → ℝ) (s : ℕ)
    {a t c H : ℝ} (ha : 0 < a) (ht : 0 < t) (hc : 0 < c) (hH : 0 ≤ H)
    (hA : Tendsto (fun n => A n / (n : ℝ) ^ s) atTop (𝓝 a))
    (hT₀ : Tendsto (fun n => T₀ n / (n : ℝ) ^ (2 * s + 1)) atTop (𝓝 t))
    (hD : Tendsto (fun n => D n / (n : ℝ) ^ (2 * s + 1)) atTop (𝓝 0))
    (hE : Tendsto (fun n => E n / (n : ℝ) ^ (s + 1)) atTop (𝓝 0))
    (hbudget : ∀ᶠ n : ℕ in atTop, T₀ n ≤ T n ∧ T n - T₀ n ≤ D n ∧ 0 ≤ D n)
    (hshadow : ∀ᶠ n : ℕ in atTop, ∀ ℓ, 0 ≤ size ℓ → size ℓ ≤ A n →
      T₀ n / A n * size ℓ + (c * (T₀ n / A n) - E n) * min (size ℓ) (A n - size ℓ) ≤ I n ℓ)
    (hquadratic : ∀ᶠ n : ℕ in atTop, ∀ ℓ, 0 ≤ size ℓ → size ℓ ≤ A n →
      T n - (H * n) * (A n - size ℓ) ^ 2 ≤ I n ℓ) :
    ∃ g : ℝ, 0 < g ∧ ∀ᶠ n : ℕ in atTop, ∀ ℓ, 0 ≤ size ℓ → size ℓ ≤ A n →
      T n / A n * size ℓ + g * (n : ℝ) ^ (s + 1) * min (size ℓ) (A n - size ℓ) ≤ I n ℓ := by
  let q := t / a
  have hq : 0 < q := div_pos ht ha
  let g := min c 1 * q / 4
  let δ := q / (4 * (H + 1))
  have hg : 0 < g := by dsimp [g]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hgc : g < c * (t / a) := by
    have hm := mul_le_mul_of_nonneg_right (min_le_left c 1) hq.le
    have hp : 0 < c * q := mul_pos hc hq
    dsimp [g]
    change min c 1 * q / 4 < c * q
    linarith
  have hgq : g ≤ q / 4 := by
    have hm := mul_le_mul_of_nonneg_right (min_le_right c 1) hq.le
    dsimp [g]
    linarith
  have hHδ : H * δ ≤ q / 4 := by
    dsimp [δ]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    have hden : 0 < 4 * (H + 1) := by positivity
    have hid : q / (4 * (H + 1)) * (4 * (H + 1)) = q := div_mul_cancel₀ q hden.ne'
    have hp : 0 < q / (4 * (H + 1)) := div_pos hq hden
    nlinarith
  have hnear : H * δ + g < t / a := by change H * δ + g < q; linarith
  have hfar := far_shadow_gap_eventually A T₀ D E s ha hδ hgc hA hT₀ hD hE
  have hnear' := near_shadow_gap_eventually A T₀ s ha hnear hA hT₀
  refine ⟨g, hg, ?_⟩
  filter_upwards [hfar, hnear', normalized_limit_eventually_pos A ha s hA,
    hbudget, hshadow, hquadratic, eventually_gt_atTop (0 : ℕ)] with n hnfar hnnear hnA hnb hnS hnQ hn0
  intro ℓ hℓ hℓA
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hK : 0 < δ * (n : ℝ) ^ s := mul_pos hδ (pow_pos hnR s)
  by_cases hk : δ * (n : ℝ) ^ s ≤ A n - size ℓ
  · exact absorb_shadow_error hnA hℓ hK hk hnb.2.2 hnb.2.1 (hnS ℓ hℓ hℓA) hnfar
  · apply absorb_quadratic_cokernel hnA hℓ hℓA (mul_nonneg hH hnR.le)
      (le_of_not_ge hk) (mul_nonneg hg.le (pow_nonneg hnR.le _)) (hnQ ℓ hℓ hℓA)
    exact hnnear.trans (div_le_div_of_nonneg_right hnb.1 hnA.le)

end Froberg
