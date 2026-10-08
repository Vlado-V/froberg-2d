import Froberg.CountedOuterStrata

/-! The exact dimension reserve absorbs every additional scalar count of
order smaller than n^(d-1), including all prepared even scalar shifts. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem outer_augmented_deficit_eventually_positive {d h b : ℕ} (hd : 3 ≤ d)
    (f extra : ℕ → ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hextra : Tendsto (fun n : ℕ => (extra n : ℝ)/(n : ℝ)^(d-1)) atTop (𝓝 0))
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) :
    ∀ᶠ n : ℕ in atTop,0 < outerTargetCount d h b f n-
      ((upperCount n d+extra n : ℕ) : ℝ)*outerSourceCount d h b f n := by
  have hb : Tendsto (fun n : ℕ => (b : ℝ)*((n+d-1).choose d : ℝ)/(n : ℝ)^(2*d-2))
      atTop (𝓝 0) := by
    simpa only [mul_div_assoc,mul_zero] using
      (monomial_count_normalized_small_tendsto (show d<2*d-2 by omega)).const_mul (b : ℝ)
  have he := hextra.mul ((monomial_count_normalized_tendsto (d-1)).const_mul (h : ℝ))
  have he' : Tendsto (fun n : ℕ =>
      ((extra n : ℝ)*(h : ℝ)*((n+(d-1)-1).choose (d-1) : ℝ))/(n : ℝ)^(2*d-2))
      atTop (𝓝 0) := by
    have hexp : (d-1)+(d-1)=2*d-2 := by omega
    convert he using 1
    · ext n
      rw [←hexp,pow_add]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    · simp
  have hl : Tendsto (fun n : ℕ =>
      ((b : ℝ)*((n+d-1).choose d : ℝ)+
        (extra n : ℝ)*(h : ℝ)*((n+(d-1)-1).choose (d-1) : ℝ))/(n : ℝ)^(2*d-2))
      atTop (𝓝 0) := by simpa only [add_div,add_zero] using hb.add he'
  have hsmall := eventually_lt_of_normalized_limits _ _ _ _ _ hl
    (scaled_power_normalized_limit δ (2*d-2)) hδ
  filter_upwards [hsmall,hreserve] with n hn hr
  have hs : outerSourceCount d h b f n ≤ (h : ℝ)*((n+(d-1)-1).choose (d-1) : ℝ) := by
    unfold outerSourceCount
    have hf : (0 : ℝ) ≤ f n := Nat.cast_nonneg _
    have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg _
    linarith
  have hecost := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (extra n) : (0 : ℝ) ≤ extra n)
  have hbase := outer_deficit_eq_reserve d h b n f
  have hnon : 0 ≤ (b : ℝ)*(upperCount n d : ℝ) := by positivity
  rw [Nat.cast_add]
  nlinarith

namespace VectorExpansionOpen
open Module Quartic VectorMultiplicationCoordinates
variable {K : Type*} [Field K] [Infinite K] {d h b : ℕ}

theorem eventually_augmented_outer_capacity (hd : 3 ≤ d)
    (f extra : ℕ → ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hextra : Tendsto (fun n : ℕ => (extra n : ℝ)/(n : ℝ)^(d-1)) atTop (𝓝 0))
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) :
    ∀ᶠ n : ℕ in atTop,∀ (G : ℝ) (g : Fin (f n+b) → Rows K h n (d-1)),
      StrictModel g d G →
      (upperCount n d+extra n)*finrank K (Source g) ≤ finrank K (Target g d) := by
  filter_upwards [outer_augmented_deficit_eventually_positive (b := b) hd f extra hδ hextra hreserve,
    eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  intro G g hg
  have hs : (finrank K (Source g) : ℝ)=outerSourceCount d h b f n := by
    rw [hg.source_real_count hnpos]
    unfold outerSourceCount
    push_cast
    ring
  have ht : (finrank K (Target g d) : ℝ)=outerTargetCount d h b f n := by
    rw [hg.target_real_count hnpos,show d-1+d=2*d-1 by omega]
    unfold outerTargetCount
    push_cast
    rfl
  have hle : ((upperCount n d+extra n : ℕ) : ℝ)*finrank K (Source g)≤finrank K (Target g d) := by
    rw [hs,ht]
    linarith
  exact_mod_cast hle

end VectorExpansionOpen
end Froberg
