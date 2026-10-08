import Froberg.OuterDimensionLimits
import Froberg.AsymptoticCounts

/-! The exact dimension reserve survives the finitely many private columns. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

lemma outer_deficit_eq_reserve (d h b n : ℕ) (f : ℕ → ℕ) :
    outerTargetCount d h b f n-(upperCount n d : ℝ)*outerSourceCount d h b f n=
      dimensionReserve d h n (f n)-(b : ℝ)*
        (((n+d-1).choose d : ℝ)-(upperCount n d : ℝ)) := by
  unfold outerTargetCount outerSourceCount dimensionReserve
  ring

theorem outer_deficit_eventually_positive {d h b : ℕ} (hd : 3 ≤ d)
    (f : ℕ → ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) :
    ∀ᶠ n in atTop,
      0 < outerTargetCount d h b f n-(upperCount n d : ℝ)*outerSourceCount d h b f n := by
  have hb : Tendsto (fun n : ℕ => (b : ℝ)*((n+d-1).choose d : ℝ)/(n : ℝ)^(2*d-2))
      atTop (𝓝 0) := by
    simpa only [mul_div_assoc,mul_zero] using
      (monomial_count_normalized_small_tendsto (show d<2*d-2 by omega)).const_mul (b : ℝ)
  have hsmall := eventually_lt_of_normalized_limits
    (fun n : ℕ => (b : ℝ)*((n+d-1).choose d : ℝ))
    (fun n : ℕ => δ*(n : ℝ)^(2*d-2)) (2*d-2) 0 δ
    hb (scaled_power_normalized_limit _ _) hδ
  filter_upwards [hsmall,hreserve] with n hn hr
  rw [outer_deficit_eq_reserve]
  have hp : (0 : ℝ) ≤ (b : ℝ)*(upperCount n d : ℝ) := by positivity
  nlinarith

end Froberg
