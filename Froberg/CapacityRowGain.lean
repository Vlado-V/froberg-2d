import Froberg.StrictTransportGain

/-! Converting actual fiber-image bounds into the hypotheses of the strict
transport inequality. -/
noncomputable section
namespace Froberg
open Finset
variable {I : Type*} [Fintype I]

lemma normalized_capacity_gain (c d u g : ℝ) (hc : 0 < c) (hcd : c ≤ d)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hg : min c (d * u) ≤ c * g) :
    u + (min c (d - c) / c) * u * (1 - u) ≤ g := by
  have h := (capacity_decrease_gain c d u hc.le hcd hu hu1).trans hg
  have hcancel : c * (min c (d - c) / c) = min c (d - c) := by field_simp
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    c * (u + (min c (d - c) / c) * u * (1 - u)) =
        c * u + (c * (min c (d - c) / c)) * u * (1 - u) := by ring
    _ = c * u + min c (d - c) * u * (1 - u) := by rw [hcancel]
    _ ≤ c * g := h

lemma normalized_capacity_le (c d u g : ℝ) (hc : 0 < c) (hcd : c ≤ d)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hg : min c (d * u) ≤ c * g) : u ≤ g := by
  have h := normalized_capacity_gain c d u g hc hcd hu hu1 hg
  have hk : 0 ≤ min c (d - c) / c := div_nonneg (le_min hc.le (sub_nonneg.mpr hcd)) hc.le
  have hgain : 0 ≤ (min c (d - c) / c) * u * (1 - u) := by positivity
  linarith

/-- A target image containing every projected source image satisfies both
the maximum and the averaged capacity-decrease lower bounds. -/
theorem capacity_row_gain (C d u : I → ℝ) (c g : ℝ)
    (hC0 : ∀ i, 0 ≤ C i) (hC : ∑ i, C i = 1) (hc : 0 < c)
    (hcd : ∀ i, 0 < C i → c ≤ d i)
    (hu : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1)
    (hg : ∀ i, 0 < C i → min c (d i * u i) ≤ c * g) :
    (∀ i, 0 < C i → u i ≤ g) ∧
    weightedMean C u + ∑ i, (C i * (min c (d i - c) / c)) * u i * (1 - u i) ≤ g := by
  constructor
  · intro i hi
    exact normalized_capacity_le c (d i) (u i) g hc (hcd i hi) (hu i) (hu1 i) (hg i hi)
  · have hp (i : I) :
        C i * (u i + (min c (d i - c) / c) * u i * (1 - u i)) ≤ C i * g := by
      by_cases hi : C i = 0
      · simp [hi]
      · have hCi : 0 < C i := lt_of_le_of_ne (hC0 i) (Ne.symm hi)
        exact mul_le_mul_of_nonneg_left
          (normalized_capacity_gain c (d i) (u i) g hc (hcd i hCi) (hu i) (hu1 i) (hg i hCi)) (hC0 i)
    have hh := sum_le_sum (fun i (_ : i ∈ (univ : Finset I)) => hp i)
    simp only [mul_add, sum_add_distrib, ← sum_mul, hC, one_mul] at hh
    convert hh using 1
    simp only [weightedMean]
    congr 1
    apply sum_congr rfl
    intro i _
    ring

end Froberg
