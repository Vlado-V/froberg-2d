module

public import Mathlib.Tactic

@[expose] public section

/-! # Pure real inequalities for absorbing finite shadow errors

These lemmas isolate the two elementary estimates in B.2: away from full
source dimension the exceptional error is lower order; near full dimension
the quadratic cokernel bound supplies the surplus.
-/

namespace Froberg

/-- With codimension at least `K`, the source dimension is controlled by the
smaller of dimension and codimension. -/
theorem dimension_le_multiple_min {A ℓ K : ℝ} (hA : 0 < A) (hℓ : 0 ≤ ℓ)
    (hK : 0 < K) (hk : K ≤ A - ℓ) :
    ℓ ≤ (1 + A / K) * min ℓ (A - ℓ) := by
  have hAK : 0 ≤ A / K := (div_pos hA hK).le
  rcases le_total ℓ (A - ℓ) with h | h
  · rw [min_eq_left h]
    nlinarith [mul_nonneg hAK hℓ]
  · rw [min_eq_right h]
    have hmul := mul_le_mul_of_nonneg_left hk hAK
    have hcancel : A / K * K = A := div_mul_cancel₀ A hK.ne'
    have hk0 : 0 ≤ A - ℓ := hK.le.trans hk
    nlinarith

/-- A lower-order discrepancy between total and retained targets is absorbed
by a strict shadow surplus. -/
theorem absorb_shadow_error {A T T₀ I ℓ D E c g K : ℝ}
    (hA : 0 < A) (hℓ : 0 ≤ ℓ) (hK : 0 < K) (hk : K ≤ A - ℓ)
    (hD : 0 ≤ D) (hT : T - T₀ ≤ D)
    (hI : T₀ / A * ℓ + (c * (T₀ / A) - E) * min ℓ (A - ℓ) ≤ I)
    (hgap : g + E + D / A * (1 + A / K) ≤ c * (T₀ / A)) :
    T / A * ℓ + g * min ℓ (A - ℓ) ≤ I := by
  have hm : 0 ≤ min ℓ (A - ℓ) := le_min hℓ (hK.le.trans hk)
  have hr := dimension_le_multiple_min hA hℓ hK hk
  have hDr := mul_le_mul_of_nonneg_left hr (div_nonneg hD hA.le)
  have hTr := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hT hA.le) hℓ
  have hg := mul_le_mul_of_nonneg_right hgap hm
  rw [sub_div] at hTr
  nlinarith only [hI, hDr, hTr, hg]

/-- Near full dimension, a quadratic bound on missing targets gives the
same linear surplus. -/
theorem absorb_quadratic_cokernel {A T I ℓ U K g : ℝ}
    (hA : 0 < A) (hℓ : 0 ≤ ℓ) (hℓA : ℓ ≤ A) (hU : 0 ≤ U)
    (hK : A - ℓ ≤ K) (hg : 0 ≤ g)
    (hI : T - U * (A - ℓ) ^ 2 ≤ I) (hgap : U * K + g ≤ T / A) :
    T / A * ℓ + g * min ℓ (A - ℓ) ≤ I := by
  have hk : 0 ≤ A - ℓ := sub_nonneg.mpr hℓA
  have hUK := mul_le_mul_of_nonneg_left hK hU
  have hUKk := mul_le_mul_of_nonneg_right hUK hk
  have hmk := mul_le_mul_of_nonneg_left (min_le_right ℓ (A - ℓ)) hg
  have hgapk := mul_le_mul_of_nonneg_right hgap hk
  have hTA : T / A * A = T := div_mul_cancel₀ T hA.ne'
  nlinarith only [hI, hUKk, hmk, hgapk, hTA]

end Froberg
