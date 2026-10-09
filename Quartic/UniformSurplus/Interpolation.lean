module

public import Quartic.UniformCertificate
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! Numerical interpolation of the 32 uniform vertex certificates. -/

namespace Quartic.UniformSurplus

open Quartic.UniformCertificate

noncomputable section

/-- The manuscript's polynomial at an arbitrary core fraction. -/
def surplusPolynomial (cell : Fin 4) (z u x r : ℝ) : ℝ :=
  100 * (sourceDim z u * imageBound z u x r - targetDim z u * ell z u x r) -
    sourceDim z u * denominator cell z u x r

theorem max_interpolate (lo hi x k s : ℝ)
    (hxlo : lo ≤ x) (hxhi : x ≤ hi)
    (hside : k ≤ lo ∨ hi ≤ k)
    (hx : x = (1-s)*lo+s*hi) :
    max x k = (1-s)*max lo k+s*max hi k := by
  rcases hside with h | h
  · rw [max_eq_left (h.trans hxlo), max_eq_left h,
      max_eq_left (h.trans (hxlo.trans hxhi))]
    exact hx
  · rw [max_eq_right (hxhi.trans h), max_eq_right ((hxlo.trans hxhi).trans h),
      max_eq_right h]
    ring

theorem knot_separation (cell r : Fin 4) :
    ((r:ℕ):ℝ)/3 ≤ endpoint cell 0 ∨ endpoint cell 1 ≤ ((r:ℕ):ℝ)/3 := by
  fin_cases cell <;> fin_cases r <;> norm_num [endpoint, knots]

theorem knot_separation_half (cell r : Fin 4) :
    min (((r:ℕ):ℝ)/2) 1 ≤ endpoint cell 0 ∨
      endpoint cell 1 ≤ min (((r:ℕ):ℝ)/2) 1 := by
  fin_cases cell <;> fin_cases r <;> norm_num [endpoint, knots]

theorem surplus_interpolate (cell r : Fin 4) (z u x s : ℝ)
    (hxlo : endpoint cell 0 ≤ x) (hxhi : x ≤ endpoint cell 1)
    (hx : x = (1-s)*endpoint cell 0+s*endpoint cell 1) :
    surplusPolynomial cell z u x r =
      (1-s)*inequalityPolynomial cell r 0 z u+
      s*inequalityPolynomial cell r 1 z u := by
  have hmax := max_interpolate _ _ x (((r:ℕ):ℝ) / 3) s hxlo hxhi
    (knot_separation cell r) hx
  have hhalf := max_interpolate _ _ x (min (((r:ℕ):ℝ)/2) 1) s hxlo hxhi
    (knot_separation_half cell r) hx
  unfold surplusPolynomial inequalityPolynomial imageBound
  rw [hmax, hhalf]
  unfold denominator ell
  split_ifs <;> rw [hx] <;> ring

theorem surplus_prefix (cell r : Fin 4) (z u x : ℝ)
    (hz0 : 1/2 ≤ z) (hz1 : z ≤ 14/25)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/64)
    (hxlo : endpoint cell 0 ≤ x) (hxhi : x ≤ endpoint cell 1) :
    0 ≤ surplusPolynomial cell z u x r := by
  have hgap : 0 < endpoint cell 1 - endpoint cell 0 := by
    fin_cases cell <;> norm_num [endpoint, knots]
  let s := (x-endpoint cell 0)/(endpoint cell 1-endpoint cell 0)
  have hs0 : 0 ≤ s := div_nonneg (sub_nonneg.mpr hxlo) (le_of_lt hgap)
  have hs1 : s ≤ 1 := (div_le_one hgap).mpr (by linarith)
  have hx : x = (1-s)*endpoint cell 0+s*endpoint cell 1 := by
    dsimp [s]
    field_simp
    ring
  rw [surplus_interpolate cell r z u x s hxlo hxhi hx]
  exact add_nonneg
    (mul_nonneg (sub_nonneg.mpr hs1)
      (uniform_bernstein_inequality cell r 0 z u hz0 hz1 hu0 hu1))
    (mul_nonneg hs0 (uniform_bernstein_inequality cell r 1 z u hz0 hz1 hu0 hu1))

theorem knot_interval (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∃ cell : Fin 4, endpoint cell 0 ≤ x ∧ x ≤ endpoint cell 1 := by
  by_cases h0 : x ≤ 1/3
  · exact ⟨0, by norm_num [endpoint, knots]; exact ⟨hx0, h0⟩⟩
  by_cases h1 : x ≤ 1/2
  · exact ⟨1, by norm_num [endpoint, knots]; exact ⟨le_of_lt (lt_of_not_ge h0), h1⟩⟩
  by_cases h2 : x ≤ 2/3
  · exact ⟨2, by norm_num [endpoint, knots]; exact ⟨le_of_lt (lt_of_not_ge h1), h2⟩⟩
  exact ⟨3, by norm_num [endpoint, knots]; exact ⟨le_of_lt (lt_of_not_ge h2), hx1⟩⟩

end
end Quartic.UniformSurplus
