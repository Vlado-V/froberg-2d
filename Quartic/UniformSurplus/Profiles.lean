module

public import Quartic.UniformSurplus.Interpolation

@[expose] public section

/-! Explicit ordered-profile barycentric interpolation. No assertion about
geometric subspaces is used in this numerical module. -/

namespace Quartic.UniformSurplus
open Quartic.UniformCertificate
noncomputable section

def weighted (f : Fin 4 → ℝ) (y₁ y₂ y₃ : ℝ) : ℝ :=
  (1-y₁)*f 0+(y₁-y₂)*f 1+(y₂-y₃)*f 2+y₃*f 3

def OrderedProfile (y₁ y₂ y₃ : ℝ) : Prop :=
  0 ≤ y₃ ∧ y₃ ≤ y₂ ∧ y₂ ≤ y₁ ∧ y₁ ≤ 1

theorem weighted_nonnegative {f : Fin 4 → ℝ} {y₁ y₂ y₃ : ℝ}
    (hy : OrderedProfile y₁ y₂ y₃) (hf : ∀r, 0 ≤ f r) :
    0 ≤ weighted f y₁ y₂ y₃ := by
  unfold weighted
  exact add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (sub_nonneg.mpr hy.2.2.2) (hf 0))
    (mul_nonneg (sub_nonneg.mpr hy.2.2.1) (hf 1)))
    (mul_nonneg (sub_nonneg.mpr hy.2.1) (hf 2)))
    (mul_nonneg hy.1 (hf 3))

theorem weighted_mono {f g : Fin 4 → ℝ} {y₁ y₂ y₃ : ℝ}
    (hy : OrderedProfile y₁ y₂ y₃) (hfg : ∀r, f r ≤ g r) :
    weighted f y₁ y₂ y₃ ≤ weighted g y₁ y₂ y₃ := by
  have h := weighted_nonnegative hy (fun r => sub_nonneg.mpr (hfg r))
  dsimp [weighted] at *
  linarith

def profileDim (z u x y₁ y₂ y₃ : ℝ) : ℝ :=
  coreA z u*x+freeW z*(y₁+y₂+y₃)

def profileDenominator (cell : Fin 4) (z u x y₁ y₂ y₃ : ℝ) : ℝ :=
  if cell = 0 then profileDim z u x y₁ y₂ y₃
  else if cell = 3 then sourceDim z u-profileDim z u x y₁ y₂ y₃
  else sourceDim z u/2

theorem weighted_ell (z u x y₁ y₂ y₃ : ℝ) :
    weighted (fun r => ell z u x r) y₁ y₂ y₃ = profileDim z u x y₁ y₂ y₃ := by
  norm_num [weighted, ell, profileDim]
  ring

theorem weighted_polynomial (cell : Fin 4) (z u x y₁ y₂ y₃ : ℝ) :
    weighted (fun r => surplusPolynomial cell z u x r) y₁ y₂ y₃ =
      100*(sourceDim z u*weighted (fun r => imageBound z u x r) y₁ y₂ y₃-
        targetDim z u*profileDim z u x y₁ y₂ y₃)-
      sourceDim z u*profileDenominator cell z u x y₁ y₂ y₃ := by
  unfold weighted surplusPolynomial denominator profileDenominator ell profileDim
  norm_num
  split_ifs <;> ring

theorem sourceDim_pos (z u : ℝ) (hz1 : z ≤ 14/25) (hu1 : u ≤ 1/64) :
    0 < sourceDim z u := by
  unfold sourceDim coreA freeW
  linarith

theorem profileDenominator_lower (cell : Fin 4) (z u x y₁ y₂ y₃ : ℝ) :
    min (profileDim z u x y₁ y₂ y₃)
      (sourceDim z u-profileDim z u x y₁ y₂ y₃) ≤
    profileDenominator cell z u x y₁ y₂ y₃ := by
  unfold profileDenominator
  split_ifs
  · exact min_le_left _ _
  · exact min_le_right _ _
  · have h₁ := min_le_left (profileDim z u x y₁ y₂ y₃)
      (sourceDim z u-profileDim z u x y₁ y₂ y₃)
    have h₂ := min_le_right (profileDim z u x y₁ y₂ y₃)
      (sourceDim z u-profileDim z u x y₁ y₂ y₃)
    linarith

/-- Extension of all 32 polynomial certificates to every ordered profile,
expressed as its explicit convex combination of prefix image bounds. -/
theorem weighted_uniform_surplus (z u x y₁ y₂ y₃ : ℝ)
    (hz0 : 1/2 ≤ z) (hz1 : z ≤ 14/25)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/64)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy : OrderedProfile y₁ y₂ y₃) :
    targetDim z u/sourceDim z u*profileDim z u x y₁ y₂ y₃+
      (1/100)*min (profileDim z u x y₁ y₂ y₃)
        (sourceDim z u-profileDim z u x y₁ y₂ y₃) ≤
      weighted (fun r => imageBound z u x r) y₁ y₂ y₃ := by
  obtain ⟨cell, hxlo, hxhi⟩ := knot_interval x hx0 hx1
  have h := weighted_nonnegative hy
    (fun r => surplus_prefix cell r z u x hz0 hz1 hu0 hu1 hxlo hxhi)
  rw [weighted_polynomial] at h
  have ha := sourceDim_pos z u hz1 hu1
  have hD := mul_le_mul_of_nonneg_left
    (profileDenominator_lower cell z u x y₁ y₂ y₃) (le_of_lt ha)
  have hdiv : sourceDim z u*(targetDim z u/sourceDim z u) = targetDim z u := by
    field_simp
  apply (mul_le_mul_iff_right₀ ha).mp
  nlinarith [congrArg (fun v : ℝ => v*profileDim z u x y₁ y₂ y₃) hdiv]

end
end Quartic.UniformSurplus
