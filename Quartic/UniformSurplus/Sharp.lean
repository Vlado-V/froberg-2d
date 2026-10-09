module

public import Quartic.UniformSurplus.Profiles

@[expose] public section

/-! Endpoint chords of the quadratic and cubic layer polynomials suffice for
the uniform bound. This proves the numerical profile inequality directly. -/

namespace Quartic.UniformSurplus
open Quartic.UniformCertificate
noncomputable section

def layer₂ (z u y : ℝ) : ℝ :=
  quadratic z u-(freeW z-freeW z*y)*(freeW z-freeW z*y+u)/2

def layer₃ (z u y : ℝ) : ℝ :=
  cubic z u-(freeW z-freeW z*y)*(freeW z-freeW z*y+u)*
    (freeW z-freeW z*y+2*u)/6

theorem layer₂_chord (z u y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    quadratic z u*y ≤ layer₂ z u y := by
  have h : 0 ≤ (freeW z)^2*y*(1-y)/2 := by positivity
  unfold layer₂ quadratic at *
  nlinarith [sq_nonneg (freeW z)]

theorem layer₃_chord (z u y : ℝ) (hz : z ≤ 1) (hu : 0 ≤ u)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    cubic z u*y ≤ layer₃ z u y := by
  have hw : 0 ≤ freeW z := by unfold freeW; linarith
  have hyA : 0 ≤ 1-y := by linarith
  have hyB : 0 ≤ 2-y := by linarith
  have h : 0 ≤ (freeW z)^2*y*(1-y)*(freeW z*(2-y)+3*u)/6 := by positivity
  have heq : layer₃ z u y-cubic z u*y =
      (freeW z)^2*y*(1-y)*(freeW z*(2-y)+3*u)/6 := by
    unfold layer₃ cubic
    ring
  linarith

/-- The normalized sharp profile, with an arbitrary core shadow `b` satisfying
its linear lower bound. The three free layer parameters are fractions of w. -/
def sharpNormalized (z u b x y₁ y₂ y₃ : ℝ) : ℝ :=
  b*freeW z+(coreB z u-b)*freeW z*y₁+
    coreA z u*(x*quadratic z u+(max x (1/2)-x)*layer₂ z u y₁+
      (1-max x (1/2))*layer₂ z u y₂)+
    layer₃ z u y₁+layer₃ z u y₂+layer₃ z u y₃

theorem weighted_image_formula (z u x y₁ y₂ y₃ : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    weighted (fun r => imageBound z u x r) y₁ y₂ y₃ =
      coreB z u*freeW z*weighted (fun r => max x (((r:ℕ):ℝ) / 3)) y₁ y₂ y₃+
      coreA z u*quadratic z u*(x+(max x (1/2)-x)*y₁+(1-max x (1/2))*y₂)+
      cubic z u*(y₁+y₂+y₃) := by
  norm_num [weighted, imageBound, max_eq_left hx0, max_eq_right hx1]
  ring

theorem weighted_max_bound (x y₁ y₂ y₃ : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy : OrderedProfile y₁ y₂ y₃) :
    weighted (fun r => max x (((r:ℕ):ℝ)/3)) y₁ y₂ y₃ ≤ x+(1-x)*y₁ := by
  let f : Fin 4 → ℝ := ![x, 1, 1, 1]
  have h : ∀r:Fin 4, max x (((r:ℕ):ℝ)/3) ≤ f r := by
    intro r
    fin_cases r <;> norm_num [f, max_eq_left hx0, max_le_iff, hx1]
  have hw := weighted_mono hy h
  dsimp [weighted, f] at hw ⊢
  linarith

/-- The exact sharp layer polynomial dominates the explicit prefix average. -/
theorem weighted_le_sharp (z u b x y₁ y₂ y₃ : ℝ)
    (hz0 : 1/2 ≤ z) (hz1 : z ≤ 14/25)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/64)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy : OrderedProfile y₁ y₂ y₃)
    (hb : coreB z u*x ≤ b) :
    weighted (fun r => imageBound z u x r) y₁ y₂ y₃ ≤
      sharpNormalized z u b x y₁ y₂ y₃ := by
  have hw : 0 ≤ freeW z := by unfold freeW; linarith
  have hA : 0 ≤ coreA z u := by unfold coreA; linarith
  have hB : 0 ≤ coreB z u := by
    unfold coreB
    have hz : 0 ≤ z := by linarith
    have hzu : 0 ≤ z-u := by linarith
    positivity
  have hy₁0 : 0 ≤ y₁ := hy.1.trans (hy.2.1.trans hy.2.2.1)
  have hy₂0 : 0 ≤ y₂ := hy.1.trans hy.2.1
  have hy₂1 : y₂ ≤ 1 := hy.2.2.1.trans hy.2.2.2
  have hy₃1 : y₃ ≤ 1 := hy.2.1.trans hy₂1
  have hhalf : max x (1/2) ≤ 1 := max_le hx1 (by norm_num)
  have hfirst := mul_le_mul_of_nonneg_left (weighted_max_bound x y₁ y₂ y₃ hx0 hx1 hy)
    (mul_nonneg hB hw)
  have hbdiff : 0 ≤ (b-coreB z u*x)*freeW z*(1-y₁) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hb) hw) (sub_nonneg.mpr hy.2.2.2)
  have hq₁ := mul_le_mul_of_nonneg_left (layer₂_chord z u y₁ hy₁0 hy.2.2.2)
    (mul_nonneg hA (sub_nonneg.mpr (le_max_left x (1/2))))
  have hq₂ := mul_le_mul_of_nonneg_left (layer₂_chord z u y₂ hy₂0 hy₂1)
    (mul_nonneg hA (sub_nonneg.mpr hhalf))
  have hc₁ := layer₃_chord z u y₁ (by linarith) hu0 hy₁0 hy.2.2.2
  have hc₂ := layer₃_chord z u y₂ (by linarith) hu0 hy₂0 hy₂1
  have hc₃ := layer₃_chord z u y₃ (by linarith) hu0 hy.1 hy₃1
  rw [weighted_image_formula z u x y₁ y₂ y₃ hx0 hx1]
  unfold sharpNormalized
  nlinarith

/-- The numerical content of `sc:uniform-surplus` for every real ordered
profile. No minimum or geometric degeneration hypothesis is needed here. -/
theorem sharp_normalized_surplus (z u b x y₁ y₂ y₃ : ℝ)
    (hz0 : 1/2 ≤ z) (hz1 : z ≤ 14/25)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/64)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy : OrderedProfile y₁ y₂ y₃)
    (hb : coreB z u*x ≤ b) :
    targetDim z u/sourceDim z u*profileDim z u x y₁ y₂ y₃+
      (1/100)*min (profileDim z u x y₁ y₂ y₃)
        (sourceDim z u-profileDim z u x y₁ y₂ y₃) ≤
      sharpNormalized z u b x y₁ y₂ y₃ :=
  (weighted_uniform_surplus z u x y₁ y₂ y₃ hz0 hz1 hu0 hu1 hx0 hx1 hy).trans
    (weighted_le_sharp z u b x y₁ y₂ y₃ hz0 hz1 hu0 hu1 hx0 hx1 hy hb)

end
end Quartic.UniformSurplus
