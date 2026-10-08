import Quartic.UniformScalar.RealCounts

/-! Exact scalar incidence consequences of a uniform image-surplus hypothesis. -/

namespace Quartic.UniformScalar

noncomputable section

def codimensionR (k S c d : ℝ) : ℝ := max (k-4*d) 0 + max (S-c*d) 0
def covectorR (j E q a d : ℝ) : ℝ := j-E+q*d+d*(a-d)-1

/-- The manuscript's uniform image lower bound, using `T/a=q+j/a`. -/
def uniformLower (q j a D d : ℝ) : ℝ := (q+j/a)*d+D*min d (a-d)

theorem codimensionR_lower (k S c d : ℝ) : k+S-(c+4)*d ≤ codimensionR k S c d := by
  have h₁ := le_max_left (k-4*d) 0
  have h₂ := le_max_left (S-c*d) 0
  unfold codimensionR
  linarith

/-- Uniform surplus exceeding the source dimension implies the outer inequality. -/
theorem outer_of_uniform_surplus (q j a D d E : ℝ)
    (ha : 0 < a) (hj : 0 ≤ j) (hDa : a ≤ D)
    (hdlo : 0 ≤ d) (hdhi : d ≤ a) (hE : uniformLower q j a D d ≤ E) :
    d*(q+a-d) ≤ E := by
  have hja : 0 ≤ j/a := div_nonneg hj ha.le
  unfold uniformLower at hE
  by_cases hhalf : d ≤ a-d
  · rw [min_eq_left hhalf] at hE
    have hp := mul_nonneg hdlo (show 0 ≤ D+j/a-a+d by linarith)
    nlinarith only [hE, hp]
  · rw [min_eq_right (by linarith : a-d ≤ d)] at hE
    have hp := mul_nonneg (show 0 ≤ a-d by linarith) (show 0 ≤ D-d by linarith)
    have hjd := mul_nonneg hja hdlo
    nlinarith only [hE, hp, hjd]

/-- The two domination estimates convert uniform surplus into the normal
incidence alternative. No geometric statement is hidden in this implication. -/
theorem normal_of_uniform_surplus (q c j a h k S D d E : ℝ)
    (ha : 0 < a) (hh : h=k+S) (hdlo : 0 < d) (hdhi : d < a)
    (hD₁ : c+4+a-j/a < D) (hD₂ : a+j/a < D)
    (hE : uniformLower q j a D d ≤ E) :
    covectorR j E q a d < 0 ∨
      covectorR j E q a d-codimensionR k S c d ≤ max (j-h) 0-1 := by
  have hC : h-(c+4)*d ≤ codimensionR k S c d := by
    rw [hh]
    exact codimensionR_lower k S c d
  unfold uniformLower at hE
  by_cases hhalf : d ≤ a-d
  · rw [min_eq_left hhalf] at hE
    have hp : d*(c+4+a-d-j/a-D) < 0 :=
      mul_neg_of_pos_of_neg hdlo (by linarith)
    have hbound : covectorR j E q a d-codimensionR k S c d < j-h-1 := by
      unfold covectorR
      nlinarith only [hE, hC, hp]
    right
    have ht := le_max_left (j-h) 0
    linarith
  · rw [min_eq_right (by linarith : a-d ≤ d)] at hE
    have hp : (a-d)*(j/a+d-D) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith)
    have hratio : a*(j/a)=j := by field_simp
    left
    unfold covectorR
    nlinarith only [hE, hp, hratio]

/-- Both scalar incidence tests follow from uniform surplus and the established
dimension/ratio domination conditions. -/
theorem incidence_of_uniform_surplus (q c j a h k S D d E : ℝ)
    (ha : 0 < a) (hj : 0 ≤ j) (hh : h=k+S)
    (hdlo : 0 < d) (hdhi : d < a)
    (hDa : a ≤ D) (hD₁ : c+4+a-j/a < D) (hD₂ : a+j/a < D)
    (hE : uniformLower q j a D d ≤ E) :
    d*(q+a-d) ≤ E ∧
      (covectorR j E q a d < 0 ∨
        covectorR j E q a d-codimensionR k S c d ≤ max (j-h) 0-1) :=
  ⟨outer_of_uniform_surplus q j a D d E ha hj hDa hdlo.le hdhi.le hE,
    normal_of_uniform_surplus q c j a h k S D d E ha hh hdlo hdhi hD₁ hD₂ hE⟩

end
end Quartic.UniformScalar
