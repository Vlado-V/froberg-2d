module

public import Froberg.CapacityScalar
public import Froberg.CapacityProductIdentity
public import Froberg.OddOutputLimit

@[expose] public section

/-! The scalar-capacity inequalities in the normalization of the actual
odd-half output space. -/
noncomputable section
namespace Froberg

theorem scalarCapacity_reciprocal {d R : ℕ} (hRd : R≤d) :
    (scalarCapacity d R)⁻¹ = (R.factorial : ℝ)*((d-R).factorial : ℝ)*
      (scalarCapacityBinomial d R : ℝ) := by
  unfold scalarCapacityBinomial
  rw [choose_real_factorial (show d-R≤2*d-R by omega),
    show 2*d-R-(d-R)=d by omega]
  unfold scalarCapacity
  field_simp [factorial_real_ne_zero]

/-- Exact transfer from B.8 to the leading coefficient of the odd-half
output space. -/
theorem sparse_odd_density_gap {d R : ℕ} (hR : 0<R) (hRd : R≤d)
    (γ : ℝ)
    (hgap : 2*γ/scalarCapacity d R+
      (scalarCapacityBinomial d R : ℝ)*criticalRatio d<1) :
    γ*2^R*((d-R).factorial : ℝ)*(scalarCapacityBinomial d R : ℝ) +
      (2^(R-1)/(R.factorial : ℝ))*(scalarCapacityBinomial d R : ℝ)*criticalRatio d <
        2^(R-1)/(R.factorial : ℝ) := by
  have hδ : 0<(2 : ℝ)^(R-1)/(R.factorial : ℝ) := by positivity
  have hp : (2 : ℝ)^R=2^(R-1)*2 := by rw [← pow_succ,Nat.sub_add_cancel hR]
  have he : (2^(R-1)/(R.factorial : ℝ))*(2*γ/scalarCapacity d R) =
      γ*2^R*((d-R).factorial : ℝ)*(scalarCapacityBinomial d R : ℝ) := by
    rw [div_eq_mul_inv (2*γ),scalarCapacity_reciprocal hRd,hp]
    field_simp [factorial_real_ne_zero]
    <;> ring
  have hh := mul_lt_mul_of_pos_left hgap hδ
  rw [mul_add,he,mul_one] at hh
  simpa only [mul_assoc] using hh

theorem higher_sparse_scalar_margin {d R : ℕ} (hd : 9≤d)
    (hR : R∈activeHigherIndices d) :
    2*((101/100 : ℝ)*higherCountGamma d R)/scalarCapacity d R+
      (scalarCapacityBinomial d R : ℝ)*criticalRatio d<1 := by
  have hh := higher_scalar_capacity hd hR
  have hm : 2*((101/100 : ℝ)*higherCountGamma d R)/scalarCapacity d R ≤
      2*(253/250 : ℝ)*higherCountGamma d R/scalarCapacity d R := by
    apply div_le_div_of_nonneg_right _ (scalarCapacity_pos d R).le
    nlinarith [higherCountGamma_pos d R]
  linarith

end Froberg
