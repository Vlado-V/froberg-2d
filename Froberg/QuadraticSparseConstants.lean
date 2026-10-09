module

public import Froberg.SparseLayerConstants
public import Froberg.QuadraticOutputDimension

@[expose] public section

/-! The actual quadratic count, including the deleted output coordinates,
satisfies the strict sparse capacity inequality in every degree at least three. -/
noncomputable section
namespace Froberg

theorem quadratic_sparse_scalar_margin {d : ℕ} (hd : 3≤d) :
    countBeta d/(scalarCapacity d 2*(1-outerColumnRate d^2))+
      (scalarCapacityBinomial d 2 : ℝ)*criticalRatio d<1 := by
  by_cases hd8 : d≤8
  · exact small_quadratic_scalar_capacity hd hd8
  have hd9 : 9≤d := by omega
  have hρ := (outerColumnRate_bounds hd).1
  have hr := outerColumnRate_small hd9
  have hsq : outerColumnRate d^2 < (1/75 : ℝ)^2 :=
    (sq_lt_sq₀ hρ.le (by norm_num)).mpr hr
  have hden : (4999/5000 : ℝ) ≤ 1-outerColumnRate d^2 := by norm_num at hsq; linarith
  have hG : 0<countGammaTwo d := (countTauFour_pos hd).trans_le (countTauFour_le_gamma d)
  have hβ : countBeta d≤(253/250 : ℝ)*countGammaTwo d := by unfold countBeta; linarith
  have hβ0 : 0≤(253/250 : ℝ)*countGammaTwo d := by positivity
  have hb := div_le_div₀ hβ0 hβ
    (mul_pos (scalarCapacity_pos d 2) (by norm_num : (0 : ℝ)<4999/5000))
    (mul_le_mul_of_nonneg_left hden (scalarCapacity_pos d 2).le)
  have he : ((253/250 : ℝ)*countGammaTwo d)/(scalarCapacity d 2*(4999/5000)) =
      ((253/250 : ℝ)*countGammaTwo d/scalarCapacity d 2)*(5000/4999) := by ring
  rw [he] at hb
  have hcap := quadratic_scalar_capacity hd9
  linarith

theorem quadratic_sparse_density_gap {d : ℕ} (hd : 3≤d) :
    countBeta d*((d-2).factorial : ℝ)*(scalarCapacityBinomial d 2 : ℝ)+
      quadraticOutputDensity d*(scalarCapacityBinomial d 2 : ℝ)*criticalRatio d <
        quadraticOutputDensity d := by
  have hδ : 0<quadraticOutputDensity d := lt_trans (by norm_num) (quadraticOutputDensity_lower hd)
  have hz : 1-outerColumnRate d^2≠0 := by
    have : 0<1-outerColumnRate d^2 := by unfold quadraticOutputDensity at hδ; linarith
    exact this.ne'
  have he : quadraticOutputDensity d *
      (countBeta d/(scalarCapacity d 2*(1-outerColumnRate d^2))) =
      countBeta d*((d-2).factorial : ℝ)*(scalarCapacityBinomial d 2 : ℝ) := by
    rw [div_mul_eq_div_mul_one_div,div_eq_mul_inv (countBeta d),scalarCapacity_reciprocal (by omega : 2≤d)]
    norm_num [quadraticOutputDensity,Nat.factorial]
    field_simp
    <;> ring
  have hh := mul_lt_mul_of_pos_left (quadratic_sparse_scalar_margin hd) hδ
  rw [mul_add,he,mul_one] at hh
  simpa only [mul_assoc] using hh

end Froberg
