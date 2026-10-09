module

public import Froberg.ProductCapacityLimits

@[expose] public section

/-! The proved B.9 bounds give a strict gap for the actual deleted output
counts, including the quadratic loss. -/
noncomputable section
namespace Froberg

theorem half_output_product_identity {d j : ℕ} (hjd : j ≤ d) :
    ((1/2 : ℝ)^j/(j.factorial : ℝ))/(2^(d-j+1)*((d-j).factorial : ℝ)) =
      productCapacity d j := by
  unfold productCapacity
  rw [div_pow,one_pow]
  have hp : (2 : ℝ)^(d+1) = 2^j*2^(d-j+1) := by
    rw [← pow_add,show j+(d-j+1)=d+1 by omega]
  rw [hp]
  ring

theorem higher_diagonal_product_identity {d j : ℕ} (hj : 2 < j) (hjd : j ≤ d) :
    diagonalOutputDensity d j/(2^(d-j+1)*((d-j).factorial : ℝ)) =
      productCapacity d j := by
  unfold diagonalOutputDensity
  rw [if_neg (by omega),sub_zero,half_output_product_identity hjd]

theorem quadratic_diagonal_product_margin {d : ℕ} (hd : 9 ≤ d) :
    (1249/1250 : ℝ)*productCapacity d 2 <
      diagonalOutputDensity d 2/(2^(d-2+1)*((d-2).factorial : ℝ)) := by
  have hp := (outerColumnRate_bounds (show 3 ≤ d by omega)).1
  have hl := outerColumnRate_small hd
  have hs : outerColumnRate d^2 < (1/75 : ℝ)^2 :=
    (sq_lt_sq₀ hp.le (by norm_num)).mpr hl
  have hδ : (1249/1250 : ℝ)*((1/2 : ℝ)^2/((2 : ℕ).factorial : ℝ)) < diagonalOutputDensity d 2 := by
    unfold diagonalOutputDensity
    norm_num [Nat.factorial] at hs ⊢
    linarith
  have h := div_lt_div_of_pos_right hδ
    (show (0 : ℝ)<2^(d-2+1)*((d-2).factorial : ℝ) by positivity)
  rw [mul_div_assoc,half_output_product_identity (show 2 ≤ d by omega)] at h
  exact h

theorem quadratic_finite_product_density_gap {d : ℕ} (hd : 9 ≤ d) :
    (253/250 : ℝ)*countGammaTwo d <
      diagonalOutputDensity d 2/(2^(d-2+1)*((d-2).factorial : ℝ)) := by
  have h := quadratic_product_capacity hd
  have hp := productCapacity_pos d 2
  have hbase : (253/250 : ℝ)*countGammaTwo d < (1249/1250 : ℝ)*productCapacity d 2 := by
    have hh := (div_lt_iff₀ hp).mp (show (253/250 : ℝ)*countGammaTwo d/productCapacity d 2 < 1249/1250 by linarith)
    linarith
  exact hbase.trans (quadratic_diagonal_product_margin hd)

theorem higher_finite_product_density_gap {d j : ℕ} (hd : 9 ≤ d)
    (hj : j ∈ activeHigherIndices d) :
    (253/250 : ℝ)*higherCountGamma d j <
      diagonalOutputDensity d j/(2^(d-j+1)*((d-j).factorial : ℝ)) := by
  have hj4 := (Finset.mem_filter.mp hj).2
  have hbounds := activeEvenIndices_bounds (show 3 ≤ d by omega) (Finset.mem_filter.mp hj).1
  rw [higher_diagonal_product_identity (by omega) hbounds.2.1.le]
  exact (div_lt_one (productCapacity_pos d j)).mp (higher_product_capacity hd hj)

end Froberg
