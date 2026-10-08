import Froberg.CapacityProductBounds
import Froberg.CapacityFinite
import Froberg.CapacityFactorials

/-! # Product-capacity inequalities in all degrees at least nine -/

noncomputable section
namespace Froberg

/-- A uniform exponential bound for the quadratic density. -/
theorem quadratic_product_density_bound {d : ℕ} (hd : 9 ≤ d) :
    countGammaTwo d / productCapacity d 2 <
      64 * (2 * (d : ℝ) - 3) / (2 : ℝ) ^ d := by
  have hC : (0 : ℝ) < (2 * d - 4).choose (d - 2) := by
    exact_mod_cast Nat.choose_pos (show d - 2 ≤ 2 * d - 4 by omega)
  have hcentral : (d - 2).centralBinom = (2 * d - 4).choose (d - 2) := by
    simp only [Nat.centralBinom]
    congr 1 <;> omega
  have hl : (4 : ℝ) ^ (d - 2) ≤
      (2 * ((d - 2 : ℕ) : ℝ) + 1) * ((2 * d - 4).choose (d - 2) : ℝ) := by
    exact_mod_cast (hcentral ▸ Nat.four_pow_le_two_mul_add_one_mul_centralBinom (d - 2))
  have hl' : (4 : ℝ) ^ (d - 2) ≤
      2 * (2 * ((d - 2 : ℕ) : ℝ) + 1) * ((2 * d - 4).choose (d - 2) : ℝ) := by
    nlinarith [show 0 ≤ (4 : ℝ) ^ (d - 2) by positivity]
  have h := reciprocal_of_binomial_lower_bound (d - 2) _ hC hl'
  rw [show d - 2 + 3 = d + 1 by omega, show d - 2 + 2 = d by omega,
    Nat.cast_sub (by omega : 2 ≤ d), Nat.cast_ofNat] at h
  have h' : (2 : ℝ) ^ (d + 1) / ((2 * d - 4).choose (d - 2) : ℝ) ≤
      64 * (2 * (d : ℝ) - 3) / (2 : ℝ) ^ d := by
    convert h using 1 <;> ring
  have hρ : criticalRatio 2 < 1 := (quadratic_critical_ratio_lt).trans (by norm_num)
  have hp : 0 < (2 : ℝ) ^ (d + 1) / ((2 * d - 4).choose (d - 2) : ℝ) := div_pos (by positivity) hC
  have hlt := mul_lt_mul_of_pos_right hρ hp
  rw [one_mul] at hlt
  have hg : countGammaTwo d = countTauFour d := by
    simp [countGammaTwo, show ¬d ≤ 8 by omega]
  rw [hg, tauFour_product_ratio (by omega), mul_div_assoc]
  exact hlt.trans_le h'

/-- The actual fourth-layer density is smaller than its scalar-capacity ratio. -/
theorem fourth_actual_product_density_bound {d : ℕ} (hd : 8 ≤ d) :
    higherCountGamma d 4 / productCapacity d 4 <
      64 * (2 * (d : ℝ) - 3) / (2 : ℝ) ^ d := by
  have hγ := gamma_four_scalar_bound (d := d) (by omega)
  have hγ' : higherCountGamma d 4 < scalarCapacity d 4 := by
    have h := (div_lt_iff₀ (scalarCapacity_pos d 4)).mp hγ
    have hp := scalarCapacity_pos d 4
    nlinarith
  exact (div_lt_div_of_pos_right hγ' (productCapacity_pos d 4)).trans_le
    (fourth_product_density_bound hd)

/-- B.9 for the quadratic products. -/
theorem quadratic_product_capacity {d : ℕ} (hd : 9 ≤ d) :
    (253 / 250 : ℝ) * countGammaTwo d / productCapacity d 2 * (1250 / 1249) < 1 := by
  by_cases hsmall : d ≤ 12
  · exact finite_quadratic_product_capacity hd hsmall
  have h := (quadratic_product_density_bound hd).trans_le
    (capacity_linear_power_bound (by omega : 13 ≤ d))
  rw [mul_div_assoc]
  linarith

/-- B.9 for every active higher product family. -/
theorem higher_product_capacity {d j : ℕ} (hd : 9 ≤ d) (hj : j ∈ activeHigherIndices d) :
    (253 / 250 : ℝ) * higherCountGamma d j / productCapacity d j < 1 := by
  by_cases hsmall : d ≤ 12
  · exact (finite_higher_capacities hd hsmall hj).2
  have hd13 : 13 ≤ d := by omega
  have hj4 := (Finset.mem_filter.mp hj).2
  have hbase := activeEvenIndices_bounds (by omega : 3 ≤ d) (Finset.mem_filter.mp hj).1
  by_cases hjFour : j = 4
  · subst j
    have h := (fourth_actual_product_density_bound (by omega : 8 ≤ d)).trans_le
      (capacity_linear_power_bound hd13)
    rw [mul_div_assoc]
    linarith
  · have hj6 : 6 ≤ j := by
      obtain ⟨k, hk⟩ := hbase.2.2
      omega
    have ht : 4 ≤ d - j := by
      have he := (Finset.mem_filter.mp hj).1
      unfold activeEvenIndices at he
      rw [if_neg (by omega : ¬d ≤ 8)] at he
      simp only [Finset.mem_filter, Finset.mem_range] at he
      omega
    have h := (higher_product_density_bound hj6 ht hbase.2.1.le).trans
      (capacity_quadratic_power_bound hd13)
    rw [mul_div_assoc]
    linarith

end Froberg
