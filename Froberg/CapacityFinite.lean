module

public import Froberg.CapacityRatios

@[expose] public section

/-! # Exact capacity checks in degrees nine through twelve -/

noncomputable section
namespace Froberg

private theorem finite_higher_indices {d j : ℕ} (hd : 9 ≤ d) (hd' : d ≤ 12)
    (hj : j ∈ activeHigherIndices d) : j = 4 ∨ j = 6 := by
  have hj' := (Finset.mem_filter.mp hj).1
  have h4 := (Finset.mem_filter.mp hj).2
  have he := (activeEvenIndices_bounds (by omega : 3 ≤ d) hj').2.2
  unfold activeEvenIndices at hj'
  rw [if_neg (by omega : ¬d ≤ 8)] at hj'
  simp only [Finset.mem_filter, Finset.mem_range] at hj'
  obtain ⟨k, hk⟩ := he
  omega

/-- The first scalar inequality of B.8, including the quadratic output loss. -/
theorem finite_quadratic_scalar_capacity {d : ℕ} (hd : 9 ≤ d) (hd' : d ≤ 12) :
    (253 / 250 : ℝ) * countGammaTwo d / scalarCapacity d 2 * (5000 / 4999) +
      (scalarCapacityBinomial d 2 : ℝ) * criticalRatio d < 1 := by
  have hρ := criticalRatio_rational_upper (d := d) (by omega)
  have hρ2 := quadratic_critical_ratio_lt
  interval_cases d <;>
    norm_num [Nat.choose_eq_factorial_div_factorial, countGammaTwo, countTauFour, scalarCapacity, scalarCapacityBinomial,
      centralHalfBinomial] at hρ ⊢ <;> linarith

/-- The quadratic product inequality of B.9. -/
theorem finite_quadratic_product_capacity {d : ℕ} (hd : 9 ≤ d) (hd' : d ≤ 12) :
    (253 / 250 : ℝ) * countGammaTwo d / productCapacity d 2 * (1250 / 1249) < 1 := by
  have hρ2 := quadratic_critical_ratio_lt
  interval_cases d <;>
    norm_num [Nat.choose_eq_factorial_div_factorial, countGammaTwo, countTauFour, productCapacity] <;> linarith

/-- Every active higher family satisfies both scalar and product capacities. -/
theorem finite_higher_capacities {d j : ℕ} (hd : 9 ≤ d) (hd' : d ≤ 12)
    (hj : j ∈ activeHigherIndices d) :
    2 * (253 / 250 : ℝ) * higherCountGamma d j / scalarCapacity d j +
      (scalarCapacityBinomial d j : ℝ) * criticalRatio d < 1 ∧
    (253 / 250 : ℝ) * higherCountGamma d j / productCapacity d j < 1 := by
  have hρ := criticalRatio_rational_upper (d := d) (by omega)
  rcases finite_higher_indices hd hd' hj with rfl | rfl
  all_goals constructor
  all_goals interval_cases d <;>
    norm_num [Nat.choose_eq_factorial_div_factorial, higherCountGamma, scalarCapacity, scalarCapacityBinomial,
      productCapacity, centralHalfBinomial] at hρ ⊢ <;> linarith

end Froberg
