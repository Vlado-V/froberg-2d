module

public import Froberg.CapacityFactors
public import Froberg.CapacityQuadratic
public import Froberg.CapacityBinomial

@[expose] public section

/-! # Uniform scalar-capacity inequalities -/

noncomputable section
namespace Froberg

private theorem scalar_step_factor_bound {j d t : ℕ} (hj : 6 ≤ j) (hd : t + 7 ≤ d) :
    (((j : ℝ) + 1) * ((j : ℝ) - 3) /
        ((2 * (j : ℝ) - 2) * (2 * (j : ℝ) - 3))) *
      (((2 * (t : ℝ) + 6) * (2 * (t : ℝ) + 5)) /
        (((t : ℝ) + 5) * ((d : ℝ) + (t : ℝ) + 1))) < 1 := by
  have hjR : (6 : ℝ) ≤ j := by exact_mod_cast hj
  have hdR : (t : ℝ) + 7 ≤ d := by exact_mod_cast hd
  have hj2 : 0 < 2 * (j : ℝ) - 2 := by linarith
  have hj3 : 0 < 2 * (j : ℝ) - 3 := by linarith
  have hL : ((j : ℝ) + 1) * ((j : ℝ) - 3) /
      ((2 * (j : ℝ) - 2) * (2 * (j : ℝ) - 3)) < 1 / 3 := by
    apply (div_lt_iff₀ (mul_pos hj2 hj3)).mpr
    nlinarith [sq_nonneg ((j : ℝ) - 2)]
  have hR : ((2 * (t : ℝ) + 6) * (2 * (t : ℝ) + 5)) /
      (((t : ℝ) + 5) * ((d : ℝ) + (t : ℝ) + 1)) < 2 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    have hp := mul_nonneg (show 0 ≤ (t : ℝ) + 5 by positivity)
      (show 0 ≤ (d : ℝ) - (t : ℝ) - 7 by linarith)
    nlinarith [Nat.cast_nonneg (α := ℝ) t]
  have hRpos : 0 < ((2 * (t : ℝ) + 6) * (2 * (t : ℝ) + 5)) /
      (((t : ℝ) + 5) * ((d : ℝ) + (t : ℝ) + 1)) := by positivity
  exact (mul_lt_mul hL hR.le hRpos (by norm_num : (0 : ℝ) ≤ 1 / 3)).trans (by norm_num)

/-- The higher scalar ratios strictly decrease with the layer index. -/
theorem higher_scalar_ratio_step {d j : ℕ} (hj : 6 ≤ j) (hjd : j + 1 ≤ d) :
    higherCountGamma d (j + 1) / scalarCapacity d (j + 1) <
      higherCountGamma d j / scalarCapacity d j := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hjd
  have h₁ : j + 1 + t - (j + 1) = t := by omega
  have h₂ : j + 1 + t - j = t + 1 := by omega
  rw [higher_scalar_factorization (by omega : 6 ≤ j + 1) (by omega),
    higher_scalar_factorization hj (by omega), h₁, h₂,
    scalarLeftFactor_step hj, scalarRightFactor_step (j + 1 + t) t]
  have hfac := scalar_step_factor_bound (j := j) (d := j + 1 + t) (t := t) hj (by omega)
  have hp : 0 < scalarLeftFactor j * scalarRightFactor (j + 1 + t) (t + 1) :=
    mul_pos scalarLeftFactor_pos scalarRightFactor_pos
  have hh := mul_lt_mul_of_pos_left hfac hp
  nlinarith only [hh]

/-- Every layer starting at six is bounded by the initial sixth-layer ratio. -/
theorem higher_scalar_density_bound {d j : ℕ} (hj : 6 ≤ j) (hjd : j ≤ d) :
    higherCountGamma d j / scalarCapacity d j < (1 / 7 : ℝ) := by
  revert hjd
  induction j, hj using Nat.le_induction with
  | base => exact fun hd => gamma_six_scalar_bound hd
  | succ j hj ih =>
      intro hjd
      exact (higher_scalar_ratio_step hj hjd).trans (ih (by omega))

/-- The quadratic scalar inequality in B.8 for all degrees at least nine. -/
theorem quadratic_scalar_capacity {d : ℕ} (hd : 9 ≤ d) :
    (253 / 250 : ℝ) * countGammaTwo d / scalarCapacity d 2 * (5000 / 4999) +
      (scalarCapacityBinomial d 2 : ℝ) * criticalRatio d < 1 := by
  have h₁ := quadratic_scalar_density_bound hd
  have h₂ := quadratic_scalar_source_bound hd
  rw [mul_div_assoc]
  linarith

/-- Every active higher scalar family satisfies B.8 uniformly. -/
theorem higher_scalar_capacity {d j : ℕ} (hd : 9 ≤ d) (hj : j ∈ activeHigherIndices d) :
    2 * (253 / 250 : ℝ) * higherCountGamma d j / scalarCapacity d j +
      (scalarCapacityBinomial d j : ℝ) * criticalRatio d < 1 := by
  have hj4 := (Finset.mem_filter.mp hj).2
  have hbase := activeEvenIndices_bounds (by omega : 3 ≤ d) (Finset.mem_filter.mp hj).1
  have hρ := higher_scalar_source_bound hj4 hbase.2.1.le
  have hγ : higherCountGamma d j / scalarCapacity d j < (2 / 5 : ℝ) := by
    by_cases hjFour : j = 4
    · subst j
      exact gamma_four_scalar_bound (by omega)
    · have hj6 : 6 ≤ j := by
        obtain ⟨k, hk⟩ := hbase.2.2
        omega
      exact (higher_scalar_density_bound hj6 hbase.2.1.le).trans (by norm_num)
  rw [mul_div_assoc]
  linarith

end Froberg
