import Froberg.TargetCosts

/-! # The convolution dimension identity and coverage of target rows -/

noncomputable section
namespace Froberg

/-- The source and target dimensions in symmetric-power convolution agree. -/
theorem convolution_dimension_identity {m a e : ℕ} (hm : 1 ≤ m) (ha : 1 ≤ a) :
    (m + a + e - 2).choose e * (m + a - 2).choose (a - 1) =
      (a + e - 1).choose e * (m + a + e - 2).choose (a + e - 1) := by
  have h := Nat.choose_mul (n := m + a + e - 2) (k := a + e - 1)
    (s := e) (by omega)
  rw [show m + a + e - 2 - e = m + a - 2 by omega,
    show a + e - 1 - e = a - 1 by omega] at h
  simpa only [mul_comm] using h.symm

/-- The listed even layers cover every positive row above four and below the pure cutoff. -/
theorem higher_layers_cover_targets {d b : ℕ} (hd : 3 ≤ d) (hb : 5 ≤ b)
    (hbd : b ≤ d) (hcut : b < d ∨ Odd d) :
    ∃ j ∈ activeHigherIndices d, j < b ∧ b < 2 * j ∧
      targetCost d j b < (101 / 100 : ℝ) * higherCountGamma d j := by
  by_cases hsmall : b ≤ 7
  · refine ⟨4, ?_, by omega, by omega, ?_⟩
    · unfold activeHigherIndices activeEvenIndices
      split_ifs with hd8
      · norm_num
        omega
      · simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨⟨by omega, by decide, by omega⟩, by omega⟩
    · exact fourth_target_cost_margin (by omega) hb hsmall (by omega)
  · let j := 2 * (b / 4 + 1)
    have hj6 : 6 ≤ j := by dsimp [j]; omega
    have hjb : j < b := by dsimp [j]; omega
    have hbj : b < 2 * j := by dsimp [j]; omega
    have hstart : 2 * j - 4 ≤ b := by dsimp [j]; omega
    have hmax : j ≤ 2 * ((d + 3) / 4) := by
      dsimp [j]
      rcases hcut with hcut | ⟨k, hk⟩ <;> omega
    have hd9 : 9 ≤ d := by
      rcases hcut with hcut | ⟨k, hk⟩ <;> omega
    refine ⟨j, ?_, hjb, hbj, ?_⟩
    · unfold activeHigherIndices activeEvenIndices
      rw [if_neg (by omega : ¬d ≤ 8)]
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨⟨by omega, ⟨b / 4 + 1, by dsimp [j]; omega⟩, by omega⟩, by omega⟩
    · exact higher_target_cost_margin hj6 (by omega) hstart hbj (by omega)

end Froberg
