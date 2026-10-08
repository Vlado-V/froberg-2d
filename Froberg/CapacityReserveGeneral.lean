import Froberg.CapacityReserve

/-! # The odd top-degree numerical margins in every degree -/

noncomputable section
namespace Froberg

theorem centralHalfBinomial_quadratic_lower {d : ℕ} (hd : 9 ≤ d) :
    4 * d ^ 2 + 3 < centralHalfBinomial d := by
  induction d, hd using Nat.le_induction with
  | base => decide
  | succ d hd ih =>
      have h := centralHalfBinomial_double_step (d := d) (by omega)
      nlinarith

theorem large_top_critical_bound {d : ℕ} (hd : 9 ≤ d) :
    (2 * (d : ℝ) ^ 2 + 1) * criticalRatio d < (1 / 4 : ℝ) := by
  have hH : 4 * (d : ℝ) ^ 2 + 3 < (centralHalfBinomial d : ℝ) := by
    exact_mod_cast centralHalfBinomial_quadratic_lower hd
  have hρ := criticalRatio_rational_upper (d := d) (by omega)
  have hmul := mul_lt_mul_of_pos_left hρ
    (show 0 < 2 * (d : ℝ) ^ 2 + 1 by positivity)
  have hdiv : (2 * (d : ℝ) ^ 2 + 1) / (2 * (centralHalfBinomial d : ℝ) - 1) < 1 / 4 := by
    apply (div_lt_iff₀ (by nlinarith : 0 < 2 * (centralHalfBinomial d : ℝ) - 1)).mpr
    nlinarith
  rw [mul_one_div] at hmul
  exact hmul.trans hdiv

theorem top_scalar_reserve_bound (d : ℕ) :
    (d.factorial : ℝ) * scalarReserveDensity d ≤ (1 / 100 : ℝ) := by
  have h := scalar_reserve_factorial_bound d d
  rw [show 2 * d - d = d by omega, Nat.sub_self] at h
  simpa [mul_comm] using h

/-- The large-degree top margin required by Lemma C.3. -/
theorem large_top_shadow_margin {d : ℕ} (hd : 9 ≤ d) :
    (2 * (d : ℝ) ^ 2 + 1) * criticalRatio d +
      (d.factorial : ℝ) * scalarReserveDensity d < 1 := by
  have hρ := large_top_critical_bound hd
  have hδ := top_scalar_reserve_bound d
  linarith

/-- The top margin holds uniformly in every odd degree at least three. -/
theorem odd_top_shadow_margin {d : ℕ} (hd : 3 ≤ d) (ho : Odd d) :
    (2 * (d : ℝ) ^ 2 + 1) * criticalRatio d +
      (d.factorial : ℝ) * scalarReserveDensity d < 1 := by
  by_cases hlarge : 9 ≤ d
  · exact large_top_shadow_margin hlarge
  · apply small_odd_top_shadow_margin
    obtain ⟨k, hk⟩ := ho
    omega

end Froberg
