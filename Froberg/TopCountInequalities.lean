import Froberg.TopCountLimits

/-! # The eventual numerical hypotheses for projected top-degree multiplication -/

noncomputable section
namespace Froberg
open Filter Polynomial
open scoped Topology

/-- The incidence ratio itself tends to infinity. -/
theorem odd_top_incidence_ratio_atTop {d : ℕ} (hd : 3 ≤ d) (ho : Odd d) :
    Tendsto (fun h : ℕ => (tailGeneratorCount d h : ℝ) * topComplementCount d h /
      (topSourceCount d h : ℝ) ^ 2) atTop atTop := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hc : 0 < 2 * ((d : ℝ) - 1) / ((d : ℝ) ^ 2 * ((d : ℝ) + 1) ^ 2) := by
    apply div_pos (by linarith) (by positivity)
  have h := (odd_top_incidence_ratio_limit hd ho).pos_mul_atTop hc
    (nat_power_tendsto_atTop 2 (by omega))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have haR : (topSourceCount d n : ℝ) ≠ 0 := by exact_mod_cast (topSourceCount_pos hn).ne'
  field_simp

/-- For large `h`, the Schubert-condition surplus exceeds the indexing dimension. -/
theorem odd_top_incidence_eventually {d : ℕ} (hd : 3 ≤ d) (ho : Odd d) :
    ∀ᶠ h : ℕ in atTop, (topSourceCount d h : ℝ) ^ 2 <
      (tailGeneratorCount d h : ℝ) * topComplementCount d h := by
  filter_upwards [(odd_top_incidence_ratio_atTop hd ho).eventually_gt_atTop 1,
    eventually_gt_atTop (0 : ℕ)] with h hh hh0
  have ha : (0 : ℝ) < topSourceCount d h := by exact_mod_cast topSourceCount_pos hh0
  exact (one_lt_div (by positivity)).mp hh

/-- Away from degree three, the limiting ratio has a strict margin over `1/(2d)`. -/
theorem odd_top_projection_eventually_large {d : ℕ} (hd : 4 ≤ d) (ho : Odd d) :
    ∀ᶠ h : ℕ in atTop, (h : ℝ) / (2 * (d : ℝ)) ≤
      (topComplementCount d h : ℝ) / topSourceCount d h := by
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hc : 1 / (2 * (d : ℝ)) < ((d : ℝ) - 1) / ((d : ℝ) * ((d : ℝ) + 1)) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have he := (odd_top_complement_ratio_limit (by omega : 3 ≤ d) ho).eventually (lt_mem_nhds hc)
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with h hh hh0
  have ha : (0 : ℝ) < topSourceCount d h := by exact_mod_cast topSourceCount_pos hh0
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh0
  apply (le_div_iff₀ ha).mpr
  have hp := (lt_div_iff₀ (mul_pos ha hhR)).mp hh
  calc
    (h : ℝ) / (2 * (d : ℝ)) * topSourceCount d h =
        (1 / (2 * (d : ℝ))) * ((topSourceCount d h : ℝ) * h) := by ring
    _ ≤ (topComplementCount d h : ℝ) := hp.le

theorem monomial_count_two_real (h : ℕ) :
    ((h + 2 - 1).choose 2 : ℝ) = (h : ℝ) * ((h : ℝ) + 1) / 2 := by
  rw [← monomialCountPolynomial_eval]
  norm_num [monomialCountPolynomial, ascPochhammer_succ_eval]
  ring

theorem monomial_count_three_real (h : ℕ) :
    ((h + 3 - 1).choose 3 : ℝ) = (h : ℝ) * ((h : ℝ) + 1) * ((h : ℝ) + 2) / 6 := by
  rw [← monomialCountPolynomial_eval]
  norm_num [monomialCountPolynomial, ascPochhammer_succ_eval]
  ring

/-- The degree-three case uses the positive next-order terms in the exact dimensions. -/
theorem cubic_top_projection_eventually :
    ∀ᶠ h : ℕ in atTop, (h : ℝ) / 6 ≤
      (topComplementCount 3 h : ℝ) / topSourceCount 3 h := by
  filter_upwards [(odd_top_count_budget_limit (d := 3) (by omega) (by decide)).1,
    eventually_ge_atTop (2 : ℕ)] with h hbudget hh2
  have hhR : (2 : ℝ) ≤ h := by exact_mod_cast hh2
  have ha : (0 : ℝ) < topSourceCount 3 h := by exact_mod_cast topSourceCount_pos (by omega : 0 < h)
  have hA : (topSourceCount 3 h : ℝ) = (h : ℝ) * ((h : ℝ) + 1) / 2 :=
    monomial_count_two_real h
  have hN := monomial_count_three_real h
  have hU : (tailGeneratorCount 3 h : ℝ) < 2 * (h : ℝ) ^ 3 / ((4 : ℕ).factorial : ℝ) + 1 := by
    simpa only [tailGeneratorCount, if_pos (by decide : Odd 3)] using
      Nat.ceil_lt_add_one (show 0 ≤ 2 * (h : ℝ) ^ 3 / ((4 : ℕ).factorial : ℝ) by positivity)
  apply (le_div_iff₀ ha).mpr
  rw [topComplementCount, Nat.cast_sub hbudget, hA]
  norm_num only [Nat.factorial] at hU
  nlinarith

/-- The projected multiplication ratio required by C.3, including degree three. -/
theorem odd_top_projection_eventually {d : ℕ} (hd : 3 ≤ d) (ho : Odd d) :
    ∀ᶠ h : ℕ in atTop, (h : ℝ) / (2 * (d : ℝ)) ≤
      (topComplementCount d h : ℝ) / topSourceCount d h := by
  by_cases hd3 : d = 3
  · subst d
    simpa only [Nat.cast_ofNat, show (2 : ℝ) * 3 = 6 by norm_num] using cubic_top_projection_eventually
  · exact odd_top_projection_eventually_large (by omega) ho

/-- Both numerical inputs hold for the actual rounded pure-family count. -/
theorem odd_top_projection_hypotheses {d : ℕ} (hd : 3 ≤ d) (ho : Odd d) :
    ∀ᶠ h : ℕ in atTop,
      tailGeneratorCount d h ≤ (h + d - 1).choose d ∧
      (topSourceCount d h : ℝ) ^ 2 < (tailGeneratorCount d h : ℝ) * topComplementCount d h ∧
      (h : ℝ) / (2 * (d : ℝ)) ≤ (topComplementCount d h : ℝ) / topSourceCount d h := by
  exact ((odd_top_count_budget_limit hd ho).1.and (odd_top_incidence_eventually hd ho)).and
    (odd_top_projection_eventually hd ho) |>.mono (fun _ h => ⟨h.1.1, h.1.2, h.2⟩)

end Froberg
