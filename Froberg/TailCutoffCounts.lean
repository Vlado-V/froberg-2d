import Froberg.TopCountInequalities

/-! The prescribed rounded pure-generator count fills the next degree for
all sufficiently large numbers of variables. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem eventually_next_degree_count_of_limit {d : ℕ} (r : ℕ → ℕ) (c : ℝ)
    (hr : Tendsto (fun h : ℕ => (r h : ℝ)/(h : ℝ)^d) atTop (𝓝 c))
    (hc : (((d+1).factorial : ℝ)⁻¹)<c) :
    ∀ᶠ h : ℕ in atTop,(h+(d+1)-1).choose (d+1)≤r h*h := by
  have hright : Tendsto (fun h : ℕ => ((r h : ℝ)*h)/(h : ℝ)^(d+1)) atTop (𝓝 c) := by
    apply hr.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with h hh
    have hne : (h : ℝ)≠0 := by exact_mod_cast hh.ne'
    rw [pow_succ]
    field_simp
  filter_upwards [(monomial_count_normalized_tendsto (d+1)).eventually_lt hright hc,
    eventually_gt_atTop (0 : ℕ)] with h hlt hh
  have hpos : (0 : ℝ)<h := by exact_mod_cast hh
  have hlt' := (div_lt_div_iff_of_pos_right (pow_pos hpos (d+1))).mp hlt
  exact_mod_cast hlt'.le

theorem eventually_tail_cutoff_count {d : ℕ} (hd : 0<d) :
    ∀ᶠ h : ℕ in atTop,(h+(d+1)-1).choose (d+1)≤tailGeneratorCount d h*h := by
  by_cases ho : Odd d
  · apply eventually_next_degree_count_of_limit _ _ (odd_tail_normalized_limit hd ho)
    have hp : (0 : ℝ)<(d+1).factorial := by exact_mod_cast Nat.factorial_pos _
    rw [inv_eq_one_div]
    exact div_lt_div_of_pos_right (by norm_num) hp
  · apply eventually_next_degree_count_of_limit _ ((d.factorial : ℝ)⁻¹)
    · simpa only [tailGeneratorCount,if_neg ho] using monomial_count_normalized_tendsto d
    · rw [factorial_add_one_real]
      have hdR : (0 : ℝ)<d := by exact_mod_cast hd
      have hp : (0 : ℝ)<d.factorial := by exact_mod_cast Nat.factorial_pos d
      exact inv_strictAnti₀ hp (by nlinarith)

end Froberg
