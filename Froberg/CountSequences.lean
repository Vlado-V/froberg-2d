import Froberg.ExactOuterLimit

/-! Simultaneous actual count sequences for the two adjacent critical counts. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem choose_exact_count_sequences {d k h lo : ℕ} {δ : ℝ}
    (hc : ∀ᶠ n in atTop,∀ upper : Bool,∃ a f e,
      ExactCountConditions d k h lo n a f e upper ∧
      δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n f) :
    ∃ a f e : Bool → ℕ → ℕ,
      (∀ upper n,a upper n ≤ n) ∧
      ∀ᶠ n in atTop,∀ upper : Bool,
        ExactCountConditions d k h lo n (a upper n) (f upper n) (e upper n) upper ∧
        δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f upper n) := by
  classical
  obtain ⟨N,hN⟩ := eventually_atTop.mp hc
  have hex (n : ℕ) (upper : Bool) : ∃ t : ℕ × ℕ × ℕ,t.1 ≤ n ∧
      (N ≤ n → ExactCountConditions d k h lo n t.1 t.2.1 t.2.2 upper ∧
        δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n t.2.1) := by
    by_cases hn : N ≤ n
    · obtain ⟨a,f,e,ha,hm⟩ := hN n hn upper
      exact ⟨(a,f,e),ha.core_le,fun _ => ⟨ha,hm⟩⟩
    · exact ⟨(0,0,0),Nat.zero_le _,fun h => False.elim (hn h)⟩
  choose t ht using hex
  refine ⟨fun u n => (t n u).1,fun u n => (t n u).2.1,fun u n => (t n u).2.2,
    fun u n => (ht n u).1,?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  exact fun u => (ht n u).2 hn

theorem nat_tendsto_atTop_of_positive_ratio (a : ℕ → ℕ) {σ : ℝ} (hσ : 0 < σ)
    (ha : Tendsto (fun n : ℕ => (a n : ℝ)/n) atTop (𝓝 σ)) : Tendsto a atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  have hbound : (fun n : ℕ => (σ/2)*(n : ℝ)) ≤ᶠ[atTop] (fun n => (a n : ℝ)) := by
    filter_upwards [ha.eventually (lt_mem_nhds (show σ/2<σ by linarith)),
      eventually_gt_atTop (0 : ℕ)] with n hn hn0
    exact ((lt_div_iff₀ (by exact_mod_cast hn0)).mp hn).le
  exact tendsto_atTop_mono' atTop hbound
    (Tendsto.const_mul_atTop (by positivity) tendsto_natCast_atTop_atTop)

theorem complement_ratio_limit (a : ℕ → ℕ) (ha : ∀ n,a n ≤ n) {σ : ℝ}
    (hr : Tendsto (fun n : ℕ => (a n : ℝ)/n) atTop (𝓝 σ)) :
    Tendsto (fun n : ℕ => ((n-a n : ℕ) : ℝ)/n) atTop (𝓝 (1-σ)) := by
  apply ((tendsto_const_nhds (x := (1 : ℝ))).sub hr).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnp : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Nat.cast_sub (ha n),sub_div,div_self hnp]

theorem exact_conditions_core_limits {d k h lo : ℕ} (hd : 3 ≤ d)
    (hk : 0 < k) (hh : h=k*centralHalfBinomial d)
    (upper : Bool) (a f e : ℕ → ℕ) (ha : ∀ n,a n ≤ n)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper) :
    Tendsto a atTop atTop ∧ Tendsto (fun n => n-a n) atTop atTop ∧
    Tendsto (fun n : ℕ => (a n : ℝ)/n) atTop (𝓝 (limitingCoreFraction d)) ∧
    Tendsto (fun n : ℕ => ((n-a n : ℕ) : ℝ)/n) atTop (𝓝 (1-limitingCoreFraction d)) := by
  have hr := exact_counts_core_limit hd hk hh (auxiliaryGeneratorCount d h)
    (fun n => adjacentCriticalCount upper n d) a f e
    (fun n _ => adjacentCriticalCount_bounds upper n d) (auxiliaryGeneratorCount_lower_order hd h)
    (hc.mono fun n hn => ⟨hn.outer_eq,hn.total,hn.quadratic_upper,hn.core_positive⟩)
  have hs := complement_ratio_limit a ha hr
  have hb := limitingCoreFraction_bounds hd
  exact ⟨nat_tendsto_atTop_of_positive_ratio a hb.1 hr,
    nat_tendsto_atTop_of_positive_ratio _ (sub_pos.mpr hb.2) hs,hr,hs⟩

end Froberg
