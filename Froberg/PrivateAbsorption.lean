module

public import Froberg.ShadowAbsorptionLimits

@[expose] public section

/-! The two uniform analytic margins for extending the core by private columns. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem private_upper_loss_limit {s : ℕ} (hs : 0<s) (A M : ℕ → ℝ)
    (b a m : ℝ) (ha : 0<a)
    (hA : Tendsto (fun n : ℕ => A n/(n : ℝ)^s) atTop (𝓝 a))
    (hM : Tendsto (fun n : ℕ => M n/(n : ℝ)^(s+1)) atTop (𝓝 m)) :
    Tendsto (fun n : ℕ => (b*M n/A n)/(n : ℝ)^(s+1)) atTop (𝓝 (0 : ℝ)) := by
  have h := ((hM.const_mul b).div hA ha.ne').div_atTop (nat_power_tendsto_atTop s hs)
  apply h.congr'
  filter_upwards [hA.eventually (lt_mem_nhds ha), eventually_gt_atTop (0 : ℕ)] with n hAn hn
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hAnR : 0<A n := (div_pos_iff_of_pos_right (pow_pos hnR s)).mp hAn
  simp only [Pi.div_apply]
  field_simp

theorem private_upper_loss_eventually {s : ℕ} (hs : 0<s) (A M : ℕ → ℝ)
    (b a m g : ℝ) (ha : 0<a) (hg : 0<g)
    (hA : Tendsto (fun n : ℕ => A n/(n : ℝ)^s) atTop (𝓝 a))
    (hM : Tendsto (fun n : ℕ => M n/(n : ℝ)^(s+1)) atTop (𝓝 m)) :
    ∀ᶠ n : ℕ in atTop, b*M n/A n ≤ (g/2)*(n : ℝ)^(s+1) := by
  have h := (private_upper_loss_limit hs A M b a m ha hA hM).eventually
    (gt_mem_nhds (show (0 : ℝ)<g/2 by positivity))
  filter_upwards [h,eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hnp : (0 : ℝ)<(n : ℝ)^(s+1) := pow_pos (by exact_mod_cast hn0) _
  exact ((div_lt_iff₀ hnp).mp hn).le

/-- A common strictly positive gain survives both the perturbed core bound
and the independent private-column bound. -/
theorem private_lower_common_margin (d : ℕ) (R G E D R' : ℕ → ℝ)
    (ρ g δ : ℝ) (hg : 0<g) (hδ : ρ<δ)
    (hR : Tendsto (fun n : ℕ => R n/(n : ℝ)^d) atTop (𝓝 ρ))
    (hG : Tendsto (fun n : ℕ => G n/(n : ℝ)^d) atTop (𝓝 g))
    (hE : Tendsto (fun n : ℕ => E n/(n : ℝ)^d) atTop (𝓝 (0 : ℝ)))
    (hD : Tendsto (fun n : ℕ => D n/(n : ℝ)^d) atTop (𝓝 δ))
    (hR' : Tendsto (fun n : ℕ => R' n/(n : ℝ)^d) atTop (𝓝 ρ)) :
    ∃ g' : ℝ, 0<g' ∧ ∀ᶠ n : ℕ in atTop,
      R' n+g'*(n : ℝ)^d ≤ R n+G n-E n ∧ R' n+g'*(n : ℝ)^d ≤ D n := by
  let g' := min g (δ-ρ)/2
  have hpos : 0<g' := by dsimp [g']; exact div_pos (lt_min hg (sub_pos.mpr hδ)) (by norm_num)
  have hleG : g'≤g/2 := by dsimp [g']; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hleD : g'≤(δ-ρ)/2 := by dsimp [g']; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hnew : Tendsto (fun n : ℕ => (R' n+g'*(n : ℝ)^d)/(n : ℝ)^d)
      atTop (𝓝 (ρ+g')) := by
    simpa only [add_div] using hR'.add (scaled_power_normalized_limit g' d)
  have hcore : Tendsto (fun n : ℕ => (R n+G n-E n)/(n : ℝ)^d)
      atTop (𝓝 (ρ+g)) := by
    simpa only [add_div,sub_div,sub_zero] using (hR.add hG).sub hE
  have h₁ := eventually_lt_of_normalized_limits _ _ d _ _ hnew hcore (by linarith)
  have h₂ := eventually_lt_of_normalized_limits _ _ d _ _ hnew hD (by linarith)
  refine ⟨g',hpos,?_⟩
  filter_upwards [h₁,h₂] with n hn₁ hn₂
  exact ⟨hn₁.le,hn₂.le⟩

end Froberg
