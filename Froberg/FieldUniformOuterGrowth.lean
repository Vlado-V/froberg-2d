module

public import Froberg.UniformOuterGrowth

@[expose] public section

/-! The strict-growth cutoff depends on numerical profiles, before any field
or coefficient vectors are chosen. -/
noncomputable section
namespace Froberg
open Module Finset Filter MonomialExpansion OuterInjection
open scoped Topology

theorem uniform_shadow_surplus_numeric
    (A T₀ D E : ℕ → ℝ) (s : ℕ)
    {a t c H : ℝ} (ha : 0 < a) (ht : 0 < t) (hc : 0 < c) (hH : 0 ≤ H)
    (hA : Tendsto (fun n => A n / (n : ℝ) ^ s) atTop (𝓝 a))
    (hT₀ : Tendsto (fun n => T₀ n / (n : ℝ) ^ (2 * s + 1)) atTop (𝓝 t))
    (hD : Tendsto (fun n => D n / (n : ℝ) ^ (2 * s + 1)) atTop (𝓝 0))
    (hE : Tendsto (fun n => E n / (n : ℝ) ^ (s + 1)) atTop (𝓝 0)) :
    ∃ g : ℝ, 0 < g ∧ ∀ᶠ n : ℕ in atTop, ∀ T x I : ℝ,
      T₀ n ≤ T → T - T₀ n ≤ D n → 0 ≤ D n → 0 ≤ x → x ≤ A n →
      T₀ n / A n * x + (c * (T₀ n / A n) - E n) * min x (A n - x) ≤ I →
      T - (H * n) * (A n - x) ^ 2 ≤ I →
      T / A n * x + g * (n : ℝ) ^ (s + 1) * min x (A n - x) ≤ I := by
  let q := t / a
  have hq : 0 < q := div_pos ht ha
  let g := min c 1 * q / 4
  let δ := q / (4 * (H + 1))
  have hg : 0 < g := by dsimp [g]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hgc : g < c * (t / a) := by
    have hm := mul_le_mul_of_nonneg_right (min_le_left c 1) hq.le
    have hp : 0 < c * q := mul_pos hc hq
    dsimp [g]
    change min c 1 * q / 4 < c * q
    linarith
  have hgq : g ≤ q / 4 := by
    have hm := mul_le_mul_of_nonneg_right (min_le_right c 1) hq.le
    dsimp [g]
    linarith
  have hHδ : H * δ ≤ q / 4 := by
    dsimp [δ]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    have hden : 0 < 4 * (H + 1) := by positivity
    have hid : q / (4 * (H + 1)) * (4 * (H + 1)) = q := div_mul_cancel₀ q hden.ne'
    have hp : 0 < q / (4 * (H + 1)) := div_pos hq hden
    nlinarith
  have hnear : H * δ + g < t / a := by change H * δ + g < q; linarith
  have hfar := far_shadow_gap_eventually A T₀ D E s ha hδ hgc hA hT₀ hD hE
  have hnear' := near_shadow_gap_eventually A T₀ s ha hnear hA hT₀
  refine ⟨g, hg, ?_⟩
  filter_upwards [hfar, hnear', normalized_limit_eventually_pos A ha s hA,
    eventually_gt_atTop (0 : ℕ)] with n hnfar hnnear hnA hn0
  intro T x I hT hTD hD0 hx hxA hS hQ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hK : 0 < δ * (n : ℝ) ^ s := mul_pos hδ (pow_pos hnR s)
  by_cases hk : δ * (n : ℝ) ^ s ≤ A n - x
  · exact absorb_shadow_error hnA hx hK hk hD0 hTD hS hnfar
  · apply absorb_quadratic_cokernel hnA hx hxA (mul_nonneg hH hnR.le)
      (le_of_not_ge hk) (mul_nonneg hg.le (pow_nonneg hnR.le _)) hQ
    exact hnnear.trans (div_le_div_of_nonneg_right hT hnA.le)

theorem field_uniform_core_outer_growth
    {k s h : ℕ} (hk : 0 < k) (hs : 0 < s) (hh : h=k*(2*s+1).choose s)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    (a z : ℕ → ℕ) (ha : Tendsto a atTop atTop) (hz : Tendsto z atTop atTop)
    (har : Tendsto (fun n : ℕ => (a n : ℝ)/n) atTop (𝓝 σ))
    (hzr : Tendsto (fun n : ℕ => (z n : ℝ)/n) atTop (𝓝 (1-σ)))
    (haz : ∀ n, a n+z n=n) :
    ∃ g : ℝ, 0 < g ∧ ∀ᶠ n in atTop,
      ∀ (K : Type) [Field K] (v : Labels k (a n) s → Fin h → K),
      (∀ U : Finset (Labels k (a n) s), U.card ≤ h → LinearIndependent K (fun i : U => v i.val)) →
      MixedExterior.UniversalMixedPosition v →
      ∀ L : Submodule K (CoreSourceSpace (z := z n) v),
      ((finrank K (CoreTargetSpace (z := z n) v) : ℝ)/finrank K (CoreSourceSpace (z := z n) v))*finrank K L +
      g*(n : ℝ)^(s+1)*min (finrank K L : ℝ)
        ((finrank K (CoreSourceSpace (z := z n) v) : ℝ)-finrank K L) ≤
      (finrank K (AttachedMultiplication.outerImage (d := s+1)
        (coreExponent (z n)) v (coreExponent_degree (z n)) L) : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hH := profileAmbientCapacity_gt_one hs
  obtain ⟨c,hc,hexp⟩ := uniform_exponent_shadow hσ hσ1 hs a z ha hz har hzr haz (k : ℝ) hkR
  let A := fun n => (k : ℝ)*∑ i, finiteSourceProfile (profileAmbientCapacity s) s (a n) (z n) i
  let T₀ := fun n => (k : ℝ)*∑ j, finiteTargetProfile s (a n) (z n) j
  let D := fun n : ℕ => (h : ℝ)*n*((n+(2*s-1)-1).choose (2*s-1) : ℝ)
  let E := fun n : ℕ => (h : ℝ)*(h*2^h)*((n+s-1).choose s : ℝ)
  have hAlim : Tendsto (fun n => A n/(n : ℝ)^s) atTop
      (𝓝 ((k : ℝ)*sourceProfileScale (profileAmbientCapacity s) σ s)) := by
    simpa only [A,mul_div_assoc] using
      (sourceProfile_total_limit hH hσ hσ1 hs a z ha hz har hzr).const_mul (k : ℝ)
  have hTlim : Tendsto (fun n => T₀ n/(n : ℝ)^(2*s+1)) atTop
      (𝓝 ((k : ℝ)*targetProfileScale σ s)) := by
    simpa only [T₀,mul_div_assoc] using
      (targetProfile_total_limit hσ hσ1 hs a z ha hz har hzr).const_mul (k : ℝ)
  obtain ⟨g,hg,hev⟩ := uniform_shadow_surplus_numeric A T₀ D E s
    (mul_pos hkR (sourceProfileScale_pos hH hσ hσ1 hs))
    (mul_pos hkR (targetProfileScale_pos hσ hσ1 hs)) hc (Nat.cast_nonneg h)
    hAlim hTlim (target_discrepancy_error_lower_order (h : ℝ) hs)
    (exceptional_projection_error_lower_order ((h : ℝ)*(h*2^h)) s)
  refine ⟨g,hg,?_⟩
  filter_upwards [hev,hexp,eventually_gt_atTop (0 : ℕ)] with n hn hne hn0
  intro K _ v hv hm L
  have hAeq : (finrank K (CoreSourceSpace (z := z n) v) : ℝ) = A n :=
    outer_source_dimension_profile hh v hv
  have hb := outer_target_dimension_budget (z := z n) hh v hv
  have hbudget : (finrank K (CoreTargetSpace (z := z n) v) : ℝ)-T₀ n ≤ D n := by
    have hazR : (a n : ℝ)+(z n : ℝ)=(n : ℝ) := by exact_mod_cast haz n
    simpa only [D,haz n,show 2*s+1-2=2*s-1 by omega,hazR] using hb.2
  have hratio : T₀ n/A n =
      (∑ j, finiteTargetProfile s (a n) (z n) j)/
      (∑ i, finiteSourceProfile (profileAmbientCapacity s) s (a n) (z n) i) := by
    exact mul_div_mul_left _ _ hkR.ne'
  have hpos : 0 < a n+z n := by rw [haz]; exact hn0
  have hshadow := actual_outer_growth_of_exponent_shadow hh hpos v hv hm
    (T₀ n/A n) (c*(T₀ n/A n)) (by rw [hratio]; exact hne) L
  have hquad := AttachedMultiplication.outer_image_codimension_le
    (coreExponent (z n)) v (coreExponent_degree (z n)) L
  have hsource := Submodule.finrank_le L
  have htarget := Submodule.finrank_le (AttachedMultiplication.outerImage (d := s+1)
    (coreExponent (z n)) v (coreExponent_degree (z n)) L)
  rw [hAeq]
  apply hn _ _ _ hb.1 hbudget (by dsimp [D]; positivity) (Nat.cast_nonneg _)
  · rw [← hAeq]
    exact_mod_cast hsource
  · simpa only [hAeq,E,haz n,mul_assoc] using hshadow
  · have hcast := (Nat.cast_le (α := ℝ)).mpr hquad
    simp only [Nat.cast_sub htarget,Nat.cast_mul,Nat.cast_pow,Nat.cast_sub hsource,
      Nat.cast_add] at hcast
    have hazR : (a n : ℝ)+(z n : ℝ)=(n : ℝ) := by exact_mod_cast haz n
    rw [hazR,hAeq] at hcast
    nlinarith

end Froberg
