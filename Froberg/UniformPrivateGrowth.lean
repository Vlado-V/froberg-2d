module

public import Froberg.PrivateUniformGrowth
public import Froberg.PrivateDimensionLimits
public import Froberg.PrivateAbsorption
public import Froberg.PrivateMultiplierBound

@[expose] public section

/-! Uniform strict expansion of the actual core presentation extended by any
fixed number of private columns. -/
noncomputable section
namespace Froberg.PrivateColumns
open Filter Module OuterInjection AttachedMultiplication
open scoped Topology

lemma uniform_private_outer_growth {K : Type*} [Field K]
    {k s h b : ℕ} (hk : 0 < k) (hs : 2 ≤ s) (hh : h=k*(2*s+1).choose s)
    (a z : ℕ → ℕ) (ha : Tendsto a atTop atTop) (hz : Tendsto z atTop atTop)
    (har : Tendsto (fun n : ℕ => (a n : ℝ)/n) atTop (𝓝 (limitingCoreFraction (s+1))))
    (hzr : Tendsto (fun n : ℕ => (z n : ℝ)/n) atTop (𝓝 (1-limitingCoreFraction (s+1))))
    (haz : ∀ n,a n+z n=n)
    (u : (n : ℕ) → Labels k (a n) s ⊕ Fin b → Fin h → K)
    (hu : ∀ n (U : Finset (Labels k (a n) s ⊕ Fin b)),U.card ≤ h → LinearIndependent K (fun i : U => u n i.val))
    (hm : ∀ n,MixedExterior.UniversalMixedPosition (u n)) :
    ∃ g : ℝ,0 < g ∧ ∀ᶠ n in atTop,∀ ι : Fin b ↪ Fin (z n),
      0 < finrank K (PrivateSourceSpace ι (u n)) ∧
      ∀ L : Submodule K (PrivateSourceSpace ι (u n)),
        ((finrank K (PrivateTargetSpace ι (u n)) : ℝ)/finrank K (PrivateSourceSpace ι (u n)))*finrank K L+
        g*(n : ℝ)^(s+1)*min (finrank K L : ℝ)
          ((finrank K (PrivateSourceSpace ι (u n)) : ℝ)-finrank K L) ≤
        (finrank K (outerImage (d := s+1) (attachedExponent ι) (u n) (attachedExponent_degree ι) L) : ℝ) := by
  let σ := limitingCoreFraction (s+1)
  have hσ := limitingCoreFraction_bounds (show 3 ≤ s+1 by omega)
  have hs0 : 0 < s := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let v := fun n (i : Labels k (a n) s) => u n (Sum.inl i)
  have hv n := MixedExterior.full_spark_comp (u n) (hu n)
    (Function.Embedding.inl : Labels k (a n) s ↪ _)
  have hmv n := (hm n).comp (Function.Embedding.inl : Labels k (a n) s ↪ _)
  obtain ⟨gc,hgc,hcore⟩ := uniform_core_outer_growth hk hs0 hh hσ.1 hσ.2 a z ha hz har hzr haz v hv hmv
  obtain ⟨c,hc,hbase⟩ := uniform_exponent_shadow hσ.1 hσ.2 hs0 a z ha hz har hzr haz (k : ℝ) hkR
  let A := fun n => (finrank K (CoreSourceSpace (z := z n) (v n)) : ℝ)
  let T := fun n => (finrank K (CoreTargetSpace (z := z n) (v n)) : ℝ)
  let A' := fun n => A n-b
  let T' := fun n => T n-(b : ℝ)*((n+s).choose (s+1) : ℝ)
  let R' := fun n => T' n/A' n
  let R₀ := fun n => (∑ j,finiteTargetProfile s (a n) (z n) j)/
    (∑ i,finiteSourceProfile (profileAmbientCapacity s) s (a n) (z n) i)
  let E := fun n : ℕ => (h : ℝ)*((h*2^h : ℕ) : ℝ)*((n+s-1).choose s : ℝ)
  let B := fun n : ℕ => (h : ℝ)*b*((n+s-1).choose s : ℝ)
  let D := fun n => (privateMultiplierLowerCount (a n) (z n) s b : ℝ)
  let α := (k : ℝ)*sourceProfileScale (profileAmbientCapacity s) σ s
  let τ := (k : ℝ)*targetProfileScale σ s
  let ρ := criticalRatio (s+1)/((s+1).factorial : ℝ)
  have hα : 0 < α := mul_pos hkR (sourceProfileScale_pos (profileAmbientCapacity_gt_one hs0) hσ.1 hσ.2 hs0)
  have hρ : 0 < ρ := div_pos (criticalRatio_bounds (by omega)).1 (by positivity)
  have hratio : targetProfileScale σ s/sourceProfileScale (profileAmbientCapacity s) σ s=ρ := by
    have h := limiting_profile_scale_ratio (show 3 ≤ s+1 by omega)
    simpa only [Nat.add_sub_cancel,← profileAmbientCapacity_eq_central] using h
  have hτα : τ/α=ρ := by
    dsimp only [τ,α]
    rw [mul_div_mul_left _ _ hkR.ne']
    exact hratio
  obtain ⟨hA,hT⟩ := actual_core_dimension_limits hk hs0 hh hσ.1 hσ.2 a z ha hz har hzr haz v hv
  obtain ⟨hA',hT',hR'⟩ := private_dimension_limits A T hs0 (b : ℝ) hα hA hT
  have hRlim : Tendsto (fun n : ℕ => R' n/(n : ℝ)^(s+1)) atTop (𝓝 ρ) := by
    change Tendsto (fun n : ℕ => R' n/(n : ℝ)^(s+1)) atTop (𝓝 (τ/α)) at hR'
    rwa [hτα] at hR'
  have hR₀ : Tendsto (fun n : ℕ => R₀ n/(n : ℝ)^(s+1)) atTop (𝓝 ρ) := by
    have hhR := target_source_ratio_limit (profileAmbientCapacity_gt_one hs0)
      hσ.1 hσ.2 hs0 a z ha hz har hzr
    change Tendsto (fun n : ℕ => R₀ n/(n : ℝ)^(s+1)) atTop
      (𝓝 (targetProfileScale σ s/sourceProfileScale (profileAmbientCapacity s) σ s)) at hhR
    rwa [hratio] at hhR
  have hE : Tendsto (fun n : ℕ => E n/(n : ℝ)^(s+1)) atTop (𝓝 0) :=
    exceptional_projection_error_lower_order ((h : ℝ)*(h*2^h : ℕ)) s
  have hB : Tendsto (fun n : ℕ => B n/(n : ℝ)^(s+1)) atTop (𝓝 0) :=
    exceptional_projection_error_lower_order ((h : ℝ)*b) s
  have hD := private_multiplier_count_limit hs b a z (Eventually.of_forall haz) har
  have hgap : ρ < privateColumnDensity (s+1)/((s+1).factorial : ℝ) :=
    div_lt_div_of_pos_right (criticalRatio_lt_privateColumnDensity (by omega)) (by positivity)
  obtain ⟨gl,hgl,hlower⟩ := private_lower_common_margin (s+1) R₀ (fun n => c*R₀ n) B D
    (fun n => R' n+E n) ρ (c*ρ) (privateColumnDensity (s+1)/((s+1).factorial : ℝ))
    (mul_pos hc hρ) hgap hR₀
    (by simpa only [mul_div_assoc] using hR₀.const_mul c) hB hD
    (by simpa only [add_div,add_zero] using hRlim.add hE)
  have hM : Tendsto (fun n : ℕ => ((n+s).choose (s+1) : ℝ)/(n : ℝ)^(s+1))
      atTop (𝓝 (1/((s+1).factorial : ℝ))) := by
    have he (n : ℕ) : n+(s+1)-1=n+s := by omega
    simpa only [he,one_div] using monomial_count_normalized_tendsto (s+1)
  have hupper := private_upper_loss_eventually hs0 A' (fun n => ((n+s).choose (s+1) : ℝ))
    (b : ℝ) α (1/((s+1).factorial : ℝ)) gc hα hgc hA' hM
  let g := min gl (gc/2)
  have hg : 0 < g := lt_min hgl (by positivity)
  have hgl' : g ≤ gl := min_le_left _ _
  have hgc' : g ≤ gc/2 := min_le_right _ _
  refine ⟨g,hg,?_⟩
  filter_upwards [hcore,hbase,hlower,hupper,normalized_limit_eventually_pos A' hα s hA',
    eventually_gt_atTop (0 : ℕ)] with n hncore hnbase hnlow hnup hnA hn0
  intro ι
  have hnpos : 0 < a n+z n := by rw [haz]; exact hn0
  have hdimA := private_source_dimension_add hk hs hh hnpos ι (u n) (hu n)
  have hdimT := private_target_dimension_add hk hs hh hnpos ι (u n) (hu n)
  have hdimAr : (finrank K (PrivateSourceSpace ι (u n)) : ℝ)=A' n := by
    have hd : (finrank K (PrivateSourceSpace ι (u n)) : ℝ)+b=A n := by
      dsimp only [A,v]
      exact_mod_cast hdimA
    dsimp only [A']
    linarith
  have hdimTr : (finrank K (PrivateTargetSpace ι (u n)) : ℝ)=T' n := by
    have hd : (finrank K (PrivateTargetSpace ι (u n)) : ℝ)+(b : ℝ)*
        ((a n+z n+(s+1)-1).choose (s+1) : ℝ)=T n := by
      dsimp only [T,v]
      exact_mod_cast hdimT
    have hN : a n+z n+(s+1)-1=n+s := by rw [haz]; omega
    rw [hN] at hd
    dsimp only [T']
    linarith
  have hpos : 0 < finrank K (PrivateSourceSpace ι (u n)) := by
    have hposR : (0 : ℝ) < finrank K (PrivateSourceSpace ι (u n)) := by rwa [hdimAr]
    exact_mod_cast hposR
  refine ⟨hpos,?_⟩
  apply private_uniform_growth_at hk hs hh hnpos ι (u n) (hu n) (hm n) hpos
    (R₀ n) (c*R₀ n) (gc*(n : ℝ)^(s+1)) (g*(n : ℝ)^(s+1)) hnbase hncore
  · rw [hdimAr,haz,show n+(s+1)-1=n+s by omega]
    have hp := mul_le_mul_of_nonneg_right hgc' (by positivity : 0 ≤ (n : ℝ)^(s+1))
    dsimp only [A'] at hnup ⊢
    linarith
  · rw [hdimAr,hdimTr]
    conv_lhs => rw [haz]
    conv_rhs => rw [haz]
    have hp := mul_le_mul_of_nonneg_right hgl' (by positivity : 0 ≤ (n : ℝ)^(s+1))
    have he : (h*((h*2^h)*(n+s-1).choose s) : ℝ)=E n := by dsimp [E]; push_cast; ring
    have hb : (h*(b*(n+s-1).choose s) : ℝ)=B n := by dsimp [B]; push_cast; ring
    push_cast
    dsimp only [E,B,R'] at hnlow
    push_cast at hnlow
    linarith [hnlow.1]
  · rw [hdimAr,hdimTr]
    conv_lhs => rw [haz]
    have hp := mul_le_mul_of_nonneg_right hgl' (by positivity : 0 ≤ (n : ℝ)^(s+1))
    have hd : D n ≤ ((privateGoodMultipliers (a n) s ι).card : ℝ) := by
      dsimp only [D]
      exact_mod_cast privateGoodMultipliers_lowerCount (a := a n) hs0 ι
    push_cast
    dsimp only [E,R'] at hnlow
    push_cast at hnlow
    linarith [hnlow.2]

end Froberg.PrivateColumns
