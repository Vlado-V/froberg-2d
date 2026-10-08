import Froberg.OuterShadowTransfer
import Froberg.OuterNearFull
import Froberg.ShadowDependentAbsorption

/-! Uniform strict growth of the actual core-attached outer module. -/
noncomputable section
namespace Froberg
open Module Finset Filter MonomialExpansion OuterInjection
open scoped Topology

abbrev CoreSourceSpace {K : Type*} [Field K] {k a z s h : ℕ}
    (v : Labels k a s → Fin h → K) :=
  (Fin h → Forms K (a+z) s) ⧸
    AttachedMultiplication.relationSpace (d := 0) (coreExponent z) v (coreExponent_degree z)

abbrev CoreTargetSpace {K : Type*} [Field K] {k a z s h : ℕ}
    (v : Labels k a s → Fin h → K) :=
  (Fin h → Forms K (a+z) (s+(s+1))) ⧸
    AttachedMultiplication.relationSpace (d := s+1) (coreExponent z) v (coreExponent_degree z)

theorem uniform_core_outer_growth {K : Type*} [Field K]
    {k s h : ℕ} (hk : 0 < k) (hs : 0 < s) (hh : h=k*(2*s+1).choose s)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    (a z : ℕ → ℕ) (ha : Tendsto a atTop atTop) (hz : Tendsto z atTop atTop)
    (har : Tendsto (fun n : ℕ => (a n : ℝ)/n) atTop (𝓝 σ))
    (hzr : Tendsto (fun n : ℕ => (z n : ℝ)/n) atTop (𝓝 (1-σ)))
    (haz : ∀ n, a n+z n=n)
    (v : (n : ℕ) → Labels k (a n) s → Fin h → K)
    (hv : ∀ n (U : Finset (Labels k (a n) s)), U.card ≤ h → LinearIndependent K (fun i : U => v n i.val))
    (hm : ∀ n, MixedExterior.UniversalMixedPosition (v n)) :
    ∃ g : ℝ, 0 < g ∧ ∀ᶠ n in atTop, ∀ L : Submodule K (CoreSourceSpace (z := z n) (v n)),
      ((finrank K (CoreTargetSpace (z := z n) (v n)) : ℝ)/finrank K (CoreSourceSpace (z := z n) (v n)))*finrank K L +
      g*(n : ℝ)^(s+1)*min (finrank K L : ℝ)
        ((finrank K (CoreSourceSpace (z := z n) (v n)) : ℝ)-finrank K L) ≤
      (finrank K (AttachedMultiplication.outerImage (d := s+1)
        (coreExponent (z n)) (v n) (coreExponent_degree (z n)) L) : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hH := profileAmbientCapacity_gt_one hs
  obtain ⟨c,hc,hexp⟩ := uniform_exponent_shadow hσ hσ1 hs a z ha hz har hzr haz (k : ℝ) hkR
  let A := fun n => (finrank K (CoreSourceSpace (z := z n) (v n)) : ℝ)
  let T := fun n => (finrank K (CoreTargetSpace (z := z n) (v n)) : ℝ)
  let T₀ := fun n => (k : ℝ)*∑ j, finiteTargetProfile s (a n) (z n) j
  let D := fun n : ℕ => (h : ℝ)*n*((n+(2*s-1)-1).choose (2*s-1) : ℝ)
  let E := fun n : ℕ => (h : ℝ)*(h*2^h)*((n+s-1).choose s : ℝ)
  let size := fun n (L : Submodule K (CoreSourceSpace (z := z n) (v n))) => (finrank K L : ℝ)
  let imageSize := fun n (L : Submodule K (CoreSourceSpace (z := z n) (v n))) =>
    (finrank K (AttachedMultiplication.outerImage (d := s+1)
      (coreExponent (z n)) (v n) (coreExponent_degree (z n)) L) : ℝ)
  have hAeq (n : ℕ) : A n = (k : ℝ)*∑ i, finiteSourceProfile (profileAmbientCapacity s) s (a n) (z n) i :=
    outer_source_dimension_profile hh (v n) (hv n)
  have hAlim : Tendsto (fun n => A n/(n : ℝ)^s) atTop
      (𝓝 ((k : ℝ)*sourceProfileScale (profileAmbientCapacity s) σ s)) := by
    have hl := (sourceProfile_total_limit hH hσ hσ1 hs a z ha hz har hzr).const_mul (k : ℝ)
    apply hl.congr'
    exact Eventually.of_forall fun n => by dsimp only; rw [hAeq]; ring
  have hTlim : Tendsto (fun n => T₀ n/(n : ℝ)^(2*s+1)) atTop
      (𝓝 ((k : ℝ)*targetProfileScale σ s)) := by
    have hl := (targetProfile_total_limit hσ hσ1 hs a z ha hz har hzr).const_mul (k : ℝ)
    apply hl.congr'
    exact Eventually.of_forall fun n => by dsimp [T₀]; ring
  have hDlim := target_discrepancy_error_lower_order (h : ℝ) hs
  have hElim := exceptional_projection_error_lower_order ((h : ℝ)*(h*2^h)) s
  have hbudget : ∀ᶠ n in atTop, T₀ n ≤ T n ∧ T n-T₀ n ≤ D n ∧ 0 ≤ D n := by
    apply Eventually.of_forall
    intro n
    have hb := outer_target_dimension_budget (z := z n) hh (v n) (hv n)
    dsimp only at hb
    have hd : 2*s+1-2=2*s-1 := by omega
    refine ⟨hb.1, ?_, ?_⟩
    · have hazR : (a n : ℝ)+(z n : ℝ)=(n : ℝ) := by exact_mod_cast haz n
      simpa only [D,haz n,hd,hazR] using hb.2
    · dsimp [D]
      positivity
  have hratio (n : ℕ) : T₀ n/A n =
      (∑ j, finiteTargetProfile s (a n) (z n) j)/
      (∑ i, finiteSourceProfile (profileAmbientCapacity s) s (a n) (z n) i) := by
    rw [hAeq]
    dsimp [T₀]
    exact mul_div_mul_left _ _ hkR.ne'
  have hshadow : ∀ᶠ n in atTop, ∀ L : Submodule K (CoreSourceSpace (z := z n) (v n)),
      0 ≤ size n L → size n L ≤ A n →
      T₀ n/A n*size n L+(c*(T₀ n/A n)-E n)*min (size n L) (A n-size n L) ≤ imageSize n L := by
    filter_upwards [hexp,eventually_gt_atTop (0 : ℕ)] with n hn hn0
    intro L _ _
    have hpos : 0 < a n+z n := by rw [haz]; exact hn0
    have hg := actual_outer_growth_of_exponent_shadow hh hpos (v n) (hv n) (hm n)
      (T₀ n/A n) (c*(T₀ n/A n)) (by rw [hratio]; exact hn) L
    simpa only [A,size,imageSize,E,haz n,mul_assoc] using hg
  have hquadratic : ∀ᶠ n in atTop, ∀ L : Submodule K (CoreSourceSpace (z := z n) (v n)),
      0 ≤ size n L → size n L ≤ A n →
      T n-((h : ℝ)*n)*(A n-size n L)^2 ≤ imageSize n L := by
    apply Eventually.of_forall
    intro n L _ _
    have hg := AttachedMultiplication.outer_image_codimension_le
      (coreExponent (z n)) (v n) (coreExponent_degree (z n)) L
    have hsource := Submodule.finrank_le L
    have htarget := Submodule.finrank_le (AttachedMultiplication.outerImage (d := s+1)
      (coreExponent (z n)) (v n) (coreExponent_degree (z n)) L)
    have hgr : T n-imageSize n L ≤ (h : ℝ)*((A n-size n L)^2*(a n+z n)) := by
      have hcast := (Nat.cast_le (α := ℝ)).mpr hg
      simp only [Nat.cast_sub htarget,Nat.cast_mul,Nat.cast_pow,Nat.cast_sub hsource,
        Nat.cast_add] at hcast
      exact hcast
    have hazR : (a n : ℝ)+(z n : ℝ)=(n : ℝ) := by exact_mod_cast haz n
    rw [hazR] at hgr
    nlinarith
  obtain ⟨g,hg,hev⟩ := uniform_shadow_surplus_dependent size A T₀ T D E imageSize s
    (mul_pos hkR (sourceProfileScale_pos hH hσ hσ1 hs))
    (mul_pos hkR (targetProfileScale_pos hσ hσ1 hs)) hc (Nat.cast_nonneg h)
    hAlim hTlim hDlim hElim hbudget hshadow hquadratic
  refine ⟨g,hg,hev.mono ?_⟩
  intro n hn L
  exact hn L (Nat.cast_nonneg _) (by dsimp only [size,A]; exact_mod_cast Submodule.finrank_le L)

end Froberg
