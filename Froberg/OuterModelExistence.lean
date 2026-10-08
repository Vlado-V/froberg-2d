import Froberg.UniformOuterGrowth
import Froberg.OuterGeneric

/-! Existence of actual core-attached presentations with uniform strict
shadow, injective presentation maps, and enough surplus for incidence. -/
noncomputable section
namespace Froberg
open Module Finset Filter OuterInjection
open scoped Topology

lemma core_source_dimension_le {K : Type*} [Field K] {k a z s h : ℕ}
    (hn : 0 < a+z) (v : Labels k a s → Fin h → K) :
    finrank K (CoreSourceSpace (z := z) v) ≤ h*(a+z+s-1).choose s := by
  have hh := (AttachedMultiplication.relationSpace (d := 0)
    (coreExponent z) v (coreExponent_degree z)).finrank_quotient_le
  simpa [CoreSourceSpace,Module.finrank_pi_fintype,finrank_forms K (a+z) s hn] using hh

theorem eventually_exists_strict_core_model {K : Type*} [Field K] [Infinite K]
    {k s h : ℕ} (hk : 0 < k) (hs : 0 < s) (hh : h=k*(2*s+1).choose s)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    (a z : ℕ → ℕ) (ha : Tendsto a atTop atTop) (hz : Tendsto z atTop atTop)
    (har : Tendsto (fun n : ℕ => (a n : ℝ)/n) atTop (𝓝 σ))
    (hzr : Tendsto (fun n : ℕ => (z n : ℝ)/n) atTop (𝓝 (1-σ)))
    (haz : ∀ n, a n+z n=n) :
    ∃ g : ℝ, 0 < g ∧ ∀ᶠ n in atTop,
      ∃ v : Labels k (a n) s → Fin h → K,
        (∀ U : Finset (Labels k (a n) s), U.card ≤ h → LinearIndependent K (fun i : U => v i.val)) ∧
        MixedExterior.UniversalMixedPosition v ∧
        (∀ c ≤ s+1, Function.Injective (AttachedMultiplication.multiplication (d := c) (coreExponent (z n)) v)) ∧
        (0 < finrank K (CoreSourceSpace (z := z n) v)) ∧
        ((finrank K (CoreSourceSpace (z := z n) v) : ℝ) ≤ g*(n : ℝ)^(s+1)) ∧
        (∀ L : Submodule K (CoreSourceSpace (z := z n) v),
          ((finrank K (CoreTargetSpace (z := z n) v) : ℝ)/finrank K (CoreSourceSpace (z := z n) v))*finrank K L +
          g*(n : ℝ)^(s+1)*(min (finrank K L)
            (finrank K (CoreSourceSpace (z := z n) v)-finrank K L) : ℕ) ≤
          (finrank K (AttachedMultiplication.outerImage (d := s+1)
            (coreExponent (z n)) v (coreExponent_degree (z n)) L) : ℝ)) := by
  classical
  have hex (n : ℕ) := MixedExterior.exists_universal_mixed_vectors
    (K := K) (α := Labels k (a n) s) h
  choose v hv hm using hex
  obtain ⟨g,hg,hgrowth⟩ := uniform_core_outer_growth hk hs hh hσ hσ1 a z ha hz har hzr haz v hv hm
  have hdom := eventually_lt_of_normalized_limits
    (fun n : ℕ => (h : ℝ)*((n+s-1).choose s : ℝ))
    (fun n : ℕ => g*(n : ℝ)^(s+1)) (s+1) 0 g
    (exceptional_projection_error_lower_order (h : ℝ) s)
    (scaled_power_normalized_limit g (s+1)) hg
  refine ⟨g,hg,?_⟩
  filter_upwards [hgrowth,hdom,ha.eventually (eventually_gt_atTop 0),
    hz.eventually (eventually_gt_atTop 0)] with n hn hdn han hzn
  have hnpos : 0 < a n+z n := by omega
  have hdimpos : (0 : ℝ) < finrank K (CoreSourceSpace (z := z n) (v n)) := by
    rw [outer_source_dimension_profile hh (v n) (hv n)]
    exact mul_pos (by exact_mod_cast hk)
      (finiteSourceProfile_total_pos (profileAmbientCapacity_gt_one hs) han hzn)
  refine ⟨v n,hv n,hm n,?_,by exact_mod_cast hdimpos,?_,?_⟩
  · apply injective_attached_of_full_spark (v n) (hv n)
    rw [show s+(s+1)=2*s+1 by omega,← hh]
  · have hd := core_source_dimension_le hnpos (v n)
    conv_rhs at hd => rw [haz]
    have hdR : (finrank K (CoreSourceSpace (z := z n) (v n)) : ℝ) ≤
        (h : ℝ)*((n+s-1).choose s : ℝ) := by exact_mod_cast hd
    exact hdR.trans hdn.le
  · intro L
    simpa only [Nat.cast_min,Nat.cast_sub (Submodule.finrank_le L)] using hn L

end Froberg
