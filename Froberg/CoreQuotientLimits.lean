module

public import Froberg.UniformOuterGrowth
public import Froberg.ProfileCriticalRatio
public import Froberg.CoreLimit

@[expose] public section

/-! Dimensions and slope limits for the actual core quotient spaces. -/
noncomputable section
namespace Froberg
open Module Filter OuterInjection
open scoped Topology

lemma actual_core_dimension_limits {K : Type*} [Field K]
    {k s h : ℕ} (hk : 0<k) (hs : 0<s) (hh : h=k*(2*s+1).choose s)
    {σ : ℝ} (hσ : 0<σ) (hσ1 : σ<1)
    (a z : ℕ → ℕ) (ha : Tendsto a atTop atTop) (hz : Tendsto z atTop atTop)
    (har : Tendsto (fun n : ℕ => (a n : ℝ)/n) atTop (𝓝 σ))
    (hzr : Tendsto (fun n : ℕ => (z n : ℝ)/n) atTop (𝓝 (1-σ)))
    (haz : ∀ n,a n+z n=n)
    (v : (n : ℕ) → Labels k (a n) s → Fin h → K)
    (hv : ∀ n (U : Finset (Labels k (a n) s)),U.card≤h → LinearIndependent K (fun i : U => v n i.val)) :
    Tendsto (fun n : ℕ => (finrank K (CoreSourceSpace (z := z n) (v n)) : ℝ)/(n : ℝ)^s)
      atTop (𝓝 ((k : ℝ)*sourceProfileScale (profileAmbientCapacity s) σ s)) ∧
    Tendsto (fun n : ℕ => (finrank K (CoreTargetSpace (z := z n) (v n)) : ℝ)/(n : ℝ)^(2*s+1))
      atTop (𝓝 ((k : ℝ)*targetProfileScale σ s)) := by
  have hH := profileAmbientCapacity_gt_one hs
  have hsource := (sourceProfile_total_limit hH hσ hσ1 hs a z ha hz har hzr).const_mul (k : ℝ)
  have hsource' : Tendsto (fun n : ℕ => (finrank K (CoreSourceSpace (z := z n) (v n)) : ℝ)/(n : ℝ)^s)
      atTop (𝓝 ((k : ℝ)*sourceProfileScale (profileAmbientCapacity s) σ s)) := by
    apply hsource.congr'
    exact Eventually.of_forall fun n => by
      dsimp only
      rw [outer_source_dimension_profile hh (v n) (hv n)]
      ring
  let T₀ := fun n => (k : ℝ)*∑ j,finiteTargetProfile s (a n) (z n) j
  let T := fun n => (finrank K (CoreTargetSpace (z := z n) (v n)) : ℝ)
  let D := fun n : ℕ => (h : ℝ)*n*((n+(2*s-1)-1).choose (2*s-1) : ℝ)
  have hT₀ : Tendsto (fun n : ℕ => T₀ n/(n : ℝ)^(2*s+1)) atTop
      (𝓝 ((k : ℝ)*targetProfileScale σ s)) := by
    apply ((targetProfile_total_limit hσ hσ1 hs a z ha hz har hzr).const_mul (k : ℝ)).congr'
    exact Eventually.of_forall fun n => by dsimp only [T₀]; ring
  have hD := target_discrepancy_error_lower_order (h : ℝ) hs
  have hb (n : ℕ) : 0≤T n-T₀ n ∧ T n-T₀ n≤D n := by
    have hh' := outer_target_dimension_budget (z := z n) hh (v n) (hv n)
    refine ⟨sub_nonneg.mpr hh'.1,?_⟩
    have he : (a n : ℝ)+(z n : ℝ)=(n : ℝ) := by exact_mod_cast haz n
    simpa only [D,show 2*s+1-2=2*s-1 by omega,haz n,he] using hh'.2
  have hdiff : Tendsto (fun n : ℕ => (T n-T₀ n)/(n : ℝ)^(2*s+1)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => div_nonneg (hb n).1 (by positivity))
      (Eventually.of_forall fun n => div_le_div_of_nonneg_right (hb n).2 (by positivity)) hD
  refine ⟨hsource',?_⟩
  have hl := hT₀.add hdiff
  simp only [add_zero] at hl
  apply hl.congr'
  exact Eventually.of_forall fun n => by dsimp only [T]; ring

end Froberg
