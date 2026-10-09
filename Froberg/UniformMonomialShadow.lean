module

public import Froberg.MonomialShadowGrowth

@[expose] public section

/-! A positive strict-shadow constant works for every source subspace
profile and every sufficiently large number of variables. -/
noncomputable section
namespace Froberg
open Finset Filter MonomialExpansion
open scoped Topology

theorem uniform_monomial_shadow {σ : ℝ} {s : ℕ}
    (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s)
    (a z : ℕ → ℕ) (ha : Tendsto a atTop atTop) (hz : Tendsto z atTop atTop)
    (har : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 σ))
    (hzr : Tendsto (fun n : ℕ => (z n : ℝ) / n) atTop (𝓝 (1-σ)))
    (haz : ∀ n, a n + z n = n) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
      ∀ (ell : (Σ i, SourceMonomialFiber (a n) (z n) s i) → ℝ)
        (b : (Σ j, TargetMonomialFiber (a n) (z n) s j) → ℝ),
      (∀ α, 0 ≤ ell α ∧ ell α ≤ profileSourceCapacity (profileAmbientCapacity s) α.1) →
      (∀ α β, OuterInjection.joinParts α.2.1.val α.2.2.val ≤
        OuterInjection.joinParts β.2.1.val β.2.2.val →
        min (profileTargetCapacity s β.1) (ell α) ≤ b β) →
      let A := ∑ i, finiteSourceProfile (profileAmbientCapacity s) s (a n) (z n) i
      let T := ∑ j, finiteTargetProfile s (a n) (z n) j
      (T/A) * (∑ α, ell α) + c * (T/A) *
        min (∑ α, ell α) (A-∑ α, ell α) ≤ ∑ β, b β := by
  have hH := profileAmbientCapacity_gt_one hs
  obtain ⟨ε,hε,hP⟩ := finite_profile_positive_transport hH hσ hσ1 hs a z ha hz har hzr
  obtain ⟨κ,hκ,hκevent⟩ := monomialMixingCoefficient_eventually_pos hH hσ hσ1 hs
    a z ha hz har hzr haz hε
  refine ⟨min (ε/profileAmbientCapacity s) (κ/2) / 4, ?_, ?_⟩
  · have hH0 := profileAmbientCapacity_pos s
    positivity
  · filter_upwards [hP,hκevent,ha.eventually (eventually_gt_atTop 0),
      hz.eventually (eventually_gt_atTop 0)] with n hn hκn han hzn
    obtain ⟨P,hrow,hcol,hP0,hPlower,hPzero⟩ := hn
    intro ell b hell hb
    exact monomial_shadow_growth han hzn hs P hP0 hPzero hrow hcol ε κ hε.le hκ.le
      (fun i j hij => (hPlower i j hij).le) hκn ell b hell hb

end Froberg
