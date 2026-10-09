module

public import Froberg.GradedCutoffProjection
public import Froberg.TailCutoffCounts

@[expose] public section

/-! The actual rounded odd pure family admits the simultaneous C.3 projection. -/
noncomputable section
namespace Froberg
open Filter Module Quartic
variable {K : Type*} [Field K] [Infinite K]

theorem eventually_odd_tail_projection {e : ℕ} (he : 2≤e) (ho : Odd (1+e)) :
    ∀ᶠ h : ℕ in atTop,
      ∃ P : Forms K h (1+e) →ₗ[K] (Fin (topComplementCount (1+e) h) → K),
        Function.Surjective P ∧ finrank K P.ker=tailGeneratorCount (1+e) h ∧
        (∀ L : Submodule K (Forms K h e),
          topComplementCount (1+e) h*finrank K L≤finrank K (Forms K h e)*
            finrank K ((BilinearImage.image (gradedMultiplication (d := 1) (e := e)) L).map P)) ∧
        BilinearImage.image (gradedMultiplication (K := K) (n := h) (d := 1+e) (e := 1)).flip P.ker=⊤ ∧
        (h : ℝ)/(2*((1+e : ℕ) : ℝ))≤
          (topComplementCount (1+e) h : ℝ)/(topSourceCount (1+e) h : ℝ) := by
  filter_upwards [odd_top_projection_hypotheses (show 3≤1+e by omega) ho,
    eventually_tail_cutoff_count (show 0<1+e by omega),
    eventually_gt_atTop (0 : ℕ),eventually_ge_atTop ((e+2)*(e+2)*(e+1))]
    with h htop hcut hh hlarge
  have hW : (h+(1+e)-1).choose (1+e)=
      tailGeneratorCount (1+e) h+topComplementCount (1+e) h := by
    dsimp only [topComplementCount]
    omega
  have hmargin : (h+e-1).choose e*(h+e-1).choose e<
      tailGeneratorCount (1+e) h*topComplementCount (1+e) h := by
    have hm := htop.2.1
    simp only [topSourceCount,show 1+e-1=e by omega,pow_two] at hm
    exact_mod_cast hm
  obtain ⟨P,hP,hker,hgrowth,hfill⟩ := exists_projected_linear_growth_with_cutoff
    (K := K) hh (show 0<e by omega) hW hmargin hlarge
    (by simpa only [show 1+e+1=e+2 by omega] using hcut)
  exact ⟨P,hP,hker,hgrowth,hfill,htop.2.2⟩

end Froberg
