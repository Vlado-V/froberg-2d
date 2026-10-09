module

public import Froberg.IndexedPureTail

@[expose] public section

/-! The odd pure projection, with its variable threshold chosen before the field. -/
noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Filter Module Quartic

theorem eventually_odd_tail_projection_uniform {e : ℕ} (he : 2≤e) (ho : Odd (1+e)) :
    ∀ᶠ h : ℕ in atTop, ∀ (K : Type) [Field K] [Infinite K],
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
  intro K _ _
  obtain ⟨P,hP,hker,hgrowth,hfill⟩ := exists_projected_linear_growth_with_cutoff
    (K := K) hh (show 0<e by omega) hW hmargin hlarge
    (by simpa only [show 1+e+1=e+2 by omega] using hcut)
  exact ⟨P,hP,hker,hgrowth,hfill,htop.2.2⟩

theorem eventually_indexed_odd_tail_projection_uniform {d : ℕ} (hd : 3 ≤ d) (ho : Odd d) :
    ∀ᶠ h : ℕ in atTop, ∀ (K : Type) [Field K] [Infinite K],
      ∃ (U : Fin (tailGeneratorCount d h) → Forms K h d)
        (R : Forms K h (1+(d-1)) →ₗ[K] (Fin (topComplementCount d h) → K)),
        LinearIndependent K U ∧ Function.Surjective R ∧
        R.ker=(Submodule.span K (Set.range U)).map (topGrowthDegree (by omega : 1 ≤ d) h).symm.toLinearMap ∧
        (∀ L : Submodule K (Forms K h (d-1)),
          topComplementCount d h*finrank K L ≤ finrank K (Forms K h (d-1))*
            finrank K ((BilinearImage.image (gradedMultiplication (d := 1) (e := d-1)) L).map R)) ∧
        BilinearImage.image (gradedMultiplication (K := K) (n := h) (d := d) (e := 1)).flip
          (Submodule.span K (Set.range U))=⊤ ∧
        (h : ℝ)/(2*(d : ℝ)) ≤ (topComplementCount d h : ℝ)/(topSourceCount d h : ℝ) := by
  have heq : 1+(d-1)=d := by omega
  have he : ∀ᶠ h : ℕ in atTop, ∀ (K : Type) [Field K] [Infinite K],
      ∃ R : Forms K h (1+(d-1)) →ₗ[K] (Fin (topComplementCount d h) → K),
        Function.Surjective R ∧ finrank K R.ker=tailGeneratorCount d h ∧
        (∀ L : Submodule K (Forms K h (d-1)),
          topComplementCount d h*finrank K L ≤ finrank K (Forms K h (d-1))*
            finrank K ((BilinearImage.image (gradedMultiplication (d := 1) (e := d-1)) L).map R)) ∧
        BilinearImage.image (gradedMultiplication (K := K) (n := h)
          (d := 1+(d-1)) (e := 1)).flip R.ker=⊤ ∧
        (h : ℝ)/(2*(d : ℝ)) ≤ (topComplementCount d h : ℝ)/(topSourceCount d h : ℝ) := by
    have hx := eventually_odd_tail_projection_uniform (show 2 ≤ d-1 by omega)
      (show Odd (1+(d-1)) by rwa [heq])
    rw [show topComplementCount (1+(d-1))=topComplementCount d from congrArg topComplementCount heq] at hx
    simpa only [heq] using hx
  filter_upwards [he] with h hh
  intro K _ _
  obtain ⟨R,hR,hker,hgrowth,hcut,hratio⟩ := hh K
  obtain ⟨v,hv,hvs⟩ := exists_indexed_submodule_basis R.ker hker
  let t := topGrowthDegree (K := K) (by omega : 1 ≤ d) h
  let U : Fin (tailGeneratorCount d h) → Forms K h d := fun i => t (v i)
  have hU : LinearIndependent K U := hv.map' t.toLinearMap t.ker
  have hspan : Submodule.span K (Set.range U)=R.ker.map t.toLinearMap := by
    rw [←hvs,Submodule.map_span,←Set.range_comp]
    rfl
  refine ⟨U,R,hU,hR,?_,hgrowth,?_,hratio⟩
  · rw [hspan,←Submodule.map_comp]
    simp only [t,LinearEquiv.comp_coe,LinearEquiv.self_trans_symm,LinearEquiv.refl_toLinearMap,
      Submodule.map_id]
  · rw [hspan]
    exact formDegreeEquiv_cutoff heq R.ker hcut


theorem eventually_odd_pure_projection_data_uniform {d : ℕ} (hd : 3 ≤ d) (ho : Odd d) :
    ∀ᶠ h : ℕ in atTop, ∀ (K : Type) [Field K] [Infinite K], Nonempty (OddPureProjectionData K d h (by omega)) := by
  filter_upwards [eventually_indexed_odd_tail_projection_uniform hd ho,
    eventually_gt_atTop (0 : ℕ)] with h hh hhpos
  intro K _ _
  obtain ⟨U,R,hU,hR,hker,hgrowth,hcut,hratio⟩ := hh K
  have hb : 0 < topComplementCount d h := by
    by_contra! hb
    have hz : topComplementCount d h=0 := Nat.eq_zero_of_le_zero hb
    rw [hz,Nat.cast_zero,zero_div] at hratio
    have hp : (0 : ℝ)<(h : ℝ)/(2*(d : ℝ)) := by
      apply div_pos
      · exact_mod_cast hhpos
      · have hd' : (0 : ℝ)<d := by exact_mod_cast (show 0<d by omega)
        positivity
    linarith
  refine ⟨⟨U,R,hU,hR,hb,hker,hgrowth,hcut,?_⟩⟩
  simpa only [show 1+(d-1)=d by omega,topSourceCount] using hratio

end Froberg
