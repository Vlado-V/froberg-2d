module

public import Froberg.OddTailProjection
public import Froberg.TopSourceProjection
public import Froberg.EvenTail

@[expose] public section

/-! Indexed pure families and the simultaneous projected top-growth data.
The family is chosen from the actual kernel of the projection. -/
noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Filter Module Quartic
variable {K : Type} [Field K] [Infinite K]

theorem exists_indexed_submodule_basis {V : Type*} [AddCommGroup V] [Module K V]
    [Module.Finite K V] (W : Submodule K V) {u : ℕ} (hu : finrank K W=u) :
    ∃ v : Fin u → V,LinearIndependent K v ∧ Submodule.span K (Set.range v)=W := by
  let b := Module.finBasisOfFinrankEq K W hu
  refine ⟨fun i => (b i).val, b.linearIndependent.map' W.subtype (Submodule.ker_subtype W), ?_⟩
  have hs := congrArg (Submodule.map W.subtype) b.span_eq
  simpa only [Submodule.map_span,←Set.range_comp,Submodule.map_top,Submodule.range_subtype,
    Function.comp_def,Submodule.subtype_apply]
    using hs

theorem formDegreeEquiv_cutoff {h a b : ℕ} (hab : a=b)
    (W : Submodule K (Forms K h a))
    (hW : BilinearImage.image (gradedMultiplication (K := K) (n := h)
      (d := a) (e := 1)).flip W=⊤) :
    BilinearImage.image (gradedMultiplication (K := K) (n := h)
      (d := b) (e := 1)).flip (W.map (formDegreeEquiv hab).toLinearMap)=⊤ := by
  subst b
  have ht : (formDegreeEquiv (K := K) (n := h) (rfl : a=a)).toLinearMap=LinearMap.id := rfl
  simpa only [ht,Submodule.map_id] using hW

theorem eventually_indexed_odd_tail_projection {d : ℕ} (hd : 3 ≤ d) (ho : Odd d) :
    ∀ᶠ h : ℕ in atTop,
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
  have he : ∀ᶠ h : ℕ in atTop,
      ∃ R : Forms K h (1+(d-1)) →ₗ[K] (Fin (topComplementCount d h) → K),
        Function.Surjective R ∧ finrank K R.ker=tailGeneratorCount d h ∧
        (∀ L : Submodule K (Forms K h (d-1)),
          topComplementCount d h*finrank K L ≤ finrank K (Forms K h (d-1))*
            finrank K ((BilinearImage.image (gradedMultiplication (d := 1) (e := d-1)) L).map R)) ∧
        BilinearImage.image (gradedMultiplication (K := K) (n := h)
          (d := 1+(d-1)) (e := 1)).flip R.ker=⊤ ∧
        (h : ℝ)/(2*(d : ℝ)) ≤ (topComplementCount d h : ℝ)/(topSourceCount d h : ℝ) := by
    have hx := eventually_odd_tail_projection (K := K) (show 2 ≤ d-1 by omega)
      (show Odd (1+(d-1)) by rwa [heq])
    rw [show topComplementCount (1+(d-1))=topComplementCount d from congrArg topComplementCount heq] at hx
    simpa only [heq] using hx
  filter_upwards [he] with h hh
  obtain ⟨R,hR,hker,hgrowth,hcut,hratio⟩ := hh
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

/-- All pure-family inputs to the actual odd endpoint construction. -/
structure OddPureProjectionData (K : Type) [Field K] (d h : ℕ) (hd : 1 ≤ d) where
  U : Fin (tailGeneratorCount d h) → Forms K h d
  R : Forms K h (1+(d-1)) →ₗ[K] (Fin (topComplementCount d h) → K)
  independent : LinearIndependent K U
  surjective : Function.Surjective R
  target_positive : 0 < topComplementCount d h
  kernel : R.ker=(Submodule.span K (Set.range U)).map (topGrowthDegree hd h).symm.toLinearMap
  growth : ∀ L : Submodule K (Forms K h (d-1)),
    topComplementCount d h*finrank K L ≤ finrank K (Forms K h (d-1))*
      finrank K ((BilinearImage.image (gradedMultiplication (d := 1) (e := d-1)) L).map R)
  cutoff : BilinearImage.image (gradedMultiplication (K := K) (n := h) (d := d) (e := 1)).flip
    (Submodule.span K (Set.range U))=⊤
  ratio : (h : ℝ)/(2*((1+(d-1) : ℕ) : ℝ)) ≤
    (topComplementCount d h : ℝ)/((h+(d-1)-1).choose (d-1) : ℝ)

theorem eventually_odd_pure_projection_data {d : ℕ} (hd : 3 ≤ d) (ho : Odd d) :
    ∀ᶠ h : ℕ in atTop,Nonempty (OddPureProjectionData K d h (by omega)) := by
  filter_upwards [eventually_indexed_odd_tail_projection (K := K) hd ho,
    eventually_gt_atTop (0 : ℕ)] with h hh hhpos
  obtain ⟨U,R,hU,hR,hker,hgrowth,hcut,hratio⟩ := hh
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
