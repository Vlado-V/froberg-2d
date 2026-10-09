module

public import Froberg.PreparedRestrictedGrowthFiber
public import Froberg.PreparedScalarThinOpen
public import Froberg.BottomThinFlag

@[expose] public section

/-! Actual-count C.4 selection on the final prepared family, while every
temporary added column and every supplied enlarged-family open is retained. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency true
namespace Froberg.PreparedParameters
open Froberg PreparedTarget Filter Module MvPolynomial VectorExpansionOpen Quartic
open scoped Topology
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K]
attribute [local irreducible] PreparedEndpointThin BaseC4GrowthProperty

theorem exact_counts_prepared_c4_selection {d k h lo u b : ℕ}
    (hd : 3 ≤ d) (hdodd : d%2=1) (hk : 0 < k)
    (hh : h=k*centralHalfBinomial d) (hhpos : 0 < h) (hb : 0 < b)
    (U : Fin u → Forms K h d) (hU : LinearIndependent K U)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K)) (hR : Function.Surjective R)
    (hker : R.ker=(Submodule.span K (Set.range U)).map
      (topGrowthDegree (by omega : 1 ≤ d) h).symm.toLinearMap)
    (hP : ∀ L : Submodule K (Forms K h (d-1)),b*finrank K L ≤
      finrank K (Forms K h (d-1))*
        finrank K ((BilinearImage.image (gradedMultiplication (d := 1) (e := d-1)) L).map R))
    (hratio : (h : ℝ)/(2*((1+(d-1) : ℕ) : ℝ)) ≤
      (b : ℝ)/((h+(d-1)-1).choose (d-1) : ℝ))
    (upper : Bool) (a f e : ℕ → ℕ) (ha : ∀ n,a n≤n)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0 < δ)
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n))
    (extra : ℕ) :
    ∃ G C ξ : ℝ,0<G ∧ 0<C ∧ 0<ξ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Finset ℕ) (counts counts' : ℕ → ℕ) (O : ℕ → Submodule K (Poly K h))
        (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
        (heven : ∀ j∈J,j%2=0) (hcounts : ∀ j∈J,counts j≤counts' j),
      Fintype.card (ProductRows.LayerLabel J counts) ≤
        Fintype.card (ProductRows.LayerLabel (allEvenIndices d) (allEvenCount d h n (e n+extra))) →
      letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O) :=
        FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
      letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts' O) :=
        FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
      ∀ (Good : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O → Prop)
        (A : MvPolynomial (Fin (finrank K
          (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O))) K)
        (D : MvPolynomial (Fin (finrank K
          (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts' O))) K),
        (∃ p : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O,
          eval ((Module.finBasis K _).equivFun p) A≠0) →
        (∀ p : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O,
          eval ((Module.finBasis K _).equivFun p) A≠0 →
            Good p ∧ OddCyclesExact U p.1 p.2 ∧
              Function.Surjective (upperTargetMap (zeroScalarEndpointFamily (by omega : 0<d) hO hJ U p.1 p.2))) →
        (∃ p : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts' O,
          eval ((Module.finBasis K _).equivFun p) D≠0) →
        ∃ p : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts' O,
          eval ((Module.finBasis K _).equivFun p) D≠0 ∧
          let p₀ := fullRestrictCounts hcounts p
          Good p₀ ∧ OddCyclesExact U p₀.1 p₀.2 ∧
          Function.Surjective (upperTargetMap (zeroScalarEndpointFamily (by omega : 0<d) hO hJ U p₀.1 p₀.2)) ∧
          PreparedEndpointThin (by omega : 0<d) hdodd hO hJ heven U (ξ*(n : ℝ)^d) p₀ ∧
          BaseC4GrowthProperty (by omega : 1≤d) R (scalarReserveCount d n) (preparedBaseProjection p₀) ∧
          StrictModel (fun i => outerVectorEquiv.symm (p.2.2 i)) d (G*(n : ℝ)^d) ∧
          ChildFlagCondition (quotientMultiplication (fun i => outerVectorEquiv.symm (p.2.2 i)) d)
            (outerScalarDeficit (fun i => outerVectorEquiv.symm (p.2.2 i))) (C*(n : ℝ)^d)
            (coefficientCoordinates (fun i => p.2.1.1 (Sum.inl i))) := by
  obtain ⟨G,C,hG,hC,hselect⟩ := exact_counts_prepared_restricted_growth_fiber (K := K) (u := u)
    hd hk hh hhpos hb R hP hratio upper a f e ha hc hδ hreserve
  obtain ⟨L,ξ,hξ,hbudget⟩ := eventually_prepared_layered_budget hd h u 0 extra e
    (fun n => oddCoefficientCount d h n) C hC
    (hc.mono fun n hn => hn.quadratic_upper)
    (Eventually.of_forall fun _ => by simp only [Nat.add_zero]; exact le_rfl)
  simp only [Nat.add_zero] at hbudget
  refine ⟨G,C,ξ,hG,hC,hξ,?_⟩
  filter_upwards [hselect,hbudget,eventually_gt_atTop (0 : ℕ)] with n hn hbgt hnpos
  intro J counts counts' O hO hJ heven hcounts hcard
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts' O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  intro Good A D hA hGood hD
  obtain ⟨p,P₀,hP₀,hfiber⟩ := hn J counts counts' O hO hcounts
    (fun p => Good p ∧ OddCyclesExact U p.1 p.2 ∧
      Function.Surjective (upperTargetMap (zeroScalarEndpointFamily (by omega : 0<d) hO hJ U p.1 p.2)))
    A D hA hGood hD
  let rest := (fullScalarFiberCoordinates (fullRestrictCounts hcounts p)).2
  let a₀ := (fullScalarFiberCoordinates (fullRestrictCounts hcounts p)).1
  have hstart := hfiber a₀ hP₀
  rw [fullCountScalarFiberLinear_at] at hstart
  have hchild := hstart.2.2.2.2
  have hbottom := ChildFlagCondition.bottom_thin_slices_coordinates (by omega : 1≤d)
    (fun i => outerVectorEquiv.symm (p.2.2 i)) (fun i => p.2.1.1 (Sum.inl i))
    (outerScalarDeficit (fun i => outerVectorEquiv.symm (p.2.2 i))) (C*(n : ℝ)^d) hchild
  have hgood₀ : ∀ z,eval ((Module.finBasis K _).equivFun z) P₀≠0 →
      OddCyclesExact U rest.1 (scalarFiberCoordinates.symm (z,rest.2.1),rest.2.2) ∧
      Function.Surjective (upperTargetMap (zeroScalarEndpointFamily (by omega : 0<d) hO hJ U rest.1
        (scalarFiberCoordinates.symm (z,rest.2.1),rest.2.2))) := by
    intro z hz
    have hv := (hfiber z hz).2.1.2
    rw [fullCountScalarFiberLinear_restrict] at hv
    exact hv
  have hsmall : 2*(higherRelationCost d h u n+oddCoefficientCount d h n+
      Fintype.card (ProductRows.LayerLabel J counts))+1≤L n := by
    have hh := hbgt.2.2.2.1
    omega
  obtain ⟨P₁,hP₁,hthin⟩ := prepared_scalar_thin_open hd hdodd hO hJ heven U rest hhpos hnpos hU
    R hR hker (C*(n : ℝ)^d) (ξ*(n : ℝ)^d) (by positivity) hbottom (scalarReserveCount d n)
    hstart.2.2.1 P₀ ⟨a₀,hP₀⟩ hgood₀ (L n) hbgt.2.1
    (hbgt.2.2.1.trans (min_le_left _ _)) (fun r => (hbgt.2.2.2.2.1 0 r).2) hsmall
  obtain ⟨z,hz⟩ := hP₁
  obtain ⟨hz₀,hs⟩ := hthin z hz
  obtain ⟨hD',hGood',hgrowth,hmodel,hchild'⟩ := hfiber z hz₀
  refine ⟨fullCountScalarFiberLinear hcounts (z,p),hD',hGood'.1,hGood'.2.1,hGood'.2.2,?_,
    hgrowth,hmodel,hchild'⟩
  rw [fullCountScalarFiberLinear_restrict]
  exact hs

end Froberg.PreparedParameters
