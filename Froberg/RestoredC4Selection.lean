import Froberg.RestoredRestrictedCertifiedFiber
import Froberg.RestoredScalarThinOpen
import Froberg.PreparedBaseGrowthOpen
import Froberg.BottomThinFlag

/-! Actual-count C.4 selection for the final restored family keeps all
temporary added columns and the supplied enlarged-family open fixed. -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true
namespace Froberg.PreparedParameters
open Froberg PreparedTarget Filter Module MvPolynomial VectorExpansionOpen Quartic
open scoped Topology
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K]
attribute [local irreducible] RestoredEndpointThin

theorem exact_counts_restored_c4_selection {d k h lo : ℕ}
    (hd : 3 ≤ d) (hdeven : d%2=0) (hk : 0 < k)
    (hh : h=k*centralHalfBinomial d) (hhpos : 0 < h)
    (upper : Bool) (a f e : ℕ → ℕ) (ha : ∀ n, a n ≤ n)
    (hc : ∀ᶠ n in atTop, ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0 < δ)
    (hreserve : ∀ᶠ n : ℕ in atTop, δ*(n : ℝ)^(2*d-2) < dimensionReserve d h n (f n))
    (extra : ℕ) :
    ∃ G C ξ : ℝ, 0 < G ∧ 0 < C ∧ 0 < ξ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Finset ℕ) (counts counts' : ℕ → ℕ) (O : ℕ → Submodule K (Poly K h))
        (hO : ∀ j ∈ J, O j ≤ Forms K h j) (hJ : ∀ j ∈ J, j ≤ d)
        (heven : ∀ j ∈ J, j%2=0) (hcounts : ∀ j ∈ J, counts j ≤ counts' j)
        (r : ℕ) (idx : Fin r ≃ Label (upperCount n d) J counts)
        (slot : Fin (finrank K (Forms K h d)) → Fin r)
        (hslot : ∀ i, 0 < degree (idx (slot i))),
      Fintype.card (ProductRows.LayerLabel J counts) ≤
        Fintype.card (ProductRows.LayerLabel (allEvenIndices d) (allEvenCount d h n (e n+extra))) →
      letI : Module.Finite K (Space n d (upperCount n d) J counts O) := finite_space hO
      letI : Module.Finite K (Space n d (upperCount n d) J counts' O) := finite_space hO
      ∀ (Good : RestoredOuterSpace n d (upperCount n d) (f n) J counts O → Prop)
        (A : MvPolynomial (Fin (finrank K (RestoredOuterSpace n d (upperCount n d) (f n) J counts O))) K)
        (D : MvPolynomial (Fin (finrank K (RestoredOuterSpace n d (upperCount n d) (f n) J counts' O))) K),
        (∃ p : RestoredOuterSpace n d (upperCount n d) (f n) J counts O,
          eval ((Module.finBasis K _).equivFun p) A ≠ 0) →
        (∀ p : RestoredOuterSpace n d (upperCount n d) (f n) J counts O,
          eval ((Module.finBasis K _).equivFun p) A ≠ 0 →
            Good p ∧
            OddSplitExact (restoredBiformFamily hdeven hO hJ heven idx slot p.1)
              (fun i => linearOddForm (by omega : 1 ≤ d) (outerVectorEquiv.symm (p.2 i))) ∧
            Function.Surjective (upperTargetMap
              (restoredOuterEndpoint (by omega : 1 ≤ d) hdeven hO hJ heven idx slot p))) →
        (∃ p : RestoredOuterSpace n d (upperCount n d) (f n) J counts' O,
          eval ((Module.finBasis K _).equivFun p) D ≠ 0) →
        ∃ p : RestoredOuterSpace n d (upperCount n d) (f n) J counts' O,
          eval ((Module.finBasis K _).equivFun p) D ≠ 0 ∧
          let p₀ := restoredRestrictCounts hcounts p
          Good p₀ ∧
          OddSplitExact (restoredBiformFamily hdeven hO hJ heven idx slot p₀.1)
            (fun i => linearOddForm (by omega : 1 ≤ d) (outerVectorEquiv.symm (p₀.2 i))) ∧
          Function.Surjective (upperTargetMap
            (restoredOuterEndpoint (by omega : 1 ≤ d) hdeven hO hJ heven idx slot p₀)) ∧
          RestoredEndpointThin (by omega : 1 ≤ d) hdeven hO hJ heven idx slot (ξ*(n : ℝ)^d) p₀ ∧
          StrictModel (fun i => outerVectorEquiv.symm (p.2 i)) d (G*(n : ℝ)^d) ∧
          ChildFlagCondition (quotientMultiplication (fun i => outerVectorEquiv.symm (p.2 i)) d)
            (outerScalarDeficit (fun i => outerVectorEquiv.symm (p.2 i))) (C*(n : ℝ)^d)
            (coefficientCoordinates (fun i => p.1.1.1 (Sum.inl i))) := by
  obtain ⟨G,C,hG,hC,hselect⟩ := exact_counts_restored_restricted_certified_fiber (K := K)
    hd hk hh hhpos upper a f e ha hc hδ hreserve
  have hgrowth := eventually_counted_odd_scalar_growth (K := K) hd hhpos upper a f e hc
  obtain ⟨L,ξ,hξ,hbudget⟩ := eventually_prepared_layered_budget hd h 0 0 extra e
    (fun n => oddCoefficientCount d h n) C hC
    (hc.mono fun n hn => hn.quadratic_upper)
    (Eventually.of_forall fun _ => by simp only [Nat.add_zero]; exact le_rfl)
  simp only [Nat.add_zero] at hbudget
  refine ⟨G,C,ξ,hG,hC,hξ,?_⟩
  filter_upwards [hselect,hgrowth,hbudget,eventually_gt_atTop (0 : ℕ)] with n hn hgn hbgt hnpos
  intro J counts counts' O hO hJ heven hcounts r idx slot hslot hcard
  letI : Module.Finite K (Space n d (upperCount n d) J counts O) := finite_space hO
  letI : Module.Finite K (Space n d (upperCount n d) J counts' O) := finite_space hO
  intro Good A D hA hGood hD
  obtain ⟨B,hB,hBgrowth⟩ := restored_base_ordinary_growth_open (counts := counts) hO hgn
  obtain ⟨v,hv⟩ := finite_basis_principal_intersection
    (V := RestoredOuterSpace n d (upperCount n d) (f n) J counts O) ![A,B] (by
      intro i
      fin_cases i
      · exact hA
      · exact hB)
  have hAB : ∃ v : RestoredOuterSpace n d (upperCount n d) (f n) J counts O,
      eval ((Module.finBasis K _).equivFun v) (A*B) ≠ 0 :=
    ⟨v,by simpa [map_mul] using mul_ne_zero (hv 0) (hv 1)⟩
  obtain ⟨p,P₀,hP₀,hfiber⟩ := hn J counts counts' O hO hcounts
    (fun p => (Good p ∧
      OddSplitExact (restoredBiformFamily hdeven hO hJ heven idx slot p.1)
        (fun i => linearOddForm (by omega : 1 ≤ d) (outerVectorEquiv.symm (p.2 i))) ∧
      Function.Surjective (upperTargetMap
        (restoredOuterEndpoint (by omega : 1 ≤ d) hdeven hO hJ heven idx slot p))) ∧
      ∀ (j : ℕ) (hj : 3 ≤ j) (hjd : j ≤ d),
        OddScalarLayerProperty (scalarReserveCount d n) (by omega) hjd
          (oddScalarBiformParameters (restoredBaseProjection p)))
    (A*B) D hAB (by
      intro p hp
      have hboth := mul_ne_zero_iff.mp (show eval ((Module.finBasis K _).equivFun p) A *
        eval ((Module.finBasis K _).equivFun p) B ≠ 0 by simpa only [map_mul] using hp)
      exact ⟨hGood p hboth.1,hBgrowth p hboth.2⟩) hD
  let rest := (restoredScalarFiberCoordinates (restoredRestrictCounts hcounts p)).2
  let a₀ := (restoredScalarFiberCoordinates (restoredRestrictCounts hcounts p)).1
  have hstart := hfiber a₀ hP₀
  rw [restoredCountScalarFiberLinear_at] at hstart
  have hbottom := ChildFlagCondition.bottom_thin_slices_coordinates (by omega : 1 ≤ d)
    (fun i => outerVectorEquiv.symm (p.2 i)) (fun i => p.1.1.1 (Sum.inl i))
    (outerScalarDeficit (fun i => outerVectorEquiv.symm (p.2 i))) (C*(n : ℝ)^d) hstart.2.2.2
  have hgood₀ : ∀ z, eval ((Module.finBasis K _).equivFun z) P₀ ≠ 0 →
      OddSplitExact
        (restoredBiformFamily hdeven hO hJ heven idx slot (restoredScalarFiberCoordinates.symm (z,rest)).1)
        (fun i => linearOddForm (by omega : 1 ≤ d) (outerVectorEquiv.symm (rest.2.2 i))) ∧
      Function.Surjective (upperTargetMap (restoredOuterEndpoint (by omega : 1 ≤ d)
        hdeven hO hJ heven idx slot (restoredScalarFiberCoordinates.symm (z,rest)))) := by
    intro z hz
    have hv := (hfiber z hz).2.1.1.2
    rw [restoredCountScalarFiberLinear_restrict] at hv
    exact hv
  have hsmall : 2*(oddCoefficientCount d h n+Fintype.card (ProductRows.LayerLabel J counts))+1 ≤ L n := by
    have hb := hbgt.2.2.2.1
    omega
  obtain ⟨P₁,hP₁,hthin⟩ := restored_scalar_thin_open hd hdeven hO hJ heven idx slot hslot rest
    hhpos hnpos (C*(n : ℝ)^d) (ξ*(n : ℝ)^d) (by positivity) hbottom (scalarReserveCount d n)
    (fun j hj hjd _ => hstart.2.1.2 j hj hjd) P₀ ⟨a₀,hP₀⟩ hgood₀ (L n) hbgt.2.1
    (hbgt.2.2.1.trans (min_le_left _ _)) (fun k => (hbgt.2.2.2.2.1 0 k).2) hsmall
  obtain ⟨z,hz⟩ := hP₁
  obtain ⟨hz₀,hs⟩ := hthin z hz
  obtain ⟨hD',hGood',hmodel,hchild⟩ := hfiber z hz₀
  refine ⟨restoredCountScalarFiberLinear hcounts (z,p),hD',hGood'.1.1,hGood'.1.2.1,
    hGood'.1.2.2,?_,hmodel,hchild⟩
  rw [restoredCountScalarFiberLinear_restrict]
  exact hs

end Froberg.PreparedParameters
