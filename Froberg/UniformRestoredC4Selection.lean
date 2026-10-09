module

public import Froberg.RestoredC4Selection
public import Froberg.StrictThinCoefficientOpen
public import Froberg.FieldUniformC4Growth
public import Froberg.FieldUniformCountedPrivate

@[expose] public section

/-! Field-uniform restored C.4 selection. The strict-model and ordinary
scalar-growth opens are inputs; the positive thinness constant and its
numerical cutoff are chosen before the field and restored family. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true
namespace Froberg.PreparedParameters
open Froberg PreparedTarget Filter Module MvPolynomial VectorExpansionOpen Quartic
open VectorMultiplicationCoordinates BilinearScalarFamily
open scoped Topology
attribute [local instance] tensorFormGroup
attribute [local irreducible] RestoredEndpointThin

/-- The passage from an outer open to a full restored joint selection is finite. -/
theorem restored_joint_of_strict_thin_open {K : Type} [Field K] [Infinite K]
    {h n d f : ℕ} {G C : ℝ} (hnpos : 0 < n)
    (houter : StrictThinCoefficientOpen K h n d f G C) :
      ∀ (J : Finset ℕ) (counts : ℕ → ℕ) (O : ℕ → Submodule K (Poly K h))
        (hO : ∀ j∈J,O j≤Forms K h j),
      letI : Module.Finite K (Space n d (upperCount n d) J counts O) := finite_space hO
      ∀ D : MvPolynomial (Fin (finrank K
        (RestoredOuterSpace n d (upperCount n d) f J counts O))) K,
        (∃ p : RestoredOuterSpace n d (upperCount n d) f J counts O,
          eval ((Module.finBasis K _).equivFun p) D≠0) →
        ∃ p : RestoredOuterSpace n d (upperCount n d) f J counts O,
          eval ((Module.finBasis K _).equivFun p) D≠0 ∧
          StrictModel (fun i => PreparedTarget.outerVectorEquiv.symm (p.2 i)) d G ∧
          ChildFlagCondition (quotientMultiplication (fun i => PreparedTarget.outerVectorEquiv.symm (p.2 i)) d)
            (outerScalarDeficit (fun i => PreparedTarget.outerVectorEquiv.symm (p.2 i))) C
            (coefficientCoordinates (fun i => p.1.1.1 (Sum.inl i))) := by
  have hn := strictThinCoefficientOpen_joint hnpos houter
  intro J counts O hO
  letI : Module.Finite K (Space n d (upperCount n d) J counts O) := finite_space hO
  letI : Module.Finite K (RestoredJointRest n d J counts O) := finite_restoredJointRest hO
  intro D hD
  let L := restoredJointFromCoordinates (m := n) (d := d) (q := upperCount n d) (f := f) (counts := counts) hO
  let coord := (Module.finBasis K (RestoredOuterSpace n d (upperCount n d) f J counts O)).equivFun
  let P := substituteAffine (coord.toLinearMap.comp L) 0 D
  have heval (x) : eval x P=eval (coord (L x)) D := by
    rw [show P=substituteAffine (coord.toLinearMap.comp L) 0 D from rfl,eval_substituteAffine,add_zero]
    rfl
  have hP : ∃ x,eval x P≠0 := by
    obtain ⟨p,hp⟩ := hD
    obtain ⟨x,hx⟩ := restoredJointFromCoordinates_surjective hO p
    exact ⟨x,by rw [heval,hx];exact hp⟩
  obtain ⟨pF,pQ,pR,hp,hmodel,hchild⟩ := hn _ P hP
  let p := L (Sum.elim pF (Sum.elim pQ pR))
  have hcoords := restoredJointFromCoordinates_eval hO pF pQ pR
  have hF : (fun i => PreparedTarget.outerVectorEquiv.symm (p.2 i))=VectorParameters.generators pF :=
    congrArg Prod.fst hcoords
  have hQ : (fun i => p.1.1.1 (Sum.inl i))=coefficientForms K n d (upperCount n d) pQ :=
    congrArg (fun x => x.2.1) hcoords
  refine ⟨p,?_,?_,?_⟩
  · exact (heval _).symm ▸ hp
  · rw [hF]
    exact hmodel
  · rw [hF,hQ]
    change ChildFlagCondition _ _ _ (coefficientCoordinates (coefficientCoordinates.symm pQ))
    rw [LinearEquiv.apply_symm_apply]
    exact hchild

/-- Restriction to the base counts and scalar freezing preserve the supplied open. -/
theorem restored_restricted_fiber_of_strict_thin_open
    {K : Type} [Field K] [Infinite K] {h n d f : ℕ} {G C : ℝ}
    (hnpos : 0 < n) (houter : StrictThinCoefficientOpen K h n d f G C) :
      ∀ (J : Finset ℕ) (counts counts' : ℕ → ℕ) (O : ℕ → Submodule K (Poly K h))
        (hO : ∀ j ∈ J, O j ≤ Forms K h j) (hcounts : ∀ j ∈ J, counts j ≤ counts' j),
      letI : Module.Finite K (Space n d (upperCount n d) J counts O) := finite_space hO
      letI : Module.Finite K (Space n d (upperCount n d) J counts' O) := finite_space hO
      ∀ (Good : RestoredOuterSpace n d (upperCount n d) f J counts O → Prop)
        (A : MvPolynomial (Fin (finrank K
          (RestoredOuterSpace n d (upperCount n d) f J counts O))) K)
        (D : MvPolynomial (Fin (finrank K
          (RestoredOuterSpace n d (upperCount n d) f J counts' O))) K),
        (∃ v : RestoredOuterSpace n d (upperCount n d) f J counts O,
          eval ((Module.finBasis K _).equivFun v) A ≠ 0) →
        (∀ v : RestoredOuterSpace n d (upperCount n d) f J counts O,
          eval ((Module.finBasis K _).equivFun v) A ≠ 0 → Good v) →
        (∃ v : RestoredOuterSpace n d (upperCount n d) f J counts' O,
          eval ((Module.finBasis K _).equivFun v) D ≠ 0) →
        ∃ (p : RestoredOuterSpace n d (upperCount n d) f J counts' O)
          (P₀ : MvPolynomial (Fin (finrank K (PositiveScalars (K := K) n d J counts))) K),
          eval ((Module.finBasis K _).equivFun
            (restoredScalarFiberCoordinates (restoredRestrictCounts hcounts p)).1) P₀ ≠ 0 ∧
          ∀ a', eval ((Module.finBasis K _).equivFun a') P₀ ≠ 0 →
            let p' := restoredCountScalarFiberLinear hcounts (a',p)
            eval ((Module.finBasis K _).equivFun p') D ≠ 0 ∧
            Good (restoredRestrictCounts hcounts p') ∧
            StrictModel (fun i => outerVectorEquiv.symm (p'.2 i)) d G ∧
            ChildFlagCondition (quotientMultiplication (fun i => outerVectorEquiv.symm (p'.2 i)) d)
              (outerScalarDeficit (fun i => outerVectorEquiv.symm (p'.2 i))) C
              (coefficientCoordinates (fun i => p'.1.1.1 (Sum.inl i))) := by
  have hn := restored_joint_of_strict_thin_open hnpos houter
  intro J counts counts' O hO hcounts
  letI : Module.Finite K (Space n d (upperCount n d) J counts O) := finite_space hO
  letI : Module.Finite K (Space n d (upperCount n d) J counts' O) := finite_space hO
  intro Good A D hA hGood hD
  obtain ⟨B,hB,hBgood⟩ := principal_open_linear_pullback (restoredRestrictCounts hcounts)
    (restoredRestrictCounts_surjective hcounts) A hA Good hGood
  obtain ⟨v,hv⟩ := finite_basis_principal_intersection
    (V := RestoredOuterSpace n d (upperCount n d) f J counts' O)
    ![B,D] (by
      intro i
      fin_cases i
      · exact hB
      · exact hD)
  have hBD : ∃ v : RestoredOuterSpace n d (upperCount n d) f J counts' O,
      eval ((Module.finBasis K _).equivFun v) (B*D) ≠ 0 :=
    ⟨v,by simpa [map_mul] using mul_ne_zero (hv 0) (hv 1)⟩
  obtain ⟨p,hp,hmodel,hchild⟩ := hn J counts' O hO (B*D) hBD
  obtain ⟨P₀,hP₀,hfiber⟩ := restored_count_joint_scalar_fiber_at hcounts hO
    G C (B*D) p hp hmodel hchild
  refine ⟨p,P₀,hP₀,?_⟩
  intro a' ha'
  obtain ⟨hBD',hm,hchild'⟩ := hfiber a' ha'
  have hboth := mul_ne_zero_iff.mp (show
      eval ((Module.finBasis K _).equivFun (restoredCountScalarFiberLinear hcounts (a',p))) B *
      eval ((Module.finBasis K _).equivFun (restoredCountScalarFiberLinear hcounts (a',p))) D ≠ 0 by
        simpa only [map_mul] using hBD')
  exact ⟨hboth.2,hBgood _ hboth.1,hm,hchild'⟩

/-- The thinness constant and cutoff precede the choice of the field and
all restored-family parameters. Only uniform input opens are assumed. -/
theorem field_uniform_restored_c4_selection {d h : ℕ}
    (hd : 3 ≤ d) (hdeven : d%2=0) (hhpos : 0 < h)
    (f e : ℕ → ℕ) (extra : ℕ) {G C : ℝ} (hG : 0 < G) (hC : 0 < C)
    (he : ∀ᶠ n : ℕ in atTop,
      (e n : ℝ) < countBeta d*(h : ℝ)^2*(n : ℝ)^(d-2))
    (houter : ∀ᶠ n : ℕ in atTop, ∀ (K : Type) [Field K] [Infinite K],
      StrictThinCoefficientOpen K h n d (f n) (G*(n : ℝ)^d) (C*(n : ℝ)^d))
    (hgrowth : ∀ᶠ n : ℕ in atTop, ∀ (K : Type) [Field K] [Infinite K],
      HasOddScalarLayersOpen K h n d (f n) (upperCount n d) (scalarReserveCount d n)) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (K : Type) [Field K] [Infinite K] [IsAlgClosed K],
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
  obtain ⟨L,ξ,hξ,hbudget⟩ := eventually_prepared_layered_budget hd h 0 0 extra e
    (fun n => oddCoefficientCount d h n) C hC he
    (Eventually.of_forall fun _ => by simp only [Nat.add_zero]; exact le_rfl)
  simp only [Nat.add_zero] at hbudget
  refine ⟨ξ,hξ,?_⟩
  filter_upwards [houter,hgrowth,hbudget,eventually_gt_atTop (0 : ℕ)] with n ho hg hbgt hnpos
  intro K _ _ _
  have hn := restored_restricted_fiber_of_strict_thin_open hnpos (ho K)
  have hgn := hg K
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

/-- Exact count hypotheses provide both input opens uniformly over the field. -/
theorem uniform_exact_counts_restored_c4_selection {d k h lo : ℕ}
    (hd : 3 ≤ d) (hdeven : d%2=0) (hk : 0 < k)
    (hh : h=k*centralHalfBinomial d) (hhpos : 0 < h)
    (upper : Bool) (a f e : ℕ → ℕ) (ha : ∀ n, a n ≤ n)
    (hc : ∀ᶠ n in atTop, ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0 < δ)
    (hreserve : ∀ᶠ n : ℕ in atTop, δ*(n : ℝ)^(2*d-2) < dimensionReserve d h n (f n))
    (extra : ℕ) :
    ∃ G C ξ : ℝ, 0 < G ∧ 0 < C ∧ 0 < ξ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (K : Type) [Field K] [Infinite K] [IsAlgClosed K],
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
  obtain ⟨G,C,hG,hC,ho⟩ := uniform_exact_counts_private_thin_open (b := 0)
    hd hk hh hhpos upper a f e ha hc hδ hreserve
  have houter : ∀ᶠ n : ℕ in atTop, ∀ (K : Type) [Field K] [Infinite K],
      StrictThinCoefficientOpen K h n d (f n) (G*(n : ℝ)^d) (C*(n : ℝ)^d) := by
    simpa only [StrictThinCoefficientOpen,Nat.add_zero] using ho
  obtain ⟨ξ,hξ,hselect⟩ := field_uniform_restored_c4_selection hd hdeven hhpos f e extra hG hC
    (hc.mono fun n hn => hn.quadratic_upper) houter
    (eventually_uniform_counted_odd_scalar_growth hd hhpos upper a f e hc)
  exact ⟨G,C,ξ,hG,hC,hξ,hselect⟩

end Froberg.PreparedParameters
