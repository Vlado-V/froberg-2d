module

public import Froberg.PreparedC4Selection
public import Froberg.FieldUniformC4Growth
public import Froberg.StrictThinCoefficientOpen
public import Froberg.FieldUniformCountedPrivate

@[expose] public section

/-! Field-independent C.4 selection for the odd prepared family. Every
asymptotic choice is numerical; fields, pure tuples and projections are
introduced only after the resulting cutoff. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency true
namespace Froberg.PreparedParameters
open Froberg PreparedTarget Filter Module MvPolynomial VectorExpansionOpen Quartic
open scoped Topology
attribute [local instance] tensorFormGroup
attribute [local irreducible] PreparedEndpointThin BaseC4GrowthProperty

theorem prepared_joint_of_strict_thin_open {K : Type} [Field K] [Infinite K]
    {h n d f u : ℕ} {G C : ℝ} (hnpos : 0 < n)
    (houter : StrictThinCoefficientOpen K h n d f G C) :
      ∀ (J : Finset ℕ) (counts : ℕ → ℕ) (O : ℕ → Submodule K (Poly K h))
        (hO : ∀ j∈J,O j≤Forms K h j),
      letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts O) :=
        FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
      ∀ D : MvPolynomial (Fin (finrank K
        (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts O))) K,
        (∃ p : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts O,
          eval ((Module.finBasis K _).equivFun p) D≠0) →
        ∃ p : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts O,
          eval ((Module.finBasis K _).equivFun p) D≠0 ∧
          StrictModel (fun i => PreparedTarget.outerVectorEquiv.symm (p.2.2 i)) d G ∧
          ChildFlagCondition (quotientMultiplication (fun i => PreparedTarget.outerVectorEquiv.symm (p.2.2 i)) d)
            (outerScalarDeficit (fun i => PreparedTarget.outerVectorEquiv.symm (p.2.2 i))) C
            (coefficientCoordinates (fun i => p.2.1.1 (Sum.inl i))) := by
  intro J counts O hO
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  letI : Module.Finite K (JointRest n d (upperCount n d) f u J counts O) := finite_jointRest hO
  intro D hD
  let L := preparedJointFromCoordinates (m := n) (d := d) (q := upperCount n d) (f := f) (u := u) (counts := counts) hO
  let coord := (Module.finBasis K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts O)).equivFun
  let P := substituteAffine (coord.toLinearMap.comp L) 0 D
  have heval (x) : eval x P=eval (coord (L x)) D := by
    rw [show P=substituteAffine (coord.toLinearMap.comp L) 0 D from rfl,eval_substituteAffine,add_zero]
    rfl
  have hP : ∃ x,eval x P≠0 := by
    obtain ⟨p,hp⟩ := hD
    obtain ⟨x,hx⟩ := preparedJointFromCoordinates_surjective hO p
    exact ⟨x,by rw [heval,hx];exact hp⟩
  obtain ⟨pF,pQ,pR,hp,hmodel,hchild⟩ := strictThinCoefficientOpen_joint hnpos houter _ P hP
  let p := L (Sum.elim pF (Sum.elim pQ pR))
  have hcoords := preparedJointFromCoordinates_eval hO pF pQ pR
  have hF : (fun i => PreparedTarget.outerVectorEquiv.symm (p.2.2 i))=VectorParameters.generators pF :=
    congrArg Prod.fst hcoords
  have hQ : (fun i => p.2.1.1 (Sum.inl i))=coefficientForms K n d (upperCount n d) pQ :=
    congrArg (fun x => x.2.1) hcoords
  refine ⟨p,?_,?_,?_⟩
  · exact (heval _).symm ▸ hp
  · rw [hF]
    exact hmodel
  · rw [hF,hQ]
    change ChildFlagCondition _ _ _ (coefficientCoordinates (coefficientCoordinates.symm pQ))
    rw [LinearEquiv.apply_symm_apply]
    exact hchild


def PreparedGrowthFiberAt (K : Type) [Field K] [Infinite K]
    {h d b : ℕ} (hd : 1 ≤ d) (n f u : ℕ)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K)) (G C : ℝ) : Prop :=
      ∀ (J : Finset ℕ) (counts counts' : ℕ → ℕ) (O : ℕ → Submodule K (Poly K h))
        (hO : ∀ j ∈ J, O j ≤ Forms K h j) (hcounts : ∀ j ∈ J, counts j ≤ counts' j),
      letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts O) :=
        FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
      letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts' O) :=
        FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
      ∀ (Good : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts O → Prop)
        (A : MvPolynomial (Fin (finrank K
          (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts O))) K)
        (D : MvPolynomial (Fin (finrank K
          (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts' O))) K),
        (∃ v : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts O,
          eval ((Module.finBasis K _).equivFun v) A ≠ 0) →
        (∀ v : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts O,
          eval ((Module.finBasis K _).equivFun v) A ≠ 0 → Good v) →
        (∃ v : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts' O,
          eval ((Module.finBasis K _).equivFun v) D ≠ 0) →
        ∃ (p : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts' O)
          (P₀ : MvPolynomial (Fin (finrank K (PositiveScalars (K := K) n d J counts))) K),
          eval ((Module.finBasis K _).equivFun
            (fullScalarFiberCoordinates (fullRestrictCounts hcounts p)).1) P₀ ≠ 0 ∧
          ∀ a', eval ((Module.finBasis K _).equivFun a') P₀ ≠ 0 →
            let p' := fullCountScalarFiberLinear hcounts (a',p)
            eval ((Module.finBasis K _).equivFun p') D ≠ 0 ∧
            Good (fullRestrictCounts hcounts p') ∧
            BaseC4GrowthProperty hd R (scalarReserveCount d n)
              (preparedBaseProjection (fullRestrictCounts hcounts p')) ∧
            StrictModel (fun i => outerVectorEquiv.symm (p'.2.2 i)) d G ∧
            ChildFlagCondition (quotientMultiplication (fun i => outerVectorEquiv.symm (p'.2.2 i)) d)
              (outerScalarDeficit (fun i => outerVectorEquiv.symm (p'.2.2 i))) C
              (coefficientCoordinates (fun i => p'.2.1.1 (Sum.inl i)))

theorem prepared_growth_fiber_of_strict_thin_open {K : Type} [Field K] [Infinite K]
    {h n d f u b : ℕ} (hd : 1 ≤ d) {G C : ℝ} (hnpos : 0 < n)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K))
    (houter : StrictThinCoefficientOpen K h n d f G C)
    (hgrowth : HasBaseC4GrowthOpen (m := n) (f := f) (q := upperCount n d)
      hd R (scalarReserveCount d n)) : PreparedGrowthFiberAt K hd n f u R G C := by
  intro J counts counts' O hO hcounts
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts' O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  intro Good A D hA hGood hD
  obtain ⟨B,hB,hBgrowth⟩ := prepared_base_growth_open (u := u) (counts := counts) hd hO R hgrowth
  obtain ⟨v,hv⟩ := finite_basis_principal_intersection
    (V := FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts O)
    ![A,B] (by intro i; fin_cases i; exact hA; exact hB)
  have hAB : ∃ v : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts O,
      eval ((Module.finBasis K _).equivFun v) (A*B) ≠ 0 :=
    ⟨v,by simpa [map_mul] using mul_ne_zero (hv 0) (hv 1)⟩
  let GoodPlus := fun v => Good v ∧ BaseC4GrowthProperty hd R (scalarReserveCount d n)
      (preparedBaseProjection v)
  have hABgood : ∀ v : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts O,
      eval ((Module.finBasis K _).equivFun v) (A*B) ≠ 0 → GoodPlus v := by
    intro v hv
    have hboth := mul_ne_zero_iff.mp (show eval ((Module.finBasis K _).equivFun v) A *
        eval ((Module.finBasis K _).equivFun v) B ≠ 0 by simpa only [map_mul] using hv)
    exact ⟨hGood v hboth.1,hBgrowth v hboth.2⟩
  obtain ⟨E,hE,hEgood⟩ := principal_open_linear_pullback (fullRestrictCounts hcounts)
    (fullRestrictCounts_surjective hcounts) (A*B) hAB GoodPlus hABgood
  obtain ⟨v,hv⟩ := finite_basis_principal_intersection
    (V := FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts' O)
    ![E,D] (by intro i; fin_cases i; exact hE; exact hD)
  have hED : ∃ v : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts' O,
      eval ((Module.finBasis K _).equivFun v) (E*D) ≠ 0 :=
    ⟨v,by simpa [map_mul] using mul_ne_zero (hv 0) (hv 1)⟩
  obtain ⟨p,hp,hmodel,hchild⟩ := prepared_joint_of_strict_thin_open hnpos houter J counts' O hO (E*D) hED
  obtain ⟨P₀,hP₀,hfiber⟩ := prepared_count_joint_scalar_fiber_at hcounts hO G C (E*D) p hp hmodel hchild
  refine ⟨p,P₀,hP₀,?_⟩
  intro a' ha'
  obtain ⟨hED',hm,hchild'⟩ := hfiber a' ha'
  have hboth := mul_ne_zero_iff.mp (show
      eval ((Module.finBasis K _).equivFun (fullCountScalarFiberLinear hcounts (a',p))) E *
      eval ((Module.finBasis K _).equivFun (fullCountScalarFiberLinear hcounts (a',p))) D ≠ 0 by
        simpa only [map_mul] using hED')
  exact ⟨hboth.2,(hEgood _ hboth.1).1,(hEgood _ hboth.1).2,hm,hchild'⟩

def PreparedC4SelectionAt (K : Type) [Field K] [Infinite K] [IsAlgClosed K]
    {d h u b : ℕ} (hd : 3 ≤ d) (hdodd : d%2=1) (n f e extra : ℕ)
    (U : Fin u → Forms K h d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K)) (G C ξ : ℝ) : Prop :=
      ∀ (J : Finset ℕ) (counts counts' : ℕ → ℕ) (O : ℕ → Submodule K (Poly K h))
        (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
        (heven : ∀ j∈J,j%2=0) (hcounts : ∀ j∈J,counts j≤counts' j),
      Fintype.card (ProductRows.LayerLabel J counts) ≤
        Fintype.card (ProductRows.LayerLabel (allEvenIndices d) (allEvenCount d h n (e+extra))) →
      letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts O) :=
        FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
      letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts' O) :=
        FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
      ∀ (Good : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts O → Prop)
        (A : MvPolynomial (Fin (finrank K
          (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts O))) K)
        (D : MvPolynomial (Fin (finrank K
          (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts' O))) K),
        (∃ p : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts O,
          eval ((Module.finBasis K _).equivFun p) A≠0) →
        (∀ p : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts O,
          eval ((Module.finBasis K _).equivFun p) A≠0 →
            Good p ∧ OddCyclesExact U p.1 p.2 ∧
              Function.Surjective (upperTargetMap (zeroScalarEndpointFamily (by omega : 0<d) hO hJ U p.1 p.2))) →
        (∃ p : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts' O,
          eval ((Module.finBasis K _).equivFun p) D≠0) →
        ∃ p : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) f u J counts' O,
          eval ((Module.finBasis K _).equivFun p) D≠0 ∧
          let p₀ := fullRestrictCounts hcounts p
          Good p₀ ∧ OddCyclesExact U p₀.1 p₀.2 ∧
          Function.Surjective (upperTargetMap (zeroScalarEndpointFamily (by omega : 0<d) hO hJ U p₀.1 p₀.2)) ∧
          PreparedEndpointThin (by omega : 0<d) hdodd hO hJ heven U (ξ*(n : ℝ)^d) p₀ ∧
          BaseC4GrowthProperty (by omega : 1≤d) R (scalarReserveCount d n) (preparedBaseProjection p₀) ∧
          StrictModel (fun i => outerVectorEquiv.symm (p.2.2 i)) d (G*(n : ℝ)^d) ∧
          ChildFlagCondition (quotientMultiplication (fun i => outerVectorEquiv.symm (p.2.2 i)) d)
            (outerScalarDeficit (fun i => outerVectorEquiv.symm (p.2.2 i))) (C*(n : ℝ)^d)
            (coefficientCoordinates (fun i => p.2.1.1 (Sum.inl i)))

theorem field_uniform_prepared_c4_selection {d k h lo u b : ℕ}
    (hd : 3 ≤ d) (hdodd : d%2=1) (hhpos : 0 < h) (hb : 0 < b)
    (hratio : (h : ℝ)/(2*((1+(d-1) : ℕ) : ℝ)) ≤
      (b : ℝ)/((h+(d-1)-1).choose (d-1) : ℝ))
    (upper : Bool) (a f e : ℕ → ℕ)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    (extra : ℕ) (G C : ℝ) (hC : 0 < C)
    (houter : ∀ᶠ n : ℕ in atTop, ∀ (K : Type) [Field K] [Infinite K],
      StrictThinCoefficientOpen K h n d (f n) (G*(n : ℝ)^d) (C*(n : ℝ)^d)) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (K : Type) [Field K] [Infinite K] [IsAlgClosed K],
      ∀ U : Fin u → Forms K h d, LinearIndependent K U →
      ∀ R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K), Function.Surjective R →
      R.ker=(Submodule.span K (Set.range U)).map (topGrowthDegree (by omega : 1≤d) h).symm.toLinearMap →
      (∀ L : Submodule K (Forms K h (d-1)),b*finrank K L ≤
        finrank K (Forms K h (d-1))*
          finrank K ((BilinearImage.image (gradedMultiplication (d := 1) (e := d-1)) L).map R)) →
      PreparedC4SelectionAt K hd hdodd n (f n) (e n) extra U R G C ξ := by
  have hgrowth := eventually_uniform_counted_base_c4_growth hd hhpos hb hratio upper a f e hc
  obtain ⟨L,ξ,hξ,hbudget⟩ := eventually_prepared_layered_budget hd h u 0 extra e
    (fun n => oddCoefficientCount d h n) C hC
    (hc.mono fun n hn => hn.quadratic_upper)
    (Eventually.of_forall fun _ => by simp only [Nat.add_zero]; exact le_rfl)
  simp only [Nat.add_zero] at hbudget
  refine ⟨ξ,hξ,?_⟩
  filter_upwards [houter,hgrowth,hbudget,eventually_gt_atTop (0 : ℕ)] with n houterN hgrowthN hbgt hnpos
  intro K _ _ _ U hU R hR hker hP
  have hn := prepared_growth_fiber_of_strict_thin_open (u := u) (by omega : 1≤d)
    hnpos R (houterN K) (hgrowthN K R hP)
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



/-- Exact counts supply the outer open as well. All three constants and
all scalar-variable thresholds precede the field and pure-family choices. -/
theorem uniform_exact_counts_prepared_c4_selection {d k h lo u b : ℕ}
    (hd : 3 ≤ d) (hdodd : d%2=1) (hk : 0 < k)
    (hh : h=k*centralHalfBinomial d) (hhpos : 0 < h) (hb : 0 < b)
    (hratio : (h : ℝ)/(2*((1+(d-1) : ℕ) : ℝ)) ≤
      (b : ℝ)/((h+(d-1)-1).choose (d-1) : ℝ))
    (upper : Bool) (a f e : ℕ → ℕ) (ha : ∀ n,a n≤n)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0 < δ)
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n))
    (extra : ℕ) :
    ∃ G C ξ : ℝ,0<G ∧ 0<C ∧ 0<ξ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (K : Type) [Field K] [Infinite K] [IsAlgClosed K],
      ∀ U : Fin u → Forms K h d, LinearIndependent K U →
      ∀ R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K), Function.Surjective R →
      R.ker=(Submodule.span K (Set.range U)).map (topGrowthDegree (by omega : 1≤d) h).symm.toLinearMap →
      (∀ L : Submodule K (Forms K h (d-1)),b*finrank K L ≤
        finrank K (Forms K h (d-1))*
          finrank K ((BilinearImage.image (gradedMultiplication (d := 1) (e := d-1)) L).map R)) →
      PreparedC4SelectionAt K hd hdodd n (f n) (e n) extra U R G C ξ := by
  obtain ⟨G,C,hG,hC,hopen⟩ := uniform_exact_counts_private_thin_open (b := 0)
    hd hk hh hhpos upper a f e ha hc hδ hreserve
  have houter : ∀ᶠ n : ℕ in atTop, ∀ (K : Type) [Field K] [Infinite K],
      StrictThinCoefficientOpen K h n d (f n) (G*(n : ℝ)^d) (C*(n : ℝ)^d) := by
    filter_upwards [hopen] with n hn
    intro K _ _
    simpa only [StrictThinCoefficientOpen,Nat.add_zero] using hn K
  obtain ⟨ξ,hξ,hselect⟩ := field_uniform_prepared_c4_selection (u := u)
    hd hdodd hhpos hb hratio upper a f e hc extra G C hC houter
  exact ⟨G,C,ξ,hG,hC,hξ,hselect⟩

end Froberg.PreparedParameters
