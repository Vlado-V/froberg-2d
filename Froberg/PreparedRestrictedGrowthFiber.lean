module

public import Froberg.PreparedRestrictedCertifiedFiber
public import Froberg.PreparedBaseGrowthOpen

@[expose] public section

/-! The actual-count shared base growth, base certificates, and enlarged
certificates coexist before the temporary columns are frozen. -/
noncomputable section
set_option maxHeartbeats 200000
namespace Froberg.PreparedParameters
open Froberg PreparedTarget Filter Module MvPolynomial VectorExpansionOpen Quartic
open scoped Topology
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K]

theorem exact_counts_prepared_restricted_growth_fiber {d k h lo u b : ℕ}
    (hd : 3 ≤ d) (hk : 0 < k) (hh : h = k*centralHalfBinomial d) (hhpos : 0 < h)
    (hb : 0 < b) (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K))
    (hP : ∀ L : Submodule K (Forms K h (d-1)), b*finrank K L ≤
      finrank K (Forms K h (d-1))*
        finrank K ((BilinearImage.image (gradedMultiplication (d := 1) (e := d-1)) L).map R))
    (hratio : (h : ℝ)/(2*((1+(d-1) : ℕ) : ℝ)) ≤
      (b : ℝ)/((h+(d-1)-1).choose (d-1) : ℝ))
    (upper : Bool) (a f e : ℕ → ℕ) (ha : ∀ n, a n ≤ n)
    (hc : ∀ᶠ n in atTop, ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0 < δ)
    (hreserve : ∀ᶠ n : ℕ in atTop, δ*(n : ℝ)^(2*d-2) < dimensionReserve d h n (f n)) :
    ∃ G C : ℝ, 0 < G ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Finset ℕ) (counts counts' : ℕ → ℕ) (O : ℕ → Submodule K (Poly K h))
        (hO : ∀ j ∈ J, O j ≤ Forms K h j) (hcounts : ∀ j ∈ J, counts j ≤ counts' j),
      letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O) :=
        FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
      letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts' O) :=
        FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
      ∀ (Good : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O → Prop)
        (A : MvPolynomial (Fin (finrank K
          (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O))) K)
        (D : MvPolynomial (Fin (finrank K
          (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts' O))) K),
        (∃ v : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O,
          eval ((Module.finBasis K _).equivFun v) A ≠ 0) →
        (∀ v : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O,
          eval ((Module.finBasis K _).equivFun v) A ≠ 0 → Good v) →
        (∃ v : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts' O,
          eval ((Module.finBasis K _).equivFun v) D ≠ 0) →
        ∃ (p : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts' O)
          (P₀ : MvPolynomial (Fin (finrank K (PositiveScalars (K := K) n d J counts))) K),
          eval ((Module.finBasis K _).equivFun
            (fullScalarFiberCoordinates (fullRestrictCounts hcounts p)).1) P₀ ≠ 0 ∧
          ∀ a', eval ((Module.finBasis K _).equivFun a') P₀ ≠ 0 →
            let p' := fullCountScalarFiberLinear hcounts (a',p)
            eval ((Module.finBasis K _).equivFun p') D ≠ 0 ∧
            Good (fullRestrictCounts hcounts p') ∧
            BaseC4GrowthProperty (by omega : 1 ≤ d) R (scalarReserveCount d n)
              (preparedBaseProjection (fullRestrictCounts hcounts p')) ∧
            StrictModel (fun i => outerVectorEquiv.symm (p'.2.2 i)) d (G*(n : ℝ)^d) ∧
            ChildFlagCondition (quotientMultiplication (fun i => outerVectorEquiv.symm (p'.2.2 i)) d)
              (outerScalarDeficit (fun i => outerVectorEquiv.symm (p'.2.2 i))) (C*(n : ℝ)^d)
              (coefficientCoordinates (fun i => p'.2.1.1 (Sum.inl i))) := by
  obtain ⟨G,C,hG,hC,hselect⟩ := exact_counts_prepared_restricted_certified_fiber (K := K) (u := u)
    hd hk hh hhpos upper a f e ha hc hδ hreserve
  have hgrowth := eventually_counted_base_c4_growth (K := K)
    hd hhpos hb R hP hratio upper a f e hc
  refine ⟨G,C,hG,hC,?_⟩
  filter_upwards [hselect,hgrowth] with n hn hgrowth
  intro J counts counts' O hO hcounts
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts' O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  intro Good A D hA hGood hD
  obtain ⟨B,hB,hBgrowth⟩ := prepared_base_growth_open (u := u) (counts := counts)
    (by omega : 1 ≤ d) hO R hgrowth
  obtain ⟨v,hv⟩ := finite_basis_principal_intersection
    (V := FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O)
    ![A,B] (by
      intro i
      fin_cases i
      · exact hA
      · exact hB)
  have hAB : ∃ v : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O,
      eval ((Module.finBasis K _).equivFun v) (A*B) ≠ 0 :=
    ⟨v,by simpa [map_mul] using mul_ne_zero (hv 0) (hv 1)⟩
  have hABgood : ∀ v : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O,
      eval ((Module.finBasis K _).equivFun v) (A*B) ≠ 0 →
      Good v ∧ BaseC4GrowthProperty (by omega : 1 ≤ d) R (scalarReserveCount d n)
        (preparedBaseProjection v) := by
    intro v hv
    have hboth := mul_ne_zero_iff.mp (show eval ((Module.finBasis K _).equivFun v) A *
        eval ((Module.finBasis K _).equivFun v) B ≠ 0 by simpa only [map_mul] using hv)
    exact ⟨hGood v hboth.1,hBgrowth v hboth.2⟩
  obtain ⟨p,P₀,hP₀,hfiber⟩ := hn J counts counts' O hO hcounts
    (fun v => Good v ∧ BaseC4GrowthProperty (by omega : 1 ≤ d) R (scalarReserveCount d n)
      (preparedBaseProjection v)) (A*B) D hAB hABgood hD
  refine ⟨p,P₀,hP₀,?_⟩
  intro a' ha'
  obtain ⟨hD',hgood,hmodel,hchild⟩ := hfiber a' ha'
  exact ⟨hD',hgood.1,hgood.2,hmodel,hchild⟩

end Froberg.PreparedParameters
