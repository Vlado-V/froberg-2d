import Froberg.PreparedCountScalarFiber
import Froberg.PreparedJointSelection
import Froberg.FiniteBasisPrincipalIntersection

/-! Select enlarged prepared parameters while imposing the final
certificates on their base restriction, then freeze all temporary slots. -/
noncomputable section
set_option maxHeartbeats 150000
namespace Froberg.PreparedParameters
open Froberg PreparedTarget Filter Module MvPolynomial VectorExpansionOpen
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

theorem prepared_count_joint_scalar_fiber_at {h m d q f u : ℕ}
    {J : Finset ℕ} {c c' : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}
    (hc : ∀ j ∈ J, c j ≤ c' j) (hO : ∀ j ∈ J, O j ≤ Forms K h j) (G C : ℝ) :
    letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J c' O) :=
      FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
    ∀ (D : MvPolynomial (Fin (finrank K
      (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J c' O))) K)
      (p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J c' O),
      eval ((Module.finBasis K _).equivFun p) D ≠ 0 →
      StrictModel (fun i => outerVectorEquiv.symm (p.2.2 i)) d G →
      ChildFlagCondition (quotientMultiplication (fun i => outerVectorEquiv.symm (p.2.2 i)) d)
        (outerScalarDeficit (fun i => outerVectorEquiv.symm (p.2.2 i))) C
        (coefficientCoordinates (fun i => p.2.1.1 (Sum.inl i))) →
      ∃ P₀ : MvPolynomial (Fin (finrank K (PositiveScalars (K := K) m d J c))) K,
        eval ((Module.finBasis K _).equivFun
          (fullScalarFiberCoordinates (fullRestrictCounts hc p)).1) P₀ ≠ 0 ∧
        ∀ a, eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0 →
          let p' := fullCountScalarFiberLinear hc (a,p)
          eval ((Module.finBasis K _).equivFun p') D ≠ 0 ∧
          StrictModel (fun i => outerVectorEquiv.symm (p'.2.2 i)) d G ∧
          ChildFlagCondition (quotientMultiplication (fun i => outerVectorEquiv.symm (p'.2.2 i)) d)
            (outerScalarDeficit (fun i => outerVectorEquiv.symm (p'.2.2 i))) C
            (coefficientCoordinates (fun i => p'.2.1.1 (Sum.inl i))) := by
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J c' O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  intro D p hp hmodel hchild
  obtain ⟨P₀,hP₀,hgood⟩ := principal_open_full_count_scalar_fiber_at hc hO D p hp
  exact ⟨P₀,hP₀,fun a ha => ⟨hgood a ha,hmodel,hchild⟩⟩

/-- The temporary extra columns remain fixed, while the final base family
keeps its supplied certificate and the enlarged family keeps its own open. -/
theorem exact_counts_prepared_restricted_certified_fiber {d k h lo u : ℕ}
    (hd : 3 ≤ d) (hk : 0 < k) (hh : h = k*centralHalfBinomial d) (hhpos : 0 < h)
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
            StrictModel (fun i => outerVectorEquiv.symm (p'.2.2 i)) d (G*(n : ℝ)^d) ∧
            ChildFlagCondition (quotientMultiplication (fun i => outerVectorEquiv.symm (p'.2.2 i)) d)
              (outerScalarDeficit (fun i => outerVectorEquiv.symm (p'.2.2 i))) (C*(n : ℝ)^d)
              (coefficientCoordinates (fun i => p'.2.1.1 (Sum.inl i))) := by
  obtain ⟨G,C,hG,hC,hjoint⟩ := exact_counts_prepared_joint (K := K) (u := u)
    hd hk hh hhpos upper a f e ha hc hδ hreserve
  refine ⟨G,C,hG,hC,?_⟩
  filter_upwards [hjoint] with n hn
  intro J counts counts' O hO hcounts
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts' O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  intro Good A D hA hGood hD
  obtain ⟨B,hB,hBgood⟩ := principal_open_linear_pullback (fullRestrictCounts hcounts)
    (fullRestrictCounts_surjective hcounts) A hA Good hGood
  obtain ⟨v,hv⟩ := finite_basis_principal_intersection
    (V := FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts' O)
    ![B,D] (by
      intro i
      fin_cases i
      · exact hB
      · exact hD)
  have hBD : ∃ v : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts' O,
      eval ((Module.finBasis K _).equivFun v) (B*D) ≠ 0 :=
    ⟨v,by simpa [map_mul] using mul_ne_zero (hv 0) (hv 1)⟩
  obtain ⟨p,hp,hmodel,hchild⟩ := hn J counts' O hO (B*D) hBD
  obtain ⟨P₀,hP₀,hfiber⟩ := prepared_count_joint_scalar_fiber_at hcounts hO
    (G*(n : ℝ)^d) (C*(n : ℝ)^d) (B*D) p hp hmodel hchild
  refine ⟨p,P₀,hP₀,?_⟩
  intro a' ha'
  obtain ⟨hBD',hm,hchild'⟩ := hfiber a' ha'
  have hboth := mul_ne_zero_iff.mp (show
      eval ((Module.finBasis K _).equivFun (fullCountScalarFiberLinear hcounts (a',p))) B *
      eval ((Module.finBasis K _).equivFun (fullCountScalarFiberLinear hcounts (a',p))) D ≠ 0 by
        simpa only [map_mul] using hBD')
  exact ⟨hboth.2,hBgood _ hboth.1,hm,hchild'⟩

end Froberg.PreparedParameters
