module

public import Froberg.RestoredCountScalarFiber
public import Froberg.RestoredJointSelection
public import Froberg.FiniteBasisPrincipalIntersection

@[expose] public section

/-! Select enlarged restored parameters while imposing the final
certificates on their base restriction, then freeze all temporary slots. -/
noncomputable section
set_option maxHeartbeats 150000
namespace Froberg.PreparedParameters
open Froberg PreparedTarget Filter Module MvPolynomial VectorExpansionOpen
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

theorem restored_count_joint_scalar_fiber_at {h m d q f : ℕ}
    {J : Finset ℕ} {c c' : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}
    (hc : ∀ j ∈ J, c j ≤ c' j) (hO : ∀ j ∈ J, O j ≤ Forms K h j) (G C : ℝ) :
    letI : Module.Finite K (Space m d q J c' O) := finite_space hO
    ∀ (D : MvPolynomial (Fin (finrank K
      (RestoredOuterSpace m d q f J c' O))) K)
      (p : RestoredOuterSpace m d q f J c' O),
      eval ((Module.finBasis K _).equivFun p) D ≠ 0 →
      StrictModel (fun i => outerVectorEquiv.symm (p.2 i)) d G →
      ChildFlagCondition (quotientMultiplication (fun i => outerVectorEquiv.symm (p.2 i)) d)
        (outerScalarDeficit (fun i => outerVectorEquiv.symm (p.2 i))) C
        (coefficientCoordinates (fun i => p.1.1.1 (Sum.inl i))) →
      ∃ P₀ : MvPolynomial (Fin (finrank K (PositiveScalars (K := K) m d J c))) K,
        eval ((Module.finBasis K _).equivFun
          (restoredScalarFiberCoordinates (restoredRestrictCounts hc p)).1) P₀ ≠ 0 ∧
        ∀ a, eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0 →
          let p' := restoredCountScalarFiberLinear hc (a,p)
          eval ((Module.finBasis K _).equivFun p') D ≠ 0 ∧
          StrictModel (fun i => outerVectorEquiv.symm (p'.2 i)) d G ∧
          ChildFlagCondition (quotientMultiplication (fun i => outerVectorEquiv.symm (p'.2 i)) d)
            (outerScalarDeficit (fun i => outerVectorEquiv.symm (p'.2 i))) C
            (coefficientCoordinates (fun i => p'.1.1.1 (Sum.inl i))) := by
  letI : Module.Finite K (Space m d q J c' O) := finite_space hO
  intro D p hp hmodel hchild
  obtain ⟨P₀,hP₀,hgood⟩ := principal_open_restored_count_scalar_fiber_at hc hO D p hp
  exact ⟨P₀,hP₀,fun a ha => ⟨hgood a ha,hmodel,hchild⟩⟩

/-- The temporary extra columns remain fixed, while the final base family
keeps its supplied certificate and the enlarged family keeps its own open. -/
theorem exact_counts_restored_restricted_certified_fiber {d k h lo : ℕ}
    (hd : 3 ≤ d) (hk : 0 < k) (hh : h = k*centralHalfBinomial d) (hhpos : 0 < h)
    (upper : Bool) (a f e : ℕ → ℕ) (ha : ∀ n, a n ≤ n)
    (hc : ∀ᶠ n in atTop, ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0 < δ)
    (hreserve : ∀ᶠ n : ℕ in atTop, δ*(n : ℝ)^(2*d-2) < dimensionReserve d h n (f n)) :
    ∃ G C : ℝ, 0 < G ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Finset ℕ) (counts counts' : ℕ → ℕ) (O : ℕ → Submodule K (Poly K h))
        (hO : ∀ j ∈ J, O j ≤ Forms K h j) (hcounts : ∀ j ∈ J, counts j ≤ counts' j),
      letI : Module.Finite K (Space n d (upperCount n d) J counts O) := finite_space hO
      letI : Module.Finite K (Space n d (upperCount n d) J counts' O) := finite_space hO
      ∀ (Good : RestoredOuterSpace n d (upperCount n d) (f n) J counts O → Prop)
        (A : MvPolynomial (Fin (finrank K
          (RestoredOuterSpace n d (upperCount n d) (f n) J counts O))) K)
        (D : MvPolynomial (Fin (finrank K
          (RestoredOuterSpace n d (upperCount n d) (f n) J counts' O))) K),
        (∃ v : RestoredOuterSpace n d (upperCount n d) (f n) J counts O,
          eval ((Module.finBasis K _).equivFun v) A ≠ 0) →
        (∀ v : RestoredOuterSpace n d (upperCount n d) (f n) J counts O,
          eval ((Module.finBasis K _).equivFun v) A ≠ 0 → Good v) →
        (∃ v : RestoredOuterSpace n d (upperCount n d) (f n) J counts' O,
          eval ((Module.finBasis K _).equivFun v) D ≠ 0) →
        ∃ (p : RestoredOuterSpace n d (upperCount n d) (f n) J counts' O)
          (P₀ : MvPolynomial (Fin (finrank K (PositiveScalars (K := K) n d J counts))) K),
          eval ((Module.finBasis K _).equivFun
            (restoredScalarFiberCoordinates (restoredRestrictCounts hcounts p)).1) P₀ ≠ 0 ∧
          ∀ a', eval ((Module.finBasis K _).equivFun a') P₀ ≠ 0 →
            let p' := restoredCountScalarFiberLinear hcounts (a',p)
            eval ((Module.finBasis K _).equivFun p') D ≠ 0 ∧
            Good (restoredRestrictCounts hcounts p') ∧
            StrictModel (fun i => outerVectorEquiv.symm (p'.2 i)) d (G*(n : ℝ)^d) ∧
            ChildFlagCondition (quotientMultiplication (fun i => outerVectorEquiv.symm (p'.2 i)) d)
              (outerScalarDeficit (fun i => outerVectorEquiv.symm (p'.2 i))) (C*(n : ℝ)^d)
              (coefficientCoordinates (fun i => p'.1.1.1 (Sum.inl i))) := by
  obtain ⟨G,C,hG,hC,hjoint⟩ := exact_counts_restored_joint (K := K)
    hd hk hh hhpos upper a f e ha hc hδ hreserve
  refine ⟨G,C,hG,hC,?_⟩
  filter_upwards [hjoint] with n hn
  intro J counts counts' O hO hcounts
  letI : Module.Finite K (Space n d (upperCount n d) J counts O) := finite_space hO
  letI : Module.Finite K (Space n d (upperCount n d) J counts' O) := finite_space hO
  intro Good A D hA hGood hD
  obtain ⟨B,hB,hBgood⟩ := principal_open_linear_pullback (restoredRestrictCounts hcounts)
    (restoredRestrictCounts_surjective hcounts) A hA Good hGood
  obtain ⟨v,hv⟩ := finite_basis_principal_intersection
    (V := RestoredOuterSpace n d (upperCount n d) (f n) J counts' O)
    ![B,D] (by
      intro i
      fin_cases i
      · exact hB
      · exact hD)
  have hBD : ∃ v : RestoredOuterSpace n d (upperCount n d) (f n) J counts' O,
      eval ((Module.finBasis K _).equivFun v) (B*D) ≠ 0 :=
    ⟨v,by simpa [map_mul] using mul_ne_zero (hv 0) (hv 1)⟩
  obtain ⟨p,hp,hmodel,hchild⟩ := hn J counts' O hO (B*D) hBD
  obtain ⟨P₀,hP₀,hfiber⟩ := restored_count_joint_scalar_fiber_at hcounts hO
    (G*(n : ℝ)^d) (C*(n : ℝ)^d) (B*D) p hp hmodel hchild
  refine ⟨p,P₀,hP₀,?_⟩
  intro a' ha'
  obtain ⟨hBD',hm,hchild'⟩ := hfiber a' ha'
  have hboth := mul_ne_zero_iff.mp (show
      eval ((Module.finBasis K _).equivFun (restoredCountScalarFiberLinear hcounts (a',p))) B *
      eval ((Module.finBasis K _).equivFun (restoredCountScalarFiberLinear hcounts (a',p))) D ≠ 0 by
        simpa only [map_mul] using hBD')
  exact ⟨hboth.2,hBgood _ hboth.1,hm,hchild'⟩

end Froberg.PreparedParameters
