module

public import Froberg.PreparedJointCoordinates

@[expose] public section

/-! The exact-count generic child flag and thin bottom quotient can be
chosen inside any nonempty open of the full actual prepared family. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedParameters
open Froberg Filter Module MvPolynomial VectorMultiplicationCoordinates VectorExpansionOpen
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

theorem exact_counts_prepared_joint {d k h lo u : ℕ}
    (hd : 3≤d) (hk : 0<k) (hh : h=k*centralHalfBinomial d) (hhpos : 0<h)
    (upper : Bool) (a f e : ℕ → ℕ) (ha : ∀ n,a n ≤ n)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0<δ)
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) :
    ∃ G C : ℝ,0<G ∧ 0<C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Finset ℕ) (counts : ℕ → ℕ) (O : ℕ → Submodule K (Poly K h))
        (hO : ∀ j∈J,O j≤Forms K h j),
      letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O) :=
        FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
      ∀ D : MvPolynomial (Fin (finrank K
        (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O))) K,
        (∃ p : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O,
          eval ((Module.finBasis K _).equivFun p) D≠0) →
        ∃ p : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O,
          eval ((Module.finBasis K _).equivFun p) D≠0 ∧
          StrictModel (fun i => PreparedTarget.outerVectorEquiv.symm (p.2.2 i)) d (G*(n : ℝ)^d) ∧
          ChildFlagCondition (quotientMultiplication (fun i => PreparedTarget.outerVectorEquiv.symm (p.2.2 i)) d)
            (outerScalarDeficit (fun i => PreparedTarget.outerVectorEquiv.symm (p.2.2 i))) (C*(n : ℝ)^d)
            (coefficientCoordinates (fun i => p.2.1.1 (Sum.inl i))) := by
  obtain ⟨G,C,hG,hC,hjoint⟩ := exact_count_generic_flag_joint (K := K) (b := 0)
    hd hk hh hhpos upper a f e ha hc hδ hreserve
  simp only [Nat.add_zero] at hjoint
  refine ⟨G,C,hG,hC,?_⟩
  filter_upwards [hjoint] with n hn
  intro J counts O hO
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  letI : Module.Finite K (JointRest n d (upperCount n d) (f n) u J counts O) := finite_jointRest hO
  intro D hD
  let L := preparedJointFromCoordinates (m := n) (d := d) (q := upperCount n d) (f := f n) (u := u) (counts := counts) hO
  let coord := (Module.finBasis K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O)).equivFun
  let P := substituteAffine (coord.toLinearMap.comp L) 0 D
  have heval (x) : eval x P=eval (coord (L x)) D := by
    rw [show P=substituteAffine (coord.toLinearMap.comp L) 0 D from rfl,eval_substituteAffine,add_zero]
    rfl
  have hP : ∃ x,eval x P≠0 := by
    obtain ⟨p,hp⟩ := hD
    obtain ⟨x,hx⟩ := preparedJointFromCoordinates_surjective hO p
    exact ⟨x,by rw [heval,hx];exact hp⟩
  obtain ⟨pF,pQ,pR,hp,hmodel,hchild⟩ := hn _ P hP
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

end Froberg.PreparedParameters
