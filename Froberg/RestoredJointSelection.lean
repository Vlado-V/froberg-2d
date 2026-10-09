module

public import Froberg.RestoredJointCoordinates

@[expose] public section

/-! The exact-count generic child flag and thin bottom quotient can be
chosen inside any nonempty open of the full actual restored family. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedParameters
open Froberg Filter Module MvPolynomial VectorMultiplicationCoordinates VectorExpansionOpen
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

theorem exact_counts_restored_joint {d k h lo : ℕ}
    (hd : 3≤d) (hk : 0<k) (hh : h=k*centralHalfBinomial d) (hhpos : 0<h)
    (upper : Bool) (a f e : ℕ → ℕ) (ha : ∀ n,a n ≤ n)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0<δ)
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) :
    ∃ G C : ℝ,0<G ∧ 0<C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Finset ℕ) (counts : ℕ → ℕ) (O : ℕ → Submodule K (Poly K h))
        (hO : ∀ j∈J,O j≤Forms K h j),
      letI : Module.Finite K (Space n d (upperCount n d) J counts O) := finite_space hO
      ∀ D : MvPolynomial (Fin (finrank K
        (RestoredOuterSpace n d (upperCount n d) (f n) J counts O))) K,
        (∃ p : RestoredOuterSpace n d (upperCount n d) (f n) J counts O,
          eval ((Module.finBasis K _).equivFun p) D≠0) →
        ∃ p : RestoredOuterSpace n d (upperCount n d) (f n) J counts O,
          eval ((Module.finBasis K _).equivFun p) D≠0 ∧
          StrictModel (fun i => PreparedTarget.outerVectorEquiv.symm (p.2 i)) d (G*(n : ℝ)^d) ∧
          ChildFlagCondition (quotientMultiplication (fun i => PreparedTarget.outerVectorEquiv.symm (p.2 i)) d)
            (outerScalarDeficit (fun i => PreparedTarget.outerVectorEquiv.symm (p.2 i))) (C*(n : ℝ)^d)
            (coefficientCoordinates (fun i => p.1.1.1 (Sum.inl i))) := by
  obtain ⟨G,C,hG,hC,hjoint⟩ := exact_count_generic_flag_joint (K := K) (b := 0)
    hd hk hh hhpos upper a f e ha hc hδ hreserve
  simp only [Nat.add_zero] at hjoint
  refine ⟨G,C,hG,hC,?_⟩
  filter_upwards [hjoint] with n hn
  intro J counts O hO
  letI : Module.Finite K (Space n d (upperCount n d) J counts O) := finite_space hO
  letI : Module.Finite K (RestoredJointRest n d J counts O) := finite_restoredJointRest hO
  intro D hD
  let L := restoredJointFromCoordinates (m := n) (d := d) (q := upperCount n d) (f := f n) (counts := counts) hO
  let coord := (Module.finBasis K (RestoredOuterSpace n d (upperCount n d) (f n) J counts O)).equivFun
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


/-- Once the generic child flag and outer model have been chosen in a full
open, every point of a nonempty positive-scalar fiber keeps both choices. -/
theorem restored_joint_positive_scalar_fiber_at {h m d q f : ℕ}
    {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}
    (hO : ∀ j∈J,O j≤Forms K h j) (G C : ℝ) :
    letI : Module.Finite K (Space m d q J counts O) := finite_space hO
    ∀ (D : MvPolynomial (Fin (finrank K (RestoredOuterSpace m d q f J counts O))) K)
      (p : RestoredOuterSpace m d q f J counts O),
      eval ((Module.finBasis K _).equivFun p) D≠0 →
      StrictModel (fun i => PreparedTarget.outerVectorEquiv.symm (p.2 i)) d G →
      ChildFlagCondition (quotientMultiplication (fun i => PreparedTarget.outerVectorEquiv.symm (p.2 i)) d)
        (outerScalarDeficit (fun i => PreparedTarget.outerVectorEquiv.symm (p.2 i))) C
        (coefficientCoordinates (fun i => p.1.1.1 (Sum.inl i))) →
      ∃ E : MvPolynomial (Fin (finrank K (PositiveScalars (K := K) m d J counts))) K,
        eval ((Module.finBasis K _).equivFun (restoredScalarFiberCoordinates p).1) E≠0 ∧
        ∀ a,eval ((Module.finBasis K _).equivFun a) E≠0 →
          let p' := restoredScalarFiberCoordinates.symm (a,(restoredScalarFiberCoordinates p).2)
          eval ((Module.finBasis K _).equivFun p') D≠0 ∧
          StrictModel (fun i => PreparedTarget.outerVectorEquiv.symm (p'.2 i)) d G ∧
          ChildFlagCondition (quotientMultiplication (fun i => PreparedTarget.outerVectorEquiv.symm (p'.2 i)) d)
            (outerScalarDeficit (fun i => PreparedTarget.outerVectorEquiv.symm (p'.2 i))) C
            (coefficientCoordinates (fun i => p'.1.1.1 (Sum.inl i))) := by
  letI : Module.Finite K (Space m d q J counts O) := finite_space hO
  intro D p hp hmodel hchild
  obtain ⟨E,hE,hgood⟩ := principal_open_restored_scalar_fiber_at hO D p hp
  exact ⟨E,hE,fun a ha => ⟨hgood a ha,hmodel,hchild⟩⟩

end Froberg.PreparedParameters
