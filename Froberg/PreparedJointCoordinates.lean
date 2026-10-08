import Froberg.PreparedScalarFiberAt
import Froberg.VectorModelCoordinates
import Froberg.CountedJointSelection

/-! Independent monomial coordinates for the outer F family, scalar Q
family, and remaining actual prepared parameters. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial VectorMultiplicationCoordinates
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

abbrev JointRest (m d q f u : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ)
    (O : ℕ → Submodule K (Poly K h)) :=
  PreparedTarget.OuterSpace K (Fin h) m d u ×
    (PositiveScalars (K := K) m d J counts ×
      ((j : J) → Fin (counts j.val) → biformImage (O j.val) (Forms K m (d-j.val))))

def preparedJointCoordinates :
    FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O ≃ₗ[K]
      (Fin f → Rows K h m (d-1)) × ((Fin q → Forms K m d) × JointRest m d q f u J counts O) where
  toFun p := (fun i => PreparedTarget.outerVectorEquiv.symm (p.2.2 i),
    (fun i => p.2.1.1 (Sum.inl i),(p.1,((scalarFiberCoordinates p.2.1).1,p.2.1.2))))
  invFun x := (x.2.2.1,(scalarFiberCoordinates.symm (x.2.2.2.1,(x.2.1,x.2.2.2.2)),
    fun i => PreparedTarget.outerVectorEquiv (x.1 i)))
  left_inv p := by
    apply Prod.ext
    · rfl
    apply Prod.ext
    · exact scalarFiberCoordinates.symm_apply_apply p.2.1
    · funext i
      exact LinearEquiv.apply_symm_apply _ _
  right_inv x := by
    rcases x with ⟨g,Q,P,a,E⟩
    apply Prod.ext
    · funext i
      exact LinearEquiv.symm_apply_apply _ _
    apply Prod.ext
    · rfl
    apply Prod.ext
    · rfl
    apply Prod.ext
    · funext i
      exact scalarFiberCoordinates_symm_positive a (Q,E) i
    · rfl
  map_add' p p' := by
    apply Prod.ext
    · funext i
      exact map_add _ _ _
    · rfl
  map_smul' a p := by
    apply Prod.ext
    · funext i
      exact map_smul (PreparedTarget.outerVectorEquiv (K := K) (h := h) (m := m) (d := d)).symm a (p.2.2 i)
    · rfl

theorem finite_jointRest (hO : ∀ j∈J,O j≤Forms K h j) :
    Module.Finite K (JointRest m d q f u J counts O) := by
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  let pr : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O →ₗ[K]
      JointRest m d q f u J counts O :=
    (LinearMap.snd K _ _).comp ((LinearMap.snd K _ _).comp preparedJointCoordinates.toLinearMap)
  apply Module.Finite.of_surjective pr
  intro p
  refine ⟨preparedJointCoordinates.symm (0,0,p),?_⟩
  change (preparedJointCoordinates (preparedJointCoordinates.symm (0,0,p))).2.2=p
  rw [LinearEquiv.apply_symm_apply]

def preparedJointFromCoordinates (hO : ∀ j∈J,O j≤Forms K h j) :
    ((VectorParameters.Index h m (d-1) f ⊕
      (CoefficientIndex m d q ⊕ Fin (finrank K (JointRest m d q f u J counts O)))) → K) →ₗ[K]
        FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O := by
  letI : Module.Finite K (JointRest m d q f u J counts O) := finite_jointRest hO
  let I := VectorParameters.Index h m (d-1) f ⊕
    (CoefficientIndex m d q ⊕ Fin (finrank K (JointRest m d q f u J counts O)))
  let g : (I → K) →ₗ[K] (Fin f → Rows K h m (d-1)) :=
    VectorParameters.generatorsEquiv.toLinearMap.comp (LinearMap.funLeft K K Sum.inl)
  let Q : (I → K) →ₗ[K] (Fin q → Forms K m d) :=
    coefficientCoordinates.symm.toLinearMap.comp (LinearMap.funLeft K K (Sum.inr ∘ Sum.inl))
  let R : (I → K) →ₗ[K] JointRest m d q f u J counts O :=
    (Module.finBasis K (JointRest m d q f u J counts O)).equivFun.symm.toLinearMap.comp
    (LinearMap.funLeft K K (Sum.inr ∘ Sum.inr))
  exact preparedJointCoordinates.symm.toLinearMap.comp (g.prod (Q.prod R))

theorem preparedJointFromCoordinates_eval (hO : ∀ j∈J,O j≤Forms K h j)
    (pF : VectorParameters.Index h m (d-1) f → K) (pQ : CoefficientIndex m d q → K)
    (pR : Fin (finrank K (JointRest m d q f u J counts O)) → K) :
    letI : Module.Finite K (JointRest m d q f u J counts O) := finite_jointRest hO
    preparedJointCoordinates (preparedJointFromCoordinates hO (Sum.elim pF (Sum.elim pQ pR)))=
      (VectorParameters.generators pF,coefficientForms K m d q pQ,
        (Module.finBasis K (JointRest m d q f u J counts O)).equivFun.symm pR) := by
  letI : Module.Finite K (JointRest m d q f u J counts O) := finite_jointRest hO
  change preparedJointCoordinates (preparedJointCoordinates.symm _)=_
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem preparedJointFromCoordinates_surjective (hO : ∀ j∈J,O j≤Forms K h j) :
    Function.Surjective (preparedJointFromCoordinates (m := m) (d := d) (q := q)
      (f := f) (u := u) (counts := counts) hO) := by
  letI : Module.Finite K (JointRest m d q f u J counts O) := finite_jointRest hO
  intro p
  let x := preparedJointCoordinates p
  refine ⟨Sum.elim (VectorParameters.coordinates x.1)
    (Sum.elim (coefficientCoordinates x.2.1) ((Module.finBasis K _).equivFun x.2.2)),?_⟩
  apply preparedJointCoordinates.injective
  rw [preparedJointFromCoordinates_eval]
  have hQ : coefficientForms K m d q (coefficientCoordinates x.2.1)=x.2.1 :=
    coefficientCoordinates.symm_apply_apply x.2.1
  simp only [VectorParameters.generators_coordinates,hQ,LinearEquiv.symm_apply_apply]
  rfl

end Froberg.PreparedParameters
