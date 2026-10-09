module

public import Froberg.RestoredScalarFiber
public import Froberg.VectorModelCoordinates
public import Froberg.CountedJointSelection

@[expose] public section

/-! Independent coordinates for the outer family, base scalar family,
and remaining restored parameters. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial VectorMultiplicationCoordinates
variable {K : Type} [Field K] [Infinite K] {h m d q f : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

abbrev RestoredJointRest (m d : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ)
    (O : ℕ → Submodule K (Poly K h)) :=
  (Fin (finrank K (Forms K h d)) → Forms K h d) ×
    (PositiveScalars (K := K) m d J counts ×
      ((j : J) → Fin (counts j.val) → biformImage (O j.val) (Forms K m (d-j.val))))

def restoredJointCoordinates : RestoredOuterSpace m d q f J counts O ≃ₗ[K]
    (Fin f → Rows K h m (d-1)) × ((Fin q → Forms K m d) × RestoredJointRest m d J counts O) where
  toFun p := (fun i => PreparedTarget.outerVectorEquiv.symm (p.2 i),
    (fun i => p.1.1.1 (Sum.inl i),(p.1.2,((scalarFiberCoordinates p.1.1).1,p.1.1.2))))
  invFun x := ((scalarFiberCoordinates.symm (x.2.2.2.1,(x.2.1,x.2.2.2.2)),x.2.2.1),
    fun i => PreparedTarget.outerVectorEquiv (x.1 i))
  left_inv p := by
    apply Prod.ext
    · apply Prod.ext
      · exact scalarFiberCoordinates.symm_apply_apply p.1.1
      · rfl
    · funext i
      exact LinearEquiv.apply_symm_apply _ _
  right_inv x := by
    rcases x with ⟨g,Q,U,a,E⟩
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
      exact map_smul (PreparedTarget.outerVectorEquiv (K := K) (h := h) (m := m) (d := d)).symm a (p.2 i)
    · rfl

theorem finite_restoredJointRest (hO : ∀ j∈J,O j≤Forms K h j) :
    Module.Finite K (RestoredJointRest m d J counts O) := by
  letI : Module.Finite K (Space m d 0 J counts O) := finite_space hO
  let pr : RestoredOuterSpace m d 0 0 J counts O →ₗ[K] RestoredJointRest m d J counts O :=
    (LinearMap.snd K _ _).comp ((LinearMap.snd K _ _).comp restoredJointCoordinates.toLinearMap)
  apply Module.Finite.of_surjective pr
  intro p
  refine ⟨restoredJointCoordinates.symm (0,0,p),?_⟩
  change (restoredJointCoordinates (restoredJointCoordinates.symm (0,0,p))).2.2=p
  rw [LinearEquiv.apply_symm_apply]

def restoredJointFromCoordinates (hO : ∀ j∈J,O j≤Forms K h j) :
    ((VectorParameters.Index h m (d-1) f ⊕
      (CoefficientIndex m d q ⊕ Fin (finrank K (RestoredJointRest m d J counts O)))) → K) →ₗ[K]
        RestoredOuterSpace m d q f J counts O := by
  letI : Module.Finite K (RestoredJointRest m d J counts O) := finite_restoredJointRest hO
  let I := VectorParameters.Index h m (d-1) f ⊕
    (CoefficientIndex m d q ⊕ Fin (finrank K (RestoredJointRest m d J counts O)))
  let g : (I → K) →ₗ[K] (Fin f → Rows K h m (d-1)) :=
    VectorParameters.generatorsEquiv.toLinearMap.comp (LinearMap.funLeft K K Sum.inl)
  let Q : (I → K) →ₗ[K] (Fin q → Forms K m d) :=
    coefficientCoordinates.symm.toLinearMap.comp (LinearMap.funLeft K K (Sum.inr ∘ Sum.inl))
  let R : (I → K) →ₗ[K] RestoredJointRest m d J counts O :=
    (Module.finBasis K (RestoredJointRest m d J counts O)).equivFun.symm.toLinearMap.comp
    (LinearMap.funLeft K K (Sum.inr ∘ Sum.inr))
  exact restoredJointCoordinates.symm.toLinearMap.comp (g.prod (Q.prod R))

theorem restoredJointFromCoordinates_eval (hO : ∀ j∈J,O j≤Forms K h j)
    (pF : VectorParameters.Index h m (d-1) f → K) (pQ : CoefficientIndex m d q → K)
    (pR : Fin (finrank K (RestoredJointRest m d J counts O)) → K) :
    letI : Module.Finite K (RestoredJointRest m d J counts O) := finite_restoredJointRest hO
    restoredJointCoordinates (restoredJointFromCoordinates hO (Sum.elim pF (Sum.elim pQ pR)))=
      (VectorParameters.generators pF,coefficientForms K m d q pQ,
        (Module.finBasis K (RestoredJointRest m d J counts O)).equivFun.symm pR) := by
  letI : Module.Finite K (RestoredJointRest m d J counts O) := finite_restoredJointRest hO
  change restoredJointCoordinates (restoredJointCoordinates.symm _)=_
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem restoredJointFromCoordinates_surjective (hO : ∀ j∈J,O j≤Forms K h j) :
    Function.Surjective (restoredJointFromCoordinates (m := m) (d := d) (q := q)
      (f := f) (counts := counts) hO) := by
  letI : Module.Finite K (RestoredJointRest m d J counts O) := finite_restoredJointRest hO
  intro p
  let x := restoredJointCoordinates p
  refine ⟨Sum.elim (VectorParameters.coordinates x.1)
    (Sum.elim (coefficientCoordinates x.2.1) ((Module.finBasis K _).equivFun x.2.2)),?_⟩
  apply restoredJointCoordinates.injective
  rw [restoredJointFromCoordinates_eval]
  have hQ : coefficientForms K m d q (coefficientCoordinates x.2.1)=x.2.1 :=
    coefficientCoordinates.symm_apply_apply x.2.1
  simp only [VectorParameters.generators_coordinates,hQ,LinearEquiv.symm_apply_apply]
  rfl

end Froberg.PreparedParameters
