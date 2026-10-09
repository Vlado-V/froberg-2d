module

public import Froberg.PreparedBiformCompatibility
public import Froberg.FullPreparedFibers
public import Froberg.FreezeParameters

@[expose] public section

/-! The positive-row scalar coefficients form an actual independent
factor of the shared prepared parameter space. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

abbrev PositiveScalars (m d : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ) :=
  Fin (Fintype.card (ProductRows.LayerLabel J counts)) → Forms K m d

abbrev ScalarFiberRest (m d q : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ)
    (O : ℕ → Submodule K (Poly K h)) :=
  (Fin q → Forms K m d) ×
    ((j : J) → Fin (counts j.val) → biformImage (O j.val) (Forms K m (d-j.val)))

def scalarFiberCoordinates : Space m d q J counts O ≃ₗ[K]
    PositiveScalars (K := K) m d J counts × ScalarFiberRest m d q J counts O where
  toFun p := ((fun i => p.1 (Sum.inr ((Fintype.equivFin _).symm i))),
    (fun i => p.1 (Sum.inl i),p.2))
  invFun p := (Sum.elim p.2.1 (fun i => p.1 ((Fintype.equivFin _) i)),p.2.2)
  left_inv p := by
    apply Prod.ext
    · funext i
      cases i <;> simp
    · rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      simp
    · rfl
  map_add' p p' := rfl
  map_smul' c p := rfl

@[simp] theorem scalarFiberCoordinates_symm_base
    (a : PositiveScalars (K := K) m d J counts) (p : ScalarFiberRest m d q J counts O) (i : Fin q) :
    (scalarFiberCoordinates.symm (a,p)).1 (Sum.inl i)=p.1 i := rfl

@[simp] theorem scalarFiberCoordinates_symm_positive
    (a : PositiveScalars (K := K) m d J counts) (p : ScalarFiberRest m d q J counts O)
    (i : Fin (Fintype.card (ProductRows.LayerLabel J counts))) :
    (scalarFiberCoordinates.symm (a,p)).1 (Sum.inr ((Fintype.equivFin _).symm i))=a i := by
  simp [scalarFiberCoordinates]

@[simp] theorem scalarFiberCoordinates_symm_high
    (a : PositiveScalars (K := K) m d J counts) (p : ScalarFiberRest m d q J counts O) :
    (scalarFiberCoordinates.symm (a,p)).2=p.2 := rfl

abbrev FullScalarFiberRest (m d q f u : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ)
    (O : ℕ → Submodule K (Poly K h)) :=
  PreparedTarget.OuterSpace K (Fin h) m d u ×
    (ScalarFiberRest m d q J counts O × PreparedTarget.OuterSpace K (Fin h) m d f)

def fullScalarFiberCoordinates :
    FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O ≃ₗ[K]
      PositiveScalars (K := K) m d J counts × FullScalarFiberRest m d q f u J counts O where
  toFun p := ((scalarFiberCoordinates p.2.1).1,(p.1,((scalarFiberCoordinates p.2.1).2,p.2.2)))
  invFun p := (p.2.1,(scalarFiberCoordinates.symm (p.1,p.2.2.1),p.2.2.2))
  left_inv p := by
    apply Prod.ext
    · rfl
    apply Prod.ext
    · exact scalarFiberCoordinates.symm_apply_apply p.2.1
    · rfl
  right_inv p := by
    rcases p with ⟨a,P,rest,F⟩
    change ((scalarFiberCoordinates (scalarFiberCoordinates.symm (a,rest))).1,
      P,(scalarFiberCoordinates (scalarFiberCoordinates.symm (a,rest))).2,F)=(a,P,rest,F)
    rw [LinearEquiv.apply_symm_apply]
  map_add' p p' := rfl
  map_smul' c p := rfl

theorem finite_fullScalarFiberRest (hO : ∀ j∈J,O j≤Forms K h j) :
    Module.Finite K (FullScalarFiberRest m d q f u J counts O) := by
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  let pr : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O →ₗ[K]
      FullScalarFiberRest m d q f u J counts O :=
    (LinearMap.snd K _ _).comp fullScalarFiberCoordinates.toLinearMap
  apply Module.Finite.of_surjective pr
  intro p
  refine ⟨fullScalarFiberCoordinates.symm (0,p),?_⟩
  change (fullScalarFiberCoordinates (fullScalarFiberCoordinates.symm (0,p))).2=p
  rw [LinearEquiv.apply_symm_apply]

theorem principal_open_positive_scalar_fiber (hO : ∀ j∈J,O j≤Forms K h j) :
    letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
      FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
    ∀ D : MvPolynomial (Fin (finrank K
      (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O))) K,
      (∃ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O,
        eval ((Module.finBasis K _).equivFun p) D≠0) →
      ∃ rest : FullScalarFiberRest m d q f u J counts O,
        ∃ E : MvPolynomial (Fin (finrank K (PositiveScalars (K := K) m d J counts))) K,
          (∃ a : PositiveScalars (K := K) m d J counts,
            eval ((Module.finBasis K _).equivFun a) E≠0) ∧
          ∀ a,eval ((Module.finBasis K _).equivFun a) E≠0 →
            eval ((Module.finBasis K _).equivFun (fullScalarFiberCoordinates.symm (a,rest))) D≠0 := by
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  intro D hD
  exact principal_open_freeze_parameters fullScalarFiberCoordinates.symm.toLinearMap
    fullScalarFiberCoordinates.symm.surjective D hD
    (fun p => eval ((Module.finBasis K _).equivFun p) D≠0) (fun p hp => hp)

end Froberg.PreparedParameters
