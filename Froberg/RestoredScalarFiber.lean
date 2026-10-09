module

public import Froberg.PreparedScalarFiberAt
public import Froberg.RestoredOuterOddOpen

@[expose] public section

/-! Positive scalar coefficients remain a free factor after pure even
restoration. Restricting a principal open through a good point freezes the
base family, all high terms, the pure tuple, and the outer odd family. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

abbrev RestoredScalarRest (m d q f : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ)
    (O : ℕ → Submodule K (Poly K h)) :=
  ScalarFiberRest m d q J counts O ×
    ((Fin (finrank K (Forms K h d)) → Forms K h d) ×
      PreparedTarget.OuterSpace K (Fin h) m d f)

def restoredScalarFiberCoordinates : RestoredOuterSpace m d q f J counts O ≃ₗ[K]
    PositiveScalars (K := K) m d J counts × RestoredScalarRest m d q f J counts O where
  toFun p := ((scalarFiberCoordinates p.1.1).1,((scalarFiberCoordinates p.1.1).2,p.1.2,p.2))
  invFun p := ((scalarFiberCoordinates.symm (p.1,p.2.1),p.2.2.1),p.2.2.2)
  left_inv p := by
    apply Prod.ext
    · apply Prod.ext
      · exact scalarFiberCoordinates.symm_apply_apply p.1.1
      · rfl
    · rfl
  right_inv p := by
    rcases p with ⟨a,rest,U,F⟩
    change ((scalarFiberCoordinates (scalarFiberCoordinates.symm (a,rest))).1,
      (scalarFiberCoordinates (scalarFiberCoordinates.symm (a,rest))).2,U,F)=(a,rest,U,F)
    rw [LinearEquiv.apply_symm_apply]
  map_add' p p' := rfl
  map_smul' c p := rfl

theorem finite_restoredScalarRest (hO : ∀ j∈J,O j≤Forms K h j) :
    Module.Finite K (RestoredScalarRest m d q f J counts O) := by
  letI : Module.Finite K (Space m d q J counts O) := finite_space hO
  let pr : RestoredOuterSpace m d q f J counts O →ₗ[K] RestoredScalarRest m d q f J counts O :=
    (LinearMap.snd K _ _).comp restoredScalarFiberCoordinates.toLinearMap
  apply Module.Finite.of_surjective pr
  intro p
  refine ⟨restoredScalarFiberCoordinates.symm (0,p),?_⟩
  change (restoredScalarFiberCoordinates (restoredScalarFiberCoordinates.symm (0,p))).2=p
  rw [LinearEquiv.apply_symm_apply]

@[simp] theorem restoredScalarFiber_base
    (a : PositiveScalars (K := K) m d J counts) (rest : RestoredScalarRest m d q f J counts O)
    (i : Fin q) :
    (restoredScalarFiberCoordinates.symm (a,rest)).1.1.1 (Sum.inl i)=rest.1.1 i := rfl

@[simp] theorem restoredScalarFiber_high
    (a : PositiveScalars (K := K) m d J counts) (rest : RestoredScalarRest m d q f J counts O) :
    (restoredScalarFiberCoordinates.symm (a,rest)).1.1.2=rest.1.2 := rfl

@[simp] theorem restoredScalarFiber_pure
    (a : PositiveScalars (K := K) m d J counts) (rest : RestoredScalarRest m d q f J counts O) :
    (restoredScalarFiberCoordinates.symm (a,rest)).1.2=rest.2.1 := rfl

@[simp] theorem restoredScalarFiber_outer
    (a : PositiveScalars (K := K) m d J counts) (rest : RestoredScalarRest m d q f J counts O) :
    (restoredScalarFiberCoordinates.symm (a,rest)).2=rest.2.2 := rfl

theorem principal_open_restored_scalar_fiber_at (hO : ∀ j∈J,O j≤Forms K h j) :
    letI : Module.Finite K (Space m d q J counts O) := finite_space hO
    ∀ (D : MvPolynomial (Fin (finrank K (RestoredOuterSpace m d q f J counts O))) K)
      (p : RestoredOuterSpace m d q f J counts O),
      eval ((Module.finBasis K _).equivFun p) D≠0 →
      ∃ E : MvPolynomial (Fin (finrank K (PositiveScalars (K := K) m d J counts))) K,
        eval ((Module.finBasis K _).equivFun (restoredScalarFiberCoordinates p).1) E≠0 ∧
        ∀ a,eval ((Module.finBasis K _).equivFun a) E≠0 →
          eval ((Module.finBasis K _).equivFun
            (restoredScalarFiberCoordinates.symm (a,(restoredScalarFiberCoordinates p).2))) D≠0 := by
  letI : Module.Finite K (Space m d q J counts O) := finite_space hO
  intro D p hp
  apply principal_open_freeze_at restoredScalarFiberCoordinates.symm.toLinearMap
    (restoredScalarFiberCoordinates p).1 (restoredScalarFiberCoordinates p).2 D
  simpa only [LinearEquiv.coe_toLinearMap,Prod.eta,LinearEquiv.symm_apply_apply] using hp

end Froberg.PreparedParameters
