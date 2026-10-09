module

public import Froberg.BottomVectorRows
public import Froberg.OddSourceGraphCoordinates

@[expose] public section

/-! The B.3 vector source and its scalar quotient target identify with the
actual bottom tensor source and target, with literal product compatibility. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module MvPolynomial TensorProduct Quartic VectorMultiplicationCoordinates
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f : ℕ}

def bottomTensorFamily (g : Fin f → Rows K h m (d-1)) :
    Fin f → Forms K h 1 ⊗[K] Forms K m (d-1) := fun i => linearOutputTensorEquiv (g i)

def bottomVectorSourceEquiv (g : Fin f → Rows K h m (d-1)) :
    VectorExpansionOpen.Source g ≃ₗ[K] OddBottomQuotient (bottomTensorFamily g) :=
  Submodule.Quotient.equiv _ _ linearOutputTensorEquiv (by
    rw [Submodule.map_span,←Set.range_comp']
    rfl)

@[simp] theorem bottomVectorSourceEquiv_mk (g : Fin f → Rows K h m (d-1))
    (v : Rows K h m (d-1)) :
    bottomVectorSourceEquiv g ((Submodule.span K (Set.range g)).mkQ v)=
      (Submodule.span K (Set.range (bottomTensorFamily g))).mkQ (linearOutputTensorEquiv v) := rfl

def bottomVectorTargetEquiv (hd : 1 ≤ d)
    (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1)) :
    BilinearScalarFamily.ScalarQuotient (VectorExpansionOpen.quotientMultiplication g d) Q ≃ₗ[K]
      (OddRowTensor K h m 1 (2*d-1) ⧸
        tensorOddRowRelations (b := 1) (by decide) hd (fun i => scalarBiformEquiv (h := h) (Q i))
          (bottomTensorFamily g)) :=
  (BilinearScalarFamily.scalarDoubleQuotientEquiv multiplication (Submodule.span K (Set.range g)) Q).trans
    (Submodule.Quotient.equiv _ _ (bottomOutputTargetEquiv hd)
      (bottomRow_range_comparison hd Q g).symm)

@[simp] theorem bottomVectorTargetEquiv_mk (hd : 1 ≤ d)
    (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1))
    (v : Rows K h m ((d-1)+d)) :
    bottomVectorTargetEquiv hd Q g
      ((BilinearScalarFamily.multiplication (VectorExpansionOpen.quotientMultiplication g d) Q).range.mkQ
        ((BilinearImage.image multiplication (Submodule.span K (Set.range g))).mkQ v))=
      (tensorOddRowRelations (b := 1) (by decide) hd (fun i => scalarBiformEquiv (h := h) (Q i))
        (bottomTensorFamily g)).mkQ (bottomOutputTargetEquiv hd v) := rfl

def bottomTensorScalarAction (hd : 1 ≤ d)
    (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1)) :
    Forms K m d →ₗ[K] OddBottomQuotient (bottomTensorFamily g) →ₗ[K]
      (OddRowTensor K h m 1 (2*d-1) ⧸
        tensorOddRowRelations (b := 1) (by decide) hd (fun i => scalarBiformEquiv (h := h) (Q i))
          (bottomTensorFamily g)) :=
  ((BilinearScalarFamily.scalarQuotientBilinear (VectorExpansionOpen.quotientMultiplication g d) Q).compl₂
    (bottomVectorSourceEquiv g).symm.toLinearMap).compr₂ₛₗ (bottomVectorTargetEquiv hd Q g).toLinearMap

@[simp] theorem bottomTensorScalarAction_mk (hd : 1 ≤ d)
    (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1))
    (p : Forms K m d) (v : Forms K h 1 ⊗[K] Forms K m (d-1)) :
    bottomTensorScalarAction hd Q g p ((Submodule.span K (Set.range (bottomTensorFamily g))).mkQ v)=
      (tensorOddRowRelations (b := 1) (by decide) hd (fun i => scalarBiformEquiv (h := h) (Q i))
        (bottomTensorFamily g)).mkQ (oddRowScalarAction (b := 1) hd (scalarBiformEquiv (h := h) p) v) := by
  obtain ⟨x,rfl⟩ := (linearOutputTensorEquiv (K := K) (h := h) (m := m) (s := d-1)).surjective v
  rw [←bottomVectorSourceEquiv_mk]
  change bottomVectorTargetEquiv hd Q g
    (BilinearScalarFamily.scalarQuotientBilinear (VectorExpansionOpen.quotientMultiplication g d) Q p
      ((bottomVectorSourceEquiv g).symm (bottomVectorSourceEquiv g ((Submodule.span K (Set.range g)).mkQ x))))=_
  rw [LinearEquiv.symm_apply_apply]
  change bottomVectorTargetEquiv hd Q g
    ((BilinearScalarFamily.multiplication (VectorExpansionOpen.quotientMultiplication g d) Q).range.mkQ
      ((BilinearImage.image multiplication (Submodule.span K (Set.range g))).mkQ (multiplication p x)))=_
  rw [bottomVectorTargetEquiv_mk,bottom_vector_scalar_action]

theorem bottomTensorScalarAction_compatible (hd : 1 ≤ d)
    (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1))
    (p : Forms K m d) (v : VectorExpansionOpen.Source g) :
    bottomVectorTargetEquiv hd Q g
      (BilinearScalarFamily.scalarQuotientBilinear (VectorExpansionOpen.quotientMultiplication g d) Q p v)=
      bottomTensorScalarAction hd Q g p (bottomVectorSourceEquiv g v) := by
  change _=bottomVectorTargetEquiv hd Q g
    (BilinearScalarFamily.scalarQuotientBilinear (VectorExpansionOpen.quotientMultiplication g d) Q p
      ((bottomVectorSourceEquiv g).symm (bottomVectorSourceEquiv g v)))
  rw [LinearEquiv.symm_apply_apply]

end Froberg
