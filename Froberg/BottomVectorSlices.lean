import Froberg.BottomVectorQuotient
import Froberg.OddRowCoordinateRelations
import Froberg.OddTargetBaseCoordinates
import Froberg.ClosedKernelEquivalence

/-! The B.3 closed kernel slices transfer to the literal bottom quotient
in the ambient odd target decomposition. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module MvPolynomial TensorProduct VectorMultiplicationCoordinates
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f : ℕ}

def bottomCoordinateTargetEquiv (hd : 1 ≤ d)
    (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1)) :
    (OddRowTensor K h m 1 (2*d-1) ⧸
      tensorOddRowRelations (b := 1) (by decide) hd (fun i => scalarBiformEquiv (h := h) (Q i))
        (bottomTensorFamily g)) ≃ₗ[K]
      OddTargetRowQuotient
        (fun i => scalarEvenBiform (h := h) (Q i))
        (fun i => oddBiformEmbedding hd (by decide) (bottomTensorFamily g i))
        (oddTargetBottomIndex hd) :=
  Submodule.quotEquivOfEq _ _
    (odd_coordinate_relations_eq_row hd (fun i => scalarBiformEquiv (h := h) (Q i))
      (bottomTensorFamily g) (oddTargetBottomIndex hd) hd).symm

def bottomCoordinateScalarAction (hd : 1 ≤ d)
    (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1)) :
    Forms K m d →ₗ[K] OddBottomQuotient (bottomTensorFamily g) →ₗ[K]
      OddTargetRowQuotient
        (fun i => scalarEvenBiform (h := h) (Q i))
        (fun i => oddBiformEmbedding hd (by decide) (bottomTensorFamily g i))
        (oddTargetBottomIndex hd) :=
  (bottomTensorScalarAction hd Q g).compr₂ₛₗ (bottomCoordinateTargetEquiv hd Q g).toLinearMap

@[simp] theorem bottomCoordinateScalarAction_mk (hd : 1 ≤ d)
    (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1))
    (p : Forms K m d) (v : Forms K h 1 ⊗[K] Forms K m (d-1)) :
    bottomCoordinateScalarAction hd Q g p ((Submodule.span K (Set.range (bottomTensorFamily g))).mkQ v)=
      (coordinateRelation (oddBackgroundBlockRelations
        (fun i => scalarEvenBiform (h := h) (Q i))
        (fun i => oddBiformEmbedding hd (by decide) (bottomTensorFamily g i)))
        (oddTargetBottomIndex hd)).mkQ
          (oddRowScalarAction (b := 1) hd (scalarBiformEquiv (h := h) p) v) := by
  rw [bottomCoordinateScalarAction,LinearMap.compr₂ₛₗ_apply,bottomTensorScalarAction_mk]
  rfl

theorem bottomCoordinateScalarAction_closed_slices (hd : 1 ≤ d)
    (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1))
    (s : ℕ → ℕ)
    (hs : BilinearScalarFamily.HasClosedKernelSlices
      (BilinearScalarFamily.scalarQuotientBilinear (VectorExpansionOpen.quotientMultiplication g d) Q) s) :
    BilinearScalarFamily.HasClosedKernelSlices (bottomCoordinateScalarAction hd Q g) s := by
  apply BilinearScalarFamily.HasClosedKernelSlices.equiv
    (LinearEquiv.refl K (Forms K m d)) (bottomVectorSourceEquiv g)
    ((bottomVectorTargetEquiv hd Q g).trans (bottomCoordinateTargetEquiv hd Q g))
    _ _ _ s hs
  intro p v
  change bottomCoordinateTargetEquiv hd Q g
    (bottomVectorTargetEquiv hd Q g
      (BilinearScalarFamily.scalarQuotientBilinear (VectorExpansionOpen.quotientMultiplication g d) Q p v))=
    bottomCoordinateTargetEquiv hd Q g (bottomTensorScalarAction hd Q g p (bottomVectorSourceEquiv g v))
  rw [bottomTensorScalarAction_compatible]

end Froberg
