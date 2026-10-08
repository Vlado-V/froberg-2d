import Froberg.OddTargetBaseCoordinates

/-! The actual ambient target quotient is a quotient by a graph after
the scalar and outer-linear background relations have been removed. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable (hd : 1≤d)
  (Q : Fin q → biformParitySpace K h m d 0)
  (F : Fin f → biformParitySpace K h m d 1)
  (hQ : ∀ i,(Q i).val.IsWeightedHomogeneous (blockWeight h m) 0)
  (hF : ∀ i,(F i).val.IsWeightedHomogeneous (blockWeight h m) 1)
  (G : Fin u → biformParitySpace K h m d 1)

def oddAmbientRelationMap :
    (Fin u → Forms K h 0 ⊗[K] Forms K m d) →ₗ[K] OddTargetBaseSpace hd Q F :=
  (oddTargetBaseMap hd Q F hQ hF).comp (privateScalarRelations G)

def oddAmbientBottomRelationMap :
    (Fin u → Forms K h 0 ⊗[K] Forms K m d) →ₗ[K]
      OddTargetRowQuotient Q F (oddTargetBottomIndex hd) :=
  (LinearMap.fst K _ _).comp (oddAmbientRelationMap hd Q F hQ hF G)

def oddAmbientHigherRelationMap :
    (Fin u → Forms K h 0 ⊗[K] Forms K m d) →ₗ[K] HigherOddTargetRows hd Q F :=
  (LinearMap.snd K _ _).comp (oddAmbientRelationMap hd Q F hQ hF G)

theorem oddAmbientRelationMap_prod :
    (oddAmbientBottomRelationMap hd Q F hQ hF G).prod
      (oddAmbientHigherRelationMap hd Q F hQ hF G)=oddAmbientRelationMap hd Q F hQ hF G := by
  apply LinearMap.ext
  intro v
  rfl

def oddAmbientGraphQuotientEquiv :
    (biformParitySpace K h m (2*d) 1 ⧸ ambientOddRelations Q F G) ≃ₗ[K]
      (OddTargetBaseSpace hd Q F ⧸
        ((oddAmbientBottomRelationMap hd Q F hQ hF G).prod
          (oddAmbientHigherRelationMap hd Q F hQ hF G)).range) := by
  have hk := oddTargetBaseMap_kernel hd Q F hQ hF
  have hr : (privateScalarRelations G).range.map (oddTargetBaseMap hd Q F hQ hF)=
      ((oddAmbientBottomRelationMap hd Q F hQ hF G).prod
        (oddAmbientHigherRelationMap hd Q F hQ hF G)).range := by
    rw [oddAmbientRelationMap_prod,oddAmbientRelationMap,LinearMap.range_comp]
  exact (Submodule.quotEquivOfEq _ _
    (congrArg (fun S => S ⊔ (privateScalarRelations G).range) hk.symm)).trans
      ((projectedQuotientEquiv (oddTargetBaseMap hd Q F hQ hF)
        (oddTargetBaseMap_surjective hd Q F hQ hF) (privateScalarRelations G).range).trans
          (Submodule.quotEquivOfEq _ _ hr))

end Froberg
