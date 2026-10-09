module

public import Froberg.OddAmbientGraph

@[expose] public section

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

attribute [local irreducible] oddAmbientBottomRelationMap oddAmbientHigherRelationMap

def oddAmbientCoordinates
    (D : HigherOddTargetRows hd Q F →ₗ[K] OddTargetRowQuotient Q F (oddTargetBottomIndex hd))
    (hD : D.comp (oddAmbientHigherRelationMap hd Q F hQ hF G)=
      oddAmbientBottomRelationMap hd Q F hQ hF G) :
    (biformParitySpace K h m (2*d) 1 ⧸ ambientOddRelations Q F G) ≃ₗ[K]
      OddTargetRowQuotient Q F (oddTargetBottomIndex hd) ×
        (HigherOddTargetRows hd Q F ⧸ (oddAmbientHigherRelationMap hd Q F hQ hF G).range) := by
  let e := @factoredGraphCoordinates K
      (Fin u → Forms K h 0 ⊗[K] Forms K m d)
      (OddTargetRowQuotient Q F (oddTargetBottomIndex hd))
      (HigherOddTargetRows hd Q F) _ _ _
      (oddTargetRowQuotientGroup Q F (oddTargetBottomIndex hd))
      (oddTargetRowQuotientModule Q F (oddTargetBottomIndex hd))
      (higherOddTargetRowsGroup hd Q F) (higherOddTargetRowsModule hd Q F)
      (oddAmbientBottomRelationMap hd Q F hQ hF G)
      (oddAmbientHigherRelationMap hd Q F hQ hF G) D hD
  exact (oddAmbientGraphQuotientEquiv hd Q F hQ hF G).trans e

@[simp] theorem oddAmbientCoordinates_mk
    (D : HigherOddTargetRows hd Q F →ₗ[K] OddTargetRowQuotient Q F (oddTargetBottomIndex hd))
    (hD : D.comp (oddAmbientHigherRelationMap hd Q F hQ hF G)=
      oddAmbientBottomRelationMap hd Q F hQ hF G)
    (p : biformParitySpace K h m (2*d) 1) :
    oddAmbientCoordinates hd Q F hQ hF G D hD ((ambientOddRelations Q F G).mkQ p)=
      ((oddTargetBaseMap hd Q F hQ hF p).1-D (oddTargetBaseMap hd Q F hQ hF p).2,
        (oddAmbientHigherRelationMap hd Q F hQ hF G).range.mkQ
          (oddTargetBaseMap hd Q F hQ hF p).2) := rfl

theorem exists_odd_ambient_correction
    (hk : (oddAmbientHigherRelationMap hd Q F hQ hF G).ker≤
      (oddAmbientBottomRelationMap hd Q F hQ hF G).ker) :
    ∃ D : HigherOddTargetRows hd Q F →ₗ[K] OddTargetRowQuotient Q F (oddTargetBottomIndex hd),
      D.comp (oddAmbientHigherRelationMap hd Q F hQ hF G)=
        oddAmbientBottomRelationMap hd Q F hQ hF G :=
  exists_graph_correction (K := K)
    (U := Fin u → Forms K h 0 ⊗[K] Forms K m d)
    (X := OddTargetRowQuotient Q F (oddTargetBottomIndex hd))
    (Y := HigherOddTargetRows hd Q F)
    (oddAmbientBottomRelationMap hd Q F hQ hF G)
    (oddAmbientHigherRelationMap hd Q F hQ hF G) hk

end Froberg
