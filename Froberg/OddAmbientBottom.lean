module

public import Froberg.OddAmbientCoordinates
public import Froberg.OddTargetBottomCoordinates

@[expose] public section

/-! Corrected ambient coordinates preserve the literal bottom row and
its scalar multiplication. -/
noncomputable section
set_option maxHeartbeats 700000
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
  (D : HigherOddTargetRows hd Q F →ₗ[K] OddTargetRowQuotient Q F (oddTargetBottomIndex hd))
  (hD : D.comp (oddAmbientHigherRelationMap hd Q F hQ hF G)=
    oddAmbientBottomRelationMap hd Q F hQ hF G)

theorem oddAmbientCoordinates_weighted_bottom
    (p : biformParitySpace K h m (2*d) 1)
    (hp : p.val.IsWeightedHomogeneous (blockWeight h m) 1) :
    oddAmbientCoordinates hd Q F hQ hF G D hD ((ambientOddRelations Q F G).mkQ p)=
      ((oddTargetBaseMap hd Q F hQ hF p).1,0) := by
  rw [oddAmbientCoordinates_mk,oddTargetBaseMap_weighted_higher_zero hd Q F hQ hF p hp]
  simp only [map_zero,sub_zero]

theorem oddAmbientCoordinates_bottom_product
    (s : biformParitySpace K h m d 0)
    (hs : s.val.IsWeightedHomogeneous (blockWeight h m) 0)
    (v : biformParitySpace K h m d 1)
    (hv : v.val.IsWeightedHomogeneous (blockWeight h m) 1) :
    oddAmbientCoordinates hd Q F hQ hF G D hD
      ((ambientOddRelations Q F G).mkQ (evenScalarOddProduct s v))=
      ((oddTargetBaseMap hd Q F hQ hF (evenScalarOddProduct s v)).1,0) := by
  rw [oddAmbientCoordinates_mk,oddTargetBaseMap_bottom_product hd Q F hQ hF s hs v hv]
  simp only [map_zero,sub_zero]

end Froberg
