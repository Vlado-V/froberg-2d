module

public import Froberg.OddBackgroundRow

@[expose] public section

/-! Actual coordinate relation spaces are the literal two-family row ranges. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f : ℕ}

theorem odd_coordinate_relations_eq_row (hd : 1 ≤ d)
    (Q : Fin q → Forms K h 0 ⊗[K] Forms K m d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (r : Fin ((2*d+1)/2)) (hr : 2*r.val+1 ≤ d) :
    coordinateRelation (oddBackgroundBlockRelations
      (fun i => evenBiformEmbedding (Nat.zero_le d) (by decide) (Q i))
      (fun i => oddBiformEmbedding hd (by decide) (F i))) r=
      (oddTensorRowMap (by omega) hr Q F).range := by
  have he : (LinearMap.proj r).comp
      (oddBiformCoordinatesEquiv (K := K) (h := h) (m := m) (d := 2*d)).toLinearMap=
      biformTensorComponent (by omega : 2*r.val+1 ≤ 2*d) := by
    apply LinearMap.ext
    intro v
    exact (biformTensorComponent_eq_oddCoordinates v r).symm
  change ((oddBackgroundRelations _ _).map _).map _=_
  rw [←Submodule.map_comp,he]
  exact oddBackground_tensor_row_range (by omega) hr (by omega) Q F

end Froberg
