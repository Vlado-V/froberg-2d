import Froberg.OddTargetBaseCoordinates
import Froberg.BiformTensorComponent

/-! Vanishing of an actual higher quotient coordinate gives literal
membership in the corresponding component of the background relations. -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f b : ℕ}

theorem higher_target_zero_component_mem (hd : 1≤d)
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (hQ : ∀ i,(Q i).val.IsWeightedHomogeneous (blockWeight h m) 0)
    (hF : ∀ i,(F i).val.IsWeightedHomogeneous (blockWeight h m) 1)
    (r : {r : Fin ((2*d+1)/2) // r≠oddTargetBottomIndex hd})
    (hr : 2*r.val.val+1=b) (hb : b≤2*d)
    (v : biformParitySpace K h m (2*d) 1)
    (hv : (oddTargetBaseMap hd Q F hQ hF v).2 r=0) :
    biformTensorComponent hb v∈(oddBackgroundRelations Q F).map (biformTensorComponent hb) := by
  rw [oddTargetBaseMap_higher] at hv
  have hm := (Submodule.Quotient.mk_eq_zero
    (coordinateRelation (oddBackgroundBlockRelations Q F) r.val)).mp hv
  rcases hm with ⟨z,hz,he⟩
  rcases hz with ⟨p,hp,hpz⟩
  have hec : oddBiformCoordinatesEquiv p r.val=oddBiformCoordinatesEquiv v r.val := by
    rw [←hpz] at he
    exact he
  refine ⟨p,hp,?_⟩
  apply sumBiformMap_injective
  rw [biformTensorComponent_spec,biformTensorComponent_spec]
  have he' := congrArg sumBiformMap hec
  rw [oddBiformCoordinatesEquiv_component,oddBiformCoordinatesEquiv_component,hr] at he'
  exact he'

end Froberg
