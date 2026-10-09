module

public import Froberg.BiformTensorComponent

@[expose] public section

/-! Literal homogeneous output weights are killed by every different
tensor-component projection. -/
noncomputable section
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d t b : ℕ} {p : ZMod 2}

theorem biformTensorComponent_weighted_zero (ht : t ≤ d) (htb : t≠b)
    (v : biformParitySpace K h m d p)
    (hv : v.val.IsWeightedHomogeneous (blockWeight h m) b) :
    biformTensorComponent ht v=0 := by
  apply sumBiformMap_injective
  rw [biformTensorComponent_spec,map_zero]
  exact hv.weightedHomogeneousComponent_ne _ htb

end Froberg
