module

public import Froberg.AmbientTopGrowth
public import Froberg.BiformComponentVanish

@[expose] public section

/-! The actual top growth projection annihilates every other output
weight, in particular the literal bottom row. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f u b w : ℕ}

theorem ambientTopMap_weighted_zero (hdw : d≠w)
    (v : biformParitySpace K h m (2*d) 1)
    (hv : v.val.IsWeightedHomogeneous (blockWeight h m) w) :
    ambientTopMap v=0 := by
  have hz := biformTensorComponent_weighted_zero (K := K) (h := h) (m := m)
    (d := 2*d) (t := d) (by omega) hdw v hv
  change (topRowTarget (K := K) (h := h) (m := m) (d := d))
    (biformTensorComponent (by omega : d ≤ 2*d) v)=0
  rw [hz]
  exact (topRowTarget (K := K) (h := h) (m := m) (d := d)).map_zero

theorem ambientTopGrowthProjection_weighted_zero (hdp : 1 ≤ d) (hd : Odd d) (hd1 : 1<d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K))
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (hU : ∀ i,R ((topGrowthDegree hdp h).symm (U i))=0)
    (hdw : d≠w) (v : biformParitySpace K h m (2*d) 1)
    (hv : v.val.IsWeightedHomogeneous (blockWeight h m) w) :
    ambientTopGrowthProjection hdp hd hd1 R Q F U P hU
      ((ambientOddRelations (fun i => scalarEvenBiform (h := h) (Q i))
        (fun i => oddBiformEmbedding hdp (by decide) (F i))
        (fun i => mixedPureOddGenerator hd (U i) (P i))).mkQ v)=0 := by
  simp only [ambientTopGrowthProjection,LinearMap.comp_apply,ambientTopProjection_mk]
  rw [ambientTopMap_weighted_zero hdw v hv,map_zero,map_zero]

end Froberg
