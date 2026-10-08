import Froberg.OddAmbientHigherBlocks

/-! Non-top target rows are unchanged by the private scalar relations. -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable (hdp : 1≤d) (hd : Odd d)
  (Q : Fin q → biformParitySpace K h m d 0)
  (F : Fin f → biformParitySpace K h m d 1)
  (hQ : ∀ i,(Q i).val.IsWeightedHomogeneous (blockWeight h m) 0)
  (hF : ∀ i,(F i).val.IsWeightedHomogeneous (blockWeight h m) 1)
  (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
  (r : {r : Fin ((2*d+1)/2) // r≠oddTargetBottomIndex hdp})

theorem mixedAmbientHigher_relation_bot (hr : 2*r.val.val+1≠d) :
    coordinateRelation (oddAmbientHigherRelationMap hdp Q F hQ hF
      (fun i => mixedPureOddGenerator hd (U i) (P i))).range r=⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨z,⟨v,hv⟩,hx⟩
  rw [←hv] at hx
  change oddAmbientHigherRelationMap hdp Q F hQ hF
    (fun i => mixedPureOddGenerator hd (U i) (P i)) v r=x at hx
  exact (Submodule.mem_bot K).mpr (hx.symm.trans
    (mixedAmbientHigher_other_zero hdp hd Q F hQ hF U P r hr v))

def oddAmbientNonTopBlockEquiv (hr : 2*r.val.val+1≠d) :
    (OddTargetRowQuotient Q F r.val ⧸
      coordinateRelation (oddAmbientHigherRelationMap hdp Q F hQ hF
        (fun i => mixedPureOddGenerator hd (U i) (P i))).range r) ≃ₗ[K]
      OddTargetRowQuotient Q F r.val :=
  Submodule.quotEquivOfEqBot _ (mixedAmbientHigher_relation_bot hdp hd Q F hQ hF U P r hr)

end Froberg
