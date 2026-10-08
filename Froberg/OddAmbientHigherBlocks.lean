import Froberg.OddAmbientGraph
import Froberg.MixedScalarComponents

/-! The higher ambient relation space is supported only in the top row.
All other odd target rows, including those above the source range, remain. -/
noncomputable section
set_option maxHeartbeats 1000000
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

theorem mixedAmbientHigher_other_zero
    (r : {r : Fin ((2*d+1)/2) // r≠oddTargetBottomIndex hdp})
    (hr : 2*r.val.val+1≠d) (v : Fin u → Forms K h 0 ⊗[K] Forms K m d) :
    oddAmbientHigherRelationMap hdp Q F hQ hF
      (fun i => mixedPureOddGenerator hd (U i) (P i)) v r=0 := by
  have hr1 : 2*r.val.val+1≠1 := by
    intro he
    apply r.property
    apply Fin.ext
    change r.val.val=0
    omega
  change (oddTargetBaseMap hdp Q F hQ hF
    (privateScalarRelations (fun i => mixedPureOddGenerator hd (U i) (P i)) v)).2 r=0
  rw [oddTargetBaseMap_higher]
  have hc : oddBiformCoordinatesEquiv
      (privateScalarRelations (fun i => mixedPureOddGenerator hd (U i) (P i)) v) r.val=0 := by
    apply sumBiformMap_injective
    rw [oddBiformCoordinatesEquiv_component,map_zero]
    exact mixedScalarRelations_other hd hr1 hr U P v
  rw [hc,map_zero]

theorem mixedAmbientHigher_range_single :
    ∀ x : HigherOddTargetRows hdp Q F,
      x∈(oddAmbientHigherRelationMap hdp Q F hQ hF
        (fun i => mixedPureOddGenerator hd (U i) (P i))).range →
      ∀ r : {r : Fin ((2*d+1)/2) // r≠oddTargetBottomIndex hdp},
        Pi.single r (x r)∈(oddAmbientHigherRelationMap hdp Q F hQ hF
          (fun i => mixedPureOddGenerator hd (U i) (P i))).range := by
  classical
  rintro _ ⟨v,rfl⟩ r
  by_cases hr : 2*r.val.val+1=d
  · have he : Pi.single r (oddAmbientHigherRelationMap hdp Q F hQ hF
        (fun i => mixedPureOddGenerator hd (U i) (P i)) v r)=
        oddAmbientHigherRelationMap hdp Q F hQ hF
          (fun i => mixedPureOddGenerator hd (U i) (P i)) v := by
      funext s
      by_cases hs : s=r
      · subst s
        exact Pi.single_eq_same _ _
      · rw [Pi.single_eq_of_ne hs]
        symm
        apply mixedAmbientHigher_other_zero hdp hd Q F hQ hF U P s _ v
        intro hsd
        apply hs
        apply Subtype.ext
        apply Fin.ext
        omega
    rw [he]
    exact ⟨v,rfl⟩
  · rw [mixedAmbientHigher_other_zero hdp hd Q F hQ hF U P r hr v]
    simpa only [Pi.single_zero] using (Submodule.zero_mem
      (oddAmbientHigherRelationMap hdp Q F hQ hF
        (fun i => mixedPureOddGenerator hd (U i) (P i))).range)

def oddAmbientHigherBlocksEquiv :
    (HigherOddTargetRows hdp Q F ⧸
      (oddAmbientHigherRelationMap hdp Q F hQ hF
        (fun i => mixedPureOddGenerator hd (U i) (P i))).range) ≃ₗ[K]
    ((r : {r : Fin ((2*d+1)/2) // r≠oddTargetBottomIndex hdp}) →
      OddTargetRowQuotient Q F r.val ⧸
        coordinateRelation (oddAmbientHigherRelationMap hdp Q F hQ hF
          (fun i => mixedPureOddGenerator hd (U i) (P i))).range r) :=
  coordinateQuotientEquiv _ (mixedAmbientHigher_range_single hdp hd Q F hQ hF U P)

end Froberg
