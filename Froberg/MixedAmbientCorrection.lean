import Froberg.MixedAmbientKernel
import Froberg.OddAmbientCoordinates

/-! Actual ambient graph correction from pure-column independence and
concrete top-row separation. Scalar/linear weight conditions are proved. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct Quartic.SplitTensor
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}

theorem scalarEvenBiform_weighted (p : Forms K m d) :
    (scalarEvenBiform (h := h) p).val.IsWeightedHomogeneous (blockWeight h m) 0 := by
  change (sumBiformMap (scalarBiformEquiv (h := h) p)).IsWeightedHomogeneous (blockWeight h m) 0
  exact biformImage_output_weight (Forms K h 0) (Forms K m d) le_rfl
    (sumBiformMap_range.le ⟨_,rfl⟩)

theorem oddLinearBiform_weighted (hdp : 1≤d)
    (v : Forms K h 1 ⊗[K] Forms K m (d-1)) :
    (oddBiformEmbedding hdp (by decide) v).val.IsWeightedHomogeneous (blockWeight h m) 1 :=
  linearOutput_weighted v

theorem exists_mixed_ambient_correction (hdp : 1≤d) (hd : Odd d) (hd1 : 1<d)
    (Q : Fin q → Forms K m d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (hU : LinearIndependent K U)
    (hE : Disjoint ((rawTopFamily F).range.map (rawTopTarget hdp).toLinearMap)
      (leftRelations (Submodule.span K (Set.range U)) ⊔ rightRelations (Submodule.span K (Set.range Q)))) :
    ∃ D : HigherOddTargetRows hdp (fun i => scalarEvenBiform (h := h) (Q i))
        (fun i => oddBiformEmbedding hdp (by decide) (F i)) →ₗ[K]
      OddTargetRowQuotient (fun i => scalarEvenBiform (h := h) (Q i))
        (fun i => oddBiformEmbedding hdp (by decide) (F i)) (oddTargetBottomIndex hdp),
      D.comp (oddAmbientHigherRelationMap hdp (fun i => scalarEvenBiform (h := h) (Q i))
        (fun i => oddBiformEmbedding hdp (by decide) (F i))
        (fun i => scalarEvenBiform_weighted (Q i)) (fun i => oddLinearBiform_weighted hdp (F i))
        (fun i => mixedPureOddGenerator hd (U i) (P i)))=
      oddAmbientBottomRelationMap hdp (fun i => scalarEvenBiform (h := h) (Q i))
        (fun i => oddBiformEmbedding hdp (by decide) (F i))
        (fun i => scalarEvenBiform_weighted (Q i)) (fun i => oddLinearBiform_weighted hdp (F i))
        (fun i => mixedPureOddGenerator hd (U i) (P i)) := by
  exact exists_odd_ambient_correction hdp _ _ _ _ _
    (mixed_ambient_higher_kernel hdp hd hd1 Q F U P hU
      (fun i => scalarEvenBiform_weighted (Q i)) (fun i => oddLinearBiform_weighted hdp (F i)) hE)

end Froberg
