module

public import Froberg.OddAmbientGraph
public import Froberg.OddTargetHigherKernel
public import Froberg.TopRowComparison
public import Froberg.TensorIndependentCoefficients
public import Froberg.ScalarBackgroundRelations

@[expose] public section

/-! The top separation condition forces every relation with zero higher
coordinates to be an existing Q relation, so it cannot kill the bottom. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct Quartic.SplitTensor
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}

theorem mixed_ambient_higher_kernel (hdp : 1≤d) (hd : Odd d) (hd1 : 1<d)
    (Q : Fin q → Forms K m d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (hU : LinearIndependent K U)
    (hQ : ∀ i,(scalarEvenBiform (h := h) (Q i)).val.IsWeightedHomogeneous (blockWeight h m) 0)
    (hF : ∀ i,(oddBiformEmbedding hdp (by decide) (F i)).val.IsWeightedHomogeneous (blockWeight h m) 1)
    (hE : Disjoint ((rawTopFamily F).range.map (rawTopTarget hdp).toLinearMap)
      (leftRelations (Submodule.span K (Set.range U)) ⊔ rightRelations (Submodule.span K (Set.range Q)))) :
    (oddAmbientHigherRelationMap hdp (fun i => scalarEvenBiform (h := h) (Q i))
      (fun i => oddBiformEmbedding hdp (by decide) (F i)) hQ hF
      (fun i => mixedPureOddGenerator hd (U i) (P i))).ker ≤
    (oddAmbientBottomRelationMap hdp (fun i => scalarEvenBiform (h := h) (Q i))
      (fun i => oddBiformEmbedding hdp (by decide) (F i)) hQ hF
      (fun i => mixedPureOddGenerator hd (U i) (P i))).ker := by
  intro v hv
  let G := fun i => mixedPureOddGenerator hd (U i) (P i)
  let r : Fin ((2*d+1)/2) := ⟨(d-1)/2,by omega⟩
  have hr : 2*r.val+1=d := by
    have ho := Nat.odd_iff.mp hd
    dsimp [r]
    omega
  have hrne : r≠oddTargetBottomIndex hdp := by
    intro he
    have he' := congrArg Fin.val he
    change r.val=0 at he'
    omega
  have hz : (oddTargetBaseMap hdp (fun i => scalarEvenBiform (h := h) (Q i))
      (fun i => oddBiformEmbedding hdp (by decide) (F i)) hQ hF
      (privateScalarRelations G v)).2 ⟨r,hrne⟩=0 := by
    exact congrFun hv ⟨r,hrne⟩
  have hm := higher_target_zero_component_mem hdp
    (fun i => scalarEvenBiform (h := h) (Q i))
    (fun i => oddBiformEmbedding hdp (by decide) (F i)) hQ hF
    ⟨r,hrne⟩ hr (by omega : d≤2*d) (privateScalarRelations G v) hz
  change biformTensorComponent (by omega : d≤2*d) (privateScalarRelations G v)∈
    (oddBackgroundRelations
      (fun i => evenBiformEmbedding (Nat.zero_le d) (by decide) (scalarBiformEquiv (h := h) (Q i)))
      (fun i => oddBiformEmbedding hdp (by decide) (F i))).map
        (biformTensorComponent (by omega : d≤2*d)) at hm
  rw [oddBackground_tensor_row_range hdp le_rfl (Nat.odd_iff.mp hd)] at hm
  have ht : topRowTarget (biformTensorComponent (by omega : d≤2*d) (privateScalarRelations G v))∈
      (oddTensorRowMap hdp le_rfl (fun i => scalarBiformEquiv (h := h) (Q i)) F).range.map
        topRowTarget.toLinearMap := ⟨_,hm,rfl⟩
  rw [topRow_range_comparison hdp Q F] at ht
  change biformDegreeTransport rfl (by omega : 2*d-d=d)
      (biformTensorComponent (by omega : d≤2*d)
        (privateScalarRelations (fun i => mixedPureOddGenerator hd (U i) (P i)) v))∈_ at ht
  rw [mixedScalarRelations_top hd hd1 U P v] at ht
  have hc := separated_tensor_coefficients_mem U hU (Submodule.span K (Set.range Q))
    ((rawTopFamily F).range.map (rawTopTarget hdp).toLinearMap) hE
    (fun i => (scalarBiformEquiv (h := h)).symm (v i)) (by simpa only [sup_comm] using ht)
  have hs := privateScalarRelations_mem_scalar_background
    (fun i => scalarBiformEquiv (h := h) (Q i)) G v
    (fun i => (scalarBiform_span_iff Q (v i)).mpr (hc i))
  have hb : privateScalarRelations G v∈oddBackgroundRelations
      (fun i => scalarEvenBiform (h := h) (Q i))
      (fun i => oddBiformEmbedding hdp (by decide) (F i)) :=
    (show (evenScalarOddFamily (fun i => scalarEvenBiform (h := h) (Q i))).range≤
      oddBackgroundRelations (fun i => scalarEvenBiform (h := h) (Q i))
        (fun i => oddBiformEmbedding hdp (by decide) (F i)) from le_sup_left) hs
  have hbase : oddTargetBaseMap hdp (fun i => scalarEvenBiform (h := h) (Q i))
      (fun i => oddBiformEmbedding hdp (by decide) (F i)) hQ hF (privateScalarRelations G v)=0 :=
by
      apply LinearMap.mem_ker.mp
      rw [oddTargetBaseMap_kernel hdp _ _ hQ hF]
      exact hb
  change (oddTargetBaseMap hdp (fun i => scalarEvenBiform (h := h) (Q i))
    (fun i => oddBiformEmbedding hdp (by decide) (F i)) hQ hF (privateScalarRelations G v)).1=0
  rw [hbase]
  rfl

end Froberg
