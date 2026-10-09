module

public import Froberg.TopRowComparison
public import Froberg.MixedScalarComponents
public import Froberg.OddBackgroundProduct

@[expose] public section

/-! The actual ambient target projects to the C.11 tensor quotient.
Only a projection is needed for its scalar image lower bound. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct Quartic.SplitTensor
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}

abbrev RawOddTopTensor (K : Type) [Field K] (h m d : ℕ) := Forms K h d ⊗[K] Forms K m d

instance rawOddTopTensorGroup : AddCommGroup (RawOddTopTensor K h m d) := tensorFormGroup
instance rawOddTopTensorModule : Module K (RawOddTopTensor K h m d) := TensorProduct.leftModule

def ambientTopRelations (hdp : 1≤d) (Q : Fin q → Forms K m d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) (U : Fin u → Forms K h d) :
    Submodule K (RawOddTopTensor K h m d) :=
  leftRelations (Submodule.span K (Set.range U)) ⊔
    (rightRelations (Submodule.span K (Set.range Q)) ⊔
      (rawTopFamily F).range.map (rawTopTarget hdp).toLinearMap)

def ambientTopMap : biformParitySpace K h m (2*d) 1 →ₗ[K] RawOddTopTensor K h m d :=
  topRowTarget.toLinearMap.comp (biformTensorComponent (by omega : d≤2*d))

theorem ambientTopMap_background (hdp : 1≤d) (hd : Odd d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    (oddBackgroundRelations (fun i => scalarEvenBiform (h := h) (Q i))
      (fun i => oddBiformEmbedding hdp (by decide) (F i))).map ambientTopMap=
      (rawTopFamily F).range.map (rawTopTarget hdp).toLinearMap ⊔
        rightRelations (Submodule.span K (Set.range Q)) := by
  rw [ambientTopMap,Submodule.map_comp]
  change ((oddBackgroundRelations
    (fun i => evenBiformEmbedding (Nat.zero_le d) (by decide) (scalarBiformEquiv (h := h) (Q i)))
    (fun i => oddBiformEmbedding hdp (by decide) (F i))).map
      (biformTensorComponent (by omega : d≤2*d))).map topRowTarget.toLinearMap=_
  rw [oddBackground_tensor_row_range hdp le_rfl (Nat.odd_iff.mp hd)]
  exact topRow_range_comparison hdp Q F

theorem ambientTopMap_private_mem (hdp : 1≤d) (hd : Odd d) (hd1 : 1<d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (v : Fin u → Forms K h 0 ⊗[K] Forms K m d) :
    ambientTopMap (privateScalarRelations (fun i => mixedPureOddGenerator hd (U i) (P i)) v)∈
      ambientTopRelations hdp Q F U := by
  have he := mixedScalarRelations_top hd hd1 U P v
  change ambientTopMap (privateScalarRelations (fun i => mixedPureOddGenerator hd (U i) (P i)) v)=_ at he
  rw [he]
  apply (show leftRelations (Submodule.span K (Set.range U))≤ambientTopRelations hdp Q F U from le_sup_left)
  rw [←sumTensorLeft_range U]
  exact ⟨fun i => (scalarBiformEquiv (h := h)).symm (v i),sumTensorLeft_apply _ _⟩

theorem ambientTopMap_relations (hdp : 1≤d) (hd : Odd d) (hd1 : 1<d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    ambientOddRelations (fun i => scalarEvenBiform (h := h) (Q i))
      (fun i => oddBiformEmbedding hdp (by decide) (F i))
      (fun i => mixedPureOddGenerator hd (U i) (P i))≤
      (ambientTopRelations hdp Q F U).comap ambientTopMap := by
  apply sup_le
  · rw [←Submodule.map_le_iff_le_comap,ambientTopMap_background hdp hd Q F]
    exact sup_le (le_trans le_sup_right le_sup_right) (le_trans le_sup_left le_sup_right)
  · rintro _ ⟨v,rfl⟩
    exact ambientTopMap_private_mem hdp hd hd1 Q F U P v

def ambientTopProjection (hdp : 1≤d) (hd : Odd d) (hd1 : 1<d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    (biformParitySpace K h m (2*d) 1 ⧸
      ambientOddRelations (fun i => scalarEvenBiform (h := h) (Q i))
        (fun i => oddBiformEmbedding hdp (by decide) (F i))
        (fun i => mixedPureOddGenerator hd (U i) (P i))) →ₗ[K]
      RawOddTopTensor K h m d ⧸ ambientTopRelations hdp Q F U :=
  Submodule.mapQ _ _ ambientTopMap (ambientTopMap_relations hdp hd hd1 Q F U P)

@[simp] theorem ambientTopProjection_mk (hdp : 1≤d) (hd : Odd d) (hd1 : 1<d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (v : biformParitySpace K h m (2*d) 1) :
    ambientTopProjection hdp hd hd1 Q F U P
      ((ambientOddRelations (fun i => scalarEvenBiform (h := h) (Q i))
        (fun i => oddBiformEmbedding hdp (by decide) (F i))
        (fun i => mixedPureOddGenerator hd (U i) (P i))).mkQ v)=
      (ambientTopRelations hdp Q F U).mkQ (ambientTopMap v) := rfl

theorem ambientTopMap_scalar_product (p : Forms K m d)
    (v : biformParitySpace K h m d 1) :
    ambientTopMap (evenScalarOddProduct (scalarEvenBiform (h := h) p) v)=
      topRowScalarCoefficient (biformTensorComponent le_rfl v) ⊗ₜ[K] p := by
  change topRowTarget (biformTensorComponent (by omega : d≤2*d)
    (evenScalarOddProduct (evenBiformEmbedding (Nat.zero_le d) (by decide)
      (scalarBiformEquiv (h := h) p)) v))=_
  rw [biformTensorComponent_scalar_product le_rfl]
  exact topRow_scalar_action (K := K) (h := h) (m := m) (d := d) p
    (biformTensorComponent le_rfl v)

end Froberg
