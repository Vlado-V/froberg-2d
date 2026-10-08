import Froberg.MixedPureComponents
import Froberg.BiformDegreeTransport
import Froberg.BiformTensorComponent

/-! Literal components of the scalar multiples of U+P. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d u t : ℕ}

theorem privateScalarRelations_val
    (G : Fin u → biformParitySpace K h m d 1)
    (v : Fin u → Forms K h 0 ⊗[K] Forms K m d) :
    (privateScalarRelations G v).val=∑ i,(G i).val*sumBiformMap (v i) := by
  rw [privateScalarRelations,LinearMap.comp_apply,privateEvenCoefficientMap_val]
  rfl

theorem scalarBiform_polynomial (v : Forms K h 0 ⊗[K] Forms K m d) :
    sumBiformMap v=rename Sum.inr ((scalarBiformEquiv (h := h)).symm v).val := by
  obtain ⟨a,rfl⟩ := (scalarBiformEquiv (K := K) (h := h) (n := m) (d := d)).surjective v
  rw [LinearEquiv.symm_apply_apply,scalarBiformEquiv_apply,sumBiformMap_tmul]
  change rename Sum.inl (C (1 : K))*rename Sum.inr a.val=_
  simp

theorem privateScalarRelations_component
    (G : Fin u → biformParitySpace K h m d 1)
    (v : Fin u → Forms K h 0 ⊗[K] Forms K m d) :
    weightedHomogeneousComponent (blockWeight h m) t (privateScalarRelations G v).val=
      ∑ i,weightedHomogeneousComponent (blockWeight h m) t (G i).val*sumBiformMap (v i) := by
  rw [privateScalarRelations_val,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hv : (sumBiformMap (v i)).IsWeightedHomogeneous (blockWeight h m) 0 :=
    biformImage_output_weight (Forms K h 0) (Forms K m d) le_rfl
      (sumBiformMap_range.le ⟨v i,rfl⟩)
  simpa only [Nat.add_zero] using
    weighted_component_mul_homogeneous (blockWeight h m) (G i).val (sumBiformMap (v i)) t 0 hv

theorem mixedScalarRelations_other (hd : Odd d) (ht1 : t≠1) (htd : t≠d)
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (v : Fin u → Forms K h 0 ⊗[K] Forms K m d) :
    weightedHomogeneousComponent (blockWeight h m) t
      (privateScalarRelations (fun i => mixedPureOddGenerator hd (U i) (P i)) v).val=0 := by
  rw [privateScalarRelations_component]
  simp only [mixedPureOddGenerator_other hd ht1 htd,zero_mul,Finset.sum_const_zero]

theorem mixedScalarRelations_bottom (hd : Odd d) (hd1 : 1<d)
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (v : Fin u → Forms K h 0 ⊗[K] Forms K m d) :
    weightedHomogeneousComponent (blockWeight h m) 1
      (privateScalarRelations (fun i => mixedPureOddGenerator hd (U i) (P i)) v).val=
      ∑ i,sumBiformMap (P i)*sumBiformMap (v i) := by
  rw [privateScalarRelations_component]
  simp only [mixedPureOddGenerator_bottom hd hd1]

theorem mixedScalarRelations_top (hd : Odd d) (hd1 : 1<d)
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (v : Fin u → Forms K h 0 ⊗[K] Forms K m d) :
    biformDegreeTransport rfl (by omega : 2*d-d=d)
      (biformTensorComponent (by omega : d≤2*d)
        (privateScalarRelations (fun i => mixedPureOddGenerator hd (U i) (P i)) v))=
      ∑ i,(U i) ⊗ₜ[K] ((scalarBiformEquiv (h := h)).symm (v i)) := by
  apply sumBiformMap_injective
  rw [sumBiformMap_degreeTransport,biformTensorComponent_spec,
    privateScalarRelations_component,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mixedPureOddGenerator_top hd hd1,sumBiformMap_tmul,scalarBiform_polynomial]

end Froberg
