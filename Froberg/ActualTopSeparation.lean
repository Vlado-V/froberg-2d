import Froberg.AmbientTopGrowth
import Froberg.MixedAmbientCorrection

/-! Injectivity of the actual projected top family gives precisely the
concrete C.10 separation needed for the mixed ambient graph correction. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct Quartic Quartic.SplitTensor
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f u b : ℕ}

theorem actual_top_separation (hdp : 1≤d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K))
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d)
    (hU : ∀ i,R ((topGrowthDegree hdp h).symm (U i))=0)
    (hinj : Function.Injective (projectedTopMap R (topGrowthParameters hdp Q F))) :
    Disjoint ((rawTopFamily F).range.map (rawTopTarget hdp).toLinearMap)
      (leftRelations (Submodule.span K (Set.range U)) ⊔ rightRelations (Submodule.span K (Set.range Q))) := by
  let pi := topGrowthTensorMap (m := m) hdp R
  let f' := (rawTopTarget hdp).toLinearMap.comp (rawTopFamily F)
  let Q' := (topGrowthParameters hdp Q F).2
  let g := sumTensorRight (K := K) (X := Fin b → K) Q'
  have he : pi.comp f'=(TensorProduct.map R
      (LinearMap.id : Forms K m (1+(d-1)) →ₗ[K] _)).comp (rawTopFamily F) := by
    apply LinearMap.ext
    intro a
    change TensorProduct.map R (LinearMap.id : Forms K m (1+(d-1)) →ₗ[K] _)
      ((rawTopTarget hdp).symm (rawTopTarget hdp (rawTopFamily F a)))=_
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have hi : Function.Injective ((pi.comp f').coprod g) := by
    rw [he]
    change Function.Injective (projectedTensorFamily (K := K) (A := Fin f → Forms K h (d-1) ⊗[K] Forms K m 1) R (rawTopFamily F) Q')
    rw [projectedTopMap_eq_tensorFamily] at hinj
    exact hinj
  have hleft : leftRelations (Submodule.span K (Set.range U))≤pi.ker := by
    rw [←sumTensorLeft_range U]
    rintro _ ⟨v,rfl⟩
    change topGrowthTensorMap hdp R (sumTensorLeft U v)=0
    simp only [sumTensorLeft_apply,map_sum,topGrowthTensorMap_tmul,hU,zero_tmul,Finset.sum_const_zero]
  have hright : (rightRelations (Submodule.span K (Set.range Q))).map pi≤g.range := by
    rw [←sumTensorRight_range Q]
    rintro _ ⟨_,⟨v,rfl⟩,rfl⟩
    refine ⟨fun i => R ((topGrowthDegree hdp h).symm (v i)),?_⟩
    change sumTensorRight Q' (fun i => R ((topGrowthDegree hdp h).symm (v i)))=
      topGrowthTensorMap hdp R (sumTensorRight Q v)
    simp only [sumTensorRight_apply,map_sum,topGrowthTensorMap_tmul,Q',topGrowthParameters]
  apply disjoint_iff_inf_le.mpr
  rintro v ⟨⟨w,⟨a,ha⟩,hw⟩,hv⟩
  obtain ⟨s,hs,t,ht,hst⟩ := Submodule.mem_sup.mp hv
  obtain ⟨c,hc⟩ := hright ⟨t,ht,rfl⟩
  have hav : f' a=v := by
    change rawTopTarget hdp (rawTopFamily F a)=v
    rw [ha]
    exact hw
  have hpa : pi (f' a)=g c := by
    rw [hav,←hst,map_add,show pi s=0 from LinearMap.mem_ker.mp (hleft hs),zero_add,hc]
  have hz : ((pi.comp f').coprod g) (a,-c)=0 := by
    simp only [LinearMap.coprod_apply,LinearMap.comp_apply,map_neg,hpa,add_neg_cancel]
  have he0 : (a,-c)=(0,0) := hi (hz.trans (map_zero _).symm)
  have ha0 : a=0 := congrArg Prod.fst he0
  apply (Submodule.mem_bot K).mpr
  rw [←hav,ha0,map_zero]

end Froberg
