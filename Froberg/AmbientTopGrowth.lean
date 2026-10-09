module

public import Froberg.AmbientTopProjection
public import Froberg.TopQuotientGrowth
public import Froberg.BilinearScalarReparam

@[expose] public section

/-! The actual top-row projection lands in the quotient used by the
generic growth theorem. Both the scalar and coefficient transports are
explicit, and preserve the literal product. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct Quartic Quartic.SplitTensor
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f u b : ℕ}

def topGrowthDegree (hdp : 1≤d) (n : ℕ) :
    Forms K n (1+(d-1)) ≃ₗ[K] Forms K n d :=
  formDegreeEquiv (by omega)

def topGrowthParameters (hdp : 1≤d) (Q : Fin q → Forms K m d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    ProjectedTopParameters K h m (d-1) f q :=
  (F,fun i => (topGrowthDegree hdp m).symm (Q i))

def topGrowthTensorMap (hdp : 1≤d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K)) :
    RawOddTopTensor K h m d →ₗ[K] ((Fin b → K) ⊗[K] Forms K m (1+(d-1))) :=
  (TensorProduct.map R (LinearMap.id : Forms K m (1+(d-1)) →ₗ[K] _)).comp
    (rawTopTarget hdp).symm.toLinearMap

@[simp] theorem topGrowthTensorMap_tmul (hdp : 1≤d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K))
    (x : Forms K h d) (y : Forms K m d) :
    topGrowthTensorMap hdp R (x ⊗ₜ[K] y)=
      R ((topGrowthDegree hdp h).symm x) ⊗ₜ[K] (topGrowthDegree hdp m).symm y := by
  simp only [topGrowthTensorMap,LinearMap.comp_apply,LinearEquiv.coe_coe,
    rawTopTarget,biformDegreeTransport,TensorProduct.congr_symm,
    TensorProduct.congr_tmul,TensorProduct.map_tmul,LinearMap.id_apply,topGrowthDegree]

theorem topGrowthTensorMap_relations (hdp : 1≤d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K))
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d)
    (hU : ∀ i,R ((topGrowthDegree hdp h).symm (U i))=0) :
    ambientTopRelations hdp Q F U ≤
      (projectedTensorFamily (K := K) (A := Fin f → Forms K h (d-1) ⊗[K] Forms K m 1) R (rawTopFamily F) (topGrowthParameters hdp Q F).2).range.comap
        (topGrowthTensorMap hdp R) := by
  apply sup_le
  · rw [←sumTensorLeft_range U]
    rintro _ ⟨v,rfl⟩
    change topGrowthTensorMap hdp R (sumTensorLeft U v)∈(projectedTensorFamily (K := K) (A := Fin f → Forms K h (d-1) ⊗[K] Forms K m 1) R (rawTopFamily F) (topGrowthParameters hdp Q F).2).range
    simp only [sumTensorLeft_apply,map_sum,topGrowthTensorMap_tmul,hU,zero_tmul,
      Finset.sum_const_zero]
    exact Submodule.zero_mem _
  · apply sup_le
    · rw [←sumTensorRight_range Q]
      rintro _ ⟨v,rfl⟩
      change topGrowthTensorMap hdp R (sumTensorRight Q v)∈(projectedTensorFamily (K := K) (A := Fin f → Forms K h (d-1) ⊗[K] Forms K m 1) R (rawTopFamily F) (topGrowthParameters hdp Q F).2).range
      refine ⟨(0,fun i => R ((topGrowthDegree hdp h).symm (v i))),?_⟩
      simp only [projectedTensorFamily,LinearMap.coprod_apply,map_zero,zero_add,
        sumTensorRight_apply,map_sum,topGrowthTensorMap_tmul,topGrowthParameters]
    · rintro _ ⟨w,⟨a,rfl⟩,rfl⟩
      change topGrowthTensorMap hdp R (rawTopTarget hdp (rawTopFamily F a))∈(projectedTensorFamily (K := K) (A := Fin f → Forms K h (d-1) ⊗[K] Forms K m 1) R (rawTopFamily F) (topGrowthParameters hdp Q F).2).range
      refine ⟨(a,0),?_⟩
      simp only [projectedTensorFamily,LinearMap.coprod_apply,map_zero,add_zero,
        topGrowthTensorMap,LinearMap.comp_apply,LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]

def topGrowthQuotientProjection (hdp : 1≤d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K))
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d)
    (hU : ∀ i,R ((topGrowthDegree hdp h).symm (U i))=0) :
    (RawOddTopTensor K h m d ⧸ ambientTopRelations hdp Q F U) →ₗ[K]
      ((Fin b → K) ⊗[K] Forms K m (1+(d-1))) ⧸
        (projectedTensorFamily (K := K) (A := Fin f → Forms K h (d-1) ⊗[K] Forms K m 1) R (rawTopFamily F) (topGrowthParameters hdp Q F).2).range :=
  Submodule.mapQ _ _ (topGrowthTensorMap hdp R)
    (topGrowthTensorMap_relations hdp R Q F U hU)

@[simp] theorem topGrowthQuotientProjection_tmul (hdp : 1≤d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K))
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d)
    (hU : ∀ i,R ((topGrowthDegree hdp h).symm (U i))=0)
    (x : Forms K h d) (y : Forms K m d) :
    topGrowthQuotientProjection hdp R Q F U hU
      ((ambientTopRelations hdp Q F U).mkQ (x ⊗ₜ[K] y))=
    projectedTensorScalarAction (K := K) (A := Fin f → Forms K h (d-1) ⊗[K] Forms K m 1) R (rawTopFamily F) (topGrowthParameters hdp Q F).2
      ((topGrowthDegree hdp m).symm y) (R ((topGrowthDegree hdp h).symm x)) := by
  change (projectedTensorFamily (K := K) (A := Fin f → Forms K h (d-1) ⊗[K] Forms K m 1) R (rawTopFamily F) (topGrowthParameters hdp Q F).2).range.mkQ (topGrowthTensorMap hdp R (x ⊗ₜ[K] y))=_
  rw [topGrowthTensorMap_tmul]
  rfl

def ambientTopGrowthProjection (hdp : 1≤d) (hd : Odd d) (hd1 : 1<d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K))
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (hU : ∀ i,R ((topGrowthDegree hdp h).symm (U i))=0) :=
  (topGrowthQuotientProjection hdp R Q F U hU).comp
    (ambientTopProjection hdp hd hd1 Q F U P)

def topGrowthScalarAction (hdp : 1≤d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K))
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :=
  (projectedTensorScalarAction (K := K) (A := Fin f → Forms K h (d-1) ⊗[K] Forms K m 1) R (rawTopFamily F) (topGrowthParameters hdp Q F).2).comp
    (topGrowthDegree hdp m).symm.toLinearMap

theorem ambientTopGrowthProjection_product (hdp : 1≤d) (hd : Odd d) (hd1 : 1<d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K))
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (hU : ∀ i,R ((topGrowthDegree hdp h).symm (U i))=0)
    (p : Forms K m d) (v : biformParitySpace K h m d 1) :
    ambientTopGrowthProjection hdp hd hd1 R Q F U P hU
      ((ambientOddRelations (fun i => scalarEvenBiform (h := h) (Q i))
        (fun i => oddBiformEmbedding hdp (by decide) (F i))
        (fun i => mixedPureOddGenerator hd (U i) (P i))).mkQ
          (evenScalarOddProduct (scalarEvenBiform (h := h) p) v))=
      topGrowthScalarAction hdp R Q F p
        (R ((topGrowthDegree hdp h).symm
          (topRowScalarCoefficient (biformTensorComponent le_rfl v)))) := by
  simp only [ambientTopGrowthProjection,LinearMap.comp_apply,ambientTopProjection_mk]
  rw [ambientTopMap_scalar_product,topGrowthQuotientProjection_tmul]
  rfl

theorem topGrowthScalarAction_growth (hdp : 1≤d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K)) (hR : Function.Surjective R)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (t : ℕ)
    (hgrowth : ∀ L : Submodule K (Fin b → K),t*finrank K L≤
      finrank K (BilinearImage.image (projectedTopScalarAction R
        (topGrowthParameters hdp Q F)) L))
    (L : Submodule K (Fin b → K)) :
    t*finrank K L≤finrank K (BilinearImage.image (topGrowthScalarAction hdp R Q F) L) := by
  rw [topGrowthScalarAction,bilinearImage_scalar_comp _ _ (topGrowthDegree hdp m).symm.surjective]
  have hg := top_tensor_scalar_growth R hR (topGrowthParameters hdp Q F) hgrowth L
  rw [tensorFamilyScalarAction_finrank] at hg
  exact hg

end Froberg
