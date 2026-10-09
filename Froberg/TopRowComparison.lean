module

public import Froberg.OddBackgroundRow
public import Froberg.BiformDegreeTransport
public import Froberg.TopTensorExactness

@[expose] public section

/-! The top biform row is the literal raw tensor family plus the scalar
right-factor relations. All degree-zero factors are removed by explicit
linear equivalences. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
namespace Froberg
open Module MvPolynomial TensorProduct Quartic.SplitTensor
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f : ℕ}

def topRowTarget :
    (Forms K h d ⊗[K] Forms K m (2*d-d)) ≃ₗ[K] (Forms K h d ⊗[K] Forms K m d) :=
  biformDegreeTransport rfl (by omega)

def rawTopTarget (hd : 1 ≤ d) :
    (Forms K h (1+(d-1)) ⊗[K] Forms K m (1+(d-1))) ≃ₗ[K]
      (Forms K h d ⊗[K] Forms K m d) :=
  biformDegreeTransport (by omega) (by omega)

def topRowLinearCoefficient :
    (Forms K h (d-1) ⊗[K] Forms K m (d-d+1)) ≃ₗ[K]
      (Forms K h (d-1) ⊗[K] Forms K m 1) :=
  biformDegreeTransport rfl (by omega)

def topRowScalarCoefficient :
    (Forms K h d ⊗[K] Forms K m (d-d)) ≃ₗ[K] Forms K h d :=
  (biformDegreeTransport rfl (Nat.sub_self d)).trans (rightScalarBiformEquiv (m := m)).symm

@[simp] theorem sumBiformMap_topRowTarget (v : Forms K h d ⊗[K] Forms K m (2*d-d)) :
    sumBiformMap (topRowTarget v)=sumBiformMap v := sumBiformMap_degreeTransport _ _ v

@[simp] theorem sumBiformMap_rawTopTarget (hd : 1 ≤ d)
    (v : Forms K h (1+(d-1)) ⊗[K] Forms K m (1+(d-1))) :
    sumBiformMap (rawTopTarget hd v)=sumBiformMap v := sumBiformMap_degreeTransport _ _ v

@[simp] theorem sumBiformMap_topRowLinearCoefficient
    (v : Forms K h (d-1) ⊗[K] Forms K m (d-d+1)) :
    sumBiformMap (topRowLinearCoefficient v)=sumBiformMap v := sumBiformMap_degreeTransport _ _ v

theorem sumBiformMap_topRowScalarCoefficient
    (v : Forms K h d ⊗[K] Forms K m (d-d)) :
    rename Sum.inl (topRowScalarCoefficient v).val=sumBiformMap v := by
  let z := biformDegreeTransport (K := K) (h := h) (m := m) (a := d)
    rfl (Nat.sub_self d) v
  have he := sumBiformMap_rightScalar (m := m) ((rightScalarBiformEquiv (K := K) (h := h) (m := m) (a := d)).symm z)
  rw [LinearEquiv.apply_symm_apply] at he
  change rename Sum.inl ((rightScalarBiformEquiv (m := m)).symm z).val=_
  rw [←he]
  exact sumBiformMap_degreeTransport _ _ v

theorem sumBiformMap_tensorProduct {a b c e : ℕ}
    (p : Forms K h a ⊗[K] Forms K m c) (v : Forms K h b ⊗[K] Forms K m e) :
    sumBiformMap (tensorFormProduct (d := c) (gradedMultiplication (d := a) (e := b)) p v)=
      sumBiformMap p*sumBiformMap v := by
  induction p using TensorProduct.inductionOn with
  | tmul x y =>
    induction v using TensorProduct.inductionOn with
    | tmul z w =>
      rw [tensorFormProduct_tmul,sumBiformMap_tmul,sumBiformMap_tmul,sumBiformMap_tmul]
      change rename Sum.inl (x.val*z.val)*rename Sum.inr (w.val*y.val)=_
      simp only [map_mul]
      ring
    | add x y hx hy => simp only [map_add,hx,hy,mul_add]
  | add x y hx hy => simp only [map_add,LinearMap.add_apply,hx,hy,add_mul]

theorem topRow_linear_action (hd : 1 ≤ d)
    (p : Forms K h 1 ⊗[K] Forms K m (d-1))
    (v : Forms K h (d-1) ⊗[K] Forms K m (d-d+1)) :
    topRowTarget (oddRowLinearAction hd le_rfl p v)=
      rawTopTarget hd (tensorFormProduct (d := d-1)
        (gradedMultiplication (d := 1) (e := d-1)) p (topRowLinearCoefficient v)) := by
  apply sumBiformMap_injective
  rw [sumBiformMap_topRowTarget,oddRowLinearAction,sumBiformMap_action,
    sumBiformMap_rawTopTarget,sumBiformMap_tensorProduct,sumBiformMap_topRowLinearCoefficient]

theorem topRow_scalar_action
    (p : Forms K m d) (v : Forms K h d ⊗[K] Forms K m (d-d)) :
    topRowTarget (oddRowScalarAction le_rfl (scalarBiformEquiv (h := h) p) v)=
      topRowScalarCoefficient v ⊗ₜ[K] p := by
  apply sumBiformMap_injective
  rw [sumBiformMap_topRowTarget,oddRowScalarAction,sumBiformMap_action,
    scalarBiformEquiv_apply,sumBiformMap_tmul,sumBiformMap_tmul,
    sumBiformMap_topRowScalarCoefficient]
  change (rename Sum.inl (C (1 : K))*rename Sum.inr p.val)*sumBiformMap v=
    sumBiformMap v*rename Sum.inr p.val
  simp [mul_comm]


def topRowCoefficients :
    ((Fin f → Forms K h (d-1) ⊗[K] Forms K m (d-d+1)) ×
      (Fin q → Forms K h d ⊗[K] Forms K m (d-d))) ≃ₗ[K]
    ((Fin f → Forms K h (d-1) ⊗[K] Forms K m 1) × (Fin q → Forms K h d)) :=
  LinearEquiv.prodCongr (LinearEquiv.piCongrRight (fun _ => topRowLinearCoefficient))
    (LinearEquiv.piCongrRight (fun _ => topRowScalarCoefficient))

theorem oddTensorRowMap_top_apply (hd : 1 ≤ d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (a : Fin f → Forms K h (d-1) ⊗[K] Forms K m (d-d+1))
    (c : Fin q → Forms K h d ⊗[K] Forms K m (d-d)) :
    oddTensorRowMap hd le_rfl (fun i => scalarBiformEquiv (h := h) (Q i)) F (a,c)=
      (∑ i,oddRowLinearAction hd le_rfl (F i) (a i))+
        ∑ i,oddRowScalarAction le_rfl (scalarBiformEquiv (h := h) (Q i)) (c i) := by
  simp only [oddTensorRowMap,twoFamilyMultiplication,LinearMap.coprod_apply,
    BilinearScalarFamily.multiplication_apply]

theorem rawTopFamily_apply (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (a : Fin f → Forms K h (d-1) ⊗[K] Forms K m 1) :
    rawTopFamily F a=∑ i,tensorFormProduct (d := d-1)
      (gradedMultiplication (d := 1) (e := d-1)) (F i) (a i) :=
  BilinearScalarFamily.multiplication_apply _ _ _

set_option backward.isDefEq.respectTransparency true in
theorem topRow_map_comparison (hd : 1 ≤ d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    (topRowTarget (K := K) (h := h) (m := m) (d := d)).toLinearMap.comp
      (oddTensorRowMap hd le_rfl (fun i => scalarBiformEquiv (h := h) (Q i)) F)=
    (((rawTopTarget hd).toLinearMap.comp (rawTopFamily F)).coprod
      (sumTensorRight (K := K) (X := Forms K h d) Q)).comp (topRowCoefficients (K := K) (h := h) (m := m) (d := d) (f := f) (q := q)).toLinearMap := by
  apply LinearMap.ext
  rintro ⟨a,c⟩
  change (topRowTarget (K := K) (h := h) (m := m) (d := d)) (oddTensorRowMap hd le_rfl _ F (a,c))=
    rawTopTarget hd (rawTopFamily F (fun i => topRowLinearCoefficient (a i)))+
      sumTensorRight Q (fun i => topRowScalarCoefficient (c i))
  rw [oddTensorRowMap_top_apply]
  simp only [map_add,map_sum,topRow_linear_action hd,topRow_scalar_action,
    rawTopFamily_apply,sumTensorRight_apply]

theorem topRow_range_comparison (hd : 1 ≤ d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    (oddTensorRowMap hd le_rfl (fun i => scalarBiformEquiv (h := h) (Q i)) F).range.map
      topRowTarget.toLinearMap=
    (rawTopFamily F).range.map (rawTopTarget hd).toLinearMap ⊔
      rightRelations (Submodule.span K (Set.range Q)) := by
  have he := congrArg LinearMap.range (topRow_map_comparison hd Q F)
  rw [LinearMap.range_comp,LinearMap.range_comp,
    LinearMap.range_eq_top.mpr topRowCoefficients.surjective,Submodule.map_top,
    LinearMap.range_coprod,LinearMap.range_comp,sumTensorRight_range] at he
  exact he

end Froberg
