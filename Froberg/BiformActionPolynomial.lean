module

public import Froberg.BiformActions
public import Froberg.BiformCoordinates

@[expose] public section

/-! The normalized tensor actions are literal multiplication in the same
sum-variable polynomial ring as the prepared-family elimination. -/
noncomputable section
namespace Froberg
open Module TensorProduct MvPolynomial
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K]
variable {h n a b c e r t : ℕ}

def sumBiformMap : (Forms K h a ⊗[K] Forms K n c) →ₗ[K] MvPolynomial (Fin h ⊕ Fin n) K :=
  (tensorEquivSum K (Fin h) (Fin n) K).toLinearMap.comp
    (TensorProduct.map (Forms K h a).subtype (Forms K n c).subtype)

@[simp] theorem sumBiformMap_tmul (x : Forms K h a) (y : Forms K n c) :
    sumBiformMap (x ⊗ₜ[K] y)=rename Sum.inl x.val*rename Sum.inr y.val := by
  simp [sumBiformMap,tensorEquivSum_tmul]

theorem sumBiformMap_injective : Function.Injective (sumBiformMap (K := K) (h := h) (n := n) (a := a) (c := c)) :=
  (tensorEquivSum K (Fin h) (Fin n) K).injective.comp
    (TensorProduct.map_injective_of_flat_flat _ _
      (Forms K h a).injective_subtype (Forms K n c).injective_subtype)

theorem sumBiformMap_range :
    (sumBiformMap (K := K) (h := h) (n := n) (a := a) (c := c)).range=
      biformImage (Forms K h a) (Forms K n c) := by
  rw [sumBiformMap,LinearMap.range_comp]
  rfl

theorem sumBiformMap_degree_equiv (hx : a+b=r) (hy : e+c=t)
    (z : Forms K h (a+b) ⊗[K] Forms K n (e+c)) :
    sumBiformMap (tensorDegreeEquiv hx hy z)=sumBiformMap z := by
  subst r
  subst t
  induction z using TensorProduct.inductionOn with
  | tmul x y => simp [tensorDegreeEquiv,formDegreeEquiv]
  | add x y hx hy => simp only [map_add,hx,hy]

/-- The common-target tensor action is actual polynomial multiplication. -/
theorem sumBiformMap_action (hx : a+b=r) (hy : e+c=t)
    (p : Forms K h a ⊗[K] Forms K n c) (v : Forms K h b ⊗[K] Forms K n e) :
    sumBiformMap (biformAction hx hy p v)=sumBiformMap p*sumBiformMap v := by
  change sumBiformMap (tensorDegreeEquiv hx hy (tensorFormProduct (gradedMultiplication (d := a) (e := b)) p v))=_
  rw [sumBiformMap_degree_equiv]
  induction p using TensorProduct.inductionOn with
  | tmul x y =>
    induction v using TensorProduct.inductionOn with
    | tmul z u =>
      rw [tensorFormProduct_tmul,sumBiformMap_tmul,sumBiformMap_tmul,sumBiformMap_tmul]
      change rename Sum.inl (x.val*z.val)*rename Sum.inr (u.val*y.val)=_
      simp only [map_mul]
      ring
    | add x y hx hy => simp only [map_add,hx,hy,mul_add]
  | add x y hx hy => simp only [map_add,LinearMap.add_apply,hx,hy,add_mul]

/-- Every actual coefficient satisfying the homogeneous biform constraints
has a tensor preimage. -/
theorem exists_sumBiformMap_of_homogeneous {f : MvPolynomial (Fin h ⊕ Fin n) K}
    (hf : f.IsHomogeneous (a+c))
    (ha : f.IsWeightedHomogeneous (Sum.elim (fun _ => 1) (fun _ => 0)) a) :
    ∃ z : Forms K h a ⊗[K] Forms K n c,sumBiformMap z=f := by
  have hm := mem_biformImage_of_homogeneous hf ha
  rw [← sumBiformMap_range] at hm
  exact hm

end Froberg
