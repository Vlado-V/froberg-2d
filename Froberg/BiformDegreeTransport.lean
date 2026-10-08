import Froberg.ScalarBiformParameter
import Froberg.BiformActionPolynomial

/-! Degree transports and the right-hand degree-zero tensor unit preserve
literal polynomial embeddings. -/
noncomputable section
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m a b c e : ℕ}

def biformDegreeTransport (ha : a=b) (hc : c=e) :
    (Forms K h a ⊗[K] Forms K m c) ≃ₗ[K] (Forms K h b ⊗[K] Forms K m e) :=
  TensorProduct.congr (formDegreeEquiv ha) (formDegreeEquiv hc)

@[simp] theorem sumBiformMap_degreeTransport (ha : a=b) (hc : c=e)
    (v : Forms K h a ⊗[K] Forms K m c) :
    sumBiformMap (biformDegreeTransport ha hc v)=sumBiformMap v := by
  subst b
  subst e
  induction v using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add,hx,hy]

def rightScalarBiformEquiv : Forms K h a ≃ₗ[K] (Forms K h a ⊗[K] Forms K m 0) :=
  (TensorProduct.rid K (Forms K h a)).symm.trans
    (TensorProduct.congr (LinearEquiv.refl K (Forms K h a)) (constantFormEquiv (h := m)))

@[simp] theorem rightScalarBiformEquiv_apply (v : Forms K h a) :
    rightScalarBiformEquiv (m := m) v=v ⊗ₜ[K] constantFormEquiv (h := m) (1 : K) := by
  simp only [rightScalarBiformEquiv,LinearEquiv.trans_apply,TensorProduct.rid_symm_apply,
    TensorProduct.congr_tmul,LinearEquiv.refl_apply]

@[simp] theorem sumBiformMap_rightScalar (v : Forms K h a) :
    sumBiformMap (rightScalarBiformEquiv (m := m) v)=rename Sum.inl v.val := by
  rw [rightScalarBiformEquiv_apply,sumBiformMap_tmul]
  change rename Sum.inl v.val*rename Sum.inr (C (1 : K))=_
  simp

end Froberg
