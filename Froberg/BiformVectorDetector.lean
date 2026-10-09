module

public import Froberg.BiformOutputConstraint
public import Froberg.PrivateMixedRow

@[expose] public section

/-! A linear output detector applied coefficientwise to actual biforms. -/
noncomputable section
namespace Froberg
open MvPolynomial TensorProduct Module
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} {n c h t : ℕ}

def biformVectorDetector (T : MvPolynomial σ K →ₗ[K] (Fin c → K)) :
    MvPolynomial (σ ⊕ Fin n) K →ₗ[K] (Fin c → Poly K n) :=
  LinearMap.pi fun k => ((TensorProduct.lid K (Poly K n)).toLinearMap.comp
    (TensorProduct.map (LinearMap.proj k) (LinearMap.id : Poly K n →ₗ[K] Poly K n))).comp
      (biformOutputMap T)

@[simp] theorem biformVectorDetector_tmul (T : MvPolynomial σ K →ₗ[K] (Fin c → K))
    (a : MvPolynomial σ K) (b : Poly K n) (k : Fin c) :
    biformVectorDetector T (rename Sum.inl a*rename Sum.inr b) k=T a k • b := by
  simp only [biformVectorDetector,LinearMap.pi_apply,LinearMap.comp_apply,
    biformOutputMap_tmul,TensorProduct.map_tmul,LinearMap.proj_apply,
    LinearMap.id_apply,LinearEquiv.coe_coe,TensorProduct.lid_tmul]

theorem biformVectorDetector_polynomialVector
    (T : MvPolynomial σ K →ₗ[K] (Fin c → K))
    (o : Fin h → MvPolynomial σ K) (p : Fin h → Poly K n) (k : Fin c) :
    biformVectorDetector T (polynomialVector o p) k=∑ j,T (o j) k • p j := by
  simp only [polynomialVector_apply,map_sum,Finset.sum_apply,biformVectorDetector_tmul]

theorem biformVectorDetector_homogeneous
    (T : MvPolynomial σ K →ₗ[K] (Fin c → K))
    (O : Submodule K (MvPolynomial σ K))
    {p : MvPolynomial (σ ⊕ Fin n) K} (hp : p∈biformImage O (Forms K n t)) (k : Fin c) :
    (biformVectorDetector T p k).IsHomogeneous t := by
  rcases hp with ⟨_,⟨z,rfl⟩,rfl⟩
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    change (biformVectorDetector T (tensorEquivSum K σ (Fin n) K (a.val ⊗ₜ[K] b.val)) k).IsHomogeneous t
    rw [tensorEquivSum_tmul,biformVectorDetector_tmul]
    exact Submodule.smul_mem _ _ b.property
  | add a b ha hb =>
    simpa only [map_add,Pi.add_apply] using ha.add hb

theorem biformVectorDetector_eq_zero
    (T : MvPolynomial σ K →ₗ[K] (Fin c → K))
    (O : Submodule K (MvPolynomial σ K)) (C : Submodule K (Poly K n))
    (hO : O≤T.ker) {p : MvPolynomial (σ ⊕ Fin n) K} (hp : p∈biformImage O C) :
    biformVectorDetector T p=0 := by
  have hz : biformOutputMap T p=0 := biformImage_le_output_kernel T O C hO hp
  funext k
  change (TensorProduct.lid K (Poly K n))
    (TensorProduct.map (LinearMap.proj k) (LinearMap.id : Poly K n →ₗ[K] Poly K n)
      (biformOutputMap T p))=0
  rw [hz,map_zero,map_zero]

/-- Scalar multiplication in the second variable block commutes with an
arbitrary linear output detector. -/
theorem biformVectorDetector_scalar_mul
    (T : MvPolynomial σ K →ₗ[K] (Fin c → K))
    (f : Poly K n) (p : MvPolynomial (σ ⊕ Fin n) K) (k : Fin c) :
    biformVectorDetector T (rename Sum.inr f*p) k=f*biformVectorDetector T p k := by
  obtain ⟨z,rfl⟩ := (tensorEquivSum K σ (Fin n) K).surjective p
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [tensorEquivSum_tmul]
    have he : rename Sum.inr f*(rename Sum.inl a*rename Sum.inr b)=
        rename Sum.inl a*rename Sum.inr (f*b) := by rw [map_mul];ring
    rw [he,biformVectorDetector_tmul,biformVectorDetector_tmul,mul_smul_comm]
  | add a b ha hb =>
    simpa only [map_add,mul_add,Pi.add_apply] using congrArg₂ HAdd.hAdd ha hb

end Froberg
