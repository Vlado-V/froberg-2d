module

public import Froberg.BiformWitnesses

@[expose] public section

/-! Output constraints survive adjoining scalar variables and renaming
within the two variable blocks. -/
noncomputable section
namespace Froberg
open MvPolynomial TensorProduct
variable {K : Type} [Field K] [Infinite K]
variable {σ τ σ' τ' X : Type*} [AddCommGroup X] [Module K X]

/-- Apply an output-space linear map coefficientwise in the scalar variables. -/
def biformOutputMap (T : MvPolynomial σ K →ₗ[K] X) :
    MvPolynomial (σ ⊕ τ) K →ₗ[K] X ⊗[K] MvPolynomial τ K :=
  (TensorProduct.map T LinearMap.id).comp
    (MvPolynomial.tensorEquivSum K σ τ K).symm.toLinearMap

@[simp] theorem biformOutputMap_tmul (T : MvPolynomial σ K →ₗ[K] X)
    (a : MvPolynomial σ K) (b : MvPolynomial τ K) :
    biformOutputMap T (rename Sum.inl a * rename Sum.inr b) = T a ⊗ₜ[K] b := by
  rw [← tensorEquivSum_tmul]
  simp [biformOutputMap]

/-- Every polynomial in a tensor image satisfies every imposed output
constraint on its first factor. -/
theorem biformImage_le_output_kernel (T : MvPolynomial σ K →ₗ[K] X)
    (O : Submodule K (MvPolynomial σ K)) (C : Submodule K (MvPolynomial τ K))
    (hO : O ≤ T.ker) : biformImage O C ≤ (biformOutputMap (τ := τ) T).ker := by
  rintro p ⟨a,⟨z,rfl⟩,rfl⟩
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    change biformOutputMap T (MvPolynomial.tensorEquivSum K σ τ K (a.val ⊗ₜ[K] b.val)) = 0
    rw [tensorEquivSum_tmul,biformOutputMap_tmul,hO a.property,zero_tmul]
  | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb

theorem mul_mem_biformImage (O : Submodule K (MvPolynomial σ K))
    (C : Submodule K (MvPolynomial τ K)) {a : MvPolynomial σ K} {b : MvPolynomial τ K}
    (ha : a ∈ O) (hb : b ∈ C) :
    rename Sum.inl a * rename Sum.inr b ∈ biformImage O C := by
  refine ⟨a ⊗ₜ[K] b,?_,tensorEquivSum_tmul a b⟩
  exact ⟨(⟨a,ha⟩ : O) ⊗ₜ[K] (⟨b,hb⟩ : C),rfl⟩

/-- Independent renamings in the two blocks preserve the tensor-image
membership used to impose quadratic output constraints. -/
theorem biformImage_rename (f : σ → σ') (g : τ → τ')
    (O : Submodule K (MvPolynomial σ K)) (C : Submodule K (MvPolynomial τ K)) :
    (biformImage O C).map (rename (Sum.map f g)).toLinearMap ≤
      biformImage (O.map (rename f).toLinearMap) (C.map (rename g).toLinearMap) := by
  rintro p ⟨a,⟨b,⟨z,rfl⟩,rfl⟩,rfl⟩
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    change rename (Sum.map f g) (MvPolynomial.tensorEquivSum K σ τ K (a.val ⊗ₜ[K] b.val)) ∈ _
    rw [tensorEquivSum_tmul,map_mul,rename_rename,rename_rename]
    have h := mul_mem_biformImage (O.map (rename f).toLinearMap) (C.map (rename g).toLinearMap)
      (a := rename f a.val) (b := rename g b.val) ⟨a.val,a.property,rfl⟩ ⟨b.val,b.property,rfl⟩
    simpa only [rename_rename,Function.comp_def,Sum.map_inl,Sum.map_inr] using h
  | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb

end Froberg
