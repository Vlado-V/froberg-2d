module

public import Froberg.BiformOutputConstraint
public import Froberg.ProductRowProfiles

@[expose] public section

/-! Scalar profiles survive arbitrary linear combinations in the complete
product image of a biform subspace. -/
noncomputable section
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] [Infinite K] {σ τ : Type*}

theorem biformImage_product_le
    (O O' : Submodule K (MvPolynomial σ K)) (C C' : Submodule K (MvPolynomial τ K)) :
    biformImage O C*biformImage O' C'≤biformImage (O*O') (C*C') := by
  apply Submodule.mul_le.mpr
  rintro _ ⟨_,⟨x,rfl⟩,rfl⟩ _ ⟨_,⟨y,rfl⟩,rfl⟩
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | tmul a' b' =>
      change tensorEquivSum K σ τ K (a.val ⊗ₜ[K] b.val)*
        tensorEquivSum K σ τ K (a'.val ⊗ₜ[K] b'.val)∈_
      rw [tensorEquivSum_tmul,tensorEquivSum_tmul]
      have he : rename Sum.inl a.val*rename Sum.inr b.val*
          (rename Sum.inl a'.val*rename Sum.inr b'.val)=
          rename Sum.inl (a.val*a'.val)*rename Sum.inr (b.val*b'.val) := by
        rw [map_mul,map_mul]
        ring
      rw [he]
      exact mul_mem_biformImage _ _ (Submodule.mul_mem_mul a.property a'.property)
        (Submodule.mul_mem_mul b.property b'.property)
    | add y z hy hz =>
      simpa only [map_add,mul_add] using Submodule.add_mem (biformImage (O*O') (C*C')) hy hz
  | add x y hx hy =>
    simpa only [map_add,add_mul] using Submodule.add_mem (biformImage (O*O') (C*C')) hx hy

variable {n D j r : ℕ}

theorem deletedBidegreeSpace_half_weight (S : Finset (Fin n)) :
    deletedBidegreeSpace K S D j≤weightedHomogeneousSubmodule K (ProductRows.halfWeight S) j := by
  intro f hf a ha
  rw [ProductRows.weight_halfWeight]
  by_contra hn
  exact ha (((mem_deletedBidegreeSpace_iff S j f).mp hf).2 a hn)

theorem biform_pairProducts_single_profile
    (S : Finset (Fin n)) (O : Submodule K (MvPolynomial σ K))
    (C : Submodule K (Poly K n))
    (hC : C*C≤deletedBidegreeSpace K S D j)
    (f : Fin r → MvPolynomial (σ ⊕ Fin n) K) (hf : ∀ i,f i∈biformImage O C) :
    ∀ p,(pairProducts f p).IsWeightedHomogeneous
      (Sum.elim (fun _ : σ => 0) (ProductRows.halfWeight S)) j := by
  intro p
  induction p using Sym2.inductionOn with
  | _ a b =>
    apply biformImage_right_weight (ProductRows.halfWeight S) (O*O) (C*C)
      (hC.trans (deletedBidegreeSpace_half_weight S))
    exact biformImage_product_le O O C C (Submodule.mul_mem_mul (hf a) (hf b))

end Froberg
