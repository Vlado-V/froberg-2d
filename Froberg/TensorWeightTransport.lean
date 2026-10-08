import Froberg.PairedScalarSeparation

/-! Output half-degree is preserved when adjoining arbitrary scalar
variables. This supplies the distinct-degree tags in Lemma B.4. -/
noncomputable section
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] [Infinite K]
variable {σ τ M : Type*} [AddCommMonoid M]

def leftTensorWeight (w : σ → M) : σ ⊕ τ → M := Sum.elim w (fun _ => 0)

theorem weightedHomogeneous_zero_weight (p : MvPolynomial σ K) :
    p.IsWeightedHomogeneous (fun _ => (0 : M)) 0 := by
  intro a _
  simp [Finsupp.weight_apply]

/-- Tensoring by arbitrary scalar polynomials preserves the output weight. -/
theorem tensorEquivSum_weighted (w : σ → M) {j : M}
    {a : MvPolynomial σ K} (ha : a.IsWeightedHomogeneous w j)
    (b : MvPolynomial τ K) :
    (MvPolynomial.tensorEquivSum K σ τ K (a ⊗ₜ[K] b)).IsWeightedHomogeneous
      (leftTensorWeight w) j := by
  rw [tensorEquivSum_tmul]
  have hl := rename_weightedHomogeneous (K := K) (⟨Sum.inl,Sum.inl_injective⟩ : σ ↪ σ ⊕ τ)
    w (leftTensorWeight w) (fun _ => rfl) ha
  have hr := rename_weightedHomogeneous (K := K) (⟨Sum.inr,Sum.inr_injective⟩ : τ ↪ σ ⊕ τ)
    (fun _ => (0 : M)) (leftTensorWeight w) (fun _ => rfl) (weightedHomogeneous_zero_weight b)
  change (rename Sum.inl a).IsWeightedHomogeneous (leftTensorWeight w) j at hl
  change (rename Sum.inr b).IsWeightedHomogeneous (leftTensorWeight w) 0 at hr
  simpa only [add_zero] using hl.mul hr

/-- The full tensor image, not only its pure tensors, has the prescribed
output half-degree. -/
theorem tensorImage_weighted (w : σ → M) {j : M}
    (O : Submodule K (MvPolynomial σ K)) (C : Submodule K (MvPolynomial τ K))
    (hO : O ≤ weightedHomogeneousSubmodule K w j) :
    (LinearMap.range (TensorProduct.map O.subtype C.subtype)).map
      (MvPolynomial.tensorEquivSum K σ τ K).toLinearMap ≤
      weightedHomogeneousSubmodule K (leftTensorWeight w) j := by
  rintro x ⟨y,⟨z,rfl⟩,rfl⟩
  induction z using TensorProduct.inductionOn with
  | tmul a b => exact tensorEquivSum_weighted w (hO a.property) b.val
  | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb

end Froberg
