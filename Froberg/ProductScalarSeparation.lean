import Froberg.BiformScalarProjection
import Froberg.ProductRowProfiles
import Froberg.ParityProfileScalar

/-! The actual common scalar image is disjoint from the entire formal
product image in B.4. -/
noncomputable section
namespace Froberg
open MvPolynomial Module
variable {K : Type} [Field K] {σ : Type*}

@[simp] theorem scalarExponent_weight {n : ℕ} [Fintype σ]
    (w : Fin n → ℕ) (a : (σ ⊕ Fin n) →₀ ℕ) :
    Finsupp.weight w (scalarExponent a) =
      Finsupp.weight (Sum.elim (fun _ : σ => 0) w) a := by
  simp [Finsupp.weight_eq_sum,Fintype.sum_sum_type,scalarExponent]

/-- A removed scalar half-degree is killed coefficientwise even when all
output variables remain present. -/
theorem biform_profile_zero {n k p j : ℕ} [Fintype σ]
    (S : Finset (Fin n)) (f : MvPolynomial (σ ⊕ Fin n) K)
    (hf : f.IsWeightedHomogeneous (Sum.elim (fun _ : σ => 0) (ProductRows.halfWeight S)) k)
    (hk : k%2=p ∨ k=j) :
    biformScalarMap (retainMonomials (parityProfileRetained S p j)) f=0 := by
  rw [biformScalarMap_retain]
  ext a
  rw [coeff_retainMonomials]
  by_cases hP : parityProfileRetained S p j (scalarExponent a)
  · rw [if_pos hP]
    by_contra hc
    have h := hf hc
    rw [← scalarExponent_weight,ProductRows.weight_halfWeight] at h
    rcases hk with hk | hk
    · exact hP.1 (h ▸ hk)
    · exact hP.2 (h ▸ hk)
  · simp [hP]

namespace ProductRows

/-- Product half-profiles are annihilated by the same coefficientwise
scalar projection used to make the common scalar family injective. -/
theorem product_range_le_biform_scalar_kernel {n : ℕ} [Fintype σ]
    (S : Finset (Fin n)) (e : ℕ → ℕ)
    (q : (j : ℕ) → Fin (e j) → MvPolynomial (σ ⊕ Fin n) K)
    {J : Finset ℕ} {R d : ℕ} (heven : ∀ j∈J, Even j) (hdegree : ∀ j∈J,j≤d)
    (hq : ∀ j∈J, ∀ i, (q j i).IsWeightedHomogeneous
      (Sum.elim (fun _ : σ => 0) (halfWeight S)) (assignedScalarDegree R d j)) :
    (multiplication e q J R).range ≤
      (biformScalarMap (σ := σ) (retainMonomials (K := K)
        (parityProfileRetained S (d%2) (2*((d-R/2)/2))))).ker := by
  rw [multiplication,Finsupp.range_linearCombination]
  apply Submodule.span_le.mpr
  rintro f ⟨⟨r,c⟩,rfl⟩
  apply biform_profile_zero S _ (products_scalar_weighted e q _ hq r c)
  split_ifs with h
  · right
    have hj := r.property.2.2
    have heq : r.val.val=R/2 := by omega
    simp [heq]
  · left
    have hjd := hdegree _ r.property.1
    obtain ⟨k,hk⟩ := heven _ r.property.1
    omega

/-- Exact disjointness of the common scalar product space and all product
blocks, with arbitrary output coefficients on the scalar side. -/
theorem scalar_product_disjoint_product_row {n : ℕ} [Fintype σ] [Infinite K]
    (S : Finset (Fin n)) (e : ℕ → ℕ)
    (q : (j : ℕ) → Fin (e j) → MvPolynomial (σ ⊕ Fin n) K)
    {J : Finset ℕ} {R d t r : ℕ}
    (heven : ∀ j∈J, Even j) (hdegree : ∀ j∈J,j≤d)
    (hq : ∀ j∈J, ∀ i, (q j i).IsWeightedHomogeneous
      (Sum.elim (fun _ : σ => 0) (halfWeight S)) (assignedScalarDegree R d j))
    (O : Submodule K (MvPolynomial σ K)) (f : Fin r → Forms K n d)
    (hf : Function.Injective (ProjectedPrefix.multiplication
      (parityProfileRetained S (d%2) (2*((d-R/2)/2))) f t)) :
    Disjoint (biformImage O (familySpace f * Forms K n t)) (multiplication e q J R).range := by
  have hs := biformImage_disjoint_scalar_kernel O (familySpace f * Forms K n t)
    (retainMonomials (parityProfileRetained S (d%2) (2*((d-R/2)/2))))
    (ProjectedPrefix.scalar_product_disjoint_kernel _ f hf)
  exact hs.mono_right (product_range_le_biform_scalar_kernel S e q heven hdegree hq)

end ProductRows
end Froberg
