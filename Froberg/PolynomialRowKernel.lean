module

public import Froberg.BiformOutputProjection
public import Froberg.ProductScalarSeparation
public import Froberg.SeparatedRowKernel

@[expose] public section

/-! The scalar-profile and output-parity projections remove the entire formal
product block from an actual polynomial relation. -/
noncomputable section
namespace Froberg.ProductRows
open Froberg MvPolynomial Module
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n : ℕ}

/-- Even output half-degrees of all product blocks are fixed by the same
output projection, irrespective of their scalar profiles. -/
theorem product_row_even_projection (w : σ → ℕ) (e : ℕ → ℕ)
    (q : (j : ℕ) → Fin (e j) → MvPolynomial (σ ⊕ Fin n) K)
    {J : Finset ℕ} {R : ℕ} (heven : ∀ j∈J,Even j)
    (hq : ∀ j∈J,∀ i,(q j i).IsWeightedHomogeneous
      (Sum.elim w (fun _ : Fin n => 0)) (assignedDegree R j)) :
    (biformOutputEndomorphism (retainMonomials (fun a => Finsupp.weight w a%2=0))).comp
      (multiplication e q J R) = multiplication e q J R := by
  rw [multiplication,← Finsupp.linearCombination_linear_comp]
  congr 1
  funext x
  change biformOutputEndomorphism (retainMonomials (fun a => Finsupp.weight w a%2=0))
    (products e q x.1 x.2)=products e q x.1 x.2
  rw [biformOutputEndomorphism_retain]
  simp_rw [outputExponent_weight]
  rw [retainMonomials_weighted _ (fun k : ℕ => k%2=0) (products_weighted e q _ heven hq x.1 x.2)]
  have hev := heven x.1.val.val x.1.property.1
  obtain ⟨k,hk⟩ := hev
  rw [if_pos (by omega)]

/-- Adjoining all formal products preserves the exact scalar/new-layer kernel.
The hypotheses on the new layer require only its explicit odd output support. -/
theorem polynomial_row_kernel
    {A B U : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U]
    (w : σ → ℕ) (Yhalf : Finset (Fin n)) (e : ℕ → ℕ)
    (q : (j : ℕ) → Fin (e j) → MvPolynomial (σ ⊕ Fin n) K)
    {J : Finset ℕ} {R d t r : ℕ} (heven : ∀ j∈J,Even j) (hdegree : ∀ j∈J,j≤d)
    (hqX : ∀ j∈J,∀ i,(q j i).IsWeightedHomogeneous
      (Sum.elim w (fun _ : Fin n => 0)) (assignedDegree R j))
    (hqY : ∀ j∈J,∀ i,(q j i).IsWeightedHomogeneous
      (Sum.elim (fun _ : σ => 0) (halfWeight Yhalf)) (assignedScalarDegree R d j))
    (hproducts : Function.Injective (multiplication e q J R))
    (f : Fin r → Forms K n d)
    (hf : Function.Injective (ProjectedPrefix.multiplication
      (parityProfileRetained Yhalf (d%2) (2*((d-R/2)/2))) f t))
    (S : A →ₗ[K] MvPolynomial (σ ⊕ Fin n) K)
    (E : B →ₗ[K] MvPolynomial (σ ⊕ Fin n) K)
    (hS : S.range≤biformImage (homogeneousSubmodule σ K R) (familySpace f*Forms K n t))
    (hE : ∀ b, biformOutputEndomorphism
      (retainMonomials (fun a => Finsupp.weight w a%2=0)) (E b)=0)
    (Z : U →ₗ[K] (A × B)) (hZ : (addRow S E).ker=Z.range) :
    (addRow (addRow S E) (multiplication e q J R)).ker =
      ((LinearMap.inl K (A × B) ((Σ j : Row J R, Columns e j) →₀ K)).comp Z).range := by
  apply addRow_kernel_eq_mandatory S E (multiplication e q J R)
    (biformImage (homogeneousSubmodule σ K R) (familySpace f*Forms K n t))
    (biformOutputEndomorphism (retainMonomials (fun a => Finsupp.weight w a%2=0))) hS
  · intro x hx
    apply biformOutputEndomorphism_preserves _ _ _ _ hx
    intro a ha
    exact retainMonomials_preserves_homogeneous _ ha
  · apply LinearMap.ext
    intro b
    exact hE b
  · exact product_row_even_projection w e q heven hqX
  · exact scalar_product_disjoint_product_row Yhalf e q heven hdegree hqY _ f hf
  · exact hproducts
  · exact hZ

end Froberg.ProductRows
