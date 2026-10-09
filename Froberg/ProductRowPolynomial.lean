module

public import Froberg.ProductRowOpen

@[expose] public section

/-! Polynomial dependence of the complete product-row linear map. -/
noncomputable section
namespace Froberg.ProductRows
open Froberg Module MvPolynomial Quartic
variable {K : Type} [Field K]
variable {ι σ U : Type*} [AddCommGroup U] [Module K U] [FiniteDimensional K U]

/-- The same coefficient parameters control every column of the linear map. -/
theorem product_row_polynomial (counts : ℕ → ℕ) (L : U →ₗ[K] MvPolynomial σ K)
    (q : (j : ℕ) → Fin (counts j) → (ι → K) → U) (J : Finset ℕ) (R : ℕ)
    (hq : ∀ j∈J,∀ i,IsPolynomialFamily (q j i)) :
    IsPolynomialFamily (fun a => multiplication counts (fun j i => L (q j i a)) J R) := by
  classical
  apply isPolynomialFamily_linearMap
  intro x
  have hsum := IsPolynomialFamily.sum (fun p : (r : Row J R) × Columns counts r =>
    (isPolynomialFamily_const (x p)).smul (products_polynomial counts L q hq p.1 p.2))
  convert hsum using 1
  funext a
  exact Finsupp.sum_fintype _ _ (fun _ => zero_smul _ _)

end Froberg.ProductRows
