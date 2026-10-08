import Quartic.FiniteEndpointCertificate

/-! Sparse product rows reconstructed from original generator supports and a
checked monomial-product lookup. No expanded quartic-row table is required. -/
namespace Quartic.FiniteEndpointProductRows

variable {n b₂ b₄ r s : ℕ}

/-- The literal sparse row for a selected generator times a selected monomial. -/
def rows (productIndex : Fin b₂ → Fin b₂ → Fin b₄)
    (support : Fin r → List (Fin b₂)) (selected : Fin s → Fin r × Fin b₂)
    (i : Fin s) : List (Fin b₄) :=
  (support (selected i).1).map (fun j => productIndex j (selected i).2)

/-- Checking the monomial-product lookup suffices for every polynomial support
identity used by the finite endpoint certificate. Repeated entries are retained. -/
theorem product_supports
    (E₂ : Fin b₂ → Fin n →₀ ℕ) (E₄ : Fin b₄ → Fin n →₀ ℕ)
    (productIndex : Fin b₂ → Fin b₂ → Fin b₄)
    (hprod : ∀ i j, E₄ (productIndex i j) = E₂ i + E₂ j)
    (support : Fin r → List (Fin b₂)) (selected : Fin s → Fin r × Fin b₂)
    (i : Fin s) :
    (rows productIndex support selected i).map E₄ =
      (support (selected i).1).map (fun j => E₂ j + E₂ (selected i).2) := by
  simp only [rows,List.map_map,Function.comp_def,hprod]

/-- Natural-number table entries become genuine monomial indices only after a
checked range bound; out-of-range values are never silently truncated. -/
def boundedIndex (productIndex : Fin b₂ → Fin b₂ → ℕ)
    (hbound : ∀ i j, productIndex i j < b₄) (i j : Fin b₂) : Fin b₄ :=
  ⟨productIndex i j,hbound i j⟩

/-- The same support bridge for a compact natural-number product-index table. -/
theorem product_supports_nat
    (E₂ : Fin b₂ → Fin n →₀ ℕ) (E₄ : Fin b₄ → Fin n →₀ ℕ)
    (productIndex : Fin b₂ → Fin b₂ → ℕ)
    (hbound : ∀ i j, productIndex i j < b₄)
    (hprod : ∀ i j, E₄ ⟨productIndex i j,hbound i j⟩ = E₂ i + E₂ j)
    (support : Fin r → List (Fin b₂)) (selected : Fin s → Fin r × Fin b₂)
    (i : Fin s) :
    (rows (boundedIndex productIndex hbound) support selected i).map E₄ =
      (support (selected i).1).map (fun j => E₂ j + E₂ (selected i).2) :=
  product_supports E₂ E₄ (boundedIndex productIndex hbound) hprod support selected i

end Quartic.FiniteEndpointProductRows
