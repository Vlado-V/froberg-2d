module

public import Froberg.SingleProfileProducts
public import Froberg.ScalarProductRow

@[expose] public section

/-! Empty new layers with arbitrary output splitting require only one
retained scalar profile, as in the small-degree appendix. -/
noncomputable section
namespace Froberg
open Module MvPolynomial AttachedMultiplication MonomialExpansion
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n R d s r H j : ℕ}
variable {V : Type*} [AddCommGroup V] [Module K V]

theorem single_profile_scalar_product_row_injective
    (o : Fin H → MvPolynomial σ K) (ho : LinearIndependent K o)
    (hdeg : ∀ i,(o i).IsHomogeneous R)
    (S : Finset (Fin n)) (P : V →ₗ[K] MvPolynomial (σ ⊕ Fin n) K)
    (hP : Function.Injective P)
    (hPY : ∀ p,(P p).IsWeightedHomogeneous
      (Sum.elim (fun _ : σ => 0) (ProductRows.halfWeight S)) j)
    (Q : Fin r → Forms K n d)
    (hQ : Function.Injective (ProjectedPrefix.multiplication
      (fun α => partialDegree S α≠j) Q s)) :
    Function.Injective (addRow (polynomialScalarRow (s := s) o Q) P) := by
  apply addRow_injective_of_disjoint _ _
  · exact (polynomialFormVector_injective o ho).comp
      (vector_scalar_injective_of_projected _ Q hQ)
  · exact hP
  · exact (single_profile_product_disjoint S P hPY
      (homogeneousSubmodule σ K R) Q hQ).mono_left
      (polynomialScalarRow_range o _ hdeg Q)

end Froberg
