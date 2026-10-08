import Froberg.ProductScalarSeparation
import Froberg.PolynomialVectorRows
import Froberg.ScalarVectorInjection

/-! Empty new layers need no output-half condition: scalar-profile
separation alone proves the entire row injective. -/
noncomputable section
namespace Froberg
open Module MvPolynomial AttachedMultiplication
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n R d s r H : ℕ}

/-- Actual scalar and product rows have no kernel when their images are
disjoint and both individual maps are injective. -/
theorem addRow_injective_of_disjoint
    {A B V : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [AddCommGroup V] [Module K V]
    (S : A →ₗ[K] V) (P : B →ₗ[K] V)
    (hS : Function.Injective S) (hP : Function.Injective P)
    (hSP : Disjoint S.range P.range) : Function.Injective (addRow S P) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  rintro ⟨a,b⟩ hab
  change S a+P b=0 at hab
  have hPb : P b∈S.range := by
    rw [eq_neg_of_add_eq_zero_right hab,←map_neg]
    exact ⟨-a,rfl⟩
  have hb0 : P b=0 := Submodule.disjoint_def.mp hSP _ hPb ⟨b,rfl⟩
  have ha0 : S a=0 := by simpa only [hb0,add_zero] using hab
  exact Prod.ext (hS (ha0.trans (map_zero _).symm)) (hP (hb0.trans (map_zero _).symm))

/-- The empty-layer case of B.4 uses only the scalar profiles of products.
It therefore allows the stronger small-degree quadratic output witness. -/
theorem scalar_product_row_injective
    (o : Fin H → MvPolynomial σ K) (ho : LinearIndependent K o)
    (hdeg : ∀ i,(o i).IsHomogeneous R)
    (Yhalf : Finset (Fin n)) (counts : ℕ → ℕ)
    (E : (j : ℕ) → Fin (counts j) → MvPolynomial (σ ⊕ Fin n) K)
    (J : Finset ℕ) (heven : ∀ j∈J,Even j) (hdegree : ∀ j∈J,j≤d)
    (hEY : ∀ j∈J,∀ i,(E j i).IsWeightedHomogeneous
      (Sum.elim (fun _ : σ => 0) (ProductRows.halfWeight Yhalf))
      (ProductRows.assignedScalarDegree R d j))
    (hproducts : Function.Injective (ProductRows.multiplication counts E J R))
    (Q : Fin r → Forms K n d)
    (hQ : Function.Injective (ProjectedPrefix.multiplication
      (parityProfileRetained Yhalf (d%2) (2*((d-R/2)/2))) Q s)) :
    Function.Injective (addRow (polynomialScalarRow (s := s) o Q)
      (ProductRows.multiplication counts E J R)) := by
  apply addRow_injective_of_disjoint _ _
  · exact (polynomialFormVector_injective o ho).comp
      (vector_scalar_injective_of_projected _ Q hQ)
  · exact hproducts
  · exact (ProductRows.scalar_product_disjoint_product_row Yhalf counts E heven
      hdegree hEY (homogeneousSubmodule σ K R) Q hQ).mono_left
      (polynomialScalarRow_range o _ hdeg Q)

end Froberg
