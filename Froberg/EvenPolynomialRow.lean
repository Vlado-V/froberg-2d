import Froberg.PolynomialOutputImage
import Froberg.PolynomialRowKernel
import Froberg.IntermediateOutputEmbedding
import Froberg.ScalarVectorInjection

/-! The complete even polynomial row: common scalars, a sparse new layer,
and all formal products. Its only kernel is the literal constant Koszul source. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Froberg
open Module MvPolynomial AttachedMultiplication
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ]
variable {n s d R h H m r : ℕ}

/-- Combine the two independent detections and the free-output extension in
the actual ambient polynomial ring. -/
theorem even_polynomial_row_kernel
    (w : σ → ℕ) (Yhalf : Finset (Fin n))
    (o : Fin H → MvPolynomial σ K) (ho : LinearIndependent K o)
    (hdegree : ∀ j,(o j).IsHomogeneous R)
    (L : (Fin h → K) →ₗ[K] (Fin H → K)) (hL : Function.Injective L)
    (hLodd : ∀ z,retainMonomials (fun a => Finsupp.weight w a%2=0) (outputCombination o (L z))=0)
    (e : Fin m → Fin n →₀ ℕ) (v : Fin m → Fin h → K) (he : ∀ i,(e i).degree=s)
    (Q : Fin r → Forms K n d)
    (hE : Function.Injective (AttachedMultiplication.multiplication (d := d) e v))
    (hQ : Function.Injective (BilinearScalarFamily.multiplication (quotientMultiply e v he) Q))
    (counts : ℕ → ℕ)
    (q : (j : ℕ) → Fin (counts j) → MvPolynomial (σ ⊕ Fin n) K)
    (J : Finset ℕ) (heven : ∀ j∈J,Even j) (hJ : ∀ j∈J,j≤d)
    (hqX : ∀ j∈J,∀ i,(q j i).IsWeightedHomogeneous
      (Sum.elim w (fun _ : Fin n => 0)) (ProductRows.assignedDegree R j))
    (hqY : ∀ j∈J,∀ i,(q j i).IsWeightedHomogeneous
      (Sum.elim (fun _ : σ => 0) (ProductRows.halfWeight Yhalf))
      (ProductRows.assignedScalarDegree R d j))
    (hproducts : Function.Injective (ProductRows.multiplication counts q J R))
    (hscalar : Function.Injective (ProjectedPrefix.multiplication
      (parityProfileRetained Yhalf (d%2) (2*((d-R/2)/2))) Q s)) :
    (addRow (polynomialIntermediateRow o e (fun i => L (v i)) he Q)
      (ProductRows.multiplication counts q J R)).ker =
      ((LinearMap.inl K
        ((Fin r → Fin H → Forms K n s) × (Fin m → Forms K n d))
        ((Σ j : ProductRows.Row J R, ProductRows.Columns counts j) →₀ K)).comp
        (intermediateKoszul e (fun i => L (v i)) he Q)).range := by
  have hfree := vector_scalar_injective_of_projected (J := Fin H)
    (parityProfileRetained Yhalf (d%2) (2*((d-R/2)/2))) Q hscalar
  have hkernel := intermediateRow_ker_output_embedding L hL e v he Q hE hQ hfree
  have hpoly : (polynomialIntermediateRow o e (fun i => L (v i)) he Q).ker =
      (intermediateKoszul e (fun i => L (v i)) he Q).range := by
    rw [← hkernel]
    ext x
    change polynomialFormVector o (s+d) (intermediateRow e (fun i => L (v i)) he Q x)=0 ↔
      intermediateRow e (fun i => L (v i)) he Q x=0
    exact (polynomialFormVector_injective o ho).eq_iff' (map_zero _)
  rw [polynomialIntermediateRow_eq_addRow] at hpoly ⊢
  apply ProductRows.polynomial_row_kernel w Yhalf counts q heven hJ hqX hqY
    hproducts Q hscalar (polynomialScalarRow o Q) (polynomialLayerRow o e (fun i => L (v i)) he)
  · exact polynomialScalarRow_range o (homogeneousSubmodule σ K R) hdegree Q
  · intro p
    exact polynomialLayerRow_output_zero o e (fun i => L (v i)) he
      (retainMonomials (fun a => Finsupp.weight w a%2=0)) (fun i => hLodd (v i)) p
  · exact hpoly

end Froberg
