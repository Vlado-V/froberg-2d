import Froberg.EvenRowWithVectorsOpen
import Froberg.SparseEmbeddedRelations

/-! The same finite even-row witness satisfies all prescribed private-output
quotient injections. The vector tuple is chosen only once. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Froberg
open Module MvPolynomial AttachedMultiplication Quartic.PolynomialBilinearCoordinates
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ]
variable {n s d R h H m r b : ℕ}
variable {I : Type*} [Fintype I]

/-- All parts of a finite even-row witness use the same actual scalar list. -/
theorem exists_even_polynomial_row_with_relations
    (hn : 0<n) (hh : 0<h)
    (w : σ → ℕ) (Yhalf : Finset (Fin n))
    (o : Fin H → MvPolynomial σ K) (ho : LinearIndependent K o)
    (hdegree : ∀ j,(o j).IsHomogeneous R)
    (L : (Fin h → K) →ₗ[K] (Fin H → K)) (hL : Function.Injective L)
    (hLodd : ∀ z,retainMonomials (fun a => Finsupp.weight w a%2=0) (outputCombination o (L z))=0)
    (e : Fin m → Fin n →₀ ℕ) (he : ∀ i,(e i).degree=s)
    (hdiv : ∀ β : Fin n →₀ ℕ,Fintype.card {i : Fin m // e i≤β}≤b*β.degree.choose s)
    (Relations : I → Submodule K (Fin H → K))
    (hrelations : ∀ i,b*(s+1).choose s≤h-finrank K (Relations i))
    (hcap : b*(s+d).choose s≤h)
    (hcount : h*(s+d).choose s * (r+h*(n+s-1).choose s+(h*2^h)*(n+(d-1)-1).choose (d-1)) ≤
      (h-b*(s+d).choose s)*(n+s+d-1).choose d)
    (counts : ℕ → ℕ)
    (q : (j : ℕ) → Fin (counts j) → MvPolynomial (σ ⊕ Fin n) K)
    (J : Finset ℕ) (heven : ∀ j∈J,Even j) (hJ : ∀ j∈J,j≤d)
    (hqX : ∀ j∈J,∀ i,(q j i).IsWeightedHomogeneous
      (Sum.elim w (fun _ : Fin n => 0)) (ProductRows.assignedDegree R j))
    (hqY : ∀ j∈J,∀ i,(q j i).IsWeightedHomogeneous
      (Sum.elim (fun _ : σ => 0) (ProductRows.halfWeight Yhalf))
      (ProductRows.assignedScalarDegree R d j))
    (hproducts : Function.Injective (ProductRows.multiplication counts q J R))
    (hscalarOpen : ∃ D : MvPolynomial (Fin (finrank K (Fin r → Forms K n d))) K,
      (∃ Q : Fin r → Forms K n d,eval (coordinates K _ Q) D≠0) ∧
      ∀ Q : Fin r → Forms K n d,eval (coordinates K _ Q) D≠0 →
        Function.Injective (ProjectedPrefix.multiplication
          (parityProfileRetained Yhalf (d%2) (2*((d-R/2)/2))) Q s)) :
    ∃ (v : Fin m → Fin h → K) (Q : Fin r → Forms K n d),
        (∀ i c,c≤1 → ∀ p : Fin m → Forms K n c,
          (∀ β,sparseOutputCoefficient e (fun j => L (v j)) p β∈Relations i) → p=0) ∧
        (∀ i,(attachedPolynomialFamily o e (fun i => L (v i)) i).IsHomogeneous (R+s)) ∧
        Function.Injective (homogeneousMultiplication (d := 0) e (fun i => L (v i)) he) ∧
        (∀ c≤d,Function.Injective (homogeneousMultiplication (d := c) e (fun i => L (v i)) he)) ∧
        (addRow (polynomialIntermediateRow o e (fun i => L (v i)) he Q)
          (ProductRows.multiplication counts q J R)).ker =
          ((LinearMap.inl K
            ((Fin r → Fin H → Forms K n s) × (Fin m → Forms K n d))
            ((Σ j : ProductRows.Row J R, ProductRows.Columns counts j) →₀ K)).comp
            (intermediateKoszul e (fun i => L (v i)) he Q)).range := by
  obtain ⟨D,hD,hgood⟩ := sparse_embedded_relations_open (d := 1) L hL Relations e he hdiv hrelations
  obtain ⟨v,Q,hv,hhom,hzero,hfull,hker⟩ := exists_even_polynomial_row_in_open
    hn hh w Yhalf o ho hdegree L hL hLodd e he hdiv D hD hcap hcount
    counts q J heven hJ hqX hqY hproducts hscalarOpen
  exact ⟨v,Q,hgood v hv,hhom,hzero,hfull,hker⟩

end Froberg
