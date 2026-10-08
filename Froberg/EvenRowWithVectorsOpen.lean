import Froberg.EvenPolynomialRow
import Froberg.GenericDimensions
import Froberg.SparseIntermediateOpen

/-! A complete finite B.4 witness from the proved sparse budget and retained
scalar open. The scalar list is chosen once for both conditions. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Froberg
open Module MvPolynomial AttachedMultiplication Quartic.PolynomialBilinearCoordinates
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ]
variable {n s d R h H m r b : ℕ}

/-- All parts of a finite even-row witness use the same actual scalar list. -/
theorem exists_even_polynomial_row_in_open
    (hn : 0<n) (hh : 0<h)
    (w : σ → ℕ) (Yhalf : Finset (Fin n))
    (o : Fin H → MvPolynomial σ K) (ho : LinearIndependent K o)
    (hdegree : ∀ j,(o j).IsHomogeneous R)
    (L : (Fin h → K) →ₗ[K] (Fin H → K)) (hL : Function.Injective L)
    (hLodd : ∀ z,retainMonomials (fun a => Finsupp.weight w a%2=0) (outputCombination o (L z))=0)
    (e : Fin m → Fin n →₀ ℕ) (he : ∀ i,(e i).degree=s)
    (hdiv : ∀ β : Fin n →₀ ℕ,Fintype.card {i : Fin m // e i≤β}≤b*β.degree.choose s)
    (Dextra : MvPolynomial (Fin (finrank K (Fin m → Fin h → K))) K)
    (hDextra : ∃ x,eval x Dextra≠0)
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
        eval (coordinates K _ v) Dextra≠0 ∧
        (∀ i,(attachedPolynomialFamily o e (fun i => L (v i)) i).IsHomogeneous (R+s)) ∧
        Function.Injective (homogeneousMultiplication (d := 0) e (fun i => L (v i)) he) ∧
        (∀ c≤d,Function.Injective (homogeneousMultiplication (d := c) e (fun i => L (v i)) he)) ∧
        (addRow (polynomialIntermediateRow o e (fun i => L (v i)) he Q)
          (ProductRows.multiplication counts q J R)).ker =
          ((LinearMap.inl K
            ((Fin r → Fin H → Forms K n s) × (Fin m → Forms K n d))
            ((Σ j : ProductRows.Row J R, ProductRows.Columns counts j) →₀ K)).comp
            (intermediateKoszul e (fun i => L (v i)) he Q)).range := by
  obtain ⟨v,hvextra,hv,hpos,hinj,P,hP,hPQ⟩ :=
    exists_sparse_intermediate_in_open hn hh e he hdiv hcap hcount Dextra hDextra
  obtain ⟨D,hD,hDQ⟩ := hscalarOpen
  have hP' : ∃ a,eval a P≠0 := by obtain ⟨Q,hQ⟩ := hP; exact ⟨coordinates K _ Q,hQ⟩
  have hD' : ∃ a,eval a D≠0 := by obtain ⟨Q,hQ⟩ := hD; exact ⟨coordinates K _ Q,hQ⟩
  obtain ⟨a,haP,haD⟩ := principal_opens_intersect hP' hD'
  let Q : Fin r → Forms K n d := (coordinates K _).symm a
  have hQa : coordinates K _ Q=a := (coordinates K _).apply_symm_apply a
  have hQP : eval (coordinates K _ Q) P≠0 := hQa.symm ▸ haP
  have hQD : eval (coordinates K _ Q) D≠0 := hQa.symm ▸ haD
  have hfull (c : ℕ) (hc : c≤d) : Function.Injective
      (homogeneousMultiplication (d := c) e (fun i => L (v i)) he) := by
    intro p p' hp
    apply hinj c hc
    have hbase : homogeneousMultiplication (d := c) e v he p=homogeneousMultiplication e v he p' := by
      apply vectorOutputMap_injective L hL
      simpa only [vectorOutputMap_homogeneousMultiplication] using hp
    exact congrArg (fun f j => (f j).val) hbase
  refine ⟨v,Q,hvextra,attachedPolynomialFamily_homogeneous o hdegree e _ he,
    hfull 0 (Nat.zero_le d),hfull,?_⟩
  exact even_polynomial_row_kernel w Yhalf o ho hdegree L hL hLodd e v he Q
    (hinj d le_rfl) (hPQ Q hQP) counts q J heven hJ hqX hqY hproducts (hDQ Q hQD)

end Froberg
