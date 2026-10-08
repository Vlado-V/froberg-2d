import Froberg.SparseFullOutput

/-! A new-layer witness in an arbitrary prescribed output subspace, with
all ambient output coefficients allowed. This includes the quadratic row. -/
noncomputable section
namespace Froberg
open Module MvPolynomial AttachedMultiplication Quartic.PolynomialBilinearCoordinates
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ]

/-- Sparse quotient exactness extends to every output direction and is
compatible with an arbitrary nonempty scalar-injectivity open. -/
theorem exists_sparse_full_output_row_all_degrees {n R s d b m r : ℕ}
    (hn : 0<n) (O : Submodule K (MvPolynomial σ K))
    (hO : O≤homogeneousSubmodule σ K R) (hOpos : 0<finrank K O)
    (hm : m≤b*(n+s-1).choose s) (hcap : b*(s+d).choose s≤finrank K O)
    (hcount : finrank K O*(s+d).choose s *
      (r+finrank K O*(n+s-1).choose s+(finrank K O*2^(finrank K O))*(n+(d-1)-1).choose (d-1)) ≤
      (finrank K O-b*(s+d).choose s)*(n+s+d-1).choose d)
    (hscalarOpen : ∃ D : MvPolynomial (Fin (finrank K (Fin r → Forms K n d))) K,
      (∃ Q : Fin r → Forms K n d,eval (coordinates K _ Q) D≠0) ∧
      ∀ Q : Fin r → Forms K n d,eval (coordinates K _ Q) D≠0 →
        Function.Injective (prefixMultiplication Q s)) :
    ∃ (o : Fin (finrank K (homogeneousSubmodule σ K R)) → MvPolynomial σ K)
      (e : Fin m → Fin n →₀ ℕ)
      (v : Fin m → Fin (finrank K (homogeneousSubmodule σ K R)) → K),
      ∃ he : ∀ i,(e i).degree=s,
      ∃ Q : Fin r → Forms K n d,
        LinearIndependent K o ∧ (∀ i,(o i).IsHomogeneous R) ∧
        (∀ i,attachedPolynomialFamily o e v i∈biformImage O (Forms K n s)) ∧
        (∀ i,(attachedPolynomialFamily o e v i).IsHomogeneous (R+s)) ∧
        Function.Injective (homogeneousMultiplication (d := 0) e v he) ∧
        (∀ c ≤ d,Function.Injective (homogeneousMultiplication (d := c) e v he)) ∧
        (polynomialIntermediateRow o e v he Q).ker=(intermediateKoszul e v he Q).range := by
  obtain ⟨o,L,ho,hdeg,hL,hLO⟩ := homogeneous_output_coordinate_embedding O hO
  obtain ⟨e,v,he,hdiv,hv,hpos,hinj,P,hP,hPQ⟩ :=
    exists_exact_sparse_intermediate (K := K) hn hOpos hm hcap hcount
  obtain ⟨D,hD,hDQ⟩ := hscalarOpen
  have hP' : ∃ a,eval a P≠0 := by obtain ⟨Q,hQ⟩ := hP; exact ⟨coordinates K _ Q,hQ⟩
  have hD' : ∃ a,eval a D≠0 := by obtain ⟨Q,hQ⟩ := hD; exact ⟨coordinates K _ Q,hQ⟩
  obtain ⟨a,haP,haD⟩ := principal_opens_intersect hP' hD'
  let Q : Fin r → Forms K n d := (coordinates K _).symm a
  have hQa : coordinates K _ Q=a := (coordinates K _).apply_symm_apply a
  have hQP : eval (coordinates K _ Q) P≠0 := hQa.symm ▸ haP
  have hQD : eval (coordinates K _ Q) D≠0 := hQa.symm ▸ haD
  refine ⟨o,e,(fun i => L (v i)),he,Q,ho,hdeg,?_,
    attachedPolynomialFamily_homogeneous o hdeg e _ he,?_,?_,?_⟩
  · intro i
    rw [attachedPolynomialFamily_factor]
    exact mul_mem_biformImage O (Forms K n s) (hLO (v i)) (isHomogeneous_monomial _ (he i))
  · intro p p' hp
    apply hinj 0 (Nat.zero_le d)
    have hbase : homogeneousMultiplication (d := 0) e v he p=homogeneousMultiplication e v he p' := by
      apply vectorOutputMap_injective L hL
      simpa only [vectorOutputMap_homogeneousMultiplication] using hp
    exact congrArg (fun f j => (f j).val) hbase
  · intro c hc p p' hp
    apply hinj c hc
    have hbase : homogeneousMultiplication (d := c) e v he p=homogeneousMultiplication e v he p' := by
      apply vectorOutputMap_injective L hL
      simpa only [vectorOutputMap_homogeneousMultiplication] using hp
    exact congrArg (fun f j => (f j).val) hbase
  · have hk := intermediateRow_ker_output_embedding L hL e v he Q
      (hinj d le_rfl) (hPQ Q hQP) (vector_scalar_injective_of_prefix Q (hDQ Q hQD))
    rw [← hk]
    ext x
    change polynomialFormVector o (s+d) (intermediateRow e (fun i => L (v i)) he Q x)=0 ↔
      intermediateRow e (fun i => L (v i)) he Q x=0
    exact (polynomialFormVector_injective o ho).eq_iff' (map_zero _)

end Froberg
