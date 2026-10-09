module

public import Froberg.EvenPolynomialRow
public import Froberg.SingleProfileScalar

@[expose] public section

/-! The Appendix E rows use a single scalar half-degree, including their
unequal output splits. The exact row kernel needs no balanced output split. -/
noncomputable section
namespace Froberg
open Module MvPolynomial AttachedMultiplication MonomialExpansion
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n s d R h H m r j : ℕ}

theorem biform_single_profile_zero (S : Finset (Fin n))
    (f : MvPolynomial (σ ⊕ Fin n) K)
    (hf : f.IsWeightedHomogeneous
      (Sum.elim (fun _ : σ => 0) (ProductRows.halfWeight S)) j) :
    biformScalarMap (retainMonomials (fun α => partialDegree S α≠j)) f=0 := by
  rw [biformScalarMap_retain]
  ext a
  rw [coeff_retainMonomials]
  by_cases ha : partialDegree S (scalarExponent a)≠j
  · rw [if_pos ha]
    by_contra hc
    have hh := hf hc
    rw [←scalarExponent_weight,ProductRows.weight_halfWeight] at hh
    exact ha hh
  · rw [if_neg ha]
    rfl

theorem single_profile_product_disjoint
    {V : Type*} [AddCommGroup V] [Module K V]
    (S : Finset (Fin n)) (P : V →ₗ[K] MvPolynomial (σ ⊕ Fin n) K)
    (hP : ∀ v,(P v).IsWeightedHomogeneous
      (Sum.elim (fun _ : σ => 0) (ProductRows.halfWeight S)) j)
    (O : Submodule K (MvPolynomial σ K)) (Q : Fin r → Forms K n d)
    (hQ : Function.Injective (ProjectedPrefix.multiplication (fun α => partialDegree S α≠j) Q s)) :
    Disjoint (biformImage O (familySpace Q*Forms K n s)) P.range := by
  apply (biformImage_disjoint_scalar_kernel O (familySpace Q*Forms K n s)
    (retainMonomials (fun α => partialDegree S α≠j))
    (ProjectedPrefix.scalar_product_disjoint_kernel _ Q hQ)).mono_right
  rintro _ ⟨v,rfl⟩
  exact biform_single_profile_zero S _ (hP v)

/-- An arbitrary injective product block in one scalar profile can be
adjoined to the same sparse/scalar row without introducing any relation. -/
theorem single_profile_even_row_kernel
    {V : Type*} [AddCommGroup V] [Module K V]
    (w : σ → ℕ) (S : Finset (Fin n))
    (o : Fin H → MvPolynomial σ K) (ho : LinearIndependent K o)
    (hdegree : ∀ k,(o k).IsHomogeneous R)
    (L : (Fin h → K) →ₗ[K] (Fin H → K)) (hL : Function.Injective L)
    (hLodd : ∀ z,retainMonomials (fun α => Finsupp.weight w α%2=0) (outputCombination o (L z))=0)
    (e : Fin m → Fin n →₀ ℕ) (v : Fin m → Fin h → K) (he : ∀ i,(e i).degree=s)
    (Q : Fin r → Forms K n d)
    (hE : Function.Injective (AttachedMultiplication.multiplication (d := d) e v))
    (hQ : Function.Injective (BilinearScalarFamily.multiplication (quotientMultiply e v he) Q))
    (P : V →ₗ[K] MvPolynomial (σ ⊕ Fin n) K) (hP : Function.Injective P)
    (hPX : (biformOutputEndomorphism (retainMonomials (fun α => Finsupp.weight w α%2=0))).comp P=P)
    (hPY : ∀ p,(P p).IsWeightedHomogeneous
      (Sum.elim (fun _ : σ => 0) (ProductRows.halfWeight S)) j)
    (hscalar : Function.Injective (ProjectedPrefix.multiplication (fun α => partialDegree S α≠j) Q s)) :
    (addRow (polynomialIntermediateRow o e (fun i => L (v i)) he Q) P).ker=
      ((LinearMap.inl K ((Fin r → Fin H → Forms K n s) × (Fin m → Forms K n d)) V).comp
        (intermediateKoszul e (fun i => L (v i)) he Q)).range := by
  have hfree := vector_scalar_injective_of_projected (J := Fin H)
    (fun α => partialDegree S α≠j) Q hscalar
  have hkernel := intermediateRow_ker_output_embedding L hL e v he Q hE hQ hfree
  have hpoly : (polynomialIntermediateRow o e (fun i => L (v i)) he Q).ker=
      (intermediateKoszul e (fun i => L (v i)) he Q).range := by
    rw [←hkernel]
    ext x
    change polynomialFormVector o (s+d) (intermediateRow e (fun i => L (v i)) he Q x)=0 ↔
      intermediateRow e (fun i => L (v i)) he Q x=0
    exact (polynomialFormVector_injective o ho).eq_iff' (map_zero _)
  rw [polynomialIntermediateRow_eq_addRow] at hpoly ⊢
  apply addRow_kernel_eq_mandatory (polynomialScalarRow o Q)
    (polynomialLayerRow o e (fun i => L (v i)) he) P
    (biformImage (homogeneousSubmodule σ K R) (familySpace Q*Forms K n s))
    (biformOutputEndomorphism (retainMonomials (fun α => Finsupp.weight w α%2=0)))
  · exact polynomialScalarRow_range o _ hdegree Q
  · intro x hx
    apply biformOutputEndomorphism_preserves _ _ _ _ hx
    intro a ha
    exact retainMonomials_preserves_homogeneous _ ha
  · apply LinearMap.ext
    intro p
    exact polynomialLayerRow_output_zero o e (fun i => L (v i)) he
      (retainMonomials (fun α => Finsupp.weight w α%2=0)) (fun i => hLodd (v i)) p
  · exact hPX
  · exact single_profile_product_disjoint S P hPY _ Q hscalar
  · exact hP
  · exact hpoly

end Froberg
