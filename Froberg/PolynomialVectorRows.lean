module

public import Froberg.SparsePolynomialFamily
public import Froberg.Prefix
public import Froberg.BiformOutputProjection
public import Froberg.SeparatedRowKernel

@[expose] public section

/-! Actual scalar and new-layer polynomial row maps, with their coefficient
space constraints made explicit. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ I J : Type*} [Fintype I] [Fintype J] {n s d q : ℕ}

theorem polynomialFormVector_mem_biform
    (o : J → MvPolynomial σ K) (O : Submodule K (MvPolynomial σ K))
    (C : Submodule K (Poly K n)) (ho : ∀ j,o j∈O)
    (p : J → Forms K n s) (hp : ∀ j,(p j).val∈C) :
    polynomialFormVector o s p∈biformImage O C := by
  rw [polynomialFormVector_apply,polynomialVector_apply]
  exact Submodule.sum_mem _ (fun j hj => mul_mem_biformImage O C (ho j) (hp j))

namespace AttachedMultiplication

def polynomialScalarRow (o : J → MvPolynomial σ K) (Q : Fin q → Forms K n d) :
    (Fin q → J → Forms K n s) →ₗ[K] MvPolynomial (σ ⊕ Fin n) K :=
  (polynomialFormVector o (s+d)).comp (BilinearScalarFamily.multiplication vectorMultiply Q)

def polynomialLayerRow (o : J → MvPolynomial σ K)
    (e : I → Fin n →₀ ℕ) (v : I → J → K) (he : ∀ i,(e i).degree=s) :
    (I → Forms K n d) →ₗ[K] MvPolynomial (σ ⊕ Fin n) K :=
  (polynomialFormVector o (s+d)).comp (homogeneousMultiplication e v he)

theorem polynomialIntermediateRow_eq_addRow (o : J → MvPolynomial σ K)
    (e : I → Fin n →₀ ℕ) (v : I → J → K) (he : ∀ i,(e i).degree=s)
    (Q : Fin q → Forms K n d) :
    polynomialIntermediateRow o e v he Q =
      addRow (polynomialScalarRow (s := s) o Q) (polynomialLayerRow (d := d) o e v he) := by
  apply LinearMap.ext
  intro p
  change polynomialFormVector o (s+d)
    (BilinearScalarFamily.multiplication vectorMultiply Q p.1 + homogeneousMultiplication e v he p.2) = _
  exact map_add _ _ _

/-- Every scalar coefficient is in the literal scalar ideal piece. -/
theorem polynomialScalarRow_range (o : J → MvPolynomial σ K)
    (O : Submodule K (MvPolynomial σ K)) (ho : ∀ j,o j∈O)
    (Q : Fin q → Forms K n d) :
    (polynomialScalarRow (s := s) o Q).range≤biformImage O (familySpace Q*Forms K n s) := by
  rintro x ⟨p,rfl⟩
  apply polynomialFormVector_mem_biform o O _ ho
  intro j
  simp only [BilinearScalarFamily.multiplication_apply,Finset.sum_apply,Submodule.coe_sum,vectorMultiply_val]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.mul_mem_mul (Submodule.subset_span ⟨i,rfl⟩) (p i j).property

/-- The layer row is the literal sum of products by the attached polynomial
family, not an abstract isomorphic multiplication map. -/
theorem polynomialLayerRow_apply (o : J → MvPolynomial σ K)
    (e : I → Fin n →₀ ℕ) (v : I → J → K) (he : ∀ i,(e i).degree=s)
    (p : I → Forms K n d) :
    polynomialLayerRow o e v he p =
      ∑ i,attachedPolynomialFamily o e v i * rename Sum.inr (p i).val := by
  exact (attachedPolynomialFamily_multiplication o e v p).symm

end AttachedMultiplication
end Froberg
