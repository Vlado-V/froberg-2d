import Froberg.HomogeneousOutputCoordinates

/-! The output constraint of a sparse family survives every scalar multiplier. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ I J : Type*} [Fintype I] [Fintype J] {n s d : ℕ}

theorem attachedPolynomialFamily_factor
    (o : J → MvPolynomial σ K) (e : I → Fin n →₀ ℕ) (v : I → J → K) (i : I) :
    attachedPolynomialFamily o e v i =
      rename Sum.inl (outputCombination o (v i)) * rename Sum.inr (monomial (e i) 1) := by
  simp only [attachedPolynomialFamily,polynomialVector_apply,outputCombination,
    LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_smul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [smul_mul_assoc,← mul_smul_comm,← map_smul,smul_monomial,smul_eq_mul,mul_one]

/-- A sparse family with outputs in O retains that output condition after
multiplication by arbitrary homogeneous scalar coefficients. -/
theorem polynomialLayerRow_mem_biform
    (o : J → MvPolynomial σ K) (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i,(e i).degree=s)
    (O : Submodule K (MvPolynomial σ K)) (ho : ∀ i,outputCombination o (v i)∈O)
    (p : I → Forms K n d) :
    AttachedMultiplication.polynomialLayerRow o e v he p∈biformImage O (Forms K n (s+d)) := by
  rw [AttachedMultiplication.polynomialLayerRow_apply]
  apply Submodule.sum_mem
  intro i hi
  rw [attachedPolynomialFamily_factor,mul_assoc,← map_mul]
  exact mul_mem_biformImage O (Forms K n (s+d)) (ho i)
    ((isHomogeneous_monomial (1 : K) (he i)).mul (p i).property)

theorem biformOutputEndomorphism_eq_zero_of_mem
    (T : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (O : Submodule K (MvPolynomial σ K)) (C : Submodule K (Poly K n))
    (hO : O≤T.ker) {f : MvPolynomial (σ ⊕ Fin n) K} (hf : f∈biformImage O C) :
    biformOutputEndomorphism T f=0 := by
  have ht : biformOutputMap T f=0 := biformImage_le_output_kernel T O C hO hf
  change MvPolynomial.tensorEquivSum K σ (Fin n) K (biformOutputMap T f)=0
  rw [ht,map_zero]

/-- The full new-layer row is annihilated by every output projection that
annihilates its actual generator output vectors. -/
theorem polynomialLayerRow_output_zero
    (o : J → MvPolynomial σ K) (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i,(e i).degree=s)
    (T : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (ho : ∀ i,T (outputCombination o (v i))=0)
    (p : I → Forms K n d) :
    biformOutputEndomorphism T (AttachedMultiplication.polynomialLayerRow o e v he p)=0 := by
  apply biformOutputEndomorphism_eq_zero_of_mem T T.ker (Forms K n (s+d)) le_rfl
  exact polynomialLayerRow_mem_biform o e v he T.ker ho p

end Froberg
