module

public import Quartic.CharTwoCertificate

@[expose] public section

/-! A coefficient of the already checked inverse detects a surviving monomial. -/
noncomputable section
namespace Quartic.CharTwoCertificate
open Module MvPolynomial Matrix
open FiniteEndpointChecker FiniteEndpointCheckerPolynomial FiniteEndpointCertificate
set_option maxHeartbeats 2000000

variable {K : Type*} [Field K] [CharP K 2]
variable {n lo hi b₂ b₄ L : ℕ} (D : Data n lo hi b₂ b₄ L)

theorem lower_range_eq_span :
    LinearMap.range (quadraticMultiplication (D.lowerQuadrics (K := K))) =
      Submodule.span K (Set.range (fun i : Fin L => D.product (K := K) (D.lowerIndex i))) := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact lower_product_mem D i)
  · change finrank K (Submodule.span K (Set.range (D.product ∘ D.lowerIndex))) = _
    rw [finrank_span_eq_card ((products_independent (K := K) D).comp
      D.lowerIndex D.lowerIndex_injective), Fintype.card_fin]
    have hq := quartic_quotient_add_rank (D.lowerQuadrics (K := K))
    rw [lower_dimension D, D.dimension₄] at hq
    have he := D.expected_lower
    omega

theorem lower_exact (hlo : 0 ≤ Counts.chi n lo) :
    LinearMap.ker (quadraticMultiplication (D.lowerQuadrics (K := K))) ≤
      koszulSpace (D.lowerQuadrics (K := K)) := by
  have hq := lowerQuadrics_independent (K := K) D
  have heuler := quartic_euler_identity (D.lowerQuadrics (K := K)) hq
  rw [lower_dimension D] at heuler
  change ((Counts.chi n lo).toNat : ℤ) - _ = _ at heuler
  have hhom := homology_add_pairs (D.lowerQuadrics (K := K)) hq
  have hB : finrank K (koszulSpace (D.lowerQuadrics (K := K))) = lo.choose 2 :=
    (finrank_span_eq_card (koszulVector_linearIndependent _ hq)).trans card_generatorPair
  have heq : koszulSpace (D.lowerQuadrics (K := K)) =
      LinearMap.ker (quadraticMultiplication (D.lowerQuadrics (K := K))) := by
    apply Submodule.eq_of_le_of_finrank_eq (kernel_contains_koszul _)
    omega
  exact heq.ge

/-- A nonzero inverse coordinate after the lower basis detects an element outside
the entire lower multiplication image, not only outside the selected rows. -/
theorem outside_lower_of_inverse_bit (t j : Fin b₄) (hj : L ≤ j.val)
    (hbit : (D.inverse t).testBit j.val = true)
    (m : Forms K n 4)
    (hm : ∀ k, m.val.coeff (D.exponent₄ k) = (Pi.single t (1 : K) : Fin b₄ → K) k) :
    m ∉ LinearMap.range (quadraticMultiplication (D.lowerQuadrics (K := K))) := by
  classical
  let A : Matrix (Fin b₄) (Fin b₄) K := (sparseMatrix D.rows).map (binaryMap (K := K))
  let B : Matrix (Fin b₄) (Fin b₄) K := (packedMatrix b₄ D.inverse).map (binaryMap (K := K))
  have hab : A * B = 1 := by
    have h := congrArg (binaryMap (K := K)).mapMatrix (inverse_identity D.rows D.inverse D.inverse_checked)
    simpa only [map_mul, map_one, RingHom.mapMatrix_apply, A, B] using h
  let C : Forms K n 4 →ₗ[K] (Fin b₄ → K) :=
    (LinearMap.pi (fun k => MvPolynomial.lcoeff K (D.exponent₄ k))).comp (Forms K n 4).subtype
  let f : Forms K n 4 →ₗ[K] K := (LinearMap.proj j).comp (B.vecMulLinear.comp C)
  have hp (i : Fin b₄) : f (D.product (K := K) i) = if i = j then 1 else 0 := by
    have hc : C (D.product (K := K) i) = A i := by
      funext k
      change (rowPolynomial (K := K) D.exponent₄ (D.rows i)).coeff (D.exponent₄ k) = _
      rw [congrFun (coefficients_rowPolynomial D.exponent₄ D.injective₄ (D.rows i)) k]
      exact (binaryMap_sparseRow (D.rows i) k).symm
    change (C (D.product i) ᵥ* B) j = _
    rw [hc]
    change (A * B) i j = _
    rw [hab]
    rfl
  have hs : Submodule.span K (Set.range (fun i : Fin L => D.product (K := K) (D.lowerIndex i))) ≤
      LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change f (D.product (D.lowerIndex i)) = 0
    rw [hp, if_neg]
    intro he
    have := congrArg Fin.val he
    change i.val = j.val at this
    omega
  have hfm : f m ≠ 0 := by
    have hc : C m = Pi.single t (1 : K) := funext hm
    change (C m ᵥ* B) j ≠ 0
    rw [hc, Matrix.single_one_vecMul]
    change binaryMap (K := K) (if (D.inverse t).testBit j.val then 1 else 0) ≠ 0
    simp [hbit]
  intro hmrange
  rw [lower_range_eq_span D] at hmrange
  exact hfm (hs hmrange)

/-- Convenient specialization to a square whose coefficient vector is a monomial. -/
theorem marked_of_inverse_bit (hlo : 0 ≤ Counts.chi n lo)
    (t j : Fin b₄) (hj : L ≤ j.val) (hbit : (D.inverse t).testBit j.val = true)
    (ζ : Forms K n 2)
    (hζ : ∀ k, (mulQuadratic ζ ζ).val.coeff (D.exponent₄ k) =
      (Pi.single t (1 : K) : Fin b₄ → K) k) :
    MarkedLowerWitness K n lo :=
  ⟨D.lowerQuadrics, lowerQuadrics_independent D, lower_exact D hlo, ζ,
    outside_lower_of_inverse_bit D t j hj hbit (mulQuadratic ζ ζ) hζ⟩

/-- The square of a single variable, viewed as a quadratic form. -/
def coordinateQuadratic (z : Fin n) : Forms K n 2 :=
  ⟨monomial (Finsupp.single z 2) 1, isHomogeneous_monomial _ (by simp)⟩

theorem coordinateQuadratic_square (z : Fin n) :
    (mulQuadratic (coordinateQuadratic (K := K) z) (coordinateQuadratic z)).val =
      monomial (Finsupp.single z 4) (1 : K) := by
  simp [coordinateQuadratic, mulQuadratic, monomial_mul_monomial, ← Finsupp.single_add]

/-- A single inverse bit certifies that the square of a coordinate quadratic survives. -/
theorem marked_of_coordinate_inverse_bit (hlo : 0 ≤ Counts.chi n lo)
    (z : Fin n) (t j : Fin b₄) (ht : D.exponent₄ t = Finsupp.single z 4)
    (hj : L ≤ j.val) (hbit : (D.inverse t).testBit j.val = true) :
    MarkedLowerWitness K n lo := by
  apply marked_of_inverse_bit D hlo t j hj hbit (coordinateQuadratic z)
  intro k
  rw [coordinateQuadratic_square, ← ht]
  simp [coeff_monomial, D.injective₄.eq_iff, Pi.single_apply, eq_comm]

end Quartic.CharTwoCertificate
