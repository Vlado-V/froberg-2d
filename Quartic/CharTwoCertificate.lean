module

public import Quartic.FiniteEndpointCertificate
public import Quartic.MarkedLowerWitness

@[expose] public section

/-! Interpretation of the checked binary certificates over any field of characteristic two. -/
noncomputable section
namespace Quartic.CharTwoCertificate
open Module MvPolynomial Matrix
open FiniteEndpointChecker FiniteEndpointCheckerPolynomial FiniteEndpointCertificate
set_option maxHeartbeats 2000000

variable {K : Type*} [Field K] [CharP K 2]

def binaryMap : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K

theorem binaryMap_injective : Function.Injective (binaryMap (K := K)) :=
  ZMod.castHom_injective K

theorem binaryMap_sparseRow {N : ℕ} (s : List (Fin N)) (j : Fin N) :
    binaryMap (K := K) (sparseRow s j) =
      ((s.map (fun i => Pi.single i (1 : K))).sum) j := by
  classical
  induction s with
  | nil => simp [sparseRow]
  | cons i s ih =>
    simp only [sparseRow, List.map_cons, List.sum_cons, Pi.add_apply, map_add] at *
    rw [ih]
    simp [Pi.single_apply]

theorem rows_independent {N : ℕ} (A : Fin N → List (Fin N)) (B : Fin N → ℕ)
    (h : checkInverse A B = true) :
    LinearIndependent K (fun i => ((A i).map (fun j => Pi.single j (1 : K))).sum) := by
  have hd : ((sparseMatrix A).map (binaryMap (K := K))).det ≠ 0 :=
    MinorLift.det_ne_zero_under_injective_map (binaryMap (K := K)) binaryMap_injective
      (sparseMatrix A) (determinant_ne_zero A B h)
  have hi := Matrix.linearIndependent_rows_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))
  have he : ((sparseMatrix A).map (binaryMap (K := K))).row =
      fun i => ((A i).map (fun j => Pi.single j (1 : K))).sum := by
    funext i j
    exact binaryMap_sparseRow (A i) j
  rwa [he] at hi

theorem polynomials_independent {N n : ℕ}
    (p : Fin N → Poly K n) (E : Fin N → Fin n →₀ ℕ)
    (A : Fin N → List (Fin N)) (B : Fin N → ℕ) (h : checkInverse A B = true)
    (hc : ∀ i, (fun j => (p i).coeff (E j)) =
      ((A i).map (fun j => Pi.single j (1 : K))).sum) : LinearIndependent K p := by
  let C : Poly K n →ₗ[K] (Fin N → K) := LinearMap.pi (fun j => MvPolynomial.lcoeff K (E j))
  apply LinearIndependent.of_comp C
  change LinearIndependent K (fun i j => (p i).coeff (E j))
  rw [show (fun i j => (p i).coeff (E j)) =
      (fun i => ((A i).map (fun j => Pi.single j (1 : K))).sum) from funext hc]
  exact rows_independent A B h

theorem coefficients_rowPolynomial {N n : ℕ} (E : Fin N → Fin n →₀ ℕ)
    (hE : Function.Injective E) (s : List (Fin N)) :
    (fun j => (rowPolynomial (K := K) E s).coeff (E j)) =
      (s.map (fun i => Pi.single i (1 : K))).sum := by
  classical
  induction s with
  | nil => ext j; simp [rowPolynomial]
  | cons i s ih =>
    ext j
    simp only [rowPolynomial, List.map_cons, List.sum_cons, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, coeff_monomial, Pi.add_apply]
    simp only [hE.eq_iff]
    have hij := congrFun ih j
    change ((s.map (fun k => monomial (E k) (1 : K))).sum).coeff (E j) = _ at hij
    rw [hij]
    simp [Pi.single_apply, eq_comm]

theorem sparse_count {N : ℕ} (s : List (Fin N)) (j : Fin N) :
    (s.map (fun i => Pi.single i (1 : K))).sum j = (s.count j : K) := by
  classical
  induction s with
  | nil => simp
  | cons i s ih =>
    simp only [List.map_cons, List.sum_cons, Pi.add_apply]
    rw [ih]
    by_cases h : i = j
    · subst i
      simp only [Pi.single_eq_same, List.count_cons_self, Nat.cast_add, Nat.cast_one]
      exact add_comm _ _
    · rw [List.count_cons_of_ne h]
      simp [Pi.single_apply, h, Ne.symm h]

theorem rowPolynomial_coeff_count {N n : ℕ} (E : Fin N → Fin n →₀ ℕ)
    (hE : Function.Injective E) (s : List (Fin N)) (j : Fin N) :
    (rowPolynomial (K := K) E s).coeff (E j) = (s.count j : K) := by
  rw [congrFun (coefficients_rowPolynomial E hE s) j, sparse_count]

theorem rowPolynomial_mul_monomial {N n : ℕ} (E : Fin N → Fin n →₀ ℕ)
    (s : List (Fin N)) (e : Fin n →₀ ℕ) :
    rowPolynomial (K := K) E s * monomial e 1 =
      (s.map (fun j => monomial (E j + e) (1 : K))).sum := by
  induction s with
  | nil => simp [rowPolynomial]
  | cons i s ih =>
    simp only [rowPolynomial, List.map_cons, List.sum_cons, add_mul, monomial_mul_monomial, one_mul]
    exact congrArg (fun z => monomial (E i + e) (1 : K) + z) ih

theorem product_mem_range {n r : ℕ} (q : Fin r → Forms K n 2) (i : Fin r)
    (a : Forms K n 2) : mulQuadratic (q i) a ∈ LinearMap.range (quadraticMultiplication q) := by
  classical
  refine ⟨Pi.single i a, ?_⟩
  apply Subtype.ext
  simp only [quadraticMultiplication_val, mulQuadratic, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

theorem rank_lower_bound {n r s : ℕ} (q : Fin r → Forms K n 2)
    (f : Fin s → Forms K n 4) (hf : LinearIndependent K f)
    (hmem : ∀ i, f i ∈ LinearMap.range (quadraticMultiplication q)) :
    s ≤ finrank K (LinearMap.range (quadraticMultiplication q)) := by
  have hs : Submodule.span K (Set.range f) ≤ LinearMap.range (quadraticMultiplication q) :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hmem i)
  simpa [finrank_span_eq_card hf] using Submodule.finrank_mono hs

variable {n lo hi b₂ b₄ L : ℕ} (D : Data n lo hi b₂ b₄ L)
include D

theorem product_identity (i : Fin b₄) : D.product (K := K) i =
    mulQuadratic (D.quadrics (D.selected i).1) (D.multiplier (D.selected i).2) := by
  apply Subtype.ext
  change rowPolynomial D.exponent₄ (D.rows i) =
    rowPolynomial (K := K) D.exponent₂ (D.support (D.selected i).1) *
      monomial (D.exponent₂ (D.selected i).2) 1
  rw [rowPolynomial_mul_monomial]
  have h := congrArg (fun xs => (xs.map (fun z => monomial z (1 : K))).sum) (D.product_supports i)
  simpa only [List.map_map, Function.comp_def, rowPolynomial] using h

theorem quadrics_independent : LinearIndependent K (D.quadrics (K := K)) := by
  apply LinearIndependent.of_comp (Forms K n 2).subtype
  apply polynomials_independent
    (fun i => (D.quadrics (K := K) i).val) (D.exponent₂ ∘ D.quadColumns)
    D.quadMinor D.quadInverse D.quad_inverse_checked
  intro i
  funext j
  change (rowPolynomial (K := K) D.exponent₂ (D.support i)).coeff (D.exponent₂ (D.quadColumns j)) = _
  rw [rowPolynomial_coeff_count D.exponent₂ D.injective₂, sparse_count]
  exact congrArg (fun n : ℕ => (n : K)) (D.quad_counts i j)

theorem products_independent : LinearIndependent K (D.product (K := K)) := by
  apply LinearIndependent.of_comp (Forms K n 4).subtype
  apply polynomials_independent _ D.exponent₄ D.rows D.inverse D.inverse_checked
  intro i
  exact coefficients_rowPolynomial D.exponent₄ D.injective₄ (D.rows i)

theorem upper_rank : b₄ ≤ finrank K (LinearMap.range (quadraticMultiplication (D.quadrics (K := K)))) := by
  apply rank_lower_bound _ _ (products_independent D)
  intro i
  rw [product_identity D]
  exact product_mem_range _ _ _

theorem lowerQuadrics_independent : LinearIndependent K (D.lowerQuadrics (K := K)) :=
  (quadrics_independent D).comp (Fin.castLE D.lo_le_hi) (Fin.castLE_injective D.lo_le_hi)

theorem lower_product_mem (i : Fin L) : D.product (K := K) (D.lowerIndex i) ∈
    LinearMap.range (quadraticMultiplication (D.lowerQuadrics (K := K))) := by
  rw [product_identity D]
  let j : Fin lo := ⟨(D.selected (D.lowerIndex i)).1.val, D.lower_selected i⟩
  have he : j.castLE D.lo_le_hi = (D.selected (D.lowerIndex i)).1 := Fin.ext rfl
  have hj : D.quadrics (K := K) (D.selected (D.lowerIndex i)).1 = D.lowerQuadrics j := by
    rw [Data.lowerQuadrics, he]
  rw [hj]
  exact product_mem_range _ _ _

theorem lower_rank : L ≤ finrank K (LinearMap.range
    (quadraticMultiplication (D.lowerQuadrics (K := K)))) :=
  rank_lower_bound _ _ ((products_independent D).comp D.lowerIndex D.lowerIndex_injective)
    (lower_product_mem D)

theorem lower_dimension : finrank K (QuarticQuotient K n
    (Submodule.span K (Set.range (fun i => (D.lowerQuadrics (K := K) i).val)))) =
      expectedDimension n lo := by
  have hq := quartic_quotient_add_rank (D.lowerQuadrics (K := K))
  have hlo := quartic_quotient_lower_bound (D.lowerQuadrics (K := K)) (lowerQuadrics_independent D)
  have hr := lower_rank (K := K) D
  have he := D.expected_lower
  rw [D.dimension₄] at hq
  omega

theorem lower_witness : QuarticWitness K n lo :=
  EndpointReduction.witness_of_ordered (D.lowerQuadrics (K := K))
    (lowerQuadrics_independent D) (lower_dimension D)

theorem upper_witness : QuarticWitness K n hi := by
  apply EndpointReduction.witness_of_ordered (D.quadrics (K := K)) (quadrics_independent D)
  have hq := quartic_quotient_add_rank (D.quadrics (K := K))
  have hr := upper_rank (K := K) D
  rw [D.expected_upper, D.dimension₄] at *
  omega

theorem generic_of_certificate (hadjacent : hi ≤ lo + 1)
    (hlo : 0 ≤ Counts.chi n lo) (hhi : Counts.chi n hi ≤ 0)
    (r : ℕ) (hr : r ≤ (n + 1).choose 2) : GenericQuartic K n r :=
  EndpointReduction.adjacent_endpoints_imply_generic lo hi hadjacent
    (lower_witness D) (upper_witness D) hlo hhi hr

end Quartic.CharTwoCertificate
