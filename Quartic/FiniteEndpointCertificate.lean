module

public import Quartic.FiniteEndpointCheckerPolynomial

@[expose] public section

/-! One mathematical soundness theorem for every finite endpoint certificate.
All remaining work per dimension is checking finite data against these fields. -/
namespace Quartic.FiniteEndpointCertificate
open Module MvPolynomial
open FiniteEndpointChecker FiniteEndpointCheckerPolynomial
set_option maxHeartbeats 2000000

/-- Separately checked rows imply the whole Boolean certificate without evaluating it again. -/
theorem checkInverse_of_equations {s : ℕ} (A : Fin s → List (Fin s)) (B : Fin s → ℕ)
    (h : ∀ i, xorSum ((A i).map B) = 2^i.val) : checkInverse A B = true := by
  apply List.all_eq_true.mpr
  intro i _
  exact decide_eq_true (h i)

/-- The packed inverse checker asserts exactly its individual row equations. -/
theorem checkInverse_iff {s : ℕ} (A : Fin s → List (Fin s)) (B : Fin s → ℕ) :
    checkInverse A B = true ↔ ∀ i, xorSum ((A i).map B) = 2^i.val :=
  ⟨checkInverse_equations A B,checkInverse_of_equations A B⟩

structure Data (n lo hi b₂ b₄ L : ℕ) where
  exponent₂ : Fin b₂ → Fin n →₀ ℕ
  exponent₄ : Fin b₄ → Fin n →₀ ℕ
  degree₂ : ∀ i, (exponent₂ i).degree = 2
  degree₄ : ∀ i, (exponent₄ i).degree = 4
  injective₂ : Function.Injective exponent₂
  injective₄ : Function.Injective exponent₄
  support : Fin hi → List (Fin b₂)
  rows : Fin b₄ → List (Fin b₄)
  inverse : Fin b₄ → ℕ
  inverse_checked : checkInverse rows inverse = true
  selected : Fin b₄ → Fin hi × Fin b₂
  product_supports : ∀ i, (rows i).map exponent₄ =
    (support (selected i).1).map (fun j => exponent₂ j + exponent₂ (selected i).2)
  quadColumns : Fin hi → Fin b₂
  quadMinor : Fin hi → List (Fin hi)
  quadInverse : Fin hi → ℕ
  quad_inverse_checked : checkInverse quadMinor quadInverse = true
  quad_counts : ∀ i j, (support i).count (quadColumns j) = (quadMinor i).count j
  lower_le : L ≤ b₄
  lower_selected : ∀ i : Fin L, (selected ⟨i.val,lt_of_lt_of_le i.isLt lower_le⟩).1.val < lo
  lo_le_hi : lo ≤ hi
  dimension₄ : (n+3).choose 4 = b₄
  expected_lower : expectedDimension n lo + L = b₄
  expected_upper : expectedDimension n hi = 0

namespace Data
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {n lo hi b₂ b₄ L : ℕ}
variable (D : Data n lo hi b₂ b₄ L)
include D

def quadrics (i : Fin hi) : Forms K n 2 := rowForm D.exponent₂ D.degree₂ (D.support i)

theorem quadrics_independent : LinearIndependent K (D.quadrics (K := K)) := by
  apply LinearIndependent.of_comp (Forms K n 2).subtype
  apply polynomials_independent_of_coefficients
    (fun i => (D.quadrics (K := K) i).val) (D.exponent₂ ∘ D.quadColumns)
    D.quadMinor D.quadInverse D.quad_inverse_checked
  intro i
  funext j
  change (rowPolynomial (K := K) D.exponent₂ (D.support i)).coeff (D.exponent₂ (D.quadColumns j)) = _
  rw [rowPolynomial_coeff_count D.exponent₂ D.injective₂,sparse_count]
  exact congrArg (fun n : ℕ => (n : K)) (D.quad_counts i j)

def multiplier (i : Fin b₂) : Forms K n 2 :=
  ⟨monomial (D.exponent₂ i) 1,isHomogeneous_monomial _ (D.degree₂ i)⟩

def product (i : Fin b₄) : Forms K n 4 := rowForm D.exponent₄ D.degree₄ (D.rows i)

theorem product_identity (i : Fin b₄) : D.product (K := K) i =
    mulQuadratic (D.quadrics (D.selected i).1) (D.multiplier (D.selected i).2) := by
  apply Subtype.ext
  exact (FiniteEndpointCheckerPolynomial.product_identity D.exponent₄ D.exponent₂
    (D.support (D.selected i).1) (D.exponent₂ (D.selected i).2) (D.rows i) (D.product_supports i)).symm

theorem products_independent : LinearIndependent K (D.product (K := K)) :=
  rowForms_independent D.exponent₄ D.degree₄ D.injective₄ D.rows D.inverse D.inverse_checked

theorem upper_rank : b₄ ≤ finrank K (LinearMap.range (quadraticMultiplication (D.quadrics (K := K)))) := by
  apply rank_lower_bound _ _ D.products_independent
  intro i
  rw [D.product_identity]
  exact product_mem_range _ _ _

def lowerQuadrics (i : Fin lo) : Forms K n 2 := D.quadrics (i.castLE D.lo_le_hi)

theorem lowerQuadrics_independent : LinearIndependent K (D.lowerQuadrics (K := K)) :=
  D.quadrics_independent.comp (Fin.castLE D.lo_le_hi) (Fin.castLE_injective D.lo_le_hi)

def lowerIndex (i : Fin L) : Fin b₄ := i.castLE D.lower_le

theorem lowerIndex_injective : Function.Injective D.lowerIndex := Fin.castLE_injective D.lower_le

theorem lower_rank : L ≤ finrank K (LinearMap.range
    (quadraticMultiplication (D.lowerQuadrics (K := K)))) := by
  apply rank_lower_bound _ (fun i => D.product (D.lowerIndex i))
    (D.products_independent.comp D.lowerIndex D.lowerIndex_injective)
  intro i
  rw [D.product_identity]
  let j : Fin lo := ⟨(D.selected (D.lowerIndex i)).1.val,D.lower_selected i⟩
  have he : j.castLE D.lo_le_hi = (D.selected (D.lowerIndex i)).1 := Fin.ext rfl
  have hj : D.quadrics (K := K) (D.selected (D.lowerIndex i)).1 = D.lowerQuadrics j := by
    rw [lowerQuadrics,he]
  rw [hj]
  exact product_mem_range _ _ _

theorem lower_witness : QuarticWitness K n lo := by
  apply EndpointReduction.witness_of_ordered (D.lowerQuadrics (K := K)) D.lowerQuadrics_independent
  have hq := quartic_quotient_add_rank (D.lowerQuadrics (K := K))
  have hlo := quartic_quotient_lower_bound (D.lowerQuadrics (K := K)) D.lowerQuadrics_independent
  have hr := D.lower_rank (K := K)
  have he := D.expected_lower
  rw [D.dimension₄] at hq
  omega

theorem upper_witness : QuarticWitness K n hi := by
  apply EndpointReduction.witness_of_ordered (D.quadrics (K := K)) D.quadrics_independent
  have hq := quartic_quotient_add_rank (D.quadrics (K := K))
  have hr := D.upper_rank (K := K)
  rw [D.expected_upper,D.dimension₄] at *
  omega

theorem generic_of_certificate (hadjacent : hi ≤ lo+1)
    (hlo : 0 ≤ Counts.chi n lo) (hhi : Counts.chi n hi ≤ 0)
    (r : ℕ) (hr : r ≤ (n+1).choose 2) : GenericQuartic K n r :=
  EndpointReduction.adjacent_endpoints_imply_generic lo hi hadjacent
    D.lower_witness D.upper_witness hlo hhi hr

end
end Data
end Quartic.FiniteEndpointCertificate
