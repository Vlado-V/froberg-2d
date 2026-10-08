import Quartic.FiniteEndpointCheckerSupport7

/-! The supplied seven-variable endpoints, using the common sparse-inverse checker.
All generator and product identities are literal monomial equalities. -/
noncomputable section
namespace Quartic.FiniteEndpointCheckerSeven
open Module MvPolynomial
open FiniteEndpointChecker FiniteEndpointCheckerPolynomial
open FiniteEndpointCheckerData7 FiniteEndpointCheckerSupport7
variable {K : Type*} [Field K] [CharZero K]
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- The exact supplied binary quadrics, with coefficients 0 or 1 in K. -/
def quadrics (i : Fin 9) : Forms K 7 2 :=
  rowForm exponent2 exponent2_degree (quadSupport i)

theorem quadrics_independent : LinearIndependent K (quadrics (K := K)) := by
  apply LinearIndependent.of_comp (Forms K 7 2).subtype
  apply polynomials_independent_of_coefficients
    (fun i => (quadrics (K := K) i).val) (exponent2 ∘ quadColumns)
    quadMinor quadInverse quad_inverse_checked
  intro i
  funext j
  change (rowPolynomial (K := K) exponent2 (quadSupport i)).coeff (exponent2 (quadColumns j)) = _
  rw [rowPolynomial_coeff_count exponent2 exponent2_injective,sparse_count]
  exact congrArg (fun n : ℕ => (n : K)) (quad_coefficient_counts i j)

def multiplier (i : Fin 28) : Forms K 7 2 :=
  ⟨monomial (exponent2 i) 1,isHomogeneous_monomial _ (exponent2_degree i)⟩

def certifiedProduct (i : Fin 210) : Forms K 7 4 :=
  rowForm exponent4 exponent4_degree (rows i)

theorem certifiedProduct_identity (i : Fin 210) :
    certifiedProduct (K := K) i =
      mulQuadratic (quadrics (selected i).1) (multiplier (selected i).2) := by
  apply Subtype.ext
  exact (product_identity exponent4 exponent2 (quadSupport (selected i).1)
    (exponent2 (selected i).2) (rows i) (product_supports i)).symm

theorem products_independent : LinearIndependent K (certifiedProduct (K := K)) :=
  rowForms_independent exponent4 exponent4_degree exponent4_injective rows inverse inverse_checked

theorem upper_rank : 210 ≤ finrank K (LinearMap.range (quadraticMultiplication (quadrics (K := K)))) := by
  apply rank_lower_bound _ _ products_independent
  intro i
  rw [certifiedProduct_identity]
  exact product_mem_range _ _ _

def lowerQuadrics (i : Fin 8) : Forms K 7 2 := quadrics i.castSucc

theorem lowerQuadrics_independent : LinearIndependent K (lowerQuadrics (K := K)) :=
  quadrics_independent.comp Fin.castSucc (Fin.castSucc_injective 8)

def lowerIndex (i : Fin 196) : Fin 210 := ⟨i.val,by omega⟩

theorem lowerIndex_injective : Function.Injective lowerIndex := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 210 => k.val) h)

theorem lower_rank : 196 ≤ finrank K (LinearMap.range
    (quadraticMultiplication (lowerQuadrics (K := K)))) := by
  apply rank_lower_bound _ (fun i => certifiedProduct (lowerIndex i))
    (products_independent.comp lowerIndex lowerIndex_injective)
  intro i
  rw [certifiedProduct_identity]
  let j : Fin 8 := ⟨(selected (lowerIndex i)).1.val,lower_selected i⟩
  have he : j.castSucc = (selected (lowerIndex i)).1 := Fin.ext rfl
  have hj : quadrics (K := K) (selected (lowerIndex i)).1 = lowerQuadrics j := by
    rw [lowerQuadrics,he]
  rw [hj]
  exact product_mem_range _ _ _

/-- Lower endpoint witness over every characteristic-zero field. -/
theorem lower_witness : QuarticWitness K 7 8 := by
  apply EndpointReduction.witness_of_ordered (lowerQuadrics (K := K)) lowerQuadrics_independent
  have hq := quartic_quotient_add_rank (lowerQuadrics (K := K))
  have hlo := quartic_quotient_lower_bound (lowerQuadrics (K := K)) lowerQuadrics_independent
  have hr := lower_rank (K := K)
  norm_num [expectedDimension,Nat.choose] at hq hlo ⊢
  omega

/-- Upper endpoint witness over every characteristic-zero field. -/
theorem upper_witness : QuarticWitness K 7 9 := by
  apply EndpointReduction.witness_of_ordered (quadrics (K := K)) quadrics_independent
  have hq := quartic_quotient_add_rank (quadrics (K := K))
  have hr := upper_rank (K := K)
  norm_num [expectedDimension,Nat.choose] at hq ⊢
  omega

theorem generic_seven_variables (r : ℕ) (hr : r ≤ (7+1).choose 2) : GenericQuartic K 7 r := by
  apply EndpointReduction.adjacent_endpoints_imply_generic 8 9 (by omega)
    lower_witness upper_witness (by norm_num [Counts.chi,Counts.b2,Counts.b4,Nat.choose])
    (by norm_num [Counts.chi,Counts.b2,Counts.b4,Nat.choose]) hr

end Quartic.FiniteEndpointCheckerSeven
