import Quartic.FiniteEndpointMetadata18
import Quartic.FiniteEndpointRows18
import Quartic.FiniteEndpointMinor18
import Quartic.FiniteEndpointCertificate
import Quartic.FiniteEndpointNatural

/-! The complete supplied 18-variable endpoints, instantiated from checked actual
polynomial metadata, multiplication inverse rows, and a quadratic coefficient minor. -/
namespace Quartic.FiniteEndpointCertified18
noncomputable section
open FiniteEndpointChecker FiniteEndpointCertificate
open FiniteEndpointMetadata18Data
set_option maxHeartbeats 2000000

def inverse : Fin 5985 → Nat :=
  FiniteEndpointNatural.finInverse FiniteEndpointInverse18.binaryInverse

theorem inverse_checked : checkInverse rows inverse = true := by
  unfold inverse
  rw [FiniteEndpointMetadata18Data.rows_eq_natural]
  exact FiniteEndpointNatural.checkInverse_of_bounded_equations
    (by decide) naturalRow FiniteEndpointInverse18.binaryInverse
    (fun i _ => FiniteEndpointMetadata18.naturalRow_bound i)
    FiniteEndpointRows18.all_rows_checked

def certificate : Data 18 39 40 171 5985 5928 where
  exponent₂ := exponent2
  exponent₄ := exponent4
  degree₂ := exponent2_degree
  degree₄ := exponent4_degree
  injective₂ := FiniteEndpointMetadata18.exponent2_injective
  injective₄ := FiniteEndpointMetadata18.exponent4_injective
  support := quadSupport
  rows := rows
  inverse := inverse
  inverse_checked := inverse_checked
  selected := selected
  product_supports := FiniteEndpointMetadata18.product_supports
  quadColumns := FiniteEndpointMinor18.columns
  quadMinor := FiniteEndpointMinor18.rows
  quadInverse := FiniteEndpointMinor18.inverse
  quad_inverse_checked := FiniteEndpointMinor18.inverse_checked
  quad_counts := FiniteEndpointMinor18.counts
  lower_le := by decide +kernel
  lower_selected := FiniteEndpointMetadata18.lower_selected
  lo_le_hi := by decide +kernel
  dimension₄ := by decide +kernel
  expected_lower := by decide +kernel
  expected_upper := by decide +kernel

variable {K : Type*} [Field K] [CharZero K]

theorem lower_witness : QuarticWitness K 18 39 := certificate.lower_witness

theorem upper_witness : QuarticWitness K 18 40 := certificate.upper_witness

/-- Every admissible generator count over every characteristic-zero field. -/
theorem generic (r : ℕ) (hr : r ≤ (18+1).choose 2) : GenericQuartic K 18 r :=
  certificate.generic_of_certificate (by decide +kernel) (by decide +kernel)
    (by decide +kernel) r hr

end
end Quartic.FiniteEndpointCertified18
