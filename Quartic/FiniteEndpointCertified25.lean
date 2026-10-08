import Quartic.FiniteEndpointMetadata25
import Quartic.FiniteEndpointRows25
import Quartic.FiniteEndpointMinor25
import Quartic.FiniteEndpointCertificate
import Quartic.FiniteEndpointNatural

/-! The complete supplied 25-variable endpoints, instantiated from checked actual
polynomial metadata, multiplication inverse rows, and a quadratic coefficient minor. -/
namespace Quartic.FiniteEndpointCertified25
noncomputable section
open FiniteEndpointChecker FiniteEndpointCertificate
open FiniteEndpointMetadata25Data
set_option maxHeartbeats 2000000

def inverse : Fin 20475 → Nat :=
  FiniteEndpointNatural.finInverse FiniteEndpointInverse25.binaryInverse

theorem inverse_checked : checkInverse rows inverse = true := by
  unfold inverse
  rw [FiniteEndpointMetadata25Data.rows_eq_natural]
  exact FiniteEndpointNatural.checkInverse_of_bounded_equations
    (by decide) naturalRow FiniteEndpointInverse25.binaryInverse
    (fun i _ => FiniteEndpointMetadata25.naturalRow_bound i)
    FiniteEndpointRows25.all_rows_checked

def certificate : Data 25 70 71 325 20475 20335 where
  exponent₂ := exponent2
  exponent₄ := exponent4
  degree₂ := exponent2_degree
  degree₄ := exponent4_degree
  injective₂ := FiniteEndpointMetadata25.exponent2_injective
  injective₄ := FiniteEndpointMetadata25.exponent4_injective
  support := quadSupport
  rows := rows
  inverse := inverse
  inverse_checked := inverse_checked
  selected := selected
  product_supports := FiniteEndpointMetadata25.product_supports
  quadColumns := FiniteEndpointMinor25.columns
  quadMinor := FiniteEndpointMinor25.rows
  quadInverse := FiniteEndpointMinor25.inverse
  quad_inverse_checked := FiniteEndpointMinor25.inverse_checked
  quad_counts := FiniteEndpointMinor25.counts
  lower_le := by decide +kernel
  lower_selected := FiniteEndpointMetadata25.lower_selected
  lo_le_hi := by decide +kernel
  dimension₄ := by decide +kernel
  expected_lower := by decide +kernel
  expected_upper := by decide +kernel

variable {K : Type*} [Field K] [CharZero K]

theorem lower_witness : QuarticWitness K 25 70 := certificate.lower_witness

theorem upper_witness : QuarticWitness K 25 71 := certificate.upper_witness

/-- Every admissible generator count over every characteristic-zero field. -/
theorem generic (r : ℕ) (hr : r ≤ (25+1).choose 2) : GenericQuartic K 25 r :=
  certificate.generic_of_certificate (by decide +kernel) (by decide +kernel)
    (by decide +kernel) r hr

end
end Quartic.FiniteEndpointCertified25
