import Quartic.FiniteEndpointMetadata22
import Quartic.FiniteEndpointRows22
import Quartic.FiniteEndpointMinor22
import Quartic.FiniteEndpointCertificate
import Quartic.FiniteEndpointNatural

/-! The complete supplied 22-variable endpoints, instantiated from checked actual
polynomial metadata, multiplication inverse rows, and a quadratic coefficient minor. -/
namespace Quartic.FiniteEndpointCertified22
noncomputable section
open FiniteEndpointChecker FiniteEndpointCertificate
open FiniteEndpointMetadata22Data
set_option maxHeartbeats 2000000

def inverse : Fin 12650 → Nat :=
  FiniteEndpointNatural.finInverse FiniteEndpointInverse22.binaryInverse

theorem inverse_checked : checkInverse rows inverse = true := by
  unfold inverse
  rw [FiniteEndpointMetadata22Data.rows_eq_natural]
  exact FiniteEndpointNatural.checkInverse_of_bounded_equations
    (by decide) naturalRow FiniteEndpointInverse22.binaryInverse
    (fun i _ => FiniteEndpointMetadata22.naturalRow_bound i)
    FiniteEndpointRows22.all_rows_checked

def certificate : Data 22 56 57 253 12650 12628 where
  exponent₂ := exponent2
  exponent₄ := exponent4
  degree₂ := exponent2_degree
  degree₄ := exponent4_degree
  injective₂ := FiniteEndpointMetadata22.exponent2_injective
  injective₄ := FiniteEndpointMetadata22.exponent4_injective
  support := quadSupport
  rows := rows
  inverse := inverse
  inverse_checked := inverse_checked
  selected := selected
  product_supports := FiniteEndpointMetadata22.product_supports
  quadColumns := FiniteEndpointMinor22.columns
  quadMinor := FiniteEndpointMinor22.rows
  quadInverse := FiniteEndpointMinor22.inverse
  quad_inverse_checked := FiniteEndpointMinor22.inverse_checked
  quad_counts := FiniteEndpointMinor22.counts
  lower_le := by decide +kernel
  lower_selected := FiniteEndpointMetadata22.lower_selected
  lo_le_hi := by decide +kernel
  dimension₄ := by decide +kernel
  expected_lower := by decide +kernel
  expected_upper := by decide +kernel

variable {K : Type*} [Field K] [CharZero K]

theorem lower_witness : QuarticWitness K 22 56 := certificate.lower_witness

theorem upper_witness : QuarticWitness K 22 57 := certificate.upper_witness

/-- Every admissible generator count over every characteristic-zero field. -/
theorem generic (r : ℕ) (hr : r ≤ (22+1).choose 2) : GenericQuartic K 22 r :=
  certificate.generic_of_certificate (by decide +kernel) (by decide +kernel)
    (by decide +kernel) r hr

end
end Quartic.FiniteEndpointCertified22
