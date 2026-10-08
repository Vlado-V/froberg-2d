import Quartic.FiniteEndpointMetadata28
import Quartic.FiniteEndpointRows28
import Quartic.FiniteEndpointMinor28
import Quartic.FiniteEndpointCertificate
import Quartic.FiniteEndpointNatural

/-! The complete supplied 28-variable endpoints, instantiated from checked actual
polynomial metadata, multiplication inverse rows, and a quadratic coefficient minor. -/
namespace Quartic.FiniteEndpointCertified28
noncomputable section
open FiniteEndpointChecker FiniteEndpointCertificate
open FiniteEndpointMetadata28Data
set_option maxHeartbeats 2000000

def inverse : Fin 31465 → Nat :=
  FiniteEndpointNatural.finInverse FiniteEndpointInverse28.binaryInverse

theorem inverse_checked : checkInverse rows inverse = true := by
  unfold inverse
  rw [FiniteEndpointMetadata28Data.rows_eq_natural]
  exact FiniteEndpointNatural.checkInverse_of_bounded_equations
    (by decide) naturalRow FiniteEndpointInverse28.binaryInverse
    (fun i _ => FiniteEndpointMetadata28.naturalRow_bound i)
    FiniteEndpointRows28.all_rows_checked

def certificate : Data 28 86 87 406 31465 31261 where
  exponent₂ := exponent2
  exponent₄ := exponent4
  degree₂ := exponent2_degree
  degree₄ := exponent4_degree
  injective₂ := FiniteEndpointMetadata28.exponent2_injective
  injective₄ := FiniteEndpointMetadata28.exponent4_injective
  support := quadSupport
  rows := rows
  inverse := inverse
  inverse_checked := inverse_checked
  selected := selected
  product_supports := FiniteEndpointMetadata28.product_supports
  quadColumns := FiniteEndpointMinor28.columns
  quadMinor := FiniteEndpointMinor28.rows
  quadInverse := FiniteEndpointMinor28.inverse
  quad_inverse_checked := FiniteEndpointMinor28.inverse_checked
  quad_counts := FiniteEndpointMinor28.counts
  lower_le := by decide +kernel
  lower_selected := FiniteEndpointMetadata28.lower_selected
  lo_le_hi := by decide +kernel
  dimension₄ := by decide +kernel
  expected_lower := by decide +kernel
  expected_upper := by decide +kernel

variable {K : Type*} [Field K] [CharZero K]

theorem lower_witness : QuarticWitness K 28 86 := certificate.lower_witness

theorem upper_witness : QuarticWitness K 28 87 := certificate.upper_witness

/-- Every admissible generator count over every characteristic-zero field. -/
theorem generic (r : ℕ) (hr : r ≤ (28+1).choose 2) : GenericQuartic K 28 r :=
  certificate.generic_of_certificate (by decide +kernel) (by decide +kernel)
    (by decide +kernel) r hr

end
end Quartic.FiniteEndpointCertified28
