import Quartic.FiniteEndpointMetadata19
import Quartic.FiniteEndpointRows19
import Quartic.FiniteEndpointMinor19
import Quartic.FiniteEndpointCertificate
import Quartic.FiniteEndpointNatural

/-! The complete supplied 19-variable endpoints, instantiated from checked actual
polynomial metadata, multiplication inverse rows, and a quadratic coefficient minor. -/
namespace Quartic.FiniteEndpointCertified19
noncomputable section
open FiniteEndpointChecker FiniteEndpointCertificate
open FiniteEndpointMetadata19Data
set_option maxHeartbeats 2000000

def inverse : Fin 7315 → Nat :=
  FiniteEndpointNatural.finInverse FiniteEndpointInverse19.binaryInverse

theorem inverse_checked : checkInverse rows inverse = true := by
  unfold inverse
  rw [FiniteEndpointMetadata19Data.rows_eq_natural]
  exact FiniteEndpointNatural.checkInverse_of_bounded_equations
    (by decide) naturalRow FiniteEndpointInverse19.binaryInverse
    (fun i _ => FiniteEndpointMetadata19.naturalRow_bound i)
    FiniteEndpointRows19.all_rows_checked

def certificate : Data 19 43 44 190 7315 7267 where
  exponent₂ := exponent2
  exponent₄ := exponent4
  degree₂ := exponent2_degree
  degree₄ := exponent4_degree
  injective₂ := FiniteEndpointMetadata19.exponent2_injective
  injective₄ := FiniteEndpointMetadata19.exponent4_injective
  support := quadSupport
  rows := rows
  inverse := inverse
  inverse_checked := inverse_checked
  selected := selected
  product_supports := FiniteEndpointMetadata19.product_supports
  quadColumns := FiniteEndpointMinor19.columns
  quadMinor := FiniteEndpointMinor19.rows
  quadInverse := FiniteEndpointMinor19.inverse
  quad_inverse_checked := FiniteEndpointMinor19.inverse_checked
  quad_counts := FiniteEndpointMinor19.counts
  lower_le := by decide +kernel
  lower_selected := FiniteEndpointMetadata19.lower_selected
  lo_le_hi := by decide +kernel
  dimension₄ := by decide +kernel
  expected_lower := by decide +kernel
  expected_upper := by decide +kernel

variable {K : Type*} [Field K] [CharZero K]

theorem lower_witness : QuarticWitness K 19 43 := certificate.lower_witness

theorem upper_witness : QuarticWitness K 19 44 := certificate.upper_witness

/-- Every admissible generator count over every characteristic-zero field. -/
theorem generic (r : ℕ) (hr : r ≤ (19+1).choose 2) : GenericQuartic K 19 r :=
  certificate.generic_of_certificate (by decide +kernel) (by decide +kernel)
    (by decide +kernel) r hr

end
end Quartic.FiniteEndpointCertified19
