import Quartic.FiniteEndpointMetadata26
import Quartic.FiniteEndpointRows26
import Quartic.FiniteEndpointMinor26
import Quartic.FiniteEndpointCertificate
import Quartic.FiniteEndpointNatural

/-! The complete supplied 26-variable endpoints, instantiated from checked actual
polynomial metadata, multiplication inverse rows, and a quadratic coefficient minor. -/
namespace Quartic.FiniteEndpointCertified26
noncomputable section
open FiniteEndpointChecker FiniteEndpointCertificate
open FiniteEndpointMetadata26Data
set_option maxHeartbeats 2000000

def inverse : Fin 23751 → Nat :=
  FiniteEndpointNatural.finInverse FiniteEndpointInverse26.binaryInverse

theorem inverse_checked : checkInverse rows inverse = true := by
  unfold inverse
  rw [FiniteEndpointMetadata26Data.rows_eq_natural]
  exact FiniteEndpointNatural.checkInverse_of_bounded_equations
    (by decide) naturalRow FiniteEndpointInverse26.binaryInverse
    (fun i _ => FiniteEndpointMetadata26.naturalRow_bound i)
    FiniteEndpointRows26.all_rows_checked

def certificate : Data 26 75 76 351 23751 23550 where
  exponent₂ := exponent2
  exponent₄ := exponent4
  degree₂ := exponent2_degree
  degree₄ := exponent4_degree
  injective₂ := FiniteEndpointMetadata26.exponent2_injective
  injective₄ := FiniteEndpointMetadata26.exponent4_injective
  support := quadSupport
  rows := rows
  inverse := inverse
  inverse_checked := inverse_checked
  selected := selected
  product_supports := FiniteEndpointMetadata26.product_supports
  quadColumns := FiniteEndpointMinor26.columns
  quadMinor := FiniteEndpointMinor26.rows
  quadInverse := FiniteEndpointMinor26.inverse
  quad_inverse_checked := FiniteEndpointMinor26.inverse_checked
  quad_counts := FiniteEndpointMinor26.counts
  lower_le := by decide +kernel
  lower_selected := FiniteEndpointMetadata26.lower_selected
  lo_le_hi := by decide +kernel
  dimension₄ := by decide +kernel
  expected_lower := by decide +kernel
  expected_upper := by decide +kernel

variable {K : Type*} [Field K] [CharZero K]

theorem lower_witness : QuarticWitness K 26 75 := certificate.lower_witness

theorem upper_witness : QuarticWitness K 26 76 := certificate.upper_witness

/-- Every admissible generator count over every characteristic-zero field. -/
theorem generic (r : ℕ) (hr : r ≤ (26+1).choose 2) : GenericQuartic K 26 r :=
  certificate.generic_of_certificate (by decide +kernel) (by decide +kernel)
    (by decide +kernel) r hr

end
end Quartic.FiniteEndpointCertified26
