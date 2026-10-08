import Quartic.FiniteEndpointMetadata17
import Quartic.FiniteEndpointRows17
import Quartic.FiniteEndpointMinor17
import Quartic.FiniteEndpointCertificate
import Quartic.FiniteEndpointNatural

/-! The complete supplied 17-variable endpoints, instantiated from checked actual
polynomial metadata, multiplication inverse rows, and a quadratic coefficient minor. -/
namespace Quartic.FiniteEndpointCertified17
noncomputable section
open FiniteEndpointChecker FiniteEndpointCertificate
open FiniteEndpointMetadata17Data
set_option maxHeartbeats 2000000

def inverse : Fin 4845 → Nat :=
  FiniteEndpointNatural.finInverse FiniteEndpointInverse17.binaryInverse

theorem inverse_checked : checkInverse rows inverse = true := by
  unfold inverse
  rw [FiniteEndpointMetadata17Data.rows_eq_natural]
  exact FiniteEndpointNatural.checkInverse_of_bounded_equations
    (by decide) naturalRow FiniteEndpointInverse17.binaryInverse
    (fun i _ => FiniteEndpointMetadata17.naturalRow_bound i)
    FiniteEndpointRows17.all_rows_checked

def certificate : Data 17 35 36 153 4845 4760 where
  exponent₂ := exponent2
  exponent₄ := exponent4
  degree₂ := exponent2_degree
  degree₄ := exponent4_degree
  injective₂ := FiniteEndpointMetadata17.exponent2_injective
  injective₄ := FiniteEndpointMetadata17.exponent4_injective
  support := quadSupport
  rows := rows
  inverse := inverse
  inverse_checked := inverse_checked
  selected := selected
  product_supports := FiniteEndpointMetadata17.product_supports
  quadColumns := FiniteEndpointMinor17.columns
  quadMinor := FiniteEndpointMinor17.rows
  quadInverse := FiniteEndpointMinor17.inverse
  quad_inverse_checked := FiniteEndpointMinor17.inverse_checked
  quad_counts := FiniteEndpointMinor17.counts
  lower_le := by decide +kernel
  lower_selected := FiniteEndpointMetadata17.lower_selected
  lo_le_hi := by decide +kernel
  dimension₄ := by decide +kernel
  expected_lower := by decide +kernel
  expected_upper := by decide +kernel

variable {K : Type*} [Field K] [CharZero K]

theorem lower_witness : QuarticWitness K 17 35 := certificate.lower_witness

theorem upper_witness : QuarticWitness K 17 36 := certificate.upper_witness

/-- Every admissible generator count over every characteristic-zero field. -/
theorem generic (r : ℕ) (hr : r ≤ (17+1).choose 2) : GenericQuartic K 17 r :=
  certificate.generic_of_certificate (by decide +kernel) (by decide +kernel)
    (by decide +kernel) r hr

end
end Quartic.FiniteEndpointCertified17
