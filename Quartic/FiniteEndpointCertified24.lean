import Quartic.FiniteEndpointMetadata24
import Quartic.FiniteEndpointRows24
import Quartic.FiniteEndpointMinor24
import Quartic.FiniteEndpointCertificate
import Quartic.FiniteEndpointNatural

/-! The complete supplied 24-variable endpoints, instantiated from checked actual
polynomial metadata, multiplication inverse rows, and a quadratic coefficient minor. -/
namespace Quartic.FiniteEndpointCertified24
noncomputable section
open FiniteEndpointChecker FiniteEndpointCertificate
open FiniteEndpointMetadata24Data
set_option maxHeartbeats 2000000

def inverse : Fin 17550 → Nat :=
  FiniteEndpointNatural.finInverse FiniteEndpointInverse24.binaryInverse

theorem inverse_checked : checkInverse rows inverse = true := by
  unfold inverse
  rw [FiniteEndpointMetadata24Data.rows_eq_natural]
  exact FiniteEndpointNatural.checkInverse_of_bounded_equations
    (by decide) naturalRow FiniteEndpointInverse24.binaryInverse
    (fun i _ => FiniteEndpointMetadata24.naturalRow_bound i)
    FiniteEndpointRows24.all_rows_checked

def certificate : Data 24 65 66 300 17550 17420 where
  exponent₂ := exponent2
  exponent₄ := exponent4
  degree₂ := exponent2_degree
  degree₄ := exponent4_degree
  injective₂ := FiniteEndpointMetadata24.exponent2_injective
  injective₄ := FiniteEndpointMetadata24.exponent4_injective
  support := quadSupport
  rows := rows
  inverse := inverse
  inverse_checked := inverse_checked
  selected := selected
  product_supports := FiniteEndpointMetadata24.product_supports
  quadColumns := FiniteEndpointMinor24.columns
  quadMinor := FiniteEndpointMinor24.rows
  quadInverse := FiniteEndpointMinor24.inverse
  quad_inverse_checked := FiniteEndpointMinor24.inverse_checked
  quad_counts := FiniteEndpointMinor24.counts
  lower_le := by decide +kernel
  lower_selected := FiniteEndpointMetadata24.lower_selected
  lo_le_hi := by decide +kernel
  dimension₄ := by decide +kernel
  expected_lower := by decide +kernel
  expected_upper := by decide +kernel

variable {K : Type*} [Field K] [CharZero K]

theorem lower_witness : QuarticWitness K 24 65 := certificate.lower_witness

theorem upper_witness : QuarticWitness K 24 66 := certificate.upper_witness

/-- Every admissible generator count over every characteristic-zero field. -/
theorem generic (r : ℕ) (hr : r ≤ (24+1).choose 2) : GenericQuartic K 24 r :=
  certificate.generic_of_certificate (by decide +kernel) (by decide +kernel)
    (by decide +kernel) r hr

end
end Quartic.FiniteEndpointCertified24
