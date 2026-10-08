import Quartic.FiniteEndpointMetadata20
import Quartic.FiniteEndpointRows20
import Quartic.FiniteEndpointMinor20
import Quartic.FiniteEndpointCertificate
import Quartic.FiniteEndpointNatural

/-! The complete supplied 20-variable endpoints, instantiated from checked actual
polynomial metadata, multiplication inverse rows, and a quadratic coefficient minor. -/
namespace Quartic.FiniteEndpointCertified20
noncomputable section
open FiniteEndpointChecker FiniteEndpointCertificate
open FiniteEndpointMetadata20Data
set_option maxHeartbeats 2000000

def inverse : Fin 8855 → Nat :=
  FiniteEndpointNatural.finInverse FiniteEndpointInverse20.binaryInverse

theorem inverse_checked : checkInverse rows inverse = true := by
  unfold inverse
  rw [FiniteEndpointMetadata20Data.rows_eq_natural]
  exact FiniteEndpointNatural.checkInverse_of_bounded_equations
    (by decide) naturalRow FiniteEndpointInverse20.binaryInverse
    (fun i _ => FiniteEndpointMetadata20.naturalRow_bound i)
    FiniteEndpointRows20.all_rows_checked

def certificate : Data 20 47 48 210 8855 8789 where
  exponent₂ := exponent2
  exponent₄ := exponent4
  degree₂ := exponent2_degree
  degree₄ := exponent4_degree
  injective₂ := FiniteEndpointMetadata20.exponent2_injective
  injective₄ := FiniteEndpointMetadata20.exponent4_injective
  support := quadSupport
  rows := rows
  inverse := inverse
  inverse_checked := inverse_checked
  selected := selected
  product_supports := FiniteEndpointMetadata20.product_supports
  quadColumns := FiniteEndpointMinor20.columns
  quadMinor := FiniteEndpointMinor20.rows
  quadInverse := FiniteEndpointMinor20.inverse
  quad_inverse_checked := FiniteEndpointMinor20.inverse_checked
  quad_counts := FiniteEndpointMinor20.counts
  lower_le := by decide +kernel
  lower_selected := FiniteEndpointMetadata20.lower_selected
  lo_le_hi := by decide +kernel
  dimension₄ := by decide +kernel
  expected_lower := by decide +kernel
  expected_upper := by decide +kernel

variable {K : Type*} [Field K] [CharZero K]

theorem lower_witness : QuarticWitness K 20 47 := certificate.lower_witness

theorem upper_witness : QuarticWitness K 20 48 := certificate.upper_witness

/-- Every admissible generator count over every characteristic-zero field. -/
theorem generic (r : ℕ) (hr : r ≤ (20+1).choose 2) : GenericQuartic K 20 r :=
  certificate.generic_of_certificate (by decide +kernel) (by decide +kernel)
    (by decide +kernel) r hr

end
end Quartic.FiniteEndpointCertified20
