import Quartic.FiniteEndpointMetadata23
import Quartic.FiniteEndpointRows23
import Quartic.FiniteEndpointMinor23
import Quartic.FiniteEndpointCertificate
import Quartic.FiniteEndpointNatural

/-! The complete supplied 23-variable endpoints, instantiated from checked actual
polynomial metadata, multiplication inverse rows, and a quadratic coefficient minor. -/
namespace Quartic.FiniteEndpointCertified23
noncomputable section
open FiniteEndpointChecker FiniteEndpointCertificate
open FiniteEndpointMetadata23Data
set_option maxHeartbeats 2000000

def inverse : Fin 14950 → Nat :=
  FiniteEndpointNatural.finInverse FiniteEndpointInverse23.binaryInverse

theorem inverse_checked : checkInverse rows inverse = true := by
  unfold inverse
  rw [FiniteEndpointMetadata23Data.rows_eq_natural]
  exact FiniteEndpointNatural.checkInverse_of_bounded_equations
    (by decide) naturalRow FiniteEndpointInverse23.binaryInverse
    (fun i _ => FiniteEndpointMetadata23.naturalRow_bound i)
    FiniteEndpointRows23.all_rows_checked

def certificate : Data 23 60 61 276 14950 14790 where
  exponent₂ := exponent2
  exponent₄ := exponent4
  degree₂ := exponent2_degree
  degree₄ := exponent4_degree
  injective₂ := FiniteEndpointMetadata23.exponent2_injective
  injective₄ := FiniteEndpointMetadata23.exponent4_injective
  support := quadSupport
  rows := rows
  inverse := inverse
  inverse_checked := inverse_checked
  selected := selected
  product_supports := FiniteEndpointMetadata23.product_supports
  quadColumns := FiniteEndpointMinor23.columns
  quadMinor := FiniteEndpointMinor23.rows
  quadInverse := FiniteEndpointMinor23.inverse
  quad_inverse_checked := FiniteEndpointMinor23.inverse_checked
  quad_counts := FiniteEndpointMinor23.counts
  lower_le := by decide +kernel
  lower_selected := FiniteEndpointMetadata23.lower_selected
  lo_le_hi := by decide +kernel
  dimension₄ := by decide +kernel
  expected_lower := by decide +kernel
  expected_upper := by decide +kernel

variable {K : Type*} [Field K] [CharZero K]

theorem lower_witness : QuarticWitness K 23 60 := certificate.lower_witness

theorem upper_witness : QuarticWitness K 23 61 := certificate.upper_witness

/-- Every admissible generator count over every characteristic-zero field. -/
theorem generic (r : ℕ) (hr : r ≤ (23+1).choose 2) : GenericQuartic K 23 r :=
  certificate.generic_of_certificate (by decide +kernel) (by decide +kernel)
    (by decide +kernel) r hr

end
end Quartic.FiniteEndpointCertified23
