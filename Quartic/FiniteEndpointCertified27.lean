import Quartic.FiniteEndpointMetadata27
import Quartic.FiniteEndpointRows27
import Quartic.FiniteEndpointMinor27
import Quartic.FiniteEndpointCertificate
import Quartic.FiniteEndpointNatural

/-! The complete supplied 27-variable endpoints, instantiated from checked actual
polynomial metadata, multiplication inverse rows, and a quadratic coefficient minor. -/
namespace Quartic.FiniteEndpointCertified27
noncomputable section
open FiniteEndpointChecker FiniteEndpointCertificate
open FiniteEndpointMetadata27Data
set_option maxHeartbeats 2000000

def inverse : Fin 27405 → Nat :=
  FiniteEndpointNatural.finInverse FiniteEndpointInverse27.binaryInverse

theorem inverse_checked : checkInverse rows inverse = true := by
  unfold inverse
  rw [FiniteEndpointMetadata27Data.rows_eq_natural]
  exact FiniteEndpointNatural.checkInverse_of_bounded_equations
    (by decide) naturalRow FiniteEndpointInverse27.binaryInverse
    (fun i _ => FiniteEndpointMetadata27.naturalRow_bound i)
    FiniteEndpointRows27.all_rows_checked

def certificate : Data 27 81 82 378 27405 27378 where
  exponent₂ := exponent2
  exponent₄ := exponent4
  degree₂ := exponent2_degree
  degree₄ := exponent4_degree
  injective₂ := FiniteEndpointMetadata27.exponent2_injective
  injective₄ := FiniteEndpointMetadata27.exponent4_injective
  support := quadSupport
  rows := rows
  inverse := inverse
  inverse_checked := inverse_checked
  selected := selected
  product_supports := FiniteEndpointMetadata27.product_supports
  quadColumns := FiniteEndpointMinor27.columns
  quadMinor := FiniteEndpointMinor27.rows
  quadInverse := FiniteEndpointMinor27.inverse
  quad_inverse_checked := FiniteEndpointMinor27.inverse_checked
  quad_counts := FiniteEndpointMinor27.counts
  lower_le := by decide +kernel
  lower_selected := FiniteEndpointMetadata27.lower_selected
  lo_le_hi := by decide +kernel
  dimension₄ := by decide +kernel
  expected_lower := by decide +kernel
  expected_upper := by decide +kernel

variable {K : Type*} [Field K] [CharZero K]

theorem lower_witness : QuarticWitness K 27 81 := certificate.lower_witness

theorem upper_witness : QuarticWitness K 27 82 := certificate.upper_witness

/-- Every admissible generator count over every characteristic-zero field. -/
theorem generic (r : ℕ) (hr : r ≤ (27+1).choose 2) : GenericQuartic K 27 r :=
  certificate.generic_of_certificate (by decide +kernel) (by decide +kernel)
    (by decide +kernel) r hr

end
end Quartic.FiniteEndpointCertified27
