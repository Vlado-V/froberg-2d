import Quartic.FiniteEndpointMetadata21
import Quartic.FiniteEndpointRows21
import Quartic.FiniteEndpointMinor21
import Quartic.FiniteEndpointCertificate
import Quartic.FiniteEndpointNatural

/-! The complete supplied 21-variable endpoints, instantiated from checked actual
polynomial metadata, multiplication inverse rows, and a quadratic coefficient minor. -/
namespace Quartic.FiniteEndpointCertified21
noncomputable section
open FiniteEndpointChecker FiniteEndpointCertificate
open FiniteEndpointMetadata21Data
set_option maxHeartbeats 2000000

def inverse : Fin 10626 → Nat :=
  FiniteEndpointNatural.finInverse FiniteEndpointInverse21.binaryInverse

theorem inverse_checked : checkInverse rows inverse = true := by
  unfold inverse
  rw [FiniteEndpointMetadata21Data.rows_eq_natural]
  exact FiniteEndpointNatural.checkInverse_of_bounded_equations
    (by decide) naturalRow FiniteEndpointInverse21.binaryInverse
    (fun i _ => FiniteEndpointMetadata21.naturalRow_bound i)
    FiniteEndpointRows21.all_rows_checked

def certificate : Data 21 51 52 231 10626 10506 where
  exponent₂ := exponent2
  exponent₄ := exponent4
  degree₂ := exponent2_degree
  degree₄ := exponent4_degree
  injective₂ := FiniteEndpointMetadata21.exponent2_injective
  injective₄ := FiniteEndpointMetadata21.exponent4_injective
  support := quadSupport
  rows := rows
  inverse := inverse
  inverse_checked := inverse_checked
  selected := selected
  product_supports := FiniteEndpointMetadata21.product_supports
  quadColumns := FiniteEndpointMinor21.columns
  quadMinor := FiniteEndpointMinor21.rows
  quadInverse := FiniteEndpointMinor21.inverse
  quad_inverse_checked := FiniteEndpointMinor21.inverse_checked
  quad_counts := FiniteEndpointMinor21.counts
  lower_le := by decide +kernel
  lower_selected := FiniteEndpointMetadata21.lower_selected
  lo_le_hi := by decide +kernel
  dimension₄ := by decide +kernel
  expected_lower := by decide +kernel
  expected_upper := by decide +kernel

variable {K : Type*} [Field K] [CharZero K]

theorem lower_witness : QuarticWitness K 21 51 := certificate.lower_witness

theorem upper_witness : QuarticWitness K 21 52 := certificate.upper_witness

/-- Every admissible generator count over every characteristic-zero field. -/
theorem generic (r : ℕ) (hr : r ≤ (21+1).choose 2) : GenericQuartic K 21 r :=
  certificate.generic_of_certificate (by decide +kernel) (by decide +kernel)
    (by decide +kernel) r hr

end
end Quartic.FiniteEndpointCertified21
