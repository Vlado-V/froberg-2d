module

public import Quartic.FiniteEndpointMetadata30
public import Quartic.FiniteEndpointRows30
public import Quartic.FiniteEndpointMinor30
public import Quartic.FiniteEndpointCertificate
public import Quartic.FiniteEndpointNatural

@[expose] public section

/-! The complete supplied 30-variable endpoints, instantiated from checked actual
polynomial metadata, multiplication inverse rows, and a quadratic coefficient minor. -/
namespace Quartic.FiniteEndpointCertified30
noncomputable section
open FiniteEndpointChecker FiniteEndpointCertificate
open FiniteEndpointMetadata30Data
set_option maxHeartbeats 2000000

def inverse : Fin 40920 → Nat :=
  FiniteEndpointNatural.finInverse FiniteEndpointInverse30.binaryInverse

theorem inverse_checked : checkInverse rows inverse = true := by
  unfold inverse
  rw [FiniteEndpointMetadata30Data.rows_eq_natural]
  exact FiniteEndpointNatural.checkInverse_of_bounded_equations
    (by decide) naturalRow FiniteEndpointInverse30.binaryInverse
    (fun i _ => FiniteEndpointMetadata30.naturalRow_bound i)
    FiniteEndpointRows30.all_rows_checked

def certificate : Data 30 98 99 465 40920 40817 where
  exponent₂ := exponent2
  exponent₄ := exponent4
  degree₂ := exponent2_degree
  degree₄ := exponent4_degree
  injective₂ := FiniteEndpointMetadata30.exponent2_injective
  injective₄ := FiniteEndpointMetadata30.exponent4_injective
  support := quadSupport
  rows := rows
  inverse := inverse
  inverse_checked := inverse_checked
  selected := selected
  product_supports := FiniteEndpointMetadata30.product_supports
  quadColumns := FiniteEndpointMinor30.columns
  quadMinor := FiniteEndpointMinor30.rows
  quadInverse := FiniteEndpointMinor30.inverse
  quad_inverse_checked := FiniteEndpointMinor30.inverse_checked
  quad_counts := FiniteEndpointMinor30.counts
  lower_le := by decide +kernel
  lower_selected := FiniteEndpointMetadata30.lower_selected
  lo_le_hi := by decide +kernel
  dimension₄ := by decide +kernel
  expected_lower := by decide +kernel
  expected_upper := by decide +kernel

variable {K : Type*} [Field K] [CharZero K]

theorem lower_witness : QuarticWitness K 30 98 := certificate.lower_witness

theorem upper_witness : QuarticWitness K 30 99 := certificate.upper_witness

/-- Every admissible generator count over every characteristic-zero field. -/
theorem generic (r : ℕ) (hr : r ≤ (30+1).choose 2) : GenericQuartic K 30 r :=
  certificate.generic_of_certificate (by decide +kernel) (by decide +kernel)
    (by decide +kernel) r hr

end
end Quartic.FiniteEndpointCertified30
