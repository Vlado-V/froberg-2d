module

public import Quartic.FiniteEndpointMetadata29
public import Quartic.FiniteEndpointRows29
public import Quartic.FiniteEndpointMinor29
public import Quartic.FiniteEndpointCertificate
public import Quartic.FiniteEndpointNatural

@[expose] public section

/-! The complete supplied 29-variable endpoints, instantiated from checked actual
polynomial metadata, multiplication inverse rows, and a quadratic coefficient minor. -/
namespace Quartic.FiniteEndpointCertified29
noncomputable section
open FiniteEndpointChecker FiniteEndpointCertificate
open FiniteEndpointMetadata29Data
set_option maxHeartbeats 2000000

def inverse : Fin 35960 → Nat :=
  FiniteEndpointNatural.finInverse FiniteEndpointInverse29.binaryInverse

theorem inverse_checked : checkInverse rows inverse = true := by
  unfold inverse
  rw [FiniteEndpointMetadata29Data.rows_eq_natural]
  exact FiniteEndpointNatural.checkInverse_of_bounded_equations
    (by decide) naturalRow FiniteEndpointInverse29.binaryInverse
    (fun i _ => FiniteEndpointMetadata29.naturalRow_bound i)
    FiniteEndpointRows29.all_rows_checked

def certificate : Data 29 92 93 435 35960 35834 where
  exponent₂ := exponent2
  exponent₄ := exponent4
  degree₂ := exponent2_degree
  degree₄ := exponent4_degree
  injective₂ := FiniteEndpointMetadata29.exponent2_injective
  injective₄ := FiniteEndpointMetadata29.exponent4_injective
  support := quadSupport
  rows := rows
  inverse := inverse
  inverse_checked := inverse_checked
  selected := selected
  product_supports := FiniteEndpointMetadata29.product_supports
  quadColumns := FiniteEndpointMinor29.columns
  quadMinor := FiniteEndpointMinor29.rows
  quadInverse := FiniteEndpointMinor29.inverse
  quad_inverse_checked := FiniteEndpointMinor29.inverse_checked
  quad_counts := FiniteEndpointMinor29.counts
  lower_le := by decide +kernel
  lower_selected := FiniteEndpointMetadata29.lower_selected
  lo_le_hi := by decide +kernel
  dimension₄ := by decide +kernel
  expected_lower := by decide +kernel
  expected_upper := by decide +kernel

variable {K : Type*} [Field K] [CharZero K]

theorem lower_witness : QuarticWitness K 29 92 := certificate.lower_witness

theorem upper_witness : QuarticWitness K 29 93 := certificate.upper_witness

/-- Every admissible generator count over every characteristic-zero field. -/
theorem generic (r : ℕ) (hr : r ≤ (29+1).choose 2) : GenericQuartic K 29 r :=
  certificate.generic_of_certificate (by decide +kernel) (by decide +kernel)
    (by decide +kernel) r hr

end
end Quartic.FiniteEndpointCertified29
