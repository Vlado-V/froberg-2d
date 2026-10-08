import Quartic.FiniteEndpointCheckerSupport9
import Quartic.FiniteEndpointCertificate

/-! The supplied nine-variable endpoints instantiate the common finite-certificate
soundness theorem. All algebraic rank conclusions come from that theorem; the
fields below contain checked finite data and numerical endpoint identities. -/
namespace Quartic.FiniteEndpointCheckerNine
open FiniteEndpointCertificate
open FiniteEndpointCheckerData9 FiniteEndpointCheckerSupport9

/-- The complete literal-support certificate for the supplied nine-variable family. -/
def certificate : Data 9 12 13 45 495 474 where
  exponent₂ := exponent2
  exponent₄ := exponent4
  degree₂ := exponent2_degree
  degree₄ := exponent4_degree
  injective₂ := exponent2_injective
  injective₄ := exponent4_injective
  support := quadSupport
  rows := rows
  inverse := inverse
  inverse_checked := inverse_checked
  selected := selected
  product_supports := product_supports
  quadColumns := quadColumns
  quadMinor := quadMinor
  quadInverse := quadInverse
  quad_inverse_checked := quad_inverse_checked
  quad_counts := quad_coefficient_counts
  lower_le := by decide
  lower_selected := lower_selected
  lo_le_hi := by decide
  dimension₄ := by decide
  expected_lower := by decide
  expected_upper := by decide

variable {K : Type*} [Field K] [CharZero K]

/-- 12 explicit quadrics attain the positive lower endpoint. -/
theorem lower_witness : QuarticWitness K 9 12 := certificate.lower_witness

/-- 13 explicit quadrics generate every quartic. -/
theorem upper_witness : QuarticWitness K 9 13 := certificate.upper_witness

/-- The complete nine-variable generic theorem over every characteristic-zero field. -/
theorem generic_nine_variables (r : ℕ) (hr : r ≤ (9+1).choose 2) :
    GenericQuartic K 9 r :=
  certificate.generic_of_certificate (by decide) (by decide) (by decide) r hr

end Quartic.FiniteEndpointCheckerNine
