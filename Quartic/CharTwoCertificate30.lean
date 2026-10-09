module

public import Quartic.CharTwoCertificateSquare
public import Quartic.FiniteEndpointCertified30

@[expose] public section

/-! Characteristic-two endpoints using the existing certified family in 30 variables.
The additional inverse bit certifies a surviving fourth power. -/
noncomputable section
namespace Quartic.CharTwoCertificate30
open FiniteEndpointCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

abbrev certificate := FiniteEndpointCertified30.certificate

theorem first_exponent :
    certificate.exponent₄ (0 : Fin 40920) = Finsupp.single (0 : Fin 30) 4 := by
  change FiniteEndpointCheckerPolynomial.listExponent (FiniteEndpointMetadata30Data.vars4 0) = _
  have hv : FiniteEndpointMetadata30Data.vars4 0 = [0, 0, 0, 0] := by decide +kernel
  rw [hv]
  ext i
  by_cases hi : i = 0
  · subst i
    simp [FiniteEndpointCheckerPolynomial.listExponent]
  · simp [FiniteEndpointCheckerPolynomial.listExponent, Finsupp.single_apply, hi, Ne.symm hi]

theorem surviving_bit : (certificate.inverse (0 : Fin 40920)).testBit 40817 = true := by
  decide +kernel

variable {K : Type*} [Field K] [CharP K 2]

theorem lower_witness : QuarticWitness K 30 98 :=
  CharTwoCertificate.lower_witness certificate

theorem upper_witness : QuarticWitness K 30 99 :=
  CharTwoCertificate.upper_witness certificate

theorem marked_lower : MarkedLowerWitness K 30 98 :=
  CharTwoCertificate.marked_of_coordinate_inverse_bit certificate
    (by decide +kernel) (0 : Fin 30) (0 : Fin 40920) ⟨40817, by decide +kernel⟩
    first_exponent (by decide +kernel) surviving_bit

theorem generic (r : ℕ) (hr : r ≤ (30 + 1).choose 2) : GenericQuartic K 30 r :=
  CharTwoCertificate.generic_of_certificate certificate
    (by decide +kernel) (by decide +kernel) (by decide +kernel) r hr

end Quartic.CharTwoCertificate30
