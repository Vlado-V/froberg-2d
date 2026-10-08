import Froberg.Generic
import Quartic.Main

/-! The quadratic endpoint base from the fully proved quartic development.
The imported source closure and its hashes are recorded in Quartic/PROVENANCE.txt. -/
noncomputable section
namespace Froberg
open Module
variable {K : Type*} [Field K] [CharZero K] {n r : ℕ}

/-- The degree-four endpoint for general quadrics, over every characteristic
zero field, holds in every positive number of variables. -/
theorem genericEndpoint_quadratic (hn : 0 < n) (hr : r ≤ (n + 1).choose 2) :
    GenericEndpoint K n 2 r := by
  obtain ⟨Q, hQ, hQr, hdim⟩ := Quartic.main_witness (K := K) n hn r hr
  obtain ⟨q, hq, hspan⟩ := Quartic.quadratic_subspace_has_basis Q hQ
  subst r
  let a : CoefficientIndex n 2 (finrank K Q) → K := coefficientCoordinates q
  have ha : coefficientForms K n 2 (finrank K Q) a = q :=
    coefficientCoordinates.symm_apply_apply q
  apply genericEndpoint_of_coefficient_witness hn a
  · rwa [ha]
  · unfold coefficientSpace
    rw [ha, hspan]
    change finrank K (Quartic.QuarticQuotient K n Q) = expectedEndpoint n 2 (finrank K Q)
    simpa only [Quartic.expectedDimension, expectedEndpoint, euler,
      show n + 2 * 2 - 1 = n + 3 by omega,
      show n + 2 - 1 = n + 1 by omega] using hdim

end Froberg
