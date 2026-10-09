module

public import Froberg.GenericMonotonicity
public import Quartic.Generic
public import Quartic.Multiplication

@[expose] public section

/-! Transfer the actual quartic quotient statement to the uniform endpoint API. -/
noncomputable section
namespace Froberg.QuadraticGenericBridge
open Module
variable {K : Type} [Field K] [Infinite K] {n r : ℕ}

theorem endpoint_of_witness (hn : 0 < n) (hw : Quartic.QuarticWitness K n r) :
    GenericEndpoint K n 2 r := by
  obtain ⟨Q,hQ,hQr,hdim⟩ := hw
  obtain ⟨q,hq,hspan⟩ := Quartic.quadratic_subspace_has_basis Q hQ
  subst r
  let a : CoefficientIndex n 2 (finrank K Q) → K := coefficientCoordinates q
  have ha : coefficientForms K n 2 (finrank K Q) a=q :=
    coefficientCoordinates.symm_apply_apply q
  apply genericEndpoint_of_coefficient_witness hn a
  · rwa [ha]
  · unfold coefficientSpace
    rw [ha,hspan]
    change finrank K (Quartic.QuarticQuotient K n Q)=expectedEndpoint n 2 (finrank K Q)
    simpa only [Quartic.expectedDimension,expectedEndpoint,euler,
      show n+2*2-1=n+3 by omega,show n+2-1=n+1 by omega] using hdim

theorem endpoint_of_generic (hn : 0 < n) (hg : Quartic.GenericQuartic K n r) :
    GenericEndpoint K n 2 r :=
  endpoint_of_witness hn (Quartic.generic_implies_witness K n r hg)

theorem criticalDefect_zero (hn : 0 < n)
    (hg : ∀ r,r ≤ (n+1).choose 2 → Quartic.GenericQuartic K n r) :
    criticalDefect K n 2=0 := by
  have hlbound := lowerCount_le_monomial_count hn 2
  have hubound := upperCount_le_monomial_count hn 2
  have hlo := endpoint_of_generic hn (hg (lowerCount n 2) (by simpa using hlbound))
  have hhi := endpoint_of_generic hn (hg (upperCount n 2) (by simpa using hubound))
  have hcL := (genericEndpoint_iff_genericCokernel hn hlbound).mp hlo
  have hcU := (genericEndpoint_iff_genericCokernel hn hubound).mp hhi
  have hsignL := euler_lowerCount_nonneg hn 2
  have hsignU := euler_upperCount_nonpos hn 2
  have hhom := generic_euler (K := K) hn hlbound
  unfold expectedEndpoint at hcL hcU
  unfold criticalDefect
  omega

end Froberg.QuadraticGenericBridge
