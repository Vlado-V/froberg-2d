module

public import Quartic.UniformScalar.Counts
public import Quartic.UniformScalar.Incidence

@[expose] public section

/-!
# Uniform scalar transfer conditions for every child dimension at least 320

All integer structural counts and scalar domination estimates are proved at the
actual adjacent endpoints. The final theorem converts the explicit uniform
image-surplus hypothesis into the two incidence tests. `UniformSurplus` supplies
the numerical hypothesis for every sharp profile. Applying it to arbitrary
subspaces still requires the actual profile-image bound and its degeneration
interpretation; no geometric image bound is assumed implicitly here.
-/

namespace Quartic.UniformScalar

open Quartic.Counts Quartic.UniformEndpoint

/-- Both original scalar incidence inequalities follow from the manuscript's
uniform surplus, at the actual endpoint counts, for every `m≥320`. -/
theorem scalar_incidence_from_uniform_surplus
    (m : ℕ) (hm : 320 ≤ m) (upper : Bool) (d E : ℝ)
    (hdlo : 0 < d) (hdhi : d < (ProfileCertificate.totalA m (mixedCount m upper) : ℝ))
    (hE :
      (targetCount m (mixedCount m upper) : ℝ) /
        (ProfileCertificate.totalA m (mixedCount m upper) : ℝ) * d +
      (m : ℝ)^2/100 * min d ((ProfileCertificate.totalA m (mixedCount m upper) : ℝ)-d) ≤ E) :
    let q := upperEndpoint m
    let c := mixedCount m upper
    let a : ℝ := ProfileCertificate.totalA m c
    let J : ℝ := j m q c
    let K : ℝ := k31 m c
    let S : ℝ := (H m q c : ℝ)+3+(delta m q : ℝ)
    d*((q : ℝ)+a-d) ≤ E ∧
      (covectorR J E q a d < 0 ∨
        covectorR J E q a d-codimensionR K S c d ≤ max (J-(hTotal m q c : ℝ)) 0-1) := by
  have hdom := actual_domination m hm upper
  have hsign := structural_dimension_signs m hm upper
  have hJ : (0 : ℝ) ≤ (j m (upperEndpoint m) (mixedCount m upper) : ℝ) := by
    exact_mod_cast hsign.1.le
  have hTa : (targetCount m (mixedCount m upper) : ℝ) /
      (ProfileCertificate.totalA m (mixedCount m upper) : ℝ) =
      (upperEndpoint m : ℝ) + (j m (upperEndpoint m) (mixedCount m upper) : ℝ) /
        (ProfileCertificate.totalA m (mixedCount m upper) : ℝ) := by
    rw [target_count_identity m hm upper, add_div,
      mul_div_cancel_right₀ _ (ne_of_gt hdom.1)]
  have hE' : uniformLower (upperEndpoint m)
      (j m (upperEndpoint m) (mixedCount m upper))
      (ProfileCertificate.totalA m (mixedCount m upper)) ((m : ℝ)^2/100) d ≤ E := by
    unfold uniformLower
    simpa only [hTa] using hE
  have htotal : (hTotal m (upperEndpoint m) (mixedCount m upper) : ℝ) =
      (k31 m (mixedCount m upper) : ℝ) +
        ((H m (upperEndpoint m) (mixedCount m upper) : ℝ)+3+(delta m (upperEndpoint m) : ℝ)) := by
    unfold hTotal
    push_cast
    ring
  exact incidence_of_uniform_surplus _ _ _ _ _ _ _ _ _ _ hdom.1 hJ htotal hdlo hdhi
    hdom.2.2.2.2.2.le hdom.2.2.2.1 hdom.2.2.2.2.1 hE'

end Quartic.UniformScalar
