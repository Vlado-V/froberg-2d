module

public import Quartic.WeakHullProfile.Hull
public import Quartic.MarkedHullCertificate
public import Quartic.SharpMinimization.Finite

@[expose] public section

/-!
# Marked scalar inequalities for sharp profiles in dimensions 130 through 319

An explicit rational convex mixture in one certified weak-vertex cell has
exactly the profile's source dimension and image no greater than its sharp
value. The checked finite hull certificates therefore apply to every ordered
rational profile, in particular to every integral profile from an actual
subspace.
-/
namespace Quartic.MarkedWeakHullProfile
open Quartic.WeakHullProfile
open HullCertificate ProfileCertificate SharpCertificate

/-- The finite weak-hull certificates apply to every ordered sharp profile. -/
theorem finite_profile_bounds (m:ℕ) (hmlo:130 ≤ m) (hmhi:m ≤ 319) 
    (i:ℕ) (hi:i ≤ coreA (FiniteCounts.mixedCount m false))
    (n₁ n₂ n₃:ℚ)
    (hn:0 ≤ n₃ ∧ n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ (freeW m (FiniteCounts.mixedCount m false):ℚ))
    (d:ℤ) (hdlo:1 ≤ d) (hdhi:d<(totalA m (FiniteCounts.mixedCount m false):ℤ))
    (hd:(i:ℚ)+n₁+n₂+n₃=(d:ℚ)) :
    ImageBounds (markedScalars (scalars m (FiniteCounts.upperEndpoint m) (FiniteCounts.mixedCount m false)))
      (sharpProfile (parameters m (FiniteCounts.mixedCount m false) i) n₁ n₂ n₃) d := by
  have hc:4 ≤ FiniteCounts.mixedCount m false :=
    (FiniteCounts.structural_binomial_counts m (by omega) hmhi false).1
  obtain ⟨cell,helig,hpoint,himage⟩:=exists_eligible_hull m (FiniteCounts.mixedCount m false)
    i hc hi n₁ n₂ n₃ hn d hdlo hdhi hd
  obtain ⟨left,right,hline,hinc⟩:=MarkedHullCertificate.hull_inequality m hmlo hmhi cell d helig
  exact hinc.mono ((hline.supports_hull hpoint).trans himage)

/-- Canonical endpoint version, independent of the finite-table presentation. -/
theorem actual_endpoint_profile_bounds (m:ℕ) (hmlo:130 ≤ m) (hmhi:m ≤ 319) 
    (i:ℕ) (hi:i ≤ coreA (UniformEndpoint.mixedCount m false))
    (n₁ n₂ n₃:ℚ)
    (hn:0 ≤ n₃ ∧ n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ (freeW m (UniformEndpoint.mixedCount m false):ℚ))
    (d:ℤ) (hdlo:1 ≤ d) (hdhi:d<(totalA m (UniformEndpoint.mixedCount m false):ℤ))
    (hd:(i:ℚ)+n₁+n₂+n₃=(d:ℚ)) :
    ImageBounds (markedScalars (scalars m (UniformEndpoint.upperEndpoint m) (UniformEndpoint.mixedCount m false)))
      (sharpProfile (parameters m (UniformEndpoint.mixedCount m false) i) n₁ n₂ n₃) d := by
  simp only [UniformEndpoint.mixedCount_eq_table m (by omega),
    UniformEndpoint.upperEndpoint_eq_table m (by omega)] at hi hn hdhi ⊢
  exact finite_profile_bounds m hmlo hmhi i hi n₁ n₂ n₃ hn d hdlo hdhi hd

/-- Both original scalar tests for every nontrivial integral actual profile. -/
theorem source_scalar_inequalities (m:ℕ) (hmlo:130 ≤ m) (hmhi:m ≤ 319) 
    (i n₁ n₂ n₃:ℕ) (hi:i ≤ coreA (UniformEndpoint.mixedCount m false))
    (hn₁:n₁ ≤ freeW m (UniformEndpoint.mixedCount m false)) (hn₂:n₂ ≤ n₁) (hn₃:n₃ ≤ n₂)
    (hdlo:0<profileDim i n₁ n₂ n₃)
    (hdhi:profileDim i n₁ n₂ n₃<totalA m (UniformEndpoint.mixedCount m false)) :
    SharpMinimization.ImageBoundsReal
      (markedScalars (scalars m (UniformEndpoint.upperEndpoint m) (UniformEndpoint.mixedCount m false)))
      (UniformSurplus.sourceSharp m (UniformEndpoint.mixedCount m false) i n₁ n₂ n₃)
      (profileDim i n₁ n₂ n₃) := by
  have h:=actual_endpoint_profile_bounds m hmlo hmhi i hi n₁ n₂ n₃
    ⟨by positivity,by exact_mod_cast hn₃,by exact_mod_cast hn₂,by exact_mod_cast hn₁⟩
    (profileDim i n₁ n₂ n₃) (by exact_mod_cast hdlo) (by exact_mod_cast hdhi)
    (by simp [profileDim])
  have hr:=SharpMinimization.imageBounds_cast h
  rw [← UniformSurplus.sourceSharp_eq_rational] at hr
  simpa only [Rat.cast_natCast] using hr

end Quartic.MarkedWeakHullProfile
