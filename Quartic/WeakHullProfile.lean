module

public import Quartic.WeakHullProfile.Hull
public import Quartic.HullCertificate
public import Quartic.SharpMinimization.Finite

@[expose] public section

/-!
# Scalar inequalities for all sharp profiles in dimensions 130 through 319

An explicit rational convex mixture in one certified weak-vertex cell has
exactly the profile's source dimension and image no greater than its sharp
value. The checked finite hull certificates therefore apply to every ordered
rational profile, in particular to every integral profile from an actual
subspace.
-/
namespace Quartic.WeakHullProfile
open HullCertificate ProfileCertificate SharpCertificate

/-- The finite weak-hull certificates apply to every ordered sharp profile. -/
theorem finite_profile_bounds (m:ℕ) (hmlo:130 ≤ m) (hmhi:m ≤ 319) (upper:Bool)
    (i:ℕ) (hi:i ≤ coreA (FiniteCounts.mixedCount m upper))
    (n₁ n₂ n₃:ℚ)
    (hn:0 ≤ n₃ ∧ n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ (freeW m (FiniteCounts.mixedCount m upper):ℚ))
    (d:ℤ) (hdlo:1 ≤ d) (hdhi:d<(totalA m (FiniteCounts.mixedCount m upper):ℤ))
    (hd:(i:ℚ)+n₁+n₂+n₃=(d:ℚ)) :
    ImageBounds (scalars m (FiniteCounts.upperEndpoint m) (FiniteCounts.mixedCount m upper))
      (sharpProfile (parameters m (FiniteCounts.mixedCount m upper) i) n₁ n₂ n₃) d := by
  have hc:4 ≤ FiniteCounts.mixedCount m upper :=
    (FiniteCounts.structural_binomial_counts m (by omega) hmhi upper).1
  obtain ⟨cell,helig,hpoint,himage⟩:=exists_eligible_hull m (FiniteCounts.mixedCount m upper)
    i hc hi n₁ n₂ n₃ hn d hdlo hdhi hd
  obtain ⟨left,right,hline,hinc⟩:=HullCertificate.hull_inequality m hmlo hmhi upper cell d helig
  exact hinc.mono ((hline.supports_hull hpoint).trans himage)

/-- Canonical endpoint version, independent of the finite-table presentation. -/
theorem actual_endpoint_profile_bounds (m:ℕ) (hmlo:130 ≤ m) (hmhi:m ≤ 319) (upper:Bool)
    (i:ℕ) (hi:i ≤ coreA (UniformEndpoint.mixedCount m upper))
    (n₁ n₂ n₃:ℚ)
    (hn:0 ≤ n₃ ∧ n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ (freeW m (UniformEndpoint.mixedCount m upper):ℚ))
    (d:ℤ) (hdlo:1 ≤ d) (hdhi:d<(totalA m (UniformEndpoint.mixedCount m upper):ℤ))
    (hd:(i:ℚ)+n₁+n₂+n₃=(d:ℚ)) :
    ImageBounds (scalars m (UniformEndpoint.upperEndpoint m) (UniformEndpoint.mixedCount m upper))
      (sharpProfile (parameters m (UniformEndpoint.mixedCount m upper) i) n₁ n₂ n₃) d := by
  simp only [UniformEndpoint.mixedCount_eq_table m (by omega),
    UniformEndpoint.upperEndpoint_eq_table m (by omega)] at hi hn hdhi ⊢
  exact finite_profile_bounds m hmlo hmhi upper i hi n₁ n₂ n₃ hn d hdlo hdhi hd

/-- Both original scalar tests for every nontrivial integral actual profile. -/
theorem source_scalar_inequalities (m:ℕ) (hmlo:130 ≤ m) (hmhi:m ≤ 319) (upper:Bool)
    (i n₁ n₂ n₃:ℕ) (hi:i ≤ coreA (UniformEndpoint.mixedCount m upper))
    (hn₁:n₁ ≤ freeW m (UniformEndpoint.mixedCount m upper)) (hn₂:n₂ ≤ n₁) (hn₃:n₃ ≤ n₂)
    (hdlo:0<profileDim i n₁ n₂ n₃)
    (hdhi:profileDim i n₁ n₂ n₃<totalA m (UniformEndpoint.mixedCount m upper)) :
    SharpMinimization.ImageBoundsReal
      (scalars m (UniformEndpoint.upperEndpoint m) (UniformEndpoint.mixedCount m upper))
      (UniformSurplus.sourceSharp m (UniformEndpoint.mixedCount m upper) i n₁ n₂ n₃)
      (profileDim i n₁ n₂ n₃) := by
  have h:=actual_endpoint_profile_bounds m hmlo hmhi upper i hi n₁ n₂ n₃
    ⟨by positivity,by exact_mod_cast hn₃,by exact_mod_cast hn₂,by exact_mod_cast hn₁⟩
    (profileDim i n₁ n₂ n₃) (by exact_mod_cast hdlo) (by exact_mod_cast hdhi)
    (by simp [profileDim])
  have hr:=SharpMinimization.imageBounds_cast h
  rw [← UniformSurplus.sourceSharp_eq_rational] at hr
  simpa only [Rat.cast_natCast] using hr

set_option maxRecDepth 4096 in
set_option backward.isDefEq.respectTransparency false in
/-- The outer bound at the full profile, supplied by the certified full weak vertex. -/
theorem full_profile_outer (m:ℕ) (hmlo:130 ≤ m) (hmhi:m ≤ 319) (upper:Bool) :
    (UniformEndpoint.upperEndpoint m:ℚ)*(totalA m (UniformEndpoint.mixedCount m upper):ℚ) ≤
      sharpProfile (parameters m (UniformEndpoint.mixedCount m upper)
        (coreA (UniformEndpoint.mixedCount m upper)))
        (freeW m (UniformEndpoint.mixedCount m upper))
        (freeW m (UniformEndpoint.mixedCount m upper))
        (freeW m (UniformEndpoint.mixedCount m upper)) := by
  simp only [UniformEndpoint.mixedCount_eq_table m (by omega),
    UniformEndpoint.upperEndpoint_eq_table m (by omega)]
  let c:=FiniteCounts.mixedCount m upper
  have hc:4 ≤ c := (FiniteCounts.structural_binomial_counts m (by omega) hmhi upper).1
  have hA:(coreA c:ℚ)≠0:=ne_of_gt (by exact_mod_cast coreA_pos c hc)
  have hw:(freeW m c:ℚ)≠0:=ne_of_gt (by exact_mod_cast freeW_pos m c)
  have hweak:=weakAverage_le_sharp m c (coreA c) hc le_rfl
    (freeW m c) (freeW m c) (freeW m c) ⟨by positivity,le_rfl,le_rfl,le_rfl⟩
  have hfull:=HullCertificate.full_vertex_outer m hmlo hmhi upper
  apply hfull.trans
  simp only [weakAverage,div_self hA,div_self hw,weighted,sub_self,zero_mul,zero_add,one_mul] at hweak
  change weakImage (coreA c) (coreB c) (freeW m c) (Counts.b2 (freeW m c))
    (Counts.b3 (freeW m c)) 1 3 ≤ _ at hweak
  exact hweak

/-- The outer incidence inequality on the entire nonempty source range, including d=a. -/
theorem source_outer_inequality (m:ℕ) (hmlo:130 ≤ m) (hmhi:m ≤ 319) (upper:Bool)
    (i n₁ n₂ n₃:ℕ) (hi:i ≤ coreA (UniformEndpoint.mixedCount m upper))
    (hn₁:n₁ ≤ freeW m (UniformEndpoint.mixedCount m upper)) (hn₂:n₂ ≤ n₁) (hn₃:n₃ ≤ n₂)
    (hdlo:0<profileDim i n₁ n₂ n₃)
    (hdhi:profileDim i n₁ n₂ n₃ ≤ totalA m (UniformEndpoint.mixedCount m upper)) :
    (profileDim i n₁ n₂ n₃:ℝ)*((UniformEndpoint.upperEndpoint m:ℝ)+
      (totalA m (UniformEndpoint.mixedCount m upper):ℝ)-(profileDim i n₁ n₂ n₃:ℝ)) ≤
      UniformSurplus.sourceSharp m (UniformEndpoint.mixedCount m upper) i n₁ n₂ n₃ := by
  by_cases hlt:profileDim i n₁ n₂ n₃<totalA m (UniformEndpoint.mixedCount m upper)
  · exact (source_scalar_inequalities m hmlo hmhi upper i n₁ n₂ n₃ hi hn₁ hn₂ hn₃ hdlo hlt).1
  · have heq:profileDim i n₁ n₂ n₃=totalA m (UniformEndpoint.mixedCount m upper):=by omega
    have heq':i+n₁+n₂+n₃=coreA (UniformEndpoint.mixedCount m upper)+
        3*freeW m (UniformEndpoint.mixedCount m upper):=heq
    have hi':i=coreA (UniformEndpoint.mixedCount m upper):=by omega
    have h₁:n₁=freeW m (UniformEndpoint.mixedCount m upper):=by omega
    have h₂:n₂=freeW m (UniformEndpoint.mixedCount m upper):=by omega
    have h₃:n₃=freeW m (UniformEndpoint.mixedCount m upper):=by omega
    have hfull:=full_profile_outer m hmlo hmhi upper
    have hR:(UniformEndpoint.upperEndpoint m:ℝ)*(totalA m (UniformEndpoint.mixedCount m upper):ℝ) ≤
        (sharpProfile (parameters m (UniformEndpoint.mixedCount m upper)
          (coreA (UniformEndpoint.mixedCount m upper)))
          (freeW m (UniformEndpoint.mixedCount m upper))
          (freeW m (UniformEndpoint.mixedCount m upper))
          (freeW m (UniformEndpoint.mixedCount m upper)):ℝ):=by exact_mod_cast hfull
    rw [← UniformSurplus.sourceSharp_eq_rational] at hR
    simp only [Rat.cast_natCast] at hR
    rw [heq,hi',h₁,h₂,h₃]
    nlinarith

end Quartic.WeakHullProfile
