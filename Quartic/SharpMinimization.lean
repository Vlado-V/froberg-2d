import Quartic.SharpMinimization.Finite

/-!
# Sharp-profile minimization and finite scalar inequalities

For every fixed integer core dimension, the sharp expression attains its
minimum over an ordered fixed-sum real profile slice on one of the six prefix
edges. The proof combines exact polynomial concavity with explicit triangular
slice decompositions and finite Jensen inequalities.

Consequently the existing finite edge certificates establish both scalar
incidence inequalities for all ordered real profiles at integral source
dimension, for every child dimension 41 through 129 and both actual endpoints.
No geometric image-rank interpretation is claimed here.
-/
namespace Quartic.SharpMinimization
open Quartic.UniformSurplus
noncomputable section

/-- Both sharp scalar tests at canonical endpoints, on the complete real
ordered profile domain at a nontrivial integral source dimension. -/
theorem actual_endpoint_profile_bounds (m : ℕ) (hmlo : 41 ≤ m) (hmhi : m ≤ 129)
    (upper : Bool) (i : ℕ) (hi : i ≤ ProfileCertificate.coreA (UniformEndpoint.mixedCount m upper))
    (n₁ n₂ n₃ : ℝ)
    (hn : 0 ≤ n₃ ∧ n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ (ProfileCertificate.freeW m (UniformEndpoint.mixedCount m upper):ℝ))
    (d : ℤ) (hdlo : 1 ≤ d)
    (hdhi : d < (ProfileCertificate.totalA m (UniformEndpoint.mixedCount m upper):ℤ))
    (hd : (i:ℝ)+n₁+n₂+n₃=(d:ℝ)) :
    ImageBoundsReal (HullCertificate.scalars m (UniformEndpoint.upperEndpoint m) (UniformEndpoint.mixedCount m upper))
      (sourceSharp m (UniformEndpoint.mixedCount m upper) i n₁ n₂ n₃) d := by
  simp only [UniformEndpoint.mixedCount_eq_table m (by omega),
    UniformEndpoint.upperEndpoint_eq_table m (by omega)] at hi hn hdhi ⊢
  exact finite_sharp_profile_bounds m hmlo hmhi upper i hi n₁ n₂ n₃ hn d hdlo hdhi hd

/-- The full outer source range, now also at canonical endpoints. -/
theorem actual_endpoint_outer (m : ℕ) (hmlo : 41 ≤ m) (hmhi : m ≤ 129)
    (upper : Bool) (i : ℕ) (hi : i ≤ ProfileCertificate.coreA (UniformEndpoint.mixedCount m upper))
    (n₁ n₂ n₃ : ℝ)
    (hn : 0 ≤ n₃ ∧ n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ (ProfileCertificate.freeW m (UniformEndpoint.mixedCount m upper):ℝ))
    (d : ℤ) (hdlo : 1 ≤ d)
    (hdhi : d ≤ (ProfileCertificate.totalA m (UniformEndpoint.mixedCount m upper):ℤ))
    (hd : (i:ℝ)+n₁+n₂+n₃=(d:ℝ)) :
    (d:ℝ)*((UniformEndpoint.upperEndpoint m:ℝ)+
      (ProfileCertificate.totalA m (UniformEndpoint.mixedCount m upper):ℝ)-(d:ℝ)) ≤
      sourceSharp m (UniformEndpoint.mixedCount m upper) i n₁ n₂ n₃ := by
  simp only [UniformEndpoint.mixedCount_eq_table m (by omega),
    UniformEndpoint.upperEndpoint_eq_table m (by omega)] at hi hn hdhi ⊢
  exact finite_sharp_outer m hmlo hmhi upper i hi n₁ n₂ n₃ hn d hdlo hdhi hd

end
end Quartic.SharpMinimization
