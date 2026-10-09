module

public import Quartic.MarkedSharpCertificate
public import Quartic.SharpMinimization.Finite

@[expose] public section

/-! The marked sharp edge certificates extend to every ordered real profile
by the existing concave minimization theorem. -/

namespace Quartic.MarkedSharpProfile

open Quartic.UniformSurplus Quartic.UniformScalar
open Quartic.HullCertificate Quartic.FiniteCounts Quartic.SharpMinimization

noncomputable section

/-- Marked lower-endpoint incidence bounds on every ordered real profile with
nontrivial integral source dimension in the finite sharp range. -/
theorem finite_sharp_profile_bounds (m : ℕ) (hmlo : 41 ≤ m) (hmhi : m ≤ 129)
    (hm88 : m ≠ 88) (i : ℕ) (hi : i ≤ ProfileCertificate.coreA (mixedCount m false))
    (n₁ n₂ n₃ : ℝ)
    (hn : 0 ≤ n₃ ∧ n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ (ProfileCertificate.freeW m (mixedCount m false):ℝ))
    (d : ℤ) (hdlo : 1 ≤ d) (hdhi : d < (ProfileCertificate.totalA m (mixedCount m false):ℤ))
    (hd : (i:ℝ)+n₁+n₂+n₃=(d:ℝ)) :
    ImageBoundsReal (markedScalars (scalars m (upperEndpoint m) (mixedCount m false)))
      (sourceSharp m (mixedCount m false) i n₁ n₂ n₃) d := by
  have hsum : n₁+n₂+n₃=(d:ℝ)-(i:ℝ) := by linarith
  obtain ⟨e,he,hle⟩ := source_edge_reduction m (mixedCount m false) i hi n₁ n₂ n₃ hn
  rw [hsum] at he hle
  rw [sourceSharp_edge_cast] at hle
  have hlo : (i:ℤ)+(SharpCertificate.edgeLeft e:ℤ)*(ProfileCertificate.freeW m (mixedCount m false):ℤ) ≤ d := by
    have hr : (i:ℝ)+(SharpCertificate.edgeLeft e:ℝ)*(ProfileCertificate.freeW m (mixedCount m false):ℝ) ≤ (d:ℝ) := by
      linarith [he.1]
    exact_mod_cast hr
  have hhi : d ≤ (i:ℤ)+(SharpCertificate.edgeRight e:ℤ)*(ProfileCertificate.freeW m (mixedCount m false):ℤ) := by
    have hr : (d:ℝ) ≤ (i:ℝ)+(SharpCertificate.edgeRight e:ℝ)*(ProfileCertificate.freeW m (mixedCount m false):ℝ) := by
      linarith [he.2]
    exact_mod_cast hr
  have h := MarkedSharpCertificate.sharp_edge_inequalities m hmlo hmhi hm88 i hi e d ⟨hdlo,hdhi,hlo,hhi⟩
  exact (imageBounds_cast h).mono hle

end
end Quartic.MarkedSharpProfile
