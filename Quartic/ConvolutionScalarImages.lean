module

public import Quartic.ConvolutionFiniteImages
public import Quartic.WeakHullProfile

@[expose] public section

/-!
# Actual scalar image bounds throughout the infinite range m ≥ 41

The finite sharp and weak-hull ranges and the uniform surplus range are now
combined for actual subspaces. These are image-dimension inequalities; a
geometric incidence theorem is still needed to deduce simultaneous genericity.
-/
noncomputable section
namespace Quartic.ConvolutionScalarImages
open ConvolutionFreePieces ConvolutionProfileImage ProfileCertificate UniformEndpoint
open ConvolutionProfileBound ConvolutionFiniteImages
variable {K : Type*} [Field K]

/-- The weak-hull certificates apply to the actual quadratic image of every
nontrivial source subspace in their finite range. -/
theorem weak_scalar_image_bounds [Infinite K] (m : ℕ) (hmlo : 130 ≤ m)
    (hmhi : m ≤ 319) (upper : Bool)
    (S : Submodule K (Piece K (coreP (mixedCount m upper) + 1)
      (freeW m (mixedCount m upper)) 1))
    (hdlo : 0 < Module.finrank K S)
    (hdhi : Module.finrank K S < totalA m (mixedCount m upper)) :
    SharpMinimization.ImageBoundsReal
      (HullCertificate.scalars m (upperEndpoint m) (mixedCount m upper))
      (Module.finrank K (quadraticImage S) : ℝ) (Module.finrank K S : ℤ) := by
  obtain ⟨i, n₁, n₂, n₃, hi, hn₃, hn₂, hn₁, hd, hE, _⟩ :=
    exists_profile_bounds m (mixedCount m upper)
      (canonical_mixedCount_ge_four m (by omega) hmhi upper) S
  have hdim : Module.finrank K S = profileDim i n₁ n₂ n₃ := hd
  have h := WeakHullProfile.source_scalar_inequalities m hmlo hmhi upper
    i n₁ n₂ n₃ hi hn₁ hn₂ hn₃ (by omega) (by omega)
  rw [← hdim] at h
  exact h.mono hE

/-- The weak-hull outer inequality also includes zero and full actual subspaces. -/
theorem weak_outer_image_bound [Infinite K] (m : ℕ) (hmlo : 130 ≤ m)
    (hmhi : m ≤ 319) (upper : Bool)
    (S : Submodule K (Piece K (coreP (mixedCount m upper) + 1)
      (freeW m (mixedCount m upper)) 1)) :
    let d : ℝ := Module.finrank K S
    d * ((upperEndpoint m : ℝ) + (totalA m (mixedCount m upper) : ℝ) - d) ≤
      (Module.finrank K (quadraticImage S) : ℝ) := by
  dsimp only
  by_cases hd0 : Module.finrank K S = 0
  · simp only [hd0, Nat.cast_zero, zero_mul]
    exact Nat.cast_nonneg _
  obtain ⟨i, n₁, n₂, n₃, hi, hn₃, hn₂, hn₁, hd, hE, _⟩ :=
    exists_profile_bounds m (mixedCount m upper)
      (canonical_mixedCount_ge_four m (by omega) hmhi upper) S
  have hdim : Module.finrank K S = profileDim i n₁ n₂ n₃ := hd
  have hdhi : profileDim i n₁ n₂ n₃ ≤ totalA m (mixedCount m upper) := by
    unfold totalA profileDim
    omega
  have h := WeakHullProfile.source_outer_inequality m hmlo hmhi upper i n₁ n₂ n₃
    hi hn₁ hn₂ hn₃ (by omega) hdhi
  rw [← hdim] at h
  exact h.trans hE

/-- The scalar record used by the finite certificates is exactly the source
formula used in the uniform range. -/
theorem imageBoundsReal_iff_source (m q c : ℕ) (E : ℝ) (d : ℤ) :
    SharpMinimization.ImageBoundsReal (HullCertificate.scalars m q c) E d ↔
      (d : ℝ) * ((q : ℝ) + (totalA m c : ℝ) - d) ≤ E ∧
      (UniformScalar.covectorR (Counts.j m q c) E q (totalA m c) d < 0 ∨
        UniformScalar.covectorR (Counts.j m q c) E q (totalA m c) d -
          UniformScalar.codimensionR (Counts.k31 m c)
            ((Counts.H m q c : ℝ) + 3 + (Counts.delta m q : ℝ)) c d ≤
          max ((Counts.j m q c : ℝ) - (Counts.hTotal m q c : ℝ)) 0 - 1) := by
  have h := HullCertificate.scalars_original_counts m q c
  have ha : (HullCertificate.scalars m q c).a = totalA m c := rfl
  have hq : (HullCertificate.scalars m q c).q = q := rfl
  have hc : (HullCertificate.scalars m q c).c = c := rfl
  simp only [SharpMinimization.ImageBoundsReal, HullCertificate.codimension, HullCertificate.target,
    h.1, h.2.1, h.2.2.1, h.2.2.2, ha, hq, hc, Int.cast_natCast, Int.cast_add,
    Int.cast_sub, Int.cast_mul, Int.cast_max, Int.cast_ofNat, Int.cast_zero, Int.cast_one,
    UniformScalar.codimensionR]

/-- Both scalar incidence tests for every actual nontrivial subspace and
both canonical endpoints, for every child dimension at least 41. -/
theorem scalar_image_bounds [Infinite K] (m : ℕ) (hm : 41 ≤ m) (upper : Bool)
    (S : Submodule K (Piece K (coreP (mixedCount m upper) + 1)
      (freeW m (mixedCount m upper)) 1))
    (hdlo : 0 < Module.finrank K S)
    (hdhi : Module.finrank K S < totalA m (mixedCount m upper)) :
    SharpMinimization.ImageBoundsReal
      (HullCertificate.scalars m (upperEndpoint m) (mixedCount m upper))
      (Module.finrank K (quadraticImage S) : ℝ) (Module.finrank K S : ℤ) := by
  by_cases h₁ : m ≤ 129
  · exact sharp_scalar_image_bounds m hm h₁ upper S hdlo hdhi
  by_cases h₂ : m ≤ 319
  · exact weak_scalar_image_bounds m (by omega) h₂ upper S hdlo hdhi
  rw [imageBoundsReal_iff_source]
  simpa only [Int.cast_natCast] using uniform_scalar_image_bounds m (by omega) upper S hdlo hdhi

/-- The outer inequality for every actual subspace throughout the infinite
range m≥41, including zero and full source dimensions. -/
theorem outer_image_bound [Infinite K] (m : ℕ) (hm : 41 ≤ m) (upper : Bool)
    (S : Submodule K (Piece K (coreP (mixedCount m upper) + 1)
      (freeW m (mixedCount m upper)) 1)) :
    let d : ℝ := Module.finrank K S
    d * ((upperEndpoint m : ℝ) + (totalA m (mixedCount m upper) : ℝ) - d) ≤
      (Module.finrank K (quadraticImage S) : ℝ) := by
  by_cases h₁ : m ≤ 129
  · exact sharp_outer_image_bound m hm h₁ upper S
  by_cases h₂ : m ≤ 319
  · exact weak_outer_image_bound m (by omega) h₂ upper S
  exact uniform_outer_image_bound m (by omega) upper S

end Quartic.ConvolutionScalarImages
