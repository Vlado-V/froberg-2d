import Quartic.ConvolutionProfileBound
import Quartic.SharpMinimization
import Quartic.ProfileCertificate

/-!
# Finite scalar consequences for actual convolution images

The finite profile certificates now apply to arbitrary actual source subspaces:
their integral profiles and image bounds come from the checked initial-subspace
and coefficient-layer constructions. For child dimensions 41 through 129 this
gives both scalar image tests. For dimensions 28 through 40 it gives the
integral cell inequality with the actual image dimension on the right. The
geometric interpretation of the numerical cell expression remains separate.
-/
noncomputable section
namespace Quartic.ConvolutionFiniteImages
open ConvolutionFreePieces ConvolutionProfileImage ProfileCertificate
open UniformEndpoint ConvolutionProfileBound
variable {K : Type*} [Field K]

/-- The minimum core size required by the actual profile theorem follows from
its independently checked finite endpoint counts. -/
theorem canonical_mixedCount_ge_four (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 319)
    (upper : Bool) : 4 ≤ mixedCount m upper := by
  rw [mixedCount_eq_table m hmhi]
  exact (FiniteCounts.structural_counts m hmlo hmhi upper).2.1

/-- Both finite sharp scalar tests hold for the actual quadratic image of every
nontrivial source subspace. No profile or image lower bound is assumed. -/
theorem sharp_scalar_image_bounds [Infinite K] (m : ℕ) (hmlo : 41 ≤ m)
    (hmhi : m ≤ 129) (upper : Bool)
    (S : Submodule K (Piece K (coreP (mixedCount m upper) + 1)
      (freeW m (mixedCount m upper)) 1))
    (hdlo : 0 < Module.finrank K S)
    (hdhi : Module.finrank K S < totalA m (mixedCount m upper)) :
    SharpMinimization.ImageBoundsReal
      (HullCertificate.scalars m (upperEndpoint m) (mixedCount m upper))
      (Module.finrank K (quadraticImage S) : ℝ) (Module.finrank K S : ℤ) := by
  obtain ⟨i, n₁, n₂, n₃, hi, hn₃, hn₂, hn₁, hd, hE, _⟩ :=
    exists_profile_bounds m (mixedCount m upper)
      (canonical_mixedCount_ge_four m (by omega) (by omega) upper) S
  have hn : (0 : ℝ) ≤ n₃ ∧ (n₃ : ℝ) ≤ n₂ ∧ (n₂ : ℝ) ≤ n₁ ∧
      (n₁ : ℝ) ≤ freeW m (mixedCount m upper) := by
    exact ⟨Nat.cast_nonneg _, by exact_mod_cast hn₃, by exact_mod_cast hn₂,
      by exact_mod_cast hn₁⟩
  have h := SharpMinimization.actual_endpoint_profile_bounds m hmlo hmhi upper
    i hi n₁ n₂ n₃ hn (Module.finrank K S) (by exact_mod_cast hdlo)
    (by exact_mod_cast hdhi) (by exact_mod_cast hd.symm)
  exact h.mono hE

/-- The finite sharp outer inequality includes the zero and full actual source
subspaces; their dimension bounds follow from the extracted integral profile. -/
theorem sharp_outer_image_bound [Infinite K] (m : ℕ) (hmlo : 41 ≤ m)
    (hmhi : m ≤ 129) (upper : Bool)
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
      (canonical_mixedCount_ge_four m (by omega) (by omega) upper) S
  have hn : (0 : ℝ) ≤ n₃ ∧ (n₃ : ℝ) ≤ n₂ ∧ (n₂ : ℝ) ≤ n₁ ∧
      (n₁ : ℝ) ≤ freeW m (mixedCount m upper) := by
    exact ⟨Nat.cast_nonneg _, by exact_mod_cast hn₃, by exact_mod_cast hn₂,
      by exact_mod_cast hn₁⟩
  have hdhi : Module.finrank K S ≤ totalA m (mixedCount m upper) := by
    unfold totalA
    omega
  have h := SharpMinimization.actual_endpoint_outer m hmlo hmhi upper i hi
    n₁ n₂ n₃ hn (Module.finrank K S) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd0)
    (by exact_mod_cast hdhi) (by exact_mod_cast hd.symm)
  simpa only [Int.cast_natCast] using h.trans hE

/-- The small finite certificate, with its numerical profile image expression
replaced by the dimension of the actual quadratic multiplication image.
The existential profile is ordered and has exactly the dimension of `S`.
This statement does not assert a geometric cell-dimension interpretation. -/
theorem exists_integral_cell_image_bound [Infinite K] (m : ℕ) (hmlo : 28 ≤ m)
    (hmhi : m ≤ 40) (upper : Bool)
    (S : Submodule K (Piece K (coreP (mixedCount m upper) + 1)
      (freeW m (mixedCount m upper)) 1))
    (hdlo : 0 < Module.finrank K S)
    (hdhi : Module.finrank K S < totalA m (mixedCount m upper)) :
    ∃ i n₁ n₂ n₃ : ℕ, i ≤ coreA (mixedCount m upper) ∧
      n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ freeW m (mixedCount m upper) ∧
      Module.finrank K S = i + n₁ + n₂ + n₃ ∧
      (upperEndpoint m : ℤ) * (Module.finrank K S : ℤ) +
        Cell m (mixedCount m upper) i n₁ n₂ n₃ +
        min (((mixedCount m upper : ℤ) + 4) * (Module.finrank K S : ℤ))
          (Counts.j m (upperEndpoint m) (mixedCount m upper)) ≤
        (Module.finrank K (quadraticImage S) : ℤ) := by
  obtain ⟨i, n₁, n₂, n₃, hi, hn₃, hn₂, hn₁, hd, _, hE⟩ :=
    exists_profile_bounds m (mixedCount m upper)
      (canonical_mixedCount_ge_four m hmlo (by omega) upper) S
  refine ⟨i, n₁, n₂, n₃, hi, hn₃, hn₂, hn₁, hd, ?_⟩
  have hdim : Module.finrank K S = profileDim i n₁ n₂ n₃ := hd
  have hp : (upperEndpoint m : ℤ) * (profileDim i n₁ n₂ n₃ : ℤ) +
      Cell m (mixedCount m upper) i n₁ n₂ n₃ +
      min (((mixedCount m upper : ℤ) + 4) * (profileDim i n₁ n₂ n₃ : ℤ))
        (Counts.j m (upperEndpoint m) (mixedCount m upper)) ≤
      Phi m (mixedCount m upper) i n₁ n₂ n₃ := by
    simp only [mixedCount_eq_table m (by omega), upperEndpoint_eq_table m (by omega)]
      at hi hn₁ hdhi ⊢
    exact profile_inequality m hmlo hmhi upper i n₁ n₂ n₃ hi hn₁ hn₂ hn₃
      (by omega) (by omega)
  rw [← hdim] at hp
  exact hp.trans hE

end Quartic.ConvolutionFiniteImages
