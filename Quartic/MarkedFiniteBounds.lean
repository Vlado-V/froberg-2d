module

public import Quartic.MarkedFiniteBoundsCore
public import Quartic.MarkedSharpProfile
public import Quartic.MarkedWeakHullProfile
public import Quartic.ConvolutionFiniteImages

@[expose] public section

/-! The stronger marked incidence bounds throughout the finite induction
range. The small range uses the literal Cell profile; dimensions 41 through
319 use the actual sharp image bound and the Grassmannian stratum budget. -/

namespace Quartic.MarkedFiniteBounds

set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

open Quartic.Counts Quartic.HullCertificate Quartic.ProfileCertificate
open Quartic.SharpMinimization Quartic.UniformScalar
open Quartic.UniformEndpoint
open Quartic.MarkedProfileBounds

/-- The transfer count is the canonical lower parent endpoint. -/
theorem finite_lower_parent_count (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 319) :
    upperEndpoint m + mixedCount m false + 4 = lowerEndpoint (m + 3) := by
  rw [upperEndpoint_eq_table m (by omega), mixedCount_eq_table m hmhi,
    lowerEndpoint_eq_table (m + 3) (by omega)]
  exact (FiniteCounts.structural_counts m hmlo hmhi false).1.symm

set_option maxRecDepth 10000 in
private theorem integral_parent_88 :
    chi (88 + 3) (upperEndpoint 88 + mixedCount 88 false + 4) = 0 := by
  rw [upperEndpoint_eq_table 88 (by decide), mixedCount_eq_table 88 (by decide)]
  decide +kernel

/-- The marked scalar tests for every integral ordered profile in the sharp
and weak-hull ranges, with the positive parent Euler hypothesis excluding the
unique integral endpoint in this range. -/
theorem source_scalar_inequalities (m : ℕ) (hmlo : 41 ≤ m) (hmhi : m ≤ 319)
    (hpos : 0 < chi (m + 3) (upperEndpoint m + mixedCount m false + 4))
    (i n₁ n₂ n₃ : ℕ) (hi : i ≤ coreA (mixedCount m false))
    (hn₁ : n₁ ≤ freeW m (mixedCount m false)) (hn₂ : n₂ ≤ n₁) (hn₃ : n₃ ≤ n₂)
    (hdlo : 0 < profileDim i n₁ n₂ n₃)
    (hdhi : profileDim i n₁ n₂ n₃ < totalA m (mixedCount m false)) :
    ImageBoundsReal (markedScalars (scalars m (upperEndpoint m) (mixedCount m false)))
      (UniformSurplus.sourceSharp m (mixedCount m false) i n₁ n₂ n₃) (profileDim i n₁ n₂ n₃) := by
  by_cases hm : m ≤ 129
  · have hm88 : m ≠ 88 := by
      intro h
      subst m
      rw [integral_parent_88] at hpos
      omega
    simp only [mixedCount_eq_table m hmhi, upperEndpoint_eq_table m (by omega)]
      at hi hn₁ hdhi ⊢
    apply MarkedSharpProfile.finite_sharp_profile_bounds m hmlo hm hm88 i hi n₁ n₂ n₃
      ⟨by positivity, by exact_mod_cast hn₃, by exact_mod_cast hn₂, by exact_mod_cast hn₁⟩
      (profileDim i n₁ n₂ n₃) (by exact_mod_cast hdlo) (by exact_mod_cast hdhi)
    simp [profileDim]
  · exact MarkedWeakHullProfile.source_scalar_inequalities m (by omega) hmhi
      i n₁ n₂ n₃ hi hn₁ hn₂ hn₃ hdlo hdhi

/-- Original-count form of the marked covector inequality on all profiles in
dimensions 41 through 319. -/
theorem source_covector_bound (m : ℕ) (hmlo : 41 ≤ m) (hmhi : m ≤ 319)
    (hpos : 0 < chi (m + 3) (upperEndpoint m + mixedCount m false + 4))
    (i n₁ n₂ n₃ : ℕ) (hi : i ≤ coreA (mixedCount m false))
    (hn₁ : n₁ ≤ freeW m (mixedCount m false)) (hn₂ : n₂ ≤ n₁) (hn₃ : n₃ ≤ n₂)
    (hdlo : 0 < profileDim i n₁ n₂ n₃)
    (hdhi : profileDim i n₁ n₂ n₃ < totalA m (mixedCount m false)) :
    MarkedCovectorBound m (upperEndpoint m) (mixedCount m false)
      (UniformSurplus.sourceSharp m (mixedCount m false) i n₁ n₂ n₃) (profileDim i n₁ n₂ n₃) :=
  marked_covector_bound_of_imageBounds _ _ _ _ _ hpos
    (source_scalar_inequalities m hmlo hmhi hpos i n₁ n₂ n₃ hi hn₁ hn₂ hn₃ hdlo hdhi)

/-- The small-range Cell-stratum covector test, at the canonical endpoints. -/
theorem small_profile_covector_bound (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 40)
    (i n₁ n₂ n₃ : ℕ) (hi : i ≤ coreA (mixedCount m false))
    (hn₁ : n₁ ≤ freeW m (mixedCount m false)) (hn₂ : n₂ ≤ n₁) (hn₃ : n₃ ≤ n₂)
    (hdlo : 0 < profileDim i n₁ n₂ n₃)
    (hdhi : profileDim i n₁ n₂ n₃ < totalA m (mixedCount m false)) :
    let q := upperEndpoint m
    let c := mixedCount m false
    let d : ℤ := profileDim i n₁ n₂ n₃
    let R := j m q c - Phi m c i n₁ n₂ n₃ + q * d + Cell m c i n₁ n₂ n₃ - 1
    R < 0 ∨ R - markedCodimension m q c d ≤ chi (m + 3) (q + c + 4) - 2 := by
  dsimp only
  rw [← transfer_euler_identity]
  simp only [mixedCount_eq_table m (by omega), upperEndpoint_eq_table m (by omega)]
    at hi hn₁ hdhi ⊢
  exact profile_marked_inequality m hmlo hmhi i n₁ n₂ n₃ hi hn₁ hn₂ hn₃ hdlo hdhi

open Quartic.ConvolutionFreePieces Quartic.ConvolutionProfileImage
open Quartic.ConvolutionProfileBound Quartic.ConvolutionFiniteImages

/-- The marked covector estimate for the actual multiplication image of each
nontrivial source subspace. Its profile and image bound are constructed, rather
than supplied as hypotheses. -/
theorem actual_covector_bound {K : Type*} [Field K] [Infinite K]
    (m : ℕ) (hmlo : 41 ≤ m) (hmhi : m ≤ 319)
    (hpos : 0 < chi (m + 3) (upperEndpoint m + mixedCount m false + 4))
    (S : Submodule K (Piece K (coreP (mixedCount m false) + 1)
      (freeW m (mixedCount m false)) 1))
    (hdlo : 0 < Module.finrank K S)
    (hdhi : Module.finrank K S < totalA m (mixedCount m false)) :
    MarkedCovectorBound m (upperEndpoint m) (mixedCount m false)
      (Module.finrank K (quadraticImage S)) (Module.finrank K S) := by
  obtain ⟨i, n₁, n₂, n₃, hi, hn₃, hn₂, hn₁, hd, hE, _⟩ :=
    exists_profile_bounds m (mixedCount m false)
      (canonical_mixedCount_ge_four m (by omega) hmhi false) S
  have hd' : Module.finrank K S = profileDim i n₁ n₂ n₃ := hd
  have hb := source_covector_bound m hmlo hmhi hpos i n₁ n₂ n₃ hi hn₁ hn₂ hn₃
    (by omega) (by omega)
  rw [← hd'] at hb
  exact hb.mono hE

end Quartic.MarkedFiniteBounds
