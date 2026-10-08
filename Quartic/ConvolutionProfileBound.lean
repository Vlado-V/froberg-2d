import Quartic.ConvolutionInitialSplit
import Quartic.ConvolutionIntegralProfile

/-!
# Uniform profile bounds for arbitrary actual convolution subspaces

The initial-subspace construction, the exact split-source multiplication
estimates, and the monomial counts are combined with no extra rank hypotheses.
This proves the image-profile bound for every core size and every number of
free variables. Geometric incidence dimensions and the quartic transfer theorem
are separate obligations.
-/
noncomputable section
namespace Quartic.ConvolutionProfileBound
open ConvolutionFreePieces ConvolutionProfileImage ConvolutionProfileRanks
open ConvolutionProfileDimension ConvolutionInitialSplit ConvolutionSplitProfile
open ConvolutionIntegralProfile LayerRankCounts ProfileCertificate
open UniformEndpoint UniformScalar
variable {K : Type*} [Field K]

/-- Every actual source subspace has an ordered integral profile, with exactly
its source dimension, satisfying both sharp and ceiling-based image bounds. -/
theorem exists_profile_bounds [Infinite K] (m c : ℕ) (hc : 4 ≤ c)
    (S : Submodule K (Piece K (coreP c + 1) (freeW m c) 1)) :
    ∃ i n₁ n₂ n₃ : ℕ, i ≤ coreA c ∧ n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ freeW m c ∧
      Module.finrank K S = i + n₁ + n₂ + n₃ ∧
      UniformSurplus.sourceSharp m c i n₁ n₂ n₃ ≤
        (Module.finrank K (quadraticImage S) : ℝ) ∧
      Phi m c i n₁ n₂ n₃ ≤ (Module.finrank K (quadraticImage S) : ℤ) := by
  obtain ⟨L, D, hd, hE⟩ := exists_split_replacement S
  have ht : 2 ≤ coreP c + 1 := by unfold coreP; omega
  have hi : Module.finrank K L ≤ coreA c := by
    simpa only [coreA, Nat.add_sub_cancel] using core_rank_le ht L
  have hn := levelCounts_ordered (fun i => Module.finrank K (D i))
  refine ⟨Module.finrank K L, levelCount (fun i => Module.finrank K (D i)) 1,
    levelCount (fun i => Module.finrank K (D i)) 2,
    levelCount (fun i => Module.finrank K (D i)) 3, hi, hn.1, hn.2.1, hn.2.2, ?_, ?_, ?_⟩
  · rw [← hd]
    exact split_source_profile_dimension L D
  · exact (split_profile_bound m c hc L D).trans (by exact_mod_cast hE)
  · exact (split_Phi_bound m c hc L D).trans (by exact_mod_cast hE)

/-- Uniform surplus for the actual quadratic image of every source subspace,
for both canonical endpoints and every child dimension at least 320. -/
theorem uniform_image_surplus [Infinite K] (m : ℕ) (hm : 320 ≤ m) (upper : Bool)
    (S : Submodule K (Piece K (coreP (mixedCount m upper) + 1)
      (freeW m (mixedCount m upper)) 1)) :
    let c := mixedCount m upper
    let d : ℝ := Module.finrank K S
    (targetCount m c : ℝ) / (totalA m c : ℝ) * d +
      (m : ℝ)^2 / 100 * min d ((totalA m c : ℝ) - d) ≤
        (Module.finrank K (quadraticImage S) : ℝ) := by
  obtain ⟨L, D, hd, hE⟩ := exists_split_replacement S
  have h := ConvolutionSplitProfile.uniform_image_surplus m hm upper L D
  dsimp only at h ⊢
  rw [hd] at h
  exact h.trans (by exact_mod_cast hE)

/-- The outer scalar image inequality for every actual source subspace,
including the zero and full subspace. -/
theorem uniform_outer_image_bound [Infinite K] (m : ℕ) (hm : 320 ≤ m) (upper : Bool)
    (S : Submodule K (Piece K (coreP (mixedCount m upper) + 1)
      (freeW m (mixedCount m upper)) 1)) :
    let c := mixedCount m upper
    let d : ℝ := Module.finrank K S
    d * ((upperEndpoint m : ℝ) + (totalA m c : ℝ) - d) ≤
      (Module.finrank K (quadraticImage S) : ℝ) := by
  obtain ⟨L, D, hd, hE⟩ := exists_split_replacement S
  have h := ConvolutionSplitProfile.uniform_outer_image_bound m hm upper L D
  dsimp only at h ⊢
  rw [hd] at h
  exact h.trans (by exact_mod_cast hE)

/-- Both scalar incidence tests for actual images of every nontrivial source
subspace. No profile or image-rank bound remains as an assumption. -/
theorem uniform_scalar_image_bounds [Infinite K] (m : ℕ) (hm : 320 ≤ m) (upper : Bool)
    (S : Submodule K (Piece K (coreP (mixedCount m upper) + 1)
      (freeW m (mixedCount m upper)) 1))
    (hdlo : 0 < Module.finrank K S)
    (hdhi : Module.finrank K S < totalA m (mixedCount m upper)) :
    let q := upperEndpoint m
    let c := mixedCount m upper
    let a : ℝ := totalA m c
    let d : ℝ := Module.finrank K S
    let E : ℝ := Module.finrank K (quadraticImage S)
    let J : ℝ := Counts.j m q c
    let K₃₁ : ℝ := Counts.k31 m c
    let T : ℝ := (Counts.H m q c : ℝ) + 3 + (Counts.delta m q : ℝ)
    d * ((q : ℝ) + a - d) ≤ E ∧
      (covectorR J E q a d < 0 ∨
        covectorR J E q a d - codimensionR K₃₁ T c d ≤
          max (J - (Counts.hTotal m q c : ℝ)) 0 - 1) := by
  exact scalar_incidence_from_uniform_surplus m hm upper _ _
    (by exact_mod_cast hdlo) (by exact_mod_cast hdhi) (uniform_image_surplus m hm upper S)

end Quartic.ConvolutionProfileBound
