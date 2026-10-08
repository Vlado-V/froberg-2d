import Quartic.ConvolutionProfileRanks
import Quartic.ConvolutionProfileDimension
import Quartic.UniformSurplus

/-!
# The sharp profile bound for actual split subspaces

All dimensions here refer to genuine convolution quotient subspaces and their
quadratic multiplication images. The uniform scalar bounds therefore apply
to these split sources with no additional numerical or image-rank hypotheses.
The passage from an arbitrary subspace to a split one is a separate step.
-/
noncomputable section
namespace Quartic.ConvolutionSplitProfile
open ConvolutionFreePieces ConvolutionProfileImage ConvolutionProfileRanks
open ConvolutionProfileDimension LayerRankCounts ProfileCertificate
open UniformEndpoint UniformScalar
variable {K : Type*} [Field K] {t w : ℕ}

/-- The three profile counts recover the exact split-source dimension. -/
theorem split_source_profile_dimension (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) :
    Module.finrank K (splitSource L D) = Module.finrank K L +
      levelCount (fun i => Module.finrank K (D i)) 1 +
      levelCount (fun i => Module.finrank K (D i)) 2 +
      levelCount (fun i => Module.finrank K (D i)) 3 := by
  rw [splitSource_finrank, rank_sum_nat_eq_layers _ (fun i => output_rank_le_three (D i))]
  omega

theorem split_source_profile_dimension_real (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) :
    (Module.finrank K (splitSource L D) : ℝ) = (Module.finrank K L : ℝ) +
      (levelCount (fun i => Module.finrank K (D i)) 1 : ℝ) +
      (levelCount (fun i => Module.finrank K (D i)) 2 : ℝ) +
      (levelCount (fun i => Module.finrank K (D i)) 3 : ℝ) := by
  exact_mod_cast split_source_profile_dimension L D

theorem profile_counts_ordered (D : Fin w → Submodule K (Piece K t 0 0)) :
    (0 : ℝ) ≤ levelCount (fun i => Module.finrank K (D i)) 3 ∧
      (levelCount (fun i => Module.finrank K (D i)) 3 : ℝ) ≤
        levelCount (fun i => Module.finrank K (D i)) 2 ∧
      (levelCount (fun i => Module.finrank K (D i)) 2 : ℝ) ≤
        levelCount (fun i => Module.finrank K (D i)) 1 ∧
      (levelCount (fun i => Module.finrank K (D i)) 1 : ℝ) ≤ w := by
  have h := levelCounts_ordered (fun i => Module.finrank K (D i))
  exact ⟨by positivity, by exact_mod_cast h.1, by exact_mod_cast h.2.1,
    by exact_mod_cast h.2.2⟩

/-- The full source sharp profile bounds the actual quadratic image of every
split subspace, for every number of core and free variables. -/
theorem split_profile_bound [Infinite K] (m c : ℕ) (hc : 4 ≤ c)
    (L : Submodule K (Piece K (coreP c + 1) 0 1))
    (D : Fin (freeW m c) → Submodule K (Piece K (coreP c + 1) 0 0)) :
    UniformSurplus.sourceSharp m c (Module.finrank K L)
      (levelCount (fun i => Module.finrank K (D i)) 1)
      (levelCount (fun i => Module.finrank K (D i)) 2)
      (levelCount (fun i => Module.finrank K (D i)) 3) ≤
        (Module.finrank K (quadraticImage (splitSource L D)) : ℝ) := by
  apply (source_sharp_le_layer_sum m c hc L D).trans
  exact_mod_cast layer_finrank_sum_le L D

/-- The quantitative uniform surplus for actual split-subspace image dimensions
at every canonical endpoint with child dimension at least 320. -/
theorem uniform_image_surplus [Infinite K] (m : ℕ) (hm : 320 ≤ m) (upper : Bool)
    (L : Submodule K (Piece K (coreP (mixedCount m upper) + 1) 0 1))
    (D : Fin (freeW m (mixedCount m upper)) →
      Submodule K (Piece K (coreP (mixedCount m upper) + 1) 0 0)) :
    let c := mixedCount m upper
    let d : ℝ := Module.finrank K (splitSource L D)
    (targetCount m c : ℝ) / (totalA m c : ℝ) * d +
      (m : ℝ)^2 / 100 * min d ((totalA m c : ℝ) - d) ≤
        (Module.finrank K (quadraticImage (splitSource L D)) : ℝ) := by
  have hc := c_range m hm upper
  have ht : 2 ≤ coreP (mixedCount m upper) + 1 := by unfold coreP; omega
  have hi : Module.finrank K L ≤ coreA (mixedCount m upper) := by
    simpa only [coreA, Nat.add_sub_cancel] using core_rank_le ht L
  have h := UniformSurplus.source_uniform_surplus m hm upper _ hi _ _ _ (profile_counts_ordered D)
  dsimp only at h ⊢
  rw [← split_source_profile_dimension_real L D] at h
  exact h.trans (split_profile_bound m _ hc.1 L D)

/-- The outer scalar inequality for actual split-subspace image dimensions,
including the zero and full source subspaces. -/
theorem uniform_outer_image_bound [Infinite K] (m : ℕ) (hm : 320 ≤ m) (upper : Bool)
    (L : Submodule K (Piece K (coreP (mixedCount m upper) + 1) 0 1))
    (D : Fin (freeW m (mixedCount m upper)) →
      Submodule K (Piece K (coreP (mixedCount m upper) + 1) 0 0)) :
    let c := mixedCount m upper
    let d : ℝ := Module.finrank K (splitSource L D)
    d * ((upperEndpoint m : ℝ) + (totalA m c : ℝ) - d) ≤
      (Module.finrank K (quadraticImage (splitSource L D)) : ℝ) := by
  have hc := c_range m hm upper
  have ht : 2 ≤ coreP (mixedCount m upper) + 1 := by unfold coreP; omega
  have hi : Module.finrank K L ≤ coreA (mixedCount m upper) := by
    simpa only [coreA, Nat.add_sub_cancel] using core_rank_le ht L
  have h := UniformSurplus.source_outer_inequality m hm upper _ hi _ _ _ (profile_counts_ordered D)
  dsimp only at h ⊢
  rw [← split_source_profile_dimension_real L D] at h
  exact h.trans (split_profile_bound m _ hc.1 L D)

/-- Both numerical incidence tests now hold for actual split-subspace images.
The geometric covector-locus dimension interpretation remains separate. -/
theorem uniform_scalar_image_bounds [Infinite K] (m : ℕ) (hm : 320 ≤ m) (upper : Bool)
    (L : Submodule K (Piece K (coreP (mixedCount m upper) + 1) 0 1))
    (D : Fin (freeW m (mixedCount m upper)) →
      Submodule K (Piece K (coreP (mixedCount m upper) + 1) 0 0))
    (hdlo : 0 < Module.finrank K (splitSource L D))
    (hdhi : Module.finrank K (splitSource L D) < totalA m (mixedCount m upper)) :
    let q := upperEndpoint m
    let c := mixedCount m upper
    let a : ℝ := totalA m c
    let d : ℝ := Module.finrank K (splitSource L D)
    let E : ℝ := Module.finrank K (quadraticImage (splitSource L D))
    let J : ℝ := Counts.j m q c
    let K₃₁ : ℝ := Counts.k31 m c
    let S : ℝ := (Counts.H m q c : ℝ) + 3 + (Counts.delta m q : ℝ)
    d * ((q : ℝ) + a - d) ≤ E ∧
      (covectorR J E q a d < 0 ∨
        covectorR J E q a d - codimensionR K₃₁ S c d ≤
          max (J - (Counts.hTotal m q c : ℝ)) 0 - 1) := by
  have hc := c_range m hm upper
  have ht : 2 ≤ coreP (mixedCount m upper) + 1 := by unfold coreP; omega
  have hi : Module.finrank K L ≤ coreA (mixedCount m upper) := by
    simpa only [coreA, Nat.add_sub_cancel] using core_rank_le ht L
  have hdloR : (0 : ℝ) < Module.finrank K (splitSource L D) := by exact_mod_cast hdlo
  have hdhiR : (Module.finrank K (splitSource L D) : ℝ) < totalA m (mixedCount m upper) := by
    exact_mod_cast hdhi
  rw [split_source_profile_dimension_real L D] at hdloR hdhiR
  have h := UniformSurplus.scalar_inequalities_of_profile_bound m hm upper _ hi _ _ _ _
    (profile_counts_ordered D) hdloR hdhiR (split_profile_bound m _ hc.1 L D)
  dsimp only at h ⊢
  rw [← split_source_profile_dimension_real L D] at h
  exact h

end Quartic.ConvolutionSplitProfile
