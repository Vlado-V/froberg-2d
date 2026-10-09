module

public import Quartic.ConvolutionSplitProfile

@[expose] public section

/-!
# The manuscript's integral Phi bound for actual split subspaces

The ceiling-based profile estimate is obtained from the already checked core
shadow, actual monomial-layer ranks, and injective assembly into the image.
-/
noncomputable section
namespace Quartic.ConvolutionIntegralProfile
open ConvolutionFreePieces ConvolutionProfileImage ConvolutionProfileRanks
open ConvolutionProfileDimension LayerRankCounts ProfileCertificate
variable {K : Type*} [Field K]

/-- The ceiling relaxation never exceeds the sharp core shadow. -/
theorem gamma_le_coreShadow (c i : ℕ) (hc : 4 ≤ c) (hi : i ≤ coreA c) :
    gamma c i ≤ SharpCertificate.coreShadow c i := by
  rw [gamma_eq_ceiling c i hc, Int.ceil_le]
  exact_mod_cast UniformSurplus.core_shadow_linear c i hc hi

/-- The layer-count expression with the ceiling shadow is precisely Phi. -/
theorem Phi_eq_sharpCount (m c i n₁ n₂ n₃ : ℕ) :
    Phi m c i n₁ n₂ n₃ =
      sharpCount (freeW m c) (coreP c) i (coreB c) (gamma c i) n₁ n₂ n₃ := by
  have he : max (i : ℤ) (coreP c : ℤ) - (i : ℤ) = max ((coreP c : ℤ) - (i : ℤ)) 0 := by omega
  simp only [Phi, sharpCount, coreA, he, FiniteCounts.quadratics_eq_b2]
  ring

/-- The exact integral profile image estimate for every actual split source. -/
theorem split_Phi_bound [Infinite K] (m c : ℕ) (hc : 4 ≤ c)
    (L : Submodule K (Piece K (coreP c + 1) 0 1))
    (D : Fin (freeW m c) → Submodule K (Piece K (coreP c + 1) 0 0)) :
    Phi m c (Module.finrank K L)
      (levelCount (fun i => Module.finrank K (D i)) 1)
      (levelCount (fun i => Module.finrank K (D i)) 2)
      (levelCount (fun i => Module.finrank K (D i)) 3) ≤
      (Module.finrank K (quadraticImage (splitSource L D)) : ℤ) := by
  have ht : 2 ≤ coreP c + 1 := by unfold coreP; omega
  have hi : Module.finrank K L ≤ coreA c := by
    simpa only [coreA, Nat.add_sub_cancel] using core_rank_le ht L
  have h := sharp_rank_sum (fun i => Module.finrank K (D i))
    (fun i => Module.finrank K (linearLayer L D i))
    (fun b => Module.finrank K (quadraticLayer L D b))
    (fun b => Module.finrank K (cubicLayer D b))
    (coreP c) (Module.finrank K L) (coreB c) (gamma c (Module.finrank K L)) hi
    (fun i => (gamma_le_coreShadow c _ hc hi).trans (source_linear_rank_base c hc L D i))
    (fun i hi => by rw [coreB_eq_binomial]; exact_mod_cast linear_rank_full ht L D i hi)
    (quadratic_rank_base L D)
    (fun b hb => by simpa only [Nat.add_sub_cancel] using quadratic_rank_meets_one ht L D b hb)
    (fun b hb => by simpa only [Nat.add_sub_cancel] using quadratic_rank_meets_two ht L D b hb)
    (cubic_rank_incident D)
  rw [Phi_eq_sharpCount]
  apply h.trans
  exact_mod_cast layer_finrank_sum_le L D

end Quartic.ConvolutionIntegralProfile
