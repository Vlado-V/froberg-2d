module

public import Quartic.ConvolutionProfileCoordinates
public import Quartic.ConvolutionFiniteImages
public import Quartic.IteratedCovectorCharts
public import Quartic.ProfileOuterFinite
public import Quartic.ConvolutionOuterIncidence

@[expose] public section

/-! # The finite image budget for the actual polynomial profile charts -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Quartic.ConvolutionProfileChartBound
open Module ConvolutionFreePieces ConvolutionInitialImage ConvolutionInitialSplit
open ConvolutionProfileCoordinates ProfileChartBound ProfileCertificate LayerRankCounts
open UniformEndpoint ConvolutionProfileImage ConvolutionProfileRanks
variable {K : Type*} [Field K] {t w : ℕ}

theorem ranks_le (ht : 2 ≤ t) (S : Submodule K (Piece K t w 1)) (i : Fin (w+1)) :
    ranks ht S i ≤ blockDimensions (2*(t-1)) w i := by
  have h := Submodule.finrank_le (FilteredImage.initialPiece
    (fun i => Fin (blockDimensions (2*(t-1)) w i) → K)
    (S.map (ConvolutionProfileCoordinates.coordinates ht).toLinearMap) i)
  simpa only [ranks,Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using h

theorem ranks_sum (ht : 2 ≤ t) (S : Submodule K (Piece K t w 1)) :
    (∑ i,ranks ht S i)=finrank K S := by
  simp only [ranks]
  rw [FilteredImage.sum_initialPiece_finrank,(ConvolutionProfileCoordinates.coordinates ht).finrank_map_eq]

theorem ranks_as_blocks (ht : 2 ≤ t) (S : Submodule K (Piece K t w 1)) :
    ranks ht S=blockRanks (ranks ht S 0) (fun i => ranks ht S i.succ) := by
  funext i
  induction i using Fin.cases <;> rfl

theorem ranks_levelCount (ht : 2 ≤ t) (S : Submodule K (Piece K t w 1)) (h : ℕ) :
    levelCount (fun i => ranks ht S i.succ) h=
      levelCount (fun i => finrank K (freePart (initial S) i)) h := by
  simp only [ranks_succ]
  exact levelCount_permutation (fun i => finrank K (freePart (initial S) i))
    (OrderedDegreeOne.freePermutation w) h

/-- The actual prefix profile satisfies the integral image estimate. -/
theorem profile_Phi_le_image [Infinite K] (m c : ℕ) (hc : 4 ≤ c)
    (ht : 2 ≤ coreP c+1)
    (S : Submodule K (Piece K (coreP c+1) (freeW m c) 1)) :
    Phi m c (ranks ht S 0)
      (levelCount (fun i => ranks ht S i.succ) 1)
      (levelCount (fun i => ranks ht S i.succ) 2)
      (levelCount (fun i => ranks ht S i.succ) 3) ≤
      (finrank K (ConvolutionProfileImage.quadraticImage S):ℤ) := by
  rw [ranks_zero,ranks_levelCount,ranks_levelCount,ranks_levelCount]
  have h := ConvolutionIntegralProfile.split_Phi_bound m c hc
    (corePart (initial S)) (freePart (initial S))
  rw [←initial_eq_split] at h
  exact h.trans (by exact_mod_cast quadraticImage_initial_finrank_le S)

/-- Genuine chart parameters are bounded by the Cell expression of the same
actual prefix profile used in the image theorem. -/
theorem parameterCount_le_profile_Cell (m c : ℕ) (ht : 2 ≤ coreP c+1)
    (S : Submodule K (Piece K (coreP c+1) (freeW m c) 1)) :
    (IteratedBlockCharts.parameterCount (blockDimensions (2*((coreP c+1)-1)) (freeW m c))
      (ranks ht S):ℤ) ≤ Cell m c (ranks ht S 0)
        (levelCount (fun i => ranks ht S i.succ) 1)
        (levelCount (fun i => ranks ht S i.succ) 2)
        (levelCount (fun i => ranks ht S i.succ) 3) := by
  conv_lhs => rw [ranks_as_blocks]
  apply parameterCount_le_Cell
  · simpa only [coreA,Nat.add_sub_cancel,blockDimensions,Fin.cons_zero] using ranks_le ht S 0
  · intro i
    exact ranks_le ht S i.succ

/-- The finite numerical test is valid for the literal chart profile, rather
than merely for some unrelated existential profile. -/
theorem profile_integral_cell_image_bound [Infinite K] (m : ℕ) (hmlo : 28 ≤ m)
    (hmhi : m ≤ 40) (upper : Bool)
    (ht : 2 ≤ coreP (mixedCount m upper)+1)
    (S : Submodule K (Piece K (coreP (mixedCount m upper)+1) (freeW m (mixedCount m upper)) 1))
    (hdlo : 0 < finrank K S) (hdhi : finrank K S < totalA m (mixedCount m upper)) :
    (upperEndpoint m:ℤ)*(finrank K S:ℤ)+
      Cell m (mixedCount m upper) (ranks ht S 0)
        (levelCount (fun i => ranks ht S i.succ) 1)
        (levelCount (fun i => ranks ht S i.succ) 2)
        (levelCount (fun i => ranks ht S i.succ) 3)+
      min (((mixedCount m upper:ℤ)+4)*(finrank K S:ℤ))
        (Counts.j m (upperEndpoint m) (mixedCount m upper)) ≤
      (finrank K (ConvolutionProfileImage.quadraticImage S):ℤ) := by
  have hi : ranks ht S 0 ≤ coreA (mixedCount m upper) := by
    simpa only [coreA,Nat.add_sub_cancel,blockDimensions,Fin.cons_zero] using ranks_le ht S 0
  have hr : ∀ i : Fin (freeW m (mixedCount m upper)),ranks ht S i.succ ≤ 3 := fun i => ranks_le ht S i.succ
  have hn := levelCounts_ordered (fun i => ranks ht S i.succ)
  have hd : finrank K S=profileDim (ranks ht S 0)
      (levelCount (fun i => ranks ht S i.succ) 1)
      (levelCount (fun i => ranks ht S i.succ) 2)
      (levelCount (fun i => ranks ht S i.succ) 3) := by
    rw [←ranks_sum ht S,ranks_as_blocks]
    exact IteratedCovectorCharts.sum_blockRanks _ _ hr
  have hp := profile_Phi_le_image m (mixedCount m upper)
    (ConvolutionFiniteImages.canonical_mixedCount_ge_four m hmlo (by omega) upper) ht S
  apply le_trans _ hp
  rw [hd]
  simp only [mixedCount_eq_table m (by omega),upperEndpoint_eq_table m (by omega)] at hi hn hdlo hdhi ⊢
  apply profile_inequality m hmlo hmhi upper _ _ _ _ hi hn.2.2 hn.2.1 hn.1
  · rw [←hd]
    exact hdlo
  · rw [←hd]
    exact hdhi

/-- The exact number of parameters in the covering chart plus the tuple
coefficients is bounded by the actual image rank, for every positive subspace. -/
theorem profile_parameter_image_bound [Infinite K] (m : ℕ) (hmlo : 28 ≤ m)
    (hmhi : m ≤ 40) (upper : Bool)
    (ht : 2 ≤ coreP (mixedCount m upper)+1)
    (S : Submodule K (Piece K (coreP (mixedCount m upper)+1) (freeW m (mixedCount m upper)) 1))
    (hdlo : 0 < finrank K S) :
    IteratedBlockCharts.parameterCount
      (blockDimensions (2*((coreP (mixedCount m upper)+1)-1)) (freeW m (mixedCount m upper)))
      (ranks ht S)+upperEndpoint m*finrank K S ≤
      finrank K (ConvolutionProfileImage.quadraticImage S) := by
  have hc := ConvolutionFiniteImages.canonical_mixedCount_ge_four m hmlo (by omega) upper
  have hi : ranks ht S 0 ≤ coreA (mixedCount m upper) := by
    simpa only [coreA,Nat.add_sub_cancel,blockDimensions,Fin.cons_zero] using ranks_le ht S 0
  have hr : ∀ i : Fin (freeW m (mixedCount m upper)),ranks ht S i.succ ≤ 3 := fun i => ranks_le ht S i.succ
  have hn := levelCounts_ordered (fun i => ranks ht S i.succ)
  have hd : finrank K S=profileDim (ranks ht S 0)
      (levelCount (fun i => ranks ht S i.succ) 1)
      (levelCount (fun i => ranks ht S i.succ) 2)
      (levelCount (fun i => ranks ht S i.succ) 3) := by
    rw [←ranks_sum ht S,ranks_as_blocks]
    exact IteratedCovectorCharts.sum_blockRanks _ _ hr
  have hdhi : finrank K S ≤ totalA m (mixedCount m upper) := by
    have h := Submodule.finrank_le S
    rw [ConvolutionOuterIncidence.source_finrank _ hc] at h
    exact h
  have hnumerical : (upperEndpoint m:ℤ)*(finrank K S:ℤ)+
      Cell m (mixedCount m upper) (ranks ht S 0)
        (levelCount (fun i => ranks ht S i.succ) 1)
        (levelCount (fun i => ranks ht S i.succ) 2)
        (levelCount (fun i => ranks ht S i.succ) 3) ≤
      Phi m (mixedCount m upper) (ranks ht S 0)
        (levelCount (fun i => ranks ht S i.succ) 1)
        (levelCount (fun i => ranks ht S i.succ) 2)
        (levelCount (fun i => ranks ht S i.succ) 3) := by
    rw [hd]
    have hdlo' : 0 < profileDim (ranks ht S 0)
        (levelCount (fun i => ranks ht S i.succ) 1)
        (levelCount (fun i => ranks ht S i.succ) 2)
        (levelCount (fun i => ranks ht S i.succ) 3) := by omega
    have hdhi' : profileDim (ranks ht S 0)
        (levelCount (fun i => ranks ht S i.succ) 1)
        (levelCount (fun i => ranks ht S i.succ) 2)
        (levelCount (fun i => ranks ht S i.succ) 3) ≤ totalA m (mixedCount m upper) := by omega
    simp only [mixedCount_eq_table m (by omega),upperEndpoint_eq_table m (by omega)] at hi hn hdhi' ⊢
    exact ProfileOuterFinite.profile_outer_bound m hmlo hmhi upper _ _ _ _ hi hn.2.2 hn.2.1 hn.1 hdlo' hdhi'
  have himage := profile_Phi_le_image m (mixedCount m upper) hc ht S
  have hchart := parameterCount_le_profile_Cell m (mixedCount m upper) ht S
  have h : ((IteratedBlockCharts.parameterCount
      (blockDimensions (2*((coreP (mixedCount m upper)+1)-1)) (freeW m (mixedCount m upper)))
      (ranks ht S)+upperEndpoint m*finrank K S:ℕ):ℤ) ≤
      (finrank K (ConvolutionProfileImage.quadraticImage S):ℤ) := by
    push_cast
    simp only [Nat.add_sub_cancel] at hchart
    linarith
  exact_mod_cast h

end Quartic.ConvolutionProfileChartBound
