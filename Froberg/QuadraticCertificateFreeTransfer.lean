/-
Copyright (c) 2026 Vlado Vojdanovski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlado Vojdanovski
-/
module

public import Froberg.QuadraticDefectFlag
public import Quartic.ExtendedEndpointBudget
public import Quartic.ExtendedExpansionMotionBridge
public import Quartic.ExtendedSlicedResponseRank
public import Quartic.ExtendedDeformationRank
public import Quartic.StrongExpansionCommonOpenOmega
public import Quartic.StrongExpansionMotionBridge
public import Quartic.ActualSlicedResponseRankOmega
public import Quartic.ActualDeformationRankOmega
public import Quartic.DefectRankCount

/-!
# Certificate-free quadratic transfer in every characteristic

The ordinary trace handles a surviving marked square. If the square is killed,
the fourth-order correction supplies the extra response direction. Both cases
give the exact two-defect bound with no finite endpoint witnesses.
-/

@[expose] public section

noncomputable section

namespace Froberg.QuadraticCertificateFreeTransfer

open Module MvPolynomial Quartic UniformEndpoint
open ActualDeformationColumnsOmega ActualDeformationResponseOmega RowMultiplicationCoordinates

variable {K : Type*} [Field K] [Infinite K] [IsAlgClosed K]

set_option maxHeartbeats 2000000 in
theorem parent_defect_witness (m : ℕ) (hm : 320 ≤ m) (upper : Bool) :
    ∃ f : Fin (4 + (mixedCount m upper + upperEndpoint m)) → Forms K (3 + m) 2,
      LinearIndependent K f ∧
      (finrank K (QuarticHomology f) : ℤ) ≤
        max (genericHomology K m 2 (upperEndpoint m - 1) : ℤ)
          ((genericCokernel K m 2 (upperEndpoint m) : ℤ) -
            Counts.chi (3 + m) (4 + (mixedCount m upper + upperEndpoint m))) ∧
      (finrank K (QuadraticChildFlag.Coker f) : ℤ) ≤
        max (genericCokernel K m 2 (upperEndpoint m) : ℤ)
          ((genericHomology K m 2 (upperEndpoint m - 1) : ℤ) +
            Counts.chi (3 + m) (4 + (mixedCount m upper + upperEndpoint m))) := by
  classical
  obtain ⟨ω, hω, hω1⟩ := ThreeBlockOmega.exists_parameter (K := K)
  obtain ⟨G, hG, hExtended⟩ := ExtendedEndpointBudget.generic_augmented
    (K := K) ω hω hω1 m hm upper
  obtain ⟨g, r₀, E, hE, hg, hexp, D, hD, hgood⟩ :=
    StrongExpansionCommonOpenOmega.exists_fixed_open_with (K := K) (L := K)
      ω m hm upper hω hω1 G hG
  obtain ⟨A, hA, hflag⟩ := QuadraticDefectFlag.principal_open (K := K) (by omega : 0 < m)
  obtain ⟨a, haD, haA⟩ := principal_opens_intersect hD hA
  have hDA : ∃ a, eval a (D * A) ≠ 0 :=
    ⟨a, by simpa only [map_mul] using mul_ne_zero haD haA⟩
  obtain ⟨h, hhDA, hslices⟩ := StrongActualSlices.exists_all_corrections_in_open
    (I := Fin ((m + 1).choose 2 + 2)) m hm upper
    (fun w => StrongActualSlices.markedCorrectionCount m upper w.val)
    g hg E hE hexp (D * A) hDA
  have hpair : eval (FixedBlockChildOpen.encodeChild h) D ≠ 0 ∧
      eval (FixedBlockChildOpen.encodeChild h) A ≠ 0 := by
    simpa only [map_mul, mul_ne_zero_iff] using hhDA
  obtain ⟨hblock, hf13, _, hGpoint⟩ := hgood _ hpair.1
  have hdata := hflag _ hpair.2
  simp only [FixedBlockChildOpen.decode_encode] at hblock hf13 hGpoint hdata
  obtain ⟨hh, hc, k, lost, hlostLower, hlostUpper, hcase, hlostRank⟩ := hdata
  let U := (childMarkedCoefficient h k).range
  have hdim : (finrank K U : ℤ) = Counts.delta m (upperEndpoint m) +
      genericCokernel K m 2 (upperEndpoint m) - lost := hlostRank
  have hUle : finrank K U ≤ (m + 1).choose 2 := by
    calc
      finrank K U ≤ finrank K (Forms K m 2 ⧸ Submodule.span K (Set.range h)) :=
        Submodule.finrank_le U
      _ ≤ finrank K (Forms K m 2) := Submodule.finrank_quotient_le _
      _ = (m + 1).choose 2 := finrank_quadrics K m
  have hs := hblock.1.2.2.1
  have hr₀ := hblock.1.2.2.2
  rw [AugmentedGeneric.coefficientMixed_encode, AugmentedGeneric.coefficientChild_encode] at hs hr₀
  rw [AugmentedGeneric.coefficientMotions_encode] at hr₀
  have htrace : Function.Injective (SplitMiddle31.mixedMultiplication (ActualTraceMotion.rowMixed g)) := by
    rw [ActualTraceMotion.rowMixed_eq_transpose]
    simpa only [AugmentedGeneric.coefficientMixed_encode,
      SimultaneousBlockConditionsOmega.transposeMixed,
      SimultaneousBlockConditions.transposeMixed] using hblock.2.2.1
  have hrExtended : Function.Injective (ExtendedAugmentedGeneric.quotientAugmented ω
      (AugmentedGeneric.productMap g) h r₀) := by
    have hi := (hExtended _ hGpoint).2.2
    rw [AugmentedGeneric.coefficientMixed_encode, AugmentedGeneric.coefficientChild_encode,
      AugmentedGeneric.coefficientMotions_encode] at hi
    exact hi
  have hparams : ∃ r : Fin 4 → Forms K m 2, ∃ s : Fin (mixedCount m upper) → Forms K m 2,
      ∃ ε : K, ∃ N : ℕ,
      LinearIndependent K (deformedFamily g h s r (Pi.single k (markedDirection ω)) ε) ∧
      min (Counts.hTotal m (upperEndpoint m) (mixedCount m upper) +
        genericCokernel K m 2 (upperEndpoint m) -
        genericHomology K m 2 (upperEndpoint m - 1))
        (Counts.j m (upperEndpoint m) (mixedCount m upper)) ≤ (N : ℤ) ∧
      finrank K (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range + N ≤
        finrank K (quadraticMultiplication
          (deformedFamily g h s r (Pi.single k (markedDirection ω)) ε)).range := by
    rcases hcase with hexact | ⟨a, ha⟩
    · let w : Fin ((m + 1).choose 2 + 2) := ⟨finrank K U, by omega⟩
      obtain ⟨Z, hclosed⟩ := StrongExpansionMotionBridge.closed_slices hm g h U (hslices w)
      obtain ⟨r, s, _, hresponse⟩ := ActualSlicedResponseRankOmega.exists_response_rank_formula
        ω g h U Z hclosed hg hh hs htrace hf13.2.1 hf13.2.2 r₀ hr₀
      obtain ⟨ε, _, hlin, hgain⟩ := ActualDeformationRankOmega.exists_independent_rank_gain
        ω g h s r k U (canonical_marked_representatives h k) hg hh
      refine ⟨r, s, ε, _, hlin, ?_, hgain⟩
      rw [hresponse, hdim, hexact]
      apply le_of_eq
      congr 1
      unfold Counts.hTotal Counts.k31
      push_cast
      ring
    · let w : Fin ((m + 1).choose 2 + 2) := ⟨finrank K U + 1, by omega⟩
      obtain ⟨Z, hclosed⟩ := ExtendedExpansionMotionBridge.closed_slices hm g h U (hslices w)
      obtain ⟨r, s, _, hresponse⟩ := ExtendedSlicedResponseRank.exists_response_rank_formula
        ω g h U Z hclosed hg hh hs htrace hf13.2.1 hf13.2.2 r₀ hrExtended
      obtain ⟨ε, _, hlin, hgain⟩ := ExtendedDeformationRank.exists_independent_rank_gain
        ω g h s r k U (canonical_marked_representatives h k) hs a ha hg hh
      refine ⟨r, s, ε, _, hlin, ?_, hgain⟩
      rw [hresponse, hdim]
      apply min_le_min_right
      unfold Counts.hTotal Counts.k31
      push_cast
      omega
  obtain ⟨r, s, ε, N, hlin, hresponse, hgain⟩ := hparams
  let f := deformedFamily g h s r (Pi.single k (markedDirection ω)) ε
  have hsplit := DefectRankCount.split_rank_lower g h hs hh hf13.2.1 hf13.2.2
  rw [hc] at hsplit
  obtain ⟨hH, hC⟩ := DefectRankCount.defect_bounds_of_gain f hlin _ N
    (genericCokernel K m 2 (upperEndpoint m))
    (genericHomology K m 2 (upperEndpoint m - 1)) hsplit hresponse hgain
  exact ⟨f, hlin, hH, hC⟩

end Froberg.QuadraticCertificateFreeTransfer
