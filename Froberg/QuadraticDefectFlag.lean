/-
Copyright (c) 2026 Vlado Vojdanovski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlado Vojdanovski
-/
module

public import Froberg.QuadraticChildFlag
public import Quartic.RefinedMarkedCoefficient
public import Quartic.ExceptionalChildCycle
public import Quartic.ActualDeformationColumns

/-!
# Quadratic flags with the possible square obstruction retained

These generic flags exist in every characteristic. Their coefficient-image
dimension records the kernel exactly, bounding its excess over old homology
by one instead of assuming that a distinguished square survives.
-/

@[expose] public section

noncomputable section

namespace Froberg.QuadraticDefectFlag

open Module MvPolynomial Quartic UniformEndpoint ActualDeformationColumns
open FixedBlockChildOpen

variable {K : Type*} [Field K] [Infinite K] {n : ℕ}

def Data (q : Fin (upperEndpoint n) → Forms K n 2) : Prop :=
  LinearIndependent K q ∧
  finrank K (QuadraticChildFlag.Coker q) = genericCokernel K n 2 (upperEndpoint n) ∧
  ∃ (k : Fin (upperEndpoint n)) (lost : ℕ),
    genericHomology K n 2 (upperEndpoint n - 1) ≤ lost ∧
    lost ≤ genericHomology K n 2 (upperEndpoint n - 1) + 1 ∧
    (lost = genericHomology K n 2 (upperEndpoint n - 1) ∨
      ∃ a : (quadraticMultiplication q).ker, a.val k = q k) ∧
    (finrank K (childMarkedCoefficient q k).range : ℤ) =
      Counts.delta n (upperEndpoint n) + genericCokernel K n 2 (upperEndpoint n) - lost

theorem principal_open (hn : 0 < n) :
    ∃ D : MvPolynomial (ChildIndex n (upperEndpoint n)) K,
      (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 → Data (decode a) := by
  classical
  have hpos := SharedChildFlag.upper_positive (by omega : 1 ≤ n)
  unfold Data
  generalize heq : upperEndpoint n = q at *
  cases q with
  | zero => omega
  | succ r =>
    have hr : r + 1 ≤ (n + 1).choose 2 := by
      simpa only [heq] using upper_le_quadratics n
    obtain ⟨D, hD, hgood⟩ := QuadraticChildFlag.generic_flag_open (K := K) hn hr
    refine ⟨D, hD, ?_⟩
    intro a ha
    obtain ⟨hi, hc, hh⟩ := hgood a ha
    let lost := finrank K (MarkedCoefficient.markedCoefficientMap (decode a)).ker
    refine ⟨hi, hc, Fin.last r, lost, ?_, ?_, ?_, ?_⟩
    · have h := RefinedMarkedCoefficient.old_le_ordinary_kernel (decode a) hi
      simpa only [hh, Nat.add_sub_cancel] using h
    · have h := RefinedMarkedCoefficient.ordinary_kernel_le_old_add_one (decode a) hi
      simpa only [hh, Nat.add_sub_cancel] using h
    · rcases ExceptionalChildCycle.rank_or_self_cycle (decode a) hi with hrank | hself
      · left
        have hnull := (MarkedCoefficient.markedCoefficientMap (decode a)).finrank_range_add_finrank_ker
        change finrank K (MarkedCoefficient.markedCoefficientMap (decode a)).range + lost =
          finrank K (QuarticHomology (decode a)) at hnull
        rw [hh] at hrank
        simpa only [Nat.add_sub_cancel] using (show lost = genericHomology K n 2 r by omega)
      · exact Or.inr hself
    · have heuler := quartic_euler_identity (decode a) hi
      change (finrank K (QuadraticChildFlag.Coker (decode a)) : ℤ) - _ = _ at heuler
      rw [hc] at heuler
      have hnull := (MarkedCoefficient.markedCoefficientMap (decode a)).finrank_range_add_finrank_ker
      change finrank K (MarkedCoefficient.markedCoefficientMap (decode a)).range + lost =
        finrank K (QuarticHomology (decode a)) at hnull
      have hnullZ : (finrank K (MarkedCoefficient.markedCoefficientMap (decode a)).range : ℤ) +
          lost = finrank K (QuarticHomology (decode a)) := by
        exact_mod_cast hnull
      have hrange : (childMarkedCoefficient (decode a) (Fin.last r)).range =
          (MarkedCoefficient.markedCoefficientMap (decode a)).range :=
        SharedChildFlag.markedCycles_range (decode a)
      rw [hrange]
      simp only [Counts.delta]
      linear_combination hnullZ - heuler

end Froberg.QuadraticDefectFlag
