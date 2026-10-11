/-
Copyright (c) 2026 Vlado Vojdanovski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlado Vojdanovski
-/
module

public import Quartic.UniformScalar.Counts
public import Quartic.ExtendedAugmentedGeneric

/-! The uniform endpoint estimates leave room for all four pure traces. -/

@[expose] public section

namespace Quartic.ExtendedEndpointBudget
open UniformScalar UniformEndpoint Counts

theorem augmented_budget (m : ℕ) (hm : 320 ≤ m) (upper : Bool) :
    upperEndpoint m + (mixedCount m upper + 1).choose 2 + 4 ≤ (m + 1).choose 2 := by
  have h := actual_validCounts m hm upper
  have hc := h.c_coarse
  have hq := h.q_coarse.2
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hsq : (320 : ℝ) * m ≤ (m : ℝ) ^ 2 := by nlinarith [h.1]
  have hcsq := mul_nonneg (sub_nonneg.mpr hc.2.2.1)
    (show 0 ≤ 3 * (m : ℝ) / 5 + mixedCount m upper by linarith [hc.2.1])
  have hreal : (4 : ℝ) ≤ alphaR m (upperEndpoint m) -
      (mixedCount m upper : ℝ) * (mixedCount m upper + 1) / 2 := by
    unfold alphaR
    nlinarith [h.1]
  have hint : (4 : ℤ) ≤ alpha m (upperEndpoint m) - b2 (mixedCount m upper) := by
    have hcast : (4 : ℝ) ≤ (alpha m (upperEndpoint m) : ℝ) -
        (b2 (mixedCount m upper) : ℝ) := by
      rw [alpha_cast, b2_cast]
      exact hreal
    exact_mod_cast hcast
  simp only [alpha, b2] at hint
  omega

theorem generic_augmented {K : Type*} [Field K] (ω : K)
    (hω : ω ≠ 0) (hω1 : ω ≠ -1) (m : ℕ) (hm : 320 ≤ m) (upper : Bool) :
    ExtendedAugmentedGeneric.GenericAugmented K ω m (mixedCount m upper) (upperEndpoint m) :=
  ExtendedAugmentedGeneric.genericAugmented_of_budget ω
    (c_range m hm upper).2 (augmented_budget m hm upper) hω hω1

end Quartic.ExtendedEndpointBudget
