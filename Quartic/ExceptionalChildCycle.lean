/-
Copyright (c) 2026 Vlado Vojdanovski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlado Vojdanovski
-/
module

public import Quartic.MarkedDefect

/-! A killed marked square supplies exactly the self-coefficient cycle needed
by the fourth-order correction. Thus the old rank formula or the exceptional
cycle is available for every independent child family, in every characteristic. -/

@[expose] public section

noncomputable section
namespace Quartic.ExceptionalChildCycle
open Module EndpointHomology MarkedCoefficient

variable {K : Type*} [Field K] {n r : ℕ}

theorem self_cycle_iff (q : Fin (r + 1) → Forms K n 2) :
    (∃ a : (quadraticMultiplication q).ker, a.val (Fin.last r) = q (Fin.last r)) ↔
      mulQuadratic (q (Fin.last r)) (q (Fin.last r)) ∈
        (quadraticMultiplication (prefixFamily q)).range := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨-prefixFamily a.val, ?_⟩
    have hs := quadraticMultiplication_split_last q a.val
    rw [a.property, ha] at hs
    rw [map_neg]
    exact neg_eq_iff_add_eq_zero.mpr hs.symm
  · rintro ⟨b, hb⟩
    let a : Fin (r + 1) → Forms K n 2 := Fin.snoc (-b) (q (Fin.last r))
    have ha : a (Fin.last r) = q (Fin.last r) := by simp [a]
    have hp : prefixFamily a = -b := by
      funext i
      simp [a, prefixFamily]
    refine ⟨⟨a, ?_⟩, ha⟩
    change quadraticMultiplication q a = 0
    rw [quadraticMultiplication_split_last, hp, ha, map_neg, hb, neg_add_cancel]

theorem rank_or_self_cycle (q : Fin (r + 1) → Forms K n 2)
    (hq : LinearIndependent K q) :
    (finrank K (markedCoefficientMap q).range +
      finrank K (QuarticHomology (prefixFamily q)) = finrank K (QuarticHomology q)) ∨
    ∃ a : (quadraticMultiplication q).ker, a.val (Fin.last r) = q (Fin.last r) := by
  classical
  by_cases hs : mulQuadratic (q (Fin.last r)) (q (Fin.last r)) ∈
      (quadraticMultiplication (prefixFamily q)).range
  · exact Or.inr ((self_cycle_iff q).mpr hs)
  · exact Or.inl (MarkedDefect.marked_rank_add_old q hq hs)

end Quartic.ExceptionalChildCycle
