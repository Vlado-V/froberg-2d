module

public import Froberg.TailCutoffCounts
public import Froberg.PureCutoff

@[expose] public section

/-! Actual pure-generator cutoff spaces for the prescribed manuscript counts. -/
noncomputable section
namespace Froberg
open Filter Module Quartic
variable {K : Type*} [Field K] [Infinite K]

theorem eventually_tail_dimension_bound {d : ℕ} (hd : 3≤d) :
    ∀ᶠ h : ℕ in atTop,tailGeneratorCount d h≤(h+d-1).choose d := by
  by_cases ho : Odd d
  · exact (odd_top_count_budget_limit hd ho).1
  · exact Eventually.of_forall (fun h => by simp [tailGeneratorCount,ho])

theorem eventually_pure_tail_cutoff {d : ℕ} (hd : 3≤d) :
    ∀ᶠ h : ℕ in atTop,∃ U : Submodule K (Forms K h d),
      finrank K U=tailGeneratorCount d h ∧
      BilinearImage.image (gradedMultiplication (K := K) (n := h) (d := d) (e := 1)).flip U=⊤ := by
  filter_upwards [eventually_tail_dimension_bound hd,eventually_tail_cutoff_count (by omega : 0<d),
    eventually_gt_atTop (0 : ℕ),eventually_ge_atTop ((1+d)*((1+d)*d))]
      with h hdim hcut hpos hlarge
  exact exists_pure_cutoff_subspace hpos (by omega)
    (by simpa only [Nat.choose_one_right] using hlarge) hcut hdim

end Froberg
