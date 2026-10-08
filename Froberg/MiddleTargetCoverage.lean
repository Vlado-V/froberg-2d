import Froberg.MiddleRowConvolution
import Froberg.TargetCoverage

/-! Every required middle target row is filled at its actual prescribed
higher-layer density. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology
variable {K : Type*} [Field K] [Infinite K]

theorem eventually_higher_target_row {d b : ℕ} (hd : 3 ≤ d) (hb : 5 ≤ b)
    (hbd : b ≤ d) (hcut : b < d ∨ Odd d) :
    ∃ j ∈ activeHigherIndices d, j < b ∧ b < 2*j ∧
      ∀ᶠ h : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
        ∃ (o : Fin ⌈(101/100 : ℝ)*higherCountGamma d j*(h : ℝ)^j*(m : ℝ)^(d-j)⌉₊ → Forms K h j)
          (f : Fin ⌈(101/100 : ℝ)*higherCountGamma d j*(h : ℝ)^j*(m : ℝ)^(d-j)⌉₊ → Forms K m (d-j)),
          Function.Surjective (biformFamilyMap (x := b-j) (y := d+j-b) o f) := by
  obtain ⟨j,hj,hjb,hbj,hcost⟩ := higher_layers_cover_targets hd hb hbd hcut
  refine ⟨j,hj,hjb,hbj,?_⟩
  exact eventually_target_row_from_prefix (by omega) (by omega) hjb.le hbj (by omega) _ hcost

end Froberg
