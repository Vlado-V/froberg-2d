import Froberg.OddSourceDimensionBudget

/-! The C.4 constants can be chosen before any prepared coefficient or
relation subspace is selected. -/
noncomputable section
namespace Froberg
open Filter Module
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

theorem eventually_uniform_prepared_layered_budget {d : ℕ} (hd : 3 ≤ d)
    (h u z extra : ℕ) (hh : 0 < h) (e : ℕ → ℕ)
    (Cbottom : ℝ) (hCbottom : 0 < Cbottom)
    (he : ∀ᶠ m : ℕ in atTop,(e m : ℝ)<countBeta d*(h : ℝ)^2*(m : ℝ)^(d-2)) :
    ∃ (L : ℕ → ℕ) (ξ : ℝ),0 < ξ ∧ ∀ᶠ m in atTop,
      0 < m ∧ 0 < L m ∧ L m ≤ ⌊Cbottom*(m : ℝ)^d⌋₊ ∧
      L m ≤ min (scalarReserveCount d m) ⌊oddRowExtraDensity d*(m : ℝ)^d⌋₊ ∧
      (∀ S : Submodule K (biformParitySpace K h (m+z) d 1),
        2*(higherRelationCost d h u (m+z)+
          finrank K (biformParitySpace K h (m+z) d 1 ⧸ S)+
          Fintype.card (ProductRows.LayerLabel (PreparedParameters.allEvenIndices d)
            (PreparedParameters.allEvenCount d h (m+z) (e (m+z)+extra))))+1 ≤ L m) ∧
      (∀ j r : ℕ,j ≤ BilinearCovectorStrata.thinSlices j (ξ*(m : ℝ)^d) r+
          ⌈ξ*(m : ℝ)^d*(r : ℝ)⌉₊ ∧
          ⌈ξ*(m : ℝ)^d*(r : ℝ)⌉₊ ≤ L m*r/2) ∧
      ∀ T k : ℕ,0 < BilinearCovectorStrata.thinSlices T (Cbottom*(m : ℝ)^d) k →
        BilinearCovectorStrata.thinSlices T (Cbottom*(m : ℝ)^d) k+
          ⌊Cbottom*(m : ℝ)^d⌋₊*k ≤ T := by
  obtain ⟨L,ξ,hξ,hgood⟩ := eventually_prepared_layered_budget hd h u z extra e
    (fun m => oddCoefficientCount d h (m+z)) Cbottom hCbottom he
    (Eventually.of_forall fun _ => le_rfl)
  refine ⟨L,ξ,hξ,?_⟩
  filter_upwards [hgood,eventually_gt_atTop (0 : ℕ)] with m hm hmpos
  refine ⟨hmpos,hm.1,hm.2.1,hm.2.2.1,?_,hm.2.2.2.2.1,hm.2.2.2.2.2⟩
  intro S
  have hdim := odd_biform_quotient_finrank_le_count hh (by omega : 0 < m+z) S
  have hs := hm.2.2.2.1
  omega

end Froberg
