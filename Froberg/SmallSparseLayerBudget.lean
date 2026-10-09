module

public import Froberg.SparseLayerBudget
public import Froberg.SmallDegreeCapacities

@[expose] public section

/-! Appendix E supplies the sparse fourth-layer margin, completing the
active higher-layer finite budgets in every degree at least three. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem higher_sparse_scalar_margin_all {d R : ℕ} (hd : 3≤d)
    (hR : R∈activeHigherIndices d) :
    2*((101/100 : ℝ)*higherCountGamma d R)/scalarCapacity d R+
      (scalarCapacityBinomial d R : ℝ)*criticalRatio d<1 := by
  by_cases hd8 : d≤8
  · have hR4 : R=4 := by
      simp only [activeHigherIndices,activeEvenIndices,if_pos hd8,Finset.mem_filter,
        Finset.mem_insert,Finset.mem_singleton] at hR
      omega
    subst R
    have hRlt := (activeEvenIndices_bounds hd (Finset.mem_filter.mp hR).1).2.1
    exact small_fourth_scalar_capacity (by omega) hd8
  · exact higher_sparse_scalar_margin (by omega) hR

theorem eventually_higher_sparse_layer_budget_all {d R : ℕ} (hd : 3≤d)
    (hR : R∈activeHigherIndices d) :
    ∀ᶠ w : ℕ in atTop,
      let b := sparseBlockCount ((101/100 : ℝ)*higherCountGamma d R) R (d-R) w
      let H := oddOutputDimension w R
      0<H ∧ b*(d-R+d).choose (d-R) ≤ H ∧
      ∀ q : ℕ → ℕ,
        Tendsto (fun n : ℕ => (q n : ℝ)/(n : ℝ)^d) atTop
          (𝓝 (criticalRatio d/(d.factorial : ℝ))) →
        ∀ᶠ n : ℕ in atTop,
          higherGeneratorCount d (2*w) n R ≤ b*(n+(d-R)-1).choose (d-R) ∧
          H*(d-R+d).choose (d-R)*
            (q n+H*(n+(d-R)-1).choose (d-R)+(H*2^H)*(n+(d-1)-1).choose (d-1)) ≤
            (H-b*(d-R+d).choose (d-R))*(n+(d-R)+d-1).choose d := by
  have hactive := activeEvenIndices_bounds hd (Finset.mem_filter.mp hR).1
  simpa only [higherGeneratorCount,Nat.cast_mul,Nat.cast_ofNat] using
    eventually_sparse_odd_layer_budget (by omega : 2≤d) (by omega : 0<R) hactive.2.1
      ((101/100 : ℝ)*higherCountGamma d R)
      (mul_nonneg (by norm_num) (higherCountGamma_pos d R).le)
      (higher_sparse_scalar_margin_all hd hR)

end Froberg
