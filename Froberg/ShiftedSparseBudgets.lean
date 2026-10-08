import Froberg.ShiftedCountLimits
import Froberg.SmallSparseLayerBudget

/-! Active higher sparse layers use exactly the same output block count
when the prescribed generator count includes fixed private variables. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem eventually_higher_sparse_layer_budget_shift {d R : ℕ} (hd : 3≤d)
    (hR : R∈activeHigherIndices d) :
    ∀ᶠ w : ℕ in atTop,
      let b := sparseBlockCount ((101/100 : ℝ)*higherCountGamma d R) R (d-R) w
      let H := oddOutputDimension w R
      0<H ∧ b*(d-R+d).choose (d-R)≤H ∧
      ∀ z extra : ℕ,∀ q : ℕ → ℕ,
        Tendsto (fun n : ℕ => (q n : ℝ)/(n : ℝ)^d) atTop
          (𝓝 (criticalRatio d/(d.factorial : ℝ))) →
        ∀ᶠ n : ℕ in atTop,
          higherGeneratorCount d (2*w) (n+z) R+extra≤b*(n+(d-R)-1).choose (d-R) ∧
          H*(d-R+d).choose (d-R)*
            (q n+H*(n+(d-R)-1).choose (d-R)+(H*2^H)*(n+(d-1)-1).choose (d-1))≤
            (H-b*(d-R+d).choose (d-R))*(n+(d-R)+d-1).choose d := by
  have hactive := activeEvenIndices_bounds hd (Finset.mem_filter.mp hR).1
  filter_upwards [eventually_higher_sparse_layer_budget_all hd hR] with w hw
  refine ⟨hw.1,hw.2.1,fun z extra q hq => ?_⟩
  have hc := sparseBlockCount_eventually_covers_shift_add
    ((101/100 : ℝ)*higherCountGamma d R)
    (mul_nonneg (by norm_num) (higherCountGamma_pos d R).le) R w z extra
    (by omega : 0<d-R)
  filter_upwards [hc,hw.2.2 q hq] with n hn hbudget
  exact ⟨by simpa only [higherGeneratorCount,Nat.cast_mul,Nat.cast_ofNat] using hn,hbudget.2⟩

end Froberg
