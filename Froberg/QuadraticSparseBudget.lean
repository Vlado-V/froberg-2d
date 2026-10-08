import Froberg.QuadraticSparseConstants
import Froberg.FullSparseBlockCount
import Froberg.IntermediateScalarBudget

/-! The finite sparse budget for the actual quadratic output D, in every
degree at least three. Exact counts may be any integer below the prescribed
strict upper bound. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem eventually_quadratic_sparse_margin {d : ℕ} (hd : 3≤d) :
    ∀ᶠ h : ℕ in atTop,
      let b := fullSparseBlockCount (countBeta d) 2 (d-2) h
      let H := quadraticOutputDimension d h
      0<H ∧ b*scalarCapacityBinomial d 2≤H ∧
        (b : ℝ)*scalarCapacityBinomial d 2+
          (H : ℝ)*scalarCapacityBinomial d 2*criticalRatio d<H := by
  have hγ : 0≤countBeta d := by
    have hG := (countTauFour_pos hd).trans_le (countTauFour_le_gamma d)
    unfold countBeta
    positivity
  have hb := fullSparseBlockCount_limit (s := d-2) (by omega : 0<2) (countBeta d) hγ
  have hH := quadraticOutputDimension_limit hd
  have hlim := (hb.mul_const (scalarCapacityBinomial d 2 : ℝ)).add
    ((hH.mul_const (scalarCapacityBinomial d 2 : ℝ)).mul_const (criticalRatio d))
  have hl : Tendsto (fun h : ℕ =>
      ((fullSparseBlockCount (countBeta d) 2 (d-2) h : ℝ)*scalarCapacityBinomial d 2+
        (quadraticOutputDimension d h : ℝ)*scalarCapacityBinomial d 2*criticalRatio d)/(h : ℝ)^2)
      atTop (𝓝 (countBeta d*((d-2).factorial : ℝ)*(scalarCapacityBinomial d 2 : ℝ)+
        quadraticOutputDensity d*(scalarCapacityBinomial d 2 : ℝ)*criticalRatio d)) := by
    apply hlim.congr'
    exact Eventually.of_forall fun h => by dsimp only; ring
  filter_upwards [eventually_lt_of_normalized_limits _ _ 2 _ _ hl hH
    (quadratic_sparse_density_gap hd)] with h hh
  have hp : 0≤(quadraticOutputDimension d h : ℝ)*scalarCapacityBinomial d 2*criticalRatio d :=
    mul_nonneg (by positivity) (criticalRatio_bounds (by omega : 2≤d)).1.le
  have hle : (fullSparseBlockCount (countBeta d) 2 (d-2) h : ℝ)*scalarCapacityBinomial d 2 <
      quadraticOutputDimension d h := by linarith
  have hleN : fullSparseBlockCount (countBeta d) 2 (d-2) h*scalarCapacityBinomial d 2 <
      quadraticOutputDimension d h := by exact_mod_cast hle
  exact ⟨lt_of_le_of_lt (Nat.zero_le _) hleN,hleN.le,hh⟩

theorem eventually_quadratic_sparse_layer_budget {d : ℕ} (hd : 3≤d) :
    ∀ᶠ h : ℕ in atTop,
      let b := fullSparseBlockCount (countBeta d) 2 (d-2) h
      let H := quadraticOutputDimension d h
      0<H ∧ b*(d-2+d).choose (d-2)≤H ∧
      ∀ q : ℕ → ℕ,
        Tendsto (fun n : ℕ => (q n : ℝ)/(n : ℝ)^d) atTop
          (𝓝 (criticalRatio d/(d.factorial : ℝ))) →
        ∀ᶠ n : ℕ in atTop, ∀ r : ℕ,
          (r : ℝ)<countBeta d*(h : ℝ)^2*(n : ℝ)^(d-2) →
          r≤b*(n+(d-2)-1).choose (d-2) ∧
          H*(d-2+d).choose (d-2)*
            (q n+H*(n+(d-2)-1).choose (d-2)+(H*2^H)*(n+(d-1)-1).choose (d-1)) ≤
            (H-b*(d-2+d).choose (d-2))*(n+(d-2)+d-1).choose d := by
  have heq : d-2+d=2*d-2 := by omega
  have hγ : 0≤countBeta d := by
    have hG := (countTauFour_pos hd).trans_le (countTauFour_le_gamma d)
    unfold countBeta
    positivity
  filter_upwards [eventually_quadratic_sparse_margin hd] with h hh
  dsimp only at hh ⊢
  have hc : fullSparseBlockCount (countBeta d) 2 (d-2) h*(d-2+d).choose (d-2) ≤
      quadraticOutputDimension d h := by
    simpa only [scalarCapacityBinomial,heq] using hh.2.1
  refine ⟨hh.1,hc,fun q hq => ?_⟩
  have hg : ((fullSparseBlockCount (countBeta d) 2 (d-2) h*(d-2+d).choose (d-2) : ℕ) : ℝ)+
      (quadraticOutputDimension d h : ℝ)*((d-2+d).choose (d-2) : ℝ)*criticalRatio d <
        quadraticOutputDimension d h := by
    simpa only [Nat.cast_mul,heq,scalarCapacityBinomial] using hh.2.2
  have hb := eventually_intermediate_scalar_budget (by omega : d-2<d) hc q hq hg
  filter_upwards [fullSparseBlockCount_eventually_covers (countBeta d) hγ 2 h
    (by omega : 0<d-2),hb] with n hn hbn
  intro r hr
  refine ⟨?_,hbn⟩
  apply le_trans _ hn
  have hrc := hr.le.trans (Nat.le_ceil (countBeta d*(h : ℝ)^2*(n : ℝ)^(d-2)))
  exact_mod_cast hrc

end Froberg
