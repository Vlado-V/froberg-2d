import Froberg.SparseLayerConstants
import Froberg.SparseBlockCount
import Froberg.IntermediateScalarBudget

/-! Exact finite sparse-layer budgets from the actual rounded counts,
including the complete exceptional-shadow term. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

/-- The selected scalar blocks leave a strict incidence margin inside the
actual odd-half output space. -/
theorem eventually_sparse_odd_margin {d R : ℕ} (hd : 2≤d) (hR : 0<R) (hRd : R≤d)
    (γ : ℝ) (hγ : 0≤γ)
    (hgap : 2*γ/scalarCapacity d R+
      (scalarCapacityBinomial d R : ℝ)*criticalRatio d<1) :
    ∀ᶠ w : ℕ in atTop,
      0<oddOutputDimension w R ∧
      sparseBlockCount γ R (d-R) w*scalarCapacityBinomial d R ≤ oddOutputDimension w R ∧
      (sparseBlockCount γ R (d-R) w : ℝ)*scalarCapacityBinomial d R+
        (oddOutputDimension w R : ℝ)*scalarCapacityBinomial d R*criticalRatio d <
          oddOutputDimension w R := by
  have hb := sparseBlockCount_limit (s := d-R) hR γ hγ
  have hH := oddOutputDimension_normalized_limit hR
  have hlim := (hb.mul_const (scalarCapacityBinomial d R : ℝ)).add
    ((hH.mul_const (scalarCapacityBinomial d R : ℝ)).mul_const (criticalRatio d))
  have hl : Tendsto (fun w : ℕ =>
      ((sparseBlockCount γ R (d-R) w : ℝ)*scalarCapacityBinomial d R+
        (oddOutputDimension w R : ℝ)*scalarCapacityBinomial d R*criticalRatio d)/(w : ℝ)^R)
      atTop (𝓝 (γ*2^R*((d-R).factorial : ℝ)*(scalarCapacityBinomial d R : ℝ)+
        (2^(R-1)/(R.factorial : ℝ))*(scalarCapacityBinomial d R : ℝ)*criticalRatio d)) := by
    apply hlim.congr'
    exact Eventually.of_forall fun w => by dsimp only; ring
  filter_upwards [eventually_lt_of_normalized_limits _ _ R _ _ hl hH
    (sparse_odd_density_gap hR hRd γ hgap)] with w hw
  have hp : 0≤(oddOutputDimension w R : ℝ)*scalarCapacityBinomial d R*criticalRatio d :=
    mul_nonneg (by positivity) (criticalRatio_bounds hd).1.le
  have hle : (sparseBlockCount γ R (d-R) w : ℝ)*scalarCapacityBinomial d R <
      oddOutputDimension w R := by linarith
  have hleN : sparseBlockCount γ R (d-R) w*scalarCapacityBinomial d R <
      oddOutputDimension w R := by exact_mod_cast hle
  exact ⟨lt_of_le_of_lt (Nat.zero_le _) hleN,hleN.le,hw⟩

/-- A strict B.8 scalar-capacity inequality discharges all finite numerical
inputs to the sparse new-layer construction. -/
theorem eventually_sparse_odd_layer_budget {d R : ℕ} (hd : 2≤d) (hR : 0<R) (hRd : R<d)
    (γ : ℝ) (hγ : 0≤γ)
    (hgap : 2*γ/scalarCapacity d R+
      (scalarCapacityBinomial d R : ℝ)*criticalRatio d<1) :
    ∀ᶠ w : ℕ in atTop,
      0<oddOutputDimension w R ∧
      sparseBlockCount γ R (d-R) w*(d-R+d).choose (d-R) ≤ oddOutputDimension w R ∧
      ∀ q : ℕ → ℕ,
        Tendsto (fun n : ℕ => (q n : ℝ)/(n : ℝ)^d) atTop
          (𝓝 (criticalRatio d/(d.factorial : ℝ))) →
        ∀ᶠ n : ℕ in atTop,
          ⌈γ*(2*(w : ℝ))^R*(n : ℝ)^(d-R)⌉₊ ≤
            sparseBlockCount γ R (d-R) w*(n+(d-R)-1).choose (d-R) ∧
          oddOutputDimension w R*(d-R+d).choose (d-R)*
            (q n+oddOutputDimension w R*(n+(d-R)-1).choose (d-R)+
              (oddOutputDimension w R*2^(oddOutputDimension w R))*(n+(d-1)-1).choose (d-1)) ≤
            (oddOutputDimension w R-sparseBlockCount γ R (d-R) w*(d-R+d).choose (d-R))*
              (n+(d-R)+d-1).choose d := by
  have heq : d-R+d=2*d-R := by omega
  filter_upwards [eventually_sparse_odd_margin hd hR hRd.le γ hγ hgap] with w hw
  have hc : sparseBlockCount γ R (d-R) w*(d-R+d).choose (d-R) ≤ oddOutputDimension w R := by
    simpa only [scalarCapacityBinomial,heq] using hw.2.1
  refine ⟨hw.1,hc,fun q hq => ?_⟩
  have hg : ((sparseBlockCount γ R (d-R) w*(d-R+d).choose (d-R) : ℕ) : ℝ)+
      (oddOutputDimension w R : ℝ)*((d-R+d).choose (d-R) : ℝ)*criticalRatio d < oddOutputDimension w R := by
    simpa only [Nat.cast_mul,heq,scalarCapacityBinomial] using hw.2.2
  have hb := eventually_intermediate_scalar_budget (by omega : d-R<d) hc q hq hg
  filter_upwards [sparseBlockCount_eventually_covers γ hγ R w (by omega : 0<d-R),hb]
    with n hn hbn
  exact ⟨hn,hbn⟩

/-- The higher Section 5 generator counts satisfy the complete sparse
new-layer budget, with an explicitly chosen number of scalar blocks. -/
theorem eventually_higher_sparse_layer_budget {d R : ℕ} (hd : 9≤d)
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
  have hactive := activeEvenIndices_bounds (by omega : 3≤d) (Finset.mem_filter.mp hR).1
  simpa only [higherGeneratorCount,Nat.cast_mul,Nat.cast_ofNat] using
    eventually_sparse_odd_layer_budget (by omega : 2≤d) (by omega : 0<R) hactive.2.1
      ((101/100 : ℝ)*higherCountGamma d R)
      (mul_nonneg (by norm_num) (higherCountGamma_pos d R).le)
      (higher_sparse_scalar_margin hd hR)

end Froberg
