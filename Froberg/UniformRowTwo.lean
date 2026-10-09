module

public import Froberg.RowTwoAsymptotic

@[expose] public section

/-! Row two with both numerical thresholds chosen before the coefficient field. -/
noncomputable section
namespace Froberg
open Filter Module
open scoped Topology
universe u
attribute [local instance] tensorGroup

theorem row_two_exact_of_counts {d h m rF rE : ℕ} (hd : 3 ≤ d)
    (hh : 0 < h) (hm : 0 < m)
    (hD : rowTwoQuotientDimension h ≤ quadraticOutputDimension d h)
    (hF : convolutionBlockCount (rowTwoLinearDimension h) d (d-1)*
      (m+d+(d-1)-2).choose (d-1) ≤ rF)
    (hE : convolutionBlockCount (rowTwoQuotientDimension h) (d+1) (d-2)*
      (m+(d+1)+(d-2)-2).choose (d-2) ≤ rE)
    (K : Type u) [Field K] [Infinite K] :
    RowTwoTargetWitness K (d-1) h m rF rE := by
  obtain ⟨A,hA,hAdim,hQdim⟩ := exists_linear_space_with_quadratic_quotient (K := K) hh
    (Nat.div_le_self h 4)
  letI : Module.Finite K A := Submodule.finiteDimensional_of_le hA
  have hDlo : finrank K (EndpointQuotient K h 1 A) ≤ quadraticOutputDimension d h := by
    rw [hQdim]
    exact hD
  have hDhi : quadraticOutputDimension d h ≤ finrank K (Forms K h 2) := by
    rw [finrank_forms K h 2 hh,show h+2-1=h+1 by omega]
    exact Nat.sub_le _ _
  have hCF : convolutionBlockCount (finrank K A) (d-1+1) (d-1)*
      (m+(d-1+1)+(d-1)-2).choose (d-1) ≤ rF := by
    simpa only [hAdim,show d-1+1=d by omega,rowTwoLinearDimension] using hF
  have hCE : convolutionBlockCount (finrank K (EndpointQuotient K h 1 A)) (d-1+2) (d-1-1)*
      (m+(d-1+2)+(d-1-1)-2).choose (d-1-1) ≤ rE := by
    simpa only [hQdim,show d-1+2=d+1 by omega,show d-1-1=d-2 by omega,
      rowTwoQuotientDimension] using hE
  obtain ⟨o,f,W,O,g,hW,hs⟩ := exists_row_two_from_convolution hm (by omega : 1 ≤ d-1)
    A hA hDlo hDhi hCF hCE
  refine ⟨o,f,W,O,g,by omega,?_,hs⟩
  simpa only [show d-1+1=d by omega] using hW

theorem eventually_row_two_exact_uniform {d : ℕ} (hd : 3 ≤ d) :
    ∀ᶠ h : ℕ in atTop, ∀ F : ℕ → ℕ,
      Tendsto (fun m : ℕ => (F m : ℝ)/(m : ℝ)^(d-1)) atTop
        (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))) →
      ∀ᶠ m : ℕ in atTop, ∀ (K : Type u) [Field K] [Infinite K], ∀ rE : ℕ,
        countAlpha d*(h : ℝ)^2*(m : ℝ)^(d-2) ≤ (rE : ℝ) →
        RowTwoTargetWitness K (d-1) h m (F m) rE := by
  filter_upwards [rowTwo_outer_block_margin hd,rowTwo_quadratic_count_fits hd,
    rowTwoQuotient_fits_output hd,eventually_gt_atTop (0 : ℕ)] with h hmargin hE hD hh
  intro F hF
  have hFcount : ∀ᶠ m : ℕ in atTop,
      convolutionBlockCount (rowTwoLinearDimension h) d (d-1)*
        (m+d+(d-1)-2).choose (d-1) ≤ F m := by
    filter_upwards [eventually_lt_of_normalized_limits _ _ (d-1) _ _
      (convolutionGeneratorCount_normalized_limit _ _ (show 0 < d by omega)) hF hmargin] with m hm
    exact_mod_cast hm.le
  filter_upwards [hFcount,hE,eventually_gt_atTop (0 : ℕ)] with m hFm hEm hm
  intro K _ _ rE hrE
  exact row_two_exact_of_counts hd hh hm hD hFm (hEm.trans (Nat.ceil_le.mpr hrE)) K

end Froberg
