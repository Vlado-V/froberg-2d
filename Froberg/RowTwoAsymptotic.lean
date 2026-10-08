import Froberg.RowTwoFinite
import Froberg.RowTwoLinearSpace

/-! The exact row-two target witness at the Section 5 generator densities.
The construction uses direct convolution and no preceding-degree endpoint. -/
noncomputable section
namespace Froberg
open Filter Module
open scoped Topology
variable (K : Type*) [Field K]
attribute [local instance] tensorGroup

/-- Here `s=d-1`. Both displayed maps are literal polynomial multiplication,
and the second is included through the prescribed quadratic output space. -/
def RowTwoTargetWitness (s h m rF rE : ℕ) : Prop :=
  ∃ (o : Fin rF → Forms K h 1) (f : Fin rF → Forms K m s)
    (W : Submodule K (Forms K h 2)) (O : Fin rE → W) (g : Fin rE → Forms K m (s-1))
    (he : (s-1)+(s+1)=s+s),
    finrank K W = quadraticOutputDimension (s+1) h ∧
    Function.Surjective ((biformFamilyMap (x := 1) (y := s) o f).coprod
      (vectorFormFamilyToDegree he (fun i => (O i).val) g))

variable {K} [Infinite K]

theorem eventually_row_two_exact {d : ℕ} (hd : 3 ≤ d) :
    ∀ᶠ h : ℕ in atTop, ∀ F : ℕ → ℕ,
      Tendsto (fun m : ℕ => (F m : ℝ)/(m : ℝ)^(d-1)) atTop
        (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))) →
      ∀ᶠ m : ℕ in atTop, ∀ rE : ℕ,
        countAlpha d*(h : ℝ)^2*(m : ℝ)^(d-2) ≤ (rE : ℝ) →
        RowTwoTargetWitness K (d-1) h m (F m) rE := by
  filter_upwards [rowTwo_outer_block_margin hd,rowTwo_quadratic_count_fits hd,
    rowTwoQuotient_fits_output hd,eventually_gt_atTop (0 : ℕ)] with h hmargin hE hD hh
  intro F hF
  obtain ⟨A,hA,hAdim,hQdim⟩ := exists_linear_space_with_quadratic_quotient (K := K) hh
    (Nat.div_le_self h 4)
  letI : Module.Finite K A := Submodule.finiteDimensional_of_le hA
  have hFcount : ∀ᶠ m : ℕ in atTop,
      convolutionBlockCount (rowTwoLinearDimension h) d (d-1)*
        (m+d+(d-1)-2).choose (d-1) ≤ F m := by
    filter_upwards [eventually_lt_of_normalized_limits _ _ (d-1) _ _
      (convolutionGeneratorCount_normalized_limit _ _ (show 0 < d by omega)) hF hmargin] with m hm
    exact_mod_cast hm.le
  filter_upwards [hFcount,hE,eventually_gt_atTop (0 : ℕ)] with m hFm hEm hm
  intro rE hrE
  have hDlo : finrank K (EndpointQuotient K h 1 A) ≤ quadraticOutputDimension d h := by
    rw [hQdim]
    exact hD
  have hDhi : quadraticOutputDimension d h ≤ finrank K (Forms K h 2) := by
    rw [finrank_forms K h 2 hh,show h+2-1=h+1 by omega]
    exact Nat.sub_le _ _
  have hCF : convolutionBlockCount (finrank K A) (d-1+1) (d-1)*
      (m+(d-1+1)+(d-1)-2).choose (d-1) ≤ F m := by
    simpa only [hAdim,show d-1+1=d by omega,rowTwoLinearDimension] using hFm
  have hCE : convolutionBlockCount (finrank K (EndpointQuotient K h 1 A)) (d-1+2) (d-1-1)*
      (m+(d-1+2)+(d-1-1)-2).choose (d-1-1) ≤ rE := by
    have he := hEm.trans (Nat.ceil_le.mpr hrE)
    simpa only [hQdim,show d-1+2=d+1 by omega,show d-1-1=d-2 by omega,
      rowTwoQuotientDimension] using he
  obtain ⟨o,f,W,O,g,hW,hs⟩ := exists_row_two_from_convolution hm (by omega : 1 ≤ d-1)
    A hA hDlo hDhi hCF hCE
  refine ⟨o,f,W,O,g,by omega,?_,hs⟩
  simpa only [show d-1+1=d by omega] using hW

end Froberg
