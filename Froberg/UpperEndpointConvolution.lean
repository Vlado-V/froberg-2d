import Froberg.OutputSpaceExtension
import Froberg.OutputConvolutionLimits
import Froberg.EndpointSurjectivity
import Froberg.QuadraticTargetCosts

/-! Convolution at the upper endpoint, including the imposed quadratic
output-space dimension in target row four. -/
noncomputable section
namespace Froberg
open Filter Module
open scoped Topology

theorem upperCount_normalized_limit {d : ℕ} (hd : 2 ≤ d) :
    Tendsto (fun n : ℕ => (upperCount n d : ℝ)/(n : ℝ)^d) atTop
      (𝓝 (criticalRatio d/(d.factorial : ℝ))) := by
  apply ceil_normalized_limit _ (by omega)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (kappa_bounds hn d).1.le
  · exact kappa_normalized_limit hd

variable {K : Type*} [Field K] [Infinite K]

theorem eventually_quadratic_row_four_of_endpoint {d : ℕ} (hd : 3 ≤ d)
    (hquad : ∀ n, 0 < n → GenericEndpoint K n 2 (upperCount n 2))
    (D : ℕ → ℕ)
    (hD : ∀ᶠ h : ℕ in atTop, upperCount h 2 ≤ D h ∧ D h ≤ (h+1).choose 2) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      ∃ (W : Submodule K (Forms K h 2))
        (o : Fin ⌈countAlpha d*(h : ℝ)^2*(m : ℝ)^(d-2)⌉₊ → W)
        (f : Fin ⌈countAlpha d*(h : ℝ)^2*(m : ℝ)^(d-2)⌉₊ → Forms K m (d-2)),
        finrank K W = D h ∧
        Function.Surjective (biformFamilyMap (x := 2) (y := d-2) (fun i => (o i).val) f) := by
  have hgap : (criticalRatio 2/((2 : ℕ).factorial : ℝ)) /
      (((d-2+1+(d-2)-1).choose (d-2) : ℝ)*((d-2).factorial : ℝ)) < countAlpha d := by
    have h := (quadratic_target_costs_lt_alpha hd).2.2
    rw [show d-2+1+(d-2)-1=2*d-4 by omega]
    norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,
      mul_one]
    convert h using 1
    unfold countTauFour
    ring
  have hcount := convolution_blocks_eventually_fit_density (j := 2) (a := d-2+1)
    (e := d-2) (by omega) (by omega) (by omega) (fun n => upperCount n 2)
    (criticalRatio 2/((2 : ℕ).factorial : ℝ)) (countAlpha d) (upperCount_normalized_limit (by omega)) hgap
  filter_upwards [hcount,hD,eventually_gt_atTop (0 : ℕ)] with h hc hD hh
  obtain ⟨Q,_,hQ⟩ := exists_prefix_surjective_at_upperCount hh (hquad h hh)
  filter_upwards [hc,eventually_gt_atTop (0 : ℕ)] with m hm hm0
  exact exists_biform_family_in_extended_output_space hh hm0 Q hQ hD.1
    (by simpa only [show h+2-1=h+1 by omega] using hD.2) hm

end Froberg
