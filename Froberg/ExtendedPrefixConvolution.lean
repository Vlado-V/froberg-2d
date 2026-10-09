module

public import Froberg.OutputSpaceExtension
public import Froberg.MiddleRowConvolution
public import Froberg.QuadraticTargetCosts

@[expose] public section

/-! Middle-row witnesses with the required output-space dimension. -/
noncomputable section
namespace Froberg
open Filter Module
open scoped Topology
variable {K : Type*} [Field K] [Infinite K]

theorem eventually_extended_middle_biform {j x e y : ℕ}
    (hj : 0 < j) (hxj : x < j) (he : 0 < e)
    (α δ : ℝ) (hα : convolutionOutputThreshold j x e y < α)
    (hδ : (x.factorial : ℝ)/((j+x).factorial : ℝ) < δ)
    (D : ℕ → ℕ)
    (hDlim : Tendsto (fun n : ℕ => (D n : ℝ)/(n : ℝ)^j) atTop (𝓝 δ))
    (hDupper : ∀ᶠ n : ℕ in atTop, D n ≤ (n+j-1).choose j) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      ∃ (W : Submodule K (Forms K h j))
        (o : Fin ⌈α*(h : ℝ)^j*(m : ℝ)^e⌉₊ → W)
        (f : Fin ⌈α*(h : ℝ)^j*(m : ℝ)^e⌉₊ → Forms K m e),
        finrank K W = D h ∧
        Function.Surjective (biformFamilyMap (x := x) (y := y) (fun i => (o i).val) f) := by
  have hQ : 0 < (y+1+e-1).choose e := Nat.choose_pos (by omega)
  have hden : (0 : ℝ) < ((y+1+e-1).choose e : ℝ)*(e.factorial : ℝ) := by positivity
  have hbetween : (x.factorial : ℝ)/((j+x).factorial : ℝ) <
      min (α*(((y+1+e-1).choose e : ℝ)*(e.factorial : ℝ))) δ :=
    lt_min ((div_lt_iff₀ hden).mp hα) hδ
  obtain ⟨τ,hτlo,hτhi⟩ := exists_between hbetween
  have hτ : 0 < τ := lt_trans (by positivity) hτlo
  have hτδ : τ < δ := hτhi.trans_le (min_le_right _ _)
  have hgap : τ/(((y+1+e-1).choose e : ℝ)*(e.factorial : ℝ)) < α :=
    (div_lt_iff₀ hden).mpr (hτhi.trans_le (min_le_left _ _))
  have hceil := ceil_normalized_limit (fun n : ℕ => τ*(n : ℝ)^j) hj τ
    (Eventually.of_forall fun n => mul_nonneg hτ.le (pow_nonneg (Nat.cast_nonneg n) _))
    (scaled_power_normalized_limit τ j)
  have hroom := eventually_lt_of_normalized_limits _ _ j τ δ hceil hDlim hτδ
  filter_upwards [rounded_prefix_output_count hj τ hτlo,
    rounded_convolution_blocks_margin hj (show 0 < y+1 by omega) τ α hτ hgap,
    hroom,hDupper,eventually_ge_atTop ((x+j).choose x*((x+j).choose x*j.choose x)),
    eventually_gt_atTop (0 : ℕ)] with h houtput hblocks hroom hDupper hlarge hh
  obtain ⟨Q,hQ⟩ := exists_prefix_surjective_of_large_variables (K := K) hh hxj hlarge houtput
  have hqD : ⌈τ*(h : ℝ)^j⌉₊ ≤ D h := by exact_mod_cast hroom.le
  filter_upwards [convolutionGeneratorCount_eventually_fits he (show 0 < y+1 by omega)
    (α*(h : ℝ)^j) hblocks,eventually_gt_atTop (0 : ℕ)] with m hgen hm
  exact exists_biform_family_in_extended_output_space hh hm Q hQ hqD hDupper hgen

theorem convolutionOutputThreshold_row_three {d : ℕ} (hd : 3 ≤ d) :
    convolutionOutputThreshold 2 1 (d-2) (d-1) = quadraticRowThreeCost d := by
  unfold convolutionOutputThreshold quadraticRowThreeCost
  rw [show d-1+1+(d-2)-1=2*d-3 by omega]
  norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,
    mul_one]
  ring

theorem eventually_quadratic_row_three {d : ℕ} (hd : 3 ≤ d)
    (D : ℕ → ℕ) (δ : ℝ) (hδ : (1/6 : ℝ) < δ)
    (hDlim : Tendsto (fun n : ℕ => (D n : ℝ)/(n : ℝ)^2) atTop (𝓝 δ))
    (hDupper : ∀ᶠ n : ℕ in atTop, D n ≤ (n+1).choose 2) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      ∃ (W : Submodule K (Forms K h 2))
        (o : Fin ⌈countAlpha d*(h : ℝ)^2*(m : ℝ)^(d-2)⌉₊ → W)
        (f : Fin ⌈countAlpha d*(h : ℝ)^2*(m : ℝ)^(d-2)⌉₊ → Forms K m (d-2)),
        finrank K W = D h ∧
        Function.Surjective (biformFamilyMap (x := 1) (y := d-1) (fun i => (o i).val) f) := by
  apply eventually_extended_middle_biform (by omega) (by omega) (by omega)
    (countAlpha d) δ ?_ ?_ D hDlim ?_
  · rw [convolutionOutputThreshold_row_three hd]
    exact (quadratic_target_costs_lt_alpha hd).2.1
  · norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,
      mul_one]
    exact hδ
  · simpa only [show ∀ n : ℕ, n+2-1=n+1 by omega] using hDupper

end Froberg
