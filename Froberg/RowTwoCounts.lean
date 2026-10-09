module

public import Froberg.QuadraticOutputDimension
public import Froberg.PrivateMultiplierLimits

@[expose] public section

/-! Exact dimensions and strict convolution budgets for target row two. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

def rowTwoLinearDimension (h : ℕ) : ℕ := h/4
def rowTwoQuotientDimension (h : ℕ) : ℕ := (h-h/4+1).choose 2

theorem rowTwoLinearDimension_limit :
    Tendsto (fun h : ℕ => (rowTwoLinearDimension h : ℝ)/(h : ℝ)) atTop (𝓝 (1/4 : ℝ)) := by
  simpa only [rowTwoLinearDimension,pow_one,Nat.cast_ofNat] using
    natural_division_normalized_limit (fun h : ℕ => h) (by omega : 0 < 1) (by omega : 0 < 4) 1
      (by simpa only [one_mul,pow_one] using scaled_power_normalized_limit (1 : ℝ) 1)

theorem rowTwoQuotientDimension_limit :
    Tendsto (fun h : ℕ => (rowTwoQuotientDimension h : ℝ)/(h : ℝ)^2) atTop (𝓝 (9/32 : ℝ)) := by
  have hrat : Tendsto (fun h : ℕ => ((h-h/4 : ℕ) : ℝ)/(h : ℝ)) atTop (𝓝 (3/4 : ℝ)) := by
    have hid : Tendsto (fun h : ℕ => (h : ℝ)/(h : ℝ)) atTop (𝓝 (1 : ℝ)) := by
      simpa only [one_mul,pow_one] using scaled_power_normalized_limit (1 : ℝ) 1
    have h := hid.sub rowTwoLinearDimension_limit
    norm_num only [show (1 : ℝ)-1/4=3/4 by norm_num] at h
    apply h.congr'
    exact Eventually.of_forall fun h => by simp only [rowTwoLinearDimension,Nat.cast_sub (Nat.div_le_self h 4),sub_div]
  have ha := private_nat_tendsto_atTop_of_positive_ratio (fun h : ℕ => h-h/4) (by norm_num : (0 : ℝ)<3/4) hrat
  have h := scaled_index_monomial_limit (fun h : ℕ => h-h/4) (3/4) 2 ha hrat
  norm_num [rowTwoQuotientDimension,show ∀ h : ℕ, h-h/4+2-1=h-h/4+1 by omega,Nat.factorial] at h ⊢
  exact h

theorem rowTwoQuotient_fits_output {d : ℕ} (hd : 3 ≤ d) :
    ∀ᶠ h : ℕ in atTop, rowTwoQuotientDimension h ≤ quadraticOutputDimension d h := by
  filter_upwards [eventually_lt_of_normalized_limits _ _ 2 _ _ rowTwoQuotientDimension_limit
    (quadraticOutputDimension_limit hd) (quadraticOutputDensity_lower hd)] with h hh
  exact_mod_cast hh.le

/-- Direct convolution in one quarter of the linear directions fits the
outer family with a strict margin. -/
theorem rowTwo_outer_density_gap {d : ℕ} (hd : 3 ≤ d) :
    (1/4 : ℝ)/((2*d-2).choose (d-1) : ℝ) < criticalRatio d := by
  have hmiddle := Nat.choose_le_middle (d-2) (2*d-2)
  rw [show (2*d-2)/2=d-1 by omega] at hmiddle
  have hpascal := Nat.choose_succ_succ (2*d-2) (d-2)
  simp only [Nat.succ_eq_add_one] at hpascal
  rw [show 2*d-2+1=2*d-1 by omega,show d-2+1=d-1 by omega] at hpascal
  have hH : centralHalfBinomial d ≤ 2*(2*d-2).choose (d-1) := by
    unfold centralHalfBinomial
    omega
  have hHreal : (centralHalfBinomial d : ℝ) ≤ 2*((2*d-2).choose (d-1) : ℝ) := by exact_mod_cast hH
  have hρ := (criticalRatio_bounds (show 2 ≤ d by omega)).1
  have hprod := (criticalRatio_bounds (show 2 ≤ d by omega)).2.2.1
  have hmul := mul_le_mul_of_nonneg_right hHreal hρ.le
  have hC : (0 : ℝ)<(2*d-2).choose (d-1) := by exact_mod_cast Nat.choose_pos (show d-1≤2*d-2 by omega)
  apply (div_lt_iff₀ hC).mpr
  nlinarith

/-- For sufficiently large outer dimension, the rounded linear convolution
blocks have a strict margin below the outer generator density. -/
theorem rowTwo_outer_block_margin {d : ℕ} (hd : 3 ≤ d) :
    ∀ᶠ h : ℕ in atTop,
      (convolutionBlockCount (rowTwoLinearDimension h) d (d-1) : ℝ)/((d-1).factorial : ℝ) <
        (h : ℝ)*criticalRatio d/((d-1).factorial : ℝ) := by
  have hl := convolutionBlockCount_normalized_limit (e := d-1) (by omega : 0 < 1)
    (by omega : 0 < d) rowTwoLinearDimension (1/4) (by simpa only [pow_one] using rowTwoLinearDimension_limit)
  have hgap : (1/4 : ℝ)/((d+(d-1)-1).choose (d-1) : ℝ) < criticalRatio d := by
    simpa only [show d+(d-1)-1=2*d-2 by omega] using rowTwo_outer_density_gap hd
  filter_upwards [hl.eventually (gt_mem_nhds hgap),eventually_gt_atTop (0 : ℕ)] with h hh hh0
  simp only [pow_one] at hh
  have hnum := (div_lt_iff₀ (show (0 : ℝ)<h by exact_mod_cast hh0)).mp hh
  have he := div_lt_div_of_pos_right hnum (show (0 : ℝ)<(d-1).factorial by positivity)
  simpa only [mul_comm (criticalRatio d) (h : ℝ)] using he

theorem rowTwo_quadratic_count_fits {d : ℕ} (hd : 3 ≤ d) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      convolutionBlockCount (rowTwoQuotientDimension h) (d+1) (d-2)*
        (m+(d+1)+(d-2)-2).choose (d-2) ≤
          ⌈countAlpha d*(h : ℝ)^2*(m : ℝ)^(d-2)⌉₊ := by
  apply convolution_blocks_eventually_fit_density (by omega) (by omega) (by omega)
    rowTwoQuotientDimension (9/32) (countAlpha d) rowTwoQuotientDimension_limit
  have hc := (quadratic_target_costs_lt_alpha hd).1
  rw [show d+1+(d-2)-1=2*d-2 by omega]
  convert hc using 1
  unfold quadraticRowTwoCost
  ring

end Froberg
