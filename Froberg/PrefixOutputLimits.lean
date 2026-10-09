module

public import Froberg.ConvolutionBlockLimits
public import Froberg.ScalarSeparationAsymptotic

@[expose] public section

/-! Strict output densities absorb both output rounding and block rounding. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem rounded_prefix_output_count {j x : ℕ} (hj : 0 < j) (τ : ℝ)
    (hτ : (x.factorial : ℝ)/((j+x).factorial : ℝ) < τ) :
    ∀ᶠ n : ℕ in atTop,
      (n+(j+x)-1).choose (j+x) ≤ ⌈τ*(n : ℝ)^j⌉₊*(n+x-1).choose x := by
  have hτ0 : 0 < τ := lt_trans (by positivity) hτ
  have hq := ceil_normalized_limit (fun n : ℕ => τ*(n : ℝ)^j) hj τ
    (Eventually.of_forall fun n => mul_nonneg hτ0.le (pow_nonneg (Nat.cast_nonneg n) _))
    (scaled_power_normalized_limit τ j)
  have hprod : Tendsto (fun n : ℕ =>
      ((⌈τ*(n : ℝ)^j⌉₊*(n+x-1).choose x : ℕ) : ℝ)/(n : ℝ)^(j+x))
      atTop (𝓝 (τ/(x.factorial : ℝ))) := by
    have ht := hq.mul (monomial_count_normalized_tendsto x)
    simp only [← div_eq_mul_inv] at ht
    apply ht.congr'
    apply Eventually.of_forall
    intro n
    dsimp only
    rw [Nat.cast_mul,pow_add]
    ring
  have hgap : ((j+x).factorial : ℝ)⁻¹ < τ/(x.factorial : ℝ) := by
    apply (lt_div_iff₀ (show (0 : ℝ)<x.factorial by positivity)).mpr
    simpa only [div_eq_mul_inv,mul_comm] using hτ
  filter_upwards [eventually_lt_of_normalized_limits _ _ (j+x) _ _
    (monomial_count_normalized_tendsto (j+x)) hprod hgap] with n hn
  exact_mod_cast hn.le

theorem rounded_convolution_blocks_margin {j a e : ℕ} (hj : 0 < j) (ha : 0 < a)
    (τ α : ℝ) (hτ : 0 < τ)
    (hgap : τ/(((a+e-1).choose e : ℝ)*(e.factorial : ℝ)) < α) :
    ∀ᶠ n : ℕ in atTop,
      (convolutionBlockCount ⌈τ*(n : ℝ)^j⌉₊ a e : ℝ)/(e.factorial : ℝ) < α*(n : ℝ)^j := by
  have hq := ceil_normalized_limit (fun n : ℕ => τ*(n : ℝ)^j) hj τ
    (Eventually.of_forall fun n => mul_nonneg hτ.le (pow_nonneg (Nat.cast_nonneg n) _))
    (scaled_power_normalized_limit τ j)
  have hblock := (convolutionBlockCount_normalized_limit (e := e) hj ha _ τ hq).div_const (e.factorial : ℝ)
  have hgap' : (τ/((a+e-1).choose e : ℝ))/(e.factorial : ℝ) < α := by
    simpa only [div_div] using hgap
  filter_upwards [hblock.eventually (gt_mem_nhds hgap'),eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hnp : (0 : ℝ)<(n : ℝ)^j := pow_pos (by exact_mod_cast hn0) _
  have heq : ((convolutionBlockCount ⌈τ*(n : ℝ)^j⌉₊ a e : ℝ)/(n : ℝ)^j)/(e.factorial : ℝ) =
      ((convolutionBlockCount ⌈τ*(n : ℝ)^j⌉₊ a e : ℝ)/(e.factorial : ℝ))/(n : ℝ)^j := by ring
  rw [heq] at hn
  exact (div_lt_iff₀ hnp).mp hn

end Froberg
