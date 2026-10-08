import Froberg.ThinShadowBudget
import Froberg.ScalarReserveCount

/-! Integer rounding and lower-order absorption for the actual layered
kernel budget. All kernel thresholds share the same chosen rate. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem thinSlices_integer_loss (j L : ℕ) (C : ℝ)
    (hC : 2*⌈C⌉₊ ≤ L) (r : ℕ) :
    j ≤ BilinearCovectorStrata.thinSlices j C r+⌈C*(r : ℝ)⌉₊ ∧
      ⌈C*(r : ℝ)⌉₊ ≤ L*r/2 := by
  constructor
  · unfold BilinearCovectorStrata.thinSlices
    omega
  · have hc : ⌈C*(r : ℝ)⌉₊ ≤ ⌈C⌉₊*r := by
      apply Nat.ceil_le.mpr
      exact_mod_cast mul_le_mul_of_nonneg_right (Nat.le_ceil C) (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
    apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
    calc
      ⌈C*(r : ℝ)⌉₊*2 ≤ (⌈C⌉₊*r)*2 := Nat.mul_le_mul_right 2 hc
      _ = (2*⌈C⌉₊)*r := by ring
      _ ≤ L*r := Nat.mul_le_mul_right r hC

theorem eventually_thin_integer_rate {d : ℕ} (hd : 0<d)
    {xi delta : ℝ} (hxi : 0 ≤ xi) (hgap : 2*xi<delta) :
    ∀ᶠ m : ℕ in atTop,2*⌈xi*(m : ℝ)^d⌉₊ ≤ ⌊delta*(m : ℝ)^d⌋₊ := by
  have hdelta : 0 ≤ delta := by linarith
  have hx := ceil_normalized_limit (fun m : ℕ => xi*(m : ℝ)^d) hd xi
    (Eventually.of_forall fun m => mul_nonneg hxi (pow_nonneg (Nat.cast_nonneg m) _))
    (scaled_power_normalized_limit xi d)
  have hl := floor_normalized_limit (fun m : ℕ => delta*(m : ℝ)^d) hd delta
    (Eventually.of_forall fun m => mul_nonneg hdelta (pow_nonneg (Nat.cast_nonneg m) _))
    (scaled_power_normalized_limit delta d)
  have hleft : Tendsto (fun m : ℕ => (2*⌈xi*(m : ℝ)^d⌉₊ : ℝ)/(m : ℝ)^d)
      atTop (𝓝 (2*xi)) := by
    simpa only [mul_div_assoc] using hx.const_mul 2
  filter_upwards [eventually_lt_of_normalized_limits _ _ d (2*xi) delta hleft hl hgap] with m hm
  exact_mod_cast hm.le

theorem eventually_layered_small_budget {d : ℕ} (hd : 0<d)
    {delta : ℝ} (hdelta : 0<delta) (H A q : ℕ → ℕ)
    (hH : Tendsto (fun m : ℕ => (H m : ℝ)/(m : ℝ)^d) atTop (𝓝 0))
    (hA : Tendsto (fun m : ℕ => (A m : ℝ)/(m : ℝ)^d) atTop (𝓝 0))
    (hq : Tendsto (fun m : ℕ => (q m : ℝ)/(m : ℝ)^d) atTop (𝓝 0)) :
    ∀ᶠ m : ℕ in atTop,2*(H m+A m+q m)+1 ≤ ⌊delta*(m : ℝ)^d⌋₊ := by
  have hconst : Tendsto (fun m : ℕ => (1 : ℝ)/(m : ℝ)^d) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (nat_power_tendsto_atTop d hd)
  have hleft : Tendsto (fun m : ℕ => ((2*(H m+A m+q m)+1 : ℕ) : ℝ)/(m : ℝ)^d)
      atTop (𝓝 0) := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,
      add_div,mul_div_assoc,zero_add,add_zero,mul_zero] using (((hH.add hA).add hq).const_mul 2).add hconst
  have hl := floor_normalized_limit (fun m : ℕ => delta*(m : ℝ)^d) hd delta
    (Eventually.of_forall fun m => mul_nonneg hdelta.le (pow_nonneg (Nat.cast_nonneg m) _))
    (scaled_power_normalized_limit delta d)
  filter_upwards [eventually_lt_of_normalized_limits _ _ d 0 delta hleft hl hdelta] with m hm
  exact_mod_cast hm.le

end Froberg
