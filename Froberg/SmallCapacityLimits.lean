import Froberg.ProductCapacityGeneral
import Froberg.NormalizedLimits

/-! Limits of the exact integer capacities used in Appendix E. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem natural_monomial_div_limit (c : ℕ) {q k : ℕ} (hq : 0<q) (hk : 0<k) :
    Tendsto (fun n : ℕ => ((c*n^k/q : ℕ) : ℝ)/(n : ℝ)^k)
      atTop (𝓝 ((c : ℝ)/(q : ℝ))) := by
  apply natural_division_normalized_limit _ hk hq (c : ℝ)
  simpa only [Nat.cast_mul,Nat.cast_pow] using scaled_power_normalized_limit (c : ℝ) k

theorem natural_fraction_tendsto_atTop {a b : ℕ} (ha : 0<a) (hb : 0<b) :
    Tendsto (fun n : ℕ => a*n/b) atTop atTop := by
  apply tendsto_atTop.mpr
  intro N
  filter_upwards [eventually_ge_atTop (b*N)] with n hn
  apply (Nat.le_div_iff_mul_le hb).mpr
  nlinarith

theorem natural_fraction_monomial_limit {a b : ℕ} (ha : 0<a) (hb : 0<b) (s : ℕ) :
    Tendsto (fun n : ℕ => ((a*n/b+s-1).choose s : ℝ)/(n : ℝ)^s)
      atTop (𝓝 (((a : ℝ)/(b : ℝ))^s/(s.factorial : ℝ))) := by
  apply scaled_index_monomial_limit _ _ s (natural_fraction_tendsto_atTop ha hb)
  simpa only [pow_one] using natural_monomial_div_limit a hb (by omega : 0<1)

theorem half_monomial_count_limit (s : ℕ) :
    Tendsto (fun n : ℕ => ((n/2+s-1).choose s : ℝ)/(n : ℝ)^s)
      atTop (𝓝 ((1/2 : ℝ)^s/(s.factorial : ℝ))) := by
  simpa only [one_mul,Nat.cast_one,Nat.cast_ofNat] using
    natural_fraction_monomial_limit (by omega : 0<1) (by omega : 0<2) s

theorem complement_fifths_monomial_limit (s : ℕ) :
    Tendsto (fun n : ℕ => ((n-2*n/5+s-1).choose s : ℝ)/(n : ℝ)^s)
      atTop (𝓝 ((3/5 : ℝ)^s/(s.factorial : ℝ))) := by
  have hratio : Tendsto (fun n : ℕ => ((n-2*n/5 : ℕ) : ℝ)/(n : ℝ)) atTop (𝓝 (3/5 : ℝ)) := by
    have hf : Tendsto (fun n : ℕ => ((2*n/5 : ℕ) : ℝ)/(n : ℝ)) atTop (𝓝 (2/5 : ℝ)) := by
      simpa only [pow_one,Nat.cast_ofNat] using
        natural_monomial_div_limit 2 (by omega : 0<5) (by omega : 0<1)
    have hid : Tendsto (fun n : ℕ => (n : ℝ)/(n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
      simpa only [one_mul,pow_one] using scaled_power_normalized_limit (1 : ℝ) 1
    have he : (1 : ℝ)-2/5=3/5 := by norm_num
    rw [← he]
    apply (hid.sub hf).congr'
    exact Eventually.of_forall fun n => by
      dsimp only
      rw [Nat.cast_sub (by omega : 2*n/5≤n),sub_div]
  have htop : Tendsto (fun n : ℕ => n-2*n/5) atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop (2*N)] with n hn
    omega
  exact scaled_index_monomial_limit _ _ s htop hratio

end Froberg
