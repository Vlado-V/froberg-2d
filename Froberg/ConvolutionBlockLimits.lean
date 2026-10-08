import Froberg.ConvolutionDimension
import Froberg.PairedCapacity

/-! The two rounding operations in B.7 preserve the required leading densities. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem convolutionBlockCount_normalized_limit {j a e : ℕ} (hj : 0<j) (ha : 0<a)
    (q : ℕ → ℕ) (c : ℝ)
    (hq : Tendsto (fun n : ℕ => (q n : ℝ)/(n : ℝ)^j) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (convolutionBlockCount (q n) a e : ℝ)/(n : ℝ)^j)
      atTop (𝓝 (c/((a+e-1).choose e : ℝ))) := by
  let Q := (a+e-1).choose e
  have hQ : 0<Q := Nat.choose_pos (by omega)
  have hc : Tendsto (fun n : ℕ => ((Q-1 : ℕ) : ℝ)/(n : ℝ)^j) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop (nat_power_tendsto_atTop j hj)
  have hnum : Tendsto (fun n : ℕ => ((q n+Q-1 : ℕ) : ℝ)/(n : ℝ)^j) atTop (𝓝 c) := by
    have h := hq.add hc
    simp only [add_zero] at h
    apply h.congr'
    apply Eventually.of_forall
    intro n
    dsimp only
    rw [show q n+Q-1=q n+(Q-1) by omega,Nat.cast_add,add_div]
  exact natural_division_normalized_limit _ hj hQ c hnum

theorem convolutionGeneratorCount_normalized_limit (k e : ℕ) {a : ℕ} (ha : 0<a) :
    Tendsto (fun n : ℕ => ((k*(n+a+e-2).choose e : ℕ) : ℝ)/(n : ℝ)^e)
      atTop (𝓝 ((k : ℝ)/(e.factorial : ℝ))) := by
  let v : ℕ → ℕ := fun n => n+(a-1)
  have hv : Tendsto v atTop atTop := tendsto_add_atTop_nat (a-1)
  have hid : Tendsto (fun n : ℕ => (n : ℝ)/(n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [one_mul,pow_one] using scaled_power_normalized_limit (1 : ℝ) 1
  have hconst : Tendsto (fun n : ℕ => ((a-1 : ℕ) : ℝ)/(n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ => (v n : ℝ)/(n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [v,Nat.cast_add,add_div,add_zero] using hid.add hconst
  have h := (scaled_index_monomial_limit v 1 e hv hratio).const_mul (k : ℝ)
  simp only [one_pow,mul_one_div] at h
  apply h.congr'
  apply Eventually.of_forall
  intro n
  have heq : v n+e-1=n+a+e-2 := by dsimp only [v]; omega
  dsimp only
  rw [heq,Nat.cast_mul]
  ring

theorem convolutionGeneratorCount_eventually_fits {k e a : ℕ} (he : 0<e) (ha : 0<a)
    (c : ℝ) (hgap : (k : ℝ)/(e.factorial : ℝ)<c) :
    ∀ᶠ n : ℕ in atTop, k*(n+a+e-2).choose e ≤ ⌈c*(n : ℝ)^e⌉₊ := by
  have hc : 0≤c := le_of_lt (lt_of_le_of_lt (by positivity) hgap)
  have hceil := ceil_normalized_limit (fun n : ℕ => c*(n : ℝ)^e) he c
    (Eventually.of_forall fun n => mul_nonneg hc (pow_nonneg (Nat.cast_nonneg n) _))
    (scaled_power_normalized_limit c e)
  filter_upwards [eventually_lt_of_normalized_limits _ _ e _ _
    (convolutionGeneratorCount_normalized_limit k e ha) hceil hgap] with n hn
  exact_mod_cast hn.le

end Froberg
