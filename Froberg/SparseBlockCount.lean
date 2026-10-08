import Froberg.ConvolutionBlockLimits
import Froberg.ScalarSeparationAsymptotic

/-! A rounded number of sparse scalar blocks with a strict surplus over
the prescribed generator density. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

/-- The added block leaves a strict margin after rounding the leading count. -/
def sparseBlockCount (γ : ℝ) (R s w : ℕ) : ℕ :=
  ⌈(γ*2^R*(s.factorial : ℝ))*(w : ℝ)^R⌉₊+1

theorem sparseBlockCount_limit {R s : ℕ} (hR : 0<R) (γ : ℝ) (hγ : 0≤γ) :
    Tendsto (fun w : ℕ => (sparseBlockCount γ R s w : ℝ)/(w : ℝ)^R)
      atTop (𝓝 (γ*2^R*(s.factorial : ℝ))) := by
  have hc := ceil_normalized_limit
    (fun w : ℕ => (γ*2^R*(s.factorial : ℝ))*(w : ℝ)^R)
    hR (γ*2^R*(s.factorial : ℝ))
    (Eventually.of_forall fun w => by positivity)
    (scaled_power_normalized_limit _ _)
  have h1 : Tendsto (fun w : ℕ => (1 : ℝ)/(w : ℝ)^R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (nat_power_tendsto_atTop R hR)
  simpa only [sparseBlockCount,Nat.cast_add,Nat.cast_one,add_div,add_zero] using hc.add h1

theorem sparseBlockCount_density_margin (γ : ℝ) (R s w : ℕ) :
    γ*(2*(w : ℝ))^R < (sparseBlockCount γ R s w : ℝ)/(s.factorial : ℝ) := by
  apply (lt_div_iff₀ (show (0 : ℝ)<s.factorial by positivity)).mpr
  have hc := Nat.le_ceil ((γ*2^R*(s.factorial : ℝ))*(w : ℝ)^R)
  have he : γ*(2*(w : ℝ))^R*(s.factorial : ℝ) =
      (γ*2^R*(s.factorial : ℝ))*(w : ℝ)^R := by rw [mul_pow]; ring
  rw [he]
  simp only [sparseBlockCount,Nat.cast_add,Nat.cast_one]
  linarith

/-- Every prescribed rounded count fits the chosen number of complete
scalar polynomial blocks, once the scalar variable count is large. -/
theorem sparseBlockCount_eventually_covers (γ : ℝ) (hγ : 0≤γ) (R w : ℕ)
    {s : ℕ} (hs : 0<s) :
    ∀ᶠ n : ℕ in atTop,
      ⌈γ*(2*(w : ℝ))^R*(n : ℝ)^s⌉₊ ≤ sparseBlockCount γ R s w*(n+s-1).choose s := by
  have hl := ceil_normalized_limit
    (fun n : ℕ => γ*(2*(w : ℝ))^R*(n : ℝ)^s) hs (γ*(2*(w : ℝ))^R)
    (Eventually.of_forall fun n => by positivity) (scaled_power_normalized_limit _ _)
  have hr := (monomial_count_normalized_tendsto s).const_mul (sparseBlockCount γ R s w : ℝ)
  have hr' : Tendsto (fun n : ℕ =>
      ((sparseBlockCount γ R s w*(n+s-1).choose s : ℕ) : ℝ)/(n : ℝ)^s)
      atTop (𝓝 ((sparseBlockCount γ R s w : ℝ)/(s.factorial : ℝ))) := by
    simpa only [Nat.cast_mul,mul_div_assoc,div_eq_mul_inv,mul_assoc] using hr
  filter_upwards [eventually_lt_of_normalized_limits _ _ s _ _ hl hr'
    (sparseBlockCount_density_margin γ R s w)] with n hn
  exact_mod_cast hn.le

end Froberg
