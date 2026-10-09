module

public import Froberg.FixedSlotCapacity
public import Froberg.PreparedCountIdentities

@[expose] public section

/-! Fixed additions to the scalar variable count preserve normalized leading
coefficients. Rounded counts retain the same sparse block coverage. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem normalized_limit_shift {f : ℕ → ℝ} {s : ℕ} {c : ℝ}
    (hf : Tendsto (fun n => f n/(n : ℝ)^s) atTop (𝓝 c)) (z : ℕ) :
    Tendsto (fun n => f (n+z)/(n : ℝ)^s) atTop (𝓝 c) := by
  have hr : Tendsto (fun n : ℕ => ((n+z : ℕ) : ℝ)/(n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    have hz : Tendsto (fun n : ℕ => (z : ℝ)/(n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hz
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
    simp only [Nat.cast_add,add_div,div_self hn']
  have hl := (hf.comp (tendsto_add_atTop_nat z)).mul (hr.pow s)
  simp only [one_pow,mul_one] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnz : ((n+z : ℕ) : ℝ)≠0 := by exact_mod_cast (show n+z≠0 by omega)
  dsimp only [Function.comp_apply]
  rw [div_pow]
  field_simp

theorem shifted_ceil_add_normalized_limit {s : ℕ} (hs : 0<s) (a : ℝ)
    (ha : 0≤a) (z extra : ℕ) :
    Tendsto (fun n : ℕ => ((⌈a*((n+z : ℕ) : ℝ)^s⌉₊+extra : ℕ) : ℝ)/(n : ℝ)^s)
      atTop (𝓝 a) :=
  normalized_limit_shift (ceil_scaled_add_normalized_limit hs a ha extra) z

theorem eventually_shifted_ceil_add_le_ceil {s : ℕ} (hs : 0<s) {a b : ℝ}
    (ha : 0≤a) (hab : a<b) (z extra : ℕ) :
    ∀ᶠ n : ℕ in atTop,⌈a*((n+z : ℕ) : ℝ)^s⌉₊+extra≤⌈b*(n : ℝ)^s⌉₊ := by
  have hl := shifted_ceil_add_normalized_limit hs a ha z extra
  have hr := ceil_scaled_add_normalized_limit hs b (ha.trans hab.le) 0
  simp only [Nat.add_zero] at hr
  filter_upwards [eventually_lt_of_normalized_limits _ _ s _ _ hl hr hab] with n hn
  exact_mod_cast hn.le

theorem sparseBlockCount_eventually_covers_shift_add (γ : ℝ) (hγ : 0≤γ)
    (R w z extra : ℕ) {s : ℕ} (hs : 0<s) :
    ∀ᶠ n : ℕ in atTop,⌈γ*(2*(w : ℝ))^R*((n+z : ℕ) : ℝ)^s⌉₊+extra≤
      sparseBlockCount γ R s w*(n+s-1).choose s := by
  have hl := shifted_ceil_add_normalized_limit hs (γ*(2*(w : ℝ))^R) (by positivity) z extra
  have hr := (monomial_count_normalized_tendsto s).const_mul (sparseBlockCount γ R s w : ℝ)
  have hr' : Tendsto (fun n : ℕ =>
      ((sparseBlockCount γ R s w*(n+s-1).choose s : ℕ) : ℝ)/(n : ℝ)^s)
      atTop (𝓝 ((sparseBlockCount γ R s w : ℝ)/(s.factorial : ℝ))) := by
    simpa only [Nat.cast_mul,mul_div_assoc,div_eq_mul_inv,mul_assoc] using hr
  filter_upwards [eventually_lt_of_normalized_limits _ _ s _ _ hl hr'
    (sparseBlockCount_density_margin γ R s w)] with n hn
  exact_mod_cast hn.le

theorem fullSparseBlockCount_eventually_covers_shift_add (γ : ℝ) (hγ : 0≤γ)
    (j h z extra : ℕ) {s : ℕ} (hs : 0<s) :
    ∀ᶠ n : ℕ in atTop,⌈γ*(h : ℝ)^j*((n+z : ℕ) : ℝ)^s⌉₊+extra≤
      fullSparseBlockCount γ j s h*(n+s-1).choose s := by
  have he : γ/2^j*(2*(h : ℝ))^j=γ*(h : ℝ)^j := by rw [mul_pow];field_simp
  simpa only [fullSparseBlockCount_eq,he] using
    sparseBlockCount_eventually_covers_shift_add (γ/2^j) (by positivity) j h z extra hs

/-- A fixed scalar shift and a fixed number of extra columns preserve any
strict product-capacity margin, including the Appendix E special blocks. -/
theorem eventually_product_capacity_of_limits_shift {j s : ℕ} (hs : 0<s)
    (A B : ℕ → ℕ) (a b γ : ℝ) (hγ : 0≤γ)
    (hA : Tendsto (fun h : ℕ => (A h : ℝ)/(h : ℝ)^j) atTop (𝓝 a))
    (hB : Tendsto (fun n : ℕ => (B n : ℝ)/(n : ℝ)^s) atTop (𝓝 b))
    (hgap : γ<a*b) :
    ∀ᶠ h : ℕ in atTop,∀ z extra : ℕ,∀ᶠ n : ℕ in atTop,
      ⌈γ*(h : ℝ)^j*((n+z : ℕ) : ℝ)^s⌉₊+extra≤A h*B n := by
  have hl := hA.mul_const b
  filter_upwards [hl.eventually (lt_mem_nhds hgap),eventually_gt_atTop (0 : ℕ)] with h hh hh0
  intro z extra
  have hp : 0<(h : ℝ)^j := pow_pos (by exact_mod_cast hh0) _
  have hg : γ*(h : ℝ)^j < (A h : ℝ)*b := by
    have he : (A h : ℝ)/(h : ℝ)^j*b = ((A h : ℝ)*b)/(h : ℝ)^j := by ring
    rw [he] at hh
    exact (lt_div_iff₀ hp).mp hh
  have hF := shifted_ceil_add_normalized_limit hs (γ*(h : ℝ)^j) (by positivity) z extra
  have hG : Tendsto (fun n : ℕ => ((A h*B n : ℕ) : ℝ)/(n : ℝ)^s)
      atTop (𝓝 ((A h : ℝ)*b)) := by
    simpa only [Nat.cast_mul,mul_div_assoc] using hB.const_mul (A h : ℝ)
  filter_upwards [eventually_lt_of_normalized_limits _ _ s _ _ hF hG hg] with n hn
  exact_mod_cast hn.le

end Froberg
