module

public import Froberg.ProductFiniteCapacity
public import Froberg.FullSparseBlockCount

@[expose] public section

/-! Fixed appended columns are absorbed by the strict finite capacity
margins, without changing either the prescribed density or the sparse block count. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem ceil_scaled_add_normalized_limit {s : ℕ} (hs : 0<s) (a : ℝ)
    (ha : 0≤a) (extra : ℕ) :
    Tendsto (fun n : ℕ => ((⌈a*(n : ℝ)^s⌉₊+extra : ℕ) : ℝ)/(n : ℝ)^s)
      atTop (𝓝 a) := by
  have hl := ceil_normalized_limit (fun n : ℕ => a*(n : ℝ)^s) hs a
    (Eventually.of_forall fun n => by positivity) (scaled_power_normalized_limit a s)
  have he : Tendsto (fun n : ℕ => (extra : ℝ)/(n : ℝ)^s) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (nat_power_tendsto_atTop s hs)
  simpa only [Nat.cast_add,add_div,add_zero] using hl.add he

theorem eventually_ceil_add_le_ceil {s : ℕ} (hs : 0<s) {a b : ℝ}
    (ha : 0≤a) (hab : a<b) (extra : ℕ) :
    ∀ᶠ n : ℕ in atTop,⌈a*(n : ℝ)^s⌉₊+extra≤⌈b*(n : ℝ)^s⌉₊ := by
  have hl := ceil_scaled_add_normalized_limit hs a ha extra
  have hr := ceil_scaled_add_normalized_limit hs b (ha.trans hab.le) 0
  simp only [Nat.add_zero] at hr
  filter_upwards [eventually_lt_of_normalized_limits _ _ s _ _ hl hr hab] with n hn
  exact_mod_cast hn.le

theorem sparseBlockCount_eventually_covers_add (γ : ℝ) (hγ : 0≤γ) (R w extra : ℕ)
    {s : ℕ} (hs : 0<s) :
    ∀ᶠ n : ℕ in atTop,⌈γ*(2*(w : ℝ))^R*(n : ℝ)^s⌉₊+extra≤
      sparseBlockCount γ R s w*(n+s-1).choose s := by
  have hl := ceil_scaled_add_normalized_limit hs (γ*(2*(w : ℝ))^R) (by positivity) extra
  have hr := (monomial_count_normalized_tendsto s).const_mul (sparseBlockCount γ R s w : ℝ)
  have hr' : Tendsto (fun n : ℕ =>
      ((sparseBlockCount γ R s w*(n+s-1).choose s : ℕ) : ℝ)/(n : ℝ)^s)
      atTop (𝓝 ((sparseBlockCount γ R s w : ℝ)/(s.factorial : ℝ))) := by
    simpa only [Nat.cast_mul,mul_div_assoc,div_eq_mul_inv,mul_assoc] using hr
  filter_upwards [eventually_lt_of_normalized_limits _ _ s _ _ hl hr'
    (sparseBlockCount_density_margin γ R s w)] with n hn
  exact_mod_cast hn.le

theorem fullSparseBlockCount_eventually_covers_add (γ : ℝ) (hγ : 0≤γ) (j h extra : ℕ)
    {s : ℕ} (hs : 0<s) :
    ∀ᶠ n : ℕ in atTop,⌈γ*(h : ℝ)^j*(n : ℝ)^s⌉₊+extra≤
      fullSparseBlockCount γ j s h*(n+s-1).choose s := by
  have he : γ/2^j*(2*(h : ℝ))^j=γ*(h : ℝ)^j := by rw [mul_pow];field_simp
  simpa only [fullSparseBlockCount_eq,he] using
    sparseBlockCount_eventually_covers_add (γ/2^j) (by positivity) j h extra hs

theorem eventually_quadratic_finite_product_capacity_add {d : ℕ} (hd : 9≤d) :
    ∀ᶠ h : ℕ in atTop,∀ extra : ℕ,∀ᶠ m : ℕ in atTop,∀ r : ℕ,
      (r : ℝ)<countBeta d*(h : ℝ)^2*(m : ℝ)^(d-2) →
      r+extra≤diagonalProductCount d 2 h m ∧ r+extra≤crossProductCount d 2 h m := by
  filter_upwards [eventually_product_capacity_majorant hd (two_mem_activeEvenIndices (by omega)),
    eventually_gt_atTop (0 : ℕ)] with h hh hh0
  intro extra
  have hΓ : 0<countGammaTwo d :=
    (countTauFour_pos (by omega)).trans_le (countTauFour_le_gamma d)
  have hβ : 0≤countBeta d := by unfold countBeta;positivity
  have hc : countBeta d<(253/250 : ℝ)*countGammaTwo d := by unfold countBeta;nlinarith
  have hh2 : 0<(h : ℝ)^2 := pow_pos (by exact_mod_cast hh0) 2
  have he := eventually_ceil_add_le_ceil (by omega : 0<d-2)
    (mul_nonneg hβ hh2.le) (mul_lt_mul_of_pos_right hc hh2) extra
  filter_upwards [hh,he] with m hm hem
  intro r hr
  have hrceil : r≤⌈countBeta d*(h : ℝ)^2*(m : ℝ)^(d-2)⌉₊ := by
    exact_mod_cast hr.le.trans (Nat.le_ceil _)
  have hdiag : r+extra≤diagonalProductCount d 2 h m :=
    (Nat.add_le_add_right hrceil extra).trans (hem.trans (by simpa [intermediateDensity] using hm))
  exact ⟨hdiag,hdiag.trans (diagonalProductCount_le_cross (by omega) (by omega))⟩

end Froberg
