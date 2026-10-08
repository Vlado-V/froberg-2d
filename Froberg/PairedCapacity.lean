import Froberg.CoreFraction
import Froberg.BlockParameters

/-! # The paired scalar capacity in Appendix C.2

Both divisions in `L * ((n / 2).choose s / 2)` are natural-number divisions.
Their bounded remainders do not affect the strict leading-coefficient surplus.
-/

noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem natural_division_normalized_limit (f : ℕ → ℕ) {k q : ℕ}
    (hk : 0 < k) (hq : 0 < q) (c : ℝ)
    (hf : Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ) ^ k) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => ((f n / q : ℕ) : ℝ) / (n : ℝ) ^ k)
      atTop (𝓝 (c / (q : ℝ))) := by
  have heq (n : ℕ) : (f n : ℝ) - (q : ℝ) * ((f n / q : ℕ) : ℝ) =
      ((f n % q : ℕ) : ℝ) := by
    have h : ((f n % q : ℕ) : ℝ) + (q : ℝ) * ((f n / q : ℕ) : ℝ) = (f n : ℝ) := by
      exact_mod_cast Nat.mod_add_div (f n) q
    linarith
  have he := tendsto_bdd_div_atTop_nhds_zero
    (Eventually.of_forall fun n : ℕ => (show (0 : ℝ) ≤ ((f n % q : ℕ) : ℝ) by positivity))
    (Eventually.of_forall fun n : ℕ => (show ((f n % q : ℕ) : ℝ) ≤ (q : ℝ) by
      exact_mod_cast (Nat.mod_lt (f n) hq).le)) (nat_power_tendsto_atTop k hk)
  have hh := (hf.sub he).div_const (q : ℝ)
  simp only [sub_zero] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro n
  dsimp only
  rw [← heq n]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp
  <;> ring

theorem half_index_choose_limit (s : ℕ) :
    Tendsto (fun n : ℕ => ((n / 2).choose s : ℝ) / (n : ℝ) ^ s)
      atTop (𝓝 ((1 / 2 : ℝ) ^ s / (s.factorial : ℝ))) := by
  have hid : Tendsto (fun n : ℕ => (n : ℝ) / (n : ℝ) ^ 1) atTop (𝓝 (1 : ℝ)) := by
    simpa only [one_mul, pow_one] using scaled_power_normalized_limit 1 1
  have hhalf := natural_division_normalized_limit (fun n : ℕ => n) (by omega : 0 < 1)
    (by omega : 0 < 2) 1 hid
  simp only [pow_one, Nat.cast_ofNat] at hhalf
  have htop : Tendsto (fun n : ℕ => n / 2) atTop atTop :=
    Nat.tendsto_div_const_atTop (by omega)
  let v : ℕ → ℕ := fun n => n / 2 + 1 - s
  have hv : Tendsto v atTop atTop :=
    (tendsto_sub_atTop_nat s).comp ((tendsto_add_atTop_nat 1).comp htop)
  have hconst (a : ℝ) : Tendsto (fun n : ℕ => a / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ => (v n : ℝ) / (n : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) := by
    have hh := (hhalf.add (hconst 1)).sub (hconst (s : ℝ))
    simp only [add_zero, sub_zero] at hh
    apply hh.congr'
    filter_upwards [htop.eventually_ge_atTop s] with n hn
    dsimp only [v]
    rw [Nat.cast_sub (by omega : s ≤ n / 2 + 1)]
    push_cast
    ring
  have hh := scaled_index_monomial_limit v (1 / 2) s hv hratio
  apply hh.congr'
  filter_upwards [htop.eventually_ge_atTop s] with n hn
  have hvn : v n + s - 1 = n / 2 := by dsimp only [v]; omega
  simp only [hvn]

theorem paired_monomial_capacity_limit {s : ℕ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => (((n / 2).choose s / 2 : ℕ) : ℝ) / (n : ℝ) ^ s)
      atTop (𝓝 (1 / (2 ^ (s + 1) * (s.factorial : ℝ)))) := by
  have hh := natural_division_normalized_limit (fun n : ℕ => (n / 2).choose s)
    hs (by omega : 0 < 2) _ (half_index_choose_limit s)
  convert hh using 1
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, one_pow, pow_succ]
  ring

/-- Strict leading-coefficient surplus gives the exact rounded capacity. -/
theorem eventually_paired_capacity {s L : ℕ} (hs : 0 < s) (f : ℕ → ℕ) (c : ℝ)
    (hf : Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ) ^ s) atTop (𝓝 c))
    (hgap : c < (L : ℝ) / (2 ^ (s + 1) * (s.factorial : ℝ))) :
    ∀ᶠ n : ℕ in atTop, f n ≤ L * ((n / 2).choose s / 2) := by
  have hcap : Tendsto (fun n : ℕ => ((L * ((n / 2).choose s / 2) : ℕ) : ℝ) /
      (n : ℝ) ^ s) atTop (𝓝 ((L : ℝ) / (2 ^ (s + 1) * (s.factorial : ℝ)))) := by
    simpa only [Nat.cast_mul, mul_one_div, mul_div_assoc] using
      (paired_monomial_capacity_limit hs).const_mul (L : ℝ)
  filter_upwards [eventually_lt_of_normalized_limits _ _ s _ _ hf hcap hgap] with n hn
  exact_mod_cast hn.le

/-- The actual Section 5 choice of `L` satisfies the C.2 generator capacity. -/
theorem eventually_critical_paired_capacity {d h : ℕ} (hd : 3 ≤ d) (hh : 0 < h)
    (f : ℕ → ℕ)
    (hf : Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ) ^ (d - 1))
      atTop (𝓝 ((h : ℝ) * criticalRatio d / ((d - 1).factorial : ℝ)))) :
    ∀ᶠ n : ℕ in atTop,
      f n ≤ outerColumnCount d h * ((n / 2).choose (d - 1) / 2) := by
  apply eventually_paired_capacity (by omega : 0 < d - 1) f _ hf
  rw [show d - 1 + 1 = d by omega]
  have hL := outerColumnCount_strict_lower hd hh
  have hpow : (0 : ℝ) < 2 ^ d := by positivity
  have hfac : (0 : ℝ) < (d - 1).factorial := by exact_mod_cast Nat.factorial_pos (d - 1)
  apply (lt_div_iff₀ (mul_pos hpow hfac)).mpr
  calc
    (h : ℝ) * criticalRatio d / ((d - 1).factorial : ℝ) *
        (2 ^ d * ((d - 1).factorial : ℝ)) = 2 ^ d * criticalRatio d * h := by field_simp <;> ring
    _ < outerColumnCount d h := hL

end Froberg
