import Froberg.CountConstruction
import Mathlib.Algebra.Order.Ring.Pow

/-! A fixed positive proportion of variables remains outside the auxiliary
core. An explicit rational fraction avoids any inverse-asymptotics premise. -/
noncomputable section
namespace Froberg
open Filter Polynomial
open scoped Topology

def coreFraction (s : ℕ) : ℝ := 1 - 1 / (4 * (s : ℝ))

theorem coreFraction_bounds {s : ℕ} (hs : 0 < s) :
    0 < coreFraction s ∧ coreFraction s < 1 := by
  have hsr : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hpos : (0 : ℝ) < 1 / (4 * (s : ℝ)) := by positivity
  have hle : 1 / (4 * (s : ℝ)) ≤ 1 / 4 := by
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  unfold coreFraction
  constructor <;> linarith

theorem coreFraction_pow_lower {s : ℕ} (hs : 0 < s) :
    (3 / 4 : ℝ) ≤ coreFraction s ^ s := by
  have hbound := coreFraction_bounds hs
  have hb := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ coreFraction s by linarith) s
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have heq : 1 + (s : ℝ) * (coreFraction s - 1) = 3 / 4 := by
    unfold coreFraction
    field_simp
    ring
  rwa [heq] at hb

theorem scaled_index_monomial_limit (v : ℕ → ℕ) (τ : ℝ) (k : ℕ)
    (hv : Tendsto v atTop atTop)
    (hratio : Tendsto (fun n => (v n : ℝ) / (n : ℝ)) atTop (𝓝 τ)) :
    Tendsto (fun n => ((v n + k - 1).choose k : ℝ) / (n : ℝ) ^ k)
      atTop (𝓝 (τ ^ k / (k.factorial : ℝ))) := by
  have hm := polynomial_div_pow_nat_tendsto (monomialCountPolynomial k) k
    (monomialCountPolynomial_natDegree k).le
  simp only [monomialCountPolynomial_top, monomialCountPolynomial_eval] at hm
  have hh := (hm.comp hv).mul (hratio.pow k)
  have hl : (k.factorial : ℝ)⁻¹ * τ ^ k = τ ^ k / (k.factorial : ℝ) := by ring
  rw [hl] at hh
  apply hh.congr'
  filter_upwards [hv.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℕ)] with n hvn hn
  have hv0 : (v n : ℝ) ≠ 0 := by exact_mod_cast hvn.ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  dsimp only [Function.comp_apply]
  rw [div_pow]
  field_simp

theorem floor_fraction_monomial_limit (τ : ℝ) (hτ : 0 < τ) (k : ℕ) :
    Tendsto (fun n : ℕ => ((⌊τ * (n : ℝ)⌋₊ + 1 + k - 1).choose k : ℝ) / (n : ℝ) ^ k)
      atTop (𝓝 (τ ^ k / (k.factorial : ℝ))) := by
  apply scaled_index_monomial_limit (fun n : ℕ => ⌊τ * (n : ℝ)⌋₊ + 1) τ k
  · exact (tendsto_add_atTop_nat 1).comp (tendsto_nat_floor_mul_atTop τ hτ)
  · have hf := (tendsto_nat_floor_mul_div_atTop hτ.le).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    have hone : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa only [Nat.cast_add, Nat.cast_one, add_div, add_zero, Function.comp_apply] using hf.add hone

theorem eventually_core_bound (R : ℕ → ℕ) (K s : ℕ) (τ c : ℝ) (hτ : 0 < τ)
    (hR : Tendsto (fun n => (R n : ℝ) / (n : ℝ) ^ s) atTop (𝓝 c))
    (hgap : c < (K : ℝ) * τ ^ s / (s.factorial : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∀ a f : ℕ,
      f = K * (a + s - 1).choose s → f ≤ R n → a ≤ ⌊τ * (n : ℝ)⌋₊ := by
  have hlim : Tendsto (fun n : ℕ =>
      ((K * (⌊τ * (n : ℝ)⌋₊ + 1 + s - 1).choose s : ℕ) : ℝ) / (n : ℝ) ^ s)
      atTop (𝓝 ((K : ℝ) * τ ^ s / (s.factorial : ℝ))) := by
    simpa only [Nat.cast_mul, div_eq_mul_inv, mul_assoc] using
      (floor_fraction_monomial_limit τ hτ s).const_mul (K : ℝ)
  have hh := eventually_lt_of_normalized_limits _ _ s _ _ hR hlim hgap
  filter_upwards [hh] with n hn a f hf hfr
  have hnr : R n < K * (⌊τ * (n : ℝ)⌋₊ + 1 + s - 1).choose s := by exact_mod_cast hn
  by_contra ha
  have hm := Nat.mul_le_mul_left K (monomial_count_mono_variables (t := s)
    (show ⌊τ * (n : ℝ)⌋₊ + 1 ≤ a by omega))
  omega

theorem critical_core_capacity_gap {d K h : ℕ} (hd : 3 ≤ d) (hK : 0 < K)
    (hh : h = K * centralHalfBinomial d) :
    (h : ℝ) * criticalRatio d / ((d - 1).factorial : ℝ) <
      (K : ℝ) * coreFraction (d - 1) ^ (d - 1) / ((d - 1).factorial : ℝ) := by
  have hρ := (criticalRatio_bounds (d := d) (by omega)).2.2.2
  have hpow := coreFraction_pow_lower (s := d - 1) (by omega)
  have hgap : (centralHalfBinomial d : ℝ) * criticalRatio d < coreFraction (d - 1) ^ (d - 1) := by
    linarith
  apply div_lt_div_of_pos_right _ (by exact_mod_cast Nat.factorial_pos (d - 1))
  have hm := mul_lt_mul_of_pos_left hgap (show (0 : ℝ) < K by exact_mod_cast hK)
  rw [hh]
  push_cast
  nlinarith

end Froberg
