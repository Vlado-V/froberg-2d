import Froberg.RoundingLimits
import Froberg.BoundedCounts
import Froberg.SlackPolynomial

/-! Exact generator selection from normalized limits, with uniform control
of the residual interval and any fixed lower bound on the auxiliary dimension. -/
noncomputable section
namespace Froberg
open Polynomial Filter
open scoped Topology

theorem scaled_power_normalized_limit (a : ℝ) (k : ℕ) :
    Tendsto (fun n : ℕ => a * (n : ℝ) ^ k / (n : ℝ) ^ k) atTop (𝓝 a) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hne : (n : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hn.ne')
  simp [hne]

theorem eventually_lt_of_normalized_limits (f g : ℕ → ℝ) (k : ℕ) (a b : ℝ)
    (hf : Tendsto (fun n => f n / (n : ℝ) ^ k) atTop (𝓝 a))
    (hg : Tendsto (fun n => g n / (n : ℝ) ^ k) atTop (𝓝 b)) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, f n < g n := by
  filter_upwards [hf.eventually_lt hg hab, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  exact (div_lt_div_iff_of_pos_right (pow_pos (by exact_mod_cast hn0 : (0 : ℝ) < n) k)).mp hn

theorem shifted_monomial_count_limit (k : ℕ) :
    Tendsto (fun n : ℕ => ((n + 1 + k - 1).choose k : ℝ) / (n : ℝ) ^ k)
      atTop (𝓝 ((k.factorial : ℝ)⁻¹)) := by
  have hdeg : (taylor (1 : ℝ) (monomialCountPolynomial k)).natDegree ≤ k := by
    rw [natDegree_taylor, monomialCountPolynomial_natDegree]
  have hc : (taylor (1 : ℝ) (monomialCountPolynomial k)).coeff k = (k.factorial : ℝ)⁻¹ := by
    rw [taylor_coefficient_at_bound _ _ _ (monomialCountPolynomial_natDegree k).le,
      monomialCountPolynomial_top]
  have hl := polynomial_div_pow_nat_tendsto (taylor (1 : ℝ) (monomialCountPolynomial k)) k hdeg
  rw [hc] at hl
  convert hl using 1
  congr 1
  funext n
  rw [taylor_eval, show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; rfl,
    monomialCountPolynomial_eval]

theorem eventually_exact_bounded_counts (K t lo : ℕ) (hK : 0 < K) (ht : 2 ≤ t)
    (R : ℕ → ℕ) (c A B : ℝ) (hA : 0 ≤ A) (hc : 0 < c)
    (hR : Tendsto (fun n => (R n : ℝ) / (n : ℝ) ^ t) atTop (𝓝 c))
    (hupper : c < (K : ℝ) / (t.factorial : ℝ))
    (hwidth : A + (K : ℝ) / ((t - 1).factorial : ℝ) < B) :
    ∀ᶠ n : ℕ in atTop, ∃ a f e : ℕ, lo ≤ a ∧ a ≤ n ∧
      f = K * (a + t - 1).choose t ∧ f + e = R n ∧
      A * (n : ℝ) ^ (t - 1) ≤ (e : ℝ) ∧ (e : ℝ) < B * (n : ℝ) ^ (t - 1) := by
  let emin : ℕ → ℕ := fun n => ⌈A * (n : ℝ) ^ (t - 1)⌉₊
  have hminlo : Tendsto (fun n => (emin n : ℝ) / (n : ℝ) ^ t) atTop (𝓝 0) :=
    ceil_monomial_lower_order (by omega) A hA
  have hminhi : Tendsto (fun n => (emin n : ℝ) / (n : ℝ) ^ (t - 1)) atTop (𝓝 A) :=
    ceil_normalized_limit _ (by omega) A
      (Eventually.of_forall fun n => mul_nonneg hA (pow_nonneg (Nat.cast_nonneg n) _))
      (scaled_power_normalized_limit A (t - 1))
  have hconst : Tendsto (fun n : ℕ => (K * (lo + t - 1).choose t : ℝ) / (n : ℝ) ^ t)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop (nat_power_tendsto_atTop t (by omega))
  have hloLimit : Tendsto (fun n => ((K * (lo + t - 1).choose t + emin n : ℕ) : ℝ) / (n : ℝ) ^ t)
      atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_mul, add_div, add_zero] using hconst.add hminlo
  have hhiLimit : Tendsto (fun n : ℕ => ((K * (n + 1 + t - 1).choose t : ℕ) : ℝ) / (n : ℝ) ^ t)
      atTop (𝓝 ((K : ℝ) / (t.factorial : ℝ))) := by
    simpa only [Nat.cast_mul, mul_div_assoc, div_eq_mul_inv, mul_assoc] using
      (shifted_monomial_count_limit t).const_mul (K : ℝ)
  have hwidthLimit : Tendsto (fun n : ℕ =>
      ((emin n + K * (n + 1 + (t - 1) - 1).choose (t - 1) : ℕ) : ℝ) / (n : ℝ) ^ (t - 1))
      atTop (𝓝 (A + (K : ℝ) / ((t - 1).factorial : ℝ))) := by
    have hh := hminhi.add ((shifted_monomial_count_limit (t - 1)).const_mul (K : ℝ))
    simpa only [Nat.cast_add, Nat.cast_mul, add_div, mul_div_assoc, div_eq_mul_inv, add_mul, mul_assoc] using hh
  have hlo := eventually_lt_of_normalized_limits _ _ t 0 c hloLimit hR hc
  have hhi := eventually_lt_of_normalized_limits _ _ t _ _ hR hhiLimit hupper
  have hw := eventually_lt_of_normalized_limits _ _ (t - 1) _ B hwidthLimit
    (scaled_power_normalized_limit B (t - 1)) hwidth
  filter_upwards [hlo, hhi, hw] with n hnlo hnhi hnw
  have hnl : K * (lo + t - 1).choose t + emin n ≤ R n := by exact_mod_cast hnlo.le
  have hnh : R n < K * (n + 1 + t - 1).choose t := by exact_mod_cast hnhi
  obtain ⟨a, f, e, ha₀, ha₁, hf, he, hemin, hewidth⟩ :=
    exists_exact_generator_count_with_bounds K (R n) (emin n) t lo n hK (by omega) hnl hnh
  refine ⟨a, f, e, ha₀, ha₁, hf, he, ?_, ?_⟩
  · have hceil : A * (n : ℝ) ^ (t - 1) ≤ (emin n : ℝ) := Nat.le_ceil _
    exact hceil.trans (by exact_mod_cast hemin)
  · exact (show (e : ℝ) < ((emin n + K * (n + 1 + (t - 1) - 1).choose (t - 1) : ℕ) : ℝ)
      by exact_mod_cast hewidth).trans hnw

end Froberg
