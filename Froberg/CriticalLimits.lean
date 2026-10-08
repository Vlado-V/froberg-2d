import Froberg.CriticalApproximation
import Froberg.CriticalRatioBounds
import Froberg.PolynomialAsymptotics

/-! Normalized limits for the critical count and its fixed-step increment,
including either choice of the adjacent integer count. -/
noncomputable section
namespace Froberg
open Polynomial Filter
open scoped Topology

theorem nat_power_tendsto_atTop (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ k) atTop atTop :=
  (tendsto_pow_atTop (by omega : k ≠ 0)).comp tendsto_natCast_atTop_atTop

theorem approximated_polynomial_normalized_limit (f : ℕ → ℝ)
    (P : Polynomial ℝ) (k : ℕ) (hk : 0 < k) (hP : P.natDegree ≤ k)
    (herr : Tendsto (fun n => f n - P.eval (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => f n / (n : ℝ) ^ k) atTop (𝓝 (P.coeff k)) := by
  have h := (herr.div_atTop (nat_power_tendsto_atTop k hk)).add
    (polynomial_div_pow_nat_tendsto P k hP)
  simpa only [zero_add, sub_div, sub_add_cancel] using h

theorem approximated_polynomial_increment_limit (f : ℕ → ℝ)
    (P : Polynomial ℝ) (k h : ℕ) (hk : 0 < k) (hP : P.natDegree ≤ k + 1)
    (herr : Tendsto (fun n => f n - P.eval (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => (f (n + h) - f n) / (n : ℝ) ^ k)
      atTop (𝓝 ((k + 1 : ℝ) * h * P.coeff (k + 1))) := by
  have he := ((herr.comp (tendsto_add_atTop_nat h)).sub herr).div_atTop
    (nat_power_tendsto_atTop k hk)
  have hl := he.add (finite_difference_normalized_limit P (h : ℝ) k hP)
  convert hl using 1
  · congr 1
    funext n
    simp only [Function.comp_apply, Nat.cast_add]
    ring
  · simp

theorem kappa_normalized_limit {d : ℕ} (hd : 2 ≤ d) :
    Tendsto (fun n : ℕ => kappa n d / (n : ℝ) ^ d)
      atTop (𝓝 (criticalRatio d / (d.factorial : ℝ))) := by
  obtain ⟨P, hP, hL, _, he⟩ := exists_critical_polynomial_approximation hd
  have hc : P.coeff d = criticalRatio d / (d.factorial : ℝ) := by
    rw [show P.coeff d = P.leadingCoeff by simpa only [hP] using (coeff_natDegree (p := P))]
    exact hL
  rw [← hc]
  exact approximated_polynomial_normalized_limit (fun n => kappa n d) P d
    (by omega) hP.le he

theorem kappa_increment_limit {d : ℕ} (hd : 2 ≤ d) (h : ℕ) :
    Tendsto (fun n : ℕ => (kappa (n + h) d - kappa n d) / (n : ℝ) ^ (d - 1))
      atTop (𝓝 ((d : ℝ) * h * (criticalRatio d / (d.factorial : ℝ)))) := by
  obtain ⟨P, hP, hL, _, he⟩ := exists_critical_polynomial_approximation hd
  have hi : d - 1 + 1 = d := by omega
  have hc : P.coeff d = criticalRatio d / (d.factorial : ℝ) := by
    rw [show P.coeff d = P.leadingCoeff by simpa only [hP] using (coeff_natDegree (p := P))]
    exact hL
  have hl := approximated_polynomial_increment_limit (fun n => kappa n d) P
    (d - 1) h (by omega) (by omega) he
  rw [hi, hc] at hl
  have hir : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by exact_mod_cast hi
  simpa only [hir] using hl

theorem critical_integer_error_bounds {n r : ℕ} (hn : 0 < n) (d : ℕ)
    (hrlo : lowerCount n d ≤ r) (hrhi : r ≤ upperCount n d) :
    -1 < (r : ℝ) - kappa n d ∧ (r : ℝ) - kappa n d < 1 := by
  have hfloor := Nat.lt_floor_add_one (kappa n d)
  have hceil := Nat.ceil_lt_add_one (kappa_bounds hn d).1.le
  have hlo : (lowerCount n d : ℝ) ≤ r := by exact_mod_cast hrlo
  have hhi : (r : ℝ) ≤ upperCount n d := by exact_mod_cast hrhi
  change kappa n d < (lowerCount n d : ℝ) + 1 at hfloor
  change (upperCount n d : ℝ) < kappa n d + 1 at hceil
  constructor <;> linarith

theorem rounded_critical_increment_limit {d : ℕ} (hd : 2 ≤ d) (h : ℕ)
    (r : ℕ → ℕ) (hr : ∀ n, 0 < n → lowerCount n d ≤ r n ∧ r n ≤ upperCount n d) :
    Tendsto (fun n : ℕ => ((r (n + h) : ℝ) - (upperCount n d : ℝ)) / (n : ℝ) ^ (d - 1))
      atTop (𝓝 ((d : ℝ) * h * (criticalRatio d / (d.factorial : ℝ)))) := by
  let E : ℕ → ℝ := fun n =>
    ((r (n + h) : ℝ) - kappa (n + h) d) - ((upperCount n d : ℝ) - kappa n d)
  have hbound : ∀ᶠ n : ℕ in atTop, -2 ≤ E n ∧ E n ≤ 2 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnp : 0 < n + h := by omega
    have h₁ := critical_integer_error_bounds hnp d (hr (n + h) hnp).1 (hr (n + h) hnp).2
    have h₂ := critical_integer_error_bounds hn d (lowerCount_le_upperCount n d) le_rfl
    dsimp only [E]
    constructor <;> linarith
  have he := tendsto_bdd_div_atTop_nhds_zero
    (hbound.mono fun _ h => h.1) (hbound.mono fun _ h => h.2)
    (nat_power_tendsto_atTop (d - 1) (by omega))
  have hl := he.add (kappa_increment_limit hd h)
  convert hl using 1
  · congr 1
    funext n
    dsimp only [E]
    ring
  · simp

end Froberg
