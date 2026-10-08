import Froberg.SlackLeading

/-! Positivity of the actual dimension margin for every exact count in the
prescribed interval, including both adjacent critical generator counts. -/
noncomputable section
namespace Froberg
open Polynomial Filter
open scoped Topology

theorem slack_lower_bound (T S D q f Q F h : ℝ)
    (hA : f ≤ h * S) (hq : q ≤ Q) (hf : f ≤ F) (hD : Q ≤ D) :
    h * T - h * Q * S - F * (D - Q) ≤ h * T - f * D - q * (h * S - f) := by
  have h₁ := mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hA)
  have h₂ := mul_nonneg (sub_nonneg.mpr hf) (sub_nonneg.mpr hD)
  nlinarith

theorem eventually_polynomial_pos (P : Polynomial ℝ) (k : ℕ)
    (hP : P.natDegree ≤ k) (hc : 0 < P.coeff k) :
    ∀ᶠ n : ℕ in atTop, 0 < P.eval (n : ℝ) := by
  obtain ⟨δ, hδ, hbound⟩ := polynomial_positive_lower_bound P k hP hc
  exact hbound.mono fun n hn => (mul_nonneg hδ.le (pow_nonneg (Nat.cast_nonneg n) k)).trans_lt hn

theorem eventually_rounded_critical_between {d : ℕ} (P : Polynomial ℝ)
    (he : Tendsto (fun n : ℕ => kappa n d - P.eval (n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, lowerCount n d ≤ r → r ≤ upperCount n d →
      P.eval (n : ℝ) - 2 < (r : ℝ) ∧ (r : ℝ) < P.eval (n : ℝ) + 2 := by
  have hlo := he.eventually (lt_mem_nhds (by norm_num : (-1 : ℝ) < 0))
  have hhi := he.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hlo, hhi, eventually_gt_atTop (0 : ℕ)] with n hnlo hnhi hn r hrlo hrhi
  have herr := critical_integer_error_bounds hn d hrlo hrhi
  constructor <;> linarith

theorem count_bound_polynomial_capacities {d : ℕ} (hd : 3 ≤ d)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (hL : P.coeff d = criticalRatio d / (d.factorial : ℝ))
    (h : ℕ) (hh : 0 < h) (α : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℝ) + 2 ≤ ((n + d - 1).choose d : ℝ) ∧
      (outerCountBoundPolynomial P d h α).eval (n : ℝ) ≤
        (h : ℝ) * ((n + (d - 1) - 1).choose (d - 1) : ℝ) := by
  let D := monomialCountPolynomial d - (P + C 2)
  have hDdeg : D.natDegree ≤ d := (natDegree_sub_le _ _).trans
    (max_le (monomialCountPolynomial_natDegree d).le (adjustedCritical_degree P hP))
  have hf : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  have hρ := (criticalRatio_bounds (d := d) (by omega)).2.1
  have hDcoeff : 0 < D.coeff d := by
    dsimp only [D]
    rw [coeff_sub, monomialCountPolynomial_top, adjustedCritical_coeff P (by omega), hL]
    convert div_pos (sub_pos.mpr hρ) hf using 1 <;> ring
  let A := C (h : ℝ) * monomialCountPolynomial (d - 1) - outerCountBoundPolynomial P d h α
  have hAdeg : A.natDegree ≤ d - 1 := (natDegree_sub_le _ _).trans
    (max_le ((natDegree_C_mul_le _ _).trans (monomialCountPolynomial_natDegree _).le)
      (outerCountBound_degree (by omega) P h α hP))
  have hAcoeff : 0 < A.coeff (d - 1) := by
    dsimp only [A]
    rw [coeff_sub, coeff_C_mul, monomialCountPolynomial_top, outerCountBound_top hd P h α hP,
      hL, inverse_factorial_step (by omega : 0 < d)]
    have hp : 0 < (h : ℝ) * (d : ℝ) / (d.factorial : ℝ) * (1 - criticalRatio d) :=
      mul_pos (div_pos (mul_pos (by exact_mod_cast hh) (by exact_mod_cast (show 0 < d by omega))) hf)
        (sub_pos.mpr hρ)
    convert hp using 1 <;> ring
  filter_upwards [eventually_polynomial_pos D d hDdeg hDcoeff,
    eventually_polynomial_pos A (d - 1) hAdeg hAcoeff] with n hnD hnA
  dsimp only [D] at hnD
  dsimp only [A] at hnA
  simp only [eval_sub, eval_add, eval_mul, eval_C, monomialCountPolynomial_eval] at hnD hnA
  constructor <;> linarith

theorem exact_count_positive_margin {d : ℕ} (hd : 3 ≤ d)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (hL : P.coeff d = criticalRatio d / (d.factorial : ℝ))
    (he : Tendsto (fun n : ℕ => kappa n d - P.eval (n : ℝ)) atTop (𝓝 0)) :
    ∃ H : ℕ, ∀ h : ℕ, H ≤ h → 0 < h → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ n : ℕ in atTop, ∀ r f g e : ℕ,
        lowerCount (n + h) d ≤ r → r ≤ upperCount (n + h) d →
        upperCount n d + f + g + e = r →
        countAlpha d * (h : ℝ) ^ 2 * (n : ℝ) ^ (d - 2) ≤ (e : ℝ) →
        δ * (n : ℝ) ^ (2 * d - 2) <
          (h : ℝ) * ((n + (2 * d - 1) - 1).choose (2 * d - 1) : ℝ) -
          (f : ℝ) * ((n + d - 1).choose d : ℝ) -
          (upperCount n d : ℝ) *
            ((h : ℝ) * ((n + (d - 1) - 1).choose (d - 1) : ℝ) - f) := by
  obtain ⟨H, hH⟩ := adjusted_slack_eventually_positive hd P hP hL
  refine ⟨H, fun h hh hpos => ?_⟩
  obtain ⟨δ, hδ, hmargin⟩ := hH h hh
  refine ⟨δ, hδ, ?_⟩
  have hround := eventually_rounded_critical_between P he
  have hroundshift := (tendsto_add_atTop_nat h).eventually hround
  filter_upwards [hmargin, hround, hroundshift,
    count_bound_polynomial_capacities hd P hP hL h hpos (countAlpha d)] with n hm hq hr hcap
  intro r f g e hrlo hrhi htotal hemin
  obtain ⟨hqlo, hqhi⟩ := hq (upperCount n d) (lowerCount_le_upperCount n d) le_rfl
  obtain ⟨_, hrhi'⟩ := hr r hrlo hrhi
  have htotal' : (upperCount n d : ℝ) + (f : ℝ) + (g : ℝ) + (e : ℝ) = r := by exact_mod_cast htotal
  have hF : (f : ℝ) ≤ (outerCountBoundPolynomial P d h (countAlpha d)).eval (n : ℝ) := by
    simp only [outerCountBoundPolynomial, eval_sub, eval_add, eval_C, eval_monomial, taylor_eval]
    rw [Nat.cast_add] at hrhi'
    have hg : (0 : ℝ) ≤ g := Nat.cast_nonneg g
    linarith
  have hs := slack_lower_bound
    (((n + (2 * d - 1) - 1).choose (2 * d - 1) : ℝ))
    (((n + (d - 1) - 1).choose (d - 1) : ℝ)) (((n + d - 1).choose d : ℝ))
    (upperCount n d) f (P.eval (n : ℝ) + 2)
    ((outerCountBoundPolynomial P d h (countAlpha d)).eval (n : ℝ)) h
    (hF.trans hcap.2) hqhi.le hF hcap.1
  simp only [transferSlackPolynomial, eval_sub, eval_mul, eval_add, eval_C,
    monomialCountPolynomial_eval] at hm
  exact hm.trans_le (by simpa only [mul_assoc] using hs)

end Froberg
