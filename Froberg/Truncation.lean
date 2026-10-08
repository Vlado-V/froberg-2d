import Froberg.HilbertSeries
import Froberg.CriticalApproximation

/-! Positive truncation at the endpoint in sufficiently many variables. -/

noncomputable section
namespace Froberg
open Polynomial Filter
open scoped Topology

/-- The critical leading ratio lies strictly between zero and `1/H`. -/
theorem critical_ratio_bounds {H : ℕ} (hH : 2 ≤ H) :
    0 < 1 - Real.sqrt (1 - 1 / (H : ℝ)) ∧
      1 - Real.sqrt (1 - 1 / (H : ℝ)) < 1 / (H : ℝ) := by
  have hHr : 1 < (H : ℝ) := by exact_mod_cast (show 1 < H by omega)
  have hHpos : 0 < (H : ℝ) := by linarith
  have hfrac : 0 < 1 / (H : ℝ) := by positivity
  have hfrac1 : 1 / (H : ℝ) < 1 := (div_lt_one hHpos).mpr hHr
  have hs := Real.sq_sqrt (show 0 ≤ 1 - 1 / (H : ℝ) by linarith)
  have hs0 := Real.sqrt_nonneg (1 - 1 / (H : ℝ))
  have hs1 : Real.sqrt (1 - 1 / (H : ℝ)) < 1 := by nlinarith
  have hgt : 1 - 1 / (H : ℝ) < Real.sqrt (1 - 1 / (H : ℝ)) := by nlinarith
  constructor <;> linarith

/-- Every coefficient before degree `2*d` has a strictly positive leading
surplus at the critical generator scale. -/
theorem before_endpoint_leading_gap {d j : ℕ} (hd : 2 ≤ d)
    (hdj : d ≤ j) (hj : j < 2 * d) :
    0 < (j.factorial : ℝ)⁻¹ -
      ((1 - Real.sqrt (1 - 1 / (centralHalfBinomial d : ℝ))) / (d.factorial : ℝ)) *
        ((j - d).factorial : ℝ)⁻¹ := by
  let ρ : ℝ := 1 - Real.sqrt (1 - 1 / (centralHalfBinomial d : ℝ))
  have hρ := critical_ratio_bounds (centralHalfBinomial_ge_two hd)
  change 0 < ρ ∧ ρ < 1 / (centralHalfBinomial d : ℝ) at hρ
  have hHpos : 0 < (centralHalfBinomial d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (centralHalfBinomial_ge_two hd))
  have hρH : ρ * (centralHalfBinomial d : ℝ) < 1 := (lt_div_iff₀ hHpos).mp hρ.2
  have hchoose : j.choose d ≤ centralHalfBinomial d := by
    have hmono := Nat.choose_le_choose d (show j ≤ 2 * d - 1 by omega)
    have hsym : (2 * d - 1).choose d = centralHalfBinomial d :=
      Nat.choose_symm_of_eq_add (by omega)
    exact hmono.trans_eq hsym
  have hCpos : 0 < (j.choose d : ℝ) := by exact_mod_cast Nat.choose_pos hdj
  have hρC : ρ * (j.choose d : ℝ) < 1 :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hchoose) hρ.1.le).trans_lt hρH
  have hDpos : 0 < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
  have hEpos : 0 < ((j - d).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (j - d)
  have hfact : (j.factorial : ℝ) =
      (j.choose d : ℝ) * (d.factorial : ℝ) * ((j - d).factorial : ℝ) := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hdj).symm
  change 0 < (j.factorial : ℝ)⁻¹ - (ρ / (d.factorial : ℝ)) * ((j - d).factorial : ℝ)⁻¹
  apply sub_pos.mpr
  rw [hfact]
  calc
    (ρ / (d.factorial : ℝ)) * ((j - d).factorial : ℝ)⁻¹ =
        ρ / ((d.factorial : ℝ) * ((j - d).factorial : ℝ)) := by ring
    _ < ((j.choose d : ℝ) * (d.factorial : ℝ) * ((j - d).factorial : ℝ))⁻¹ := by
      rw [inv_eq_one_div]
      apply (div_lt_div_iff₀ (mul_pos hDpos hEpos) (mul_pos (mul_pos hCpos hDpos) hEpos)).mpr
      have h := mul_lt_mul_of_pos_right hρC (mul_pos hDpos hEpos)
      nlinarith

private theorem polynomial_difference_eventually_positive (A B : Polynomial ℝ) (j : ℕ)
    (hj : 0 < j) (hA : A.natDegree = j) (hB : B.natDegree = j)
    (hgap : 0 < A.leadingCoeff - B.leadingCoeff) :
    ∀ᶠ n : ℕ in atTop, 0 < A.eval (n : ℝ) - B.eval (n : ℝ) := by
  have hdegA : A.degree = j := (degree_eq_iff_natDegree_eq_of_pos hj).mpr hA
  have hdegB : B.degree = j := (degree_eq_iff_natDegree_eq_of_pos hj).mpr hB
  have hlead := leadingCoeff_sub_of_degree_eq (hdegA.trans hdegB.symm)
    (sub_ne_zero.mp hgap.ne')
  have hcoeff : (A - B).coeff j ≠ 0 := by
    rw [coeff_sub, ← hA, coeff_natDegree, hA, ← hB, coeff_natDegree]
    exact hgap.ne'
  have hdegree : 0 < (A - B).degree :=
    lt_of_lt_of_le (by exact_mod_cast hj) (le_degree_of_ne_zero hcoeff)
  have hpos : 0 < (A - B).leadingCoeff := by rwa [hlead]
  have hlim := ((A - B).tendsto_atTop_of_leadingCoeff_nonneg hdegree hpos.le).comp
    tendsto_natCast_atTop_atTop
  simpa only [Function.comp_apply, eval_sub] using hlim.eventually_gt_atTop 0

private theorem eventually_before_endpoint_positive_at_kappa_one
    {d j : ℕ} (hd : 2 ≤ d) (hdj : d ≤ j) (hj : j < 2 * d)
    (P : Polynomial ℝ) (hPdeg : P.natDegree = d)
    (hPlead : P.leadingCoeff =
      (1 - Real.sqrt (1 - 1 / (centralHalfBinomial d : ℝ))) / (d.factorial : ℝ))
    (hlimit : Tendsto (fun n : ℕ => kappa n d - P.eval (n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, 0 < ((n + j - 1).choose j : ℝ) -
      kappa n d * ((n + (j - d) - 1).choose (j - d) : ℝ) := by
  let P' := P + C (1 : ℝ)
  have hPlt : (C (1 : ℝ)).degree < P.degree := by
    rw [(degree_eq_iff_natDegree_eq_of_pos (by omega : 0 < d)).mpr hPdeg]
    exact degree_C_le.trans_lt (by exact_mod_cast (show 0 < d by omega))
  have hP'deg : P'.natDegree = d := (natDegree_add_eq_left_of_degree_lt hPlt).trans hPdeg
  have hP'lead : P'.leadingCoeff = P.leadingCoeff := leadingCoeff_add_of_degree_lt' hPlt
  have hPpositive : 0 < P.leadingCoeff := by
    rw [hPlead]
    exact div_pos (critical_ratio_bounds (centralHalfBinomial_ge_two hd)).1
      (by exact_mod_cast Nat.factorial_pos d)
  let B := P' * monomialCountPolynomial (j - d)
  have hBdeg : B.natDegree = j := by
    rw [natDegree_mul' (by
      rw [hP'lead, monomialCountPolynomial_leadingCoeff]
      exact mul_ne_zero hPpositive.ne' (inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (j - d)))),
      hP'deg, monomialCountPolynomial_natDegree]
    omega
  have hBlead : B.leadingCoeff = P.leadingCoeff * ((j - d).factorial : ℝ)⁻¹ := by
    dsimp only [B]
    rw [leadingCoeff_mul, hP'lead, monomialCountPolynomial_leadingCoeff]
  have hpoly := polynomial_difference_eventually_positive
    (monomialCountPolynomial j) B j (by omega) (monomialCountPolynomial_natDegree j) hBdeg
      (by rw [monomialCountPolynomial_leadingCoeff, hBlead, hPlead];
          exact before_endpoint_leading_gap hd hdj hj)
  have herr : ∀ᶠ n : ℕ in atTop, kappa n d - P.eval (n : ℝ) < 1 :=
    hlimit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hpoly, herr, eventually_gt_atTop (0 : ℕ)] with n hpoly herr hn
  have hcount : 0 < ((n + (j - d) - 1).choose (j - d) : ℝ) := by
    exact_mod_cast monomial_count_pos hn (j - d)
  have hmul := mul_lt_mul_of_pos_right
    (show kappa n d < P.eval (n : ℝ) + 1 by linarith) hcount
  dsimp only [B, P'] at hpoly
  simp only [eval_mul, eval_add, eval_C, monomialCountPolynomial_eval] at hpoly
  nlinarith

/-- In sufficiently many variables, all coefficients strictly before the
endpoint remain positive even at the real critical generator count. -/
theorem eventually_before_endpoint_positive_at_kappa {d : ℕ} (hd : 2 ≤ d) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, d ≤ j → j < 2 * d →
      0 < ((n + j - 1).choose j : ℝ) -
        kappa n d * ((n + (j - d) - 1).choose (j - d) : ℝ) := by
  obtain ⟨P, hPdeg, hPlead, _, hlimit⟩ := exists_critical_polynomial_approximation hd
  have hfinite : ∀ᶠ n : ℕ in atTop, ∀ j ∈ Finset.range (2 * d), d ≤ j →
      0 < ((n + j - 1).choose j : ℝ) -
        kappa n d * ((n + (j - d) - 1).choose (j - d) : ℝ) := by
    apply (eventually_all_finset (Finset.range (2 * d))).mpr
    intro j hj
    by_cases hdj : d ≤ j
    · exact (eventually_before_endpoint_positive_at_kappa_one hd hdj
        (Finset.mem_range.mp hj) P hPdeg hPlead hlimit).mono fun n h _ => h
    · exact Eventually.of_forall fun n h => False.elim (hdj h)
  exact hfinite.mono fun n h j hdj hj => h j (Finset.mem_range.mpr hj) hdj

/-- The positive truncation has exactly the untruncated positive-part endpoint
coefficient, for every generator count up to the dimension of degree-`d` forms. -/
theorem eventually_predictedHilbertFunction_endpoint {d : ℕ} (hd : 2 ≤ d) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, r ≤ (n + d - 1).choose d →
      predictedHilbertFunction n d r (2 * d) = expectedEndpoint n d r := by
  filter_upwards [eventually_before_endpoint_positive_at_kappa hd,
    eventually_gt_atTop (0 : ℕ)] with n hbefore hn
  intro r hr
  have hendpoint := predictionCoefficient_at_endpoint n d r hn (by omega)
  by_cases heuler : 0 < euler n d r
  · have hrroot : (r : ℝ) ≤ kappa n d :=
      (euler_nonneg_iff_kappa hn d r hr).mp heuler.le
    unfold predictedHilbertFunction
    rw [positiveTruncation_eq_of_positive]
    · rw [hendpoint]
      rfl
    · intro j hj
      by_cases heq : j = 2 * d
      · simpa only [heq, hendpoint] using heuler
      · have hjlt : j < 2 * d := by omega
        by_cases hjd : j < d
        · rw [predictionCoefficient_below_degree n d r j hn hjd]
          exact_mod_cast monomial_count_pos hn j
        · have hdj : d ≤ j := by omega
          rw [predictionCoefficient_before_endpoint n d r j hn hdj hjlt]
          have hg := hbefore j hdj hjlt
          have hmul := mul_le_mul_of_nonneg_right hrroot
            (Nat.cast_nonneg ((n + (j - d) - 1).choose (j - d)) :
              (0 : ℝ) ≤ ((n + (j - d) - 1).choose (j - d) : ℝ))
          have hpositive : 0 < ((n + j - 1).choose j : ℝ) -
              (r : ℝ) * ((n + (j - d) - 1).choose (j - d) : ℝ) := by linarith
          exact_mod_cast hpositive
  · have hnonpos : euler n d r ≤ 0 := le_of_not_gt heuler
    unfold predictedHilbertFunction expectedEndpoint
    rw [positiveTruncation_eq_zero (predictionCoefficient n d r) (2 * d) (2 * d)
      le_rfl (by rwa [hendpoint]), Int.toNat_of_nonpos hnonpos]

/-- The critical count is eventually below the last pre-endpoint multiplication
threshold, as stated in the manuscript's positive-truncation argument. -/
theorem eventually_kappa_lt_preEndpoint_ratio {d : ℕ} (hd : 2 ≤ d) :
    ∀ᶠ n : ℕ in atTop,
      kappa n d < ((n + (2 * d - 1) - 1).choose (2 * d - 1) : ℝ) /
        ((n + (d - 1) - 1).choose (d - 1) : ℝ) := by
  filter_upwards [eventually_before_endpoint_positive_at_kappa hd,
    eventually_gt_atTop (0 : ℕ)] with n h hn
  have hg := h (2 * d - 1) (by omega) (by omega)
  have hsub : 2 * d - 1 - d = d - 1 := by omega
  rw [hsub] at hg
  have hpos : 0 < ((n + (d - 1) - 1).choose (d - 1) : ℝ) := by
    exact_mod_cast monomial_count_pos hn (d - 1)
  exact (lt_div_iff₀ hpos).mpr (by linarith)

/-- An explicit existential threshold version of the endpoint truncation theorem. -/
theorem exists_endpoint_truncation_threshold {d : ℕ} (hd : 2 ≤ d) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ r : ℕ, r ≤ (n + d - 1).choose d →
      predictedHilbertFunction n d r (2 * d) = expectedEndpoint n d r :=
  eventually_atTop.mp (eventually_predictedHilbertFunction_endpoint hd)

end Froberg
