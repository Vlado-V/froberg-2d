import Froberg.SqrtApproximation
import Froberg.CriticalRoot
import Froberg.MonomialCounts
import Froberg.BinomialPolynomial

/-! A genuine polynomial approximating the manuscript's critical generator
count, with irrational leading coefficient and additive error tending to zero. -/

noncomputable section
namespace Froberg
open Polynomial Filter
open scoped Topology

/-- The affine shift appearing before the radical in the critical count. -/
def criticalCenterPolynomial (d : ℕ) : Polynomial ℝ :=
  monomialCountPolynomial d + C (1 / 2)

/-- The polynomial underneath the radical in the critical count. -/
def criticalDiscriminantPolynomial (d : ℕ) : Polynomial ℝ :=
  criticalCenterPolynomial d ^ 2 - C 2 * monomialCountPolynomial (2 * d)

private theorem sub_polynomial_degree_and_lead (A B : Polynomial ℝ) (m : ℕ)
    (hA : A.natDegree = m) (hB : B.natDegree = m)
    (hne : A.leadingCoeff - B.leadingCoeff ≠ 0) :
    (A - B).natDegree = m ∧
      (A - B).leadingCoeff = A.leadingCoeff - B.leadingCoeff := by
  have hcoeff : (A - B).coeff m = A.leadingCoeff - B.leadingCoeff := by
    rw [coeff_sub, ← hA, coeff_natDegree, hA, ← hB, coeff_natDegree]
  have hbound : (A - B).natDegree ≤ m := by
    simpa only [hA, hB, max_self] using natDegree_sub_le A B
  have hdeg := natDegree_eq_of_le_of_coeff_ne_zero hbound (hcoeff ▸ hne)
  refine ⟨hdeg, ?_⟩
  change (A - B).coeff (A - B).natDegree = _
  rw [hdeg, hcoeff]

theorem criticalCenterPolynomial_degree_and_lead {d : ℕ} (hd : 0 < d) :
    (criticalCenterPolynomial d).natDegree = d ∧
      (criticalCenterPolynomial d).leadingCoeff = (d.factorial : ℝ)⁻¹ := by
  have hdegree : (monomialCountPolynomial d).degree = d :=
    (degree_eq_iff_natDegree_eq_of_pos hd).mpr (monomialCountPolynomial_natDegree d)
  have hlt : (C (1 / 2 : ℝ)).degree < (monomialCountPolynomial d).degree := by
    rw [hdegree]
    exact degree_C_le.trans_lt (by exact_mod_cast hd)
  refine ⟨?_, ?_⟩
  · exact (natDegree_add_eq_left_of_degree_lt hlt).trans (monomialCountPolynomial_natDegree d)
  · exact (leadingCoeff_add_of_degree_lt' hlt).trans (monomialCountPolynomial_leadingCoeff d)

theorem criticalDiscriminant_leading_positive {d : ℕ} (hd : 2 ≤ d) :
    0 < (d.factorial : ℝ)⁻¹ ^ 2 - 2 * ((2 * d).factorial : ℝ)⁻¹ := by
  rw [factorial_discriminant_identity (by omega : 0 < d)]
  have hH : 1 < (centralHalfBinomial d : ℝ) := by
    exact_mod_cast (show 1 < centralHalfBinomial d from lt_of_lt_of_le (by omega) (centralHalfBinomial_ge_two hd))
  have hnorm : 0 < 1 - 1 / (centralHalfBinomial d : ℝ) := by
    have hdiv := (div_lt_one (by linarith : 0 < (centralHalfBinomial d : ℝ))).mpr hH
    linarith
  have hfac : 0 < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
  exact mul_pos (sq_pos_of_pos (inv_pos.mpr hfac)) hnorm

theorem criticalDiscriminantPolynomial_degree_and_lead {d : ℕ} (hd : 2 ≤ d) :
    (criticalDiscriminantPolynomial d).natDegree = 2 * d ∧
      (criticalDiscriminantPolynomial d).leadingCoeff =
        (d.factorial : ℝ)⁻¹ ^ 2 - 2 * ((2 * d).factorial : ℝ)⁻¹ := by
  obtain ⟨hCdeg, hClead⟩ := criticalCenterPolynomial_degree_and_lead (by omega : 0 < d)
  have hA : (criticalCenterPolynomial d ^ 2).natDegree = 2 * d := by
    rw [natDegree_pow, hCdeg]
  have hB : (C (2 : ℝ) * monomialCountPolynomial (2 * d)).natDegree = 2 * d := by
    rw [natDegree_C_mul (by norm_num : (2 : ℝ) ≠ 0), monomialCountPolynomial_natDegree]
  have hdiff : (criticalCenterPolynomial d ^ 2).leadingCoeff -
      (C (2 : ℝ) * monomialCountPolynomial (2 * d)).leadingCoeff =
      (d.factorial : ℝ)⁻¹ ^ 2 - 2 * ((2 * d).factorial : ℝ)⁻¹ := by
    rw [leadingCoeff_pow, hClead, leadingCoeff_mul, leadingCoeff_C,
      monomialCountPolynomial_leadingCoeff]
  obtain ⟨hdeg, hlead⟩ := sub_polynomial_degree_and_lead _ _ (2 * d) hA hB
    (by rw [hdiff]; exact (criticalDiscriminant_leading_positive hd).ne')
  exact ⟨hdeg, hlead.trans hdiff⟩

theorem criticalDiscriminantPolynomial_eval (d n : ℕ) :
    (criticalDiscriminantPolynomial d).eval (n : ℝ) =
      (((n + d - 1).choose d : ℝ) + 1 / 2) ^ 2 -
        2 * ((n + 2 * d - 1).choose (2 * d) : ℝ) := by
  simp only [criticalDiscriminantPolynomial, criticalCenterPolynomial, eval_sub,
    eval_pow, eval_add, eval_C, eval_mul, monomialCountPolynomial_eval]

theorem criticalDiscriminant_sqrt_lead {d : ℕ} (hd : 2 ≤ d) :
    Real.sqrt (criticalDiscriminantPolynomial d).leadingCoeff =
      (d.factorial : ℝ)⁻¹ * Real.sqrt (1 - 1 / (centralHalfBinomial d : ℝ)) := by
  rw [(criticalDiscriminantPolynomial_degree_and_lead hd).2,
    factorial_discriminant_identity (by omega : 0 < d), Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (by positivity)]

/-- The critical count has a degree-`d` polynomial approximation with exactly
the irrational leading coefficient asserted by the manuscript. -/
theorem exists_critical_polynomial_with_residual {d : ℕ} (hd : 2 ≤ d) :
    ∃ P : Polynomial ℝ, P.natDegree = d ∧
      P.leadingCoeff =
        (1 - Real.sqrt (1 - 1 / (centralHalfBinomial d : ℝ))) / (d.factorial : ℝ) ∧
      Irrational P.leadingCoeff ∧
      Tendsto (fun n : ℕ => kappa n d - P.eval (n : ℝ)) atTop (𝓝 0) ∧
      (P ^ 2 - C 2 * criticalCenterPolynomial d * P +
        C 2 * monomialCountPolynomial (2 * d)).degree < (d : WithBot ℕ) := by
  obtain ⟨hDdeg, hDlead⟩ := criticalDiscriminantPolynomial_degree_and_lead hd
  have hDpositive : 0 < (criticalDiscriminantPolynomial d).leadingCoeff := by
    rw [hDlead]
    exact criticalDiscriminant_leading_positive hd
  obtain ⟨Q, hQdegree, hQlead, hQerror⟩ := exists_polynomial_square_approximation
    (criticalDiscriminantPolynomial d) d hDdeg hDpositive
  have hQdeg : Q.natDegree = d := natDegree_eq_of_degree_eq_some hQdegree
  have hQlimit := sqrt_sub_polynomial_nat_tendsto_zero
    (criticalDiscriminantPolynomial d) Q
      (by rw [hQdegree]; exact_mod_cast (show 0 < d by omega))
      (by rw [hQlead]; exact Real.sqrt_pos.mpr hDpositive)
      (by rwa [hQdegree])
  obtain ⟨hCdeg, hClead⟩ := criticalCenterPolynomial_degree_and_lead (by omega : 0 < d)
  have hdiff : (criticalCenterPolynomial d).leadingCoeff - Q.leadingCoeff =
      (1 - Real.sqrt (1 - 1 / (centralHalfBinomial d : ℝ))) / (d.factorial : ℝ) := by
    rw [hClead, hQlead, criticalDiscriminant_sqrt_lead hd]
    ring
  have hirr : Irrational ((criticalCenterPolynomial d).leadingCoeff - Q.leadingCoeff) := by
    rw [hdiff]
    exact irrational_critical_leadingCoeff (centralHalfBinomial_ge_two hd) d
  obtain ⟨hPdeg, hPlead⟩ := sub_polynomial_degree_and_lead _ _ d hCdeg hQdeg hirr.ne_zero
  refine ⟨criticalCenterPolynomial d - Q, hPdeg, hPlead.trans hdiff, ?_, ?_, ?_⟩
  · rwa [hPlead]
  · have heq : (fun n : ℕ => kappa n d - (criticalCenterPolynomial d - Q).eval (n : ℝ)) =
        fun n : ℕ => -(Real.sqrt ((criticalDiscriminantPolynomial d).eval (n : ℝ)) - Q.eval (n : ℝ)) := by
      funext n
      simp only [kappa, criticalRoot, eval_sub, criticalCenterPolynomial,
        eval_add, eval_C, monomialCountPolynomial_eval, criticalDiscriminantPolynomial_eval]
      ring
    rw [heq]
    simpa only [neg_zero] using hQlimit.neg
  · have hidentity :
        (criticalCenterPolynomial d - Q) ^ 2 -
          C 2 * criticalCenterPolynomial d * (criticalCenterPolynomial d - Q) +
          C 2 * monomialCountPolynomial (2 * d) =
        -(criticalDiscriminantPolynomial d - Q ^ 2) := by
      unfold criticalDiscriminantPolynomial
      simp only [C_ofNat]
      ring
    rw [hidentity, degree_neg]
    exact hQerror

/-- The additive approximation, with its irrational leading coefficient. -/
theorem exists_critical_polynomial_approximation {d : ℕ} (hd : 2 ≤ d) :
    ∃ P : Polynomial ℝ, P.natDegree = d ∧
      P.leadingCoeff =
        (1 - Real.sqrt (1 - 1 / (centralHalfBinomial d : ℝ))) / (d.factorial : ℝ) ∧
      Irrational P.leadingCoeff ∧
      Tendsto (fun n : ℕ => kappa n d - P.eval (n : ℝ)) atTop (𝓝 0) := by
  obtain ⟨P, hdeg, hlead, hirr, hlimit, _⟩ := exists_critical_polynomial_with_residual hd
  exact ⟨P, hdeg, hlead, hirr, hlimit⟩

end Froberg
