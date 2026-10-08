import Froberg.CriticalApproximation
import Froberg.CriticalRatioBounds
import Froberg.PolynomialCoefficients

/-! The second coefficient in the critical-root expansion, obtained from
the exact low-degree residual of its polynomial approximation. -/
noncomputable section
namespace Froberg
open Polynomial Filter
open scoped Topology

theorem criticalCenterPolynomial_subleading {d : ℕ} (hd : 2 ≤ d) :
    (criticalCenterPolynomial d).coeff (d - 1) =
      (d : ℝ) * ((d : ℝ) - 1) / (2 * (d.factorial : ℝ)) := by
  rw [criticalCenterPolynomial, coeff_add,
    monomialCountPolynomial_subleading d (by omega), coeff_C]
  simp [show d - 1 ≠ 0 by omega]

theorem critical_residual_subleading {d : ℕ} (hd : 2 ≤ d)
    (P : Polynomial ℝ) (hP : P.natDegree = d)
    (hR : (P ^ 2 - C 2 * criticalCenterPolynomial d * P +
      C 2 * monomialCountPolynomial (2 * d)).degree < (d : WithBot ℕ)) :
    P.coeff (d - 1) * ((d.factorial : ℝ)⁻¹ - P.leadingCoeff) =
      (d : ℝ) * (2 * (d : ℝ) - 1) / ((2 * d).factorial : ℝ) -
      (d : ℝ) * ((d : ℝ) - 1) / (2 * (d.factorial : ℝ)) * P.leadingCoeff := by
  have hz : (P ^ 2 - C 2 * criticalCenterPolynomial d * P +
      C 2 * monomialCountPolynomial (2 * d)).coeff (2 * d - 1) = 0 :=
    coeff_eq_zero_of_degree_lt (hR.trans_le (by exact_mod_cast (show d ≤ 2 * d - 1 by omega)))
  have hPP := product_second_coefficient P P (d - 1) (d - 1)
    (by omega) (by omega)
  obtain ⟨hCdeg, hClead⟩ := criticalCenterPolynomial_degree_and_lead (by omega : 0 < d)
  have hCP := product_second_coefficient (criticalCenterPolynomial d) P (d - 1) (d - 1)
    (by omega) (by omega)
  have hi : d - 1 + (d - 1) + 1 = 2 * d - 1 := by omega
  have hj : d - 1 + 1 = d := by omega
  have hpcoeff : P.coeff d = P.leadingCoeff := by rw [← hP, coeff_natDegree]
  have hccoeff : (criticalCenterPolynomial d).coeff d = (d.factorial : ℝ)⁻¹ := by
    calc
      _ = (criticalCenterPolynomial d).leadingCoeff := by
        simpa only [hCdeg] using (coeff_natDegree (p := criticalCenterPolynomial d))
      _ = _ := hClead
  rw [hi, hj, hpcoeff] at hPP
  rw [hi, hj, hpcoeff, hccoeff, criticalCenterPolynomial_subleading hd] at hCP
  rw [coeff_add, coeff_sub, pow_two, mul_assoc, coeff_C_mul,
    hPP, hCP, coeff_C_mul, monomialCountPolynomial_subleading (2 * d) (by omega)] at hz
  push_cast at hz
  linear_combination -(1 / 2 : ℝ) * hz

def criticalSubleadingCoefficient (d : ℕ) : ℝ :=
  ((d.factorial : ℝ) * d * (2 * (d : ℝ) - 1) / ((2 * d).factorial : ℝ) -
    criticalRatio d * d * ((d : ℝ) - 1) / (2 * (d.factorial : ℝ))) /
      (1 - criticalRatio d)

theorem critical_subleading_eq {d : ℕ} (hd : 2 ≤ d)
    (P : Polynomial ℝ) (hP : P.natDegree = d)
    (hL : P.leadingCoeff = criticalRatio d / (d.factorial : ℝ))
    (hR : (P ^ 2 - C 2 * criticalCenterPolynomial d * P +
      C 2 * monomialCountPolynomial (2 * d)).degree < (d : WithBot ℕ)) :
    P.coeff (d - 1) = criticalSubleadingCoefficient d := by
  have h := critical_residual_subleading hd P hP hR
  rw [hL] at h
  have hf : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have h2f : ((2 * d).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * d)
  have hr : 1 - criticalRatio d ≠ 0 := (sub_pos.mpr (criticalRatio_bounds hd).2.1).ne'
  unfold criticalSubleadingCoefficient
  field_simp at h ⊢
  nlinarith

end Froberg
