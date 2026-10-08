import Froberg.PolynomialCoefficients

/-! The exact polynomial whose positivity supplies the dimension margin
`T - q A` in the outer-module construction. -/
noncomputable section
namespace Froberg
open Polynomial

theorem monomialCountPolynomial_top (d : ℕ) :
    (monomialCountPolynomial d).coeff d = (d.factorial : ℝ)⁻¹ := by
  calc
    _ = (monomialCountPolynomial d).leadingCoeff := by
      simpa only [monomialCountPolynomial_natDegree] using
        (coeff_natDegree (p := monomialCountPolynomial d))
    _ = _ := monomialCountPolynomial_leadingCoeff d

def transferSlackPolynomial (d : ℕ) (P F : Polynomial ℝ) (h : ℝ) : Polynomial ℝ :=
  C h * monomialCountPolynomial (2 * d - 1) -
    C h * (P * monomialCountPolynomial (d - 1)) -
      F * (monomialCountPolynomial d - P)

theorem transferSlackPolynomial_degree {d : ℕ} (hd : 1 ≤ d)
    (P F : Polynomial ℝ) (h : ℝ) (hP : P.natDegree ≤ d) (hF : F.natDegree ≤ d - 1) :
    (transferSlackPolynomial d P F h).natDegree ≤ 2 * d - 1 := by
  have hD : (monomialCountPolynomial d - P).natDegree ≤ d :=
    (natDegree_sub_le _ _).trans (max_le (monomialCountPolynomial_natDegree d).le hP)
  have hPS : (P * monomialCountPolynomial (d - 1)).natDegree ≤ 2 * d - 1 := by
    have hh := natDegree_mul_le_of_le hP (monomialCountPolynomial_natDegree (d - 1)).le
    omega
  have hFD : (F * (monomialCountPolynomial d - P)).natDegree ≤ 2 * d - 1 := by
    have hh := natDegree_mul_le_of_le hF hD
    omega
  have hT := (natDegree_C_mul_le h (monomialCountPolynomial (2 * d - 1))).trans
    (monomialCountPolynomial_natDegree _).le
  have hQ := (natDegree_C_mul_le h (P * monomialCountPolynomial (d - 1))).trans hPS
  exact (natDegree_sub_le _ _).trans
    (max_le ((natDegree_sub_le _ _).trans (max_le hT hQ)) hFD)

theorem transferSlackPolynomial_top {d : ℕ} (hd : 1 ≤ d)
    (P F : Polynomial ℝ) (h : ℝ) (hP : P.natDegree ≤ d) (hF : F.natDegree ≤ d - 1) :
    (transferSlackPolynomial d P F h).coeff (2 * d - 1) =
      h / ((2 * d - 1).factorial : ℝ) -
        h * (P.coeff d / ((d - 1).factorial : ℝ)) -
        F.coeff (d - 1) * ((d.factorial : ℝ)⁻¹ - P.coeff d) := by
  have hD : (monomialCountPolynomial d - P).natDegree ≤ d :=
    (natDegree_sub_le _ _).trans (max_le (monomialCountPolynomial_natDegree d).le hP)
  have hPS := coeff_mul_add_eq_of_natDegree_le hP (monomialCountPolynomial_natDegree (d - 1)).le
  have hFD := coeff_mul_add_eq_of_natDegree_le hF hD
  rw [show d + (d - 1) = 2 * d - 1 by omega] at hPS
  rw [show d - 1 + d = 2 * d - 1 by omega] at hFD
  simp only [transferSlackPolynomial, coeff_sub, coeff_C_mul, hPS, hFD,
    monomialCountPolynomial_top]
  ring

theorem transferSlackPolynomial_second {d : ℕ} (hd : 2 ≤ d)
    (P F : Polynomial ℝ) (h : ℝ) (hP : P.natDegree ≤ d) (hF : F.natDegree ≤ d - 1) :
    (transferSlackPolynomial d P F h).coeff (2 * d - 2) =
      h * ((2 * (d : ℝ) - 1) * (2 * (d : ℝ) - 2) / (2 * ((2 * d - 1).factorial : ℝ))) -
      h * (P.coeff d * (((d : ℝ) - 1) * ((d : ℝ) - 2) / (2 * ((d - 1).factorial : ℝ))) +
        P.coeff (d - 1) / ((d - 1).factorial : ℝ)) -
      (F.coeff (d - 1) * ((d : ℝ) * ((d : ℝ) - 1) / (2 * (d.factorial : ℝ)) - P.coeff (d - 1)) +
        F.coeff (d - 2) * ((d.factorial : ℝ)⁻¹ - P.coeff d)) := by
  have hD : (monomialCountPolynomial d - P).natDegree ≤ d :=
    (natDegree_sub_le _ _).trans (max_le (monomialCountPolynomial_natDegree d).le hP)
  have hPS := product_second_coefficient P (monomialCountPolynomial (d - 1))
    (d - 1) (d - 2) (by omega) (by rw [monomialCountPolynomial_natDegree]; omega)
  have hFD := product_second_coefficient F (monomialCountPolynomial d - P)
    (d - 2) (d - 1) (by omega) (by omega)
  have h₁ : d - 1 + (d - 2) + 1 = 2 * d - 2 := by omega
  have h₂ : d - 2 + (d - 1) + 1 = 2 * d - 2 := by omega
  have h₃ : d - 1 + 1 = d := by omega
  have h₄ : d - 2 + 1 = d - 1 := by omega
  rw [h₁, h₃, h₄] at hPS
  rw [h₂, h₄, h₃] at hFD
  have hs : (monomialCountPolynomial (d - 1)).coeff (d - 2) =
      ((d : ℝ) - 1) * ((d : ℝ) - 2) / (2 * ((d - 1).factorial : ℝ)) := by
    have hh := monomialCountPolynomial_subleading (d - 1) (by omega)
    rw [show d - 1 - 1 = d - 2 by omega, Nat.cast_sub (by omega : 1 ≤ d)] at hh
    push_cast at hh
    convert hh using 1 <;> ring
  have ht : (monomialCountPolynomial (2 * d - 1)).coeff (2 * d - 2) =
      (2 * (d : ℝ) - 1) * (2 * (d : ℝ) - 2) / (2 * ((2 * d - 1).factorial : ℝ)) := by
    have hh := monomialCountPolynomial_subleading (2 * d - 1) (by omega)
    rw [show 2 * d - 1 - 1 = 2 * d - 2 by omega,
      Nat.cast_sub (by omega : 1 ≤ 2 * d)] at hh
    push_cast at hh
    convert hh using 1 <;> ring
  simp only [transferSlackPolynomial, coeff_sub, coeff_C_mul, hPS, hFD, hs, ht,
    monomialCountPolynomial_top, monomialCountPolynomial_subleading d (by omega : 0 < d)]
  ring

end Froberg
