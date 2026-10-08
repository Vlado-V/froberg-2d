import Froberg.PolynomialAsymptotics
import Froberg.BinomialPolynomial

/-! The two highest coefficients of the counting polynomials and their products. -/
noncomputable section
namespace Froberg
open Polynomial

theorem product_second_coefficient (P Q : Polynomial ℝ) (a b : ℕ)
    (hP : P.natDegree ≤ a + 1) (hQ : Q.natDegree ≤ b + 1) :
    (P * Q).coeff (a + b + 1) =
      P.coeff (a + 1) * Q.coeff b + P.coeff a * Q.coeff (b + 1) := by
  classical
  rw [coeff_mul]
  let S : Finset (ℕ × ℕ) := {(a + 1, b), (a, b + 1)}
  have hS : S ⊆ Finset.antidiagonal (a + b + 1) := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [Finset.mem_antidiagonal] <;> omega
  have hsum := Finset.sum_subset hS (f := fun x => P.coeff x.1 * Q.coeff x.2)
    (by
      rintro ⟨i, j⟩ hij hnot
      have hs : i + j = a + b + 1 := Finset.mem_antidiagonal.mp hij
      by_cases hi : a + 1 < i
      · rw [coeff_eq_zero_of_natDegree_lt (hP.trans_lt hi), zero_mul]
      by_cases hj : b + 1 < j
      · rw [coeff_eq_zero_of_natDegree_lt (hQ.trans_lt hj), mul_zero]
      simp only [S, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or] at hnot
      omega)
  rw [← hsum]
  simp [S]

theorem ascPochhammer_next_coefficient (d : ℕ) :
    (ascPochhammer ℝ d).nextCoeff = (d : ℝ) * ((d : ℝ) - 1) / 2 := by
  induction d with
  | zero => simpa using nextCoeff_C_eq_zero (1 : ℝ)
  | succ d ih =>
      rw [ascPochhammer_succ_right]
      have hC : (d : Polynomial ℝ) = C (d : ℝ) := by simp
      rw [hC, (monic_ascPochhammer ℝ d).nextCoeff_mul (monic_X_add_C (d : ℝ)),
        nextCoeff_X_add_C, ih]
      push_cast
      ring

theorem monomialCountPolynomial_subleading (d : ℕ) (hd : 0 < d) :
    (monomialCountPolynomial d).coeff (d - 1) =
      (d : ℝ) * ((d : ℝ) - 1) / (2 * (d.factorial : ℝ)) := by
  have hnext := nextCoeff_of_natDegree_pos
    (p := monomialCountPolynomial d) (by rwa [monomialCountPolynomial_natDegree])
  rw [monomialCountPolynomial_natDegree] at hnext
  rw [← hnext, monomialCountPolynomial, nextCoeff_C_mul, ascPochhammer_next_coefficient]
  ring

end Froberg
