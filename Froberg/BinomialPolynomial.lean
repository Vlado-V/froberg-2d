module

public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic

@[expose] public section

/-! Polynomial interpolation of homogeneous monomial counts and factorial
identities for the critical-root leading coefficient. -/

noncomputable section
namespace Froberg
open Polynomial

/-- The polynomial `x(x+1)…(x+d−1)/d!`. -/
def monomialCountPolynomial (d : ℕ) : Polynomial ℝ :=
  C ((d.factorial : ℝ)⁻¹) * ascPochhammer ℝ d

theorem monomialCountPolynomial_natDegree (d : ℕ) :
    (monomialCountPolynomial d).natDegree = d := by
  rw [monomialCountPolynomial, natDegree_C_mul, ascPochhammer_natDegree]
  exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero d)

theorem monomialCountPolynomial_leadingCoeff (d : ℕ) :
    (monomialCountPolynomial d).leadingCoeff = (d.factorial : ℝ)⁻¹ := by
  simp [monomialCountPolynomial, leadingCoeff_mul, (monic_ascPochhammer ℝ d).leadingCoeff]

theorem monomialCountPolynomial_eval (d n : ℕ) :
    (monomialCountPolynomial d).eval (n : ℝ) = ((n + d - 1).choose d : ℝ) := by
  rw [monomialCountPolynomial, eval_mul, eval_C,
    ascPochhammer_nat_eq_natCast_ascFactorial, Nat.ascFactorial_eq_factorial_mul_choose']
  push_cast
  have hfac : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  field_simp

/-- The integer denoted `H` in the critical-root formula. -/
def centralHalfBinomial (d : ℕ) : ℕ := (2 * d - 1).choose (d - 1)

theorem centralHalfBinomial_ge_two {d : ℕ} (hd : 2 ≤ d) :
    2 ≤ centralHalfBinomial d := by
  have hp : 0 < (2 * d - 1).choose (d - 1) := Nat.choose_pos (by omega)
  have hne : (2 * d - 1).choose (d - 1) ≠ 1 := by
    intro he
    have := Nat.choose_eq_one_iff.mp he
    omega
  unfold centralHalfBinomial
  omega

theorem centralBinomial_eq_twice_half {d : ℕ} (hd : 0 < d) :
    (2 * d).choose d = 2 * centralHalfBinomial d := by
  have hp := Nat.choose_succ_succ (2 * d - 1) (d - 1)
  have htop : 2 * d - 1 + 1 = 2 * d := by omega
  have hbot : d - 1 + 1 = d := by omega
  simp only [Nat.succ_eq_add_one, htop, hbot] at hp
  have hsym : (2 * d - 1).choose d = (2 * d - 1).choose (d - 1) :=
    Nat.choose_symm_of_eq_add (by omega)
  rw [hsym] at hp
  simpa only [centralHalfBinomial, two_mul] using hp

theorem factorial_twice_degree {d : ℕ} (hd : 0 < d) :
    (2 * d).factorial = 2 * centralHalfBinomial d * d.factorial ^ 2 := by
  have h := Nat.choose_mul_factorial_mul_factorial (show d ≤ 2 * d by omega)
  rw [show 2 * d - d = d by omega, centralBinomial_eq_twice_half hd] at h
  nlinarith

/-- The normalized leading coefficient of the square-root discriminant. -/
theorem factorial_discriminant_identity {d : ℕ} (hd : 0 < d) :
    (d.factorial : ℝ)⁻¹ ^ 2 - 2 * ((2 * d).factorial : ℝ)⁻¹ =
      (d.factorial : ℝ)⁻¹ ^ 2 * (1 - 1 / (centralHalfBinomial d : ℝ)) := by
  have hfac : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have hhalf : centralHalfBinomial d ≠ 0 :=
    Nat.ne_of_gt (Nat.choose_pos (by omega))
  have hhalfr : (centralHalfBinomial d : ℝ) ≠ 0 := by exact_mod_cast hhalf
  rw [factorial_twice_degree hd]
  push_cast
  field_simp

end Froberg
