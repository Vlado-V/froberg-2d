module

public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-! Polynomial approximation to a square root at positive infinity. -/

namespace Froberg
open Polynomial Filter
open scoped Topology

/-- Rationalization bounds a square-root error by the relative squared error. -/
theorem abs_sqrt_sub_le_relative_square_error (x y : ℝ) (hy : 0 < y) :
    |Real.sqrt x - y| ≤ |(x - y ^ 2) / y| := by
  by_cases hx : 0 ≤ x
  · have hs := Real.sq_sqrt hx
    have hs0 := Real.sqrt_nonneg x
    have hden : 0 < Real.sqrt x + y := by linarith
    have hid : Real.sqrt x - y = (x - y ^ 2) / (Real.sqrt x + y) := by
      apply (eq_div_iff hden.ne').mpr
      nlinarith
    rw [hid, abs_div, abs_of_pos hden, abs_div, abs_of_pos hy]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hy (by linarith)
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hneg : x - y ^ 2 < 0 := by nlinarith [sq_nonneg y]
    rw [Real.sqrt_eq_zero_of_nonpos hxneg.le, zero_sub, abs_neg, abs_of_pos hy,
      abs_div, abs_of_neg hneg, abs_of_pos hy]
    apply (le_div_iff₀ hy).mpr
    nlinarith

/-- Cancelling all terms of degree at least `deg Q` in the squared error is
sufficient for an additive square-root approximation tending to zero. -/
theorem sqrt_sub_polynomial_tendsto_zero (P Q : Polynomial ℝ)
    (hQdeg : 0 < Q.degree) (hQlead : 0 < Q.leadingCoeff)
    (herror : (P - Q ^ 2).degree < Q.degree) :
    Tendsto (fun x : ℝ => Real.sqrt (P.eval x) - Q.eval x) atTop (𝓝 0) := by
  have hratio := (P - Q ^ 2).div_tendsto_atTop_zero_of_degree_lt Q herror
  have hpositive : ∀ᶠ x : ℝ in atTop, 0 < Q.eval x :=
    (Q.tendsto_atTop_of_leadingCoeff_nonneg hQdeg hQlead.le).eventually_gt_atTop 0
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (hpositive.mono fun x hx => ?_) (by simpa using hratio.norm)
  simpa only [Real.norm_eq_abs, eval_sub, eval_pow, abs_div] using
    abs_sqrt_sub_le_relative_square_error (P.eval x) (Q.eval x) hx

/-- The same approximation evaluated at natural numbers. -/
theorem sqrt_sub_polynomial_nat_tendsto_zero (P Q : Polynomial ℝ)
    (hQdeg : 0 < Q.degree) (hQlead : 0 < Q.leadingCoeff)
    (herror : (P - Q ^ 2).degree < Q.degree) :
    Tendsto (fun n : ℕ => Real.sqrt (P.eval (n : ℝ)) - Q.eval (n : ℝ)) atTop (𝓝 0) :=
  (sqrt_sub_polynomial_tendsto_zero P Q hQdeg hQlead herror).comp tendsto_natCast_atTop_atTop

/-- One descending coefficient cancellation in the polynomial square root. -/
theorem improve_square_approximation (P Q : Polynomial ℝ) (d k : ℕ) (a : ℝ)
    (ha : a ≠ 0) (hk : k < d) (hQdeg : Q.degree = d) (hQlead : Q.leadingCoeff = a)
    (herror : (P - Q ^ 2).degree < (d + k + 1 : ℕ)) :
    ∃ Q' : Polynomial ℝ, Q'.degree = d ∧ Q'.leadingCoeff = a ∧
      (P - Q' ^ 2).degree < (d + k : ℕ) := by
  let c : ℝ := (P - Q ^ 2).coeff (d + k) / (2 * a)
  let u : Polynomial ℝ := monomial k c
  have hudeg : u.degree < Q.degree := by
    rw [hQdeg]
    exact (degree_monomial_le k c).trans_lt (by exact_mod_cast hk)
  refine ⟨Q + u, (degree_add_eq_left_of_degree_lt hudeg).trans hQdeg,
    (leadingCoeff_add_of_degree_lt' hudeg).trans hQlead, ?_⟩
  have hidentity : P - (Q + u) ^ 2 = (P - Q ^ 2) - C 2 * (Q * u) - u ^ 2 := by
    rw [C_ofNat]
    ring
  rw [hidentity, degree_lt_iff_coeff_zero]
  intro n hn
  have hnk : k ≤ n := by omega
  have hnrepr : n = (n - k) + k := by omega
  have hquad : (u ^ 2).coeff n = 0 := by
    dsimp [u]
    rw [monomial_pow, coeff_monomial]
    have hneq : k * 2 ≠ n := by omega
    simp [hneq]
  have hlinear : (C 2 * (Q * u)).coeff n = 2 * Q.coeff (n - k) * c := by
    rw [coeff_C_mul]
    dsimp [u]
    conv_lhs => arg 2; rw [hnrepr]
    rw [coeff_mul_monomial]
    ring
  rw [coeff_sub, coeff_sub, hquad, hlinear, sub_zero]
  by_cases heq : n = d + k
  · subst n
    have hQnat : Q.natDegree = d := natDegree_eq_of_degree_eq_some hQdeg
    have hQcoeff : Q.coeff d = a := by rw [← hQnat, coeff_natDegree, hQlead]
    rw [Nat.add_sub_cancel, hQcoeff]
    dsimp [c]
    field_simp
    ring
  · have hlt : d + k + 1 ≤ n := by omega
    have hRcoeff : (P - Q ^ 2).coeff n = 0 :=
      (degree_lt_iff_coeff_zero _ _).mp herror n hlt
    have hQcoeff : Q.coeff (n - k) = 0 := by
      apply coeff_eq_zero_of_degree_lt
      rw [hQdeg]
      exact_mod_cast (show d < n - k by omega)
    rw [hRcoeff, hQcoeff]
    ring

/-- Repeated coefficient cancellation reaches a remainder smaller than the
approximating polynomial. -/
theorem finish_square_approximation (P : Polynomial ℝ) (d : ℕ) (a : ℝ)
    (ha : a ≠ 0) :
    ∀ k : ℕ, k ≤ d → ∀ Q : Polynomial ℝ, Q.degree = d → Q.leadingCoeff = a →
      (P - Q ^ 2).degree < (d + k : ℕ) →
      ∃ Q' : Polynomial ℝ, Q'.degree = d ∧ Q'.leadingCoeff = a ∧
        (P - Q' ^ 2).degree < d := by
  intro k
  induction k with
  | zero =>
      intro _ Q hQdeg hQlead herror
      exact ⟨Q, hQdeg, hQlead, by simpa using herror⟩
  | succ k ih =>
      intro hk Q hQdeg hQlead herror
      obtain ⟨Q', hQ'deg, hQ'lead, herror'⟩ :=
        improve_square_approximation P Q d k a ha (by omega) hQdeg hQlead
          (by simpa [Nat.add_assoc] using herror)
      exact ih (by omega) Q' hQ'deg hQ'lead herror'

/-- Every polynomial of even degree and positive leading coefficient has a
polynomial square root up to a remainder of degree less than half its degree. -/
theorem exists_polynomial_square_approximation (P : Polynomial ℝ) (d : ℕ)
    (hPdeg : P.natDegree = 2 * d) (hPlead : 0 < P.leadingCoeff) :
    ∃ Q : Polynomial ℝ, Q.degree = d ∧ Q.leadingCoeff = Real.sqrt P.leadingCoeff ∧
      (P - Q ^ 2).degree < d := by
  let a : ℝ := Real.sqrt P.leadingCoeff
  have ha : 0 < a := Real.sqrt_pos.2 hPlead
  have hPzero : P ≠ 0 := by
    intro h
    simp [h] at hPlead
  have hPdegree : P.degree = (2 * d : ℕ) := by
    rw [degree_eq_natDegree hPzero, hPdeg]
  let Q : Polynomial ℝ := monomial d a
  have hQdeg : Q.degree = d := degree_monomial d ha.ne'
  have hQlead : Q.leadingCoeff = a := leadingCoeff_monomial a d
  have hsquare : (Q ^ 2).degree = P.degree := by
    rw [pow_two, degree_mul, hQdeg, hPdegree]
    norm_cast
    omega
  have hleading : P.leadingCoeff = (Q ^ 2).leadingCoeff := by
    rw [leadingCoeff_pow, hQlead]
    exact (Real.sq_sqrt hPlead.le).symm
  have herror : (P - Q ^ 2).degree < (d + d : ℕ) := by
    have h := degree_sub_lt_left hsquare.symm hPzero hleading
    simpa [hPdegree, two_mul] using h
  exact finish_square_approximation P d a ha.ne' d le_rfl Q hQdeg hQlead herror

/-- A positive-leading polynomial of positive even degree admits a degree-half
polynomial approximation to its square root with error tending to zero. -/
theorem exists_polynomial_sqrt_approximation (P : Polynomial ℝ) (d : ℕ)
    (hd : 0 < d) (hPdeg : P.natDegree = 2 * d) (hPlead : 0 < P.leadingCoeff) :
    ∃ Q : Polynomial ℝ, Q.natDegree = d ∧ Q.leadingCoeff = Real.sqrt P.leadingCoeff ∧
      Tendsto (fun x : ℝ => Real.sqrt (P.eval x) - Q.eval x) atTop (𝓝 0) := by
  obtain ⟨Q, hQdeg, hQlead, herror⟩ :=
    exists_polynomial_square_approximation P d hPdeg hPlead
  refine ⟨Q, natDegree_eq_of_degree_eq_some hQdeg, hQlead, ?_⟩
  apply sqrt_sub_polynomial_tendsto_zero P Q
  · rw [hQdeg]
    exact_mod_cast hd
  · rw [hQlead]
    exact Real.sqrt_pos.2 hPlead
  · rwa [hQdeg]

/-- The square-root polynomial approximation along natural-number arguments,
with its exact degree and leading coefficient retained. -/
theorem exists_polynomial_sqrt_nat_approximation (P : Polynomial ℝ) (d : ℕ)
    (hd : 0 < d) (hPdeg : P.natDegree = 2 * d) (hPlead : 0 < P.leadingCoeff) :
    ∃ Q : Polynomial ℝ, Q.natDegree = d ∧ Q.leadingCoeff = Real.sqrt P.leadingCoeff ∧
      Tendsto (fun n : ℕ => Real.sqrt (P.eval (n : ℝ)) - Q.eval (n : ℝ)) atTop (𝓝 0) := by
  obtain ⟨Q, hQdeg, hQlead, hlimit⟩ := exists_polynomial_sqrt_approximation P d hd hPdeg hPlead
  exact ⟨Q, hQdeg, hQlead, hlimit.comp tendsto_natCast_atTop_atTop⟩

end Froberg
