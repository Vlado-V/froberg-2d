module

public import Froberg.PrefixPolynomial
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

/-! Uniform eventual row retention for two balanced blocks of variables. -/
noncomputable section
namespace Froberg
open Polynomial Filter
open scoped Topology

def affineCountPolynomial (d : ℕ) (a b : ℝ) : ℝ[X] :=
  (monomialCountPolynomial d).comp (C a * X + C b)

theorem affineCountPolynomial_natDegree (d : ℕ) {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    (affineCountPolynomial d a b).natDegree = d := by
  rw [affineCountPolynomial, natDegree_comp, monomialCountPolynomial_natDegree,
    natDegree_linear ha, mul_one]

theorem affineCountPolynomial_leadingCoeff (d : ℕ) {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    (affineCountPolynomial d a b).leadingCoeff = (d.factorial : ℝ)⁻¹ * a ^ d := by
  rw [affineCountPolynomial, leadingCoeff_comp (by rw [natDegree_linear ha]; omega),
    monomialCountPolynomial_leadingCoeff, leadingCoeff_linear ha,
    monomialCountPolynomial_natDegree]

theorem affineCountPolynomial_eval (d a b m : ℕ) :
    (affineCountPolynomial d a b).eval (m : ℝ) = ((a * m + b + d - 1).choose d : ℝ) := by
  rw [affineCountPolynomial, eval_comp]
  simp only [eval_add, eval_mul, eval_C, eval_X]
  convert monomialCountPolynomial_eval d (a * m + b) using 1 <;> push_cast <;> ring

/-- The binomial law in a balanced split puts at most one half of its mass
in any single bidegree. -/
theorem balanced_weight_leading_gap {d u v : ℕ} (hd : 0 < d) (huv : u + v = d) :
    5 * ((u.factorial : ℝ)⁻¹ * (v.factorial : ℝ)⁻¹) <
      3 * ((d.factorial : ℝ)⁻¹ * 2 ^ d) := by
  have hf : (d.factorial : ℝ) > 0 := by exact_mod_cast Nat.factorial_pos d
  have hu : (u.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero u
  have hv : (v.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero v
  have hc : (d.choose u : ℝ) ≤ 2 ^ (d - 1) := by
    exact_mod_cast (show d.choose u ≤ 2 ^ (d - 1) by
      simpa only [Nat.sub_add_cancel hd] using Nat.choose_succ_le_two_pow (d - 1) u)
  have hfac : (d.choose u : ℝ) * (u.factorial : ℝ) * (v.factorial : ℝ) = d.factorial := by
    exact_mod_cast (show d.choose u * u.factorial * v.factorial = d.factorial by
      simpa only [show d - u = v by omega] using Nat.choose_mul_factorial_mul_factorial (show u ≤ d by omega))
  have he : (u.factorial : ℝ)⁻¹ * (v.factorial : ℝ)⁻¹ = (d.choose u : ℝ) / d.factorial := by
    field_simp [hu, hv, hf.ne']
    nlinarith [hfac]
  rw [he]
  have hp : (2 : ℝ) ^ d = 2 ^ (d - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel hd]
  calc
    5 * ((d.choose u : ℝ) / d.factorial) = (5 * (d.choose u : ℝ)) / d.factorial := by ring
    _ < (3 * (2 : ℝ) ^ d) / d.factorial := by
      apply (div_lt_div_iff_of_pos_right hf).mpr
      rw [hp]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (d - 1)]
    _ = 3 * ((d.factorial : ℝ)⁻¹ * 2 ^ d) := by ring

/-- Any fixed offsets in two balanced blocks retain more than two fifths
of the weighted extension mass once their common size is large enough. -/
theorem eventually_balanced_weight_bound {d u v : ℕ} (hd : 0 < d) (huv : u + v = d)
    (a b c : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      5 * ((m + a + u - 1).choose u * (m + b + v - 1).choose v) ≤
        3 * (2 * m + c + d - 1).choose d := by
  let A := affineCountPolynomial d 2 c
  let B := affineCountPolynomial u 1 a * affineCountPolynomial v 1 b
  have hA : A.natDegree = d := affineCountPolynomial_natDegree d (by norm_num) c
  have hBu : affineCountPolynomial u 1 a ≠ 0 := by
    apply leadingCoeff_ne_zero.mp
    rw [affineCountPolynomial_leadingCoeff u (by norm_num)]
    positivity
  have hBv : affineCountPolynomial v 1 b ≠ 0 := by
    apply leadingCoeff_ne_zero.mp
    rw [affineCountPolynomial_leadingCoeff v (by norm_num)]
    positivity
  have hB : B.natDegree = d := by
    dsimp only [B]
    rw [natDegree_mul hBu hBv, affineCountPolynomial_natDegree u (by norm_num),
      affineCountPolynomial_natDegree v (by norm_num), huv]
  have hlA : A.leadingCoeff = (d.factorial : ℝ)⁻¹ * 2 ^ d :=
    affineCountPolynomial_leadingCoeff d (by norm_num) c
  have hlB : B.leadingCoeff = (u.factorial : ℝ)⁻¹ * (v.factorial : ℝ)⁻¹ := by
    simp [B, leadingCoeff_mul, affineCountPolynomial_leadingCoeff _ (by norm_num : (1 : ℝ) ≠ 0)]
  let P := C (3 : ℝ) * A - C (5 : ℝ) * B
  have htop : P.coeff d = 3 * A.leadingCoeff - 5 * B.leadingCoeff := by
    dsimp only [P]
    rw [coeff_sub, coeff_C_mul, coeff_C_mul, ← hA, coeff_natDegree, hA, ← hB, coeff_natDegree]
  have hp : 0 < P.coeff d := by
    rw [htop, hlA, hlB]
    exact sub_pos.mpr (balanced_weight_leading_gap hd huv)
  have hdeg : P.natDegree ≤ d := by
    apply (natDegree_sub_le _ _).trans
    simp [natDegree_C_mul (by norm_num : (3 : ℝ) ≠ 0),
      natDegree_C_mul (by norm_num : (5 : ℝ) ≠ 0), hA, hB]
  have hplc : 0 < P.leadingCoeff := by
    rw [leadingCoeff, natDegree_eq_of_le_of_coeff_ne_zero hdeg hp.ne']
    exact hp
  have hevent := (polynomial_eventually_positive P hplc).filter_mono
    (show Filter.map (fun m : ℕ => (m : ℝ)) atTop ≤ atTop from tendsto_natCast_atTop_atTop)
  filter_upwards [hevent] with m hm
  change 0 < P.eval (m : ℝ) at hm
  simp only [P, eval_sub, eval_mul, eval_C] at hm
  change 0 < 3 * A.eval (m : ℝ) - 5 * B.eval (m : ℝ) at hm
  simp only [A, B, eval_mul] at hm
  have hAm := affineCountPolynomial_eval d 2 c m
  have hUm := affineCountPolynomial_eval u 1 a m
  have hVm := affineCountPolynomial_eval v 1 b m
  norm_num only [Nat.cast_ofNat, one_mul] at hAm hUm hVm
  rw [hAm, hUm, hVm] at hm
  have h : (5 : ℝ) * (((m + a + u - 1).choose u : ℝ) * (m + b + v - 1).choose v) ≤
      3 * (2 * m + c + d - 1).choose d := by linarith
  exact_mod_cast h

end Froberg
