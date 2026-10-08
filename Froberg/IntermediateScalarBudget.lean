import Froberg.ScalarSeparationAsymptotic
import Froberg.BalancedWeightPolynomial

/-! An explicit eventual incidence budget for the sparse new layers in B.4. -/
noncomputable section
namespace Froberg
open Polynomial Filter
open scoped Topology

theorem monomial_count_offset_normalized_tendsto (d t : ℕ) :
    Tendsto (fun n : ℕ => ((n+t+d-1).choose d : ℝ)/(n : ℝ)^d)
      atTop (𝓝 (d.factorial : ℝ)⁻¹) := by
  let P := affineCountPolynomial d 1 t
  have hP : P≠0 := by
    apply leadingCoeff_ne_zero.mp
    simp [P,affineCountPolynomial_leadingCoeff d (by norm_num : (1 : ℝ)≠0),Nat.factorial_ne_zero]
  have hdeg : P.degree=(X^d : ℝ[X]).degree := by
    rw [degree_eq_natDegree hP,degree_X_pow]
    congr 1
    exact affineCountPolynomial_natDegree d (by norm_num) t
  have ht := (P.div_tendsto_atTop_leadingCoeff_div_of_degree_eq (X^d) hdeg).comp
    tendsto_natCast_atTop_atTop
  have heval (n : ℕ) : P.eval (n : ℝ)=((n+t+d-1).choose d : ℝ) := by
    simpa only [P,Nat.cast_one,one_mul] using affineCountPolynomial_eval d 1 t n
  simpa only [Function.comp_def,heval,eval_pow,eval_X,P,
    affineCountPolynomial_leadingCoeff d (by norm_num : (1 : ℝ)≠0),one_pow,mul_one,
    leadingCoeff_X_pow,div_one] using ht

/-- The lower-order quotient-dimension and exceptional-shadow terms are
absorbed by exactly the strict sparse-layer capacity inequality. -/
theorem eventually_intermediate_scalar_budget {d s h B : ℕ} (hs : s<d) (hB : B≤h)
    (q : ℕ → ℕ)
    (hq : Tendsto (fun n : ℕ => (q n : ℝ)/(n : ℝ)^d) atTop
      (𝓝 (criticalRatio d/(d.factorial : ℝ))))
    (hgap : (B : ℝ)+(h : ℝ)*((s+d).choose s : ℝ)*criticalRatio d<h) :
    ∀ᶠ n : ℕ in atTop,
      h*(s+d).choose s * (q n+h*(n+s-1).choose s+(h*2^h)*(n+(d-1)-1).choose (d-1)) ≤
        (h-B)*(n+s+d-1).choose d := by
  have hsmall := (monomial_count_normalized_small_tendsto hs).const_mul (h : ℝ)
  have herr := (monomial_count_normalized_small_tendsto (show d-1<d by omega)).const_mul ((h*2^h : ℕ) : ℝ)
  have hl := ((hq.add hsmall).add herr).const_mul ((h*(s+d).choose s : ℕ) : ℝ)
  have hr := (monomial_count_offset_normalized_tendsto d s).const_mul ((h-B : ℕ) : ℝ)
  have hf : (0 : ℝ)<d.factorial := by exact_mod_cast Nat.factorial_pos d
  have hcast : ((h-B : ℕ) : ℝ)=(h : ℝ)-B := Nat.cast_sub hB
  have hstrict : ((h*(s+d).choose s : ℕ) : ℝ)*
      (criticalRatio d/(d.factorial : ℝ)+(h : ℝ)*0+((h*2^h : ℕ) : ℝ)*0) <
      ((h-B : ℕ) : ℝ)*(d.factorial : ℝ)⁻¹ := by
    simp only [mul_zero,add_zero,Nat.cast_mul,hcast]
    apply (mul_lt_mul_iff_left₀ hf).mp
    field_simp
    nlinarith
  filter_upwards [hl.eventually_lt hr hstrict,eventually_gt_atTop 0] with n hn hnpos
  have hnp : (0 : ℝ)<n := by exact_mod_cast hnpos
  have hp : (0 : ℝ)<(n : ℝ)^d := pow_pos hnp d
  have heq : ((h*(s+d).choose s : ℕ) : ℝ)*
      ((q n : ℝ)/(n : ℝ)^d + (h : ℝ)*(((n+s-1).choose s : ℝ)/(n : ℝ)^d) +
        ((h*2^h : ℕ) : ℝ)*(((n+(d-1)-1).choose (d-1) : ℝ)/(n : ℝ)^d)) =
      ((h*(s+d).choose s * (q n+h*(n+s-1).choose s+(h*2^h)*(n+(d-1)-1).choose (d-1)) : ℕ) : ℝ)/(n : ℝ)^d := by
    push_cast
    ring
  rw [heq] at hn
  have hrq : ((h-B : ℕ) : ℝ)*(((n+s+d-1).choose d : ℝ)/(n : ℝ)^d) =
      (((h-B)*(n+s+d-1).choose d : ℕ) : ℝ)/(n : ℝ)^d := by push_cast; ring
  rw [hrq] at hn
  exact_mod_cast ((div_lt_div_iff_of_pos_right hp).mp hn).le

end Froberg
