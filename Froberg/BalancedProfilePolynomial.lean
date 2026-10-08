import Froberg.BalancedWeightPolynomial

/-! A strict binomial-probability margin gives the corresponding eventual
weighted row margin in two balanced variable blocks. -/
noncomputable section
namespace Froberg
open Polynomial Filter Finset
open scoped Topology

private theorem inverse_factorials_choose {d u : ℕ} (hu : u ≤ d) :
    (u.factorial : ℝ)⁻¹ * ((d-u).factorial : ℝ)⁻¹ = (d.choose u : ℝ) / d.factorial := by
  have hf : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have hu' : (u.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero u
  have hv : ((d-u).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (d-u)
  have hfac : (d.choose u : ℝ) * u.factorial * (d-u).factorial = d.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hu
  field_simp [hf,hu',hv]
  nlinarith [hfac]

/-- A retained set of increments of limiting mass strictly above one
quarter retains at least one quarter for all sufficiently large block sizes. -/
theorem eventually_balanced_profile_sum_bound (d : ℕ) (U : Finset ℕ)
    (hU : ∀ u ∈ U, u ≤ d) (hgap : 2^d < 4 * ∑ u ∈ U, d.choose u)
    (a b c : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      (2*m+c+d-1).choose d ≤
        4 * ∑ u ∈ U, (m+a+u-1).choose u * (m+b+(d-u)-1).choose (d-u) := by
  let A := affineCountPolynomial d 2 c
  let B (u : ℕ) := affineCountPolynomial u 1 a * affineCountPolynomial (d-u) 1 b
  have hA : A.natDegree = d := affineCountPolynomial_natDegree d (by norm_num) c
  have hBu (u : ℕ) : affineCountPolynomial u 1 a ≠ 0 := by
    apply leadingCoeff_ne_zero.mp
    rw [affineCountPolynomial_leadingCoeff u (by norm_num)]
    positivity
  have hBv (u : ℕ) : affineCountPolynomial (d-u) 1 b ≠ 0 := by
    apply leadingCoeff_ne_zero.mp
    rw [affineCountPolynomial_leadingCoeff (d-u) (by norm_num)]
    positivity
  have hB (u : ℕ) (hu : u ∈ U) : (B u).natDegree = d := by
    dsimp only [B]
    rw [natDegree_mul (hBu u) (hBv u),affineCountPolynomial_natDegree u (by norm_num),
      affineCountPolynomial_natDegree (d-u) (by norm_num)]
    have hu' := hU u hu
    omega
  have hlA : A.leadingCoeff = (d.factorial : ℝ)⁻¹ * 2^d :=
    affineCountPolynomial_leadingCoeff d (by norm_num) c
  have hBc (u : ℕ) (hu : u ∈ U) : (B u).coeff d = (d.choose u : ℝ) / d.factorial := by
    conv_lhs => rw [← hB u hu,coeff_natDegree]
    simp only [B,leadingCoeff_mul,affineCountPolynomial_leadingCoeff _ (by norm_num : (1 : ℝ) ≠ 0),
      one_pow,mul_one]
    exact inverse_factorials_choose (hU u hu)
  have hAc : A.coeff d = (d.factorial : ℝ)⁻¹ * 2^d := by
    conv_lhs => rw [← hA,coeff_natDegree]
    exact hlA
  let P := C (4 : ℝ) * (∑ u ∈ U, B u) - A
  have htop : P.coeff d = 4 * (∑ u ∈ U, (d.choose u : ℝ)) / d.factorial -
      (d.factorial : ℝ)⁻¹ * 2^d := by
    dsimp only [P]
    rw [coeff_sub,coeff_C_mul,finset_sum_coeff,hAc]
    have hs : (∑ u ∈ U, (B u).coeff d) = ∑ u ∈ U, (d.choose u : ℝ) / d.factorial :=
      sum_congr rfl (fun u hu => hBc u hu)
    rw [hs, ← sum_div]
    ring
  have hp : 0 < P.coeff d := by
    rw [htop]
    have hg : (2 : ℝ)^d < 4 * ∑ u ∈ U, (d.choose u : ℝ) := by exact_mod_cast hgap
    have hf : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
    have hh := (div_lt_div_iff_of_pos_right hf).mpr hg
    simpa only [div_eq_mul_inv,mul_comm] using sub_pos.mpr hh
  have hdeg : P.natDegree ≤ d := by
    apply (natDegree_sub_le _ _).trans
    rw [max_le_iff]
    constructor
    · apply (natDegree_C_mul_le _ _).trans
      exact natDegree_sum_le_of_forall_le U B (fun u hu => (hB u hu).le)
    · exact hA.le
  have hplc : 0 < P.leadingCoeff := by
    rw [leadingCoeff,natDegree_eq_of_le_of_coeff_ne_zero hdeg hp.ne']
    exact hp
  have hevent := (polynomial_eventually_positive P hplc).filter_mono
    (show Filter.map (fun m : ℕ => (m : ℝ)) atTop ≤ atTop from tendsto_natCast_atTop_atTop)
  filter_upwards [hevent] with m hm
  change 0 < P.eval (m : ℝ) at hm
  simp only [P,eval_sub,eval_mul,eval_C,eval_finset_sum] at hm
  have hAm := affineCountPolynomial_eval d 2 c m
  norm_num only [Nat.cast_ofNat] at hAm
  have hBm (u : ℕ) : (B u).eval (m : ℝ) =
      ((m+a+u-1).choose u : ℝ) * ((m+b+(d-u)-1).choose (d-u) : ℝ) := by
    simp only [B,eval_mul]
    have h₁ := affineCountPolynomial_eval u 1 a m
    have h₂ := affineCountPolynomial_eval (d-u) 1 b m
    norm_num only [Nat.cast_one, one_mul] at h₁ h₂
    rw [h₁,h₂]
  simp_rw [hBm] at hm
  change 0 < 4 * (∑ u ∈ U, ((m+a+u-1).choose u : ℝ) * ((m+b+(d-u)-1).choose (d-u) : ℝ)) - (affineCountPolynomial d 2 c).eval (m : ℝ) at hm
  rw [hAm] at hm
  have hh : ((2*m+c+d-1).choose d : ℝ) ≤
      4 * ∑ u ∈ U, ((m+a+u-1).choose u : ℝ) * ((m+b+(d-u)-1).choose (d-u) : ℝ) := by linarith
  exact_mod_cast hh

end Froberg
