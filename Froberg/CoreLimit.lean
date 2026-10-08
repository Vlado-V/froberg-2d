import Froberg.CoreLower

/-! The core proportion has the exact limiting value specified in B.2. -/
noncomputable section
namespace Froberg
open Filter Polynomial
open scoped Topology

theorem tendsto_core_of_positive_fraction (a : ℕ → ℕ)
    (ha : ∀ᶠ n : ℕ in atTop, (n : ℝ) / 4 < a n) : Tendsto a atTop atTop := by
  apply tendsto_atTop.mpr
  intro N
  filter_upwards [ha, eventually_ge_atTop (4 * N)] with n hn hN
  have hN' : (4 : ℝ) * N ≤ n := by exact_mod_cast hN
  have hna : (N : ℝ) ≤ a n := by linarith
  exact_mod_cast hna

theorem core_ratio_of_monomial_limit (a : ℕ → ℕ) {K s : ℕ} (hK : 0 < K) (hs : 0 < s)
    (ha : Tendsto a atTop atTop) (c : ℝ)
    (hf : Tendsto (fun n : ℕ => ((K * (a n + s - 1).choose s : ℕ) : ℝ) / (n : ℝ) ^ s)
      atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop
      (𝓝 ((c * (s.factorial : ℝ) / K) ^ ((s : ℝ)⁻¹))) := by
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hfac : (s.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero s
  have hm := polynomial_div_pow_nat_tendsto (monomialCountPolynomial s) s
    (monomialCountPolynomial_natDegree s).le
  simp only [monomialCountPolynomial_eval, monomialCountPolynomial_top] at hm
  have hd : Tendsto (fun n : ℕ => ((K * (a n + s - 1).choose s : ℕ) : ℝ) / (a n : ℝ) ^ s)
      atTop (𝓝 ((K : ℝ) / (s.factorial : ℝ))) := by
    simpa only [Nat.cast_mul, Function.comp_apply, div_eq_mul_inv, mul_assoc] using
      (hm.comp ha).const_mul (K : ℝ)
  have hdiv := hf.div hd (div_ne_zero hK0 hfac)
  have hc : c / ((K : ℝ) / (s.factorial : ℝ)) = c * (s.factorial : ℝ) / K := by field_simp
  rw [hc] at hdiv
  have hpow : Tendsto (fun n : ℕ => ((a n : ℝ) / n) ^ s) atTop
      (𝓝 (c * (s.factorial : ℝ) / K)) := by
    apply hdiv.congr'
    filter_upwards [ha.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℕ)] with n hn hn0
    have hcount : (0 : ℝ) < (a n + s - 1).choose s := by
      exact_mod_cast (Nat.choose_pos (by omega : s ≤ a n + s - 1))
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
    have ha' : (a n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [Pi.div_apply, Nat.cast_mul]
    rw [div_pow]
    field_simp [hcount.ne']
  have hroot := hpow.rpow_const (Or.inr (show (0 : ℝ) ≤ (s : ℝ)⁻¹ by positivity))
  apply hroot.congr'
  exact Eventually.of_forall fun n => Real.pow_rpow_inv_natCast (by positivity) hs.ne'

def limitingCoreFraction (d : ℕ) : ℝ :=
  ((centralHalfBinomial d : ℝ) * criticalRatio d) ^ (((d - 1 : ℕ) : ℝ)⁻¹)

theorem limitingCoreFraction_bounds {d : ℕ} (hd : 3 ≤ d) :
    0 < limitingCoreFraction d ∧ limitingCoreFraction d < 1 := by
  have hρ := criticalRatio_bounds (d := d) (by omega)
  have hp : 0 < (centralHalfBinomial d : ℝ) * criticalRatio d := by linarith [hρ.2.2.1]
  have hp1 : (centralHalfBinomial d : ℝ) * criticalRatio d < 1 := by linarith [hρ.2.2.2]
  have hdpos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
  have hs : (0 : ℝ) < ((d - 1 : ℕ) : ℝ)⁻¹ := by positivity
  exact ⟨Real.rpow_pos_of_pos hp _, Real.rpow_lt_one hp.le hp1 hs⟩

theorem limitingCoreFraction_pow {d : ℕ} (hd : 3 ≤ d) :
    limitingCoreFraction d ^ (d - 1) = (centralHalfBinomial d : ℝ) * criticalRatio d := by
  apply Real.rpow_inv_natCast_pow
  · have := (criticalRatio_bounds (d := d) (by omega)).2.2.1
    linarith
  · omega

theorem exact_counts_core_limit {d K h : ℕ} (hd : 3 ≤ d)
    (hK : 0 < K) (hh : h = K * centralHalfBinomial d)
    (g r a f e : ℕ → ℕ)
    (hr : ∀ n, 0 < n → lowerCount n d ≤ r n ∧ r n ≤ upperCount n d)
    (hg : Tendsto (fun n => (g n : ℝ) / (n : ℝ) ^ (d - 1)) atTop (𝓝 0))
    (hcounts : ∀ᶠ n : ℕ in atTop,
      f n = K * (a n + (d - 1) - 1).choose (d - 1) ∧
      upperCount n d + f n + g n + e n = r (n + h) ∧
      (e n : ℝ) < countBeta d * (h : ℝ) ^ 2 * (n : ℝ) ^ (d - 2) ∧
      (n : ℝ) / 4 < a n) :
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 (limitingCoreFraction d)) := by
  have heUpper : Tendsto (fun n : ℕ =>
      (countBeta d * (h : ℝ) ^ 2 * (n : ℝ) ^ (d - 2)) / (n : ℝ) ^ (d - 1))
      atTop (𝓝 0) := by
    let P : Polynomial ℝ := monomial (d - 2) (countBeta d * (h : ℝ) ^ 2)
    have hdeg : P.natDegree < d - 1 := (natDegree_monomial_le _).trans_lt (by omega)
    simpa only [P, eval_monomial, coeff_eq_zero_of_natDegree_lt hdeg] using
      polynomial_div_pow_nat_tendsto P (d - 1) hdeg.le
  have he : Tendsto (fun n => (e n : ℝ) / (n : ℝ) ^ (d - 1)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => by positivity) _ heUpper
    filter_upwards [hcounts] with n hn
    exact div_le_div_of_nonneg_right hn.2.2.1.le (by positivity)
  have hc := ((rounded_critical_increment_limit' (by omega : 2 ≤ d) h r hr).sub hg).sub he
  simp only [sub_zero] at hc
  have hf : Tendsto (fun n : ℕ =>
      ((K * (a n + (d - 1) - 1).choose (d - 1) : ℕ) : ℝ) / (n : ℝ) ^ (d - 1))
      atTop (𝓝 ((h : ℝ) * criticalRatio d / ((d - 1).factorial : ℝ))) := by
    apply hc.congr'
    filter_upwards [hcounts] with n hn
    have ht : (upperCount n d : ℝ) + f n + g n + e n = r (n + h) := by
      exact_mod_cast hn.2.1
    have hfn : (f n : ℝ) = ((K * (a n + (d - 1) - 1).choose (d - 1) : ℕ) : ℝ) :=
      congrArg Nat.cast hn.1
    rw [← hfn]
    simp only [← sub_div]
    congr 1
    linarith
  have ha := tendsto_core_of_positive_fraction a (hcounts.mono fun _ hn => hn.2.2.2)
  have hout := core_ratio_of_monomial_limit a hK (by omega : 0 < d - 1) ha _ hf
  have hconst : (h : ℝ) * criticalRatio d / ((d - 1).factorial : ℝ) *
      ((d - 1).factorial : ℝ) / K = (centralHalfBinomial d : ℝ) * criticalRatio d := by
    rw [hh]
    push_cast
    have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
    have hfac : ((d - 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (d - 1)
    field_simp
  simpa only [hconst, limitingCoreFraction] using hout

end Froberg
