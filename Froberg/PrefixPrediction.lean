module

public import Froberg.Prefix

@[expose] public section

/-! Before twice the generator degree, positive truncation is simply the
nonnegative part of the two-term coefficient. -/
noncomputable section
namespace Froberg
open Finset

def countReal (n j : ℕ) : ℝ := (n + j - 1).choose j

private theorem countReal_pos {n : ℕ} (hn : 0 < n) (j : ℕ) : 0 < countReal n j := by
  unfold countReal
  exact_mod_cast monomial_count_pos hn j

private theorem countReal_succ {n : ℕ} (hn : 0 < n) (j : ℕ) :
    countReal n (j + 1) = countReal n j * (n + j) / (j + 1) := by
  have h := Nat.add_one_mul_choose_eq (n + j - 1) j
  have htop : n + j - 1 + 1 = n + j := by omega
  rw [htop] at h
  have htop' : n + (j + 1) - 1 = n + j := by omega
  apply (eq_div_iff (by positivity : (j : ℝ) + 1 ≠ 0)).mpr
  dsimp [countReal]
  exact_mod_cast h.symm.trans (Nat.mul_comm _ _)

/-- The ratio of target monomials to multiplier monomials decreases with degree. -/
theorem monomial_quotient_antitone {n : ℕ} (hn : 0 < n) (d : ℕ) :
    Antitone (fun e : ℕ => countReal n (d + e) / countReal n e) := by
  apply antitone_nat_of_succ_le
  intro e
  have hN := countReal_pos hn e
  have hM := countReal_pos hn (d + e)
  have hnp : (0 : ℝ) < n + e := by exact_mod_cast (show 0 < n + e by omega)
  have hp : (0 : ℝ) < e + 1 := by positivity
  have hdp : (0 : ℝ) < d + e + 1 := by positivity
  have hstep : ((n : ℝ) + (d + e)) * (e + 1) ≤ (d + e + 1) * (n + e) := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ d by positivity) (sub_nonneg.mpr hn')]
  rw [show d + (e + 1) = (d + e) + 1 by omega, countReal_succ hn, countReal_succ hn]
  push_cast
  have heq :
      (countReal n (d + e) * ((n : ℝ) + (d + e)) / (d + e + 1)) /
          (countReal n e * (n + e) / (e + 1)) =
        (countReal n (d + e) / countReal n e) *
          (((n : ℝ) + (d + e)) * (e + 1) / ((d + e + 1) * (n + e))) := by
    field_simp [hN.ne', hnp.ne', hdp.ne', hp.ne'] <;> ring
  rw [heq]
  exact mul_le_of_le_one_right (div_nonneg hM.le hN.le)
    ((div_le_one₀ (mul_pos hdp hnp)).mpr hstep)

/-- Positivity of one two-term coefficient implies positivity of every earlier coefficient. -/
theorem prefix_coefficient_positive_before {n d r e : ℕ} (hn : 0 < n) (hed : e < d)
    (hpos : (r : ℝ) * countReal n e < countReal n (d + e)) :
    ∀ i ≤ d + e, 0 < predictionCoefficient n d r i := by
  intro i hi
  by_cases hid : i < d
  · rw [predictionCoefficient_below_degree n d r i hn hid]
    exact_mod_cast monomial_count_pos hn i
  · have hdi : d ≤ i := by omega
    have hei : i - d ≤ e := by omega
    have hratio := monomial_quotient_antitone hn d hei
    have hstrict : (r : ℝ) < countReal n (d + e) / countReal n e :=
      (lt_div_iff₀ (countReal_pos hn e)).mpr hpos
    have hsmall := hstrict.trans_le hratio
    have hsmall' := (lt_div_iff₀ (countReal_pos hn (i - d))).mp hsmall
    rw [show d + (i - d) = i by omega] at hsmall'
    rw [predictionCoefficient_before_endpoint n d r i hn hdi (by omega)]
    dsimp [countReal] at hsmall'
    exact_mod_cast (sub_pos.mpr hsmall')

/-- In the entire prefix, positive truncation agrees with the maximal-rank formula. -/
theorem predictedHilbertFunction_prefix {n d r e : ℕ} (hn : 0 < n) (hed : e < d) :
    predictedHilbertFunction n d r (d + e) =
      (n + (d + e) - 1).choose (d + e) - r * (n + e - 1).choose e := by
  have hc := predictionCoefficient_before_endpoint n d r (d + e) hn (by omega) (by omega)
  simp only [Nat.add_sub_cancel_left] at hc
  rw [← Nat.cast_mul] at hc
  by_cases hp : r * (n + e - 1).choose e < (n + (d + e) - 1).choose (d + e)
  · have hp' : (r : ℝ) * countReal n e < countReal n (d + e) := by
      unfold countReal
      exact_mod_cast hp
    unfold predictedHilbertFunction
    rw [positiveTruncation_eq_of_positive _ _ (prefix_coefficient_positive_before hn hed hp'), hc]
    omega
  · have hnonpos : predictionCoefficient n d r (d + e) ≤ 0 := by rw [hc]; omega
    unfold predictedHilbertFunction
    rw [positiveTruncation_eq_zero _ _ _ le_rfl hnonpos]
    omega

end Froberg
