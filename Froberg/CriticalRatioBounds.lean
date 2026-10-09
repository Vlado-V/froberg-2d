module

public import Froberg.BinomialPolynomial
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-! Strict rational bounds for the critical leading ratio, used in the
large-variable construction and the deleted-bidegree estimate. -/
noncomputable section
namespace Froberg

def criticalRatio (d : ℕ) : ℝ :=
  1 - Real.sqrt (1 - 1 / (centralHalfBinomial d : ℝ))

theorem centralHalfBinomial_step {d : ℕ} (hd : 0 < d) :
    centralHalfBinomial d ≤ centralHalfBinomial (d + 1) := by
  have h := Nat.choose_succ_succ (2 * d - 1) (d - 1)
  have htop : 2 * d - 1 + 1 = 2 * d := by omega
  have hbot : d - 1 + 1 = d := by omega
  simp only [Nat.succ_eq_add_one, htop, hbot] at h
  have hle := Nat.choose_le_succ (2 * d) d
  simp only [Nat.succ_eq_add_one] at hle
  unfold centralHalfBinomial
  have ht : 2 * (d + 1) - 1 = 2 * d + 1 := by omega
  rw [ht, Nat.add_sub_cancel]
  omega

theorem centralHalfBinomial_ge_ten {d : ℕ} (hd : 3 ≤ d) :
    10 ≤ centralHalfBinomial d := by
  induction d, hd using Nat.le_induction with
  | base => decide
  | succ d hd ih => exact ih.trans (centralHalfBinomial_step (by omega))

theorem criticalRatio_identity {d : ℕ} (hd : 2 ≤ d) :
    (centralHalfBinomial d : ℝ) * criticalRatio d * (2 - criticalRatio d) = 1 := by
  have hH : (2 : ℝ) ≤ centralHalfBinomial d := by
    exact_mod_cast centralHalfBinomial_ge_two hd
  have hinside : 0 ≤ 1 - 1 / (centralHalfBinomial d : ℝ) := by
    have := (div_le_one (by linarith : 0 < (centralHalfBinomial d : ℝ))).mpr
      (show (1 : ℝ) ≤ centralHalfBinomial d by linarith)
    linarith
  have hs := Real.sq_sqrt hinside
  have hHne : (centralHalfBinomial d : ℝ) ≠ 0 := by linarith
  have hi : (centralHalfBinomial d : ℝ) * (1 / (centralHalfBinomial d : ℝ)) = 1 := by
    field_simp
  unfold criticalRatio
  nlinarith

theorem criticalRatio_bounds {d : ℕ} (hd : 2 ≤ d) :
    0 < criticalRatio d ∧ criticalRatio d < 1 ∧
      (1 / 2 : ℝ) < (centralHalfBinomial d : ℝ) * criticalRatio d ∧
      (centralHalfBinomial d : ℝ) * criticalRatio d < 3 / 5 := by
  have hH : (2 : ℝ) ≤ centralHalfBinomial d := by
    exact_mod_cast centralHalfBinomial_ge_two hd
  have hHpos : (0 : ℝ) < centralHalfBinomial d := by linarith
  have hinvpos : 0 < 1 / (centralHalfBinomial d : ℝ) := by positivity
  have hinv : 1 / (centralHalfBinomial d : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hH
  have hsnonneg := Real.sqrt_nonneg (1 - 1 / (centralHalfBinomial d : ℝ))
  have hsq := Real.sq_sqrt (show 0 ≤ 1 - 1 / (centralHalfBinomial d : ℝ) by linarith)
  have hslt : Real.sqrt (1 - 1 / (centralHalfBinomial d : ℝ)) < 1 := by nlinarith
  have hsgt : 2 / 3 < Real.sqrt (1 - 1 / (centralHalfBinomial d : ℝ)) := by nlinarith
  have hid := criticalRatio_identity hd
  have hrpos : 0 < criticalRatio d := by unfold criticalRatio; linarith
  have hrlt : criticalRatio d < 1 / 3 := by unfold criticalRatio; linarith
  have hprod : 0 < (centralHalfBinomial d : ℝ) * criticalRatio d := mul_pos hHpos hrpos
  refine ⟨hrpos, by linarith, ?_, ?_⟩ <;> nlinarith

theorem criticalRatio_sharp_bound {d : ℕ} (hd : 3 ≤ d) :
    (centralHalfBinomial d : ℝ) * criticalRatio d < 13 / 25 := by
  have hH : (10 : ℝ) ≤ centralHalfBinomial d := by
    exact_mod_cast centralHalfBinomial_ge_ten hd
  have hinv : 1 / (centralHalfBinomial d : ℝ) ≤ 1 / 10 :=
    one_div_le_one_div_of_le (by norm_num) hH
  have hsnonneg := Real.sqrt_nonneg (1 - 1 / (centralHalfBinomial d : ℝ))
  have hsq := Real.sq_sqrt (show 0 ≤ 1 - 1 / (centralHalfBinomial d : ℝ) by linarith)
  have hsgt : 12 / 13 < Real.sqrt (1 - 1 / (centralHalfBinomial d : ℝ)) := by nlinarith
  have hrlt : criticalRatio d < 1 / 13 := by unfold criticalRatio; linarith
  have hid := criticalRatio_identity (by omega : 2 ≤ d)
  have hpos := (criticalRatio_bounds (by omega : 2 ≤ d)).1
  have hprod : 0 < (centralHalfBinomial d : ℝ) * criticalRatio d :=
    mul_pos (by linarith) hpos
  nlinarith

end Froberg
