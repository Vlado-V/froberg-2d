module

public import Froberg.CapacityRatios

@[expose] public section

/-! # Room for the preceding-degree endpoint in the outer family -/

noncomputable section
namespace Froberg

theorem centralHalfBinomial_recurrence {d : ℕ} (hd : 0 < d) :
    (d + 1) * centralHalfBinomial (d + 1) =
      (4 * d + 2) * centralHalfBinomial d := by
  have h := Nat.succ_mul_centralBinom_succ d
  simp only [Nat.centralBinom] at h
  rw [centralBinomial_eq_twice_half (by omega : 0 < d + 1),
    centralBinomial_eq_twice_half hd] at h
  nlinarith

theorem centralHalfBinomial_ge_succ {d : ℕ} (hd : 2 ≤ d) :
    d + 1 ≤ centralHalfBinomial d := by
  induction d, hd using Nat.le_induction with
  | base => decide
  | succ d hd ih =>
      have h := centralHalfBinomial_double_step (d := d) (by omega)
      omega

/-- The strict factor-four gap used in Proposition B.7. -/
theorem criticalRatio_lt_four_succ {d : ℕ} (hd : 2 ≤ d) :
    criticalRatio d < 4 * criticalRatio (d + 1) := by
  let x := criticalRatio d
  let y := criticalRatio (d + 1)
  let H₀ : ℝ := centralHalfBinomial d
  let H₁ : ℝ := centralHalfBinomial (d + 1)
  have hx := criticalRatio_bounds hd
  have hy := criticalRatio_bounds (d := d + 1) (by omega)
  have hi₀ : H₀ * x * (2 - x) = 1 := criticalRatio_identity hd
  have hi₁ : H₁ * y * (2 - y) = 1 := criticalRatio_identity (by omega)
  have hr : ((d : ℝ) + 1) * H₁ = (4 * (d : ℝ) + 2) * H₀ := by
    dsimp [H₀, H₁]
    exact_mod_cast centralHalfBinomial_recurrence (d := d) (by omega)
  have hH₀ : (d : ℝ) + 1 ≤ H₀ := by
    dsimp [H₀]
    exact_mod_cast centralHalfBinomial_ge_succ hd
  have hH₁ : 0 < H₁ := by
    dsimp [H₁]
    have h := centralHalfBinomial_ge_two (d := d + 1) (by omega)
    exact_mod_cast (show 0 < centralHalfBinomial (d + 1) by omega)
  have hxpos : 0 < x := hx.1
  have hxlt : x < 1 := hx.2.1
  have hypos : 0 < y := hy.1
  have hylt : y < 1 := hy.2.1
  have hsmall : ((d : ℝ) + 1) * x < 3 / 5 :=
    (mul_le_mul_of_nonneg_right hH₀ hxpos.le).trans_lt hx.2.2.2
  have hgap : (6 * (d : ℝ) + 7) * x < 8 := by nlinarith
  change x < 4 * y
  by_contra hh
  have hxy : y ≤ x / 4 := by linarith
  have hpoly : y * (2 - y) ≤ (x / 4) * (2 - x / 4) := by
    have hprod := mul_nonneg (show 0 ≤ x / 4 - y by linarith)
      (show 0 ≤ 2 - x / 4 - y by linarith)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hpoly hH₁.le
  have hcompare : 16 * ((d : ℝ) + 1) ≤
      (4 * (d : ℝ) + 2) * H₀ * x * (8 - x) := by
    have hh := mul_le_mul_of_nonneg_left hmul
      (show 0 ≤ 16 * ((d : ℝ) + 1) by positivity)
    have heq : 16 * ((d : ℝ) + 1) * (H₁ * (x / 4 * (2 - x / 4))) =
        (4 * (d : ℝ) + 2) * H₀ * x * (8 - x) := by
      calc
        _ = (((d : ℝ) + 1) * H₁) * x * (8 - x) := by ring
        _ = _ := by rw [hr]
    rw [heq] at hh
    nlinarith [hi₁]
  have hid : (4 * (d : ℝ) + 2) * H₀ * x * (8 - x) - 16 * ((d : ℝ) + 1) =
      2 * (H₀ * x) * ((6 * (d : ℝ) + 7) * x - 8) := by
    calc
      _ = (4 * (d : ℝ) + 2) * H₀ * x * (8 - x) -
          16 * ((d : ℝ) + 1) * (H₀ * x * (2 - x)) := by rw [hi₀]; ring
      _ = _ := by ring
  have hnegative : 2 * (H₀ * x) * ((6 * (d : ℝ) + 7) * x - 8) < 0 := by
    apply mul_neg_of_pos_of_neg
    · have : 0 < H₀ := by linarith
      positivity
    · linarith
  linarith

theorem previous_criticalRatio_lt_four {d : ℕ} (hd : 3 ≤ d) :
    criticalRatio (d - 1) < 4 * criticalRatio d := by
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ d)] using
    criticalRatio_lt_four_succ (d := d - 1) (by omega)

end Froberg
